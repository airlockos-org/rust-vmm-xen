#![no_std]
#![warn(missing_docs)]
//! Bounded XenStore guest protocol over a caller-owned byte transport.
//!
//! Layout and operation numbers follow Xen 4.20.4 public/io/xs_wire.h (MIT,
//! Copyright 2005 Rusty Russell, IBM). Unlike a ring-sized exchange, this
//! client streams messages up to the protocol's 4096-byte payload limit.
//! Transport owns mapping, notification, deadlines and exclusive access to the
//! domain connection.
//!
//! # Contract and verification boundary
//!
//! Inputs from the daemon are hostile bytes. The executable core verifies
//! framing, exact reply identity/payload correspondence, error/watch grammar,
//! local ring plans, request-ID exhaustion and fail-closed transitions. It
//! admits at most 4096 payload bytes and 64 intervening watches per exchange.
//! Every finite byte loop decreases; transport and callback calls must
//! terminate under runtime deadlines. No peer cooperation is assumed for
//! parsing safety.
//!
//! `Transport` implementations are unverified effects: their ghost transcripts
//! must correspond to the actual exclusively owned stream, preserving byte
//! order and copying into private storage. The runtime must retain the failed
//! client and never reset its state on a live stream. `WatchSink` must bound
//! retained storage, terminate and avoid connection reentry. The generic core
//! cannot establish these properties of arbitrary platform implementations.
//!
//! The trusted base includes the pinned Verus/vstd specifications, Rust/LLVM,
//! liballoc and the runtime adapters. A payload buffer is reserved once to the
//! validated length; no event queue is allocated by the core. Allocation
//! failure follows the consuming kernel's fatal allocation contract, not a
//! recoverable protocol success. Proofs bound logical lengths/work, not
//! allocator metadata, physical memory mapping, hypervisor behavior or
//! scheduler wall-clock progress.

extern crate alloc;

use alloc::vec::Vec;
pub mod ring;

use vstd::{
    bytes::{u32_from_le_bytes, u32_to_le_bytes},
    prelude::*,
    slice::slice_subrange,
};

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Maximum watch notifications processed before an exchange fails closed.
pub const MAX_WATCHES: usize = 64;

/// Trusted callback boundary; storage, scheduling and callback completion are
/// caller obligations. False means capacity exhaustion, never silent loss.
pub trait WatchSink {
    /// Accept an owned-snapshot watch hint without reentering the connection.
    fn event(&mut self, path: &[u8], token: &[u8]) -> bool;
}


/// Maximum payload defined by Xen, independently of the 1024-byte shared ring.
pub const MAX_PAYLOAD: usize = 4096;

/// XenStore operations used for device discovery and lifecycle negotiation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Operation {
    /// List child names as NUL-separated strings.
    Directory = 1,
    /// Read a node's bytes.
    Read = 2,
    /// Register a path/token watch.
    Watch = 4,
    /// Remove a path/token watch.
    Unwatch = 5,
    /// Begin a transaction; its decimal ID is returned by the daemon.
    TransactionStart = 6,
    /// Commit or abort the transaction named in the header.
    TransactionEnd = 7,
    /// Write a path followed by a NUL and its value.
    Write = 11,
}

/// Failure of transport, message validation or a daemon operation.
#[derive(Debug, PartialEq, Eq)]
pub enum Error<E> {
    /// Transport failure, including caller-enforced timeout.
    Transport(
        /// Runtime error returned by the effect boundary.
        E
    ),
    /// Contradictory identity, malformed framing, or watch overflow at the
    /// caller.
    Protocol,
    /// Request exceeds the wire bound; no request was published.
    TooLarge,
    /// A previous ambiguous exchange prohibits further use of this connection.
    Poisoned,
    /// Daemon error name, without its terminal NUL (for example EAGAIN).
    Daemon(
        /// Owned nonempty error name, with its delimiter removed.
        Vec<u8>
    ),
}

/// Exclusive byte stream with bounded blocking supplied by the runtime.
///
/// Implementations must return positive progress no greater than the supplied
/// slice, or an error. They must enforce an absolute deadline, including when
/// each call makes progress. Notify the peer as needed after consuming bytes.
pub trait Transport {
    /// Ghost transcript of successfully published request bytes. Runtime
    /// implementations must correspond to the same exclusive XenStore stream.
    spec fn sent(&self) -> Seq<u8>;

    /// Ghost transcript of consumed response bytes, copied into private memory.
    spec fn received(&self) -> Seq<u8>;

    /// Platform-specific failure, normally including timeout and corrupt
    /// indices.
    type Error;

    /// Publish some request bytes, waiting for ring capacity when necessary.
    fn write(&mut self, bytes: &[u8]) -> (result: Result<usize, Self::Error>)
        ensures final(self).received() == old(self).received(),
            match result {
                Ok(size) => 0 < size <= bytes@.len() ==>
                    final(self).sent() == old(self).sent() + bytes@.subrange(0, size as int),
                Err(_) => true,
            };

    /// Copy some response bytes into private memory, waiting when necessary.
    fn read(&mut self, bytes: &mut [u8]) -> (result: Result<usize, Self::Error>)
        ensures final(bytes)@.len() == old(bytes)@.len(),
            final(self).sent() == old(self).sent(),
            match result {
                Ok(size) => 0 < size <= final(bytes)@.len() ==>
                    final(self).received() == old(self).received() + final(bytes)@.subrange(0, size as int),
                Err(_) => true,
            };
}

/// Private watch notification interleaved with a synchronous response.
/// Watch paths are hints to re-read authoritative state, not state snapshots.
pub struct Watch<'a> {
    /// Changed path, potentially beneath the registered directory.
    pub path: &'a [u8],
    /// Opaque token selected by the watch registrant.
    pub token: &'a [u8],
}

/// One outstanding request per domain connection, with non-recycled request
/// IDs.
///
/// The caller must retain this object after failure: constructing another
/// client on the same stream could accept the failed request's delayed reply.
/// Device drivers share the connection through their runtime's exclusive owner.
pub struct Client {
    /// Some is the next admissible identity; None is permanently poisoned.
    /// An exchange consumes this permission before any transport effect.
    next: Option<u32>,
}



impl Default for Client {
    /// Start with a fresh request-identity permission.
    fn default() -> Self { Self::new() }
}

impl Client {
    /// Create the sole client for a freshly provisioned connection.
    /// Whether another request can be admitted.
    pub closed spec fn ready(&self) -> bool { self.next is Some && self.next->Some_0 > 0 }

    /// Identity reserved for the next admitted request.
    pub closed spec fn next_id(&self) -> u32 { match self.next { Some(id) => id, None => 0 } }

    /// Create an unused connection state with request identity one.
    pub const fn new() -> (result: Self)
        ensures result.ready(), result.next_id() == 1,
    {
        Self { next: Some(1) }
    }

    /// Exchange one request, dispatching intervening watch events to a bounded
    /// sink.
    ///
    /// `transaction` is zero outside a transaction. Bodies follow Xen's native
    /// operation grammar. The sink must not reenter this connection; returning
    /// false means it cannot retain a notification and poisons the connection
    /// rather than silently losing configuration changes. Daemon errors consume
    /// their complete response and allow subsequent requests (including
    /// EAGAIN).
    pub fn exchange<T: Transport, W: WatchSink>(
        &mut self,
        transport: &mut T,
        operation: Operation,
        transaction: u32,
        body: &[u8],
        watch: &mut W,
    ) -> (result: Result<Vec<u8>, Error<T::Error>>)
        ensures
            result is Ok ==> final(self).ready() && final(self).next_id() == old(self).next_id() + 1
                && body@.len() <= MAX_PAYLOAD
                && result->Ok_0@.len() <= MAX_PAYLOAD
                && accepted(final(transport).received(), operation as u32,
                    old(self).next_id(), transaction, result->Ok_0@),
            result is Ok ==> body@.len() <= MAX_PAYLOAD && final(transport).sent() == old(transport).sent()
                + header_bytes(operation as u32, old(self).next_id(), transaction, body@.len() as u32) + body@,
            match result {
                Err(Error::Daemon(name)) => final(self).ready() && final(self).next_id() == old(self).next_id() + 1
                    && 0 < name@.len() < MAX_PAYLOAD
                    && forall|i: int| 0 <= i < name@.len() ==> name@[i] != 0,
                Err(Error::TooLarge) => final(self).next_id() == old(self).next_id() && final(self).ready() == old(self).ready(),
                Err(_) => !final(self).ready() && final(self).next_id() == 0,
                Ok(_) => true,
            },
    {
        let Some(id) = self.next else { return Err(Error::Poisoned); };
        if id == 0 { self.next = None; return Err(Error::Poisoned); }
        if body.len() > MAX_PAYLOAD {
            return Err(Error::TooLarge);
        }
        let Some(next) = id.checked_add(1) else {
            self.next = None;
            return Err(Error::Poisoned);
        };
        // Any failure after publication may leave an outstanding reply or a
        // partially consumed message. Only a complete daemon reply clears this.
        self.next = None;
        let mut header = encode_header(operation as u32, id, transaction, body.len() as u32);
        let ghost request = header@;
        write_all(transport, &header)?;
        write_all(transport, body)?;
        let mut remaining = MAX_WATCHES;
        loop
            invariant self.next is None, next == id + 1, id == old(self).next_id(),
                next > 0, remaining <= MAX_WATCHES, body@.len() <= MAX_PAYLOAD,
                transport.sent() == old(transport).sent() + request + body@,
                request == header_bytes(operation as u32, id, transaction, body.len() as u32),
            decreases remaining + 1,
        {
            let ghost before = transport.received();
            read_all(transport, &mut header)?;
            let ghost response_header = header@;
            let kind = word(&header, 0);
            let length = word(&header, 12) as usize;
            if length > MAX_PAYLOAD {
                return Err(Error::Protocol);
            }
            let mut reply = zeros(length);
            read_all(transport, &mut reply)?;
            if kind == 15 {
                if remaining == 0 { return Err(Error::Protocol); }
                remaining -= 1;
                let Some(split) = watch_split(&reply) else { return Err(Error::Protocol); };
                let path = slice_subrange(&reply, 0, split);
                let token = slice_subrange(&reply, split + 1, reply.len() - 1);
                if !watch.event(path, token) { return Err(Error::Protocol); }
                continue;
            }
            if word(&header, 4) != id || word(&header, 8) != transaction {
                return Err(Error::Protocol);
            }
            if kind == 16 {
                if !daemon_error(&reply) {
                    return Err(Error::Protocol);
                }
                reply.pop();
                self.next = Some(next);
                return Err(Error::Daemon(reply));
            }
            if kind != operation as u32 {
                return Err(Error::Protocol);
            }
            self.next = Some(next);
            assert(self.ready());
            assert(self.next_id() == old(self).next_id() + 1);
            assert(reply@.len() <= MAX_PAYLOAD);
            assert(transport.received() == before + response_header + reply@);
            assert(transport.received().subrange(before.len() as int, before.len() as int + 16) =~= response_header);
            assert(transport.received().len() == before.len() + 16 + reply@.len());
            assert(transport.received().subrange(before.len() as int + 16, transport.received().len() as int) =~= reply@);
            assert(vstd::bytes::spec_u32_from_le_bytes(response_header.subrange(0, 4)) == operation as u32);
            assert(vstd::bytes::spec_u32_from_le_bytes(response_header.subrange(4, 8)) == id);
            assert(vstd::bytes::spec_u32_from_le_bytes(response_header.subrange(8, 12)) == transaction);
            assert(vstd::bytes::spec_u32_from_le_bytes(response_header.subrange(12, 16)) == reply@.len());
            assert(transport.received().subrange(before.len() as int, before.len() as int + 4) =~= response_header.subrange(0,4));
            assert(transport.received().subrange(before.len() as int + 4, before.len() as int + 8) =~= response_header.subrange(4,8));
            assert(transport.received().subrange(before.len() as int + 8, before.len() as int + 12) =~= response_header.subrange(8,12));
            assert(transport.received().subrange(before.len() as int + 12, before.len() as int + 16) =~= response_header.subrange(12,16));
            assert(accepted(transport.received(), operation as u32, id, transaction, reply@));
            return Ok(reply);
        }
    }
}

/// Publish every byte while rejecting invalid progress. Each successful step
/// consumes at least one byte, so fragmented streams have bounded work.
fn write_all<T: Transport>(transport: &mut T, bytes: &[u8]) -> (result: Result<(), Error<T::Error>>)
    ensures match result { Err(Error::Transport(_)) | Err(Error::Protocol) | Ok(_) => true, _ => false },
        result is Ok ==> final(transport).sent() == old(transport).sent() + bytes@,
        final(transport).received() == old(transport).received(),
{
    let mut offset = 0;
    while offset < bytes.len()
        invariant offset <= bytes.len(),
            transport.sent() == old(transport).sent() + bytes@.subrange(0, offset as int),
            transport.received() == old(transport).received(),
        decreases bytes.len() - offset,
    {
        let size = match transport.write(slice_subrange(bytes, offset, bytes.len())) { Ok(size) => size, Err(error) => return Err(Error::Transport(error)) };
        if size == 0 || size > bytes.len() - offset { return Err(Error::Protocol); }
        offset += size;
    }
    Ok(())
}

/// Consume a private snapshot of exactly the requested length. Runtime reads
/// are trusted to implement their byte-copy effect, but progress is checked.
fn read_all<T: Transport>(transport: &mut T, bytes: &mut [u8]) -> (result: Result<(), Error<T::Error>>)
    ensures match result { Err(Error::Transport(_)) | Err(Error::Protocol) | Ok(_) => true, _ => false },
        final(bytes)@.len() == old(bytes)@.len(),
        final(transport).sent() == old(transport).sent(),
        result is Ok ==> final(transport).received() == old(transport).received() + final(bytes)@,
{
    let mut offset = 0;
    let length = bytes.len();
    while offset < length
        invariant offset <= length, bytes@.len() == length, length == old(bytes)@.len(),
            transport.sent() == old(transport).sent(),
            transport.received() == old(transport).received() + bytes@.subrange(0, offset as int),
        decreases length - offset,
    {
        let size = match transport.read(&mut bytes[offset..length]) { Ok(size) => size, Err(error) => return Err(Error::Transport(error)) };
        if size == 0 || size > length - offset { return Err(Error::Protocol); }
        offset += size;
    }
    Ok(())
}

/// Length of a text reply after removing only terminal NUL delimiters.
/// UTF-8 interpretation remains the runtime's standard-library boundary.
pub fn text_length(bytes: &[u8]) -> (length: usize)
    ensures length <= bytes@.len(),
        forall|i: int| length <= i < bytes@.len() ==> bytes@[i] == 0,
        length > 0 ==> bytes@[length - 1] != 0,
{
    let mut length = bytes.len();
    while length > 0
        invariant length <= bytes@.len(),
            forall|i: int| length <= i < bytes@.len() ==> bytes@[i] == 0,
        decreases length,
    {
        if bytes[length - 1] != 0 { return length; }
        length -= 1;
    }
    length
}

/// Allocate a protocol-bounded zeroed private buffer without unchecked indexing.
fn zeros(length: usize) -> (bytes: Vec<u8>)
    requires length <= MAX_PAYLOAD,
    ensures bytes@.len() == length,
{
    let mut bytes = Vec::with_capacity(length);
    while bytes.len() < length
        invariant bytes@.len() <= length,
        decreases length - bytes.len(),
    { bytes.push(0); }
    bytes
}

/// Exact XenStore header bytes, independent of the executable encoder.
pub open spec fn header_bytes(kind: u32, id: u32, tx: u32, length: u32) -> Seq<u8> {
    vstd::bytes::spec_u32_to_le_bytes(kind) + vstd::bytes::spec_u32_to_le_bytes(id)
        + vstd::bytes::spec_u32_to_le_bytes(tx) + vstd::bytes::spec_u32_to_le_bytes(length)
}

/// Success means the returned bytes are precisely the consumed final frame's
/// payload and its bounded length and identity fields match this request.
pub open spec fn accepted(stream: Seq<u8>, kind: u32, id: u32, tx: u32, payload: Seq<u8>) -> bool {
    let start = stream.len() - 16 - payload.len();
    &&& start >= 0
    &&& payload.len() <= MAX_PAYLOAD
    &&& stream.subrange(start + 16, stream.len() as int) == payload
    &&& vstd::bytes::spec_u32_from_le_bytes(stream.subrange(start, start + 4)) == kind
    &&& vstd::bytes::spec_u32_from_le_bytes(stream.subrange(start + 4, start + 8)) == id
    &&& vstd::bytes::spec_u32_from_le_bytes(stream.subrange(start + 8, start + 12)) == tx
    &&& vstd::bytes::spec_u32_from_le_bytes(stream.subrange(start + 12, start + 16)) == payload.len()
}

/// Encode the four fields without exposing unchecked offsets to callers.
fn encode_header(kind: u32, id: u32, tx: u32, length: u32) -> (header: [u8; 16])
    ensures header@ == header_bytes(kind, id, tx, length),
{
    let mut header = [0; 16];
    put_word(&mut header, 0, kind);
    put_word(&mut header, 4, id);
    put_word(&mut header, 8, tx);
    put_word(&mut header, 12, length);
    assert(header@ =~= header_bytes(kind, id, tx, length));
    header
}

/// Encode one little-endian word in a checked header field.
fn put_word(header: &mut [u8; 16], offset: usize, value: u32)
    requires offset <= 12,
    ensures final(header)@.subrange(offset as int, offset + 4) == vstd::bytes::spec_u32_to_le_bytes(value),
        forall|i: int| 0 <= i < 16 && !(offset <= i < offset + 4) ==> final(header)@[i] == old(header)@[i],
{
    let bytes = u32_to_le_bytes(value);
    let mut i = 0;
    while i < 4
        invariant i <= 4, offset <= 12,
            bytes@.len() == 4,
            forall|j: int| 0 <= j < i ==> header@[offset + j] == bytes@[j],
            forall|j: int| 0 <= j < 16 && !(offset <= j < offset + i) ==> header@[j] == old(header)@[j],
        decreases 4 - i,
    { header[offset + i] = bytes[i]; i += 1; }
    assert(header@.subrange(offset as int, offset + 4) =~= bytes@);
}

/// Decode only an in-bounds four-byte header field.
fn word(header: &[u8; 16], offset: usize) -> (value: u32)
    requires offset <= 12,
    ensures value == vstd::bytes::spec_u32_from_le_bytes(header@.subrange(offset as int, offset + 4)),
{ u32_from_le_bytes(slice_subrange(header, offset, offset + 4)) }

/// Accept exactly two NUL-terminated fields and return their separator.
fn watch_split(bytes: &[u8]) -> (split: Option<usize>)
    ensures match split {
        Some(i) => i + 1 < bytes@.len() && bytes@[i as int] == 0
            && bytes@[bytes@.len()-1] == 0
            && forall|j: int| 0 <= j < bytes@.len()-1 && j != i ==> bytes@[j] != 0,
        None => !(exists|i: int| 0 <= i && i + 1 < bytes@.len() && #[trigger] bytes@[i] == 0
            && bytes@[bytes@.len()-1] == 0
            && forall|j: int| 0 <= j < bytes@.len()-1 && j != i ==> bytes@[j] != 0),
    },
{
    if bytes.len() < 2 { return None; }
    if bytes[bytes.len()-1] != 0 { return None; }
    let mut split: Option<usize> = None;
    let mut i = 0;
    while i < bytes.len()-1
        invariant i <= bytes.len()-1, bytes@.len() >= 2, bytes@[bytes@.len()-1] == 0,
            match split { Some(s) => s < i && bytes@[s as int] == 0
                && forall|j: int| 0 <= j < i && j != s ==> bytes@[j] != 0,
                None => forall|j: int| 0 <= j < i ==> bytes@[j] != 0 },
        decreases bytes.len()-1-i,
    {
        if bytes[i] == 0 {
            if split.is_some() { return None; }
            split = Some(i);
        }
        i += 1;
    }
    split
}

/// Accept one nonempty NUL-terminated portable daemon error name.
fn daemon_error(bytes: &[u8]) -> (valid: bool)
    ensures valid == (bytes@.len() >= 2 && bytes@[bytes@.len()-1] == 0
        && forall|j: int| 0 <= j < bytes@.len()-1 ==> bytes@[j] != 0),
{
    if bytes.len() < 2 { return false; }
    if bytes[bytes.len()-1] != 0 { return false; }
    let mut i = 0;
    while i < bytes.len()-1
        invariant i <= bytes.len()-1,
            forall|j: int| 0 <= j < i ==> bytes@[j] != 0,
        decreases bytes.len()-1-i,
    { if bytes[i] == 0 { return false; } i += 1; }
    true
}

} // verus!

#[cfg(test)]
mod tests;
