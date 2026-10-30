#![no_std]
#![warn(missing_docs)]
//! Verified framing for single-page Xen netif packets, following Xen 4.20.4
//! public/io/netif.h and ring.h (MIT; original interface Keir Fraser
//! 2003–2004). No driver code is translated from Mini-OS or Mirage. These are
//! standard descriptor layouts, not an Airlock packet protocol or IP/firewall
//! policy.
//!
//! The initial profile disables scatter/gather, GSO, checksum completion,
//! split event channels and multiqueue. RX checksum-validation hints do not
//! authorize traffic. All descriptors are private snapshots before parsing.
//! Runtime grants, volatile copying and notification are explicit effect
//! boundaries; a proved range does not establish that a grant was revoked.

use vstd::prelude::*;

pub mod bus;
pub mod identity;
pub mod loans;
pub mod queue;

verus! {

/// Fixed size of a Xen grant page and the maximum single-page packet.
pub const PAGE: usize = 4096;
/// Netif shared ring header occupies the first cache line.
pub const HEADER: usize = 64;
/// Both native TX and RX rings have 256 entries in a grant page.
pub const SLOTS: u32 = 256;

/// Malformed or unsupported peer descriptors; never used as unchecked offsets.
#[derive(Debug, PartialEq, Eq)]
pub enum Invalid {
    /// Response identity does not belong to the posted buffer.
    Identity,
    /// Fragment, extra-info or checksum-completion flags were not negotiated.
    Flags,
    /// Length/offset would access outside the one authorized grant page.
    Bounds,
    /// An unrecognized completion status cannot release an outstanding request.
    Status,
    /// Ring indices contradict private ownership or outstanding requests.
    Counter,
}

/// Mathematical little-endian word, independently of the executable decoder.
pub open spec fn word16(bytes: Seq<u8>, at: int) -> int
    recommends 0 <= at && at + 2 <= bytes.len(),
{ bytes[at] as int + bytes[at+1] as int * 256 }

/// Mathematical little-endian grant reference.
pub open spec fn word32(bytes: Seq<u8>, at: int) -> int
    recommends 0 <= at && at + 4 <= bytes.len(),
{ word16(bytes, at) + word16(bytes, at+2) * 65536 }

/// Decode a bounded unsigned ABI field without unchecked casts or indexing.
fn get16(bytes: &[u8], at: usize) -> (word: u16)
    requires bytes@.len() >= 2, at <= bytes@.len()-2,
    ensures word == word16(bytes@, at as int),
{ bytes[at] as u16 + bytes[at+1] as u16 * 256 }

/// Write one ABI field while preserving unrelated bytes.
fn put16(bytes: &mut [u8], at: usize, word: u16)
    requires old(bytes)@.len() >= 2, at <= old(bytes)@.len()-2,
    ensures final(bytes)@.len() == old(bytes)@.len(),
        word16(final(bytes)@, at as int) == word,
        forall|i: int| 0 <= i < final(bytes)@.len() && !(at <= i < at+2)
            ==> final(bytes)@[i] == old(bytes)@[i],
{
    bytes[at] = (word % 256) as u8;
    bytes[at+1] = (word / 256) as u8;
}

/// Encode a grant reference through two checked little-endian words.
fn put32(bytes: &mut [u8], at: usize, word: u32)
    requires 4 <= old(bytes)@.len() <= usize::MAX, at <= old(bytes)@.len()-4,
    ensures final(bytes)@.len() == old(bytes)@.len(), word32(final(bytes)@, at as int) == word,
        forall|i: int| 0 <= i < final(bytes)@.len() && !(at <= i < at+4)
            ==> final(bytes)@[i] == old(bytes)@[i],
{
    let upper = at + 2;
    put16(bytes, at, (word % 65536) as u16);
    put16(bytes, upper, (word / 65536) as u16);
}

/// Encode a normal single-page TX request. The caller copies packet bytes
/// before publishing its grant and the request producer, using this exact body.
pub fn tx_request(grant: u32, id: u16, length: usize) -> (request: Option<[u8; 12]>)
    ensures match request {
        Some(bytes) => 0 < length <= PAGE && word32(bytes@, 0) == grant
            && word16(bytes@, 4) == 0 && word16(bytes@, 6) == 0
            && word16(bytes@, 8) == id && word16(bytes@, 10) == length,
        None => length == 0 || length > PAGE,
    },
{
    if length == 0 || length > PAGE { return None; }
    let mut bytes = [0; 12];
    put32(&mut bytes, 0, grant);
    put16(&mut bytes, 8, id);
    put16(&mut bytes, 10, length as u16);
    Some(bytes)
}

/// Encode one receive-buffer request with explicit zero ABI padding.
pub fn rx_request(grant: u32, id: u16) -> (bytes: [u8; 8])
    ensures word16(bytes@, 0) == id, word16(bytes@, 2) == 0, word32(bytes@, 4) == grant,
{
    let mut bytes = [0; 8];
    put16(&mut bytes, 0, id);
    put32(&mut bytes, 4, grant);
    bytes
}

/// Validated packet range in one exclusively owned/revoked data page.
/// Construction proves bounds only; the runtime must establish page ownership
/// before following these offsets or handing bytes to application code.
pub struct Frame {
    /// First packet byte within the grant page.
    offset: usize,
    /// Packet bytes accepted from the private descriptor snapshot.
    length: usize,
}

impl Frame {
    /// Every authorized byte remains inside the same grant page.
    pub closed spec fn valid(&self) -> bool { self.length > 0 && self.offset + self.length <= PAGE }

    /// Descriptor-provided first byte, after validation.
    pub closed spec fn start(&self) -> usize { self.offset }

    /// Number of packet bytes, after validation.
    pub closed spec fn size(&self) -> usize { self.length }

    /// Check the range before accepting a completion into the loan machine.
    pub(crate) fn bounded(&self) -> (valid: bool)
        ensures valid == self.valid(),
    { self.length > 0 && self.length <= PAGE && self.offset <= PAGE-self.length }

    /// Number of bytes the runtime may copy after successful grant revocation.
    pub fn len(&self) -> (length: usize)
        requires self.valid(),
        ensures length == self.size(), 0 < length <= PAGE,
    { self.length }

    /// A frame is never empty; malformed zero-length packets are dropped.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.valid(),
        ensures !empty,
    { false }

    /// Authorize one checked byte offset, never a foreign Rust slice.
    pub fn byte(&self, index: usize) -> (offset: Option<usize>)
        requires self.valid(),
        ensures match offset {
            Some(value) => index < self.size() && value == self.start()+index && value < PAGE,
            None => index >= self.size(),
        },
    {
        if index >= self.length { None } else { Some(self.offset + index) }
    }
}

/// RX completion either carries one validated packet or reports a peer drop.
pub enum Receive {
    /// A bounded packet snapshot; ownership must still be reclaimed by runtime.
    Packet(/// Validated offset and length, without authority to access a mapping.
        Frame),
    /// Zero/negative status carries no packet bytes.
    Dropped,
}

/// Validate an RX response for a posted buffer. Only flags zero or
/// data_validated are supported; neither grants firewall/checksum authority.
pub fn rx_response(bytes: &[u8; 8], expected: u16) -> (result: Result<Receive, Invalid>)
    ensures match result {
        Ok(Receive::Packet(frame)) => frame.valid() && word16(bytes@, 0) == expected
            && word16(bytes@, 4) <= 1 && frame.start() == word16(bytes@, 2)
            && frame.size() == word16(bytes@, 6),
        Ok(Receive::Dropped) => word16(bytes@, 0) == expected && word16(bytes@, 4) <= 1
            && (word16(bytes@, 6) == 0 || word16(bytes@, 6) >= 32768),
        Err(_) => !(word16(bytes@, 0) == expected && word16(bytes@, 4) <= 1
            && ((word16(bytes@, 6) == 0 || word16(bytes@, 6) >= 32768)
                || (0 < word16(bytes@, 6) && word16(bytes@, 2)+word16(bytes@, 6) <= PAGE))),
    },
{
    if get16(bytes, 0) != expected { return Err(Invalid::Identity); }
    if get16(bytes, 4) > 1 { return Err(Invalid::Flags); }
    let size = get16(bytes, 6);
    if size == 0 || size >= 32768 { return Ok(Receive::Dropped); }
    let offset = get16(bytes, 2) as usize;
    let length = size as usize;
    if length > PAGE || offset > PAGE-length { return Err(Invalid::Bounds); }
    Ok(Receive::Packet(Frame { offset, length }))
}

/// Validate one TX response. False is an explicit peer drop/error, not proof
/// that a packet reached the network. Auxiliary/null replies were not requested.
pub fn tx_response(bytes: &[u8; 4], expected: u16) -> (result: Result<bool, Invalid>)
    ensures match result {
        Ok(sent) => word16(bytes@, 0) == expected
            && if sent { word16(bytes@, 2) == 0 }
                else { word16(bytes@, 2) == 65534 || word16(bytes@, 2) == 65535 },
        Err(_) => !(word16(bytes@, 0) == expected
            && (word16(bytes@, 2) == 0 || word16(bytes@, 2) == 65534 || word16(bytes@, 2) == 65535)),
    },
{
    if get16(bytes, 0) != expected { return Err(Invalid::Identity); }
    let status = get16(bytes, 2);
    if status == 0 { return Ok(true); }
    if status == 65534 || status == 65535 { return Ok(false); }
    Err(Invalid::Status)
}

}
