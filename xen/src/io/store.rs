//! Bounded XenStore guest protocol over a caller-owned byte transport.
//!
//! Layout and operation numbers follow Xen 4.20.4 public/io/xs_wire.h (MIT,
//! Copyright 2005 Rusty Russell, IBM). Unlike a ring-sized exchange, this
//! client streams messages up to the protocol's 4096-byte payload limit.
//! Transport owns mapping, notification, deadlines and exclusive access to the
//! domain connection.

extern crate alloc;

use alloc::vec::Vec;
use core::convert::TryInto;

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
    Transport(E),
    /// Contradictory identity, malformed framing, or watch overflow at the
    /// caller.
    Protocol,
    /// Request exceeds the wire bound; no request was published.
    TooLarge,
    /// A previous ambiguous exchange prohibits further use of this connection.
    Poisoned,
    /// Daemon error name, without its terminal NUL (for example EAGAIN).
    Daemon(Vec<u8>),
}

/// Exclusive byte stream with bounded blocking supplied by the runtime.
///
/// Implementations must return positive progress no greater than the supplied
/// slice, or an error. They must enforce an absolute deadline, including when
/// each call makes progress. Notify the peer as needed after consuming bytes.
pub trait Transport {
    /// Platform-specific failure, normally including timeout and corrupt
    /// indices.
    type Error;

    /// Publish some request bytes, waiting for ring capacity when necessary.
    fn write(&mut self, bytes: &[u8]) -> Result<usize, Self::Error>;

    /// Copy some response bytes into private memory, waiting when necessary.
    fn read(&mut self, bytes: &mut [u8]) -> Result<usize, Self::Error>;
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
    /// Next request identity; exhaustion permanently poisons the connection.
    next: u32,
    /// Ambiguous failure prohibits consuming or publishing further messages.
    poisoned: bool,
}

impl Default for Client {
    fn default() -> Self {
        Self::new()
    }
}

impl Client {
    /// Create the sole client for a freshly provisioned connection.
    pub const fn new() -> Self {
        Self {
            next: 1,
            poisoned: false,
        }
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
    pub fn exchange<T: Transport>(
        &mut self,
        transport: &mut T,
        operation: Operation,
        transaction: u32,
        body: &[u8],
        mut watch: impl FnMut(Watch<'_>) -> bool,
    ) -> Result<Vec<u8>, Error<T::Error>> {
        if self.poisoned {
            return Err(Error::Poisoned);
        }
        if body.len() > MAX_PAYLOAD {
            return Err(Error::TooLarge);
        }
        let id = self.next;
        let Some(next) = id.checked_add(1) else {
            self.poisoned = true;
            return Err(Error::Poisoned);
        };
        self.next = next;
        // Any failure after publication may leave an outstanding reply or a
        // partially consumed message. Only a complete daemon reply clears this.
        self.poisoned = true;
        let mut header = [0; 16];
        for (index, value) in [operation as u32, id, transaction, body.len() as u32]
            .iter()
            .enumerate()
        {
            header[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        write_all(transport, &header)?;
        write_all(transport, body)?;
        loop {
            read_all(transport, &mut header)?;
            let word = |offset| u32::from_le_bytes(header[offset..offset + 4].try_into().unwrap());
            let kind = word(0);
            let length = word(12) as usize;
            if length > MAX_PAYLOAD {
                return Err(Error::Protocol);
            }
            let mut reply = alloc::vec![0; length];
            read_all(transport, &mut reply)?;
            if kind == 15 {
                // XS_WATCH_EVENT is asynchronous: req_id/tx_id are unspecified.
                let mut strings = reply.split(|byte| *byte == 0);
                let path = strings.next().ok_or(Error::Protocol)?;
                let token = strings.next().ok_or(Error::Protocol)?;
                if strings.next() != Some(&[][..])
                    || strings.next().is_some()
                    || !watch(Watch { path, token })
                {
                    return Err(Error::Protocol);
                }
                continue;
            }
            if word(4) != id || word(8) != transaction {
                return Err(Error::Protocol);
            }
            if kind == 16 {
                if reply.last() != Some(&0) || reply[..reply.len() - 1].contains(&0) {
                    return Err(Error::Protocol);
                }
                reply.pop();
                if reply.is_empty() {
                    return Err(Error::Protocol);
                }
                self.poisoned = false;
                return Err(Error::Daemon(reply));
            }
            if kind != operation as u32 {
                return Err(Error::Protocol);
            }
            self.poisoned = false;
            return Ok(reply);
        }
    }
}

/// Publish every byte while rejecting a broken transport progress contract.
fn write_all<T: Transport>(transport: &mut T, mut bytes: &[u8]) -> Result<(), Error<T::Error>> {
    while !bytes.is_empty() {
        let size = transport.write(bytes).map_err(Error::Transport)?;
        if size == 0 || size > bytes.len() {
            return Err(Error::Protocol);
        }
        bytes = &bytes[size..];
    }
    Ok(())
}

/// Consume exactly one frame part without borrowing foreign memory.
fn read_all<T: Transport>(transport: &mut T, mut bytes: &mut [u8]) -> Result<(), Error<T::Error>> {
    while !bytes.is_empty() {
        let size = transport.read(bytes).map_err(Error::Transport)?;
        if size == 0 || size > bytes.len() {
            return Err(Error::Protocol);
        }
        bytes = &mut bytes[size..];
    }
    Ok(())
}

#[cfg(test)]
mod tests;
