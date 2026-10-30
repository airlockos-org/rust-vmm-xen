//! Stream-level scenarios independent of a Xen mapping or Hermit scheduler.

extern crate std;

use alloc::vec;
use std::collections::VecDeque;

use super::*;

/// Fragmented daemon stream with captured request bytes and injected failures.
struct Stream {
    /// Remaining daemon bytes; EOF models an interrupted response.
    incoming: VecDeque<u8>,
    /// Captured bytes sent by the client.
    outgoing: Vec<u8>,
    /// Maximum progress per transport call, smaller than headers in some tests.
    chunk: usize,
}

impl Stream {
    /// Create a stream whose chunks exercise fragmented header and body
    /// handling.
    fn new(messages: &[Vec<u8>], chunk: usize) -> Self {
        Self {
            incoming: messages.iter().flatten().copied().collect(),
            outgoing: Vec::new(),
            chunk,
        }
    }
}

impl Transport for Stream {
    type Error = ();

    fn write(&mut self, bytes: &[u8]) -> Result<usize, ()> {
        let size = bytes.len().min(self.chunk);
        self.outgoing.extend_from_slice(&bytes[..size]);
        Ok(size)
    }

    fn read(&mut self, bytes: &mut [u8]) -> Result<usize, ()> {
        if self.incoming.is_empty() {
            return Err(());
        }
        let size = bytes.len().min(self.chunk).min(self.incoming.len());
        for byte in &mut bytes[..size] {
            *byte = self.incoming.pop_front().unwrap();
        }
        Ok(size)
    }
}

/// Encode a daemon message; payload is deliberately allowed to be malformed.
fn message(kind: u32, id: u32, transaction: u32, body: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for word in [kind, id, transaction, body.len() as u32] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes.extend_from_slice(body);
    bytes
}

/// Protocol-sized bodies stream across ring-sized boundaries in both
/// directions.
#[test]
fn full_payload_and_directory_nuls_survive_fragmentation() {
    let body = vec![b'x'; MAX_PAYLOAD];
    let response = message(11, 1, 42, &body);
    let mut stream = Stream::new(&[response], 7);
    let mut client = Client::new();
    assert_eq!(
        client.exchange(&mut stream, Operation::Write, 42, &body, |_| false),
        Ok(body.clone())
    );
    assert_eq!(stream.outgoing, message(11, 1, 42, &body));
    stream.incoming.extend(message(1, 2, 0, b"0\0vif\0"));
    assert_eq!(
        client.exchange(&mut stream, Operation::Directory, 0, b"device\0", |_| false),
        Ok(b"0\0vif\0".to_vec())
    );
}

/// Interleaved watches retain their paths/tokens and do not consume reply IDs.
#[test]
fn watches_precede_transaction_reply() {
    let mut stream = Stream::new(
        &[
            message(15, 0, 0, b"device/vif/0/state\0net\0"),
            message(7, 1, 99, b"OK\0"),
        ],
        3,
    );
    let mut events = Vec::new();
    assert_eq!(
        Client::new().exchange(
            &mut stream,
            Operation::TransactionEnd,
            99,
            b"T\0",
            |event| {
                events.push((event.path.to_vec(), event.token.to_vec()));
                true
            }
        ),
        Ok(b"OK\0".to_vec())
    );
    assert_eq!(
        events,
        vec![(b"device/vif/0/state".to_vec(), b"net".to_vec())]
    );
}

/// A transaction conflict is a complete response, allowing an explicit retry.
#[test]
fn conflict_does_not_poison_connection() {
    let mut stream = Stream::new(
        &[message(16, 1, 9, b"EAGAIN\0"), message(6, 2, 0, b"10\0")],
        16,
    );
    let mut client = Client::new();
    assert_eq!(
        client.exchange(&mut stream, Operation::TransactionEnd, 9, b"T\0", |_| false),
        Err(Error::Daemon(b"EAGAIN".to_vec()))
    );
    assert_eq!(
        client.exchange(&mut stream, Operation::TransactionStart, 0, b"\0", |_| {
            false
        }),
        Ok(b"10\0".to_vec())
    );
}

/// Contradictory identities and malformed messages cannot resynchronize
/// silently.
#[test]
fn malformed_or_interrupted_replies_poison_connection() {
    let messages = [
        message(2, 7, 0, b"value"),
        message(2, 1, 1, b"value"),
        message(11, 1, 0, b"value"),
        message(16, 1, 0, b"ENOENT"),
        message(16, 1, 0, b"E\0NOENT\0"),
        message(16, 1, 0, b""),
        message(15, 0, 0, b"path\0token"),
        message(15, 0, 0, b"path\0token\0extra\0"),
        message(2, 1, 0, &vec![0; MAX_PAYLOAD + 1]),
        message(2, 1, 0, b"value")[..18].to_vec(),
    ];
    for response in messages {
        let mut stream = Stream::new(&[response], 5);
        let mut client = Client::new();
        assert!(client
            .exchange(&mut stream, Operation::Read, 0, b"path\0", |_| true)
            .is_err());
        let published = stream.outgoing.len();
        assert_eq!(
            client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| true),
            Err(Error::Poisoned)
        );
        assert_eq!(stream.outgoing.len(), published);
    }
}

/// Caller event capacity and progress contracts fail closed without busy loops.
#[test]
fn watch_overflow_and_zero_progress_poison() {
    for response in [message(15, 0, 0, b"path\0token\0")] {
        let mut stream = Stream::new(&[response], 16);
        let mut client = Client::new();
        assert_eq!(
            client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| false),
            Err(Error::Protocol)
        );
        assert_eq!(
            client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| false),
            Err(Error::Poisoned)
        );
    }
    let mut stream = Stream::new(&[], 0);
    assert_eq!(
        Client::new().exchange(&mut stream, Operation::Read, 0, b"path\0", |_| false),
        Err(Error::Protocol)
    );
}

/// Unpublished oversized requests remain retryable without consuming an ID.
#[test]
fn local_limits_do_not_publish() {
    let mut stream = Stream::new(&[message(2, 1, 0, b"value")], 16);
    let mut client = Client::new();
    assert_eq!(
        client.exchange(
            &mut stream,
            Operation::Read,
            0,
            &vec![0; MAX_PAYLOAD + 1],
            |_| false
        ),
        Err(Error::TooLarge)
    );
    assert!(stream.outgoing.is_empty());
    assert_eq!(
        client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| false),
        Ok(b"value".to_vec())
    );
}

/// A continuous watch flood is bounded even if the transport always progresses.
#[test]
fn watch_flood_poisoning_is_bounded() {
    let events = alloc::vec![message(15, 0, 0, b"path\0token\0"); MAX_WATCHES + 1];
    let mut stream = Stream::new(&events, 64);
    let mut client = Client::new();
    let mut delivered = 0;
    assert_eq!(
        client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| {
            delivered += 1;
            true
        }),
        Err(Error::Protocol)
    );
    assert_eq!(delivered, MAX_WATCHES);
    assert_eq!(
        client.exchange(&mut stream, Operation::Read, 0, b"path\0", |_| true),
        Err(Error::Poisoned)
    );
}
