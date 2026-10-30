//! Executable boundary cases complement the proof of the production bodies.

extern crate std;

use super::*;

/// Counts effects so identity exhaustion can be checked before publication.
struct Effects {
    /// Number of transport calls attempted by the core.
    calls: usize,
}

impl Transport for Effects {
    type Error = ();

    fn read(&mut self, _: &mut [u8]) -> Result<usize, ()> {
        self.calls += 1;
        Err(())
    }

    fn write(&mut self, _: &[u8]) -> Result<usize, ()> {
        self.calls += 1;
        Err(())
    }
}

/// Sink unused by operations rejected before touching the transport.
struct Sink;

impl WatchSink for Sink {
    fn event(&mut self, _: &[u8], _: &[u8]) -> bool {
        false
    }
}

/// Request IDs cannot wrap or cause an exhausted connection to publish bytes.
#[test]
fn request_identity_exhaustion_has_no_effects() {
    let mut client = Client {
        next: Some(u32::MAX),
    };
    let mut effects = Effects { calls: 0 };
    assert_eq!(
        client.exchange(&mut effects, Operation::Read, 0, b"path\0", &mut Sink),
        Err(Error::Poisoned)
    );
    assert_eq!(
        client.exchange(&mut effects, Operation::Read, 0, b"path\0", &mut Sink),
        Err(Error::Poisoned)
    );
    assert_eq!(effects.calls, 0);
}

/// Valid counter rollover yields exact offsets and next publication indices;
/// impossible occupancy and peer changes to local indices are rejected.
#[test]
fn ring_rollover_and_local_counter_tampering() {
    let start = u32::MAX - 1;
    let plan = ring::send(start, start, start, 4).unwrap();
    assert_eq!(plan.len(), 4);
    assert_eq!(plan.offset(0), Some(1022));
    assert_eq!(plan.offset(2), Some(0));
    assert_eq!(plan.offset(4), None);
    assert_eq!(plan.finish(), 2);
    let plan = ring::receive(start, start, 2, 4).unwrap();
    assert_eq!(plan.offset(0), Some(2046));
    assert_eq!(plan.offset(2), Some(1024));
    assert_eq!(plan.finish(), 2);
    assert!(ring::send(0, 1, 0, 1).is_none());
    assert!(ring::receive(0, 1, 1, 1).is_none());
    assert!(ring::send(1025, 1025, 0, 1).is_none());
    assert!(ring::receive(0, 0, 1025, 1).is_none());
    assert!(ring::send(1024, 1024, 0, 1).unwrap().is_empty());
    assert!(ring::receive(1, 1, 1, 1).unwrap().is_empty());
}

/// Failed or interrupted initialization cannot be retried, while an established
/// connection can be observed repeatedly without consuming another permission.
#[test]
fn domain_initialization_is_monotonic() {
    let mut interrupted = domain::Gate::new();
    assert!(interrupted.begin());
    assert!(!interrupted.usable());
    assert!(!interrupted.begin());
    assert!(!interrupted.finish(false));
    assert!(!interrupted.begin());
    assert!(!interrupted.finish(true));

    let mut ready = domain::Gate::new();
    assert!(ready.begin());
    assert!(ready.finish(true));
    assert!(ready.usable());
    assert!(!ready.begin());
    assert!(ready.usable());
    ready.poison();
    assert!(!ready.usable());
    assert!(!ready.begin());
    assert!(!ready.finish(true));
}

/// Transaction IDs preserve the full u32 range and reject ambiguous grammar.
#[test]
fn transaction_id_boundaries_and_explicit_end() {
    let id = transaction::Id::parse(b"4294967295\0").unwrap();
    assert_eq!(id.wire(), u32::MAX);
    assert_eq!(id.finish(false), (u32::MAX, [b'F', 0]));
    let id = transaction::Id::parse(b"1\0").unwrap();
    assert_eq!(id.finish(true), (1, [b'T', 0]));
    for invalid in [
        b"".as_slice(),
        b"0\0",
        b"01\0",
        b"+1\0",
        b"1",
        b"4294967296\0",
        b"1\x0000\0",
        b"-1\0",
        b"1x\0",
    ] {
        assert!(transaction::Id::parse(invalid).is_none());
    }
    assert!(transaction::acknowledged(b"OK\0"));
    assert!(!transaction::acknowledged(b"OK"));
    assert!(!transaction::acknowledged(b"OK\0extra"));
}

/// Notifications coalesce by retained label; late events cannot reach a
/// replacement, and forgotten keys remain charged against the admission limit.
#[test]
fn watch_lifetime_isolation_and_quarantined_capacity() {
    let mut inbox = watches::Inbox::new();
    let first = inbox.reserve().unwrap();
    let second = inbox.reserve().unwrap();
    let body = watches::Request::new(b"device/vif/0/state", b"1", &first).unwrap();
    assert_eq!(body.read_body(), b"device/vif/0/state\0");
    assert_eq!(body.bytes(), b"device/vif/0/state\x001\0");
    assert!(watches::Request::new(b"path\0injection", b"1", &first).is_none());
    assert!(watches::Request::new(b"path", b"2", &first).is_none());
    inbox.notify(b"1");
    inbox.notify(b"1");
    assert!(inbox.take(&first));
    assert!(!inbox.take(&first));
    assert!(!inbox.take(&second));
    assert!(inbox.release(first));
    let replacement = inbox.reserve().unwrap();
    assert_ne!(replacement.wire(), 1);
    inbox.notify(b"1");
    inbox.notify(b"01");
    inbox.notify(b"4294967296");
    assert!(!inbox.take(&replacement));
    inbox.notify(b"2");
    assert!(inbox.take(&second));
    // Dropping the key is not acknowledged daemon cleanup and frees no credit.
    {
        let _abandoned = second;
    }
    let mut retained = alloc::vec::Vec::new();
    while let Some(key) = inbox.reserve() {
        retained.push(key);
    }
    assert_eq!(retained.len(), watches::LIMIT - 2);
    assert!(inbox.reserve().is_none());
    assert!(inbox.release(replacement));
    assert!(inbox.reserve().is_some());
}
