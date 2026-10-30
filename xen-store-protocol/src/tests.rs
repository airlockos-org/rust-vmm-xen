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
