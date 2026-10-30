//! Resource exhaustion, known-pending cleanup and stale owner isolation.
use xen_guest_core::resources::{Registry, Retirement};

/// Recycled slots/domain IDs acquire new local handles; failed or abandoned
/// release retains the original charge and cannot silently admit another owner.
#[test]
fn charged_retirement_and_stale_handle() {
    assert!(Registry::new(0, 1).is_none());
    assert!(Registry::new(65, 1).is_none());
    let mut registry = Registry::new(2, 1).unwrap();
    let first = registry.reserve(0).unwrap();
    let stale = first.handle();
    let slot = first.slot();
    let held = registry.reserve(42).unwrap();
    assert!(registry.reserve(43).is_none());
    let retained = match registry.release(held, false) {
        Err(token) => token,
        Ok(()) => panic!("unconfirmed release"),
    };
    let _abandoned = retained;
    assert!(registry.reserve(43).is_none());
    assert!(registry.release(first, true).is_ok());
    assert_eq!(registry.resolve(stale), None);
    let next = registry.reserve(0).unwrap();
    assert_eq!(next.slot(), slot);
    assert_ne!(next.handle(), stale);
    assert_eq!(registry.resolve(next.handle()), Some(slot));
    assert_eq!(registry.resolve(stale), None);
    assert!(registry.reserve(0x7ff0).is_none());
}

/// An identical handle/peer/slot from another origin cannot retire this owner.
#[test]
fn origin_isolation_and_known_pending_cleanup() {
    let mut a = Registry::new(1, 1).unwrap();
    let mut b = Registry::new(1, 2).unwrap();
    let first = a.reserve(42).unwrap();
    let second = b.reserve(42).unwrap();
    assert_eq!(first.handle(), second.handle());
    let first = match b.release(first, true) {
        Err(token) => token,
        Ok(()) => panic!("cross-origin retirement"),
    };
    assert!(b.reserve(43).is_none());
    assert!(a.release(first, true).is_ok());
    assert!(b.release(second, true).is_ok());

    let mut close = Retirement::new();
    assert!(close.usable());
    assert!(close.begin());
    assert!(!close.usable());
    assert!(close.begin());
    close.quarantine();
    assert!(!close.begin());
    assert!(!close.usable());
}
