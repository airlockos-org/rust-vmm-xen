//! Runtime origin binding for shared verified resource accounting. The core
//! manipulates logical labels; this adapter gives them an unforgeable owner in
//! safe Rust before any Xen effect is allowed through an owned Token.
//!
//! Trusted boundary: Rust's stable nonzero-sized static object identity and the
//! atomic compare/exchange's exclusivity. A static Origin can be claimed once,
//! never reset or recycled, even when its Registry or Tokens are dropped. Thus
//! origins cannot collide after teardown, and tokens cannot cross registries.
//! Core counter/slot/peer/release decisions execute the verified
//! implementation. The runtime still binds every real page/mapping/grant/event
//! to its token.

use core::sync::atomic::{AtomicBool, Ordering};

pub use verified::Retirement;
use xen_guest_core::resources as verified;

/// Stable, single-use runtime origin. Define one static for each resource
/// owner; its interior atomic makes distinct Origins occupy distinct mutable
/// storage.
pub struct Origin {
    /// Successful claim is terminal, including after registry/token
    /// destruction.
    claimed: AtomicBool,
}

impl Origin {
    /// Reserve a fresh origin without claiming resource or handle authority.
    pub const fn new() -> Self {
        Self {
            claimed: AtomicBool::new(false),
        }
    }

    /// Claim one accounting registry for this stable runtime owner. Invalid
    /// capacities are rejected by the core; a losing claim exposes no tokens.
    pub fn registry(&'static self, capacity: usize) -> Option<Registry> {
        let origin = core::ptr::from_ref(self).addr() as u64;
        let inner = verified::Registry::new(capacity, origin)?;
        self.claimed
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .ok()?;
        Some(Registry { inner })
    }
}

impl Default for Origin {
    fn default() -> Self {
        Self::new()
    }
}

/// One permanently origin-bound registry. Safe callers cannot select its label
/// or install a fabricated logical-core token into this runtime adapter.
pub struct Registry {
    /// Sole executable source of slot, peer and lifetime decisions.
    inner: verified::Registry,
}

impl Registry {
    /// Charge before a Xen effect. Abandonment retains the charge until
    /// teardown.
    pub fn reserve(&mut self, peer: u16) -> Option<Token> {
        self.inner.reserve(peer).map(|inner| Token { inner })
    }

    /// Whether a live/retiring charge already names this selected peer.
    pub fn contains_peer(&self, peer: u16) -> bool {
        self.inner.contains_peer(peer)
    }

    /// Resolve an existing handle under the caller's exclusive runtime guard.
    pub fn resolve(&self, handle: u32) -> Option<usize> {
        self.inner.resolve(handle)
    }

    /// Consume only this exact registry's token after confirmed release.
    /// Failure returns the original token and retains all accounting,
    /// including on drop.
    pub fn release(&mut self, token: Token, confirmed: bool) -> Result<(), Token> {
        self.inner
            .release(token.inner, confirmed)
            .map_err(|inner| Token { inner })
    }
}

/// Exclusive runtime resource token; no public constructor, conversion or Clone
/// can turn a peer claim or a pure-model label into this owner.
pub struct Token {
    /// Bound to the unique stable origin that issued it.
    inner: verified::Token,
}

impl Token {
    /// Fixed backing-page index selected before the resource was offered.
    pub fn slot(&self) -> usize {
        self.inner.slot()
    }

    /// Nonreused local label, independent of domain IDs and peer descriptors.
    pub fn handle(&self) -> u32 {
        self.inner.handle()
    }

    /// Exact controller-selected peer for this resource lifetime.
    pub fn peer(&self) -> u16 {
        self.inner.peer()
    }
}

#[cfg(test)]
mod tests {
    use super::Origin;

    /// Runtime origin claims enforce the pure core's uniqueness obligation,
    /// including after all tokens and the first registry have been dropped.
    #[test]
    fn runtime_origins_cannot_be_reclaimed_or_crossed() {
        static FIRST: Origin = Origin::new();
        static SECOND: Origin = Origin::new();
        assert!(FIRST.registry(0).is_none());
        let mut a = FIRST.registry(1).unwrap();
        assert!(FIRST.registry(1).is_none());
        let mut b = SECOND.registry(1).unwrap();
        let first = a.reserve(42).unwrap();
        let second = b.reserve(42).unwrap();
        let first = match b.release(first, true) {
            Err(token) => token,
            Ok(()) => panic!("cross-origin retirement"),
        };
        assert!(b.reserve(43).is_none());
        assert!(a.release(first, true).is_ok());
        assert!(b.release(second, true).is_ok());
        drop(a);
        assert!(FIRST.registry(1).is_none());
    }
}
