//! Fixed-capacity resource charging and nonreused local handle identities.
//! IPC endpoints and native netback retain one token per resource slot.
//! Mapping, grants and events stay in their adapters; a token is a logical
//! obligation to retain the associated pages until explicit confirmed release,
//! not a claim by a remote peer or authorization parsed from a wire value.

extern crate alloc;
use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

/// Upper bound matches the existing guest IPC grant range, not peer input.
pub const LIMIT: usize = 64;

/// One non-clonable obligation for a permanently pinned resource slot.
pub struct Token {
    /// Runtime-origin label; the effect adapter binds it to one unique owner.
    origin: u64,
    /// Index into the runtime's same fixed-capacity backing-page array.
    slot: usize,
    /// Positive local identity, never reissued during this registry lifetime.
    handle: u32,
    /// Domain selected by the trusted caller, bound before any Xen effect.
    peer: u16,
}

impl Token {
    /// Runtime origin to which this logical record belongs.
    pub closed spec fn origin(&self) -> u64 { self.origin }

    /// Runtime array slot, never selected by a peer descriptor.
    pub closed spec fn index(&self) -> usize { self.slot }

    /// Local lifetime label; deserializing it does not create this owner.
    pub closed spec fn identity(&self) -> u32 { self.handle }

    /// Exact selected domain bound to this resource lifetime.
    pub closed spec fn domain(&self) -> u16 { self.peer }

    /// Select the already charged static page slot; no allocator is invoked.
    pub fn slot(&self) -> (index: usize)
        ensures index == self.index(),
    { self.slot }

    /// Local ABI handle for later lookup under the same runtime owner guard.
    pub fn handle(&self) -> (handle: u32)
        ensures handle == self.identity(),
    { self.handle }

    /// Domain the runtime must use unchanged at every Xen effect boundary.
    pub fn peer(&self) -> (peer: u16)
        ensures peer == self.domain(),
    { self.peer }
}

/// Private copy of a charged owner's identity; the consumable token lives only
/// in the adapter. An abandoned token leaves this charge intact until teardown.
struct Entry {
    /// Local identity distinguishes recycled slots and domain-ID reuse.
    handle: u32,
    /// Caller-selected domain, unchanged across the resource lifetime.
    peer: u16,
}

/// Bounded charged slots with nonwrapping identities. No Clone or mutable view
/// permits bypassing admission or erasing a failed/quarantined charge.
pub struct Registry {
    /// Immutable origin supplied by the unique runtime owner factory.
    origin: u64,
    /// Fixed number of records, including every active or retiring resource.
    slots: Vec<Option<Entry>>,
    /// Next never-issued handle; i32::MAX is an exhausted terminal sentinel.
    next: u32,
}

impl Registry {
    /// Runtime origin bound before any token can be issued.
    pub closed spec fn origin(&self) -> u64 { self.origin }

    /// All charges have distinct live handles below the next identity.
    pub closed spec fn valid(&self) -> bool {
        &&& 1 <= self.slots@.len() <= LIMIT
        &&& 1 <= self.next <= i32::MAX
        &&& forall|i: int| #![trigger self.slots@[i]] 0 <= i < self.slots@.len() ==> match &self.slots@[i] {
            Some(entry) => 0 < entry.handle < self.next && entry.peer < 0x7ff0,
            None => true,
        }
        &&& forall|i: int, j: int| #![trigger self.slots@[i], self.slots@[j]] 0 <= i < j < self.slots@.len() ==> match (&self.slots@[i], &self.slots@[j]) {
            (Some(a), Some(b)) => a.handle != b.handle,
            _ => true,
        }
    }

    /// Fixed backing-array capacity, not the number of active resources.
    pub closed spec fn capacity(&self) -> nat { self.slots@.len() }

    /// Handle that has never been issued through this registry.
    pub closed spec fn next(&self) -> u32 { self.next }

    /// This exact token still owns the same charged slot/domain/lifetime.
    pub closed spec fn owns(&self, token: &Token) -> bool {
        token.origin == self.origin && token.slot < self.slots@.len() && match &self.slots@[token.slot as int] {
            Some(entry) => entry.handle == token.handle && entry.peer == token.peer,
            None => false,
        }
    }

    /// One slot currently carries a given local handle.
    pub closed spec fn at(&self, slot: int, handle: u32) -> bool {
        0 <= slot < self.slots@.len() && match &self.slots@[slot] {
            Some(entry) => entry.handle == handle,
            None => false,
        }
    }

    /// Preserve every other charge exactly across admission/release.
    pub closed spec fn others_same(&self, before: &Self, slot: int) -> bool {
        self.slots@.len() == before.slots@.len()
            && forall|i: int| 0 <= i < self.slots@.len() && i != slot ==> self.slots@[i] == before.slots@[i]
    }

    /// One bounded slot carries no retained charge.
    pub closed spec fn empty(&self, slot: int) -> bool {
        0 <= slot < self.slots@.len() && self.slots@[slot].is_none()
    }

    /// Capacity is exhausted only when every slot remains charged.
    pub closed spec fn full(&self) -> bool {
        forall|i: int| 0 <= i < self.slots@.len() ==> self.slots@[i].is_some()
    }

    /// Exact preservation when a requested transition is refused.
    pub closed spec fn same(&self, before: &Self) -> bool { self.slots@ == before.slots@ && self.next == before.next && self.origin == before.origin }

    /// Create fixed accounting before any real resource is offered. Invalid
    /// capacities are rejected before allocation; construction does finite work.
    /// `origin` is a logical label, not minted authority: the safe effect adapter
    /// must supply a unique stable runtime owner and prevent fabricated Tokens
    /// from crossing its boundary. This pure core itself owns no Xen resources.
    pub fn new(capacity: usize, origin: u64) -> (registry: Option<Self>)
        ensures match registry {
            Some(value) => value.valid() && value.origin() == origin && value.capacity() == capacity && value.next() == 1
                && forall|i: int| 0 <= i < value.capacity() ==> value.empty(i),
            None => capacity == 0 || capacity > LIMIT,
        },
    {
        if capacity == 0 || capacity > LIMIT { return None; }
        let mut slots: Vec<Option<Entry>> = Vec::new();
        let mut i = 0;
        while i < capacity
            invariant i == slots@.len(), i <= capacity <= LIMIT,
                forall|j: int| 0 <= j < slots@.len() ==> slots@[j].is_none(),
            decreases capacity-i,
        { slots.push(None); i += 1; }
        Some(Self { origin, slots, next: 1 })
    }

    /// Reserve before attempting mapping/binding/grant effects. Reuse requires
    /// confirmed release; identities are never wrapped, including after close.
    /// Domain zero is valid; Xen's reserved pseudo-domains are not selectable.
    pub fn reserve(&mut self, peer: u16) -> (token: Option<Token>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).origin() == old(self).origin(), final(self).capacity() == old(self).capacity(),
            match token {
                Some(value) => value.origin() == final(self).origin() && final(self).owns(&value) && value.index() < final(self).capacity()
                    && value.domain() == peer && value.identity() == old(self).next()
                    && final(self).next() == old(self).next()+1
                    && final(self).others_same(old(self), value.index() as int),
                None => final(self).same(old(self))
                    && (peer >= 0x7ff0 || old(self).next() == i32::MAX || old(self).full()),
            },
    {
        if peer >= 0x7ff0 || self.next == i32::MAX as u32 { return None; }
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), i <= self.slots@.len(), peer < 0x7ff0, self.next < i32::MAX,
                self.slots@ == old(self).slots@, self.next == old(self).next,
                forall|j: int| 0 <= j < i ==> self.slots@[j].is_some(),
            decreases self.slots.len()-i,
        {
            if self.slots[i].is_none() {
                let handle = self.next;
                self.next += 1;
                self.slots[i] = Some(Entry { handle, peer });
                return Some(Token { origin: self.origin, slot: i, handle, peer });
            }
            i += 1;
        }
        None
    }

    /// Resolve a previously issued local ABI label under the adapter's exclusive
    /// owner guard. This lookup does not create a Token or authorize a new peer.
    pub fn resolve(&self, handle: u32) -> (slot: Option<usize>)
        requires self.valid(),
        ensures match slot {
            Some(index) => index < self.capacity() && self.at(index as int, handle),
            None => forall|i: int| 0 <= i < self.capacity() ==> !self.at(i, handle),
        },
    {
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), i <= self.slots@.len(),
                forall|j: int| 0 <= j < i ==> !self.at(j, handle),
            decreases self.slots.len()-i,
        {
            match &self.slots[i] {
                Some(entry) if entry.handle == handle => return Some(i),
                _ => {},
            }
            i += 1;
        }
        None
    }

    /// A charged slot names this exact selected peer.
    pub closed spec fn peer_at(&self, slot: int, peer: u16) -> bool {
        0 <= slot < self.slots@.len() && match &self.slots@[slot] {
            Some(entry) => entry.peer == peer, None => false,
        }
    }

    /// Observe duplicate selected peers without granting or creating ownership.
    pub fn contains_peer(&self, peer: u16) -> (present: bool)
        requires self.valid(),
        ensures present == exists|i: int| 0 <= i < self.capacity() && self.peer_at(i, peer),
    {
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), i <= self.slots@.len(),
                forall|j: int| 0 <= j < i ==> !self.peer_at(j, peer),
            decreases self.slots.len()-i,
        {
            match &self.slots[i] {
                Some(entry) if entry.peer == peer => { assert(self.peer_at(i as int, peer)); return true; },
                _ => {},
            }
            i += 1;
        }
        false
    }

    /// Retire the exact owned lifetime only on confirmed release of all bound
    /// effects. Failure returns the same token and preserves every charge; even
    /// dropping that returned token cannot free/reallocate its slot.
    pub fn release(&mut self, token: Token, confirmed: bool) -> (result: Result<(), Token>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).origin() == old(self).origin(), final(self).next() == old(self).next(),
            match result {
                Ok(()) => confirmed && old(self).owns(&token)
                    && final(self).others_same(old(self), token.index() as int)
                    && !final(self).at(token.index() as int, token.identity())
                    && final(self).empty(token.index() as int),
                Err(value) => value == token && final(self).same(old(self))
                    && (!confirmed || !old(self).owns(&token)),
            },
    {
        if !confirmed || token.origin != self.origin || token.slot >= self.slots.len() { return Err(token); }
        match &self.slots[token.slot] {
            Some(entry) if entry.handle == token.handle && entry.peer == token.peer => {},
            _ => return Err(token),
        }
        self.slots[token.slot] = None;
        Ok(())
    }
}

/// Admission and fallible cleanup shared by IPC and network resource owners.
/// Known Busy results may be retried; an ambiguous error seals the owner and
/// prevents replay or any new publication while its resources remain charged.
pub struct Retirement {
    /// Coupled data admission and cleanup progress.
    phase: Phase,
}

/// Logical lifecycle, separate from the runtime's raw mapping/grant objects.
enum Phase {
    /// New data and publication operations are admitted.
    Live,
    /// No new effects; cleanup can retry only after a known pending result.
    Closing,
    /// Cleanup error is ambiguous; retain resources until domain teardown.
    Quarantined,
}

impl Retirement {
    /// Create admission state before the runtime exposes a new handle.
    pub const fn new() -> (state: Self)
        ensures state.live(),
    { Self { phase: Phase::Live } }

    /// Whether data operations or new grants/mappings are admitted.
    pub closed spec fn live(&self) -> bool { matches!(self.phase, Phase::Live) }

    /// Whether cleanup remains eligible for retry after a known pending result.
    pub closed spec fn closing(&self) -> bool { matches!(self.phase, Phase::Closing) }

    /// Whether ambiguous effects permanently forbid further calls through it.
    pub closed spec fn quarantined(&self) -> bool { matches!(self.phase, Phase::Quarantined) }

    /// Enforce operation admission at the effect boundary.
    pub fn usable(&self) -> (allowed: bool)
        ensures allowed == self.live(),
    { matches!(self.phase, Phase::Live) }

    /// Stop new operations before any fallible cleanup. A retry after a known
    /// pending (Busy) outcome is permitted; an ambiguous error is terminal.
    pub fn begin(&mut self) -> (accepted: bool)
        ensures accepted == !old(self).quarantined(),
            accepted ==> final(self).closing(), !accepted ==> final(self).quarantined(),
    {
        if matches!(self.phase, Phase::Quarantined) { return false; }
        self.phase = Phase::Closing;
        true
    }

    /// Retain charges and prohibit replay before returning an effect error.
    pub fn quarantine(&mut self)
        ensures final(self).quarantined(), !final(self).live(),
    { self.phase = Phase::Quarantined; }
}

impl Default for Retirement {
    /// Create fresh operation admission without performing external effects.
    fn default() -> Self { Self::new() }
}

}

#[cfg(test)]
mod tests {
    use super::Registry;

    /// Exhaust the next-identity sentinel without billions of fixture effects.
    /// No live owner is fabricated; the empty registry still satisfies valid().
    #[test]
    fn identity_exhaustion_is_terminal_after_release() {
        let mut registry = Registry::new(1, 1).unwrap();
        registry.next = i32::MAX as u32 - 1;
        let last = registry.reserve(0).unwrap();
        assert_eq!(last.handle(), i32::MAX as u32 - 1);
        assert!(registry.release(last, true).is_ok());
        assert!(registry.reserve(0).is_none());
    }
}
