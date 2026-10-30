//! Bounded, coalesced watch hints for one exclusive XenStore connection.
//! Numeric tokens are routing labels, not credentials. The runtime binds opaque
//! keys to its private watch objects and the originating connection. Dropping a
//! key does not return credits: only an acknowledged unwatch permits release.

extern crate alloc;

use alloc::vec::Vec;

use vstd::prelude::*;

use crate::transaction;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Maximum active and quarantined subscriptions combined.
pub const LIMIT: usize = 32;

/// One immutable subscription label. Not constructible from a daemon event and
/// not clonable; runtime watch objects retain it until explicit close.
pub struct Key {
    /// Monotonic label, never recycled during this connection lifetime.
    serial: u32,
}

impl Key {
    /// Routing identity without exposing mutable representation.
    pub closed spec fn identity(&self) -> u32 { self.serial }

    /// Obtain the label for wire-token construction, never as authorization.
    pub fn wire(&self) -> (id: u32)
        ensures id == self.identity(),
    { self.serial }
}

/// Immutable registration/removal body. Reusing these exact bytes for unwatch
/// prevents retargeting a subscription during cleanup.
pub struct Request {
    /// Private, bounded path/NUL/token/NUL encoding.
    bytes: Vec<u8>,
    /// Immutable boundary of the registered path, excluding its NUL delimiter.
    path_length: usize,
}

impl Request {
    /// Encoded bytes bound to the validated path and reserved label.
    pub closed spec fn data(&self) -> Seq<u8> { self.bytes@ }

    /// The path boundary is bounded and points at its original NUL delimiter.
    pub closed spec fn valid(&self) -> bool {
        0 < self.path_length <= 256 && self.path_length + 2 <= self.bytes@.len() <= 268
            && self.bytes@[self.path_length as int] == 0
    }

    /// The exact read request for the registered authoritative node.
    pub closed spec fn read_data(&self) -> Seq<u8> {
        self.bytes@.subrange(0, self.path_length + 1)
    }

    /// Validate candidate formatting against the actual reserved identity before
    /// publishing any effect. The formatter is not trusted to choose an identity.
    pub fn new(path: &[u8], token: &[u8], key: &Key) -> (body: Option<Self>)
        ensures match body {
            Some(value) => value.valid() && value.read_data() == path@ + seq![0u8] && 0 < path@.len() <= 256
                && (forall|i: int| 0 <= i < path@.len() ==> path@[i] != 0)
                && transaction::valid_token(token@) && transaction::number(token@) == key.identity()
                && value.data() == path@ + seq![0u8] + token@ + seq![0u8]
                && value.data().len() <= 268,
            None => !(0 < path@.len() <= 256
                && (forall|i: int| 0 <= i < path@.len() ==> path@[i] != 0)
                && transaction::valid_token(token@) && transaction::number(token@) == key.identity()),
        },
    {
        if path.is_empty() || path.len() > 256 { return None; }
        let mut i = 0;
        while i < path.len()
            invariant 0 < path@.len() <= 256, i <= path@.len(),
                forall|j: int| 0 <= j < i ==> path@[j] != 0,
            decreases path.len()-i,
        {
            if path[i] == 0 { return None; }
            i += 1;
        }
        let id = transaction::Id::parse_token(token)?;
        if id.wire() != key.serial { return None; }
        let mut bytes = Vec::with_capacity(path.len() + token.len() + 2);
        bytes.extend_from_slice(path);
        bytes.push(0);
        bytes.extend_from_slice(token);
        bytes.push(0);
        assert(bytes@.subrange(0, path@.len() as int + 1) =~= path@ + seq![0u8]);
        Some(Self { bytes, path_length: path.len() })
    }

    /// Borrow the path/NUL prefix of the same registration body for re-reading.
    pub fn read_body(&self) -> (bytes: &[u8])
        requires self.valid(),
        ensures bytes@ == self.read_data(),
    { vstd::slice::slice_subrange(self.bytes.as_slice(), 0, self.path_length + 1) }

    /// Borrow the same private bytes for registration and explicit removal.
    pub fn bytes(&self) -> (bytes: &[u8])
        ensures bytes@ == self.data(),
    { self.bytes.as_slice() }
}

/// One charged hint slot; no attacker-controlled path or payload is retained.
struct Slot {
    /// Label issued by the monotonic admission counter.
    serial: u32,
    /// Coalesced indication to re-read authoritative state.
    dirty: bool,
}

/// Fixed-admission mailbox; released IDs are never reused and late events cannot
/// address a replacement subscription. Lost keys retain their charged slot.
pub struct Inbox {
    /// Next never-issued label; exhaustion rejects admission without wrapping.
    next: u32,
    /// Active and quarantined reservations, preallocated to LIMIT entries.
    slots: Vec<Slot>,
}

impl Default for Inbox {
    /// Start without any subscriptions.
    fn default() -> Self { Self::new() }
}

impl Inbox {
    /// Every retained label was issued once, with increasing admission order.
    pub closed spec fn valid(&self) -> bool {
        &&& self.next > 0
        &&& self.slots@.len() <= LIMIT
        &&& forall|i: int| 0 <= i < self.slots@.len() ==> 0 < #[trigger] self.slots@[i].serial < self.next
        &&& forall|i: int, j: int| 0 <= i < j < self.slots@.len()
            ==> self.slots@[i].serial < self.slots@[j].serial
    }

    /// Next never-issued routing label.
    pub closed spec fn next_id(&self) -> u32 { self.next }

    /// Full logical state equality without mutable representation exposure.
    pub closed spec fn same_as(&self, other: &Self) -> bool { self.next == other.next && self.slots@ == other.slots@ }

    /// Number of charged slots, including dropped/unacknowledged subscriptions.
    pub closed spec fn retained(&self) -> nat { self.slots@.len() }

    /// Whether a label has a retained subscription reservation.
    pub closed spec fn contains(&self, id: u32) -> bool {
        exists|i: int| 0 <= i < self.slots@.len() && self.slots@[i].serial == id
    }

    /// Whether a retained label needs an authoritative re-read.
    pub closed spec fn pending(&self, id: u32) -> bool {
        exists|i: int| 0 <= i < self.slots@.len() && self.slots@[i].serial == id && self.slots@[i].dirty
    }

    /// Preservation of label membership and every unrelated dirty flag.
    pub closed spec fn unchanged_except(&self, old: &Self, id: u32) -> bool {
        &&& self.slots@.len() == old.slots@.len()
        &&& forall|i: int| 0 <= i < self.slots@.len()
            ==> self.slots@[i].serial == old.slots@[i].serial
                && (self.slots@[i].serial != id ==> self.slots@[i].dirty == old.slots@[i].dirty)
    }

    /// Admission preserves every previously retained slot and pending hint.
    pub closed spec fn extends(&self, old: &Self) -> bool {
        old.slots@.len() <= self.slots@.len()
            && self.slots@.subrange(0, old.slots@.len() as int) == old.slots@
    }

    /// Removing one label preserves every unrelated subscription and hint.
    pub closed spec fn retains_others(&self, old: &Self, id: u32) -> bool {
        if old.contains(id) {
            exists|i: int| 0 <= i < old.slots@.len() && old.slots@[i].serial == id
                && self.slots@ == old.slots@.remove(i)
        } else { self.slots@ == old.slots@ }
    }

    /// Allocate bounded slot storage once; no event payloads are queued.
    pub fn new() -> (inbox: Self)
        ensures inbox.valid(), inbox.retained() == 0,
    { Self { next: 1, slots: Vec::with_capacity(LIMIT) } }

    /// Reserve a fresh label before registering it with the daemon. Failure does
    /// not publish a request or consume an ID; the caller owns that ordering.
    pub fn reserve(&mut self) -> (key: Option<Key>)
        requires old(self).valid(),
        ensures final(self).valid(),
            match key {
                Some(value) => value.identity() == old(self).next_id() && final(self).next_id() == old(self).next_id() + 1
                    && final(self).retained() == old(self).retained() + 1
                    && final(self).contains(value.identity()) && !final(self).pending(value.identity())
                    && final(self).extends(old(self)),
                None => final(self).same_as(old(self))
                    && (old(self).retained() == LIMIT || old(self).next_id() == u32::MAX),
            },
    {
        if self.slots.len() == LIMIT || self.next == u32::MAX { return None; }
        let serial = self.next;
        self.next += 1;
        let ghost previous = self.slots@;
        self.slots.push(Slot { serial, dirty: false });
        assert(self.slots@[previous.len() as int].serial == serial);
        assert(self.contains(serial));
        assert(self.slots@.subrange(0, previous.len() as int) =~= previous);
        assert forall|i: int| 0 <= i < self.slots@.len() && self.slots@[i].serial == serial
            implies !self.slots@[i].dirty by {
            if i < previous.len() { assert(previous[i].serial < serial); }
        }
        Some(Key { serial })
    }

    /// Coalesce a recognized label without allocating or changing membership.
    fn mark(&mut self, id: u32)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).unchanged_except(old(self), id),
            final(self).next_id() == old(self).next_id(),
            final(self).pending(id) == old(self).contains(id),
    {
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), self.slots@ == old(self).slots@, self.next == old(self).next,
                i <= self.slots@.len(),
                forall|j: int| 0 <= j < i ==> self.slots@[j].serial != id,
            decreases self.slots.len()-i,
        {
            if self.slots[i].serial == id {
                assert(old(self).slots@[i as int].serial == id);
                assert(old(self).contains(id));
                self.slots.set(i, Slot { serial: id, dirty: true });
                assert(self.slots@[i as int].serial == id && self.slots@[i as int].dirty);
                assert(self.pending(id));
                return;
            }
            i += 1;
        }
    }

    /// Consume a private watch token as a hint. Malformed, stale and unknown
    /// labels cannot create subscriptions or affect any other retained label.
    pub fn notify(&mut self, token: &[u8])
        requires old(self).valid(),
        ensures final(self).valid(), final(self).retained() == old(self).retained(),
            final(self).next_id() == old(self).next_id(),
            if transaction::valid_token(token@) {
                final(self).unchanged_except(old(self), transaction::number(token@) as u32)
                    && final(self).pending(transaction::number(token@) as u32) == old(self).contains(transaction::number(token@) as u32)
            } else { final(self).same_as(old(self)) },
    {
        if let Some(id) = transaction::Id::parse_token(token) { self.mark(id.wire()); }
    }

    /// Acknowledge a locally owned hint, preserving all unrelated pending bits.
    pub fn take(&mut self, key: &Key) -> (dirty: bool)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).unchanged_except(old(self), key.identity()),
            final(self).next_id() == old(self).next_id(),
            dirty == old(self).pending(key.identity()), !final(self).pending(key.identity()),
    {
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), self.slots@ == old(self).slots@, self.next == old(self).next,
                i <= self.slots@.len(),
                forall|j: int| 0 <= j < i ==> self.slots@[j].serial != key.serial,
            decreases self.slots.len()-i,
        {
            if self.slots[i].serial == key.serial {
                let dirty = self.slots[i].dirty;
                self.slots.set(i, Slot { serial: key.serial, dirty: false });
                return dirty;
            }
            i += 1;
        }
        false
    }

    /// Consume one key only after acknowledged daemon removal. A lost key never
    /// invokes this function implicitly. No subsequent admission reuses its ID.
    pub fn release(&mut self, key: Key) -> (removed: bool)
        requires old(self).valid(),
        ensures final(self).valid(), !final(self).contains(key.identity()),
            final(self).retains_others(old(self), key.identity()),
            removed == old(self).contains(key.identity()),
            final(self).retained() == old(self).retained() - if removed { 1nat } else { 0nat },
            final(self).next_id() == old(self).next_id(),
    {
        let mut i = 0;
        while i < self.slots.len()
            invariant self.valid(), self.slots@ == old(self).slots@, self.next == old(self).next,
                i <= self.slots@.len(),
                forall|j: int| 0 <= j < i ==> self.slots@[j].serial != key.serial,
            decreases self.slots.len()-i,
        {
            if self.slots[i].serial == key.serial {
                let ghost previous = self.slots@;
                self.slots.remove(i);
                assert(self.slots@ == previous.remove(i as int));
                assert(self.retains_others(old(self), key.serial));
                return true;
            }
            i += 1;
        }
        false
    }
}

}
