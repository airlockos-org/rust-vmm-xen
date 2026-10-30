//! Frontend-owned producer/consumer counters and bounded native ring slots.
//! Plans are immutable observations, consumed after the runtime copies the
//! descriptor and publishes the corresponding index with Xen's memory ordering.
//! These range plans carry no memory/identity authority. The adapter retains
//! the same exclusive queue owner through copying and publication; a modulo
//! counter alone cannot distinguish an old plan after a complete 32-bit
//! rollover.

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use xen_store_protocol::ring::distance;
use xen_store_protocol::ring::{distance_value, next_index};

#[cfg(verus_keep_ghost)]
use crate::PAGE;
use crate::{HEADER, Invalid, SLOTS};

verus! {

/// Immutable descriptor location in one shared ring page.
pub struct Slot {
    /// Private counter value at planning time, checked again at the matching publication.
    start: u32,
    /// Offset of the native ABI slot, after the shared header.
    offset: usize,
    /// Native descriptor stride: twelve TX bytes or eight RX bytes.
    width: usize,
}

impl Slot {
    /// Every slot remains entirely inside the same page.
    pub closed spec fn valid(&self) -> bool {
        (self.width == 8 || self.width == 12) && HEADER <= self.offset
            && self.offset + self.width <= PAGE
    }

    /// Counter captured when this plan was created.
    pub closed spec fn index(&self) -> u32 { self.start }

    /// Native byte stride chosen by the ring constructor.
    pub closed spec fn stride(&self) -> usize { self.width }

    /// Byte offset inside the ring page.
    pub closed spec fn begin(&self) -> usize { self.offset }

    /// Planned byte count, independent of peer-provided payload sizes.
    pub fn len(&self) -> (length: usize)
        requires self.valid(),
        ensures length == self.stride() && (length == 8 || length == 12),
    { self.width }

    /// A native slot cannot be empty.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.valid(), ensures !empty,
    { false }

    /// Authorize one descriptor byte; malformed caller indices return None.
    pub fn byte(&self, index: usize) -> (offset: Option<usize>)
        requires self.valid(),
        ensures match offset {
            Some(value) => index < self.stride() && value == self.begin() + index && value < PAGE,
            None => index >= self.stride(),
        },
    { if index >= self.width { None } else { Some(self.offset + index) } }

    /// Previous counter for Xen's notification test, before consuming the plan.
    pub fn current(&self) -> (index: u32)
        ensures index == self.index(),
    { self.start }

    /// Next counter value for release publication after copying this slot.
    pub fn published(&self) -> (next: u32)
        ensures next as int == (self.index() as int + 1) % 0x1_0000_0000int,
    { next_index(self.start, 1) }
}

/// Private frontend counters. Packet-buffer ownership is tracked independently;
/// the runtime must satisfy both before reposting a grant-backed buffer.
pub struct Front {
    /// Requests published to the backend on this ring.
    producer: u32,
    /// Responses consumed from the backend on this ring.
    consumer: u32,
    /// Native ring ABI width, fixed at construction and never peer-controlled.
    width: usize,
}

/// Wrapping an index preserves one additional outstanding request.
proof fn advance_producer(producer: u32, consumer: u32, next: u32)
    requires distance(producer, consumer) < SLOTS,
        next as int == (producer as int + 1) % 0x1_0000_0000int,
    ensures distance(next, consumer) == distance(producer, consumer) + 1,
{
    if producer == u32::MAX {} else {}
}

/// Wrapping a consumer retires exactly one outstanding request.
proof fn advance_consumer(producer: u32, consumer: u32, next: u32)
    requires 0 < distance(producer, consumer) <= SLOTS,
        next as int == (consumer as int + 1) % 0x1_0000_0000int,
    ensures distance(producer, next) == distance(producer, consumer) - 1,
{
    if consumer == u32::MAX {} else {}
}

impl Front {
    /// Occupancy cannot exceed the native single-page ring capacity.
    pub closed spec fn valid(&self) -> bool {
        (self.width == 8 || self.width == 12) && distance(self.producer, self.consumer) <= SLOTS
    }

    /// Shadow producer used to validate locally owned shared indices.
    pub closed spec fn produced(&self) -> u32 { self.producer }

    /// Shadow response consumer, not supplied by the peer.
    pub closed spec fn consumed(&self) -> u32 { self.consumer }

    /// Native descriptor stride, independent of peer observations.
    pub closed spec fn stride(&self) -> usize { self.width }

    /// Create an empty TX ring.
    pub fn tx() -> (queue: Self)
        ensures queue.valid(), queue.produced() == 0, queue.consumed() == 0,
    { Self { producer: 0, consumer: 0, width: 12 } }

    /// Create an empty RX ring.
    pub fn rx() -> (queue: Self)
        ensures queue.valid(), queue.produced() == 0, queue.consumed() == 0,
    { Self { producer: 0, consumer: 0, width: 8 } }

    /// Plan one request without changing completion/publication state.
    pub fn request(&self, shared_producer: u32) -> (slot: Result<Option<Slot>, Invalid>)
        requires self.valid(),
        ensures match slot {
            Ok(Some(value)) => value.valid() && value.index() == self.produced() && value.stride() == self.stride()
                && value.begin() == HEADER + (self.produced() as int % SLOTS as int) * self.stride()
                && shared_producer == self.produced() && distance(self.produced(), self.consumed()) < SLOTS,
            Ok(None) => shared_producer == self.produced() && distance(self.produced(), self.consumed()) == SLOTS,
            Err(_) => shared_producer != self.produced(),
        },
    {
        if shared_producer != self.producer { return Err(Invalid::Counter); }
        if distance_value(self.producer, self.consumer) == SLOTS as u64 { return Ok(None); }
        let offset = HEADER + (self.producer as usize % SLOTS as usize) * self.width;
        Ok(Some(Slot { start: self.producer, offset, width: self.width }))
    }

    /// Record publication only for the same still-current request plan.
    pub fn posted(&mut self, slot: Slot) -> (accepted: bool)
        requires old(self).valid(), slot.valid(),
        ensures final(self).valid(), final(self).stride() == old(self).stride(), final(self).consumed() == old(self).consumed(),
            accepted ==> final(self).produced() as int == (old(self).produced() as int + 1) % 0x1_0000_0000int,
            !accepted ==> final(self).produced() == old(self).produced(),
    {
        if slot.start != self.producer || slot.width != self.width
            || distance_value(self.producer, self.consumer) >= SLOTS as u64 { return false; }
        let next = next_index(self.producer, 1);
        proof { advance_producer(self.producer, self.consumer, next); }
        self.producer = next;
        true
    }

    /// Plan one response, rejecting peer overrun of posted requests.
    pub fn response(&self, shared_producer: u32, response_producer: u32) -> (slot: Result<Option<Slot>, Invalid>)
        requires self.valid(),
        ensures match slot {
            Ok(Some(value)) => value.valid() && value.index() == self.consumed() && value.stride() == self.stride()
                && value.begin() == HEADER + (self.consumed() as int % SLOTS as int) * self.stride()
                && shared_producer == self.produced() && 0 < distance(response_producer, self.consumed()) <= distance(self.produced(), self.consumed()),
            Ok(None) => shared_producer == self.produced() && response_producer == self.consumed(),
            Err(_) => shared_producer != self.produced()
                || distance(response_producer, self.consumed()) > distance(self.produced(), self.consumed()),
        },
    {
        if shared_producer != self.producer { return Err(Invalid::Counter); }
        let ready = distance_value(response_producer, self.consumer);
        if ready > distance_value(self.producer, self.consumer) { return Err(Invalid::Counter); }
        if ready == 0 { return Ok(None); }
        let offset = HEADER + (self.consumer as usize % SLOTS as usize) * self.width;
        Ok(Some(Slot { start: self.consumer, offset, width: self.width }))
    }

    /// Consume the private descriptor snapshot before requesting another event.
    pub fn consumed_response(&mut self, slot: Slot) -> (accepted: bool)
        requires old(self).valid(), slot.valid(),
        ensures final(self).valid(), final(self).stride() == old(self).stride(), final(self).produced() == old(self).produced(),
            accepted ==> final(self).consumed() as int == (old(self).consumed() as int + 1) % 0x1_0000_0000int,
            !accepted ==> final(self).consumed() == old(self).consumed(),
    {
        if slot.start != self.consumer || slot.width != self.width
            || self.consumer == self.producer { return false; }
        let next = next_index(self.consumer, 1);
        proof { advance_consumer(self.producer, self.consumer, next); }
        self.consumer = next;
        true
    }

    /// Next response event threshold, published before the sleep/ring recheck.
    pub fn event(&self) -> (event: u32)
        ensures event as int == (self.consumed() as int + 1) % 0x1_0000_0000int,
    { next_index(self.consumer, 1) }
}

}
