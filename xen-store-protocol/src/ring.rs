//! Checked copy plans for the standard 1024-byte XenStore byte rings.
//! The runtime supplies one snapshot of shared indices and its private local
//! counter. Plans authorize only bounded byte offsets and one next index;
//! they do not grant memory access or prove a volatile copy occurred.

use vstd::prelude::*;

verus! {

/// Request and response buffers each occupy one 1024-byte region.
pub const RING_BYTES: usize = 1024;

/// One private snapshot's bounded copy plan. No Clone or public constructor:
/// runtime adapters consume a plan once after the matching byte copy.
pub struct Window {
    /// Locally owned index captured before the operation.
    start: u32,
    /// Number of bytes authorized by ring availability and caller capacity.
    count: usize,
    /// Buffer base: zero for requests, 1024 for responses.
    base: usize,
}

/// Validate the HVM store PFN against the first-4-GiB bootstrap mapping.
/// This proves address arithmetic, not the hypervisor's mapping guarantee.
pub fn page_address(frame: u64) -> (address: Option<usize>)
    ensures match address {
        Some(value) => 0 < frame < 0x10_0000 && value == frame * 4096
            && value < 0x1_0000_0000int,
        None => frame == 0 || frame >= 0x10_0000,
    },
{
    if frame == 0 || frame >= 0x10_0000 { return None; }
    Some((frame * 4096) as usize)
}

/// Admit only an empty fresh stream before request identity one is created.
pub fn fresh(request_producer: u32, request_consumer: u32, response_producer: u32, response_consumer: u32) -> (empty: bool)
    ensures empty == (request_producer == request_consumer && response_producer == response_consumer),
{ request_producer == request_consumer && response_producer == response_consumer }

/// Mathematical distance of wrapping 32-bit producer and consumer counters.
pub open spec fn distance(producer: u32, consumer: u32) -> int {
    if producer >= consumer { producer as int - consumer as int }
    else { 0x1_0000_0000int - consumer as int + producer as int }
}

/// Compute ring occupancy without machine arithmetic wraparound assumptions.
fn queued(producer: u32, consumer: u32) -> (count: u64)
    ensures count == distance(producer, consumer), count <= u32::MAX,
{
    if producer >= consumer { producer as u64 - consumer as u64 }
    else { 0x1_0000_0000u64 - consumer as u64 + producer as u64 }
}

impl Window {
    /// Every planned byte lies in one of the two ABI buffer regions.
    pub closed spec fn valid(&self) -> bool {
        self.count <= RING_BYTES && (self.base == 0 || self.base == RING_BYTES)
    }

    /// Starting local counter captured by this plan.
    pub closed spec fn start_index(&self) -> u32 { self.start }

    /// Authorized number of byte copies.
    pub closed spec fn count(&self) -> usize { self.count }

    /// ABI byte-region base selected by the direction-specific constructor.
    pub closed spec fn base(&self) -> usize { self.base }

    /// Planned byte count, bounded independently of the caller's capacity.
    pub fn len(&self) -> (count: usize)
        requires self.valid(),
        ensures count == self.count(), count <= RING_BYTES,
    { self.count }

    /// Whether no bytes can be transferred in this snapshot.
    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.count() == 0),
    { self.count == 0 }

    /// Return only an authorized byte offset in the shared page. Invalid callers
    /// receive None rather than reaching an unchecked pointer calculation.
    pub fn offset(&self, index: usize) -> (offset: Option<usize>)
        requires self.valid(),
        ensures match offset {
            Some(value) => index < self.count() && value < 2048
                && value == self.base() + ((self.start_index() as int + index) % (RING_BYTES as int)),
            None => index >= self.count(),
        },
    {
        if index >= self.count { return None; }
        let slot = (self.start as usize % RING_BYTES + index) % RING_BYTES;
        proof { assert((self.start as int % 1024 + index as int) % 1024 == (self.start as int + index as int) % 1024) by (nonlinear_arith); }
        Some(self.base + slot)
    }

    /// Consume the plan and return the next published local index. Runtime must
    /// first perform exactly len() bytes of copying using this plan's offsets.
    pub fn finish(self) -> (next: u32)
        requires self.valid(),
        ensures next as int == (self.start_index() as int + self.count()) % 0x1_0000_0000int,
    {
        ((self.start as u64 + self.count as u64) % 0x1_0000_0000u64) as u32
    }
}

/// Plan a request write. Reject peer modification of the local producer or an
/// impossible occupancy. Empty plans mean backpressure, not a corrupt stream.
pub fn send(local: u32, shared_producer: u32, consumer: u32, limit: usize) -> (plan: Option<Window>)
    ensures match plan {
        Some(window) => window.valid() && window.start_index() == local && window.base() == 0
            && window.count() <= limit && local == shared_producer
            && distance(shared_producer, consumer) <= RING_BYTES
            && window.count() == if limit < RING_BYTES - distance(shared_producer, consumer) { limit as int }
                else { RING_BYTES - distance(shared_producer, consumer) },
        None => local != shared_producer || distance(shared_producer, consumer) > RING_BYTES,
    },
{
    if local != shared_producer { return None; }
    let occupied = queued(shared_producer, consumer);
    if occupied > RING_BYTES as u64 { return None; }
    let free = RING_BYTES - occupied as usize;
    let count = if limit < free { limit } else { free };
    Some(Window { start: local, count, base: 0 })
}

/// Plan a response read, rejecting peer modification of the local consumer.
pub fn receive(local: u32, shared_consumer: u32, producer: u32, limit: usize) -> (plan: Option<Window>)
    ensures match plan {
        Some(window) => window.valid() && window.start_index() == local && window.base() == RING_BYTES
            && window.count() <= limit && local == shared_consumer
            && distance(producer, shared_consumer) <= RING_BYTES
            && window.count() == if limit < distance(producer, shared_consumer) { limit as int }
                else { distance(producer, shared_consumer) },
        None => local != shared_consumer || distance(producer, shared_consumer) > RING_BYTES,
    },
{
    if local != shared_consumer { return None; }
    let available = queued(producer, shared_consumer);
    if available > RING_BYTES as u64 { return None; }
    let count = if limit < available as usize { limit } else { available as usize };
    Some(Window { start: local, count, base: RING_BYTES })
}

}
