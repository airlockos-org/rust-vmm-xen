//! Checked wrapping counters shared by XenStore and native netif rings.
//! These operations carry no ownership or memory authority. Each protocol
//! separately validates occupancy and binds observations to its real ring.

use vstd::prelude::*;

verus! {

/// Mathematical distance of wrapping 32-bit producer and consumer counters.
pub open spec fn distance(producer: u32, consumer: u32) -> int {
    if producer >= consumer { producer as int - consumer as int }
    else { 0x1_0000_0000int - consumer as int + producer as int }
}

/// Compute a wrapping index distance without machine overflow assumptions.
pub fn distance_value(producer: u32, consumer: u32) -> (count: u64)
    ensures count == distance(producer, consumer), count <= u32::MAX,
{
    if producer >= consumer { producer as u64 - consumer as u64 }
    else { 0x1_0000_0000u64 - consumer as u64 + producer as u64 }
}

/// Advance a wrapping producer/consumer by a bounded number of entries.
pub fn next_index(index: u32, amount: u16) -> (next: u32)
    ensures next as int == (index as int + amount) % 0x1_0000_0000int,
{ ((index as u64 + amount as u64) % 0x1_0000_0000u64) as u32 }

/// Xen ring notification test after publication and a full memory barrier.
/// The event index is a peer observation, never an authority or byte offset.
pub fn event_needed(old: u32, new: u32, event: u32) -> (needed: bool)
    ensures needed == (distance(new, event) < distance(new, old)),
{ distance_value(new, event) < distance_value(new, old) }


}
