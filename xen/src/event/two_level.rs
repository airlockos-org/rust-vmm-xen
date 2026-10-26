//! Xen two-level event bitmap, with atomic clear/mask and hypercall unmask.
use core::{
    ptr::addr_of_mut,
    sync::atomic::{AtomicU64, AtomicU8, Ordering},
};

use xen_sys::{bindings::*, error::XenError, XenHypercall};

pub struct TwoLevel {
    shared: *mut shared_info,
}
unsafe impl Send for TwoLevel {}
unsafe impl Sync for TwoLevel {}
impl TwoLevel {
    /// # Safety
    /// Permanently mapped 64-bit shared-info, single vCPU 0, two-level ABI.
    pub const unsafe fn new(shared: *mut shared_info) -> Self {
        Self { shared }
    }
    pub fn mask(&self, port: u32) -> Result<(), XenError> {
        if port >= 4096 {
            return Err(XenError::Other("event port outside bitmap"));
        }
        unsafe {
            AtomicU64::from_ptr(addr_of_mut!(
                (*self.shared).evtchn_mask[(port / 64) as usize]
            ))
            .fetch_or(1 << (port % 64), Ordering::SeqCst);
        }
        Ok(())
    }
    pub fn enable_upcalls(&self) {
        unsafe {
            AtomicU8::from_ptr(addr_of_mut!((*self.shared).vcpu_info[0].evtchn_upcall_mask))
                .store(0, Ordering::SeqCst);
        }
    }
    /// One bounded snapshot. A racing notification re-arms pending_sel/upcall.
    /// Each callback must drain queue state, not count notifications as
    /// messages.
    pub fn drain(&self, mut handler: impl FnMut(u32)) {
        unsafe {
            let v = addr_of_mut!((*self.shared).vcpu_info[0]);
            AtomicU8::from_ptr(addr_of_mut!((*v).evtchn_upcall_pending)).store(0, Ordering::SeqCst);
            let mut selectors = AtomicU64::from_ptr(addr_of_mut!((*v).evtchn_pending_sel))
                .swap(0, Ordering::SeqCst);
            while selectors != 0 {
                let word = selectors.trailing_zeros() as usize;
                selectors &= selectors - 1;
                let pending =
                    AtomicU64::from_ptr(addr_of_mut!((*self.shared).evtchn_pending[word]));
                let mask = AtomicU64::from_ptr(addr_of_mut!((*self.shared).evtchn_mask[word]));
                let mut bits = pending.load(Ordering::Acquire) & !mask.load(Ordering::Acquire);
                while bits != 0 {
                    let bit = bits.trailing_zeros();
                    bits &= bits - 1;
                    pending.fetch_and(!(1u64 << bit), Ordering::SeqCst);
                    handler((word as u32) * 64 + bit);
                }
            }
        }
    }
    pub fn unmask<H: XenHypercall>(&self, hyp: &H, port: u32) -> Result<(), XenError> {
        if port >= 4096 {
            return Err(XenError::Other("event port outside bitmap"));
        }
        // Always use Xen's slow path. It re-delivers a notification that arrived
        // while masked, including the pending_sel race; no polling required.
        let arg = evtchn_unmask { port };
        unsafe {
            hyp.hypercall2(
                __HYPERVISOR_event_channel_op as _,
                [EVTCHNOP_unmask as _, (&raw const arg).addr()],
            )?;
        }
        Ok(())
    }
}
