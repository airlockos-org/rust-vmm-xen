//! Xen versioned PV clock. Based on public xen.h and Mini-OS's scaling algorithm.
use core::{
    ptr::{addr_of, read_volatile},
    sync::atomic::{AtomicU64, Ordering, fence},
};
use xen_sys::{
    bindings::{shared_info, vcpu_time_info},
    error::XenError,
};

pub struct PvClock {
    shared: *const shared_info,
    last: AtomicU64,
}
unsafe impl Send for PvClock {}
unsafe impl Sync for PvClock {}
impl PvClock {
    /// # Safety
    /// Permanently mapped Xen-owned 64-bit shared-info, for vCPU 0 only.
    pub const unsafe fn new(shared: *const shared_info) -> Self {
        Self {
            shared,
            last: AtomicU64::new(0),
        }
    }
    pub fn now_ns(&self) -> Result<u64, XenError> {
        let info = unsafe { addr_of!((*self.shared).vcpu_info[0].time) };
        let value = unsafe { read_time(info)? };
        // Clamp across scheduling/migration updates. The snapshot must still
        // be refreshed on every call; clamping alone is not a clock source.
        Ok(self.last.fetch_max(value, Ordering::Relaxed).max(value))
    }
    pub fn wallclock_ns(&self) -> Result<u64, XenError> {
        unsafe {
            for _ in 0..10_000 {
                let s = self.shared;
                let version = read_volatile(addr_of!((*s).wc_version));
                if version & 1 != 0 {
                    core::hint::spin_loop();
                    continue;
                }
                fence(Ordering::Acquire);
                let sec = u64::from(read_volatile(addr_of!((*s).wc_sec)))
                    | (u64::from(read_volatile(addr_of!((*s).wc_sec_hi))) << 32);
                let ns = u64::from(read_volatile(addr_of!((*s).wc_nsec)));
                let now = self.now_ns()?;
                fence(Ordering::Acquire);
                if version == read_volatile(addr_of!((*s).wc_version)) {
                    return sec
                        .checked_mul(1_000_000_000)
                        .and_then(|v| v.checked_add(ns))
                        .and_then(|v| v.checked_add(now))
                        .ok_or(XenError::Other("wallclock overflow"));
                }
            }
        }
        Err(XenError::Other("unstable Xen wallclock"))
    }
}
unsafe fn read_time(info: *const vcpu_time_info) -> Result<u64, XenError> {
    for _ in 0..10_000 {
        let version = unsafe { read_volatile(addr_of!((*info).version)) };
        if version & 1 != 0 {
            core::hint::spin_loop();
            continue;
        }
        fence(Ordering::Acquire);
        let (stamp, system, mul, shift) = unsafe {
            (
                read_volatile(addr_of!((*info).tsc_timestamp)),
                read_volatile(addr_of!((*info).system_time)),
                read_volatile(addr_of!((*info).tsc_to_system_mul)),
                read_volatile(addr_of!((*info).tsc_shift)),
            )
        };
        // LFENCE prevents the timestamp sample from passing earlier loads.
        let tsc = unsafe {
            core::arch::x86_64::_mm_lfence();
            let t = core::arch::x86_64::_rdtsc();
            core::arch::x86_64::_mm_lfence();
            t
        };
        fence(Ordering::Acquire);
        if version != unsafe { read_volatile(addr_of!((*info).version)) } {
            continue;
        }
        if mul == 0 || !(-63..=63).contains(&shift) {
            return Err(XenError::Other("uninitialized PV clock"));
        }
        // HVM TSC offsets can wrap the reference stamp below zero at boot.
        // Xen/Mini-OS specify unsigned subtraction, not saturating subtraction.
        return Ok(system.saturating_add(scale(tsc.wrapping_sub(stamp), mul, shift)));
    }
    Err(XenError::Other("unstable PV clock"))
}
fn scale(delta: u64, mul: u32, shift: i8) -> u64 {
    let delta = if shift < 0 {
        u128::from(delta >> (-shift as u32))
    } else {
        u128::from(delta) << (shift as u32)
    };
    ((delta.saturating_mul(u128::from(mul))) >> 32).min(u128::from(u64::MAX)) as u64
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scaling() {
        assert_eq!(scale(100, 1 << 31, 1), 100);
        assert_eq!(scale(100, 1 << 31, -1), 25);
        assert_eq!(scale(10, 1 << 31, 0), 5);
        assert_eq!(scale(7u64.wrapping_sub(u64::MAX - 2), 1 << 31, 1), 10);
    }
}
