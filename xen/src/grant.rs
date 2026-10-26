//! Grant-table v1 for auto-translated (PVH/HVM) guests. Pages are never freed
//! by this layer. Callers must pin/quarantine them while revoke or unmap is
//! busy.
use core::{
    ptr::{addr_of_mut, write_volatile},
    sync::atomic::{AtomicU16, Ordering},
};

use xen_sys::{bindings::*, error::XenError, DomId, XenHypercall};

pub struct GrantTable {
    entries: *mut grant_entry_v1,
}
impl GrantTable {
    /// # Safety
    /// Dedicated, pinned, page-aligned guest physical/identity-mapped page.
    /// The page is replaced by Xen's grant-table frame and is never an
    /// allocator page.
    pub unsafe fn initialize<H: XenHypercall>(hyp: &H, page: *mut u8) -> Result<Self, XenError> {
        let mut version = gnttab_set_version { version: 1 };
        unsafe {
            hyp.hypercall3(
                __HYPERVISOR_grant_table_op as _,
                [GNTTABOP_set_version as _, (&raw mut version).addr(), 1],
            )?;
        }
        let mut map = xen_add_to_physmap {
            domid: DomId::SELF.0,
            size: 0,
            space: XENMAPSPACE_grant_table,
            idx: 0,
            gpfn: page.addr() as u64 >> 12,
        };
        unsafe {
            hyp.hypercall2(
                __HYPERVISOR_memory_op as _,
                [XENMEM_add_to_physmap as _, (&raw mut map).addr()],
            )?;
        }
        Ok(Self {
            entries: page.cast(),
        })
    }
    /// # Safety
    /// gref is uniquely owned by caller, backing page pinned, GPA valid; only
    /// the specified authorized peer may receive the reference. v1 uses 32-bit
    /// PFNs.
    pub unsafe fn grant(&self, gref: u32, peer: DomId, pfn: u64) -> Result<(), XenError> {
        if !(8..512).contains(&gref) || pfn > u64::from(u32::MAX) {
            return Err(XenError::Other("grant bounds"));
        }
        unsafe {
            let e = self.entries.add(gref as usize);
            let flags = AtomicU16::from_ptr(addr_of_mut!((*e).flags));
            if flags.load(Ordering::Acquire) != 0 {
                return Err(XenError::Other("grant already active"));
            }
            write_volatile(addr_of_mut!((*e).domid), peer.0);
            write_volatile(addr_of_mut!((*e).frame), pfn as u32);
            flags.store(GTF_permit_access as u16, Ordering::Release);
        }
        Ok(())
    }
    pub fn revoke(&self, gref: u32) -> Result<bool, XenError> {
        if !(8..512).contains(&gref) {
            return Err(XenError::Other("grant bounds"));
        }
        unsafe {
            let flags = AtomicU16::from_ptr(addr_of_mut!((*self.entries.add(gref as usize)).flags));
            let value = flags.load(Ordering::Acquire);
            if value & (GTF_reading | GTF_writing) as u16 != 0 {
                return Ok(false);
            }
            // CAS against Xen acquiring the grant concurrently. Success both
            // withdraws permission and proves no mapping retains the page.
            Ok(flags
                .compare_exchange(value, 0, Ordering::AcqRel, Ordering::Acquire)
                .is_ok())
        }
    }
}
pub struct ForeignMapping {
    address: u64,
    handle: u32,
    active: bool,
}
impl ForeignMapping {
    /// # Safety
    /// Reserved guest physical page, identity mapped and exclusively owned.
    /// No references into it until this succeeds, nor after unmap. The grant
    /// descriptor must come from the authorized channel-establishment
    /// authority.
    pub unsafe fn map<H: XenHypercall>(
        hyp: &H,
        peer: DomId,
        gref: u32,
        address: u64,
    ) -> Result<Self, XenError> {
        if address & 4095 != 0 {
            return Err(XenError::Other("unaligned grant map"));
        }
        let mut arg = gnttab_map_grant_ref {
            host_addr: address,
            flags: GNTMAP_host_map,
            ref_: gref,
            dom: peer.0,
            status: 0,
            handle: 0,
            dev_bus_addr: 0,
        };
        unsafe {
            hyp.hypercall3(
                __HYPERVISOR_grant_table_op as _,
                [GNTTABOP_map_grant_ref as _, (&raw mut arg).addr(), 1],
            )?;
        }
        if arg.status != 0 {
            return Err(XenError::Xen(arg.status as isize));
        }
        Ok(Self {
            address,
            handle: arg.handle,
            active: true,
        })
    }
    pub fn unmap<H: XenHypercall>(&mut self, hyp: &H) -> Result<(), XenError> {
        if !self.active {
            return Ok(());
        }
        let mut arg = gnttab_unmap_grant_ref {
            host_addr: self.address,
            dev_bus_addr: 0,
            handle: self.handle,
            status: 0,
        };
        unsafe {
            hyp.hypercall3(
                __HYPERVISOR_grant_table_op as _,
                [GNTTABOP_unmap_grant_ref as _, (&raw mut arg).addr(), 1],
            )?;
        }
        if arg.status != 0 {
            return Err(XenError::Xen(arg.status as isize));
        }
        self.active = false;
        Ok(())
    }
}
// Deliberately no automatic page reclamation: failed unmap must retain backing
// address space. Platform ownership objects decide whether to quarantine it.
