//! Grant-table v1 for auto-translated (PVH/HVM) guests. Pages are never freed
//! by this layer. Callers must pin/quarantine them while revoke or unmap is
//! busy.
use core::{
    ptr::{addr_of_mut, write_volatile},
    sync::atomic::{AtomicU16, Ordering},
};

use xen_sys::{bindings::*, error::XenError, DomId, XenHypercall};

/// A view of a permanently pinned v1 grant frame. Copies share the same
/// mapping; the caller still owns each grant reference and its backing-page
/// lifetime.
#[derive(Clone, Copy)]
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

/// Copy one bounded peer grant range into the start of an exclusively owned
/// local page. Xen's grant-copy ABI is synchronous: after it returns, no
/// foreign mapping of the destination is retained. This avoids mapping a peer
/// data page across packet processing or allowing a stalled peer to retain a
/// local buffer.
///
/// # Safety
/// `local_pfn` identifies a pinned, exclusively owned identity-mapped guest
/// page; the caller must not concurrently access it during the hypercall. The
/// foreign domain must be authorized for this exact interface lifetime. `offset
/// + length` is at most 4096, and length is positive. The caller supplies
/// checked private descriptor fields and discards all destination bytes if the
/// copy fails.
///
/// This is a narrow trusted effect boundary: the hypervisor validates the grant
/// and performs the copy; neither this adapter nor descriptor proofs establish
/// Xen's implementation, memory coherence or physical page ownership.
pub unsafe fn copy_from_grant<H: XenHypercall>(
    hyp: &H,
    peer: DomId,
    grant: u32,
    offset: u16,
    length: u16,
    local_pfn: u64,
) -> Result<(), XenError> {
    let operation = gnttab_copy {
        source: gnttab_copy_gnttab_copy_ptr {
            u: gnttab_copy_gnttab_copy_ptr__bindgen_ty_1 { ref_: grant },
            domid: peer.0,
            offset,
        },
        dest: gnttab_copy_gnttab_copy_ptr {
            u: gnttab_copy_gnttab_copy_ptr__bindgen_ty_1 { gmfn: local_pfn },
            domid: DomId::SELF.0,
            offset: 0,
        },
        len: length,
        flags: GNTCOPY_source_gref as u16,
        status: 0,
    };
    unsafe { copy_grant(hyp, operation) }
}

/// Copy the start of one exclusively owned local page into a peer's receive
/// grant, without establishing any foreign mapping or retained data-page loan.
///
/// # Safety
/// `local_pfn` is a pinned readable identity-mapped guest page, exclusively
/// owned throughout this synchronous hypercall. The peer is authorized for this
/// exact interface lifetime, and `length` is in 1..=4096. Caller bytes must be
/// complete before this call. A successful return establishes only that Xen
/// completed this copy, not that the frontend accepted or delivered the packet.
///
/// The same Xen/physical-page/coherence trust boundary as copy_from_grant
/// applies.
pub unsafe fn copy_to_grant<H: XenHypercall>(
    hyp: &H,
    peer: DomId,
    grant: u32,
    length: u16,
    local_pfn: u64,
) -> Result<(), XenError> {
    let operation = gnttab_copy {
        source: gnttab_copy_gnttab_copy_ptr {
            u: gnttab_copy_gnttab_copy_ptr__bindgen_ty_1 { gmfn: local_pfn },
            domid: DomId::SELF.0,
            offset: 0,
        },
        dest: gnttab_copy_gnttab_copy_ptr {
            u: gnttab_copy_gnttab_copy_ptr__bindgen_ty_1 { ref_: grant },
            domid: peer.0,
            offset: 0,
        },
        len: length,
        flags: GNTCOPY_dest_gref as u16,
        status: 0,
    };
    unsafe { copy_grant(hyp, operation) }
}

/// Execute exactly one synchronous grant-copy operation and preserve both
/// hypercall-level and per-operation failure. No retry or batching occurs here.
///
/// # Safety
/// Both native endpoints and their page lifetimes satisfy the public wrapper's
/// contract. Xen may write only the fixed-size native operation during the
/// call.
unsafe fn copy_grant<H: XenHypercall>(hyp: &H, mut operation: gnttab_copy) -> Result<(), XenError> {
    unsafe {
        hyp.hypercall3(
            __HYPERVISOR_grant_table_op as _,
            [GNTTABOP_copy as _, (&raw mut operation).addr(), 1],
        )?;
    }
    if operation.status != 0 {
        return Err(XenError::Xen(operation.status as isize));
    }
    Ok(())
}
