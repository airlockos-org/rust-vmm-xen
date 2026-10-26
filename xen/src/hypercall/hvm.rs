use xen_sys::{
    bindings::{
        __HYPERVISOR_hvm_op, xen_hvm_get_time, xen_hvm_param, HVMOP_get_param, HVMOP_get_time,
        HVMOP_set_param,
    },
    error::XenError,
    DomId, XenConstBuffer, XenHypercall, XenMutBuffer,
};

pub trait XenHvmOp: XenHypercall {
    fn set_hvm_param(&self, index: u32, value: u64) -> Result<(), XenError> {
        let param = xen_hvm_param {
            domid: DomId::SELF.0,
            index,
            pad: 0,
            value,
        };
        let buffer = self.make_const_object(&param)?;
        unsafe {
            self.hypercall2(
                __HYPERVISOR_hvm_op as _,
                [HVMOP_set_param as _, buffer.as_hypercall_ptr().addr()],
            )?;
        }
        Ok(())
    }

    /// Xen monotonic system time in nanoseconds, paired with shared-info
    /// wallclock.
    fn get_time(&self) -> Result<u64, XenError> {
        let mut time = xen_hvm_get_time { now: 0 };
        let mut buffer = self.make_mut_object(&mut time)?;
        unsafe {
            self.hypercall2(
                __HYPERVISOR_hvm_op as _,
                [HVMOP_get_time as _, buffer.as_hypercall_ptr().addr()],
            )?;
            buffer.update();
        }
        drop(buffer);
        Ok(time.now)
    }

    fn get_hvm_param(&self, index: u32) -> Result<u64, XenError> {
        let mut param = xen_hvm_param {
            domid: DomId::SELF.0,
            index,
            pad: 0,
            value: 0,
        };
        let mut param_buffer = self.make_mut_object(&mut param)?;

        unsafe {
            self.hypercall2(
                __HYPERVISOR_hvm_op as _,
                [HVMOP_get_param as _, param_buffer.as_hypercall_ptr().addr()],
            )?;
            param_buffer.update();
            drop(param_buffer);
        };

        Ok(param.value)
    }
}

impl<H: XenHypercall> XenHvmOp for H {}
