//! Single-producer/single-consumer Xen byte rings (console and XenStore).
//! Shared indices are wrapping u32 counters, never offsets modulo capacity.
use core::sync::atomic::{AtomicU32, Ordering};

use volatile::VolatilePtr;

#[derive(Clone, Copy, Debug)]
pub struct XenRing<'a> {
    pub ring: VolatilePtr<'a, [u8]>,
    pub cons: &'a AtomicU32,
    pub prod: &'a AtomicU32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum XenRingError {
    TooLarge,
    NotReady,
    MisbehavingIndex,
}

fn queued(prod: u32, cons: u32, len: usize) -> Result<usize, XenRingError> {
    let n = prod.wrapping_sub(cons) as usize;
    if n <= len {
        Ok(n)
    } else {
        Err(XenRingError::MisbehavingIndex)
    }
}

impl XenRing<'_> {
    pub fn capacity(&self) -> usize {
        self.ring.len()
    }
    pub fn available(&self) -> usize {
        self.capacity().saturating_sub(self.queued())
    }
    pub fn queued(&self) -> usize {
        queued(
            self.prod.load(Ordering::Acquire),
            self.cons.load(Ordering::Acquire),
            self.capacity(),
        )
        .unwrap_or(self.capacity())
    }
    pub fn read(&mut self, buffer: &mut [u8], exact: bool) -> Result<usize, XenRingError> {
        if exact && buffer.len() > self.capacity() {
            return Err(XenRingError::TooLarge);
        }
        let cons = self.cons.load(Ordering::Relaxed);
        let prod = self.prod.load(Ordering::Acquire);
        let n = queued(prod, cons, self.capacity())?;
        if exact && n < buffer.len() {
            return Err(XenRingError::NotReady);
        }
        let n = n.min(buffer.len());
        if n == 0 {
            return Ok(0);
        }
        let start = cons as usize % self.capacity();
        let first = n.min(self.capacity() - start);
        self.ring
            .index(start..start + first)
            .copy_into_slice(&mut buffer[..first]);
        self.ring
            .index(..n - first)
            .copy_into_slice(&mut buffer[first..n]);
        self.cons
            .store(cons.wrapping_add(n as u32), Ordering::Release);
        Ok(n)
    }
    pub fn write(&mut self, buffer: &[u8]) -> Result<(), XenRingError> {
        if buffer.len() > self.capacity() {
            return Err(XenRingError::TooLarge);
        }
        let prod = self.prod.load(Ordering::Relaxed);
        let cons = self.cons.load(Ordering::Acquire);
        let n = queued(prod, cons, self.capacity())?;
        if buffer.len() > self.capacity() - n {
            return Err(XenRingError::NotReady);
        }
        if buffer.is_empty() {
            return Ok(());
        }
        let start = prod as usize % self.capacity();
        let first = buffer.len().min(self.capacity() - start);
        self.ring
            .index(start..start + first)
            .copy_from_slice(&buffer[..first]);
        self.ring
            .index(..buffer.len() - first)
            .copy_from_slice(&buffer[first..]);
        self.prod
            .store(prod.wrapping_add(buffer.len() as u32), Ordering::Release);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use core::ptr::NonNull;

    use super::*;
    #[test]
    fn full_ring_and_u32_wrap() {
        let mut bytes = [0u8; 8];
        let cons = AtomicU32::new(u32::MAX - 3);
        let prod = AtomicU32::new(u32::MAX - 3);
        let mut ring = XenRing {
            ring: unsafe { VolatilePtr::new(NonNull::from(&mut bytes[..])) },
            cons: &cons,
            prod: &prod,
        };
        ring.write(b"abcdefgh").unwrap();
        assert_eq!(ring.queued(), 8);
        assert_eq!(ring.available(), 0);
        assert_eq!(ring.write(b"x"), Err(XenRingError::NotReady));
        let mut out = [0; 8];
        assert_eq!(ring.read(&mut out[..3], true), Ok(3));
        ring.write(b"ijk").unwrap();
        assert_eq!(ring.read(&mut out, true), Ok(8));
        assert_eq!(&out, b"defghijk");
        assert_eq!(ring.queued(), 0);
        assert_eq!(ring.read(&mut out, true), Err(XenRingError::NotReady));
        prod.store(
            cons.load(Ordering::Relaxed).wrapping_add(9),
            Ordering::Relaxed,
        );
        assert_eq!(ring.write(b"x"), Err(XenRingError::MisbehavingIndex));
    }
}
