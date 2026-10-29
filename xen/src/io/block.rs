//! Bounded native x86-64 Xen blkif request encoding.
//! Layout follows Xen's public/io/blkif.h and public/io/protocols.h.
//! A caller owns the ring and pins its grant pages until revocation succeeds.

use core::convert::TryInto;

/// Size of a native request/response union, including eleven segment slots.
pub const SLOT_BYTES: usize = 112;
/// Ring header size from Xen's public/io/ring.h.
pub const HEADER_BYTES: usize = 64;
/// Power-of-two entry count in a single 4096-byte ring page.
pub const SLOTS: u32 = 32;

/// Operations supported by the bounded frontend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Operation {
    /// Copy disk sectors into a granted page.
    Read = 0,
    /// Copy the granted page into disk sectors.
    Write = 1,
    /// Complete previously acknowledged writes to the backend's stable storage.
    Flush = 3,
}

/// Invalid caller requests or contradictory backend responses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Invalid {
    /// Requests must address one to eight whole 512-byte sectors within the
    /// disk.
    Bounds,
    /// Response identity or operation differs from the outstanding request.
    Identity,
    /// Backend refused or failed the request, retaining its signed blkif
    /// status.
    Backend(i16),
}

/// Encode a single-page request without granting access outside that page.
pub fn request(
    operation: Operation,
    handle: u16,
    id: u64,
    sector: u64,
    bytes: usize,
    capacity: u64,
    grant: u32,
) -> Result<[u8; SLOT_BYTES], Invalid> {
    if operation == Operation::Flush {
        if bytes != 0 || sector != 0 {
            return Err(Invalid::Bounds);
        }
    } else if bytes == 0
        || bytes > 4096
        || bytes % 512 != 0
        || sector > capacity
        || (bytes / 512) as u64 > capacity - sector
    {
        return Err(Invalid::Bounds);
    }

    let mut encoded = [0; SLOT_BYTES];
    encoded[0] = operation as u8;
    encoded[1] = u8::from(operation != Operation::Flush);
    encoded[2..4].copy_from_slice(&handle.to_le_bytes());
    encoded[8..16].copy_from_slice(&id.to_le_bytes());
    encoded[16..24].copy_from_slice(&sector.to_le_bytes());
    if bytes != 0 {
        encoded[24..28].copy_from_slice(&grant.to_le_bytes());
        // The first sector is zero; the last is inclusive within the bounce page.
        encoded[29] = (bytes / 512 - 1) as u8;
    }
    Ok(encoded)
}

/// Accept only the exact response to the sole outstanding operation.
pub fn response(bytes: &[u8; 16], id: u64, operation: Operation) -> Result<(), Invalid> {
    if u64::from_le_bytes(bytes[..8].try_into().unwrap()) != id || bytes[8] != operation as u8 {
        return Err(Invalid::Identity);
    }
    let status = i16::from_le_bytes(bytes[10..12].try_into().unwrap());
    if status != 0 {
        return Err(Invalid::Backend(status));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn page_and_disk_bounds_are_checked_before_encoding() {
        for bytes in [512, 4096] {
            let request = request(Operation::Write, 51712, 42, 8, bytes, 16, 129).unwrap();
            assert_eq!(request[1], 1);
            assert_eq!(request[29], (bytes / 512 - 1) as u8);
            assert_eq!(&request[24..28], &129_u32.to_le_bytes());
            assert!(request[30..].iter().all(|byte| *byte == 0));
        }
        for (sector, bytes, capacity) in [
            (0, 0, 16),
            (0, 511, 16),
            (0, 4608, 16),
            (9, 4096, 16),
            (u64::MAX, 512, u64::MAX),
        ] {
            assert_eq!(
                request(Operation::Read, 0, 1, sector, bytes, capacity, 129),
                Err(Invalid::Bounds)
            );
        }
        assert_eq!(request(Operation::Flush, 0, 1, 0, 0, 0, 0).unwrap()[1], 0);
        assert_eq!(
            request(Operation::Flush, 0, 1, 1, 0, 0, 0),
            Err(Invalid::Bounds)
        );
    }

    #[test]
    fn stale_and_failed_responses_are_not_success() {
        let mut reply = [0; 16];
        reply[..8].copy_from_slice(&42_u64.to_le_bytes());
        reply[8] = Operation::Write as u8;
        assert_eq!(response(&reply, 42, Operation::Write), Ok(()));
        assert_eq!(
            response(&reply, 41, Operation::Write),
            Err(Invalid::Identity)
        );
        assert_eq!(
            response(&reply, 42, Operation::Read),
            Err(Invalid::Identity)
        );
        reply[10..12].copy_from_slice(&(-2_i16).to_le_bytes());
        assert_eq!(
            response(&reply, 42, Operation::Write),
            Err(Invalid::Backend(-2))
        );
    }
}
