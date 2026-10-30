//! Validate standard toolstack vif links against an explicitly selected peer.
//! The expected domain is authorization supplied by the interface owner; parsed
//! XenStore IDs and paths are observations. The adapter reads its own `domid`
//! from its domain-owned store connection and preserves that association.

extern crate alloc;
use alloc::vec::Vec;

use vstd::prelude::*;
use xen_store_protocol::transaction::Id;
#[cfg(verus_keep_ghost)]
use xen_store_protocol::transaction::{number, valid_token};

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Canonical Xen domain IDs exclude the hypervisor's reserved pseudo-domains.
pub open spec fn domain(bytes: Seq<u8>, expected: u16) -> bool {
    (bytes == seq![b'0'] && expected == 0)
        || (valid_token(bytes) && number(bytes) == expected && expected < 0x7ff0)
}

/// Compare a hostile decimal claim to the exact controller-selected domain.
/// The returned boolean creates no authority and cannot select another peer.
pub fn domain_matches(bytes: &[u8], expected: u16) -> (matched: bool)
    ensures matched == domain(bytes@, expected),
{
    if bytes.len() == 1 && bytes[0] == b'0' {
        assert(bytes@ =~= seq![b'0']);
        return expected == 0;
    }
    match Id::parse_token(bytes) {
        Some(value) => value.wire() == expected as u32 && expected < 0x7ff0,
        None => false,
    }
}

/// A well-formed own-domain label, not authorization to choose a domain.
fn own_domain(bytes: &[u8]) -> (valid: bool)
    ensures valid == (valid_token(bytes@) && number(bytes@) < 0x7ff0),
{
    match Id::parse_token(bytes) {
        Some(value) => value.wire() < 0x7ff0,
        None => false,
    }
}

/// Append bounded path fragments while preserving exact byte correspondence.
fn append(bytes: &mut Vec<u8>, part: &[u8])
    requires old(bytes)@.len() + part@.len() <= 256,
    ensures final(bytes)@ == old(bytes)@ + part@,
{
    let ghost before = bytes@;
    let mut i = 0;
    while i < part.len()
        invariant i <= part.len(), bytes@ == before + part@.subrange(0, i as int),
            before.len() + part@.len() <= 256,
        decreases part.len()-i,
    {
        bytes.push(part[i]);
        i += 1;
        assert(part@.subrange(0, i as int) =~= part@.subrange(0, i as int-1).push(part@[i as int-1]));
    }
    assert(part@.subrange(0, part@.len() as int) =~= part@);
}

/// Validate the standard backend path before the adapter follows it. The
/// returned match preserves the exact bytes it may append `/frontend` to.
pub fn backend_linked(peer: u16, peer_digits: &[u8], own_digits: &[u8], backend: &[u8]) -> (valid: bool)
    ensures valid == (domain(peer_digits@, peer)
        && valid_token(own_digits@) && number(own_digits@) < 0x7ff0
        && backend@ == b"/local/domain/"@ + peer_digits@ + b"/backend/vif/"@ + own_digits@ + b"/0"@),
{
    if !domain_matches(peer_digits, peer) || !own_domain(own_digits) { return false; }
    let mut expected = Vec::new();
    append(&mut expected, b"/local/domain/");
    append(&mut expected, peer_digits);
    append(&mut expected, b"/backend/vif/");
    append(&mut expected, own_digits);
    append(&mut expected, b"/0");
    equal(&expected, backend)
}

/// Validate the reciprocal frontend path for this same domain's vif/0.
pub fn frontend_linked(own_digits: &[u8], reciprocal: &[u8]) -> (valid: bool)
    ensures valid == (valid_token(own_digits@) && number(own_digits@) < 0x7ff0
        && reciprocal@ == b"/local/domain/"@ + own_digits@ + b"/device/vif/0"@),
{
    if !own_domain(own_digits) { return false; }
    let mut front = Vec::new();
    append(&mut front, b"/local/domain/");
    append(&mut front, own_digits);
    append(&mut front, b"/device/vif/0");
    equal(&front, reciprocal)
}

/// Exact bounded byte equality; oversized peer strings are rejected by length.
fn equal(left: &[u8], right: &[u8]) -> (same: bool)
    requires left@.len() <= 256,
    ensures same == (left@ == right@),
{
    if left.len() != right.len() { return false; }
    let mut i = 0;
    while i < left.len()
        invariant i <= left.len(), left@.len() == right@.len(), left@.len() <= 256,
            forall|j: int| 0 <= j < i ==> left@[j] == right@[j],
        decreases left.len()-i,
    {
        if left[i] != right[i] { return false; }
        i += 1;
    }
    assert(left@ =~= right@);
    true
}

}
