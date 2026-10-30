//! Standard backend descriptors for the negotiated one-page, no-offload
//! profile. Grant numbers are peer claims, never mapping authority. The adapter
//! supplies the exact controller-authorized source/destination domain to Xen
//! grant copy. Decoding uses a private snapshot; no later shared descriptor
//! reread is valid.

use vstd::prelude::*;

use crate::{Frame, Invalid, PAGE, get16, put16};
#[cfg(verus_keep_ghost)]
use crate::{word16, word32};

verus! {

/// Decode one native grant reference from the private fixed-size descriptor.
fn get32(bytes: &[u8], at: usize) -> (word: u32)
    requires 4 <= bytes@.len() <= usize::MAX, at <= bytes@.len()-4,
    ensures word == word32(bytes@, at as int),
{
    get16(bytes, at) as u32 + get16(bytes, at+2) as u32 * 65536
}

/// One bounded outgoing frame from a frontend's private descriptor snapshot.
/// Ownership of the enclosing interface supplies the domain; this does not.
pub struct Transmit {
    /// Frontend-selected source grant, meaningful only in that same domain.
    grant: u32,
    /// Frontend-selected completion label, echoed without treating it as authority.
    id: u16,
    /// Validated source range, wholly inside the one grant page.
    frame: Frame,
}

impl Transmit {
    /// Source range remains bounded independently of the mutable peer memory.
    pub closed spec fn valid(&self) -> bool { self.frame.valid() }

    /// Exact frontend grant label copied from the descriptor.
    pub closed spec fn reference(&self) -> u32 { self.grant }

    /// Exact completion label copied from the descriptor.
    pub closed spec fn identity(&self) -> u16 { self.id }

    /// Validated first packet byte.
    pub closed spec fn start(&self) -> usize { self.frame.start() }

    /// Validated packet length.
    pub closed spec fn size(&self) -> usize { self.frame.size() }

    /// Source grant for a synchronous copy from this interface's exact peer.
    pub fn grant(&self) -> (grant: u32)
        ensures grant == self.reference(),
    { self.grant }

    /// Validated byte offset for the grant-copy source.
    pub fn offset(&self) -> (offset: u16)
        requires self.valid(),
        ensures offset == self.start(), offset < PAGE,
    { self.frame.offset as u16 }

    /// Number of bytes authorized for one synchronous grant copy.
    pub fn len(&self) -> (length: u16)
        requires self.valid(),
        ensures length == self.size(), 0 < length <= PAGE,
    { self.frame.length as u16 }

    /// A successfully decoded TX descriptor always carries bytes.
    pub fn is_empty(&self) -> (empty: bool)
        requires self.valid(), ensures !empty,
    { false }

    /// Respond only after the matching grant-copy result is known. A peer error
    /// is explicit; neither success nor this descriptor promises network delivery.
    pub fn response(self, copied: bool) -> (bytes: [u8; 4])
        ensures word16(bytes@, 0) == self.identity(),
            word16(bytes@, 2) == if copied { 0int } else { 65535int },
    {
        let mut bytes = [0; 4];
        put16(&mut bytes, 0, self.id);
        put16(&mut bytes, 2, if copied { 0 } else { 65535 });
        bytes
    }
}

/// Accept a normal complete frontend packet, not fragments or extra records.
/// data_validated is only a checksum hint. CHECKSUM_PARTIAL is unsupported and
/// must have been disabled by XenStore feature negotiation before connection.
pub fn transmit(bytes: &[u8; 12]) -> (packet: Result<Transmit, Invalid>)
    ensures match packet {
        Ok(value) => value.valid() && value.reference() == word32(bytes@, 0)
            && value.identity() == word16(bytes@, 8) && value.start() == word16(bytes@, 4)
            && value.size() == word16(bytes@, 10) && (word16(bytes@, 6) == 0 || word16(bytes@, 6) == 2),
        Err(_) => !((word16(bytes@, 6) == 0 || word16(bytes@, 6) == 2)
            && 0 < word16(bytes@, 10) && word16(bytes@, 4) + word16(bytes@, 10) <= PAGE),
    },
{
    let flags = get16(bytes, 6);
    if flags != 0 && flags != 2 { return Err(Invalid::Flags); }
    let offset = get16(bytes, 4) as usize;
    let length = get16(bytes, 10) as usize;
    if length == 0 || length > PAGE || offset > PAGE-length { return Err(Invalid::Bounds); }
    Ok(Transmit { grant: get32(bytes, 0), id: get16(bytes, 8), frame: Frame { offset, length } })
}

/// A frontend receive buffer. Padding is ignored: native ring unions may retain
/// an old response there, and the netif ABI assigns it no request semantics.
pub struct ReceiveBuffer {
    /// Destination grant in the controller-selected frontend domain.
    grant: u32,
    /// Label echoed in exactly the response consuming this request.
    id: u16,
}

impl ReceiveBuffer {
    /// Exact destination grant claim copied from the request.
    pub closed spec fn reference(&self) -> u32 { self.grant }

    /// Exact completion label copied from the request.
    pub closed spec fn identity(&self) -> u16 { self.id }

    /// Destination for a synchronous grant copy to this interface's exact peer.
    pub fn grant(&self) -> (grant: u32)
        ensures grant == self.reference(),
    { self.grant }

    /// Encode a response only for a bounded successful copy, or an explicit
    /// error status. Consuming the request prevents issuing two completions
    /// through the same descriptor object. Copy failure reports no packet bytes.
    pub fn response(self, length: usize, copied: bool) -> (response: Result<[u8; 8], Invalid>)
        ensures match response {
            Ok(bytes) => word16(bytes@, 0) == self.identity() && word16(bytes@, 2) == 0
                && word16(bytes@, 4) == 0
                && if copied { 0 < length <= PAGE && word16(bytes@, 6) == length }
                    else { word16(bytes@, 6) == 65535 },
            Err(_) => copied && (length == 0 || length > PAGE),
        },
    {
        if copied && (length == 0 || length > PAGE) { return Err(Invalid::Bounds); }
        let mut bytes = [0; 8];
        put16(&mut bytes, 0, self.id);
        put16(&mut bytes, 6, if copied { length as u16 } else { 65535 });
        Ok(bytes)
    }
}

/// Snapshot one RX request; no peer length or offset is accepted from it.
pub fn receive_buffer(bytes: &[u8; 8]) -> (buffer: ReceiveBuffer)
    ensures buffer.reference() == word32(bytes@, 4), buffer.identity() == word16(bytes@, 0),
{ ReceiveBuffer { grant: get32(bytes, 4), id: get16(bytes, 0) } }

/// Validate an application packet length before copying or granting any bytes.
pub fn packet_length(bytes: usize) -> (length: Option<u16>)
    ensures match length {
        Some(value) => value == bytes && 0 < bytes <= PAGE,
        None => bytes == 0 || bytes > PAGE,
    },
{ if bytes == 0 || bytes > PAGE { None } else { Some(bytes as u16) } }

/// Canonical unsigned decimal wire claim; parsing does not create authority.
pub fn number_claim(bytes: &[u8]) -> (value: Option<u32>)
    ensures match value {
        Some(value) => (bytes@ == seq![b'0'] && value == 0)
            || (xen_store_protocol::transaction::valid_token(bytes@)
                && value == xen_store_protocol::transaction::number(bytes@)),
        None => bytes@ != seq![b'0'] && !xen_store_protocol::transaction::valid_token(bytes@),
    },
{
    if bytes.len() == 1 && bytes[0] == b'0' {
        assert(bytes@ =~= seq![b'0']);
        return Some(0);
    }
    xen_store_protocol::transaction::Id::parse_token(bytes).map(
        |value: xen_store_protocol::transaction::Id| -> (wire: u32)
            ensures wire == value.identity(),
        { value.wire() }
    )
}

}
