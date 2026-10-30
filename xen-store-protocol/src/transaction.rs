//! Validated XenStore transaction identifiers and explicit completion payloads.
//! An identifier is a daemon claim, not authorization or proof of durable
//! commit. The runtime binds it to the same exclusive connection and borrowed
//! scope.

use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Mathematical value of a sequence of decimal digits.
pub open spec fn number(digits: Seq<u8>) -> int
    decreases digits.len(),
{
    if digits.len() == 0 { 0 }
    else { number(digits.drop_last()) * 10 + digits.last() as int - 48 }
}

/// All bytes belong to the decimal digit alphabet.
pub open spec fn digits(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len() ==> 48 <= #[trigger] bytes[i] <= 57
}

/// Canonical positive u32 followed by exactly one terminal NUL, as emitted by
/// XenStore's transaction-start response. No whitespace/sign/leading zero.
pub open spec fn valid(bytes: Seq<u8>) -> bool {
    &&& 2 <= bytes.len() <= 11
    &&& bytes.last() == 0
    &&& 49 <= bytes[0] <= 57
    &&& digits(bytes.drop_last())
    &&& 0 < number(bytes.drop_last()) <= u32::MAX
}

/// Appending nonnegative decimal digits cannot lower the represented value.
proof fn prefix_bound(bytes: Seq<u8>, length: int)
    requires digits(bytes), 0 <= length <= bytes.len(),
    ensures 0 <= number(bytes.subrange(0, length)) <= number(bytes),
    decreases bytes.len(),
{
    if bytes.len() == 0 { return; }
    prefix_bound(bytes.drop_last(), if length < bytes.len() { length } else { bytes.len()-1 });
    if length < bytes.len() {
        assert(bytes.drop_last().subrange(0, length) =~= bytes.subrange(0, length));
    } else {
        assert(bytes.subrange(0, length) =~= bytes);
    }
    assert(number(bytes) >= number(bytes.drop_last()));
}

/// Well-formed daemon transaction identifier. Non-clonable runtime scopes consume
/// it when issuing their single commit/abort, without automatically replaying.
pub struct Id {
    /// Positive wire identifier, meaningful only on its originating connection.
    value: u32,
}

impl Id {
    /// Numeric wire identity without exposing mutable representation.
    pub closed spec fn identity(&self) -> u32 { self.value }

    /// Parse hostile response bytes, proving both acceptance and rejection.
    pub fn parse(bytes: &[u8]) -> (id: Option<Self>)
        ensures match id {
            Some(value) => valid(bytes@) && value.identity() == number(bytes@.drop_last()),
            None => !valid(bytes@),
        },
    {
        if bytes.len() < 2 || bytes.len() > 11 { return None; }
        if bytes[bytes.len()-1] != 0 || bytes[0] < b'1' || bytes[0] > b'9' { return None; }
        let mut i = 0;
        let mut value: u32 = 0;
        while i < bytes.len()-1
            invariant i <= bytes.len()-1, 2 <= bytes@.len() <= 11,
                bytes@[bytes@.len()-1] == 0, 49 <= bytes@[0] <= 57,
                digits(bytes@.subrange(0, i as int)),
                value == number(bytes@.subrange(0, i as int)),
            decreases bytes.len()-1-i,
        {
            let byte = bytes[i];
            if byte < b'0' || byte > b'9' {
                assert(bytes@.drop_last()[i as int] == byte);
                assert(!digits(bytes@.drop_last()));
                return None;
            }
            let next = value as u64 * 10 + (byte - b'0') as u64;
            assert(bytes@.subrange(0, i as int + 1).drop_last() =~= bytes@.subrange(0, i as int));
            assert(next == number(bytes@.subrange(0, i as int + 1)));
            if next > u32::MAX as u64 {
                proof {
                    if valid(bytes@) {
                        prefix_bound(bytes@.drop_last(), i as int + 1);
                        assert(bytes@.drop_last().subrange(0, i as int + 1) =~= bytes@.subrange(0, i as int + 1));
                        assert(false);
                    }
                }
                return None;
            }
            value = next as u32;
            i += 1;
        }
        assert(bytes@.subrange(0, i as int) =~= bytes@.drop_last());
        proof { prefix_bound(bytes@.drop_last(), 1); }
        Some(Self { value })
    }

    /// Read the validated identifier while the transaction scope remains live.
    pub fn wire(&self) -> (id: u32)
        ensures id == self.identity(),
    { self.value }

    /// Encode completion for the runtime's consuming transaction scope. The
    /// identifier itself is only a validated daemon claim, not authority to end
    /// transactions; connection/scope ownership is enforced at the adapter.
    pub fn finish(&self, commit: bool) -> (request: (u32, [u8; 2]))
        ensures request.0 == self.identity(),
            request.1@[0] == if commit { 84u8 } else { 70u8 }, request.1@[1] == 0,
    { (self.value, [if commit { b'T' } else { b'F' }, 0]) }
}

/// Only the daemon's exact acknowledgement is considered successful completion.
pub fn acknowledged(bytes: &[u8]) -> (ack: bool)
    ensures ack == (bytes@ == seq![79u8, 75u8, 0u8]),
{
    let ack = bytes.len() == 3 && bytes[0] == b'O' && bytes[1] == b'K' && bytes[2] == 0;
    if ack { assert(bytes@ =~= seq![79u8, 75u8, 0u8]); }
    ack
}

}
