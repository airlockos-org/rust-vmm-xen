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

/// Canonical positive u32 digits, without a delimiter.
pub open spec fn valid_token(bytes: Seq<u8>) -> bool {
    &&& 1 <= bytes.len() <= 10
    &&& 49 <= bytes[0] <= 57
    &&& digits(bytes)
    &&& 0 < number(bytes) <= u32::MAX
}

/// Canonical positive u32 followed by exactly one terminal NUL, as emitted by
/// XenStore's transaction-start response. No whitespace/sign/leading zero.
pub open spec fn valid(bytes: Seq<u8>) -> bool {
    &&& 2 <= bytes.len() <= 11
    &&& bytes.last() == 0
    &&& valid_token(bytes.drop_last())
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
        if bytes[bytes.len()-1] != 0 { return None; }
        let value = Self::parse_token(vstd::slice::slice_subrange(bytes, 0, bytes.len()-1));
        assert(bytes@.subrange(0, bytes@.len()-1) =~= bytes@.drop_last());
        value
    }

    /// Decode an opaque decimal watch token without allocating or treating the
    /// parsed claim as ownership/authorization for a subscription.
    pub fn parse_token(bytes: &[u8]) -> (id: Option<Self>)
        ensures match id {
            Some(value) => valid_token(bytes@) && value.identity() == number(bytes@),
            None => !valid_token(bytes@),
        },
    {
        if bytes.is_empty() || bytes.len() > 10 { return None; }
        if !(b'1'..=b'9').contains(&bytes[0]) { return None; }
        let mut i = 0;
        let mut value: u32 = 0;
        while i < bytes.len()
            invariant i <= bytes.len(), 1 <= bytes@.len() <= 10, 49 <= bytes@[0] <= 57,
                digits(bytes@.subrange(0, i as int)),
                value == number(bytes@.subrange(0, i as int)),
            decreases bytes.len()-i,
        {
            let byte = bytes[i];
            // Checked radix decoding keeps the executable predicate inside
            // the proof boundary; vstd does not specify u8::is_ascii_digit.
            let digit = match byte.checked_sub(b'0') {
                Some(digit) if digit <= 9 => digit,
                _ => {
                    assert(bytes@[i as int] == byte);
                    assert(!digits(bytes@));
                    return None;
                },
            };
            let next = value as u64 * 10 + digit as u64;
            assert(bytes@.subrange(0, i as int + 1).drop_last() =~= bytes@.subrange(0, i as int));
            assert(next == number(bytes@.subrange(0, i as int + 1)));
            if next > u32::MAX as u64 {
                proof {
                    if valid_token(bytes@) {
                        prefix_bound(bytes@, i as int + 1);
                        assert(false);
                    }
                }
                return None;
            }
            value = next as u32;
            i += 1;
        }
        assert(bytes@.subrange(0, i as int) =~= bytes@);
        proof { prefix_bound(bytes@, 1); }
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

/// Only an explicit commit conflict is retryable on this same connection.
/// Abort errors or other daemon errors leave cleanup uncertain and must be
/// quarantined by the runtime instead of inferred to be successful rollback.
pub fn conflict(commit: bool, bytes: &[u8]) -> (retryable: bool)
    ensures retryable == (commit && bytes@ == seq![69u8, 65u8, 71u8, 65u8, 73u8, 78u8]),
{
    let retryable = commit && bytes.len() == 6 && bytes[0] == b'E'
        && bytes[1] == b'A' && bytes[2] == b'G' && bytes[3] == b'A'
        && bytes[4] == b'I' && bytes[5] == b'N';
    if retryable { assert(bytes@ =~= seq![69u8, 65u8, 71u8, 65u8, 73u8, 78u8]); }
    retryable
}

}
