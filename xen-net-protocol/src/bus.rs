//! Standard XenBus state observations and one interface's volatile lifecycle.
//! XenStore values are claims by the configured peer, never authorization to
//! choose a peer, grant or path. Effect acknowledgements are runtime inputs;
//! they establish protocol completion, not disk or host-crash durability.

use vstd::prelude::*;

verus! {

/// Standard xenbus_state values from Xen's public/io/xenbus.h.
#[derive(Debug, PartialEq, Eq)]
pub enum State {
    /// Device description has not been initialized.
    Unknown,
    /// Frontend/backend is beginning initialization.
    Initialising,
    /// Backend awaits frontend transport publication.
    InitWait,
    /// Transport parameters have been published.
    Initialised,
    /// The peer reports an active connection.
    Connected,
    /// The peer is negotiating connection shutdown.
    Closing,
    /// The peer reports shutdown completion.
    Closed,
    /// Backend is reconfiguring an existing connection.
    Reconfiguring,
    /// Reconfiguration parameters are available.
    Reconfigured,
}

impl State {
    /// Native ASCII digit, independently of the executable encoder.
    pub closed spec fn digit(&self) -> u8 {
        match self {
            Self::Unknown => b'0', Self::Initialising => b'1', Self::InitWait => b'2',
            Self::Initialised => b'3', Self::Connected => b'4', Self::Closing => b'5',
            Self::Closed => b'6', Self::Reconfiguring => b'7', Self::Reconfigured => b'8',
        }
    }

    /// Validate an exact node value after the XenStore layer removes its NUL.
    pub fn matches(&self, bytes: &[u8]) -> (matched: bool)
        ensures matched == (bytes@.len() == 1 && bytes@[0] == self.digit()),
    {
        if bytes.len() != 1 { return false; }
        let digit = match self {
            Self::Unknown => b'0', Self::Initialising => b'1', Self::InitWait => b'2',
            Self::Initialised => b'3', Self::Connected => b'4', Self::Closing => b'5',
            Self::Closed => b'6', Self::Reconfiguring => b'7', Self::Reconfigured => b'8',
        };
        bytes[0] == digit
    }
}

/// Ordered local operations, independent of the untrusted remote state.
enum Phase {
    /// No interface effect has been attempted.
    Fresh,
    /// Opening owns any partially created resources.
    Opening,
    /// Both protocol connection and local publication completed.
    Ready,
    /// New data operations are prohibited while cleanup remains fallible.
    Closing,
    /// All resources were explicitly released; the old owner remains retired.
    Retired,
    /// Effects are ambiguous; all retained resources stay charged.
    Failed,
    /// Cleanup was attempted and its effects are uncertain; never replay it.
    Sealed,
}

/// Non-clonable connection lifecycle. A retired/failed owner cannot reconnect;
/// reconnect requires a fresh resource owner and identity from its controller.
pub struct Life {
    /// Related publication, data access and retirement facts in one machine.
    phase: Phase,
}

impl Default for Life {
    /// Create a fresh interface owner without performing Xen effects.
    fn default() -> Self { Self::new() }
}

impl Life {
    /// No effects have been attempted through this owner.
    pub closed spec fn fresh(&self) -> bool { matches!(self.phase, Phase::Fresh) }

    /// Initialization is incomplete and must not be attempted twice.
    pub closed spec fn opening(&self) -> bool { matches!(self.phase, Phase::Opening) }

    /// The initialized transport may accept new data operations.
    pub closed spec fn ready(&self) -> bool { matches!(self.phase, Phase::Ready) }

    /// Explicit cleanup is in progress.
    pub closed spec fn closing(&self) -> bool { matches!(self.phase, Phase::Closing) }

    /// Successful explicit cleanup retired this owner.
    pub closed spec fn retired(&self) -> bool { matches!(self.phase, Phase::Retired) }

    /// Failure is retained until explicit cleanup or domain teardown.
    pub closed spec fn failed(&self) -> bool { matches!(self.phase, Phase::Failed | Phase::Sealed) }

    /// An operational failure still permits its first explicit cleanup attempt.
    pub closed spec fn cleanup_allowed(&self) -> bool { matches!(self.phase, Phase::Failed) }

    /// Compare state without exposing its representation.
    pub closed spec fn same(&self, other: &Self) -> bool { self.phase == other.phase }

    /// Allocate logical ownership before effects; the adapter charges real pages.
    pub const fn new() -> (life: Self)
        ensures life.fresh(),
    { Self { phase: Phase::Fresh } }

    /// Reserve the sole opening attempt before the first Xen effect.
    pub fn begin(&mut self) -> (accepted: bool)
        ensures accepted == old(self).fresh(),
            accepted ==> final(self).opening(), !accepted ==> final(self).same(old(self)),
    {
        if !matches!(self.phase, Phase::Fresh) { return false; }
        self.phase = Phase::Opening;
        true
    }

    /// Publish readiness only after observing the configured peer Connected
    /// and the acknowledgement of our own Connected write. False quarantines
    /// a partially opened owner rather than reporting an unchanged empty one.
    pub fn connected(&mut self, peer: &[u8], acknowledged: bool) -> (accepted: bool)
        ensures accepted == (old(self).opening() && State::Connected.matches_spec(peer@) && acknowledged),
            old(self).opening() ==> (if accepted { final(self).ready() } else { final(self).failed() }),
            !old(self).opening() ==> final(self).same(old(self)),
    {
        if !matches!(self.phase, Phase::Opening) { return false; }
        let accepted = acknowledged && State::Connected.matches(peer);
        self.phase = if accepted { Phase::Ready } else { Phase::Failed };
        accepted
    }

    /// Check operation admission without reconstructing lifecycle rules.
    pub fn usable(&self) -> (ready: bool)
        ensures ready == self.ready(),
    { matches!(self.phase, Phase::Ready) }

    /// Retain ambiguity before propagating an effect/protocol error.
    pub fn fail(&mut self)
        ensures final(self).failed(), !final(self).ready(),
    {
        self.phase = match self.phase {
            Phase::Closing | Phase::Retired | Phase::Sealed => Phase::Sealed,
            _ => Phase::Failed,
        };
    }

    /// Stop all data operations before the first fallible cleanup effect.
    /// Failed/partial opens may be explicitly cleaned up as well. Once a cleanup
    /// attempt itself fails, its ambiguous effects may not be replayed.
    pub fn close(&mut self) -> (accepted: bool)
        ensures accepted == (old(self).opening() || old(self).ready() || old(self).cleanup_allowed()),
            accepted ==> final(self).closing(), !accepted ==> final(self).same(old(self)),
    {
        if !matches!(self.phase, Phase::Opening | Phase::Ready | Phase::Failed) { return false; }
        self.phase = Phase::Closing;
        true
    }

    /// Retire only on explicit confirmation that the peer protocol is closed,
    /// grants revoked and the event binding released. An error retains charges.
    pub fn released(&mut self, complete: bool) -> (retired: bool)
        ensures retired == (old(self).closing() && complete),
            old(self).closing() ==> (if retired { final(self).retired() } else { final(self).failed() }),
            !old(self).closing() ==> final(self).same(old(self)),
    {
        if !matches!(self.phase, Phase::Closing) { return false; }
        self.phase = if complete { Phase::Retired } else { Phase::Sealed };
        complete
    }
}

impl State {
    /// Exact wire predicate used by lifecycle postconditions.
    pub closed spec fn matches_spec(&self, bytes: Seq<u8>) -> bool {
        bytes.len() == 1 && bytes[0] == self.digit()
    }
}

/// One bounded backend control step for an already authorized interface owner.
#[derive(Debug, PartialEq, Eq)]
pub enum BackendAction {
    /// Frontend has not yet published complete transport parameters.
    Await,
    /// Read/validate parameters and connect once; partial failure is terminal.
    Connect,
    /// Existing transport may keep processing bounded packet work.
    Run,
    /// Stop data processing and explicitly retire the interface.
    Close,
    /// Unsupported/malformed/backward state cannot initiate new effects.
    Reject,
}

/// Functional protocol decision; each call observes only one exact node value.
/// No waiting loop or automatic restart permits one peer to monopolize others.
pub fn backend_action(bytes: &[u8], connected: bool) -> (action: BackendAction)
    ensures match action {
        BackendAction::Await => !connected && (State::Initialising.matches_spec(bytes@) || State::Initialised.matches_spec(bytes@)),
        BackendAction::Connect => !connected && State::Connected.matches_spec(bytes@),
        BackendAction::Run => connected && State::Connected.matches_spec(bytes@),
        BackendAction::Close => State::Closing.matches_spec(bytes@) || State::Closed.matches_spec(bytes@),
        BackendAction::Reject => !(State::Closing.matches_spec(bytes@) || State::Closed.matches_spec(bytes@)
            || State::Connected.matches_spec(bytes@)
            || (!connected && (State::Initialising.matches_spec(bytes@) || State::Initialised.matches_spec(bytes@)))),
    },
{
    if State::Connected.matches(bytes) {
        if connected { BackendAction::Run } else { BackendAction::Connect }
    } else if State::Closing.matches(bytes) || State::Closed.matches(bytes) {
        BackendAction::Close
    } else if !connected && (State::Initialising.matches(bytes) || State::Initialised.matches(bytes)) {
        BackendAction::Await
    } else { BackendAction::Reject }
}

}
