//! Monotonic initialization state for one domain's shared XenStore connection.
//! The runtime serializes effects and installs the actual connection before
//! publishing success. This machine proves initialization cannot be repeated
//! after an attempted mapping, including interrupted or failed initialization.

use vstd::prelude::*;

verus! {

/// Only initialization may advance an unused connection to usable state.
enum Phase {
    /// No XenStore effect has been attempted in this domain.
    Fresh,
    /// Initialization is in flight; interruption must not allow another attempt.
    Opening,
    /// The runtime has installed the sole connection and its private counters.
    Ready,
    /// An uncertain failure forbids further effects until domain teardown.
    Failed,
}

/// One domain's non-clonable connection initialization permission.
pub struct Gate {
    /// Monotonic lifecycle, separate from the platform's synchronization primitive.
    phase: Phase,
}

impl Default for Gate {
    /// Reserve a fresh domain's initialization permission.
    fn default() -> Self { Self::new() }
}

impl Gate {
    /// Whether the connection is available for serialized exchanges.
    pub closed spec fn ready(&self) -> bool { self.phase == Phase::Ready }

    /// Whether initialization has never been attempted.
    pub closed spec fn unused(&self) -> bool { self.phase == Phase::Fresh }

    /// Whether the runtime owes an initialization completion outcome.
    pub closed spec fn opening(&self) -> bool { self.phase == Phase::Opening }

    /// Whether failure is terminal for this domain lifetime.
    pub closed spec fn failed(&self) -> bool { self.phase == Phase::Failed }

    /// Equality of lifecycle state, without exposing its representation.
    pub closed spec fn same_as(&self, other: &Self) -> bool { self.phase == other.phase }

    /// Reserve the domain's sole initialization permission at boot.
    pub const fn new() -> (gate: Self)
        ensures gate.unused(), !gate.ready(), !gate.opening(), !gate.failed(),
    { Self { phase: Phase::Fresh } }

    /// Consume initialization permission before the runtime attempts any effect.
    pub fn begin(&mut self) -> (accepted: bool)
        ensures accepted == old(self).unused(),
            accepted ==> final(self).opening() && !final(self).unused() && !final(self).ready(),
            !accepted ==> final(self).same_as(old(self)),
    {
        match self.phase {
            Phase::Fresh => { self.phase = Phase::Opening; true },
            _ => false,
        }
    }

    /// Publish a completed initialization outcome. Success requires the runtime
    /// to have installed the connection; false represents a failed effect.
    pub fn finish(&mut self, success: bool) -> (ready: bool)
        ensures ready == (old(self).opening() && success),
            old(self).opening() ==> final(self).ready() == success,
            old(self).opening() && !success ==> final(self).failed(),
            !old(self).opening() ==> final(self).same_as(old(self)),
            old(self).opening() ==> !final(self).unused(),
    {
        match self.phase {
            Phase::Opening => {
                self.phase = if success { Phase::Ready } else { Phase::Failed };
                success
            },
            _ => false,
        }
    }

    /// Observe readiness without changing the sole initialization permission.
    pub fn usable(&self) -> (ready: bool)
        ensures ready == self.ready(),
    { matches!(self.phase, Phase::Ready) }

    /// Quarantine the connection after ambiguous stream/caller failure.
    pub fn poison(&mut self)
        ensures final(self).failed(), !final(self).ready(), !final(self).unused(),
    { self.phase = Phase::Failed; }
}

}
