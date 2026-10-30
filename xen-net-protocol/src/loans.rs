//! One pinned data page's volatile ownership across a netif request.
//! Publication is recorded before the grant/ring effect. A response alone never
//! permits reuse: the adapter must also observe successful Xen grant
//! revocation. Failed or expired effects retain a charged, quarantined page
//! until teardown. These are logical transitions, not evidence that the
//! underlying page exists, was uniquely charged, or was revoked; those remain
//! explicit adapter duties.

use vstd::prelude::*;

use crate::Receive;

verus! {

/// Which native netif ring may complete this page loan.
pub enum Direction {
    /// Backend may read the frontend's outgoing packet.
    Transmit,
    /// Backend may write one incoming packet.
    Receive,
}

/// A validated descriptor result; it does not by itself authorize page access.
pub enum Completion {
    /// Peer acknowledgement, not a guarantee of delivery on the network.
    Transmit(/// Whether the peer reported success rather than drop/error.
        bool),
    /// Bounded RX metadata, released to the caller only after revocation.
    Receive(/// Validated packet range or explicit drop.
        Receive),
}

impl Completion {
    /// Validate direction at runtime too: a safe caller cannot turn a TX
    /// completion into ownership of an RX page by violating a proof precondition.
    fn accepts(&self, direction: &Direction) -> (accepted: bool)
        ensures accepted == self.valid_for(direction),
    {
        match (self, direction) {
            (Self::Transmit(_), Direction::Transmit) => true,
            (Self::Receive(Receive::Dropped), Direction::Receive) => true,
            (Self::Receive(Receive::Packet(frame)), Direction::Receive) => frame.bounded(),
            _ => false,
        }
    }

    /// The payload agrees with the ring's fixed direction and page bounds.
    pub closed spec fn valid_for(&self, direction: &Direction) -> bool {
        match (self, direction) {
            (Self::Transmit(_), Direction::Transmit) => true,
            (Self::Receive(Receive::Dropped), Direction::Receive) => true,
            (Self::Receive(Receive::Packet(frame)), Direction::Receive) => frame.valid(),
            _ => false,
        }
    }
}

/// Related ownership facts are kept in one state, never independent flags.
enum Phase {
    /// No grant publication has been attempted since last successful revoke.
    Private,
    /// A grant or descriptor may have been published; effect may be ambiguous.
    Offered {
        /// Absolute monotonic deadline, shared across publication/completion.
        expires: u64,
    },
    /// Matching completion was copied, but the peer may still retain a mapping.
    Completed {
        /// Original deadline, never extended by a peer response.
        expires: u64,
        /// Validated outcome retained while revocation is pending.
        outcome: Completion,
    },
    /// No safe reuse is possible; retain the backing page and grant accounting.
    Quarantined,
}

/// Exclusive logical loan state for one pinned page. It is intentionally neither
/// Clone nor a memory capability; the adapter binds it to exactly one real page.
pub struct Page {
    /// Ring direction fixed before any grant is offered.
    direction: Direction,
    /// Publication, completion and reclamation are one ordered state machine.
    phase: Phase,
}

impl Page {
    /// All retained descriptor metadata has already passed bounds validation.
    pub closed spec fn valid(&self) -> bool {
        match &self.phase {
            Phase::Completed { outcome, .. } => outcome.valid_for(&self.direction),
            _ => true,
        }
    }

    /// No grant publication is currently allowed to retain a peer mapping.
    pub closed spec fn private(&self) -> bool { matches!(self.phase, Phase::Private) }

    /// Publication may have happened and no matching completion was accepted.
    pub closed spec fn offered(&self) -> bool { matches!(self.phase, Phase::Offered { .. }) }

    /// Completion is known but revocation remains pending.
    pub closed spec fn completed(&self) -> bool { matches!(self.phase, Phase::Completed { .. }) }

    /// Retained resources may not be reused in this domain lifetime.
    pub closed spec fn quarantined(&self) -> bool { matches!(self.phase, Phase::Quarantined) }

    /// Fixed native ring direction.
    pub closed spec fn direction(&self) -> Direction { self.direction }

    /// Exact state preservation on a rejected operation.
    pub closed spec fn same_state(&self, other: &Self) -> bool {
        self.phase == other.phase && self.direction == other.direction
    }

    /// The outcome is precisely the completion retained for this loan.
    pub closed spec fn completion_is(&self, value: &Completion) -> bool {
        match &self.phase { Phase::Completed { outcome, .. } => *outcome == *value, _ => false }
    }

    /// Original absolute deadline for any active grant; zero when inactive.
    pub closed spec fn deadline(&self) -> u64 {
        match self.phase {
            Phase::Offered { expires } | Phase::Completed { expires, .. } => expires,
            _ => 0,
        }
    }

    /// Create the logical owner before the first grant effect.
    pub fn new(direction: Direction) -> (page: Self)
        ensures page.valid(), page.private(), page.direction() == direction,
    { Self { direction, phase: Phase::Private } }

    /// Whether the runtime may write or clear its private data page.
    pub fn reusable(&self) -> (ready: bool)
        ensures ready == self.private(),
    { matches!(self.phase, Phase::Private) }

    /// Charge potential peer ownership before attempting publication. Invalid
    /// sequencing is rejected without extending an existing deadline.
    pub fn offer(&mut self, expires: u64) -> (accepted: bool)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).direction() == old(self).direction(),
            accepted == old(self).private(),
            accepted ==> final(self).offered() && final(self).deadline() == expires,
            !accepted ==> final(self).same_state(old(self)),
    {
        if !matches!(self.phase, Phase::Private) { return false; }
        self.phase = Phase::Offered { expires };
        true
    }

    /// Whether a matching native descriptor may complete this loan.
    pub fn awaiting(&self) -> (waiting: bool)
        ensures waiting == self.offered(),
    { matches!(self.phase, Phase::Offered { .. }) }

    /// Whether the runtime should make one nonblocking revoke attempt.
    pub fn revoking(&self) -> (pending: bool)
        ensures pending == self.completed(),
    { matches!(self.phase, Phase::Completed { .. }) }

    /// Accept one validated result for the offered page's fixed direction.
    /// A duplicate/unexpected completion leaves the existing ownership intact.
    /// The supplied reclamation deadline may shorten, never extend, the loan.
    /// RX buffers can be offered with u64::MAX while legitimately idle; accepting
    /// a completion then starts their finite reclamation budget.
    pub fn complete(&mut self, outcome: Completion, reclaim_deadline: u64) -> (accepted: bool)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).direction() == old(self).direction(),
            accepted == (old(self).offered() && outcome.valid_for(&old(self).direction())),
            accepted ==> final(self).completed() && final(self).deadline() == if reclaim_deadline < old(self).deadline() { reclaim_deadline } else { old(self).deadline() }
                && final(self).completion_is(&outcome),
            !accepted ==> final(self).same_state(old(self)),
    {
        if !outcome.accepts(&self.direction) { return false; }
        match self.phase {
            Phase::Offered { expires } => {
                let expires = if reclaim_deadline < expires { reclaim_deadline } else { expires };
                self.phase = Phase::Completed { expires, outcome };
                true
            },
            _ => false,
        }
    }

    /// Take a completion only after the adapter confirms successful revoke of
    /// this exact page's grant. False retains the page; this performs no retry,
    /// waiting, I/O or allocation. Clock expiry is checked separately so a final
    /// successful revoke may be recognized even at the deadline.
    pub fn reclaim(&mut self, revoked: bool) -> (outcome: Option<Completion>)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).direction() == old(self).direction(),
            match outcome {
                Some(value) => revoked && old(self).completed() && final(self).private()
                    && value.valid_for(&final(self).direction()) && old(self).completion_is(&value),
                None => final(self).same_state(old(self)) && (!revoked || !old(self).completed()),
            },
    {
        if !revoked || !matches!(self.phase, Phase::Completed { .. }) { return None; }
        let mut phase = Phase::Private;
        core::mem::swap(&mut self.phase, &mut phase);
        match phase {
            Phase::Completed { outcome, .. } => Some(outcome),
            _ => None,
        }
    }

    /// Expire only an active loan using the original absolute deadline. The
    /// monotonic, nonwrapping clock and correspondence to scheduling are trusted.
    pub fn expire(&mut self, now: u64) -> (expired: bool)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).direction() == old(self).direction(),
            expired == ((old(self).offered() || old(self).completed()) && now >= old(self).deadline()),
            expired ==> final(self).quarantined(),
            !expired ==> final(self).same_state(old(self)),
    {
        let expired = match self.phase {
            Phase::Offered { expires } | Phase::Completed { expires, .. } => now >= expires,
            _ => false,
        };
        if expired { self.phase = Phase::Quarantined; }
        expired
    }

    /// Quarantine before returning an ambiguous effect error. This deliberately
    /// performs no fallible cleanup and provides no path back to Private.
    pub fn quarantine(&mut self)
        requires old(self).valid(),
        ensures final(self).valid(), final(self).quarantined(),
            final(self).direction() == old(self).direction(),
    { self.phase = Phase::Quarantined; }
}

}
