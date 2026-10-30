//! Bounded XenStore protocol with a verified executable core.
//!
//! `xen-store-protocol` owns framing, validation and connection transitions.
//! This adapter preserves the callback-shaped API; the callback is an explicit
//! unverified effect boundary. It must finish in bounded time and account for
//! any retained event storage. Runtime transports must implement the documented
//! exclusive-stream, byte-copy and deadline contracts of `Transport`.

extern crate alloc;

use alloc::vec::Vec;

pub use xen_store_protocol::{
    domain, ring, text_length, transaction, Error, Operation, Transport, Watch, MAX_PAYLOAD,
    MAX_WATCHES,
};

/// Connection state whose protocol decisions execute the verified
/// implementation.
pub struct Client {
    /// Sole request identity and failure state; never reconstructed by this
    /// adapter.
    inner: xen_store_protocol::Client,
}

impl Default for Client {
    fn default() -> Self {
        Self::new()
    }
}

impl Client {
    /// Create state for one freshly provisioned, exclusively owned stream.
    pub const fn new() -> Self {
        Self {
            inner: xen_store_protocol::Client::new(),
        }
    }

    /// Preserve semantic uncertainty by refusing subsequent stream operations.
    pub fn poison(&mut self) {
        self.inner.poison();
    }

    /// Observe the core's connection state without reconstructing its rules.
    pub fn usable(&self) -> bool {
        self.inner.usable()
    }

    /// Exchange one request through the verified core. See `Transport` for the
    /// runtime assumptions. A watch flood exceeding `MAX_WATCHES` poisons the
    /// connection rather than monopolizing an exchange indefinitely.
    pub fn exchange<T: Transport>(
        &mut self,
        transport: &mut T,
        operation: Operation,
        transaction: u32,
        body: &[u8],
        watch: impl FnMut(Watch<'_>) -> bool,
    ) -> Result<Vec<u8>, Error<T::Error>> {
        self.inner.exchange(
            transport,
            operation,
            transaction,
            body,
            &mut Callback { watch },
        )
    }
}

/// Compatibility boundary that borrows the same private watch slices directly.
struct Callback<F> {
    /// Caller-owned side effect; false reports inability to retain the event.
    watch: F,
}

impl<F: FnMut(Watch<'_>) -> bool> xen_store_protocol::WatchSink for Callback<F> {
    fn event(&mut self, path: &[u8], token: &[u8]) -> bool {
        (self.watch)(Watch { path, token })
    }
}

#[cfg(test)]
mod tests;
