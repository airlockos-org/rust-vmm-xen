#![no_std]
#![warn(missing_docs)]
//! Small executable primitives shared by Xen guest protocols and services.
//! They do not implement a service loop, application message format or policy.
//! Logical resource owners are not memory capabilities: runtime adapters must
//! charge every real allocation/mapping, preserve exclusive ownership, and
//! confirm release before retiring a token. Failed cleanup remains charged.
//! Volatile ownership is reconstructed only by fresh domain/controller setup;
//! no state here promises crash durability or permits ambiguous effect replay.
//!
//! Clipboard's application ledger additionally tracks admitted participants,
//! retiring connections and allocator byte credits. Those are distinct policy
//! and heap obligations, retained in clipboard core; this library shares the
//! concrete kernel slot/handle and ring mechanics used underneath IPC/netif.

pub mod counters;
pub mod resources;
