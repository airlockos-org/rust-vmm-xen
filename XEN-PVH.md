# Native guest integration branch

Upstream: https://github.com/rust-vmm/xen
Base: `a8529dc1e50445e5579a9aa0abd763348460bdcd` (guest interfaces PR #16).

The first two integration commits preserve changes from hermit-xen
`8b2abd8f6989d11071f407eb1d760b7061329c8d`: exported/repaired hypercall and
console-ring helpers, followed by two-level events, versioned PV time and v1 grants.
Existing upstream interfaces and source notices are retained. Linux userspace
adapters live in hermit-xen's xen-transport crate, not in this guest implementation.

ABI references: Xen 4.20.4 public headers; Mini-OS `arch/x86/time.c` at
`229260e02faacab0f4d5ccb82f013480d968d335` (MIT; Rolf Neugebauer, Keir Fraser,
Grzegorz Milos, Robert Kaiser); Mirage Xen event bindings at
`be1cb7e5fdf65d853d0cebefc37c929ce35003e1` (ISC; Martin Lucina).
These references informed PV time scaling and event mask/unmask races. Their
permission notices accompany this branch in XEN-NOTICES.md. New Rust code uses
explicit unsafe boundaries and does not include Linux/Xen implementation sources.

This experimental branch is validated by [hermit-xen](https://github.com/airlockos-org/hermit-xen),
which pins compatible commits of both forks, the Rust toolchain and the test laboratory.
It is not upstream-accepted or production-ready. No AirlockOS policy is included.
Use that repository's recursive checkout and Nix builder for reproducible builds and
real-Xen regression tests. Commit changes here, publish the branch, then update the
integration repository's submodule pointer. Do not rewrite upstream history.

## Network-device reference boundary

The standard netif ABI is Xen 4.20.4 `public/io/netif.h` (MIT). Before adding
network drivers, the integration inspected Mini-OS
`229260e02faacab0f4d5ccb82f013480d968d335` (`netfront.c`) and Mirage net-xen
`03d7ac1065c395f7a0e351ac5e2e0a64a0562d1c` (netfront/netback).
Mini-OS's frontend explicitly lacks fragment/extra handling and supplies no
backend, so it cannot be used as a complete firewall network layer. Mirage's
OCaml implementation is an interoperability reference, not a directly linkable
Hermit Rust driver. Its repository license is ISC; Mini-OS's COPYING gives its
BSD-style default and lists separately GPL-covered features. Retain each file's
provenance/license if any implementation is translated; none of those driver
bodies is copied by the XenStore changes.

Reuse this fork's grants/events/ring facilities and Hermit's existing scheduler
and mapping ownership. Device negotiation uses the one domain XenStore stream
and verified protocol crate; opening another stream per device would consume
other drivers' replies. Network packet layout, feature negotiation and ownership
need their own contracts against the public ABI before integration.
