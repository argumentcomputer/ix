# Pinned Ixby reference modules

These pure Lean files are copied without changes from
[argumentcomputer/ix, revision `d4405b3ceb82e6d4cce19e48186f3272f8482e04`](https://github.com/argumentcomputer/ix/tree/d4405b3ceb82e6d4cce19e48186f3272f8482e04/Ix/Ixby)
on `jcb/ixby`, except for the four experimental crypto profile/codec files
explicitly retained at `4fdbf4084516ce1a29f6753a20d797334d7fadbb` in
`upstream.json`'s `file_revisions`. This integrates the direct Nat/Word32
reference primitives without changing the separate `IXBY`/`IXBP` protocol.
`upstream.json` records every source/license digest. The local
`Ix/Ixby.lean` only collects the execution, composition, codec, and commitment
modules needed by this compiler. They depend on `Std`; the upstream Rust,
Aiur, and Flock implementations are not dependencies of this library.

The source files compile unchanged with Compilatrix's pinned Lean 4.33.0;
the upstream branch uses 4.33.1. Keep upstream names and definitions intact.
Changes to the reference require an explicit pin update and conformance review.
The copied MIT and Apache-2.0 licenses apply to these files.
