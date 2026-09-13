# Pinned Ixby reference modules

These pure Lean files are copied without changes from
[argumentcomputer/ix, revision `4fdbf4084516ce1a29f6753a20d797334d7fadbb`](https://github.com/argumentcomputer/ix/tree/4fdbf4084516ce1a29f6753a20d797334d7fadbb/Ix/Ixby)
on `jcb/ixby`. `upstream.json` records every source/license digest. The local
`Ix/Ixby.lean` only collects the execution, composition, codec, and commitment
modules needed by this compiler. They depend on `Std`; the upstream Rust,
Aiur, and Flock implementations are not dependencies of this library.

The source files compile unchanged with Compilatrix's pinned Lean 4.33.0;
the upstream branch uses 4.33.1. Keep upstream names and definitions intact.
Changes to the reference require an explicit pin update and conformance review.
The copied MIT and Apache-2.0 licenses apply to these files.
