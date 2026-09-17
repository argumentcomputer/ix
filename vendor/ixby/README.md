# Pinned Ixby reference modules

These pure Lean files are copied without changes from
[argumentcomputer/ix, revision `6836a77c3f432c83c42428490e56811f4a69808d`](https://github.com/argumentcomputer/ix/tree/6836a77c3f432c83c42428490e56811f4a69808d/Ix/Ixby)
on `jcb/ixby`. All files come from the same revision. Runtime revision 2 adds
explicit scalar conversions, persistent arrays, and immutable byte builders.
Every artifact uses format 1 and semantics 2; the retired `IXBY`/`IXBP`
profiles and `IXBI`/`IXBO` transports are not accepted.
`upstream.json` records every source/license digest. The local
`Ix/Ixby.lean` only collects the execution, composition, codec, and commitment
modules needed by this compiler. They depend on `Std`; the upstream Rust,
Aiur, and Flock implementations are not dependencies of this library.

The source files compile unchanged with Compilatrix's pinned Lean 4.33.0;
the upstream branch uses 4.33.1. Keep upstream names and definitions intact.
Changes to the reference require an explicit pin update and conformance review.
The copied MIT and Apache-2.0 licenses apply to these files.
