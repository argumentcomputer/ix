# Frozen ix frontend fixtures (Ixon v4)

The vectors (`addressed.tsv`, `claims.tsv`, `expressions.txt`, `text.tsv`) and
the primitive inventory `primitives.tsv` are unchanged copies of the root
package's `Tests/Fixtures/ixon/` in this repository (its Ixon v4 codec is
`IxCK/Ixon`), copied by `lake exe refreeze-ixon package --ix-repo ..
--ix-revision HEAD`. The retired v4 resource handoff fixtures (`handoff/`,
`resource.tsv`) were deleted ahead of the Ixon v5 migration.
`README.md` and the copied license notices are IxCC packaging additions. Do not
regenerate expected bytes from the consumer codec.

Run `lake exe tests-ixon-v3` from `IxCC/`. See
[`docs/ixon-v4.md`](../../docs/ixon-v4.md) for admitted behavior and budgets.

## K1 pack

[`k1/`](k1/README.md) holds the first-rung scalar programs of the x86 plan, compiled
from ordinary Lean with `ix compile --equations`. The closure includes the
realized unfolding theorem (`f.eq_def`) of every recursive definition it
reaches, and `equations.json` names each definition/theorem pair by address.
The producer is a local ix change on top of the pinned revision; its manifest
(`k1/corpus.json`) records the exact revision, binary and commands.

## Role-bound closures

[`bound/`](bound/README.md) holds two closures in the role-bound envelope
(`0xE5`) this repository's `ix compile` writes by default, with their role
bindings; every other closure here is unbound (`0xE4`).

## Src tables and diagnostics

`src-tables.tsv` holds the Src front end's pinned `lazy` rows (the 28
`@[macro_inline]` Init declarations, `Bool.or` and `Bool.and`, with their
by-name arities) and its opaque-by-value row (`Lean.opaqueId`), transcribed
in `IxCC.Src.Pinned` (`pin-src-tables --repin` after a refreeze). `src-names.tsv` resolves a few Init names for
tests only; it is an untrusted oracle. [`src-diag/`](src-diag/README.md) is
the admission-diagnostics closure, [`src-sortpoly/`](src-sortpoly/README.md)
the sort-polymorphism closure (level-exact relevance), and
[`erased-blocks/`](erased-blocks/README.md) mutual and nested inductive blocks for the relevance
check's tests of constructor fields written erased. All five come from
`lake exe pin-src-tables` (`IxCCTests/Scripts/PinSrcTables.lean`) with the same ix
producer as the K1 packs; `src-tables.provenance.json` and each directory's
`provenance.json` record it, and `tests-src` compares the TSVs with the Lean
tables.
