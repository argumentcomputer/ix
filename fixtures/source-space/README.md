# Finite physical storage fixtures

`SourceSpace.lean` compiles nine Ixon maps through the existing validated map
pipeline, profiles their actual physical executions and checks exact/ample
budgets, exhausted budgets, suspended reservations and full reclamation.

`expected.json` pins the reviewed source roots and numerical matrix. Run
`lake exe source-space /tmp/new-space-artifacts` to inspect complete source,
heap and frame snapshots. The output directory must be new.

`check-source-space` imports only independent check code, regenerates two
artifact sets, checks every state and first capacity failure, decodes returned
values, and exercises 13 deliberate corruptions. It does not import the
compiler's size model. See [the proof scope and byte layout](../../docs/finite-space.md).
