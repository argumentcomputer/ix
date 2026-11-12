# RC captured-work budget input

The input of the captured-work budget tests (heap stage 2, `tests-rc-certificate`'s
`OwnedIO.budget`). `Fan.lean` writes two roots, `IxCCTests.Own.Budget.fanUnder` and
`fanOver`, with macros: `C` values `xᵢ := n + i` (512 and 513), then a balanced tree of
`s < m` tests with 2,047 leaves, then the leaf and the sum of the `xᵢ`. The code after the
tree is a join that captures the `C` values and that every leaf jumps to, so the ownership
certificate makes the checker take `C` captured tokens at each jump and at the declaration:
`fanUnder` is within `Anf.maxCapturedWork` (2²⁰), `fanOver` past it. `main` checks both
roots against an independent formula in Lean's interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-budget --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
