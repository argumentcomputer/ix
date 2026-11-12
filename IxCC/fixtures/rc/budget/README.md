# RC captured-work budget input

The input of the captured-work budget tests (heap stage 2, `tests-rc-certificate`'s
`OwnedIO.budget`). `Fan.lean` writes, with macros, ten fan functions: each binds 200 values
`xᵢ := n + i`, branches on `s` through a balanced tree of `s < m` tests with 1,047 leaves
(`fanA1`…`fanA5`) or 1,048 (`fanB1`…`fanB5`), and returns its leaf plus the sum of the `xᵢ`. The
code after the tree is a join that captures the 200 values and that every leaf jumps to, so an
ownership certificate makes the checker take 200 captured tokens at each jump and at the
declaration. The roots `IxCCTests.Own.Budget.fanUnder` and `fanOver` each sum five of them (and
return a pair, so that the automatic policy selects plain RC): 1,048,000 captured tokens, within
`Anf.maxCapturedWork` (2²⁰ = 1,048,576), and 1,049,000, past it. One fan function per program
could not reach the limit: the consumer reads expressions at most 256 deep, and each binding
nests. `main` checks both roots against an independent formula in Lean's interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-budget --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
