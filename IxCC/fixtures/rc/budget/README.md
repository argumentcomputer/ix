# RC captured-work budget input

The input of the captured-work budget tests (heap stage 2, `tests-rc-certificate`'s
`OwnedIO.budget`). `Fan.lean` writes, with macros, forty-six fan functions: each binds 150 values
`xᵢ := n + i`, branches on `s` through a balanced tree of `s < m` tests with 302 leaves
(`fanA1`…`fanA23`) or 303 (`fanB1`…`fanB23`), and returns its leaf plus the sum of the `xᵢ`. The
code after the tree is a join that captures the 150 values and that every leaf jumps to, so an
ownership certificate makes the checker take 150 captured tokens at each jump and at the
declaration. The roots `IxCCTests.Own.Budget.fanUnder` and `fanOver` each sum twenty-three of them (and
return a pair, so that the automatic policy selects plain RC): 1,045,350 captured tokens, within
`Anf.maxCapturedWork` (2²⁰ = 1,048,576), and 1,048,800, past it. One fan function per program
could not reach the limit: the consumer reads expressions at most 256 deep (each binding
nests), and the middle end takes at most 16,384 Lam nodes per global.
`main` checks both roots against an independent formula in Lean's interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-budget --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
