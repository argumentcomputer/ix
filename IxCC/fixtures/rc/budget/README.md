# RC captured-work budget input

The input of the captured-work budget tests (heap stage 2, `tests-rc-certificate`'s
`OwnedIO.budget`). `Fan.lean` writes, with macros, twenty fan functions: each binds 180 values
`xᵢ := Nat.add n i`, branches on `s` through a balanced tree of `Bool.casesOn (Nat.blt s m)` with
581 leaves (`fanA1`…`fanA10`) or 582 (`fanB1`…`fanB10`), and returns its leaf plus the sum of the
`xᵢ`. The code after the tree is a join that captures the 180 values and that every leaf jumps to,
so an ownership certificate makes the checker take 180 captured tokens at each jump and at the
declaration. The roots `IxCCTests.Own.Budget.fanUnder` and `fanOver` each sum ten of them (and
return a pair, so that the automatic policy selects plain RC): 1,047,600 captured tokens, within
`Anf.maxCapturedWork` (2²⁰ = 1,048,576), and 1,049,400, past it.

One fan function per program cannot reach the limit, and the source is written without type-class
instances or `if`, because of the limits that come first: the consumer reads expressions at most
256 deep (each binding nests); the middle end takes at most 16,384 nodes per Lam and Anf global
and 2²⁸ of back-end work (each global's nodes squared, summed). With `n + i` and `if s < m`, a
binding cost about 42 Lam nodes and a leaf 30 (instances are values after erasure), and a program
past the budget was past the back-end work first. `main` checks both roots against an independent
formula in Lean's interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-budget --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
