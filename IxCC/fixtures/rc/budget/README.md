# RC captured-work budget input

The input of the captured-work budget tests (heap stage 2, `tests-rc-certificate`'s
`OwnedIO.budget`). `Fan.lean` writes, with macros, eighty-two fan functions: each takes `s` and
`C` parameters `xᵢ` (197 for `fanA1`…`fanA41`, 198 for `fanB1`…`fanB41`), branches on `s` through
a balanced tree of `Bool.casesOn (Nat.blt s m)` with 127 leaves, and returns its leaf plus the sum
of the `xᵢ`. The code after the tree is a join that captures the `C` parameters and that every leaf
jumps to; the canonical placement captures two more variables in scope, so a canonical
certificate makes the checker take `C + 2` captured tokens at each jump and at the declaration.
The roots `IxCCTests.Own.Budget.fanUnder` and `fanOver` each call forty-one of them (in four
parts, for the node budget) with every `xᵢ` their `n`, and return the sum and `s` as a pair (so
that the automatic policy selects plain RC): canonically 41 · 199 · 128 = 1,044,352 captured
tokens, within `Anf.maxCapturedWork` (2²⁰ = 1,048,576), and 41 · 200 · 128 = 1,049,600, past it.
A liveness placement captures only the parameters: 1,033,856 and 1,039,104, both within it.

The shape is forced by the limits that come first. The consumer reads expressions at most 256
deep, and parameters and `let`s nest, so one function captures at most about 230 values; the
middle end takes at most 16,384 nodes per Lam and Anf global and 2²⁸ of back-end work (each
global's nodes squared, summed). Captured `let`s cost nodes in proportion (with `n + i` about 42
Lam nodes each, the instances being values after erasure; with `Nat.add n i` about 8 Anf nodes),
and so do leaves (`if s < m`: about 30 Lam nodes per leaf; `Bool.casesOn (Nat.blt s m)`: about
10 Anf nodes): with captured `let`s the back-end work passes 2²⁸ before the captured work reaches
2²⁰. Parameters cost no node. `main` checks both roots against an independent formula in Lean's
interpreter.

The closure and sidecar are written by the ix of this repository (role-bound) with the
commands `provenance.json` records, by `lake exe refreeze-ixon rc-budget --ix IX --ix-path
FAKE` ([`docs/corpus.md`](../../../docs/corpus.md), "Refreezing"), which also rewrites
`manifest.sha256`.
