# The Phase 1 scalar corpus

The `phase1-scalar` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.2): first-order, total programs over `Nat` and `Bool`,
compiled from Lean 4.34 sources by ix with unfolding equations, and frozen.
[`corpus.json`](corpus.json) (`ixcc/corpus/1`) records every source,
licence and origin, the ix revision and commands, the files' hashes, the
roots and their cases, with the outputs Lean's interpreter printed, the
independent constants, and the expected declines.

| Closure | Source | Licence | Roots |
| --- | --- | --- | ---: |
| `scalar` | [`src/Scalar.lean`](src/Scalar.lean) | Apache-2.0 OR MIT (re-derivations of MLton, Koka and nofib programs; origins in the manifest) | 23 |
| `strictAndOr` | [`src/lean-compile/StrictAndOr.lean`](src/lean-compile/StrictAndOr.lean) | Apache-2.0 (Lean 4) | 2 |
| `tuple` | [`src/lean-compile/Tuple.lean`](src/lean-compile/Tuple.lean) | Apache-2.0 (Lean 4) | 1 |
| `bigctor` | [`src/lean-compile/BigCtor.lean`](src/lean-compile/BigCtor.lean) | Apache-2.0 (Lean 4) | 1 |
| `typeFormerPolymorphism` | [`src/lean-compile/TypeFormerPolymorphism.lean`](src/lean-compile/TypeFormerPolymorphism.lean) | Apache-2.0 (Lean 4) | 1 |
| `natShiftr` | [`src/lean-compile/NatShiftr.lean`](src/lean-compile/NatShiftr.lean) | Apache-2.0 (Lean 4) | 1 |

The `lean-compile` sources are the first-order programs of Lean's
`tests/compile` (v4.34.0, `293d5d0c`), modified: the text up to `def main`
is upstream's, verbatim, and an `entry` root and the corpus oracle driver
replace upstream's `main`. The upstream files and their `.out.expected` are
kept byte for byte in [`src/lean-compile/upstream/`](src/lean-compile/upstream),
and the expected lines are the cases' `constant`s. Lean 4's licence is
[`LICENSES/lean4-LICENSE`](LICENSES/lean4-LICENSE).

Files per closure: `<name>.ixe` (the anonymous closure of the roots, `ix
compile --consts ROOTS --equations --anon`), `<name>.equations.json` (the
sidecar, `ixcc/k1-equations/1`, addresses resolved against the named
twin) and `<name>.census.json` (the admission census: every constant passes
decoding, the certified kernel's acceptance and the policy stage). `lake exe corpus check`
verifies them; `lake exe corpus rebuild` remakes them with the pinned ix
(byte-identical on a second build); `lake exe tests-corpus` runs every root.

## Declines (completeness findings, 2026-10-01)

Four roots are declined; each is recorded as the root's expected `decline`,
so a change in the compiler's coverage shows up as a test failure.

| Root | `stage: code` | Why |
| --- | --- | --- |
| `Scalar.impFor` | `fir: fir.closures` | nested `for` loops keep closures after the middle end (P8, Phase 2) |
| `Scalar.pyth` | `fir: fir.closures` | the same, with `break` |
| `Scalar.chooseMul` | `alloc: alloc.fallback` | a `for` loop that reads a parameter besides its counter: the specialised loop function takes 8 arguments (`tail f1(1, 1, v1, v0, 3, 1, 1, 1)`), more than the internal convention's 7 argument registers; nothing before allocation checks this, and the all-slots fallback is rejected (`convention`) |
| `typeFormerPolymorphism/entry` | `relevance: relevance-C2` | a type passed for a parameter that is relevant at this instance (`β := Type 0`) |
