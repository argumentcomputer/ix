# The ownership and usage-annotation suite, Phase 1 part

The fixtures of MT.7 (phase 1 plan; design in the local note
`plans/fixtures/ownership-suite.md`). Each fixture is a Lean program written
with ix's contract syntax (`0` erased, `1` linear, `&` affine, `!` unique,
`~` local, `let borrow`), paired with its plain twin. `lake exe tests-own`
runs them.

In Phase 1 the compiler carries written contracts but never reads them
(they are "recorded but unused" in the immortal fragment), so the suite
shows what Phase 1 can show:
- **equivalence**: an annotated program ix accepts behaves like its plain
  twin at every level and natively, and compiles to the same Fir, Cfg and
  object;
- **erasure**: `0` binders, proof arguments, `Subtype` and `Decidable` cost
  nothing in the emitted code;
- **verdicts**: ix's acceptance or rejection of each annotated source, with
  the stage and code (CI never runs ix: the verdicts are data);
- **counters**: allocations, and the reference-counting events Phase 2
  will add, from a test-side stepper over `Cfg.step`, and the bytes the
  native code allocates.

It must not be read as showing any reference-counting, reuse or speed
benefit of an annotation: Phase 1 has none.

## Files

| File | What |
| --- | --- |
| [`corpus.json`](corpus.json) | the `ownership` family, format `compilatrix/corpus/1` ([`docs/corpus.md`](../../docs/corpus.md)): every closure, with its source, licence, roots, cases and the values Lean 4.34's interpreter printed |
| [`verdicts.json`](verdicts.json) | format `compilatrix/own-verdicts/1`: ix's verdict on every annotated source, and the corpus fixture of each accepted one |
| `src/<ID>/Annotated.lean` | an annotated source (imports `Ix.Compile.SourceContract.Elab`) |
| `src/<ID>/Plain.lean` | its plain twin: the annotated text with the contract atoms, `borrow` and the elaborator import deleted; `tests-own` checks this (`CompilatrixTests.Own.Strip`) |
| `<ID>-annotated.*`, `<ID>-plain.*` | the frozen closures (`.ixe`), `eq_def` sidecars (`.equations.json`) and admission censuses (`.census.json`) |

All sources were written for Compilatr.ix (Apache-2.0 OR MIT); most are the
probes of the design note, renamed by fixture id.

## Fixtures compiled today

| ID | Annotated | ix | Compilatrix | Code against the twin |
| --- | --- | --- | --- | --- |
| OS-01 `erased-proof-arg` | `pick (0 _h : True) (n : Nat)` | accepted | compiled | equal Fir, Cfg and object |
| OS-03 `erased-data` | `ignoreFirst (0 _n : Nat) (m : Nat)`, called with `n` | accepted | compiled (CX-1; `relevance-C0` before) | equal |
| OS-03b `erased-data-dead-work` | OS-03 called with `cube n` | accepted | compiled; no `natMul` in the code | equal |
| OS-13 `linear-identity` | `linId (1 x : Nat)`, and a caller | accepted | compiled | equal |
| OS-14 `unique-nat-match` | `pred (! n : Nat)` with `match`, caller `(! n)` | accepted | compiled | equal |
| OS-22 `local-forward` | `localId (~ x : Nat) : ~ Nat`, caller `(~ n)` | accepted | compiled | equal |
| OS-02 `subtype-decidable` | plain only | – | compiled; no allocation | – |
| OS-16 `k0-reverse-plain` | plain only (its annotated twin OS-15 is rejected) | – | compiled; `2n` cells, `48n` bytes natively | – |

"Equal" is up to the source constants' numbering (ingress's indices) and
the root's content address in the object's provenance note: contracts are
part of a constant's address, so that note differs and nothing else does.

The other 40 annotated sources (OS-01b, OS-04 to OS-37, and the negatives
N-01 to N-08) are rejected by ix; `verdicts.json` records each stage and
code. OS-30 to OS-33, OS-38 and OS-39 have no source yet (Phase 2 and
later).

## The producer, and rebuilding

The closures and the verdicts come from the pinned ix of
[`docs/corpus.md`](../../docs/corpus.md) (revision `9c4b9c65`, binary SHA-256
`d8ba031a…`), with the manifest's anonymous command (`ix compile --no-build
--consts ROOTS --equations --anon`). ix elaborates an annotated source
against the Lean libraries `lake env printenv LEAN_PATH` names, through the
`lake` stand-in `plans/fixtures/ix-usage-ownership/fakebin`; on 2026-10-01
that path held a later build of ix's libraries, and the pinned binary
reproduced, byte for byte, the closures the design note's probes had made
with its own libraries (P15, P32, P34, P38), and the verdicts of its probe
matrix.

```sh
D=plans/fixtures/ix-usage-ownership
# closures, sidecars, censuses and the interpreter's values; Lean
# interprets an annotated source with ix's libraries on LEAN_PATH
LEAN_PATH=$($D/fakebin/lake env printenv LEAN_PATH) \
  .lake/build/bin/corpus rebuild fixtures/ownership/corpus.json --ix $D/ix-base --ix-path $D/fakebin
# the verdicts
.lake/build/bin/tests-own verdicts --ix $D/ix-base --ix-path $D/fakebin
```

A second rebuild left every file unchanged. `corpus check` of this family
needs no ix; `corpus check --interpret` needs the `LEAN_PATH` above.

## Running

```sh
lake exe tests-own [--cc cc] [--only strip|fixtures|equiv|erasure|counters|cx1]
```

The family is not among `tests-corpus`'s registered families: `tests-own`
runs its roots through the same levels (and `corpus check` on its
manifest) itself.
