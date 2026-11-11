# Higher-order workloads for P8

The workloads of the [closures design](../../../docs/closures-design.md)
("Exit criteria", item 2), as a family of the [fixture corpora](../../../docs/corpus.md):
real Lean programs whose closures the Phase 1 middle end does not always
remove. [`src/Closures.lean`](src/Closures.lean) holds the roots and the oracle
driver for `lean --run`; [`corpus.json`](corpus.json) records the closure, the
sidecar, the census, the cases and the interpreter's values.

| Root | Workload |
| --- | --- |
| `Closures.composeClosure` | a closure that grows on every iteration (`Decline.composeClosure` word for word) |
| `Closures.polyRec` | dictionary-passing polymorphic recursion: the recursive call is at `α × α`, with a new dictionary per level |
| `Closures.stateLoop` | a `StateT`-over-`Except` loop with the library's `StateT.bind` |
| `Closures.stateLoopSE` | the same loop in the same stack, `StateT Nat (Except Nat)`, with the stack's `Monad` instance written for it, every method given (a method left out is taken from the library's instance, with `StateT.bind` and `StateT.map`), so that no global takes more than seven parameters under either schedule |
| `Closures.storedApply` | partial and over-application through closures stored in a record that is rebuilt every iteration |
| `Closures.knot` | a fuel-indexed record of closures, each level's closures capturing the record one level down (the shape of IxCK's `coreKnot`) |

**A registered family** (`Corpus.families`): `corpus check` checks it and
`tests-corpus` compiles every root with the production compiler, whose
closures step (the roots' entries and P8) runs after the middle end, and runs
every case at every level and natively. All roots compile and agree.
`Closures.stateLoop` was declined by register allocation until 2026-11-11
(`alloc: alloc.fallback`): `StateT.bind` takes eight parameters (its four type
and instance arguments, the action, the continuation and the state), the
closures step's dispatcher calls it in tail position, and an internal tail
call passes at most seven arguments (a non-tail call passes the rest on the
stack). `Fir.lower` now makes such a call a call and a return
(`Fir.Lower.tailCall`), so the loop uses a frame per iteration (32 bytes on
the immortal route, 96 under plain RC): its last two cases run in an 8 KiB
stack (a 4 KiB budget for the machines; natively it holds 120 iterations),
50 iterations within it and 150 ending with the stack-exhaustion status (marked `spurious`: the source loop
is iterative). Only the
manifest's record of the root changed (its decline, note and two cases, whose
values Lean's interpreter gives: `corpus check --interpret`); the closure
and the other roots are as frozen. `Closures.stateLoopSE` is the same
loop within the limit, with proper tail calls. `tests-pipeline --only defun`
also compiles every root under two middle-end schedules (the Phase 1
schedule, and P1 and P2 alone, so that P8 meets every closure specialisation
would otherwise remove), compares the native results with the interpreter's
values, and certifies every root with and without
specialisation and inlining (`Recheck.compileInput`, and a compile claim that
`verifyProgram` and `verifyBytes` accept), natively equal to the interpreter
both ways.

**How it was produced** (2026-11-11, adding `Closures.stateLoopSE`; the other
roots' addresses, cases and values are those of the 2026-11-10 freeze). With
the ix of this repository (`lake build ix` at the repository root, in the
build box's checkout of `jcb/ixcc-closures-wiring`, whose root package is
`jcb/ixck-ixcc-merge`'s at `21572449d`; the revision and the binary's SHA-256
are in `corpus.json`) and Lean 4.34.1 on `PATH`, from `IxCC/`:

```sh
IX=../.lake/build/bin/ix
# pin the producer in this manifest (`refreeze-ixon producer` does not list this family)
jq --indent 2 --arg rev "$(git rev-parse 21572449d)" --arg sha "$(sha256sum $IX | cut -c1-64)" \
  --arg ver "$($IX --version | tr -d '\n')" --arg build "<the ix_build text in corpus.json>" \
  '.producer.ix_revision = $rev | .producer.ix_binary_sha256 = $sha
   | .producer.ix_version = $ver | .producer.ix_build = $build' \
  fixtures/corpus/phase2-closures/corpus.json > corpus.pinned.json
mv corpus.pinned.json fixtures/corpus/phase2-closures/corpus.json
lake exe corpus rebuild fixtures/corpus/phase2-closures/corpus.json --ix $IX
```

The rebuild runs, in `src/`, the commands the manifest records:

```sh
ix compile --no-build \
  --consts Closures.composeClosure,Closures.polyRec,Closures.stateLoop,Closures.stateLoopSE,Closures.storedApply,Closures.knot \
  --equations --anon --unbound --out closures.ixe --equations-out closures.anon.equations.json Closures.lean
ix compile --no-build \
  --consts Closures.composeClosure,Closures.polyRec,Closures.stateLoop,Closures.stateLoopSE,Closures.storedApply,Closures.knot \
  --equations --unbound --out closures.named.ixe --equations-out closures.named.equations.json Closures.lean
ix addr-of --ixe closures.named.ixe NAME     # each root, definition and equation name
lean -Dlinter.all=false --run Closures.lean < CASES   # one line `ROOT ARGS…` per case
```

`--unbound` writes the closure in the version-4 envelope that ingress reads
([corpus guide](../../../docs/corpus.md), "Refreezing"); the family is not yet
in the role-bound form. The rebuild writes `closures.ixe`,
`closures.equations.json` (the `ixcc/k1-equations/1` sidecar with every name
resolved to its address), `closures.census.json` and the cases' values.
