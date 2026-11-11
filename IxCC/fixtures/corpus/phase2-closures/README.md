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
| `Closures.stateLoop` | a `StateT`-over-`Except` loop |
| `Closures.storedApply` | partial and over-application through closures stored in a record that is rebuilt every iteration |
| `Closures.knot` | a fuel-indexed record of closures, each level's closures capturing the record one level down (the shape of IxCK's `coreKnot`) |

**A registered family** (`Corpus.families`): `corpus check` checks it and
`tests-corpus` compiles every root with the production compiler, whose
closures step (the roots' entries and P8) runs after the middle end, and runs
every case at every level and natively. All roots compile and agree but
`Closures.stateLoop`, which register allocation declines (`alloc:
alloc.fallback`, the decline the manifest records): the program has a source
global of eight parameters, past the internal calling convention's seven
argument registers. That limit is on parameter counts, not closures.
`tests-pipeline --only defun` also compiles every root under two middle-end
schedules (the Phase 1 schedule, and P1 and P2 alone, so that P8 meets every
closure specialisation would otherwise remove) and compares the native
results with the interpreter's values.

**How it was produced** (2026-11-10). With the ix of this repository (`lake
build ix` at the repository root; the revision and the binary's SHA-256 are in
`corpus.json`) and Lean 4.34.1 on `PATH`, from `IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/phase2-closures/corpus.json --ix ../.lake/build/bin/ix
```

which runs, in `src/`, the commands the manifest records:

```sh
ix compile --no-build \
  --consts Closures.composeClosure,Closures.polyRec,Closures.stateLoop,Closures.storedApply,Closures.knot \
  --equations --anon --unbound --out closures.ixe --equations-out closures.anon.equations.json Closures.lean
ix compile --no-build \
  --consts Closures.composeClosure,Closures.polyRec,Closures.stateLoop,Closures.storedApply,Closures.knot \
  --equations --unbound --out closures.named.ixe --equations-out closures.named.equations.json Closures.lean
ix addr-of --ixe closures.named.ixe NAME     # each root, definition and equation name
lean -Dlinter.all=false --run Closures.lean < CASES   # one line `ROOT ARGS…` per case
```

`--unbound` writes the closure in the version-4 envelope that ingress reads
([corpus guide](../../../docs/corpus.md), "Refreezing"). The rebuild writes
`closures.ixe`, `closures.equations.json` (the `ixcc/k1-equations/1` sidecar
with every name resolved to its address), `closures.census.json` and the cases'
values.
