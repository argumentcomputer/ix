# Certified kernel benchmarks

Build the native runner without the host package or its dependencies:

```sh
lake -d IxKernel build --wfail bench-certified-kernel
python3 scripts/bench-certified-kernel.py --output plans/native-baseline.jsonl
```

The default suite records one warmup followed by five fresh-process samples
for each input size. For a focused run:

```sh
python3 scripts/bench-certified-kernel.py --case binders --size 64 --size 128
```

The runner requires Python 3, jj, and GNU time. It snapshots the current jj
working copy to record the measured revision. Build again after changing
Lean sources; output includes source and executable SHA-256 fingerprints,
the compiled Lean version, toolchain pin, architecture, fuel, all samples,
median/range, and maximum process RSS. Measurements do not change CI verdicts.

| Case | Timed operation |
| --- | --- |
| `env` | Admit independent definitions with fresh Nat keys |
| `address` | The same workload with deterministic 32-byte Address keys |
| `references` | Admit definitions repeatedly referring to the oldest entry |
| `binders` | Annotate and check a declaration with nested lambdas |
| `beta` | Annotate and check nested identity applications |
| `context` | Push constant-size domains into the local context |
| `spine` | Weak-head reduce a typed, stuck variable-headed application |
| `ordinary` | Admit Nat/Eq, addition, and repeated recursor-computation theorems |
| `structure` | Admit Prod/Eq and repeated projection-iota/structure-eta theorems |
| `quotient` | Admit the quotient primitives and repeated lift-computation theorems |

Fixture construction happens before the native monotonic timer. The spine
fixture's typing precheck is also outside that interval. Inputs are read
from IO references inside the timed operation, and results are consumed
before it ends. Every declaration workload must accept or the process
fails. The spine must remain unchanged.

Peak RSS covers the entire process, including setup and the spine typing
precheck; it is not an allocation count for the timed operation alone.
The native results are a distinct baseline from the earlier `lean --run`
measurements. Compare like builds, inputs, fuel, and backends, and keep
acceptance coverage separate from execution time.

The standalone strict build also runs the certified fixtures, including
`Tests.Ix.Kernel.SearchOutcomes`. The latter initially records the known
low-fuel misclassification; the diagnostic repair changes that regression
to require a decline. Detailed operation-count instrumentation remains a
separate diagnostic task before the corresponding performance promotions.
