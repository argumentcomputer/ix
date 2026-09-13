# Native graph comparison

This compares the previous shared emitter with graph selection and native
certification on the fixed canonical join inputs. Both use the same native
templates and block interning. The common inputs must produce identical
snapshots, native text, ELF, observations, and executed byte-step counts.

```sh
lake build native-graph check-native-graph heap-snapshot-object
.lake/build/bin/check-native-graph \
  --fixture .lake/build/bin/native-graph \
  --consumer .lake/build/bin/heap-snapshot-object \
  --expected fixtures/native-graph/expected.json \
  --cc gcc --harness benchmarks/native/scaling_harness.c
```

The check runs two fresh producers and compares every non-timing byte with
reviewed fixtures. Independent imports contain only the persisted wire/ELF
inspectors, tool helpers, and linked C harness. They do not import a compiler,
encoder, or machine evaluator. Fresh consumer execution rebuilds each object
from its persisted snapshot and compares exact bytes.

The smoke matrix has ten objects: joins 2, 8, and 9 in both modes, then graph
10, 16, 32, and 42. Reference mode has 23 objects: joins 2 through 9 in both
modes, then graph 10, 12, 16, 24, 32, 40, and 42.

```sh
taskset -c 0 env LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=1 LC_ALL=C \
  .lake/build/bin/native-graph NEW-OUTPUT-DIRECTORY reference
.lake/build/bin/check-native-graph \
  --directory NEW-OUTPUT-DIRECTORY \
  --consumer .lake/build/bin/heap-snapshot-object \
  --expected fixtures/native-graph/expected-reference.json \
  --cc gcc --harness benchmarks/native/scaling_harness.c
```

Use three fresh reference processes, fixed case/mode order, an otherwise quiet
build environment, and GNU time around each whole process. Retain all stage
samples and report median/min/max; timings have no CI threshold. Peak RSS
belongs to the complete matrix worker, including execution, mutations,
representation formatting, replay, hashing, and IO. It does not isolate a
compiler phase or mode, and is separate from the generated program's workspace.

Eight production `IO.monoNanosNow` intervals cover one invocation each of snapshot
encoding/checking, decoding/checking, export resolution, selection, native
emission, native certificate checking, x86 encoding/checking, and ELF
writing/checking. Mutation tests and inspection formatting run after these
intervals. Fixture construction, API replay, semantic runs, budget/context
tests, inspection formatting/hashing, and file writes are excluded from
the intervals but included in process costs.

Measurement format `compilatrix/native-graph-measurements/2` additionally
times raw x86 encoding, the retained reference stream checker, canonical
layout construction, checking with that prepared layout, and complete
indexed checking (including layout construction). These five intervals
precede the ordinary `x86-encode-check` interval. Each invokes its operation
once on the same target/output, in a fixed order. All three checker calls
must accept; the ordinary certified emitter must return exactly the raw
encoder's text, offsets, and relocations. The indexed and prepared intervals
overlap in scope, as does ordinary encoding/checking with the isolated phases;
do not sum all thirteen intervals as a compiler total. Timings have no CI
threshold. The [stream checking implementation](../docs/stream-checking.md)
proves exact acceptance and rejection agreement with the reference checker.

Retain canonical snapshots, exact ELF, per-case observations, selection/plan
inspection JSON, report JSON, raw samples, tool identities, source snapshot,
seed binaries, host/CPU policy, and validation logs. Inspection formats expose
representation size; they are not stable codecs or proof recovery inputs.
A fresh source-directory replay with recorded seed binaries checks all source
and seed identities before replaying objects. Label it as seed replay, not a
fresh Lean/compiler rebuild. Publish the local archive inventory and SHA-256.

The legacy selector still rejects ten joins. Graph mode admits forty-two and
rejects forty-three at the unchanged source block bound. Exact node/edge/depth
limits, one-below-limit failures, a longer cached path, context-sensitive
ownership, malformed graph references, and per-block/node mutations are part
of every producer. See [implementation and proof scope](../docs/native-graph.md)
and the [retained reference](../docs/performance/native-graph-2026-09-12/README.md).
