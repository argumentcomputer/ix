# Native sharing comparison

This is a fixed-policy comparison of the tree and shared emitters for the
existing `compiler-scaling-joins/1` checked IxIR₂ fixture. It also checks the
shared default of the physical heap object API. The original scaling command,
fixture roots, selection limits, and historical tree ELF endpoint are retained.

Build and run the correctness gate:

```sh
lake build native-sharing check-native-sharing heap-snapshot-object
.lake/build/bin/check-native-sharing \
  --fixture .lake/build/bin/native-sharing \
  --consumer .lake/build/bin/heap-snapshot-object \
  --expected fixtures/native-sharing/expected.json \
  --cc cc --harness benchmarks/native/scaling_harness.c
```

The gate runs two fresh producers and compares every deterministic file with
its partner and the reviewed report. It independently parses snapshots and ELF
metadata, replays objects from persisted input alone, injects six corruptions
per row, disassembles the objects, and links the unchanged scaling harness. The
harness supplies boundary and deterministic random arguments, exact resource
formulas, saved-register sentinels, and a workspace bounded by guard pages.

Produce the larger reference matrix, then validate it:

```sh
.lake/build/bin/native-sharing /tmp/sharing-reference reference
.lake/build/bin/check-native-sharing \
  --directory /tmp/sharing-reference \
  --expected fixtures/native-sharing/expected-reference.json \
  --consumer .lake/build/bin/heap-snapshot-object \
  --cc cc --harness benchmarks/native/scaling_harness.c \
  --output /tmp/sharing-validation.json
```

Every output directory must be fresh. `smoke` covers tree/shared joins 2, 4, 8
and shared-only 9; `reference` covers tree/shared joins 2 through 8 and
shared-only 9. Both validate and reject 10 at the unchanged selector boundary.
No baseline-nine ELF timing is inferred from the shared endpoint.

Each case has `.ixir2`, `.o`, and `.json` files. `report.json` is deterministic;
`measurements.json` is separate. It uses `IO.monoNanosNow` around one invocation
of each of eight stages: snapshot encode/check, decode/check, export discovery,
selection, native emission, native certificate checking, x86 encoding/checking,
and ELF writing/checking. Cases run in fixed increasing-size, tree-then-shared
order. Do not interpret this as randomization or independent per-stage
processes. Fixture construction, default-API replay, semantic and mutation
checks, report hashing, JSON, and file IO occur outside the named intervals.
The complete worker process includes all of them.

The retained reference uses three fresh complete worker processes, one pinned
CPU, one Lean thread, and raw GNU `time` process observations. The
[reference report](../docs/performance/native-sharing-2026-09-12/README.md)
records the source snapshot, executable seed, host, sampling order, raw archive,
replay, and actual timing distributions. RSS is a complete-process high-water
mark, not a measurement of a compiler phase or the target workspace.

This is a code-growth and compiler-cost experiment. Linked native execution is
a correctness check; no workload throughput claim follows. The selector and
plan checker still unfold/traverse the bounded tree. Future graph-based
selection and certificates need their own correctness and measurement slice.
