# Native graph fixtures

`expected.json` freezes the ten-case smoke report; `expected-reference.json`
freezes the full 23-case matrix. Both retain the original join snapshots and
the previous shared-emitter artifacts on their common inputs. They add graph
context/certificate sizes, explicit resource boundaries, and checker mutations.

The independent checker validates complete artifact identity, persisted-only
recompilation, binutils inspection, and guarded native calls using the unchanged
[scaling harness](../../benchmarks/native/scaling_harness.c).
See the [protocol](../../benchmarks/native-graph.md).
