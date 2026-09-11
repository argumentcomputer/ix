# Allocating native reversal fixtures

`expected.json` and `expected-counter-fold.json` freeze the source, policy,
object and 73-input summaries for the two allocating-helper schedules.
`native_harness.c` supplies runtime arenas, traverses the returned pointer
graphs, releases every cell, and checks malformed calls, finite capacity,
canaries and the System V calling convention.

The [contract and replay commands](../../docs/source-native-allocating.md)
describe the proofs, exact storage requirements, fresh-process checks and
continuing scope limits. These objects are separate from the existing
runtime reversal goldens.
