# Runtime native reversal gate

`source-native-runtime` compiles one parameterized Ixon function and emits one
reversal/release ELF pair. Eight runtime inputs use that same pair. The reviewed
`expected.json` pins the source, canonical graph, complete pipeline snapshot,
object/policy identities, values, step counts, and rejection inventory.

The independent checker generates `runtime_cases.h` from the reviewed input
table and links `native_harness.c` with the pair once. One process runs every
case, fully releases each result, and checks 203 malformed calls without arena
writes. No per-input object is generated or linked.

Run the [documented gate](../../docs/source-native-runtime.md#artifact-identity-and-gate)
before reviewing a report or integrity-pin update. The existing ISA, encoder,
and ELF/linker assumptions remain active.
