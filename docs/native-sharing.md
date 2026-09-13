# Shared native blocks

The shared emitter emits repeated native
continuations once, with jumps from their incoming edges. The
original tree emitter remains selectable. Both return the same checked output
and use the existing source, physical execution, ownership, workspace, and ELF
preservation theorems.

The current object API default additionally uses
[graph selection and certificates](native-graph.md). Pass `(emission := .shared)`
to select the tree-selection path measured on this page.

This addresses the code expansion measured in the
[compiler scaling reference](performance/compiler-scaling-2026-09-12/README.md).
For its checked IxIR₂ join fixture:

| Joins | Tree blocks | Shared blocks | Tree ELF bytes | Shared ELF bytes |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 28 | 17 | 1,760 | 1,464 |
| 4 | 112 | 27 | 4,272 | 1,792 |
| 8 | 1,792 | 47 | 54,432 | 2,448 |
| 9 | not measured through ELF | 52 | not measured | 2,608 |

The [repeat measurement](performance/native-sharing-2026-09-12/README.md)
records emission, certificate checking, encoding/checking, complete process
cost, and the limits of the comparison. This fixture starts at checked IxIR₂;
it does not establish source compilation of converging joins. Separate source
and allocating CFG fixtures exercise the same emitter with calls and ownership.

## API and implementation

[`PhysicalHeap.compile`, `compileSnapshot`](../Compilatrix/X86/PhysicalHeapObject.lean)
and [`compileExport`, `compileSnapshotExport`, `compileSourceExport`](../Compilatrix/X86/PhysicalHeapExport.lean)
accept `emission : HeapTarget.Emission := .graph` and graph consumer limits. Pass
`(emission := .tree)` to retain the prior output bytes. The low-level
[`HeapTarget.compile`](../Compilatrix/X86/HeapTarget.lean) remains the original
tree entry point; `HeapTarget.compileShared` checks shared emission.

[`BlockSharing.emit`](../Compilatrix/X86/BlockSharing.lean) interns complete
native blocks after their successors have been emitted. The key includes every
instruction operand and the terminator, including branch destinations and
conditions. A hash chooses a bucket; full structural equality chooses an entry.
There is no hash-injectivity assumption. Emission order is deterministic and
does not depend on hash-table iteration. Identical epilogues and other blocks
can also be shared across selected function profiles.

Argument transfers retain the existing staging and commit instructions.
Different transfers into a common continuation remain different blocks. The
emitter changes neither instruction templates nor the selected physical tree,
and performs no dead-code, branch, or ownership-action elimination.

`emitCandidate` exposes the untrusted blocks and plans. `checkCandidate`
checks control bounds, complete function coverage, each source tree, every
instruction/slot/edge/callee match, and the capacity adapter. It checks every
use of a shared entry. `checkCandidate_program` proves that an accepted result
certifies the exact proposed program; its axiom fence contains only `propext`
and `Quot.sound`.

The existing `PhysicalHeap.Output.physicalReturns`,
`PhysicalHeap.Compiled.policyReturns`, `Compiled.physicalReturns`, and
`Exported.sourceNatReturns` quantify over arbitrary checked outputs. They
require no distinctness of plan entries. They therefore apply directly to the
shared result, including simultaneous argument copies, caller reservations,
exact counters, full reclamation, saved registers, and outside-workspace bytes.
`Compiled.rejectsCapacity` continues to cover rejected capacities. Their
existing axiom fences remain in place; source composition retains the existing
BLAKE3 boundary. No new axiom, native interface, allocator, or ABI is introduced.

## Limits and identity

The `.tree` and `.shared` paths unfold a tree, bounded by depth 128 and work 4,096. Their checker
still traverses that tree. The fixed ten-join fixture remains rejected. Linear
emitted code growth for this family does **not** establish linear selection or
certificate-checking cost, nor admission of larger CFGs. Preserving sharing in
the selector and certificate representation is supplied separately by the
current `.graph` default.

Both modes consume identical snapshot bytes, use identical selector limits and
workspace bounds, and execute the same instruction templates. ELF provenance
continues to name the input snapshot. It does not identify the emitter. Reports
record `heap-block-tree/1` or `heap-block-sharing/1`, and each resulting ELF has
its own content identity. Historical scaling fixtures and their tree artifacts
remain unchanged. The persisted-only `heap-snapshot-object` CLI retains its
legacy tree default; append `shared` to request shared emission. It also accepts
`--name SYMBOL` and the `export` entry mode for a snapshot with an export wrapper.

## Validation

The `source-native-heap` gate runs both modes over five source and four physical
CFGs. Each mode checks 95 source applications, 171 parsed-ELF executions, nine
persisted-only reloads, and 774 linked calls. The shared producer also rejects
instruction and terminator mutations to every emitted block, plus missing
function coverage. Existing admission, ownership-policy, capacity, snapshot,
artifact, and caller-state negatives remain enabled.

The `native-sharing` Nix check compares two fresh producers against reviewed
bytes for joins 2, 4, and 8 in both modes, plus shared-only 9. It checks physical,
typed x86, and parsed-ELF executions; default-API agreement; shared block
uniqueness; per-block mutations; independent snapshot/ELF inspection; exact
persisted-only recompilation; and 231 guarded linked calls. Timing values have
no CI thresholds. The full reference adds joins 3, 5, 6, and 7.

See [commands and measurement protocol](../benchmarks/native-sharing.md).
