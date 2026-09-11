# Finite storage across allocating calls

F1's first heap slice gives the actual physical IxIR₂ evaluator a checked
storage budget. It covers reservations held by suspended callers, allocating
callees, explicit frames, capacity exhaustion, and result reclamation. The
separate native list theorem derives the existing arena's exact byte budget
and composes it through source-to-ELF execution.

## Storage model

`ixir2-fixed-slot-space/1` is a versioned resource semantics for the explicit
machine. It accepts exact Word-sized Nat values and locations, with a chosen
maximum number of fields per cell. The source gate uses two fields:

| Component | Bytes charged |
| --- | ---: |
| Heap descriptor | 96 |
| Cell header | 80 |
| Runtime value | 16 |
| Two-field cell, including unused payload capacity | 112 |
| Frame header | 64 |
| Credit array entry, including a consumed entry | 48 |
| Saved continuation header | 16 |

The cell header includes kind, ownership, reference count, the full 32-byte
constructor/function identity, identity indices or arity, and payload length.
The descriptor covers cursor, capacity, the nine evaluator counters, and
reservation count. A frame charges its code reference, block, PC, array
lengths, every value, and every credit entry. An `applyMore` continuation also
charges every pending argument. Direct calls retain the entire caller frame
and add a callee frame plus a continuation header.

At every reachable physical state, the proven partition is:

```
occupied bytes = live-cell bytes + reserved-cell bytes
committed bytes = 96 + occupied bytes + retained-freed-cell bytes
```

The current evaluator appends on fresh allocation. Release leaves a hole in
the backing array; it does not make that slot available to fresh allocation.
Only a reservation authorizes filling an existing hole. Thus committed bytes
are monotone and the maximum heap demand equals the terminal backing-array
size. This remains true after releasing the result. Complete reclamation
means every ownership has been released and all fresh allocations are balanced
by frees; discarding the whole arena is a separate operation.

For example, the three-element hot map returns four live cells with four
freed slots retained. It requires 992 committed heap bytes and at most 848
explicit control bytes. During a callee allocation, one saved caller owns a
reserved cell: the new state requires 656 heap bytes, so a 655-byte budget
fails. Omitting that reservation would incorrectly report 544 bytes. The
16-element hot map peaks at 17 live nodes but commits 34 slots, requiring
3,904 heap bytes and 3,760 control bytes.

This model does not specify an IxIR₂ wire codec, a general native heap ABI, or
the Lean interpreter's host memory consumption. Immutable program code and
the host's traversal workspace are outside these two budgets. Native spills,
a general allocator/free list, and destruction-workspace bounds remain future
work. Native scalar frames retain their existing finite-stack proofs; the new
allocating-call examples execute in the physical IxIR₂ machine.

## Finite execution and proofs

`Space.profile` runs the actual selected physical policy, validates the layout
of each state, and computes independent maxima for heap and control storage.
`Space.run` checks the initial state and every successor before continuing.
A failed capacity check reports the first disallowed state's required bytes,
available bytes, and remaining control fuel. The evaluator is pure, so this
rejection commits no external memory mutation. Representation failures and
the two existing fuel failures have distinct error constructors.

The admission certificate is a successful profile, rather than a supplied
bound over individual steps. The kernel-checked contracts include:

- `Policy.Step.slotGrowth`, `Policy.Steps.slot_partition`, and
  `Layout.committed_partition`: fresh allocations grow backing storage;
  live, reserved and freed cells account for every committed slot.
- `suspendCall_bytes`: suspension preserves heap and reservation bytes while
  adding the full callee frame and continuation header.
- `Space.capacity_iff`, `Space.capacity_exhausted`, and
  `Space.run_prefix_within`: sufficient capacity reproduces the profiled
  result exactly; insufficient capacity produces a capacity error; every
  prefix of a successful finite run fits both budgets.
- `Space.execute_heap_exact`: the heap maximum is the final backing size.
- `MapCompilation.finite_refines`: original Ixon source sharing/oracle
  premises compose through the actual checked map compiler and selector to
  finite execution, source-value preservation and full shared reclamation.
- `Space.release_committedBytes`: result release retains the backing arena.

The source theorem requires successful representation profiling and sufficient
capacity. It does not claim every Nat-valued source program fits this Word
model or give a static symbolic control bound for every recursive program.
The existing reservation-ownership and peak-live theorems keep their original
scope and are reused without changing their definitions.

## Native list arena

The separate `unique-list-arena/1` ABI has a ten-word descriptor and four-word
cells. Reversal needs the `n + 1` input cells and one accumulator nil:

```
requiredBytes(n) = 8 × 10 + (8 × 4) × (n + 2)
                 = 80 + 32 × (n + 2)
```

`Layout.enough_bytes_iff` converts this byte requirement into the existing
cell-capacity premise. `Output.sourceRefinesObjects_of_bytes` carries the byte
premise through the actual emitted main/release ELF objects, source result,
native heap graph, and complete reclamation. The aligned, nonwrapping arena
and memory-permission premises remain explicit. Its caller return slot needs
eight separate stack bytes.

`capacityRejects_of_bytes` proves that a valid, readable descriptor with
insufficient cell capacity returns the failure value with memory unchanged.
The theorem applies to both native counter-policy variants. Available bytes
round down to complete cells after the descriptor: one byte below the required
total supplies only `n + 1` cells. The admitted native family remains at most
64 exact Words; this change does not extend its selector or alter its objects.

## Reproducible gate

```
lake build source-space check-source-space
lake exe check-source-space --fixture .lake/build/bin/source-space
nix build .#checks.x86_64-linux.source-space
```

Nine fresh Ixon compilations cover empty/singleton/three-element hot and cold
maps, mixed ownership, maximum Words, and a 16-element map. Each compares the
profiled, exactly funded, and generously funded executions with the ordinary
source-selected result, then releases it completely. Each also exercises a
heap budget one byte short, a control budget one byte short, an absent
descriptor budget, and zero control storage. Six additional checks separate
control/heap fuel from storage and reject oversized inputs, results and
payloads, including overflow of the descriptor-plus-cell byte total.

The compiler-independent checker reuses the full source call/reuse artifact
inspection, recomputes all sizes from 555 complete heap/frame states, verifies
reservation exclusion and the first rejected state, independently decodes
returned lists/pairs, and compares two fresh artifact sets byte for byte.
It checks all 65 native length/byte boundaries and rejects 13 corruptions,
including omitted reservations, freed backing slots, saved callers, consumed
credit entries, late failures, invalid returned locations and missing native
descriptor bytes. The reviewed summary lives in
[`fixtures/source-space/expected.json`](../fixtures/source-space/expected.json).

The existing native runtime gate still runs the emitted objects and their
insufficient-capacity cases. This slice adds no new native timing claim or
external runtime interface.

The [allocating native helper](source-native-allocating.md) extends this native
bound to a live caller reservation across actual CALL/RET. It requires 16
additional stack bytes below the external return slot and proves release of
the memory returned by ELF execution. Its capacity rejection proof preserves
all heap and stack bytes. General allocating CFG selection remains separate.
