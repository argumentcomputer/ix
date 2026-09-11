# Source native reversal with runtime input

`UniqueReuse.Runtime.compile` compiles one parameterized Ixon function,
`fun xs => reverseOnto nil xs`. Its selected native entry accepts a caller-built
list at runtime. One emitted reversal/release pair handles empty, nonempty,
repeated, maximum-Word, and 64-element inputs. The source, physical IxIR₂,
typed x86 byte-memory model, and one linked native process agree on the results
and complete reclamation.

The source is a canonical synthetic Ixon function using the unique constructors
and recursor from the [closed reversal endpoint](source-native-unique.md).
Its constants contain no input payloads. This extends that accepted schema to
a direct function entry; it does not widen ordinary lowering to unique PAPs,
general recursors, or arbitrary upstream functions.

## Compilation and proof interface

[`Runtime.compile`](../Compilatrix/UniqueReuse/Runtime.lean) certifies erasure,
checks the parameterized source shape and its unique argument/result worlds,
then validates the consuming and selected IxIR₂ programs. Static reuse requires
the existing liveness/placement certificate and full validation. Disabled reuse
or a zero rewrite budget retains the checked consuming target; invalid source
or failure of baseline target validation returns an error. The exported
one-argument declaration and reversal worker have separately checked, distinct
canonical IxIR₁ addresses. The module retains IxIR₂'s nullary main for module
validation; runtime calls enter the exported declaration.

[`Native.select` and `Output.emit`](../Compilatrix/UniqueReuse/RuntimeNative.lean)
consume that compilation and its actual static-reuse selection. `Output` holds
no runtime input values. The checked native programs and their emitted bytes
are shared across every call. `ofNats` rejects an oversized list or a Nat outside
`[0, 2^64)` before preparing a native argument; `ofNats_exact` proves that an
accepted conversion preserves every Nat exactly and respects the length bound.

[`Output.sourceRefines`](../Compilatrix/UniqueReuse/RuntimeNativeSim.lean)
quantifies over the runtime argument. `ArgumentRel` ties the source value to the
same exact-Word list in the certified erased environment and native input heap.
It states source sharing well-formedness, the finite canonical input chain,
initial counters, register arguments, sufficient capacity, byte permissions,
alignment, nonwrapping layout, and the surrounding-memory frame. Its graph
corollary derives the input's distinct finite native footprint. The caller
transfers ownership of this list and receives sole ownership of the result.

The theorem retains the established oracle correspondence, source-context
sharing well-formedness, and successful function evaluation/application premises.
It derives the related reversed source result, execution of the selected
physical IxIR₂ function from any related owned input store, and native execution
followed by complete release. `costsAgree` connects the physical IxIR₂ counters
and native counters. `Target.makeInput_valid` and
`RuntimeExecution.canonical_executes` provide concrete admitted caller states.

The native proof composes read-only validation, one accumulator allocation,
the existing reversal loop, and the existing release proof. Both calls preserve
the stack pointer, System V callee-saved registers, and bytes outside the arena.
`Execution.mainSafe` and `releaseSafe` exclude every modeled trap at every
instruction prefix. `lengthRejects` and `capacityRejects` start at the exported
entry and prove a zero return with exactly unchanged memory. Other malformed
inputs are covered by the generic read-only guard lemma and the executable
rejection matrix; there is no universal arbitrary-pointer rejection theorem.

The [finite-storage byte corollary](finite-space.md#native-list-arena) derives
`80 + 32 * (n + 2)` bytes from this ABI and uses that premise in the actual
source-to-ELF main/release theorem. It also proves the insufficient-byte
capacity guard and rounding of a partial final cell. Stack return storage
remains separate from the arena.

## Runtime arena ABI

`unique-list-runtime-arena/1` receives the descriptor in `rdi` and the number
of cons cells `n` in `rsi`. The descriptor is a nonzero, eight-byte-aligned
base with no 64-bit address wrap. The caller provides a mapped readable/writable
region: an 80-byte header followed by `C` cells of 32 bytes, where
`n ≤ 64` and `n + 2 ≤ C ≤ 66`. Payloads are exact unsigned 64-bit words.

The ten header words use the [existing arena layout](source-native-unique.md#arena-abi).
At entry, the cursor is `32(n + 1)`, capacity is `32C`, and allocation, live,
and peak counts are `n + 1`. Free, reuse, RC, payload, and reservation counts
are zero. Cell 0 is the all-zero nil. For each `1 ≤ i ≤ n`, cell `i` is
`(cons tag 1, xs[n-i], pointer to cell i-1, zero padding)`. The input root is
implicitly cell `n`; the function does not accept a separate arbitrary root.

`compilatrix_runtime_reverse` checks the length, descriptor alignment/nonzero
base, cursor, capacity, all eight counters, nil fields, and every cons tag,
tail, and padding field before its first write. The bounded scan advances by
cell address and compares stored tails; it never follows an unvalidated tail.
A failed check returns zero and leaves the arena unchanged. Mapped memory and
nonwrapping address range remain caller preconditions; these guards are not a
probe for arbitrary host pointers.

After validation, the function allocates one empty accumulator at cell `n + 1`,
reverses the supplied cells in place, frees the original nil, and returns the
root at cell 1 in `rax`. `compilatrix_runtime_drop` takes the same descriptor
and the returned root in `rsi`, clears/frees the complete result, and returns
zero. Both entries are leaves with no stack operations or runtime calls.

| Observation | On entry | After reversal | After release |
| --- | ---: | ---: | ---: |
| Allocations | `n + 1` | `n + 2` | `n + 2` |
| Frees | `0` | `1` | `n + 2` |
| Reuses | `0` | `n` | `n` |
| Live cells | `n + 1` | `n + 1` | `0` |
| Peak live cells | `n + 1` | `n + 2` | `n + 2` |
| RC operations / outstanding reservations | `0` | `0` | `0` |
| Reused payload units | `0` | `2n` | `2n` |

The function performs one fresh allocation; the totals include the caller's
input allocations. Validation takes `11n + 45` local evaluator steps, the
complete baseline reversal entry takes `42n + 82`, and release takes `17n + 16`.
These are instruction/terminator counts, not hardware cycle measurements.
Resource equalities apply at completed operation boundaries because individual
instructions update tags and counters separately. Trap exclusion covers every
instruction prefix.

## Checked counter folding

`Native.select compilation true` selects the same source/reuse certificate
with the checked counter-folding body. The default remains `false`, preserving
the original baseline byte for byte. `source-native-runtime --counter-fold OUT`
emits the folded variant; its source and canonical IxIR₁ graph are unchanged.

[`UniqueCounterFold`](../Compilatrix/X86/UniqueCounterFold.lean) removes four
cancelling live/reservation counter changes from adjacent reserve/reuse:
twelve instructions per cons cell. It retains every cell load/store, including
the reserved tag and original payload store, and both cumulative reuse/payload
counter changes. `state_eq` proves equality of every final register and arena
word for arbitrary initial counter values. `trace` derives the actual body
execution under the existing exclusive-arena layout contract. The complete
entry costs `30n + 82` local steps; its reversal `.text` is 952 bytes versus
1,036 for the baseline. These static savings do not establish a runtime speedup.

The combined reserve/reuse operation is one source observation boundary.
There is no intermediate reservation-count observation inside that folded
body. The complete operation restores the same tag/counter relation; trap
exclusion still covers every native instruction prefix. The input/guard,
source/physical/native execution, reclamation and actual parsed-object
theorems quantify over the selected variant and retain their existing premises.
The [paired experiment](../benchmarks/counter-fold.md) measures both actual
artifacts over the full existing matrix with the original driver.

## Artifact identity and gate

The ELF notes commit to the canonical two-function IxIR₁ graph, native lowering
version `3`, and baseline role versions `1`/`2`. Counter folding uses main role
version `3`, selector `unique-reverse-runtime-x86/2`, and the additional
`unique-reserve-reuse-counter-fold/1` policy field. Release text is unchanged;
its object provenance commits to the selected policy. The separately labeled native-policy
preimage commits to the source bytes, graph, entry/worker identities, source,
usage, lowering, reuse and execution policies, checker fuels and limits, runtime
ABI, arena bounds, constructor identities, and object role. Runtime payloads
are absent from these preimages. Diagnostic IxIR₂ JSON is not a wire identity.

The producer compiles and emits once, exporting one pipeline snapshot, one
object pair, and eight case snapshots. The independent checker reconstructs
canonical preimages and compares all files from two fresh producer processes
against the reviewed report. It checks input, returned and reclaimed heaps,
physical counters, and native operation boundaries without importing compiler,
selector, encoder, writer, or evaluator modules.
`--artifacts DIR` also compares the complete supplied artifact set byte for
byte with the fresh checked files. The paired benchmark uses this option to
bind its actual linked objects to the gate.

Binutils checks the two objects, exact text and provenance, absence of
relocations, and leaf instructions. On x86_64 Linux, the C harness links that
pair once and calls the same functions on all eight runtime inputs in one
process. It checks normalized graphs, all counters, saved registers, stack,
frame canaries, complete release, and 203 malformed-input calls with unchanged
arena bytes. These cover length, descriptor, cursor/capacity, counters, nil,
and cons tag/tail/padding errors. Six adapter/selection negatives and 20
deliberate artifact/observation corruptions are checked separately.

```sh
lake build source-native-runtime check-source-native-runtime
lake exe check-source-native-runtime \
  --fixture .lake/build/bin/source-native-runtime \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-runtime/native_harness.c
lake exe check-source-native-runtime \
  --fixture .lake/build/bin/source-native-runtime --variant counter-fold \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-runtime/native_harness.c
```

The `source-native-runtime` Nix check runs both variants with pinned tools. The
checker, shared checking utilities, harness, and both expected reports are integrity
pinned in the trust ledger. The new source/native theorem interfaces are
included in `Compilatrix.Fence`: native memory and execution use only ordinary
logical axioms; addressed source certificates retain the existing BLAKE3 axiom.

The [E2 object endpoint](x86-stream-objects.md) extends the source/native
kernel proof through independently parsed, certified ELF text for every
admitted runtime list. `Output.sourceRefinesObjects` retains the source
premises and adds successful emission plus a readable initial caller return
slot outside the arena. It proves main/release execution, physical returns,
exact parsed provenance, the reversed graph, and complete reclamation.
The [E1 byte bridge](x86-encoded-instructions.md) supplies the local instruction
laws. Reference ISA agreement and host linker/loader interpretation remain
separate assumptions. General open heaps, shared native RC, larger inputs,
additional source shapes, and native speedup claims remain outside this ABI.
