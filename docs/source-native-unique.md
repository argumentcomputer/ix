# Source native unique-list reversal

The bounded native endpoint compiles the checked Ixon unique-list reversal
through actual static IxIR₂ selection, typed x86-64, and ELF objects. For every
selected list of at most 64 exactly representable Word values, kernel-checked
execution returns the reversed owned chain and the separate release entry
reclaims every allocated cell. Eight source-produced object pairs also pass
independent decoding, linking, and execution on x86-64 Linux.

This endpoint uses the source schema and unchanged source contract described
in [source unique reuse](source-unique-reuse.md). It supports closed lists,
including empty lists and repeated values. Native selection rejects a Nat
outside `[0, 2^64)` without truncation, a 65-element input, disabled static
reuse, and unavailable target validation. A native skip retains the compiler's
checked IxIR₂ artifact or consuming IxIR₁ fallback.

The separate [runtime-input endpoint](source-native-runtime.md) compiles the
parameterized function once and uses one object pair for caller-built lists.
This document retains the closed-input ABI and its regression contract.

## Public interface and proof

`UniqueReuse.compile` produces the checked source artifact.
[`Native.select`](../Compilatrix/UniqueReuse/Native.lean) returns either a
reasoned skip or `Native.Output`, retaining the actual translated target,
static-reuse selection, exact source-to-Word equality, length bound, and checked
main/release programs. [`Output.emit`](../Compilatrix/UniqueReuse/NativeObject.lean)
accepts that successful certificate and emits either object role.

[`Output.sourceRefines`](../Compilatrix/UniqueReuse/NativeSim.lean) consumes only
the existing source oracle correspondence, sharing well-formedness, and
successful Ixon evaluation hypotheses. Its conclusion includes the original
source/ownership/cost endpoint and native execution for any valid arena layout.
`SourceNativeResult.witness` constructs a concrete arena internally, so the
source theorem adds no caller-supplied heap-shape, ownership, or cost premise.

`Output.executes` connects the actual selected program to `X86.runFrom` over
permissioned byte memory. Its result contains the source value relation,
returned finite list graph, exact counters, both terminating calls, complete
reclamation, and preservation of surrounding bytes and System V saved
registers. `Execution.mainSafe` and `releaseSafe` exclude every local memory or
ABI trap at every execution prefix. `Output.costsAgree` connects the native
word counters to the physical statically reused IxIR₂ result from the same
compilation.

The proof proceeds through little-endian word read/write laws, an arena word
view, instruction effects in the existing evaluator, allocation/reuse/release
traces, and full branch/loop composition. Input construction proves the owned
chains from fresh memory. The descending input and ascending accumulator have
disjoint cell intervals; `NativeList.nodup` proves the returned byte-memory
footprint has no repeated pointer. Full release clears all fields of all
`n + 2` allocated cells. The native memory/execution proof uses only the ordinary
logical axiom set. Source-facing statements inherit the already fenced BLAKE3
axiom from their addressed compiler certificate. No new axiom or native FFI
interface is introduced.

## Arena ABI

`unique-list-arena/1` uses one caller-provided region with an eight-byte-aligned,
nonzero base and no 64-bit address wrap. The modeled region is readable and
writable. Native callers provide ordinary mapped memory. The first 80 bytes
contain ten 64-bit words, followed by four-word cells:

| Header word | Meaning |
| --- | --- |
| 0 | Bump cursor in bytes from the first cell |
| 1 | Available cell capacity in bytes |
| 2–6 | Allocations, frees, reuses, live cells, peak live cells |
| 7–9 | RC operations, reused payload units, outstanding reservations |

Each 32-byte cell stores `(tag, scalar head, native tail pointer, zero padding)`.
Tags are nil `0`, cons `1`, reserved `2`, and freed `3`. Nil and freed payloads
are zero. The selected source schema's complete constructor identities give
the nil/cons tags their meaning; this is not an open constructor ABI.

`compilatrix_main` receives the descriptor in `rdi`, initially zero except for
capacity, and returns its owned root in `rax`. It checks `cursor ≤ capacity`
and sufficient remaining bytes before its first store. It builds the closed
input and an empty accumulator inside the arena, reverses in place, and frees
the old input nil. `compilatrix_unique_drop` receives the descriptor in `rdi`
and returned root in `rsi`, clears/frees the result, and returns zero. Both are
leaves using caller-saved registers, with no stack operations or runtime calls.
The arena capacity is at most 66 cells; successful main execution requires
at least `n + 2`.

| Observation | After reversal | After full release |
| --- | ---: | ---: |
| Allocations | `n + 2` | `n + 2` |
| Frees | `1` | `n + 2` |
| Reuses | `n` | `n` |
| Live cells | `n + 1` | `0` |
| Peak live cells | `n + 2` | `n + 2` |
| RC operations | `0` | `0` |
| Reused payload units | `2n` | `2n` |
| Outstanding reservations | `0` | `0` |

Main takes exactly `51n + 62` local evaluator steps, and release takes
`17n + 16`. These include block terminators; they are not hardware cycle
counts. Heap counters count arena-cell operations, excluding the harness's
allocation of the containing buffer. Resource/ownership equalities are checked
at completed allocation, reserve, reuse, and release boundaries. Individual
machine instructions update tags and counters separately, so the native
microstates are not claimed to satisfy the IxIR₂ allocation equation at every
instruction. Trap exclusion covers every instruction prefix.

## Object identity and independent gate

Both ELF notes retain the real canonical consuming IxIR₁ graph root. Native
lowering version `2` and role policy versions `1` (main) / `2` (release)
distinguish these objects from scalar selection and each other. The separate
canonical native-policy preimage commits to the unique source-policy digest,
IxIR₁ root, ABI and selector versions, arena bounds, full nil/cons identities,
exact input words, and role. Its digest is labeled as a native-policy identity;
it is never substituted for an IxIR₁ or independent IxIR₂ root.

The producer exports full source-pipeline snapshots, both typed-program
diagnostics, text bytes and block offsets, object/policy identities, byte-model
heaps, and sampled operation boundaries. Two fresh processes must produce
identical complete artifact sets and match the reviewed report. The independent
Lean checker imports only shared checking utilities and the existing hash
primitive; it reconstructs source, mode, graph, and policy preimages and
validates both returned and fully reclaimed heaps.

The gate covers empty, zero, singleton, three-element, mixed Word, maximum Word,
repeated, and 64-element inputs, plus six native-selection fallbacks. Binutils
checks 16 ELF objects, exact text, provenance, absence of relocations, and leaf
instructions. The linked C harness checks reversal, normalized pointer graphs,
all counters, saved registers, canaries, full release, and four capacity errors
that must leave the entire arena unchanged. Twelve deliberate native
corruptions exercise ABI, policy, root, pointer, padding, resource, and release
checks. The pre-existing source checker is shared without importing compiler
or evaluator code.

```sh
lake build source-native-unique check-source-native-unique
lake exe check-source-native-unique \
  --fixture .lake/build/bin/source-native-unique \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-unique/native_harness.c
```

The `source-native-unique` Nix check runs this gate with pinned tools. The
checker, native harness, shared utilities, and reviewed report are integrity
pinned in the trust ledger.

## Remaining boundary

This family's source theorem ends at the existing typed x86 semantics.
Production emission now carries the [E2 stream and ELF certificates](x86-stream-objects.md),
and the generic object-execution bridge is available for its successful typed
runs. The composed source-to-object theorem is currently exposed for the
parameterized N2 family. ISA faithfulness and system linker/loader behavior
remain ledgered. General unique graphs, external list roots, shared native heap operations,
borrow inference, broader source compilation, and independent IxIR₂ wire
identity remain separate work. No native speedup or self-hosting claim follows
from this bounded reversal witness.
