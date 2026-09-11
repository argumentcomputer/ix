# Allocating native helper

The checked runtime unique-reversal family now has an opt-in native schedule
with a real allocating helper. For a nonempty input, the caller reserves its
first cons cell, keeps its head and tail in registers, calls the helper to
allocate the result nil, and consumes the reservation after the helper returns.
The remaining list uses the existing reversal loop. Empty input calls the
same helper without a reservation.

[`AllocatingNative.select`](../Compilatrix/UniqueReuse/AllocatingNative.lean)
requires the existing successful static-reuse selection. It compiles one
function and emits one main/release object pair for every admitted runtime
input. The source family, constructor schema and exclusive arena ownership
are those of [runtime reversal](source-native-runtime.md): at most 64 exact
64-bit Words. This is a specialized native schedule for that family. General
instruction selection for allocating physical CFGs, runtime captures, recursion,
freed-slot allocation and fragmentation remain separate work.

## Finite storage and execution

The arena still needs exactly `80 + 32 × (n + 2)` admitted bytes: ten descriptor
words and `n + 2` four-word cells. A reserved cell remains in that budget while
the helper allocates. For nonempty input, the first call has these boundaries:

| Boundary | Live cells | Reserved cells | Committed cells |
| --- | ---: | ---: | ---: |
| Helper entry | n | 1 | n + 1 |
| Helper return | n + 1 | 1 | n + 2 |
| First reservation consumed | n + 2 | 0 | n + 2 |
| Main return | n + 1 | 0 | n + 2 |
| Result released | 0 | 0 | n + 2 |

The bump arena retains the backing storage of freed cells. Its committed-byte
bound includes those cells; the live counter alone is not a capacity bound.
Final allocation, reuse, release and peak counters agree with the existing
selected physical source result.

The stack contract supplies a disjoint, nonwrapping 24-byte region. At entry,
RSP points to its top eight-byte caller return slot and is 8 modulo 16. The
function subtracts eight for alignment; CALL writes the helper return address
eight bytes below that. Thus internal stack demand is **16 bytes below entry
RSP**, separately from the caller's eight bytes. The helper preserves the live
reservation pointer and saved payload operands in RDX, R8 and R9. No spills or
callee-saved register writes are needed.

[`Allocating.mainSteps`](../Compilatrix/X86/AllocatingExecution.lean) derives a
complete compositional `SafeSteps` execution for every admitted list and both
counter modes. It proves actual CALL/RET behavior, alignment, mapped stack
accesses, return-address integrity and preservation of active return slots.
The native loop and allocation proofs derive these conditions from the input
contract rather than taking an execution trace as an assumption.

[`Output.sourceRefinesObjects`](../Compilatrix/UniqueReuse/AllocatingSourceSim.lean)
connects successful ordinary Ixon application, the selected physical result,
and execution of the actual emitted ELF bytes. Its
[`ByteExecution`](../Compilatrix/UniqueReuse/AllocatingObjectSim.lean) records
the returned native pointer graph and runs the separate release object on
that exact byte memory and flags, after the caller restores RSP for the next
call. All `n + 2` allocated cells are cleared and marked freed.

[`ByteExecution.frame`](../Compilatrix/UniqueReuse/AllocatingObjectSpace.lean)
preserves every outside byte except the helper's eight-byte return slot,
including after release. That slot retains a physical code address after RET;
the typed machine instead stores a symbolic continuation token. The proof
tracks this difference explicitly, while the external return slot remains
exact. [`Object.capacityRejects`](../Compilatrix/UniqueReuse/AllocatingObjectSpace.lean)
proves that insufficient arena capacity returns zero from the actual ELF
entry with **all memory unchanged**, including the internal stack. One byte
below the required arena size rounds down to only `n + 1` complete cells.

The existing source-sharing/oracle premises, ISA reference agreement and
system linker/loader boundary remain as documented. Sixteen axiom fences
introduce no new axiom or native interface; the source and artifact identities
retain the existing Blake3 assumption.

## Versioning and exact costs

The selectors are `unique-reverse-allocating-call-x86/1` and `/2`, with ELF main
role versions 4 and 5. The release role remains version 2 and uses the existing
release text. A separate policy preimage commits to the original source/schema
and runtime policy, the allocating selector, the 16-byte stack bound, and the
role version. Runtime payloads are absent from the object identity. Existing
baseline and counter-fold runtime objects remain byte-identical.

| Input | Baseline typed steps | Counter-fold typed steps |
| --- | ---: | ---: |
| Empty | 87 | 87 |
| Nonempty length n | 42n + 86 | 30n + 98 |

The first reservation/reuse sequence is unfolded in both variants so its
reservation crosses the call; counter folding applies to subsequent loop
iterations. Actual encoded instruction counts are 106 for empty input,
`49n + 104` for nonempty baseline and `37n + 116` for nonempty counter folding.
Release takes `17n + 16` typed steps or `19n + 17` encoded instructions. These
are execution counts, with no new timing or performance claim.

## Reproducible gate

```sh
lake build source-native-allocating check-source-native-allocating
lake exe check-source-native-allocating \
  --fixture .lake/build/bin/source-native-allocating \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-allocating/native_harness.c
lake exe check-source-native-allocating \
  --fixture .lake/build/bin/source-native-allocating --variant counter-fold \
  --readelf readelf --objdump objdump --cc cc \
  --harness fixtures/source-native-allocating/native_harness.c
nix build .#checks.x86_64-linux.source-native-allocating
```

Each variant compiles once and applies the same source and target functions
to 73 runtime inputs: the eight established examples plus every length 0–64
with zero, maximum Word, the high bit, repeated and other edge payloads. Every
case compares Ixon, IxIR₀, IxIR₁, both IxIR₂ interpretations and actual ELF
execution, including complete release. The byte evaluator supplies only the
24 admitted stack bytes, observes the helper's live reservation and saved
operands, and checks insufficient-capacity and malformed-input rejection.
Additional cases deny one byte of the helper slot or caller return slot and
reject misaligned typed calls.

The independent checker imports no compiler, selector, encoder, writer or
evaluator. It reconstructs source/graph/policy preimages, compares two complete
fresh artifact sets, checks exact ELF text through GNU readelf and CALL/stack
instructions through objdump, then links each object pair once for all 73
inputs and their rejection matrix. It verifies pointer ownership, padding,
counters, canaries, stack restoration and callee-saved registers. Twenty-six
artifact and observation corruptions exercise the checker. Reviewed reports
live in [`fixtures/source-native-allocating`](../fixtures/source-native-allocating).
