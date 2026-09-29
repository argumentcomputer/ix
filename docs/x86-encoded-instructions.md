# E1: local execution of emitted instructions

E1 connects every emitted instruction form to an independent decoder and a
local machine with byte RIP and condition flags. The proofs consume the
encoder's actual byte arrays. [E2](x86-stream-objects.md) now supplies complete
program layout and ELF interpretation; agreement with an upstream ISA model
remains S2.

## Proved interface

[`Decode.lean`](../Compilatrix/X86/Decode.lean) imports only the typed syntax.
It parses opcode, REX, ModRM, SIB, little-endian displacement and immediate
fields, rejecting truncated and unsupported forms. It does not call the
encoder or typed evaluator. This is a decoder for the emitted subset, so
rejection does not mean that a byte sequence is invalid on general x86-64.

[`ByteEval.lean`](../Compilatrix/X86/ByteEval.lean) executes those decoded
operations using the existing local register and permissioned byte-memory
primitives. Its RIP is a 64-bit byte address. CF, ZF, SF and OF have explicit
values; undefined IMUL sign/zero flags remain unknown, and a branch that reads
an unknown flag fails explicitly. The typed evaluator computes comparisons
directly, whereas the byte evaluator reads the flags produced by CMP.

| Obligation | Kernel-checked result |
| --- | --- |
| Every typed instruction | `Encode.instruction_decode` consumes exactly its bytes before any suffix; `instruction_decodeAt` works at an explicit offset surrounded by arbitrary bytes and reports the actual length. `instruction_size` bounds each instruction by 1–10 bytes. |
| Every terminator | `terminator_decode` covers JMP, tail JMP, RET and the three-instruction CMP/Jcc/JMP expansion. |
| Operand fields | `EncodeBytes`, `EncodeFields`, `EncodeMemory` and `EncodeRegisters` prove all emitted widths, low/extended registers, REX byte-register selection, SIB base/index holes, scales, signed displacements, and immediate truncation/sign extension. An absent index normalizes its irrelevant scale without changing its effective address. |
| Register and memory effects | `encoded_instruction_execution` covers MOV, loads/stores, LEA, all five ALU operations, all three IMUL widths, PUSH/POP, frames, spills and reloads. A successful byte effect supplies the exact core to typed `advanceWith`; a modeled memory failure supplies the same precise fault. |
| Flags and branches | `ByteEval.compare_flags` and `Encode.compare_execution` cover all ten conditions, including signed subtraction overflow. `branch_bytes_execution` runs actual CMP/Jcc/JMP bytes through both paths. |
| Local patches | `patchSigned32_splice` proves that the actual patcher overwrites exactly four bytes and preserves every surrounding byte. `branch_patch` applies both patches to the actual terminator encoding. `signed32_checked` proves the signed range interpretation; `relative_resolves_base` proves the following-instruction-relative target equation. The layout encoder performs the range check; the low-level patcher itself only checks bounds. |
| Calls and returns | `call_pair`, `call_fault` and `ret_pair` give concrete paired typed/byte effects, including eight-byte stack slots and memory faults. `call_bytes_execution`, `ret_bytes_execution` and `jump_bytes_execution` state physical byte effects directly. |

The linear contract uses the concrete typed `advanceWith` operation. When
`machine.pc.next?` returns a successor, both executions have exactly the same
core. At an overflowing symbolic PC, the typed evaluator reports `pcOverflow`
instead of committing that core. E2 establishes valid reachable symbolic
PCs and their byte-address correspondence for certified complete streams.

The call proofs expose the two return-slot values: the typed continuation's
structural token and the next physical RIP. They do not assert that these
values are equal. The RET pair requires concrete corresponding slot reads,
matching stack frames and preserved callee-saved registers. Establishing and
preserving that relation through a complete callee is supplied by E2's
explicit stack/data-access contract and residual-byte relation.
Likewise, a typed top-level RET halts the harness; a physical RET reads its
caller's return address and increments RSP.

Named runtime calls emit ordinary CALL bytes (`runtime_call_form`). Their
typed atomic invocation still denotes an external procedure contract. E1
does not equate a single physical CALL with execution of an external body.

The public laws are audited in [`Fences/X86.lean`](../CompilatrixTests/Fences/X86.lean).
They depend only on `propext`, `Classical.choice` and `Quot.sound` (the patch
splice needs only the first and last). They add no hashing, native decision,
ISA axiom, or assumed step-simulation callback.

## Executable evidence

[`ByteExamples.lean`](../Compilatrix/X86/ByteExamples.lean) checks independently
specified bytes for SIL, clearing upper register bits, R12 SIB indices,
signed comparison overflow, sign-extended immediates, POP RSP and truncation.

The compiled [`check-x86-bytes`](../scripts/CheckX86Bytes.lean) gate covers:

- 31,921 instruction cases, including every GPR pair, width, ALU operation,
  every base/index/scale combination, immediate edges and frame/slot bounds.
  It checks exact suffix consumption, every truncated prefix and actual
  byte/typed execution effects on registers and touched memory.
- 2,000 patched branch cases across all ten conditions, widths, register and
  immediate comparisons, equal values, signed extremes and overflow.
- Denied memory bytes, control-stack faults, undefined flags, unsupported
  prefixes/forms, patch bounds, signed rel32 endpoints and corruptions.
- Four complete arithmetic, stack/spill, direct-call and tail-call streams.

These are finite regressions, not universal stream proofs. The existing GNU
objdump gate, ELF checks and linked native tests remain mandatory external
evidence. (A byte-level run of the retired N2 reversal text left with the
legacy pipeline.)

```sh
lake build Compilatrix check-x86-bytes
./.lake/build/bin/check-x86-bytes
```

## Remaining boundaries

E1 discharges the local per-form portion of the encoder assumption.
[E2](x86-stream-objects.md) composes certified complete streams, symbolic
PC/return-token correspondence, internal and external fixups, and independent
ELF text, symbol, entry and provenance interpretation. It also covers
execution from parsed object text, the attachment point for new compilers.

The byte model still uses the local ISA specification. Effective addresses
and RIP arithmetic wrap at 64 bits; canonical mapped user addresses and the
existing ABI contracts remain premises for hardware claims. The reference
model must also account for canonical-address checks and its fault behavior.
The [reference readiness decision](x86-reference-model.md) pins and maps the
candidate Sail x86 snapshot but leaves its execution comparison and Lean
adapter unverified. The [trust ledger](trusted-extern-ledger.md) retains
ISA, unchecked raw APIs, external procedure bodies, and system linker/loader
boundaries explicitly.
