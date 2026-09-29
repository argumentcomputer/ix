# E1: local execution of emitted instructions

E1 connects every emitted instruction to a separate decoder and a local
machine with byte RIP and condition flags. The proofs consume the encoder's
actual byte arrays. [E2](x86-stream-objects.md) supplies complete program
layout and ELF interpretation; agreement with an upstream ISA model remains
S2.

## The instruction table

One declarative table drives the typed machine, the byte machine, the
encoder and the decoder
([`Table/`](../Compilatrix/X86/Table/Op.lean)). A row `Op` is a mnemonic, an
operand width, an SDM encoding class (`OpEn`: MR, RM, MI, MI8, OI, O, RMI,
RMI8, D32, ZO) and, for `movzx`, a source width. `desc : Op → OpDesc` gives
each row:

- its operand slots (kinds, width, and read/write/address role) and implicit
  stack traffic;
- one semantic function `sem`, which both machines call;
- per-flag output effects (`set`, `undefined` or `unchanged`) and the flags
  the row may read;
- an encoding descriptor (operand-size prefix, REX.W, opcode map, opcode,
  ModRM use, register-in-opcode, immediate size and byte-register fields).

`Op.rows` lists the rows the compiler may emit and the decoder accepts;
`Instr.wellFormed` admits exactly those rows with operands of their slot
kinds. The typed constructors (`mov`, `load`, `alu`, `imul`, `imulImm`,
`push`, frames, spills, ...) choose rows and are proved well-formed
(`Instr.mov_wellFormed` and its siblings). Typed execution of each
constructor keeps its former meaning as a theorem (`executeInstr_mov`,
`executeInstr_alu`, ...).

The encoder is generic over the descriptor. It emits REX only when a field
needs it (W, an extended register, or SPL–DIL in a byte slot), omits a zero
displacement except from RBP/R13 bases, uses disp8 when the displacement
fits, and keeps SIB for RSP/R12 bases and absolute addresses. The
constructors choose compact immediates: `83 /d ib` and `6B /r ib` when the
value sign-extends from a byte, `mov r32, imm32` for a 64-bit move below
2^32, `mov r/m64, imm32` for a sign-extended 32-bit value, and `movabs`
otherwise.

Kernel-evaluated `Bool` checks (`decide`, never `native_decide`) establish
the table facts: `table_injective` (decoder keys are distinct),
`table_reachable` (every row is found from its own encoding),
`table_shaped` (slots match the encoding class), `table_bounded` (every
encoding fits 15 bytes) and `Encode.table_flagsFree` (linear rows read no
flags). None of them shows that a row's opcode is the one the processor
uses; the hardware and LLVM gates test that.

## Proved interface

[`Decode.lean`](../Compilatrix/X86/Decode.lean) imports only the table and
its decoder index. It parses the operand-size prefix, REX, opcode map,
opcode, ModRM, SIB, displacement and immediate, finds the row by
`(prefix, REX.W, map, opcode, ModRM digit)`, and checks the operands against
the row's slot kinds. It never calls the encoder or either evaluator.
Truncated, non-canonical and unlisted forms reject; rejection does not mean
that a byte sequence is invalid on general x86-64.

[`ByteEval.lean`](../Compilatrix/X86/ByteEval.lean) executes decoded rows with
the local register and permissioned byte-memory primitives. Its RIP is a
64-bit byte address. CF, ZF, SF and OF have explicit values; undefined flags
(IMUL's SF/ZF) remain unknown, and a branch that reads an unknown flag fails
explicitly.

| Obligation | Kernel-checked result |
| --- | --- |
| Every listed row | `Encode.row_decode` consumes exactly the row's bytes before any suffix, for every row in `Op.rows` and operands of its slot kinds. Class lemmas (`operands_opcode` for O/OI, `operands_modrm` for MR/RM/RMI/RMI8, `operands_digit` for MI/MI8) carry the proof; D32 and ZO rows have no ModRM. `Decode.one_stable` makes each decode independent of the bytes after it. |
| Every well-formed instruction | `instruction_decode` and `instruction_decodeAt` lift `row_decode` to `Instr` at an explicit offset between arbitrary bytes; `instruction_size` bounds each instruction by 1–15 bytes. |
| Every terminator | `terminator_decode` covers JMP, tail JMP, RET and the CMP/Jcc/JMP expansion. |
| Operand fields | `EncodeBytes`, `EncodeFields`, `EncodeMemory` and `EncodeRegisters` prove widths, low/extended registers, REX byte-register selection, ModRM mod 0/1/2, SIB base/index holes, scales, signed displacements, and immediate truncation/sign extension. An absent index normalizes its irrelevant scale without changing its effective address. |
| Register and memory effects | `row_execution` shows that, for every linear row reading no flags, byte execution produces the typed `advanceWith` core or the same precise fault. `instruction_execution` and `encoded_instruction_execution` lift it to well-formed instructions and their encoded bytes. |
| Flags and branches | `Compare.holds_eq` equates the `cmp` row's flags with the typed condition for all ten conditions; `ByteEval.compare_flags` and `Encode.compare_execution` cover signed subtraction overflow. `branch_bytes_execution` runs actual CMP/Jcc/JMP bytes through both paths. |
| Local patches | `patchSigned32_splice` proves that the patcher overwrites exactly four bytes. `branch_patch` applies both patches to the actual terminator encoding. `signed32_checked` proves the signed range interpretation; `relative_resolves_base` proves the following-instruction-relative target equation. The layout encoder performs the range check; the low-level patcher only checks bounds. |
| Calls and returns | `call_pair`, `call_fault` and `ret_pair` give paired typed/byte effects, including eight-byte stack slots and memory faults. `call_bytes_execution`, `ret_bytes_execution` and `jump_bytes_execution` state physical byte effects directly. |

The linear contract uses the typed `advanceWith` operation. When
`machine.pc.next?` returns a successor, both executions have exactly the same
core. At an overflowing symbolic PC, the typed evaluator reports `pcOverflow`
instead of committing that core. E2 establishes valid reachable symbolic
PCs and their byte-address correspondence for certified complete streams.

**Limit.** The typed and byte machines share each row's semantic function,
so `row_execution` shows that they apply it identically, not that the
function is right. The decoder remains separate code, but a wrong opcode in
a row is invisible to the round trip. The hardware-differential and llvm-mc
gates below test both.

The call proofs expose the two return-slot values: the typed continuation's
structural token and the next physical RIP. They do not assert that these
values are equal. The RET pair requires corresponding slot reads, matching
stack frames and preserved callee-saved registers. E2's stack/data-access
contract and residual-byte relation establish that relation through a
complete callee. A typed top-level RET halts the harness; a physical RET
reads its caller's return address and increments RSP.

Named runtime calls emit ordinary CALL bytes (`runtime_call_form`). Their
typed atomic invocation denotes an external procedure contract. E1 does not
equate a single physical CALL with execution of an external body.

The public laws are audited in [`Fences/X86.lean`](../CompilatrixTests/Fences/X86.lean).
They depend only on `propext`, `Classical.choice` and `Quot.sound`; the
table facts, `row_execution` and the patch splice need only `propext` and
`Quot.sound`. They add no hashing, native decision, ISA axiom, or assumed
step-simulation callback.

## Executable evidence

[`EncodeExamples.lean`](../Compilatrix/X86/EncodeExamples.lean) freezes byte-exact
goldens for every encoding choice, and
[`CheckX86Encoder`](../scripts/CheckX86Encoder.lean) has GNU objdump decode
the same 30 forms, the addressing/REX edges and two resolved programs.
[`ByteExamples.lean`](../Compilatrix/X86/ByteExamples.lean) checks bytes for
SIL, clearing upper register bits, R12 SIB indices, signed comparison
overflow, sign-extended immediates, POP RSP and truncation.

The compiled [`check-x86-bytes`](../scripts/CheckX86Bytes.lean) gate covers:

- 33,793 instruction cases, including every GPR pair, width, ALU operation,
  three-operand IMUL, every base/index/scale combination, imm8/imm32/imm64
  boundary values, and frame/slot bounds. It checks exact suffix
  consumption, every truncated prefix and byte/typed execution effects on
  registers and touched memory.
- 2,000 patched branch cases across all ten conditions, widths, register and
  immediate comparisons, equal values, signed extremes and overflow.
- Denied memory bytes, control-stack faults, undefined flags, unsupported
  prefixes/forms, patch bounds, signed rel32 endpoints and corruptions.
- Four complete arithmetic, stack/spill, direct-call and tail-call streams.

The [`check-x86-hardware`](../scripts/CheckX86Hardware.lean) gate enumerates
`Op.rows`: for every linear row and each kind combination of its slots it
generates register, address (SIB and displacement holes, disp8/disp32 edges)
and immediate edge cases, plus an unmapped-address fault per memory slot and
CMP/Jcc, JMP, CALL and RET recipes. It currently runs 18,767 cases natively
and compares exit, all sixteen registers, model-defined flags, changed page
bytes and faults with `ByteEval`; `llvm-mc` must decode every case to the
same instruction lengths, mnemonics and encodings.

These are finite regressions, not universal proofs. The GNU objdump gate,
ELF checks and linked native tests remain mandatory external evidence.

```sh
lake build Compilatrix check-x86-bytes check-x86-hardware
./.lake/build/bin/check-x86-bytes
```

## Remaining boundaries

E1 discharges the local per-row portion of the encoder assumption.
[E2](x86-stream-objects.md) composes certified complete streams, symbolic
PC/return-token correspondence, internal and external fixups, and independent
ELF text, symbol, entry and provenance interpretation. It also covers
execution from parsed object text, the attachment point for new compilers.

The byte model still uses the local ISA specification. Effective addresses
and RIP arithmetic wrap at 64 bits; canonical mapped user addresses and the
ABI contracts remain premises for hardware claims. The reference model must
also account for canonical-address checks and its fault behavior. The
[reference readiness decision](x86-reference-model.md) pins and maps the
candidate Sail x86 snapshot but leaves its execution comparison and Lean
adapter unverified. The [trust ledger](trusted-extern-ledger.md) retains ISA,
unchecked raw APIs, external procedure bodies, and system linker/loader
boundaries explicitly.
