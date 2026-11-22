# E1: local execution of emitted instructions

E1 connects every emitted instruction to a separate decoder and a local
machine with byte RIP and condition flags. The proofs consume the encoder's
actual byte arrays. [E2](x86-stream-objects.md) supplies complete program
layout and ELF interpretation; agreement with an upstream ISA model remains
step S2 of the [reference-model route](x86-reference-model.md).

## The instruction table

One declarative table drives the typed machine, the byte machine, the
encoder and the decoder
([`Table/`](../IxCC/X86/Table/Op.lean)). A row `Op` is a mnemonic, an
operand width, an SDM encoding class (`OpEn`: MR, RM, MI, MI8, M, MC, OI, O,
RMI, RMI8, D32, ZO) and, for `movzx`, `movsx` and `movsxd`, a source width. `desc : Op → OpDesc`
gives each row:

- its operand slots (kinds, width, and read/write/address role), its
  implicit register operands (`mul`/`div`'s `rax`/`rdx`, a shift/rotate's `cl`) and
  implicit stack traffic;
- one semantic function `sem`, which both machines call;
- per-flag output effects (`set`, `undefined` or `unchanged`) and the flags
  the row may read;
- a decidable safety precondition `safe` under which `sem` cannot fault
  (`Op.safe_ok` proves this for every row: a nonzero divisor above `div`'s
  high half; the condition's flags defined for `jcc`, `setcc` and `cmovcc`);
- an encoding descriptor (operand-size prefix, REX.W, opcode map, opcode,
  ModRM use, register-in-opcode, immediate size and byte-register fields).

The table has 243 rows across 31 mnemonics: `add`/`or`/`and`/`sub`/`xor`/
`cmp` in MR, RM, MI and MI8 forms, `test` (MR, MI), `not` and `neg` (M),
`shl`/`shr`/`sar`/`rol`/`ror` by imm8 (MI) and by `cl` (MC), `mov` (including
8- and 16-bit widths), `movzx` (including `.w64`), `movsx`, `movsxd`, `bswap`
(widths 32 and 64), `lea`, `imul` (RM, RMI, RMI8), unsigned `mul` and `div`
(M, widths 32 and 64), `setcc` and `cmovcc` for all ten
conditions, `push`, `pop`, and the control rows. A shift's CF is its last
bit shifted out and its OF is defined only for a one-bit shift; a count of
zero leaves the processor's flags unchanged, which the model makes undefined
(reading one then faults, so the model removes behaviours and adds none).
`div` raises `#DE` on a zero divisor or a quotient that does not fit, and
leaves every flag undefined.

`Op.rows` lists the rows the compiler may emit and the decoder accepts. A
row is *linear* unless it transfers control or reads flags as data
(`setcc`, `cmovcc`): the typed machine has no flags, so it runs a flag
reader only as the consumer of a fused pair. `Instr.wellFormed` admits:

- `.op o args`: a listed linear row with operands of its slot kinds;
- `.fused p pargs c cargs`: a listed linear producer that reads no flags and
  writes nothing but flags (`Op.flagsOnly`: `cmp`, `test`), a listed flag
  consumer, operands of their kinds, and `FusedOk p c` (the producer sets
  every flag the consumer reads), so flags exist only inside the pair;
- `.unwind m`: the failure exit, whose bytes are the `mov r64, r/m64` row
  with `rsp` as its destination ([E2](x86-stream-objects.md#the-failure-exit)).

A branch terminator owns the row producing its flags (`Terminator.branch p
args c yes no`): a `cmp` or `test` in any operand form, including memory
(the prologue's `cmp r11, [r15 − 56]`), or `add`/`sub` whose carry decides
`jc`/`jb` while keeping their result. `Terminator.wellFormed` requires a
listed linear producer that reads no flags and `FusedOk p (jcc c)`.
`Terminator.compare` is compare-and-branch.

The typed constructors (`mov`, `load`, `alu`, `imul`, `imulImm`, `push`,
frames, spills, ...) choose rows and are proved well-formed
(`Instr.mov_wellFormed` and its siblings). Typed execution of each
constructor keeps its former meaning as a theorem (`executeInstr_mov`,
`executeInstr_alu`, ..., `executeInstr_unwind`, `executeTerminator_compare`).

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
flags). At 243 rows they are kernel-checked by `decide`. None of them shows that a
row's opcode is the one the processor uses; the hardware and LLVM gates test
that.

## Proved interface

[`Decode.lean`](../IxCC/X86/Decode.lean) imports only the table and
its decoder index. It parses the operand-size prefix, REX, opcode map,
opcode, ModRM, SIB, displacement and immediate, finds the row by
`(prefix, REX.W, map, opcode, ModRM digit)`, and checks the operands against
the row's slot kinds. It never calls the encoder or either evaluator.
Truncated, non-canonical and unlisted forms reject; rejection does not mean
that a byte sequence is invalid on general x86-64.

[`ByteEval.lean`](../IxCC/X86/ByteEval.lean) executes decoded rows with
the local register and permissioned byte-memory primitives. Its RIP is a
64-bit byte address. CF, ZF, SF and OF have explicit values; undefined flags
(IMUL's SF/ZF, a shift's OF for counts other than one, and every flag after
a zero-count shift or `div`) remain unknown, and a branch or flag consumer
that reads an unknown flag fails explicitly. A faulting `div` reports
`divideError` (`#DE`).

| Obligation | Kernel-checked result |
| --- | --- |
| Every listed row | `Encode.row_decode` consumes exactly the row's bytes before any suffix, for every row in `Op.rows` and operands of its slot kinds. Class lemmas (`operands_opcode` for O/OI, `operands_modrm` for MR/RM/RMI/RMI8, `operands_digit` for MI/MI8/M/MC) carry the proof; D32 and ZO rows have no ModRM. `Decode.one_stable` makes each decode independent of the bytes after it. |
| Every well-formed instruction | `instruction_decode` and `instruction_decodeAt` lift `row_decode` to single-row instructions (`Instr.single`: all but fused pairs) at an explicit offset between arbitrary bytes; `instruction_size` bounds each by 1–15 bytes. `fused_decode` and `instructions_decode` decode a fused pair to its producer and then its consumer. |
| Every terminator | `terminator_decode` covers JMP, tail JMP, RET and the producer/Jcc/JMP expansion of every well-formed branch, or producer/Jcc when its false edge falls through (`Reach.fall`). |
| Operand fields | `EncodeBytes`, `EncodeFields`, `EncodeMemory` and `EncodeRegisters` prove widths, low/extended registers, REX byte-register selection, ModRM mod 0/1/2, SIB base/index holes, scales, signed displacements, and immediate truncation/sign extension. An absent index normalizes its irrelevant scale without changing its effective address. |
| Register and memory effects | `row_execution` shows that, for every linear row reading no flags, byte execution produces the typed `advanceWith` core or the same precise fault (memory, undefined flag or `#DE`). `instruction_execution` and `encoded_instruction_execution` lift it to well-formed instructions and their encoded bytes. |
| Fused pairs | `fused_execution` shows that the byte machine's two steps (producer, then consumer on the producer's flags) produce the typed pair's core or the same fault from any earlier flags: the consumer reads only flags the producer sets (`FusedOk`, `ByteEval.restrict_merge_set`). |
| Flags and branches | `Compare.holds_eq` equates the `cmp` row's flags with the typed condition for all ten conditions; `ByteEval.compare_flags` and `Encode.compare_execution` cover signed subtraction overflow. `produced_flags` shows a branch producer's core and tested condition agree from any earlier flags. `branch_bytes_execution` runs actual producer/Jcc/JMP bytes through both paths for any producer that succeeds with its condition's flags defined; `compare_branch_bytes_execution` is its compare-and-branch instance. |
| Local patches | `patchSigned32_splice` proves that the patcher overwrites exactly four bytes. `branch_patch` applies both patches to the actual encoding of any branch. `signed32_checked` proves the signed range interpretation; `relative_resolves_base` proves the following-instruction-relative target equation. The layout encoder performs the range check; the low-level patcher only checks bounds. |
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

The public laws are audited in [`Fences/X86.lean`](../IxCCTests/Fences/X86.lean).
They depend only on `propext`, `Classical.choice` and `Quot.sound`; the
table facts, `Op.safe_ok`, `row_execution` and the patch splice need only `propext` and
`Quot.sound`. They add no hashing, native decision, ISA axiom, or assumed
step-simulation callback.

## Executable evidence

[`EncodeExamples.lean`](../IxCC/X86/EncodeExamples.lean) freezes byte-exact
goldens for every encoding choice, and
[`CheckX86Encoder`](../IxCCTests/Scripts/CheckX86Encoder.lean) has GNU objdump decode
the same 30 forms, 18 Phase 1 forms (`div`, shifts by imm8 and `cl`, `test`,
`setcc`, `cmovcc`, `op r, r/m` including the prologue's `cmp r11, [r15 −
56]`, and the failure exit's `mov rsp, [r15 − 64]` = `49 8B 67 C0`), the
addressing/REX edges and two resolved programs.
[`ByteExamples.lean`](../IxCC/X86/ByteExamples.lean) checks bytes for
SIL, clearing upper register bits, R12 SIB indices, signed comparison
overflow, sign-extended immediates, POP RSP and truncation.

The compiled [`check-x86-bytes`](../IxCCTests/Scripts/CheckX86Bytes.lean) gate covers:

- 55,940 instruction cases, including every GPR pair, width, ALU operation,
  three-operand IMUL, every base/index/scale combination, imm8/imm32/imm64
  boundary values, frame/slot bounds, and every Phase 1 row over all sixteen
  registers, addressing holes and immediate edges (with `div` on zero and
  in-range divisors). It checks exact suffix consumption, every truncated
  prefix and byte/typed execution effects on registers and touched memory.
- 2,000 patched compare-and-branch cases across all ten conditions, widths,
  register and immediate comparisons, equal values, signed extremes and
  overflow, and 12,300 patched branches after `cmp`, `test`, `add` and `sub`
  producers with register and memory operands, against the typed terminator.
- 18,200 fused pairs (`cmp`/`test` into `setcc` and each `cmovcc` width, every
  condition), each run from three earlier flag states.
- Denied memory bytes, control-stack faults, undefined flags (including a
  zero-count shift), `#DE`, rejected standalone flag consumers and
  flag-writing or flag-undefined producers, unsupported prefixes/forms, patch
  bounds, signed rel32 endpoints and corruptions.
- Four complete arithmetic, stack/spill, direct-call and tail-call streams.

The [`check-x86-hardware`](../IxCCTests/Scripts/CheckX86Hardware.lean) gate enumerates
`Op.rows`: for every non-control row (flag consumers read the case's input
flags) and each kind combination of its slots it generates register,
address (SIB and displacement holes, disp8 and disp32 edges including ±2³¹)
and immediate edge cases, plus an unmapped-address fault per memory slot,
with input flags all clear, all set or random. It adds shift and rotate counts 0, 1,
each width ± 1, the masks and wrapped counts (by imm8 and by a noisy `cl`),
`div` with zero divisors, quotient overflow and in-range quotients (the
divisor in `rax`, `rdx` or elsewhere, or in memory), fused `cmp`/`test`
pairs into `setcc` and each `cmovcc` width, branches after every `cmp` and
`test` form including memory operands, `jb`/`je` after `add`/`sub`, and
JMP, CALL and RET recipes. It currently runs 63,475 cases natively (62,195 base
cases plus 1,280 `.rol`/`.ror` count-corner cases; 1,633
expected memory faults and 243 `#DE`s) and compares exit, all sixteen
registers, model-defined flags, changed page bytes and faults (memory faults
as SIGSEGV or SIGBUS, `#DE` as SIGFPE) with `ByteEval`; `llvm-mc` must decode
every case to the same instruction lengths, mnemonics and encodings.
Mutating a shift's CF, `div`'s overflow test or `cmovcc`'s write makes the
gate fail.

These are finite regressions, not universal proofs. The GNU objdump gate,
ELF checks and linked native tests remain mandatory external evidence.

```sh
lake build IxCC check-x86-bytes check-x86-hardware
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
