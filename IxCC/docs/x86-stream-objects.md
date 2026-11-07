# E2: certified instruction streams and ELF objects

Successful production emission now carries kernel-checked certificates for
the complete text and its independently parsed ELF representation. The
runtime-input source theorem reaches execution of that actual object text
for every admitted Word list. Local ISA faithfulness, external procedure
bodies, and system linker/loader behavior remain explicit boundaries.

## Complete text

[`StreamValidate.lean`](../IxCC/X86/StreamValidate.lean) validates the
ordinary encoder's output using the separate table-indexed instruction
decoder ([E1](x86-encoded-instructions.md)). A checked program's instructions
are listed table rows with operands of their slot kinds
(`Program.wellFormed`), which discharges E1's well-formedness premise. The
validator checks every instruction and terminator, exact lengths and total text size,
canonical block offsets, all internal destinations and signed displacement
bounds, and the complete ordered runtime-relocation inventory. It validates
unreachable blocks as well as reachable ones. A runtime call before linking
must contain the expected zero displacement and its named PC32 relocation.

`Stream.check_sound` converts acceptance into concrete decoding and layout
facts. `Stream.encode` returns bytes together with that proof, or an error.
Production emission and linked-stream validation use the
[indexed checker](stream-checking.md), proved exactly equal to the retained
reference checker for every program, output, and external target assignment.
It decodes bounded windows and computes canonical offset tables once.
This is translation validation: soundness covers every accepted output;
there is no completeness claim that the unchecked encoder succeeds and
passes validation for every possible input. Equivalent encodings are allowed
when they decode to the required operation with the required length.

[`StreamLayout.lean`](../IxCC/X86/StreamLayout.lean) maps symbolic
block/instruction positions to byte offsets. The map is injective and stays
inside the text; successful linear instructions have valid symbolic
successors. `StreamLinear` proves actual whole-text fetch, register/memory
effects, precise modeled memory faults, and PC advancement. `StreamControl`
composes one-byte-machine-step jumps and the two- or three-step
producer/Jcc/JMP branch expansion (`branch_at`) for any well-formed producer:
a `cmp` or `test` in any operand form, including memory, or `add`/`sub`
deciding carry or borrow. A branch whose false edge is marked `Reach.fall`
(set by layout when the false target is the next block) has no JMP: the
checker requires the false target's block to start where the Jcc ends
(`falls`), and `branch_fall_at` takes two byte steps either way. The
typed semantics ignores the mark, and `safe_progress` keeps its one to
three byte steps per typed step. The producer's core and flags carry into the
target; its condition's flags agree with the typed machine's because the
producer sets all of them (`FusedOk`). A checked program's terminators are
well-formed (`checked_terminator_wf`), which also discharges
`terminator_decode`'s premise.

Fused pairs (`Instr.fused`) are checked as two decoded rows at consecutive
offsets. `fused_progress` relates their two byte steps to the typed pair's
one step: the flag-only producer leaves the core unchanged, and the consumer
reads only flags the producer set.

`Stream.run_to_return` covers every finite successful call-free typed run,
with arbitrary initial flags and text base. A run of `fuel` typed steps uses
between one and `3 * fuel` byte steps. The final byte core is exactly the typed
core with RSP advanced by eight, and RIP is the caller's return address. The
caller slot must be readable at the final RET. The typed top-level RET alone
does not establish that physical memory premise.

## Calls and stack observations

The typed evaluator stores a structural continuation token; CALL stores a
physical RIP. [`StreamMemory.lean`](../IxCC/X86/StreamMemory.lean)
relates all registers, permissions, and data bytes outside a precise mask of
return-slot differences. Each active frame's physical slot contains the
mapped continuation address. RET retains differences in the released slot;
an ordinary store clears exactly the bytes it overwrites. This permits
reusing a released call slot and subsequently reading ordinary data stored
there, including partial overwrites.

[`StreamTrace.lean`](../IxCC/X86/StreamTrace.lean) states the concrete
conditions for `run_with_calls`:

- CALL has an aligned stack, eight writable bytes, and a return slot disjoint
  from active frames.
- Ordinary reads avoid bytes that still contain differing return values;
  ordinary writes preserve active return slots.
- Internal RET has the expected stack position, intact typed return token,
  and preserved callee-saved registers. Its physical slot value follows from
  the maintained frame relation.
- A branch's producer and both rows of a fused pair meet the ordinary access
  conditions; the mask clears exactly the bytes the producer or consumer
  writes.
- `unwind` reads its eight-byte source as ordinary data.
- The final RET reads an ordinary caller slot. External runtime invocations
  require a separate procedure contract and are excluded from this theorem.

An instruction's memory footprint comes from the table: the reads and writes
of its memory slots by role and width, plus the word a PUSH, POP, CALL or
RET moves (`Op.reads`, `Op.writes`). `Stream.run_pair` relates the logical
and physical runs of any row whose footprint meets these conditions, so
new rows need no per-form stack proof.

`SafeTrace` describes only typed execution and these concrete access
conditions. It assumes no byte-step simulation callback. Its decisions are
executable through `StreamDecidable`; kernel-checked examples establish the
full conditions for nested calls and repeated calls followed by slot reuse.
The final theorem gives register equality and byte equality outside the
remaining mask. It makes no claim that a program observing a physical return
address as ordinary data will agree with the symbolic evaluator.

## The failure exit

Every failure (`fail heap`, the prologue's `fail stack`, `fail
natOverflow`, `trap`) leaves through the export wrapper that was entered,
with status 1–4 in `rax`, 0 in `rdx`, and the caller's callee-saved
registers restored (note 05 §6.1). The wrapper saves `rsp` in the context
(`entrySp`, at `[r15 − 64]`); the exit group runs `unwind [r15 − 64]`, whose
bytes are `mov rsp, [r15 − 64]` (`49 8B 67 C0`), then restores the saved
registers and returns.

`Instr.unwind m` runs that `mov` row on the typed machine too, then keeps
only the ghost frames outside the one the reloaded stack returns through
(`cutAt`), or every frame at depth 0; it traps with `unwindMismatch` when no
frame matches. The frames it keeps are a suffix (`cutAt_suffix`), so their
physical slots stay mapped (`FramesMapped.suffix`) and `unwind_progress`
keeps the machines related in one byte step with the mask unchanged: the
dropped frames' slots stay masked until ordinary writes clear them.
`unwind_inFrame` and `Straight.Segment.safe_unwind` state the typed step
inside a caller continuation, and `ObjectEval.run_exit` lifts any certified
run that ends as an export does (`Exit`: halted with the status in `rax`,
the value in `rdx`, the caller's callee-saved registers and stack pointer
restored) to the parsed object. `StreamExamples.unwind_safe` kernel-checks
the access conditions of a wrapper failing from three nested calls. The
`Wrapper.fail_safe` theorem that derives these conditions from the frame
invariant belongs to the stacking pass.

`CallFree` still excludes `unwind`, fused pairs and calls, so `run_to_return`,
`run_from_typed` and `run_permissions` do not cover programs using them;
`run_with_calls`, `SafeSteps.run_with_calls` and `ObjectEval.run_exit` do.

Natively, `check-x86-object` links the `unwind` fixture (an export that
recurses with the prologue's stack check and fails or succeeds by argument)
under [`unwind_harness.c`](../fixtures/x86/unwind_harness.c), which loads
sentinels into the callee-saved registers and checks `rax:rdx`, the
sentinels and `rsp` for failures one, two and four frames deep, a second
successful call on the same context, and a deep recursion under a small
stack budget (status 2). A failure before any call (the wrapper's argument
check) is covered by `check-x86-streams`.

## Object interpretation and relocation

[`ELFRead.lean`](../IxCC/X86/ELFRead.lean) imports neither the encoder
nor the writer. It reads actual little-endian fields using mathematical
naturals, bounded slices, and terminated strings. It independently parses
headers, sections, symbol names and values, Rela symbol indices/types/addends,
and provenance domain, kind, root, and version fields.

[`ELFValidate.lean`](../IxCC/X86/ELFValidate.lean) checks the exact
eight-section ET_REL/EM_X86_64 inventory, sizes, alignment, nonoverlap,
executable text and non-executable-stack policy, export placement, full
symbol/relocation inventory, and exact semantic provenance. `ELF.writeChecked`
returns a certificate over the serialized bytes. `ELF.Valid.text` and
`ELF.Valid.entry` prove that independent extraction and entry selection yield
the certified text and selected block offset. An object may export further
symbols (`ELF.Input.exports`, one per export wrapper): each is a global
function in `.text` after the entry symbol, the names are distinct, and
`ELF.Valid.exported` proves that looking a name up among the defined
function symbols (`ELF.symbol?`) yields its block's offset.

Field layouts follow the reviewed [System V ELF specification](https://gabi.xinuos.com/elf.pdf)
and [x86-64 psABI](https://refspecs.linuxfoundation.org/elf/x86_64-SysV-psABI.pdf).
The provenance note uses the existing Linux/GNU convention of 32-bit note
header fields and four-byte padding in ELF64. This convention is explicitly
supported by [GNU binutils](https://sourceware.org/pipermail/binutils-cvs/2017-November/046965.html);
it is not a claim of generic ELF64 eight-byte note alignment.

[`ELFLink.lean`](../IxCC/X86/ELFLink.lean) applies parsed PC32
relocations using `S + A - P`, checks signed overflow, and records a concrete
trace of the actual four-byte patcher. For CALL's displacement field at
instruction offset plus one and addend minus four, `pc32_call` proves that
this equals the target minus the following instruction's address. Symbol
names must decode and round-trip as UTF-8; missing names, wrong types,
overflow, and out-of-bounds patches reject.

After patching, the entire stream is revalidated with its resolved external
addresses. `runtime_call_transfer` proves that the actual CALL reaches the
named address and pushes the actual continuation RIP. It does not equate
that CALL with execution of the external procedure's body.

## Compiler endpoints

All production object emitters use `Stream.encode` and `ELF.writeChecked`:
the scalar coverage pipeline, object fixture tool, bounded native unique
compiler, and parameterized native runtime compiler. Their existing artifact
format and provenance identities are preserved. The unchecked encoder and
writer remain available for isolated tests and do not supply certificates.

[`ObjectExecution.lean`](../IxCC/X86/ObjectExecution.lean) starts
execution from the text and exported symbol parsed from actual object bytes.
Its `run_from_typed` and `run_with_calls` theorems lift the corresponding
complete-stream results through serialized ELF interpretation.

The earlier source-to-object composition for runtime list reversal
(`RuntimeObjectSim.lean`) left main with the legacy pipeline; it remains on
branch `jcb/ixby-archive`. New source compilers attach through the same
`run_from_typed` and `run_with_calls` theorems.

## Evidence and remaining boundaries

[`StreamExamples.lean`](../IxCC/X86/StreamExamples.lean) uses kernel
evaluation for accepted streams, typed returns, and complete nested/reused
call safety. The public interface axioms are pinned in
[`Fences/X86.lean`](../IxCCTests/Fences/X86.lean). Generic stream/object proofs use
ordinary logical axioms; the indexed source endpoint retains the existing
addressed-source BLAKE3 boundary. No new native reflection or ISA axiom is
introduced.

[`check-x86-streams`](../IxCCTests/Scripts/CheckX86Streams.lean) checks complete objects,
all branch conditions, branches after memory `cmp`, `test`, `add` and `sub`
producers (155 objects), fused `cmp`/`test` pairs into `setcc` and `cmovcc`
(50 objects), the failure exit at depths 0, 1, 3 and 7 and after a completed
call (sentinel callee-saved registers restored, `rax:rdx = 1:0`), a corrupted
`entrySp` (`unwindMismatch`), an `entrySp` cell on a live return slot
(rejected by `SafeTrace`), an unreadable cell (the same fault on both
machines), a plain `mov rsp, [m]` before `ret` (`stackMismatch`), a nonzero
entry, wrapping byte addresses, nested and
reused call slots, partial overwrites, rejected unsafe stack observations,
corrupted instructions and relocation metadata, ELF field mutations and every
truncated prefix, positive/negative relocation endpoints and overflow, and
physical caller-slot faults. This finite gate supplements the universal
theorems and the existing GNU/linked-native gates. (A test running the
retired N2 reversal object pair left with the legacy pipeline.)

The 2026-09-09 validation passed the 760-job Lake build, all fifteen compiled
regression gates, and all seventeen Nix checks on x86_64 Linux.

```sh
lake build IxCC check-x86-streams
./.lake/build/bin/check-x86-streams
nix build .#checks.x86_64-linux.ixcc-x86-stream-objects
```

The [trust ledger](trusted-extern-ledger.md) discharges stream/layout and
serialized-object interpretation for certified production outputs. Raw
unchecked API results retain their conditional status. Actual native
execution still assumes a linker/loader that implements the proved PC32
rule, maps the parsed text immutably for executable fetch, resolves the named
procedures, and enters the selected export with the stated ABI. The local
byte model has separate code and data memory, wrapping 64-bit arithmetic,
and modeled permission faults. A hardware interpretation must also establish
that the executable mapping has no writable alias in the arena or stack.
Canonical addresses, unified hardware fetch,
reference-ISA agreement, and external runtime-body refinement remain
separate obligations. E2 does not discharge S1/S2, N3, or finite-space F1.
