# E2: certified instruction streams and ELF objects

Successful production emission now carries kernel-checked certificates for
the complete text and its independently parsed ELF representation. The
runtime-input source theorem reaches execution of that actual object text
for every admitted Word list. Local ISA faithfulness, external procedure
bodies, and system linker/loader behavior remain explicit boundaries.

## Complete text

[`StreamValidate.lean`](../Compilatrix/X86/StreamValidate.lean) validates the
ordinary encoder's output using the independent instruction decoder. It
checks every instruction and terminator, exact lengths and total text size,
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

[`StreamLayout.lean`](../Compilatrix/X86/StreamLayout.lean) maps symbolic
block/instruction positions to byte offsets. The map is injective and stays
inside the text; successful linear instructions have valid symbolic
successors. `StreamLinear` proves actual whole-text fetch, register/memory
effects, precise modeled memory faults, and PC advancement. `StreamControl`
composes one-byte-machine-step jumps and the two- or three-step CMP/Jcc/JMP
branch expansion, including both signed and unsigned comparisons.

`Stream.run_to_return` covers every finite successful call-free typed run,
with arbitrary initial flags and text base. A run of `fuel` typed steps uses
between one and `3 * fuel` byte steps. The final byte core is exactly the typed
core with RSP advanced by eight, and RIP is the caller's return address. The
caller slot must be readable at the final RET. The typed top-level RET alone
does not establish that physical memory premise.

## Calls and stack observations

The typed evaluator stores a structural continuation token; CALL stores a
physical RIP. [`StreamMemory.lean`](../Compilatrix/X86/StreamMemory.lean)
relates all registers, permissions, and data bytes outside a precise mask of
return-slot differences. Each active frame's physical slot contains the
mapped continuation address. RET retains differences in the released slot;
an ordinary store clears exactly the bytes it overwrites. This permits
reusing a released call slot and subsequently reading ordinary data stored
there, including partial overwrites.

[`StreamTrace.lean`](../Compilatrix/X86/StreamTrace.lean) states the concrete
conditions for `run_with_calls`:

- CALL has an aligned stack, eight writable bytes, and a return slot disjoint
  from active frames.
- Ordinary reads avoid bytes that still contain differing return values;
  ordinary writes preserve active return slots.
- Internal RET has the expected stack position, intact typed return token,
  and preserved callee-saved registers. Its physical slot value follows from
  the maintained frame relation.
- The final RET reads an ordinary caller slot. External runtime invocations
  require a separate procedure contract and are excluded from this theorem.

`SafeTrace` describes only typed execution and these concrete access
conditions. It assumes no byte-step simulation callback. Its decisions are
executable through `StreamDecidable`; kernel-checked examples establish the
full conditions for nested calls and repeated calls followed by slot reuse.
The final theorem gives register equality and byte equality outside the
remaining mask. It makes no claim that a program observing a physical return
address as ordinary data will agree with the symbolic evaluator.

## Object interpretation and relocation

[`ELFRead.lean`](../Compilatrix/X86/ELFRead.lean) imports neither the encoder
nor the writer. It reads actual little-endian fields using mathematical
naturals, bounded slices, and terminated strings. It independently parses
headers, sections, symbol names and values, Rela symbol indices/types/addends,
and provenance domain, kind, root, and version fields.

[`ELFValidate.lean`](../Compilatrix/X86/ELFValidate.lean) checks the exact
eight-section ET_REL/EM_X86_64 inventory, sizes, alignment, nonoverlap,
executable text and non-executable-stack policy, export placement, full
symbol/relocation inventory, and exact semantic provenance. `ELF.writeChecked`
returns a certificate over the serialized bytes. `ELF.Valid.text` and
`ELF.Valid.entry` prove that independent extraction and entry selection yield
the certified text and selected block offset.

Field layouts follow the reviewed [System V ELF specification](https://gabi.xinuos.com/elf.pdf)
and [x86-64 psABI](https://refspecs.linuxfoundation.org/elf/x86_64-SysV-psABI.pdf).
The provenance note uses the existing Linux/GNU convention of 32-bit note
header fields and four-byte padding in ELF64. This convention is explicitly
supported by [GNU binutils](https://sourceware.org/pipermail/binutils-cvs/2017-November/046965.html);
it is not a claim of generic ELF64 eight-byte note alignment.

[`ELFLink.lean`](../Compilatrix/X86/ELFLink.lean) applies parsed PC32
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

[`ObjectExecution.lean`](../Compilatrix/X86/ObjectExecution.lean) starts
execution from the text and exported symbol parsed from actual object bytes.
Its `run_from_typed` and `run_with_calls` theorems lift the corresponding
complete-stream results through serialized ELF interpretation.

[`RuntimeObjectSim.lean`](../Compilatrix/UniqueReuse/RuntimeObjectSim.lean)
composes the actual N2 source compiler and successful object emission.
`Output.sourceRefinesObjects` preserves the existing source, graph, cost,
ownership, and complete-reclamation conclusions for every admitted runtime
Word list. Both objects' parsed provenance records the selected source graph,
lowering version, and role policy. A readable initial caller return slot
outside the arena is enough: the proof derives its preservation through
main and release, including read permissions. The harness enters each export
with its normal initial RSP; each physical RET advances it by eight.

The new endpoint retains N2's existing source-argument, sharing/oracle,
successful-application, bounded-ABI, and emission-success premises. It
neither broadens the selected source family nor proves a total compiler.

## Evidence and remaining boundaries

[`StreamExamples.lean`](../Compilatrix/X86/StreamExamples.lean) uses kernel
evaluation for accepted streams, typed returns, and complete nested/reused
call safety. The public interface axioms are pinned in
[`Fence.lean`](../Compilatrix/Fence.lean). Generic stream/object proofs use
ordinary logical axioms; the indexed source endpoint retains the existing
addressed-source BLAKE3 boundary. No new native reflection or ISA axiom is
introduced.

[`check-x86-streams`](../scripts/CheckX86Streams.lean) checks complete objects,
all branch conditions, a nonzero entry, wrapping byte addresses, nested and
reused call slots, partial overwrites, rejected unsafe stack observations,
corrupted instructions and relocation metadata, ELF field mutations and every
truncated prefix, positive/negative relocation endpoints and overflow, and
physical caller-slot faults. It compiles one actual N2 object pair and runs
all eight retained inputs through parsed text, checking registers, every
arena byte, reversed pointer graphs, and complete release. This finite gate
supplements the universal theorems and the existing GNU/linked-native gates.

The 2026-09-09 validation passed the 760-job Lake build, all fifteen compiled
regression gates, and all seventeen Nix checks on x86_64 Linux.

```sh
lake build Compilatrix check-x86-streams
./.lake/build/bin/check-x86-streams
nix build .#checks.x86_64-linux.x86-stream-objects
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
