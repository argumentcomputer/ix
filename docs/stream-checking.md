# Indexed stream checking

Production `Stream.encode` and `ELFLink.resolve` validate through
`Stream.checkIndexed`. They return the existing `Stream.Valid` certificate,
so the complete-stream, relocation, and source-to-ELF theorems keep the same
statements. The original `Stream.check` remains available as a reference in
[`StreamSpec.lean`](../Compilatrix/X86/StreamSpec.lean), with its original
decoder and prefix-sum layout specification.

[`DecodeWindow.lean`](../Compilatrix/X86/DecodeWindow.lean) extracts at most
15 bytes at the requested position before converting them to a list. It uses
the same independent instruction parser. Prefix-consumption lemmas show
that accepted instructions do not inspect their remaining suffix;
`Decode.decodeWindowAt_eq` proves equality with `Decode.decodeAt` for every
byte array and natural offset. This includes malformed bytes, truncation,
unsupported prefixes, alternative encodings, and positions past the end.
The bound is the existing decoder's maximum accepted instruction length.

[`StreamIndex.lean`](../Compilatrix/X86/StreamIndex.lean) computes canonical
instruction positions, block starts, and total text size in one traversal of
the program's size lists. Each cached position is proved equal to the
original prefix-sum specification. The proposed encoder's offset table is
still checked against the canonical table. A `PreparedLayout program` carries
an erased equality proof tying its index to that exact program; callers may
reuse it with `checkPrepared` to validate multiple proposed outputs.

[`StreamIndexed.lean`](../Compilatrix/X86/StreamIndexed.lean) checks every
instruction and terminator, including unreachable blocks, with bounded
windows and indexed positions. It checks the same total length, block
offsets, target bounds, signed displacements, and ordered relocation inventory.
`Stream.checkPrepared_eq` and `Stream.checkIndexed_eq` prove exact Boolean
equality with the reference checker for every program, output, and external
target assignment. `checkIndexed_sound` then supplies the original certificate.
Four public axiom fences use only `propext`, `Classical.choice`, and
`Quot.sound`; no axiom or native interface was added.

The reference checker converts the whole text to a list at each instruction
and repeatedly recomputes prefix sums. The indexed checker instead performs
bounded work per decode and stores one position per instruction plus block
metadata. Its additional retained layout space grows with instruction and
block count. These implementation properties and the fixture timings do not
establish a universal machine-cost theorem. The byte evaluator retains the
original decoder and remains an independent semantic regression path.

The byte gate compares both decoders across 31,921 emitted instruction forms,
every proper truncation, 2,000 patched branches, and 131,084 short/padded or
out-of-range inputs. The stream gate checks both validators on ordinary and
corrupted text, offsets, and runtime relocations; it adds empty programs,
long instruction arrays through 1,024 instructions, repeated layout use,
invalid direct/tail targets, and resolved signed-rel32 endpoints and overflow.
Direct typed-x86 stress inputs do not alter source compiler admission limits.

The existing [native graph benchmark](../benchmarks/native-graph.md) now
separates raw encoding, reference validation, layout construction, prepared
validation, and complete indexed validation. All snapshot, text, ELF,
observation, and resource-bound goldens remain unchanged. Its independent
gate checks fresh persisted-input recompilation and guarded native execution.
The [retained comparison](performance/stream-check-2026-09-13/README.md)
records three fresh reference processes, raw stage samples, whole-process
memory, source and tool identities, and replay evidence.
