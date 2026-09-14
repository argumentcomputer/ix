# Typed Lean to full-runtime Ixby

The typed frontend emits a complete, executable [Ixby binary](ixby-binary.md).
The retained [Stage2 artifact](../fixtures/ixby-stage2/stage2.ixby) contains both
fixed keys and the complete verifier code: 1,002,355 bytes, 681 functions,
6,763 blocks, 146 constructor layouts, and entry function 680. A separate
`ixby-exec` process loads the binary and runs the unchanged Ixby evaluator.
Execution needs no compiler environment or retained Lean source declarations.

`Compilatrix.Ixby.LeanFrontend.compile` lowers pure monomorphic LCNF after
Lean's typed proof erasure and specialization. Every emitted block passes the
reference whole-program validator. Unknown runtime externs are rejected.
Packed byte capacity must be below 2³², matching the target byte-index ABI.

The frontend remains experimental. The [runtime proofs](ixby-representation.md)
establish exact numeric/byte laws and certify all fourteen emitted field helpers,
eleven number conversion helpers, eight Nat arithmetic/comparison helpers,
and six Nat shift/logarithm/power functions, including complete loops and caller continuations.
The complete frontend has no source-refinement certificate. It does
not produce an `IxonCompilation` or
authenticate the original anonymous Ixon source address. Constructor identities
are local layout identifiers. These source certification obligations are
separate from binary export and execution.

## Runtime representations

Naturals retain their exact mathematical values. Arithmetic uses native Nat
primitives with truncated subtraction and the reference division/remainder by
zero behavior. An optional low Word32 cache supports byte indexing and word
operations. Division and remainder produce uncached values; ordinary arithmetic
propagates them without unnecessary word conversion. Conversions consume four
bits at a time through comparisons with literals and ordinary instructions.
The USize lowering uses 64-bit source semantics.

Goldilocks operations use native field addition, subtraction, multiplication,
inversion and equality. A field-backed number retains an exact Nat view for
Lean's transparent `Fin.val` representation. Mixed field/Nat comparisons compare
exact naturals; they never reduce an arbitrary comparison operand modulo the
field. Extension values use native extension scalars, including construction,
projections, arithmetic, inversion, equality, and storage in arrays.

Ordinary immutable arrays use binary trees. Byte inputs use packed scalar
bytes; concatenations use balanced trees of byte blocks. Polymorphic updates
widen packed storage to ordinary values. Calls, partial applications,
oversaturation, lifted joins, constructors, case analysis, and tail calls use
the corresponding reference instructions. BLAKE3 uses the reference primitive.

The optional Stage2 wire lowering covers the pinned little-endian helpers,
single-byte and field writers, field reader, and specialized byte comparison.
Field I/O uses `bytesToField` and `fieldToBytes`. A two-word canonicality check
preserves the source `.field` error for encodings at or above the modulus.
The original `readBytes` and `writeBytes` functions retain truncation, byte
limits, and state updates. General array comparison callbacks compile from
source. No host invocation of the Stage2 verifier supplies an execution result.

## Binary artifact and ABI

The [full binary format](ixby-binary.md) encodes all seven scalar kinds, all
45 primitives, every operation and instruction, constructor identities,
functions, blocks, entry point, execution capacities, and maximum steps.
Minimal unsigned LEB128 encodes naturals, indices, counts, and the step budget;
there is no implicit Word32 bound on Nat or the number of transitions.
The smaller upstream cryptographic codec remains a separate format. Its
admission rules do not restrict this compiler artifact.

The Stage2 adapter embeds the original 925,789 key bytes, entrypoints 755/243,
and fixed source configuration. Its arguments are two raw scalar byte arrays:
the public claim and private native proof. Success returns the exact raw claim
bytes; rejection returns erased. The compile report identifies every function,
constructor layout, instruction and primitive, the binary SHA-256, and static
frame maxima. The binary itself contains everything needed for execution.

## Reproduction and tests

```sh
lake build stage2-ixby ixby-exec check-ixby-lean check-ixby-binary
lake exe check-ixby-lean
lake exe check-ixby-binary
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
python3 scripts/inspect_ixby.py /tmp/stage2.ixby --expected /tmp/stage2.ixby.json
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

Compilation and the typed comparison suite use Lake's environment to load LCNF.
The case runner loads the supplied binary; omitting its final path loads the
retained `fixtures/ixby-stage2/stage2.ixby`. It never recompiles in case mode.
The standalone command is:

```sh
.lake/build/bin/ixby-exec program.ixby input.ixbi output.ixbo execution.json
```

The focused suite compares 4,585 reference executions with independently
executed Lean source results. It covers large naturals beyond 64 bits, field
boundaries and zero inverses, mixed representations, extension projections and
arrays, closures, persistent arrays, byte ropes and mutation, exact wire
outputs, malformed field encodings, read offsets, writer limits, and a
10,000-iteration tail call under an eight-continuation limit. Two compiler
rejections cover unsupported Float externs and invalid byte-index capacities.
Every compared image also obtains number-layout evidence and certificates for
seven native extension helpers and eleven number conversion helpers. Eight
scalar mutations and 21 conversion mutations must fail certificate construction;
five and 17 respectively remain structurally valid programs. The conversion
contracts also have 224 admitted executions and eleven local resource cases,
including the 33-bit final-weight requirement of word-to-Nat conversion.
The eight Nat arithmetic/comparison certificates cover addition, subtraction,
multiplication, division, remainder, equality, and both order comparisons for
every input representation pair. Their contracts include exact results,
consistent caches, both subtraction branches, zero divisors, and the direct
native-field equality path. Their tests include 12,168 admitted executions,
32 caller cases, 35 local resource cases, and 48 rejected mutations, of which
43 remain structurally admitted. Twenty-one axiom guards keep the arithmetic,
comparison, and call contracts on the ordinary logical basis. Representation
and capacity premises remain explicit; these certificates do not certify general LCNF lowering.
Stage2 binary compilation performs the same certificate checks before export.

The remaining seven field certificates cover `Goldilocks.reduce`, addition,
subtraction, multiplication, negation, inversion, and `ExtGoldilocks.mk`.
They execute both `asField` conversions where required, the native operation,
exact result boxing or extension packing, and caller restoration. Their
uniform local bounds are 11 slots, 64 Nat bits, and three spare continuations;
no byte capacity or separate result bound is required. Whole-program contracts
retain ordinary program/input admission and input representation premises.
The field suite adds 6,201 admitted executions, 25 caller cases, eight
packing/projection cases, 24 resource cases, and 29 rejected mutations, of
which 24 remain structurally admitted. Seventeen additional axiom guards keep
these contracts on the ordinary logical basis. Every image and Stage2 export
obtains both field certificate families.

Six further certificates cover `Nat.shiftRight`, `Nat.log2`, `Nat.pow`, and
their loop helpers. Their finite execution proofs preserve arbitrary callers,
exact Nat results, and consistent caches. The shift and logarithm loops need
no additional continuation; the public wrappers need three spare frames.
Power needs four spare frames for its nested multiplication/conversion calls.
The public power contract derives every intermediate-product bound from the
input and final-result bounds, including zero cases and the skipped final
square. The internal loop with an arbitrary accumulator also requires the
unscaled power to fit. The tests add 6,016 admitted executions, 51 caller cases,
45 resource cases, and 44 rejected mutations, of which 40 remain structurally
admitted. Nineteen axiom guards cover the loop contracts and supporting bounds.
Every compared image and Stage2 export obtains these certificates.

The binary suite checks 81 decoded executions covering every scalar, primitive,
operation, and instruction. It also checks structured constructor/PAP input and
output, all proper-prefix truncations of representative artifacts, malformed
tags, versions, UTF-8, booleans, fields, nonminimal integers, and loader limits.
The independent Python decoder reads the exported test corpus and the full
Stage2 artifact and checks reference structural admission.

The integration gate compares two fresh binaries and manifests byte for byte
with each other and the retained artifacts. It runs the standalone executor
outside the compiler directory with `LEAN_PATH` unset, then executes all eight
Stage2 cases from serialized binaries:

| Case | Actual result | Reference transitions |
| --- | --- | ---: |
| Valid proof | Exact 34-byte claim | 4,527,451,540 |
| Changed claim root | Erased | 1,673,425,178 |
| Empty proof | Erased | 147,664,894 |
| Truncated proof | Erased | 462,935,257 |
| Trailing public byte | Erased | 253 |
| Trailing proof byte | Erased | 462,956,800 |
| Wrong claim kind | Erased | 420 |
| Malformed proof | Erased | 147,664,913 |

Step-limit exhaustion fails the test. The artifact allows 16 billion reference
transitions. The runner executes chunks of one million transitions;
`Runtime.runChunk_run` proves composition with the remaining upstream
execution. This equation concerns the runner, not compiler source refinement.
Reference execution capacities are explicit runtime bounds. The proving agent
can use the artifact, exact format, and inventory to develop its executor
independently of this compiler's export path.
