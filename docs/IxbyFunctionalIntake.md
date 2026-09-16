# Complete functional binary intake

`flock-stage3/host/src/ixby/ixbf` reads **IXBF format 1, semantics 1** programs
and format-1/semantics-0 IXFI/IXFO transports. It is a host-side foundation
for witness generation and sizing, not a constrained decoder or a Flock
proving-profile adapter. No native Exec factory consumes its acceptance bit,
decoded tables, or inventory. Existing IXBY/IXBI/IXBO codecs and keys are
unchanged.

The program revision is breaking: semantics-0 programs reject. Opcodes `45`
and `46` add unary Nat → Word32 and Word32 → Nat conversions. The
[compiler handoff](CompilatrixNatWord32Handoff.md) specifies their limits,
encoding, compiler integration, and current validation. Earlier measurements
below describe the semantics-0 milestone and its original artifacts.

## Exact boundary

The reader covers every functional scalar, operand, operation, instruction,
primitive, constructor identity, and closure/PAP value. Explicit opcode-name
mapping covers all 42 native crypto/Nat operations; the three String operations
and two conversions have no opcode in that older native registry. The paged
execution backend implements the conversions directly. Mapping names does not
prove their correspondence.

All scalar naturals and potentially unbounded metadata retain arbitrary
precision: limits, fuel, arities, local counts/references, constructor
members/tags, and projection indices. Only references that must name a finite
decoded host-array element use `usize`; oversized references reject. Minimal
unsigned LEB128, strict UTF-8, canonical field coefficients/Booleans, exact
versions/domains, and complete input consumption are required.

Whole-image validation checks even unreachable functions/blocks, unique full
constructor identities, primitive/call/closure arities, all references, and
the exact local-frame contracts of successor blocks. Every admitted object
must re-encode to its original bytes. This is a runtime check, not a Lean
decoder/refinement theorem.

The admitted model exposes immutable access to its original byte buffer and
typed syntax. Large byte/string payloads borrow the buffer. Values use flat,
decoder-owned preorder nodes and an explicit parse stack; both parsing and
destruction avoid recursive ownership. One shared node budget covers every
root, constructor child, and PAP capture.

Caller-selected loader defaults are 64 MiB per file, 8,192 bytes per LEB128
integer, 1,048,576 syntax nodes, 1,048,576 value nodes, and depth 1,024. The
syntax budget is an additional host allocation bound. These are independent
of the execution limits stored in the artifact, and are not circuit/security
approvals. Counts are checked before iteration/allocation.

## Read-only inspection

```sh
cargo run --release --locked --manifest-path flock-stage3/Cargo.toml \
  --bin ixby-ixbf-inspect -- program.ixby input.ixbi output.ixbo
```

Input/output paths are optional. Every requested file is validated before the
command prints JSON. Large metadata is rendered as decimal strings; raw file
BLAKE3 hashes are explicitly **not** the existing Exec commitment digests.
The report always states `proving_admitted: false`. It contains static whole-
image facts, not an execution result, heap/stack measurement, or prover-cost
estimate.

The real retained Stage 2 image and successful Init transports passed intake:

- Program: 1,002,355 bytes; entry 680; 681 functions; 6,763 blocks; 146 layouts.
- Maxima: arity/operand vector 55, frame locals 73, blocks/function 185,
  constructor fields 9, byte literal 744,159 bytes, Nat literal 65 bits.
- Declared fuel: exactly 16,000,000,000; source Nat bound: 4,096 bits.
- Init input: 9,611,120 bytes, containing the 34-byte claim and 9,611,064-byte
  native proof. Successful output: 49 bytes, containing that exact claim.
- Used primitive kinds: 41; no String literals or String primitive sites.

## Tests and remaining work

Twenty-one ordinary tests cover all wire families, large metadata, exact scalar
bounds, malformed/truncated/nonminimal data, dead-code validation, whole-forest
fuel, and a 2,048-deep value with an explicit loader upgrade. Two additional
opt-in tests check an independent compiler corpus and pinned real Init files.
The original exported corpus passed for 81 programs and its structured I/O
fixture. The current coverage check requires all **47** primitives, seven
scalars, eight operations, and eight instruction kinds. Re-export it after
the compiler integration; the old 45-primitive corpus is insufficient.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixbf -- --test-threads=1
IXBY_IXBF_CORPUS=/path/to/exported-corpus \
  cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  compiler_corpus_covers_complete_functional_wire -- --ignored --nocapture
IXBY_IXBF_STAGE2_IMAGE=/path/to/stage2.ixby \
IXBY_IXBF_INIT_INPUT=/path/to/init.ixbi \
IXBY_IXBF_INIT_OUTPUT=/path/to/init.ixbo \
  cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  retained_stage2_init_artifacts_match_exact_pins -- --ignored --nocapture
```

The independently built Compilatrix `check-ixby-binary <export-directory>`
command produces the corpus. The real-artifact test requires the exact retained
hashes and claim; it does not silently accept a substitute fixture.

The retained Init parser fixture now uses semantics 1: change only byte 8 of
the original 1,002,355-byte program from `0` to `1`. Its exact raw BLAKE3 is
`ad104d099c9e7dbf2ac6466d8aa8d55bc06c18d90bcb0083ed9f66153c492db4`.
The original semantics-0 hash was
`a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301`.
The I/O hashes, body, offsets, and census remain fixed. This fixture exercises
the current parser; it is not an optimized compiler image or a reuse of an old
execution proof. Production intake performs no header migration.

The [constrained codec components](IxbyFunctionalCodec.md) now check original
header metadata, natural payloads and ByteArray ranges, with isolated component
proofs. They do not yet establish whole-image admission or the identity bridge.
The remaining constrained decoder/identity bridge, streaming execution witness,
scalable memory/code access, full-state segment composition, and formal
correspondence remain separate work. See the [scaling plan](IxbyStage3ScalePlan.md).
