# Compilatrix handoff: IxBy runtime revision 2

This is the current compiler contract. It supersedes the
[Nat/Word32 revision-1 handoff](CompilatrixNatWord32Handoff.md).
The IxBy reference interpreter, codecs, and paged proof backend implement the
runtime changes below. Compilatrix has completed its runtime-v2 integration
and exported the [new CSLib workload](../flock-stage4/fixtures/cslib-runtime-v2/README.md).
Its complete reference observation matches expected output in 360,337,913
logical transitions. The [performance priorities](IxbyPerformance.md) now use
that image; a complete CSLib Flock proof remains open.

## Required migration

1. Use unboxed Nat, Word32, and Field scalars at runtime boundaries. Remove
   `Number(n, lowWord)` wrappers and their repeated extraction where the source
   representation permits this. Use explicit conversions between scalar types.
2. Lower source arrays to the native persistent array value and primitives.
3. Accumulate byte chunks with immutable builders, freeze to Bytes, and use
   the existing checked byte-slice primitive for views.
4. Emit **format 1, semantics 2 for all three artifact types**. Update profile
   bytes and regenerate every commitment, statement, setup, and proof.

The old `IXBY`/`IXBP` semantic profiles and their `IXBI`/`IXBO` transports have
been retired. Their Lean Aiur adapters, fixed-arena Flock interpreters, and
Stage 4 `CompiledExec` adapters were removed. The generic arithmetic, memory,
verifier replay, and current paged recursive proof components remain.
Execution batch classes are physical proof geometries, not semantic versions.
The [batch tuning report](IxbyBatchTuning.md) describes the available workload
shapes and 4K prototype. Selecting one does not require a compiler ABI change.

## Scalar ABI

| Runtime type | Lean value | Meaning |
| --- | --- | --- |
| Nat | `.scalar (.nat n)` | Exact nonnegative integer within `limits.natBits` |
| Word32 | `.scalar (.word32 w)` | Unsigned 32-bit word; word arithmetic wraps |
| Field | `.scalar (.field f)` | Canonical Goldilocks element, modulus `p = 2^64 - 2^32 + 1` |

There is no numeric wrapper constructor and no implicit coercion. Nat
arithmetic retains its existing exact semantics: truncated subtraction,
`n / 0 = 0`, `n % 0 = n`, and rejection of results over the declared Nat limit.
Word32, Nat, and Field equality remain separate typed operations.

| Opcode | Primitive | Arguments | Result |
| ---: | --- | --- | --- |
| 45 | `natToWord32` | Nat `n` | Word32 `n mod 2^32` |
| 46 | `word32ToNat` | Word32 `w` | Exact Nat `w` |
| 47 | `fieldToNat` | Field `f` | Canonical Nat representative in `[0,p)` |
| 48 | `natToField` | Nat `n` | Field `n mod p` |

All four are unary. Scalar input capacity is checked before conversion, and
scalar output capacity afterward. A large Nat cannot bypass its input limit
by truncating or reducing it. Converting Field to Nat can fail when the Nat
limit is too small. Existing `word32ToField` remains opcode 23.

The Lean model supports arbitrary-size Nats within its semantic limit. The
current paged prover uses immediate **Nat128**, rejects unrepresentable
values/results, and requires `natBits >= 128`. It does not prove arbitrary-
precision Nat arithmetic. Compiler proofs must distinguish source-level Nat
semantics from this physical admission bound.

## Persistent arrays

The new value is `.array (Array Value)`. Elements may contain any runtime
value, including nested arrays. Length is strictly below `2^32`. Arrays have
no observable pointer identity; every update preserves all prior versions.

| Opcode | Primitive | Arity | Contract |
| ---: | --- | ---: | --- |
| 49 | `arrayEmpty` | 0 | Empty array |
| 50 | `arrayLength` | 1 | Array → Nat length |
| 51 | `arrayGet` | 2 | Array, Nat index → element |
| 52 | `arraySet` | 3 | Array, Nat index, value → updated array |
| 53 | `arrayPush` | 2 | Array, value → array with one appended element |

Get/set require `index < length`; wrong types or out-of-range indices fail.
Indices are checked at their full Nat width before addressing. Push rejects
when the new length would reach `2^32`. Array length is independent of the
operand-vector limit. Serialized elements share the ordinary input-node and
depth budgets with all other values.

The native implementation shares immutable binary-tree paths and flat spans
from input arrays. Get reads a path. Set/push allocate one leaf and at most
32 ancestors; existing heap cells are never overwritten. Native tests cover
tree growth through length 33, updates of flat input arrays, nested values,
exact allocation counts, and preservation of old aliases.

Compiler integration must prove a representation relation between the source
sequence and this value. Preserve source indexing and out-of-bounds behavior:
an operation that returns an unchanged array on an invalid index needs an
explicit guard before calling `arraySet`.

## Immutable byte builders and slices

The builder is an internal runtime value, `.byteBuilder bytes` in the
reference semantics. It is immutable: append returns a new builder; an earlier
builder remains valid and can be frozen independently.

| Opcode | Primitive | Arity | Contract |
| ---: | --- | ---: | --- |
| 54 | `byteBuilderEmpty` | 0 | Empty builder |
| 55 | `byteBuilderAppend` | 2 | Builder, Bytes → concatenated builder |
| 56 | `byteBuilderFreeze` | 1 | Builder → Bytes |
| 57 | `byteBuilderLength` | 1 | Builder → Nat length |

Append checks both inputs and the resulting byte length against
`limits.byteArrayBytes`. Freeze checks the input length. Length checks the
Nat result capacity. Builders are **not serializable**, including when nested
inside arrays, constructors, or PAPs. Freeze before crossing an I/O boundary
or calling a Bytes primitive. Tags `5..255` remain invalid serialized values.

Native append stores the previous builder and the chunk descriptor in two
immutable heap cells; appending an empty chunk returns the existing builder.
Freeze allocates the output once and copies each byte once, visiting chunks
backwards. It takes linear work in bytes plus chunks and preserves aliases.
The native builder length is below `2^36`, also subject to the semantic limit.

Existing `bytesSlice` is opcode **42**, with arguments Bytes, Word32 start,
Word32 length. It requires `start + length <= source.length`, with no wrapping
of the bounds calculation. A native slice shares a source range and allocates
no byte cells. Empty slices are canonical empty Bytes. `bytesAppend` remains
opcode 41 and retains its copying semantics; use builders for repeated appends.

## Canonical artifacts

All fixed-width integers are little endian. All variable naturals and vector
lengths use minimal unsigned LEB128. Reject trailing data, unknown tags,
nonminimal integers, invalid UTF-8, noncanonical Booleans and field elements.

| Artifact | Twelve-byte header |
| --- | --- |
| Program | `49 58 42 46 01 00 00 00 02 00 00 00` (`IXBF`) |
| Input | `49 58 46 49 01 00 00 00 02 00 00 00` (`IXFI`) |
| Output | `49 58 46 4f 01 00 00 00 02 00 00 00` (`IXFO`) |

Semantics 0 and 1 reject for every artifact, including programs that only use
older opcodes. There is one current revision constant, with no legacy fallback.
Opcodes `0..46` retain their meanings; `47..57` are as above; `58..255` reject.
A primitive operation is `01 || opcode:u8 || count:Nat || operands`.
Both empty primitives encode count zero and still bind a result local.

The complete opcode table and a kernel-checked exhaustive inverse theorem are
in [Codec/Encode.lean](../Ix/Ixby/Codec/Encode.lean).
Existing scalar, operand, operation, instruction, and constructor-ID layouts
are unchanged from Compilatrix's functional codec. The new serialized value is:

```text
04 || elementCount:Nat || Value[0] || ... || Value[elementCount - 1]
```

For example, an input containing one array `[Nat 7, Nat 9]` has body
`01 04 02 00 00 07 00 00 09`. Input bodies remain a vector of values; output
bodies remain exactly one value. Array values may appear recursively.
The current complete paged proof still requires a **Bytes result**. Structured
array output is supported by the reference codec; serialize it to Bytes in
the guest when using the current complete proof path.

`IXFP` remains exactly 184 bytes:

```text
0    "IXFP"
4    u32 profile revision = 0
8    u32 artifact format = 1
12   u32 semantics = 2
16   ten u128 semantic limits
176  u64 maximum logical steps
```

Limit order: functions, constructors, blocks, locals, operands, continuations,
inputNodes, natBits, stringBytes, byteArrayBytes. IXBF stores these same limits
and maximum steps immediately after its header as canonical LEB128 naturals.
The reference decoder requires exact agreement with the supplied profile.
Loader file-size and depth budgets are local admission policy and are not
additional committed semantic parameters.

The experimental `IXBE` and `IXBR` statement envelopes now also use twelve-byte
format-1/semantics-2 headers. Their sizes are 140 and 108 bytes respectively.
Commitment domains and preimages remain:

```text
H_d(x) = BLAKE3("IxBy/commit/v0" || 00 || u8(d) || x)
P = H_0(profile)       B = H_1(P || program)
I = H_2(B || input)    O = H_3(B || output)
S = H_4(P || B || I || O)
```

## Compiler migration checklist

The checklist below records the migration requirements. The imported
[compiler integration record](../flock-stage3/profile/cslib-runtime-v2/compiler-integration.json)
contains the compiler's completed integration evidence. The earlier handoff
inspected Compilatrix at `18da375`; paths below are from that handoff:

- Update the vendored reference definitions and `vendor/ixby/upstream.json`
  with the actual IxBy commit and source hashes. Relevant definitions are
  `Basic`, `Primitive`, `Validate`, `Eval`, `Profile`, and the functional codec.
- Update `Compilatrix/Ixby/Binary/{Common,Encode,Decode}.lean`: all headers,
  58 primitive names/arities, array tag 4, and recursive builder rejection.
  Re-export the exhaustive corpus with all 58 primitives. The structured
  `identity.ixbi`/`identity.ixbo` pair must contain all five wire-value kinds
  with nesting depth at least three.
- Replace numeric wrapper construction/extraction in `Runtime/Number.lean`
  and callers. Update `ScalarLaws`, `ConversionCode`, `ToWord`, `FromWord`, and
  representation certificates. Preserve weighted/accumulated helper contracts
  when retaining their old signatures; the prior handoff gives the formulas.
- Replace interpreted array tree get/set/build helpers with native operations
  and prove length, indexing, update, append, and alias-preservation laws.
- Replace repeated byte-tree construction with builder append/freeze. Use
  immutable slices for subranges. Prove the resulting byte-sequence relation,
  including empty chunks, unaligned chunks, and independently frozen aliases.
- Recalculate logical-fuel bounds. Internal array/copy microsteps do not
  consume guest fuel; each ordinary Eval/Apply/Return transition still does.
- Run compiler certificates, trust audit, and required Nix checks. Recompile
  CSLib and compare the decoded result bytes against the independent expected
  output, then export current program/input/output for native proof checks.

Existing paged limits still apply: at most 1,024 functions, 256 blocks per
function, 128 locals, 64 operands, and 1,024 continuations. Input capture admits
array spans up to 65,536 elements; runtime array operations allow lengths below
`2^32`, subject to the physical heap bound. String primitive execution and
arbitrary-precision proof arithmetic have not been added by this revision.

## Validation and reproduction

The independent [fixture generator](../flock-stage4/fixtures/paged-execution-runtime-v2.py)
exercises all eleven new opcodes, nested persistent updates, an input array,
unaligned builder chunks, and a slice of the frozen result. It takes 15 logical
steps and produces 78 canonical output bytes, matching the Lean interpreter.

```sh
python3 flock-stage4/fixtures/paged-execution-runtime-v2.py --out /tmp/runtime-v2
lake build Tests.Ixby Ix.Ixby.Audit Tests.Ixby.Audit
lake env lean --run Tests/Ixby/Fixture.lean /tmp/runtime-v2
lake env lean \
  --load-dynlib .lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3.so \
  --load-dynlib .lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3Rust.so \
  --run Tests/Ixby/Main.lean
```

The reference suites pass 339 checks. The trust gate checks 19 current theorem
roots and a 711-theorem source frontier. Native validation includes exact
integer field-conversion oracles, malicious quotient/remainder and output
bits, all collection microstate outputs, both ordinary and packed state
transport, and parser-to-native input-memory agreement.

The [durable validation record](../flock-stage4/census/paged-execution-runtime-v2.json)
contains exact artifact bytes, source and binary hashes, proof receipts,
setup geometry, timings, and the independently calculated statement digest.
The fixture has **75 native microsteps**, 15 logical steps, and a
**517,843-byte complete root proof**. A fresh process compiled the approved
setup before reading only `S` and the root. It accepted the proof and rejected
all eleven statement/proof mutations. The 187 affected Rust tests, retained
Init intake, both Clippy workspaces, and main Lean test-module build pass.

Reproduce native proofs with a release CLI. Splitting leaf production and
aggregation bounds retained process memory; the successful aggregation used
two workers, `MALLOC_ARENA_MAX=2`, 71.2 GiB peak RSS, and 618.11 seconds wall
time. A preceding four-worker combined run reached its 84 GiB cap; cached
proofs were verified before reuse. These are correctness runs, not speedup
measurements.

```sh
cargo build --release --locked --manifest-path flock-stage4/Cargo.toml \
  --bin paged-execution
flock-stage4/target/release/paged-execution leaves \
  --profile /tmp/runtime-v2/profile.ixfp --class bytes --threads 2 \
  --program /tmp/runtime-v2/program.ixby --input /tmp/runtime-v2/input.ixbi \
  --output /tmp/runtime-v2/output.ixbo --out /tmp/runtime-v2-proofs
MALLOC_ARENA_MAX=2 flock-stage4/target/release/paged-execution aggregate \
  --profile /tmp/runtime-v2/profile.ixfp --class bytes --threads 2 \
  --counts 1,3,1,1,1,1,1,1,1,1,1 \
  --statement /tmp/runtime-v2-proofs/expected.statement \
  --dir /tmp/runtime-v2-proofs
```

The verifier must use the caller's independently calculated expected `S`:

```sh
MALLOC_ARENA_MAX=2 flock-stage4/target/release/paged-execution verify \
  --profile /tmp/runtime-v2/profile.ixfp --class bytes --threads 2 \
  --counts 1,3,1,1,1,1,1,1,1,1,1 --statement /path/to/approved-S.bin \
  --proof /tmp/runtime-v2-proofs/root.flock
```

The implementation has executable constraints and proof tests. A general
kernel-checked refinement theorem from the native collection circuits to the
Lean interpreter remains open. The compiler record supplies its artifact
and reference-execution evidence; a general source-to-image refinement theorem is
not implied by proving an execution fixture.

The earlier CSLib helper census measured `natural` at 9.72%, array tree get/set
at 21.16%, and four byte-tree helpers at 14.49% of logical transitions. These
are previous helper costs, **not measured savings**. The new compiler's own
before/after comparison reports 82.28% fewer transitions; its revision-1
baseline differs from that older census. See the
[current analysis](IxbyPerformance.md#what-the-new-program-spends-transitions-on).
