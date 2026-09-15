# Authenticated typed code access

`flock-stage3/host/src/ixby/ixbf_decode/code/` hashes the actual completed
typed Program records and reads them through authenticated BLAKE3 chunks.
Consumers carry a requested record and its chunk handles, without carrying
the entire declaration/body bank into every read. Handles can serve multiple
reads when their constrained chunk indices match.

Sealing still uses the existing bounded [body loader](IxbyFunctionalBodies.md).
This component does not admit the full Init image or execute its instructions.
The code digest is a new internal commitment, distinct from the original raw
file digest and the native Exec statement.

## Binding and representation

`CodeCommitSlots::seal` accepts a privately constructed
`FinishedProgramBodies`. It hashes the actual completion outputs, including
the final grammar, constructor registry, function records and every body word.
There is no production constructor for a sealed root supplied as private
advice. The test-only independent-root constructor is used solely for access
regressions and address/path censuses.

The caller supplies the **actual original digest used to authenticate Program
reads**. This is an explicit composition requirement, shared with the body
loader's authenticated-read callback. The joint proof hashes the original
buffer once and wires that same result into the code image. String and
ByteArray records retain source ranges, so embedding this digest prevents
different payload bytes with identical range descriptors from sharing a code
commitment. A later execution consumer must authenticate those payload ranges
against this original digest.

Each image word is 16 bytes, low u64 then high u64, both little-endian.
The unkeyed BLAKE3 hash covers precisely this fixed-length image:

| Region | Words | Contents |
| --- | ---: | --- |
| Schema | 6 | `IxBy/code/v0` padded to 16 bytes, then constructor/function/block/operand capacities and Nat-bit capacity |
| Program manifest | 30 | Original digest (2), actual final grammar (28) |
| Constructors | `7*C` | Actual checked constructor records |
| Functions | `5*F` | Actual completed function records |
| Blocks | `F*B*R` | Actual completed owned blocks, including ordered operands and alternatives |

Here `R = 14 + O*(7 + W) + 4*C`, and `W = max(1, ceil(NatBits/128))`.
The field definitions are those of the existing
[registry](IxbyFunctionalRegistry.md) and [bodies](IxbyFunctionalBodies.md).
Physical absence and unused fields retain their canonical zero representation.
The hash buffer's final 64-byte block is zero-padded as necessary; padding is
excluded from the committed image length.

`CodeLayout` calculates dimensions with checked u128 arithmetic and admits
only totals whose byte length fits u64. Physical address dimensions fit u32;
queries remain full 128-bit words. Large layout values enable address/path
components only. They do not expand the bounded loader or authorize a larger
original-file execution profile.

## Constrained reads and reusable chunks

Six setup-owned record kinds cover Program, Constructor, Function, Block,
Operand and Alternative. Each has a Request table and a Record table:

1. Request consumes `(enabled, owner/index, block, ordinal)`. It checks the
   full words, physical bounds, unused/disabled zeros, multiplication/addition
   overflow and exact record extent. It derives the byte cursor, record width
   and first/next chunk indices from the fixed layout.
2. Authentication uses the existing source block/path and BLAKE3 compression
   relations. Each private handle retains the actual root, index, layout and
   chunk-byte wires. Missing path siblings and chunk padding are constrained.
3. Read connects both handles' roots and indices to the sealed image and
   actual request, then passes those chunk bytes through the existing source
   window relation. It connects the resulting length and indices as well.
4. Record consumes that exact window. Enabled records must be present;
   Program must have a terminal manifest. Disabled and unused window words
   are zero. It returns the actual fields, with no whole-bank selector scan.
   Semantic checks remain supplied by the completed source-bound loader.

Authenticating a pair costs 32 compression blocks and `2*depth` path
compressions. Each additional read reusing the pair adds one Request, one
window and one Record row, with no new compression. A 4,096-bit Operand read
has four request words and 39 result words regardless of bank cardinality.
The window consumes two 1 KiB chunks. Records may cross their boundary.

The fixed sealed image length is already tied to the actual hash invocation,
so this reader needs no separate final-chunk authentication per read. The
general original-file reader still authenticates its final chunk to bind a
witness-supplied length. Its existing declaration order and relations are
preserved. Compression sharing is explicit and requires the same emitter and
row domain.

## Joint proof class

The fixed class retains the original 1 KiB, 32-dispatch-step Program loader,
two constructors, two functions, two blocks per function, three operands per
block and 4,096-bit Nats. Its typed image is 616 words / 9,856 bytes, across ten
chunks with four path levels. This is an independently versioned code-access
component class, with no changes to existing decoder/Exec setup identities.

It declares 61 tables: the existing 44 body/source/hash tables, one code hash
length table, four shared source-access tables and twelve code tables. The
old full-bank read tables have zero invocations. It uses one shared legacy
BLAKE3 compression table for the original hash (17 rows), code hash (164 rows)
and eight chunk authentications (160 rows): **341 compression rows** total.

Seven reads cover Program, Constructor, two Functions, Block, Operand and
Alternative. The first four share one chunk pair; three other pairs serve
the remaining records. Private input is 656 words: original length and buffer
(65), queries (15), eight chunk/path advice groups (576). The externally
expected vector is 123 words: original digest (2), code digest (2), queries
(15), and typed results (30/7/5/5/14/39/4).

Measured geometry is `nu=9`, unchanged Fast128, and exactly `M=26`.

| Kind | Request useful / padded columns | Record useful / padded columns |
| --- | ---: | ---: |
| Program | 5,939 / 2^15 | 18,182 / 2^16 |
| Constructor | 7,895 / 2^15 | 12,414 / 2^16 |
| Function | 7,371 / 2^15 | 11,902 / 2^16 |
| Block | 10,917 / 2^15 | 14,206 / 2^16 |
| Operand | 13,401 / 2^16 | 20,606 / 2^16 |
| Alternative | 11,826 / 2^15 | 11,646 / 2^16 |

Every Request table has 4 input / 5 output words. Record tables take 40
input words and return their record width plus one residual. The window's
two-chunk input size also stays fixed. All residuals are pinned to zero by
the slots, and new witness drivers fully initialize reused padding.

Envelope `IXFCOD00`, revision zero, uses canonical fixed-integer little-endian
bincode, an 8 MiB transport cap and strict trailing-byte rejection. Domain:

`ix:ixby:ixbf-code:bytes1024:steps32:nat4096:c2:f2:b2:o3:v0`.

Fresh verification rebuilds only the setup and consumes the independently
expected vector and proof via stdin. Its working directory is outside the
repository and its environment is cleared. It receives no original source,
native AST, code image, chunk advice or host admission decision.

## Validation

The differential corpus includes all 80 body fixtures, four same-length
String/ByteArray payload variants and a final-chunk read fixture (85 total).
Expected images are independently encoded from native-checked records, hashed
by native BLAKE3, and authenticated using
native chunk/path advice. The joint circuit derives its own records directly
from original bytes under one generic shape. The equal-length payload pairs
have identical typed descriptors and different original/code digests.

Local relation tests compare Boolean plans with separate integer evaluation,
mutate full-width addresses, controls, every output bit, padding and recycled
witness buffers. Cache tests accept repeated reads and reject different roots,
valid but swapped chunk handles, missing physical records and altered chunk
or sibling data, including disabled reads. Large-layout censuses keep counting
lazy and compare emitted schemas/matrices without allocating a code bank.
The minimum 1,008-byte access-only layout uses no path levels, reads through
the true final byte, checks single-chunk ROOT flags and rejects nonzero hash
padding. The ten-chunk class also exercises partial final chunks and promoted
subtrees.

The read-only censuses below do not allocate, seal or admit the listed images.
They establish address/path geometry, not full-image prover cost:

| C / F / B / O (NatBits = 4096) | Image bytes | Path levels | Compression calls per fresh pair |
| --- | ---: | ---: | ---: |
| 0 / 1 / 1 / 1 | 1,504 | 1 | 34 |
| 2 / 2 / 2 / 3 | 9,856 | 4 | 40 |
| 4 / 1024 / 128 / 4 | 390,153,216 | 19 | 70 |
| 4 / u32-max / 1 / 4 | 13,125,420,054,544 | 34 | 100 |

These padded layouts illustrate why access cost and full-image loading cost
must be measured separately. They are not selected Init capacities.

The proof harness also recomputes locally valid rows for substitutions at
Request, Record, source window, block, path and BLAKE3 compression boundaries.
Unused window bytes and a non-final chunk's supplied file length preserve
every local output, exercising input wiring even where local results agree.

All **41 honest serialized proofs** verified in fresh child processes under
the same setup. Each envelope is **523,548 bytes**, excluding the externally
expected vector. All **eleven recomputed substitutions** were rejected by the
fresh verifier at **Wiring**:

| Boundary | Locally recomputed substitution |
| --- | --- |
| Request | Function index 1 to 0, within the same chunk pair |
| Record | Returned Nat magnitude |
| Source window | Authenticated byte outside the requested record |
| Source block | File length with identical local compression parameters |
| Source path | Sibling CV |
| Code seal compression | Schema byte, embedded original digest, actual Nat payload word |
| Chunk/path compression | Counter, CHUNK_END flag, ROOT flag |

Each altered row was checked against its real local R1CS before proving.
The verifier also rejected changed independently expected digests, query groups
and typed results; the old body transcript/envelope; revision and proof-bit
changes; trailing bytes, truncation and the wrong public-vector size.

On 2026-09-15 all six ordinary code tests passed, including 85 joint source/image
differentials. All 256 ordinary workspace tests passed (43 opt-in), as did
formatting and release workspace/all-target Clippy with warnings denied.
The proof/attack/envelope suite took 651.56 seconds test time, 652.46 seconds
wall time and 12,732,980 KiB maximum RSS. The workspace run took 238.08 seconds
test time, 238.77 seconds wall time and 18,778,224 KiB maximum RSS. Both runs
used four Rayon workers and a 32 GiB virtual-address limit. They overlapped,
so these timings are regression evidence rather than a dedicated execution
benchmark. Logs are retained at
`/tmp/ixby-code-{proofs,workspace}-final.{log,time}`.

```sh
ulimit -c 0
ulimit -v 33554432
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::code:: \
  -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::code:: \
  -- --ignored --test-threads=1 --nocapture
```

## Remaining work

The [transport-value seal](IxbyFunctionalValueAccess.md) now retains and connects
the code's actual registry when committing typed Input/Output values. Their
authenticated node/child/root reads also reuse chunk handles.

The bounded seal and record-sized access construction must be extended to
full-image loading and connected to actual execution consumers. Streaming
original-source admission, authentication for execution allocations, locals
and continuations, the approved original-wire execution class and raw-file/Exec
commitment bridge remain required. Representative execution segments must be measured
before selecting full-workload capacities. VM-derived global fuel, complete
segments, sound composition, a pinned Init benchmark and native refinement
remain separate work. See the [scaling plan](IxbyStage3ScalePlan.md).
