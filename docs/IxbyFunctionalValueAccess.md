# Authenticated typed transport values

> Current contract: [runtime revision 2](CompilatrixRuntimeV2Handoff.md), with format-1/semantics-2 headers, 58 opcodes, and five wire-value kinds. This report preserves component milestone measurements and their original setup identities; its remaining-work sections describe that milestone. Current complete admission and execution are documented in [paged execution](IxbyFlockPagedExecution.md).

`flock-stage3/host/src/ixby/ixbf_decode/values/access/` commits the actual
completed Input or Output arena and reads individual records through reusable
BLAKE3 chunk handles. A node, child or root read carries one record-sized
window instead of a copy of the complete arena.

Sealing uses the existing bounded [value loader](IxbyFunctionalValues.md) and
[typed code seal](IxbyFunctionalCode.md). This component does not load full
Init artifacts, allocate mutable execution memory, or execute the program.

## Source, code and tree binding

`ValueCommitSlots::seal` accepts a privately constructed `FinishedValueArena`
and an actual `SealedCode`. The arena retains the completed program reference
object that initialized its dispatcher and resolved its constructors and PAPs.
The seal connects that object's entire registry and final Program grammar to
the corresponding actual wires retained by the code seal. Constructor indices,
function arities and transport limits therefore refer to the committed code's
registry. There is no production constructor accepting an independent value
root or a free code registry.

The caller supplies the **actual original transport digest used to authenticate
the arena's source reads**. This is the same explicit composition requirement
as the earlier value/body loaders and code seal. String and ByteArray records
retain original byte ranges; the embedded transport digest binds those ranges
to their payload bytes. An execution consumer must authenticate payload reads
against this digest.

The joint proof hashes each original file once and wires those exact outputs
into the code and value seals. Existing loader relations and their setup
identities are unchanged; their private wrapper objects now retain the program
binding needed by this composition.

## Canonical image

Words are 16 bytes: low u64 followed by high u64, each little-endian. Standard
unkeyed BLAKE3 commits precisely the fixed image length. Any padding in the last
64-byte compression buffer is zero and excluded from that length.

| Region | Words | Contents |
| --- | ---: | --- |
| Schema | 5 | `IxBy/values/v0` padded to 16 bytes; transport kind, node capacity, maximum tree depth, Nat-bit capacity |
| Manifest | 35 | Actual code digest (2), original transport digest (2), final transport grammar (28), node/root/depth summary (3) |
| Arena | `N*(13+W)` | Actual completed preorder nodes, including derived tree metadata |

Here `W = max(1, ceil(NatBits/128))`. Transport kind is setup-owned: Input is
one and Output is two. Node fields retain the representation specified by the
[value loader](IxbyFunctionalValues.md): presence, value/scalar kind, resolved
reference, child count, own span, scalar payload range, fixed scalar, Nat limbs,
then parent-plus-one, ordinal, subtree end index, depth and complete subtree
span. Absent physical records are canonical zero.

`ValueLayout` admits one through u32-max nodes, tree depth one through node
capacity, and the existing zero-through-4096-bit Nat capacity. The largest
image is 3,092,376,453,040 bytes, so its size and offsets fit u64. Large layouts
permit address/path components only. Actual sealing remains bounded to the
existing one-through-eight-node arena loader.

## Reads and untrusted locators

Four setup-owned kinds have separate Request and Record tables:

| Kind | Query `(enabled, node/parent, ordinal, locator)` | Result |
| --- | --- | --- |
| Manifest | `(enabled, 0, 0, 0)` | Zero index and the 35-word manifest |
| Node | `(enabled, node, 0, 0)` | Requested physical index and complete node |
| Child | `(enabled, parent, ordinal, locator)` | Located physical index and complete child |
| Root | `(enabled, 0, ordinal, locator)` | Located physical index and complete root |

Locators are untrusted physical-node hints. Request bounds all full 128-bit
query words, requires unused/disabled words to be zero, and derives the exact
record address, width and chunk pair. Record consumes that actual authenticated
window, checks presence, and requires its derived parent and ordinal to equal
the logical child/root request. The completed arena already guarantees unique
parent/ordinal assignments. A different live node with a valid Merkle path
cannot substitute for the requested child or root.

Both chunk handles retain actual root, index, layout and byte wires. Every
read connects both roots and both indices to its sealed arena and request,
including disabled reads. Source-window outputs are connected to the sealed
length and exact requested indices. Disabled results and unused window words
are zero. Manifest reads require the completed phase. Every local residual is
pinned to verifier-owned zero, and witness drivers initialize recycled padding.

Each newly authenticated pair costs `2*(16+depth)` compression invocations.
Another read using the same pair adds only Request, window and Record rows.
A 4096-bit node has 45 record words regardless of arena capacity; the read
returns that record plus its index. Payload bytes remain in the original file.

## Joint proof class

Separate approved Input/Output classes parse a 1 KiB original Program and a
1 KiB transport, with 32 dispatcher steps per file. Code capacity is
`C=2, F=2, B=2, O=3`; value capacity is four nodes, depth four and 4096 Nat bits.
The code image is 9,856 bytes; the value image is 220 words / 3,520 bytes,
spanning four chunks and two path levels.

There are 90 tables. The old full-bank body and value read tables have zero
invocations. One shared legacy BLAKE3 compression table handles both original
hashes (34 rows), the code seal (164), the value seal (59), and six authenticated
chunks (108): **365 compression rows**. The Manifest and first Root reads reuse
one pair; Node and Child reads each authenticate a further pair.

The setup uses `nu=9`, unchanged Fast128 and exactly `M=27`. Its private input
is 547 words: two original lengths/buffers (130), logical queries (7), locators
(2), and six chunk/path proofs (408). The expected public vector is 189 words:
original Program, code, transport and value digests (8); logical queries (7);
Manifest result (36); and three index-plus-node results (138).

| Kind | Request useful / padded columns | Record useful / padded columns |
| --- | ---: | ---: |
| Manifest | 3,614 / 2^15 | 22,049 / 2^16 |
| Node | 6,231 / 2^15 | 25,244 / 2^16 |
| Child | 7,261 / 2^15 | 27,052 / 2^16 |
| Root | 6,746 / 2^15 | 26,021 / 2^16 |

Request has four input/five output words. Record has 49 input words and
37 Manifest or 47 node output words, including its residual. The two-chunk
window size stays fixed as the arena grows.

Envelope `IXFVAC00`, revision zero, uses canonical fixed-integer little-endian
bincode, strict trailing-byte rejection and an 8 MiB cap. The approved kind
selects the domain, never private proof advice:

`ix:ixby:ixbf-value-access:input:bytes1024:steps32:nat4096:c2:f2:b2:o3:n4:d4:v0`

or its `output` counterpart. Fresh verification rebuilds the setup outside the
repository, clears the environment, and receives only approved kind, expected
public words and proof. It has no original bytes, native AST, image, locator,
chunk advice or host admission oracle.

## Validation

The 44-fixture differential corpus covers all four Value kinds, all seven
scalar kinds, 4096-bit Nats, split UTF-8, 800-byte ByteArrays, empty payloads,
nested PAP/constructor trees, depth four, reordered constructor identities,
empty input and multiple roots. Eight equal-length String/ByteArray variants
have identical typed records and different source/value digests. Four code
variants have identical transport bytes and records but different code/value
digests. Expected code and value images are independently serialized from
native-checked records; the circuit derives its own records from original
bytes under a single generic shape per transport kind.

Ordinary tests compare separate Boolean and checked-integer implementations,
mutate full-width queries and every output bit, and check absent nodes,
parent/ordinal mismatches, disabled advice and recycled padding. Cache tests
reject other roots, swapped valid handles, modified bytes/siblings, and valid
authenticated nodes supplied as incorrect locators. They also read a nonzero
parent's child and the second root of a forest. Cross-program seal tests
reject different unused constructor identities, constructor ordering,
function arities and transport context; each alternate program accepts the
same transport when it also supplies the code.

The 864-byte single-chunk access regression reads through the actual final
byte, checks 32-byte CHUNK_END|ROOT compression and rejects nonzero padding.
The four-chunk joint class covers straddling records and its partial final
chunk. Read-only censuses exercise the last physical address without allocating
or sealing the listed images:

| Nodes (NatBits = 4096) | Image bytes | Path levels | Compression calls per fresh pair |
| ---: | ---: | ---: | ---: |
| 1 | 1,360 | 1 | 34 |
| 4 | 3,520 | 2 | 36 |
| 1,000,000 | 720,000,640 | 20 | 72 |
| u32-max | 3,092,376,453,040 | 32 | 96 |

The opt-in suite proves every honest fixture and constructs 19 locally valid
substitutions at Request, Record, source window/block/path and compression
boundaries. Attacked rows recompute outputs and satisfy the real local R1CS
before proving. Parent/ordinal Request changes and unused window/length changes
preserve all local outputs, testing the input wiring directly. Envelope and
expected-statement mutations cover all digests, queries, result kinds,
transport setup, old domains/envelopes, revision, proof bytes, size and EOF.

On 2026-09-15 all 44 honest serialized proofs verified in fresh processes,
each 536,460 bytes, and all 19 recomputed substitutions failed at Wiring.
The complete proof regression, including envelope and expected-statement
mutations, passed in 1,111.67 seconds test time and 1,113.13 seconds wall time,
with 16,827,720 KiB maximum RSS. Logs and timing are retained under
`/tmp/ixby-value-access-proofs-final.{log,time}`.

On 2026-09-15 all 263 ordinary workspace tests passed (44 opt-in), including
the seven new access tests. Formatting and release workspace/all-target Clippy
with warnings denied passed. The workspace run took 254.04 seconds test time,
255.03 seconds wall time and 19,804,748 KiB maximum RSS. It overlapped the proof
regression, using four Rayon workers and the existing 32 GiB virtual-address
limit. These measurements are regression evidence, not an execution benchmark.
Logs and timing are retained under
`/tmp/ixby-value-access-workspace-final.{log,time}`.

```sh
ulimit -c 0
ulimit -v 33554432
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::values::access:: \
  -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::values::access:: \
  -- --ignored --test-threads=1 --nocapture
```

## Remaining work

The sealed arenas are immutable transport values. Execution allocations,
locals, continuations and state boundaries still need authentication, and
full-image loading needs streaming original-source admission. These reads
must be connected to the approved original-wire execution class and the
raw-file/Exec commitment bridge. Streaming witnesses, measured representative
execution segments, VM-derived global fuel, sound composition, a pinned full
Stage 2 workload proof and native refinement remain in the
[scaling plan](IxbyStage3ScalePlan.md).
