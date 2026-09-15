# Source-bound typed input and output values

`flock-stage3/host/src/ixby/ixbf_decode/values/` constructs bounded typed
IXFI/IXFO forests from actual original-wire dispatcher events. Constructor
identities and partial-application arities resolve against the same completed,
[instruction-checked program registry](IxbyFunctionalReferences.md) that
supplies the transport's limits and entry arity.

The component preserves scalar values and payload ranges, derives parentage,
child order, depth and complete subtree spans, and supplies constrained node,
child and root reads. It completes bounded transport value materialization.
The [typed body layer](IxbyFunctionalBodies.md) now materializes bounded
executable records from the same Program events. The
[authenticated value-access layer](IxbyFunctionalValueAccess.md) now seals
these actual records and reads them through reusable chunks. Full-image loading,
the raw-file/Exec commitment bridge, native refinement and a full Init execution
proof remain in the [scaling plan](IxbyStage3ScalePlan.md).

## Source and program binding

`ValueArenaSlots::initialize` accepts a `CheckedProgramReferences`, not a free
metadata vector or bank. The private state retains that object's actual bank
wires and initializes the transport dispatcher from its actual context. Setup
owns the transport kind, registry capacity, node/depth capacity and Nat width.
Program, Input and Output are not interchangeable proof-selected modes.

Every step calls the real dispatcher and then emits three rows:

1. **Link** matches a constructor's complete 512-bit identity to exactly one
   live constructor and checks its field count. A PAP selects a live function
   by its full index and requires fewer captured values than its arity.
2. **Node** assembles the actual event, checked scalar payload and carried
   scalar prefix into one complete raw record. Its index comes from the
   actual grammar's node count. A constructor/PAP/erased prefix completes
   immediately; a scalar completes after its fixed value or full payload.
3. **Capture** inserts that actual record at the next exact preorder index.
   The carried bank must have a contiguous live prefix. Empty packets and
   absent cells are canonical zero, and inactive steps carry the entire bank.

Scalar carry contains pending status, original value-prefix start, subtype,
and the transport body start captured from the real header. Intermediate
UTF-8 steps preserve it without emitting extra nodes. Empty String/ByteArray
values complete on their zero-length count. Nat records take all magnitude
limbs directly from the actual `NaturalDecodeGate`. Fixed scalars and payload
ranges likewise use actual dispatcher outputs.

The caller must authenticate the dispatcher's exact cursor/take requests to
one externally expected transport. ByteArray contents remain in that source;
their typed descriptor is an exact range, not a copied buffer or an unchecked
digest. The proof class below supplies complete source binding for both files.

## Canonical records and tree derivation

For `W = max(1, ceil(nat_bits / 128))`, a raw record has `R = 8 + W` words:

| Offset | Meaning |
| ---: | --- |
| 0 | Boolean presence |
| 1 | Original Value kind: scalar 0, constructor 1, PAP 2, erased 3 |
| 2 | Original scalar subtype 0–6; zero for other kinds |
| 3 | Resolved constructor/function index; zero for scalar/erased |
| 4 | Immediate child count |
| 5 | Own encoding `(start, end)` in u64 lanes |
| 6 | Scalar payload `(start, length)` in u64 lanes |
| 7 | Fixed Bool/Word32/Goldilocks/extension value |
| 8… | Exact little-endian 128-bit Nat magnitude limbs |

A constructor's index resolves its complete identity through the checked
program bank. Its own encoding span covers the constructor prefix and count;
children have their own records. A scalar's own span includes its complete
encoding, starting with the Value tag. Payload descriptors are used only for
Nat, String and ByteArray; other payloads and unused scalar words are zero.
Bool, Word32, both Goldilocks lanes, and the admitted Nat high bits are checked.

Completion consumes the actual final grammar, scalar carry and captured bank.
It requires Done/EOF, exhausted obligations, no unfinished scalar, exact node
count and a live prefix. Own spans partition the entire body without gaps or
overlap: first start equals the captured header end, adjacent spans meet,
and the last end equals EOF. An empty input has body start equal to EOF.

For each live node, a bounded scan starts with one pending node. Consuming a
preorder record subtracts one and adds its child count. The first zero is the
exclusive subtree end. All scans must finish; additions/subtractions are
checked. With at most eight nodes and checked child counts at most eight,
eight-bit internal counters are sufficient. External counts and indices are
still checked at their full 128-bit width.

Earlier subtrees containing a node determine its ancestors. The nearest one
is its parent; their count determines depth. Counting earlier records with
the same parent determines sibling/root ordinal. Explicit child counts and
root counts must agree with the resulting forest. Input root count equals
the actual entry-function arity; Output has exactly one root. Setup's maximum
depth is enforced independently of the original program's semantic limits.
There is no prover-supplied stack, parent map, traversal schedule or tree shape.

Each finished record appends five words: parent index plus one (zero for
roots), sibling/root ordinal, exclusive subtree-end index, depth (roots are
one), and complete subtree `(start, end)`. Completion also emits node count,
root count and maximum depth; all three are zero for an empty input.

Only completion constructs `FinishedValueArena`. Node, child and root reads
consume its actual immutable bank. An enabled request selects exactly one
live record by full-width index or parent/ordinal and returns its index and
entire finished record. Disabled requests/results and absent records are zero.

## Tables and experimental proof class

The component accepts physical capacities of one through eight nodes, depth
one through node capacity, and the existing zero-through-4096-bit Nat range.
It does not raise an existing Exec limit. Count-only emission remains lazy.
The dense bank and quadratic completion scans are a small-class construction;
raising these constants is not a scalable memory design.

At four nodes, depth four, 4096 Nat bits and registry `(C,F,B)=(2,2,2)`:

| Table | Input words | Output words, including residual | Inner `k_log` |
| --- | ---: | ---: | ---: |
| Link | 55 | 2 | 17 |
| Node | 83 | 46 | 17 |
| Capture | 202 | 162 | 19 |
| Finish | 193 | 184 | 19 |
| ReadNode / ReadChild / ReadRoot | 183 each | 47 each | 19 |

Each residual connects to verifier-owned zero distinct from input constants.
All old state, source, program-bank and event words remain circuit inputs,
including words that do not affect a particular local output.

The test proof class has separate approved Input and Output setups. Both
parse a 1 KiB program with complete registry/reference checks and a 1 KiB
transport, using 32 dispatcher steps per file and outer `nu=7`. One shared
hash component hashes the two buffers once each (34 compression rows total).
There are 69 tables, 137 private words and 208 expected public words:

| Public offsets | Expected data |
| --- | --- |
| 0–1 | Original program digest |
| 2–29 | Complete final Program grammar |
| 30–31 | Original transport digest |
| 32–59 | Complete final transport grammar |
| 60–62 | Node/root/depth summary |
| 63–69 | Independently specified node, child and root queries |
| 70–207 | Three selected indices and complete finished records |

The verifier does not receive a private bank or run a host decoder to decide
admission. These raw digests are not the Exec commitment chain.

Envelope `IXFVAL00`, revision zero, uses canonical fixed-integer little-endian
encoding, rejects trailing bytes and has an 8 MiB transport cap. Domain is
`ix:ixby:ixbf-values:input:bytes1024:steps32:nat4096:c2:f2:b2:n4:d4:v0`
or its `output` counterpart, selected by the externally approved setup.
The proof cannot choose its own transport kind. Existing Exec setups, old
component envelopes, pinned Flock revision, legacy BLAKE3 and Fast128 settings
remain unchanged. This new component class measures `M=26`.

## Verification

Independent fixture encoding records expected scalar values, original ranges
and preorder relationships. The native IXBF loader and complete IXFI/IXFO
decoder agree on every honest fixture and exactly re-encode both files.
The actual circuit reproduces those expected forests under one setup per kind.
Fixtures include every Value kind and all seven scalar types, Nat zero and
4096-bit magnitudes, empty strings/bytes, split UTF-8, an 800-byte ByteArray,
nested PAP/constructor values, depth four, reordered constructor identities,
nonzero program entry, and empty/multiple input roots.

Whole-circuit rejection tests cover undeclared constructor identities, wrong
constructor child counts, saturated/oversaturated PAPs, capacity overflow and
input arity disagreement with the actual program. Separate grammar and native
oracles distinguish malformed values from valid values outside the physical
class. Unit tests compare every table with independent checked-integer witness
preparation, including full-width controls/carry, all 512 identity bits, bad
topology/spans/depth, Nat boundaries, missing reads and disabled advice.
All output bits, unused columns, recycled padding and lazy shape counts are
checked against the real R1CS.

The opt-in test proves 32 honest fixtures and attempts ten recomputed
substitutions. Each verifier runs in a fresh, environment-cleared process
outside the worktree, receiving only the approved kind, expected public words
and proof. It reconstructs the setup and runs no native loader, parser, hash
oracle or semantic predicate. Complete serialized proofs measure 488,036 bytes,
excluding the external public statement.

The substitutions target a constructor identity and matching bank entry,
unused program-bank data, actual Nat magnitude, carried scalar-prefix start,
unused transport context, a carried captured value, a final arena value,
a node read address, selected tree metadata, and an unused source-buffer byte.
Changed rows recompute locally valid outputs before proving; value-row attacks
also check the actual local R1CS. Several preserve all local outputs. The
fresh verifier rejects all ten proofs at `Wiring`. Changed expected sources,
grammars, summaries, queries/results, transport kind, old domain/envelope,
proof bytes, truncation and trailing bytes also reject.

The 2026-09-15 workspace run passes all 244 ordinary tests (41 opt-in).
Formatting and release Clippy on all targets also pass with warnings denied.
The AST-free parser differential passes all 81 compiler-corpus programs and
the exact retained 1,002,355-byte Init image, 9,611,120-byte input and 49-byte
output. This is a parser regression, separate from the bounded value proofs.

The proof regression passes in 540.47 seconds in the test body, 541.32 seconds
wall, with 10,463,728 KiB maximum RSS. The workspace run takes 230.21 seconds
wall with 16,902,272 KiB maximum RSS;
the retained-artifact differential takes 176.88 seconds with 602,984 KiB.
Both overlap the proof regression, use four Rayon workers and retain the
32 GiB virtual-address cap. These are per-command regression measurements,
not isolated single-proof costs or estimates for proving Init. Logs and timing
files are retained under `/tmp/ixby-values-*-final.{log,time}`.

```sh
ulimit -c 0
ulimit -v 33554432
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::values:: \
  -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::values:: \
  -- --ignored --test-threads=1 --nocapture
```

The full Init transports still require larger-file authentication connected
to a scalable checked program representation. A typed ByteArray range in this
bounded class does not admit the 9,611,120-byte Init input or prove its execution.
The [typed body layer](IxbyFunctionalBodies.md) completes bounded executable
records from the same checked Program. [Authenticated typed code reads](IxbyFunctionalCode.md)
now consume a digest of those actual records through reusable chunk handles.
[Authenticated transport-value access](IxbyFunctionalValueAccess.md) now seals
the actual completed arena with its code and original transport digests, then
reads nodes/children/roots through reusable chunks. Execution allocations,
local/continuation memory and execution consumers remain required.
Streaming witnesses, complete state segments with VM-derived
global fuel, sound composition, a pinned Init proof
and terminal compression remain separate work.
