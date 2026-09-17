# Source-bound typed executable bodies

> Current contract: [runtime revision 2](CompilatrixRuntimeV2Handoff.md), with format-1/semantics-2 headers, 58 opcodes, and five wire-value kinds. This report preserves component milestone measurements and their original setup identities; its remaining-work sections describe that milestone. Current complete admission and execution are documented in [paged execution](IxbyFlockPagedExecution.md).

`flock-stage3/host/src/ixby/ixbf_decode/bodies/` materializes complete typed
original-wire IXBF function and block bodies. Every operand, scalar payload,
operation, callee, projection, successor and constructor alternative comes
from the actual [instruction-checked Program parser](IxbyFunctionalReferences.md).
Constrained reads consume only the privately constructed finished body bank.

This completes bounded executable-body materialization. It does not execute
those bodies, admit the full Init artifacts, or establish the raw-file/Exec
commitment bridge. Those obligations remain in the
[scaling plan](IxbyStage3ScalePlan.md).

## Event coverage and source binding

`ProgramBodySlots` owns the original `ProgramReferenceSlots` and its private
state. Initialization and each step use the genuine dispatcher. Completion
checks the actual final grammar and declaration registry, performs all existing
instruction/reference checks, and assembles **every retained actual event**.
Neither a host AST nor an advised list of block boundaries selects rows.

Two body rows follow each event:

1. **Step** starts a record on the actual Block-header event. Owner and block
   index derive from full-width grammar counters. Body events must preserve
   that identity and continue the previous byte span. Operation tags, primitive
   tags, counts, references, fields and successors come from actual decoder
   outputs. Each completed operand inserts at the exact carried ordinal;
   alternatives use the actual remaining-alternative count. Completion occurs
   only on an actual committed transition to Block, Function or Done. It emits
   the complete owned record and clears the current state.
2. **Capture** inserts that packet at its exact function/block address, requiring
   an absent destination. Earlier blocks of the same function must already be
   present and their source spans must meet. Inactive packets and absent cells
   are canonical zero; every other bank word is carried through constrained
   wires.

Scalar assembly preserves the operand-prefix start and scalar subtype. Fixed
scalars take the actual decoded value; Nat takes every actual magnitude limb;
String and ByteArray take the checked payload range. Intermediate uncommitted
UTF-8 events retain the current scalar and emit no operand. Empty String and
ByteArray complete on their zero count. Apply's closure is operand zero, before
the separately counted arguments.

**Finish** consumes the actual final Program grammar, unfinished state,
completed declaration registry and captured bodies. It requires Done/EOF,
exhausted obligations, empty current state, exact function/block coverage,
header equality, ordered complete block spans and contiguous function spans
ending at EOF. It checks canonical instruction fields, exact operand counts,
all 58 functional primitive arities, ordered operand/alternative prefixes, local
and target bounds, unique alternatives, scalar canonicality and Nat high bits.
Existing reference checks supply constructor/callee arities and successor frames.

The caller must authenticate every dispatch request to one externally expected
original file. The test class below hashes one shared buffer once and connects
every source-window read to that buffer. Payload bytes remain in that source;
a typed range is a descriptor, not an unverified copy or a standalone digest.

## Records and immutable consumers

All words are 128 bits. Metadata and lookup indices retain that full width;
source spans and payload ranges pack two u64 lanes. For
`W = max(1, ceil(nat_bits / 128))`, an operand has `7 + W` words:

| Offset | Meaning |
| ---: | --- |
| 0 | Boolean presence |
| 1 | Original kind: local 0, literal 1, erased 2 |
| 2 | Local index; zero for other kinds |
| 3 | Scalar subtype 0–6; zero for non-literals |
| 4 | Complete operand encoding `(start, end)` |
| 5 | Nat/String/ByteArray payload `(start, length)`; otherwise zero |
| 6 | Fixed Bool/Word32/Goldilocks/extension value; otherwise zero |
| 7… | Exact little-endian 128-bit Nat magnitude limbs; otherwise zero |

Each block has a 14-word header, followed by `O` operand cells and `C`
four-word alternative cells. The header is:

| Offset | Meaning |
| ---: | --- |
| 0–2 | Presence, local-frame size, original instruction tag |
| 3–6 | Operation tag, primitive opcode, constructor/direct-callee index, projection field |
| 7–8 | Argument count excluding an Apply closure; complete operand count including it |
| 9–11 | First successor, second successor, alternative count |
| 12–13 | Full block encoding `(start, end)`; block-header end |

Unused fields are zero. Each alternative stores presence, constructor index,
owned target block index and its own source span. Each finished function stores
presence, arity, entry block, exact block count and the full function span.
The original instruction byte is immediately before the block-header end.

`function`, `block`, `operand` and `alternative` accept only a
`FinishedProgramBodies` constructed by successful completion. Reads select
exactly one live record using full-width owner/index/ordinal matches. Disabled
requests require zero addresses and produce zero results; unused request fields
are zero. No public constructor
accepts a caller-supplied bank. `references()` exposes the same checked Program
object for the [transport-value arena](IxbyFunctionalValues.md).

## Explicit bounded proof class

Setup owns registry `(C,F,B)=(2,2,2)`, three operands per block, 4,096-bit Nat,
1,024 original program bytes and 32 dispatcher steps. The API allows one to
four operands and at most eight physical blocks, within the existing registry
bounds. These are component capacities, not changes to the functional format
or the existing Exec profile.

There are 44 tables: the existing 37 source/hash/dispatcher/registry/reference
tables and seven body tables. Every source event emits one Step and one Capture
row; Finish and each typed read occur once. The shared BLAKE3 component emits
17 compression rows. The private assignment has 78 words: length, 64 packed
source words and 13 read-query words. The independently expected public vector
has 105 words: original digest (2), complete final grammar (28), queries (13),
and function/block/operand/alternative results (5/14/39/4).

The measured union uses `nu=7`, Fast128 and `M=26`. Body table sizes are:

| Table | Input words | Output words including residual | Useful Boolean columns | Padded columns |
| --- | ---: | ---: | ---: | ---: |
| Step | 223 | 286 | 218,344 | 2^18 |
| Capture | 697 | 557 | 395,355 | 2^19 |
| Finish | 768 | 567 | 554,901 | 2^20 |
| ReadFunction | 570 | 6 | 150,853 | 2^19 |
| ReadBlock | 570 | 15 | 159,456 | 2^19 |
| ReadOperand | 570 | 40 | 287,757 | 2^19 |
| ReadAlternative | 570 | 5 | 163,137 | 2^19 |

Envelope `IXFBOD00`, revision zero, uses canonical fixed-integer little-endian
encoding, an 8 MiB transport cap and strict trailing-byte rejection. Domain:

`ix:ixby:ixbf-bodies:bytes1024:steps32:nat4096:c2:f2:b2:o3:v0`.

Fresh verifier children clear their environment, run outside the worktree and
receive only expected public words and serialized proof. They reconstruct the
approved setup without a native parser, source artifact, AST or body bank.

## Verification evidence

Eighty independently encoded original-wire fixtures pass the native decoder
and exact re-encoding. A separate walk of native instructions encodes each
complete block and constructs its expected typed records and spans. The circuit
uses one source-independent shape for all fixtures, and every finished bank
equals that independent result. The integer witness model and Boolean evaluator
also agree on every body row.

Coverage includes all eight instruction forms, all eight operation forms, all
45 primitives and all seven scalar kinds. Cases include nonzero entries,
multiple owners, unreachable code, forward/self/tail calls, ordered mixed
operands and Apply arguments, unique alternatives and their reset between
blocks, split UTF-8, empty payloads, an 800-byte ByteArray, a 4,096-bit Nat,
u128-max projection fields and wide frame metadata.

Ordinary negative checks cover malformed references, arities, successor frames
and duplicate alternatives, plus two native-valid programs exceeding the
physical operand capacity (including a closure plus three Apply arguments).
Table tests compare every input word under low/high-bit substitutions, all
control-byte values, canonical unused fields, ownership/address bounds,
operand/alternative order, source ranges and Nat high bits. R1CS checks bind
every output bit, padded column and recycled witness row. Tests also construct
tables at minimum and maximum capacity corners. Count-only emission matches
the complete shape.

Thirty-six honest serialized proofs verify in fresh processes under the same
setup. Each complete envelope is **487,724 bytes**, excluding the independently
expected statement. Fifteen locally recomputed attacks are rejected at the
Flock wiring check:

| Attacked row | Substitution |
| --- | --- |
| Step | Operation reference; tail callee; owner plus matching grammar owner |
| Step | Nat magnitude; actual next control; carried scalar-prefix start |
| Step | Swapped completed operands; successor target; unused Done metadata |
| Capture | Previously stored bank word during inactive carry |
| Finish | Nat magnitude; complete operand start |
| ReadBlock / ReadOperand | Valid alternate read address; returned payload limb |
| Source window | Unused original-source byte |

Each of the fourteen body-row attacks recomputes its outputs and passes its
local Boolean R1CS before proving. The unused-metadata and source-byte attacks
preserve every local output. Their rejection therefore exercises the complete
source/state/bank/read wiring, not just a failing local validity residual.

Changed expected digests, final grammar, queries and typed results also reject,
as do the earlier reference domain/envelope, changed revision/proof bits,
trailing bytes, truncation and wrong public-vector length.

On 2026-09-15, all 250 ordinary workspace tests passed (42 opt-in), as did
release workspace/all-target Clippy with warnings denied and formatting. The
complete proof/attack/envelope test took 551.32 seconds test time, 552.13 seconds
wall time and 11,178,476 KiB maximum RSS. The workspace suite took 229.56 seconds
wall time and 16,641,640 KiB maximum RSS. These jobs overlapped, used four Rayon
threads and retained the 32 GiB virtual-memory limit; these are regression-run
measurements, not an isolated execution-prover benchmark. Logs are retained at
`/tmp/ixby-bodies-{proofs,workspace}-final.{log,time}`.

Run the focused and opt-in proof suites from the repository root:

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::bodies:: \
  -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::bodies:: \
  -- --ignored --test-threads=1 --nocapture
```

## Remaining work

[Authenticated typed code access](IxbyFunctionalCode.md) now hashes the actual
completed records together with the original digest and supplies reusable
chunk handles for record-sized reads. Full Init still needs streaming
original-source admission, full-image sealing and authenticated execution
memory. The approved original-wire execution class and
raw-file/Exec commitment bridge must connect these typed records to execution.
Streaming witnesses, VM-derived global fuel, complete bounded execution
segments, sound composition and a pinned full-Init benchmark remain. Native
constraint-to-reference refinement and source/image/ABI correspondence are
separate obligations. Terminal compression is later.
