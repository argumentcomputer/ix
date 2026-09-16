# Source admission for paged execution

The paged execution memory now has constrained original-byte loading,
source-bound code capture, complete program reference checks and full
constructor-ID uniqueness, typed input materialization and initialization
constraints. Their proof chains now have
[recursive composition with output binding and execution](IxbyFlockRecursion.md#complete-paged-execution-aggregation),
validated by a complete original-format identity proof and fresh receiver.
The full CSLib execution proof remains to be generated.

## Original byte banks

[`source_bytes`](../flock-stage3/host/src/ixby/ixbf_decode/paged/source_bytes/mod.rs)
has separate fixed Program and Input setups. Each batch authenticates two
adjacent 1 KiB chunks and the exact final chunk to the same standard unkeyed
BLAKE3 digest. The final chunk binds the claimed length, including empty files.
The setup supports original files through 16 MiB.

The copy gate derives all 64 memory addresses from the chunk cursor and the
setup-owned bank. Its new cell values are the authenticated source words;
every old cell is constrained to zero. A missing second chunk and the bytes
after EOF produce zero cells. The shared memory-tree proof authenticates these
actual old/new cells to both memory roots. There is no host-selected address
list or native acceptance flag in this relation.

The nine public words contain one source identity `[length, digest2]` and two
`[chunk cursor, memory root2]` boundaries. A complete chain starts at cursor
zero and ends after the exact final chunk. Program loading starts at the
fixed empty memory root; Input loading starts at the Program's final root.
The full execution composition must constrain those stage links.

Four real **393,532-byte proofs** verify in fresh processes receiving only
their expected statements and proof bytes. Both Program and Input setups
cover an initial and final batch. Every changed public word and malformed
envelope rejects. Eight locally valid recomputed control, address, live-chunk
and byte substitutions reject at Flock's wiring check. Ordinary tests cover
empty files, exact chunk boundaries, odd chunk counts, EOF padding, full-width
metadata, poisoned row padding and complete native-memory root equality.

The fixed class has 64 leaves, at most 127 internal memory-tree nodes,
`nu=10`, `M=24` and 126,908 dense field words. Source authentication and memory
authentication share their compression table. The four-proof test took
20.30 seconds wall time, with 3,556,596 KiB peak process RSS and four Rayon
threads. This includes setup, fresh verifier processes and adversarial proofs.

## Source-bound packed code

[`code_capture`](../flock-stage3/host/src/ixby/ixbf_decode/paged/code_capture/mod.rs)
consumes the actual constrained Program dispatcher fields. It writes function
declarations, full constructor identities and field counts, block headers,
operands and case alternatives into the execution layout. Function/block
ownership and all write positions derive from the grammar's counters.

Seven capture words carry the current function/block, open flag, partial
header, operand count, pending scalar kind and a 256-bit case-constructor
bitmap. The bitmap rejects duplicate alternatives. A completed header passes
the same physical code checker used by instruction fetch, including primitive
arity and exact operand count. Local operands must reference the block's live
locals. The fixed profile captures Nat128 magnitudes, original String/Bytes
source offsets, canonical fixed scalars and Erased. UTF-8 partial steps and
batch padding preserve pending state without creating extra writes.

The batch authenticates source chunks, runs up to 32 actual parser/capture
steps and proves all generated accesses through the ordered memory log and
shared tree. It carries **all 30 parser words, seven capture words and two
memory-root words** at both boundaries, plus the three source identity words:
81 public words total. Its fixed class has 32 memory leaves, up to 255 parent
nodes, `nu=10`, `M=26` and 495,216 dense field words. Advice stops before any
source-page, step, cell or parent-node quota is exceeded.

Three real **452,899-byte joint proofs** verify in fresh processes. They cover
declarations, wide natural literals and byte payload references. All 81 public
word substitutions and malformed envelopes reject. Four locally valid
recomputed constructor-ID, write-position, Nat-magnitude and payload-range
substitutions reject at Flock's wiring check. Setup took 3.161 seconds; witness
evaluation plus proving took 0.399–0.728 seconds per honest proof with four
Rayon threads. These small batches are not full-execution throughput estimates.

The complete original 1,016,587-byte CSLib program passes **1,227 joint circuit
evaluations**, covering 37,878 parser events. Every intermediate boundary is
equal, the parser reaches EOF/Done, capture state closes, and the final memory
root equals the native packed program including its original bytes. Evaluation
took 51.961 seconds after setup and raw memory loading. Independently, every
captured typed cell equals the native packer's 24,823 typed cells. These are
circuit/differential checks; the complete 1,227-batch chain has not yet been
proved or aggregated.

## Complete program references

[`references`](../flock-stage3/host/src/ixby/ixbf_decode/paged/references/mod.rs)
walks every declared function, block and case alternative in a fixed order,
including unused code. Three carried words contain the traversal position,
cached function declaration and pending case header. Each active row advances
that enumeration; padding preserves the state and issues canonical null reads.
The walk starts at function zero and ends only after the final declared block
and all its alternatives.

Four read ports derive addresses from that state and actual memory replies.
The circuit checks function entry frames, foreign and self-call arities,
strictly undersaturated closures, constructor field counts and all static
successor frames. Case alternatives receive their constructor fields in the
target frame. Every read is authenticated to the same expected memory root.
The source-capture component supplies canonical instruction/operand encoding,
scalar validation, local references and duplicate-alternative rejection.

The 11 public words are `[function count, constructor count, entry, root2]`
plus two three-word traversal boundaries. Composition must bind all context
words to the completed Program parser and the root to completed code capture.
This is a conditional reference checker until those links are proved.

The fixed class has 32 rows, 32 memory leaves, at most 255 parents, `nu=10`,
`M=26` and 295,358 dense field words. Three **335,443-byte proofs** verify in
fresh processes receiving only their expected statements and proof bytes.
Every changed public word and malformed envelope rejects. Five locally valid
recomputed context, traversal, callee, successor and alternative substitutions
reject at Flock's wiring check. Setup took 2.539 seconds and honest witness
evaluation plus proving took 0.123–0.390 seconds per batch with four Rayon
threads. The full adversarial/fresh-verifier test took 12.53 seconds wall time
and peaked at 2,011,204 KiB process RSS.

All **994 original CSLib reference circuit batches pass**, covering 9,087
steps: 681 functions, 6,763 blocks and 1,643 alternatives. The memory root
stays unchanged, every boundary links, and the complete traversal reaches its
required endpoint. Circuit evaluation and native advice took 25.059 seconds
after setup. The whole reference chain has not yet been proved and aggregated.

## Full constructor identities

[`constructor_ids`](../flock-stage3/host/src/ixby/ixbf_decode/paged/constructor_ids/mod.rs)
reads both ID cells for each of the 256 physical constructor positions at
fixed addresses. Each identity contains all four field words: the 256-bit
block ID, Nat128 member and Nat128 tag. The declared count determines each
record's active flag; undeclared positions must contain zeros. An active
all-zero ID remains valid.

An exact permutation sorts whole `[active, ID4]` records. A constrained audit
requires an active prefix with strictly increasing 512-bit IDs, followed by
canonical padding. Thus it rejects duplicate identities without relying on
a truncated hash or host uniqueness decision. The shared memory tree binds
all 512 read-only cells to the same expected root. Its three public words are
the declared count and root; composition must bind both to source capture.

The fixed class has 512 leaves, at most 1,023 parents, `nu=12`, `M=28` and
1,172,734 dense field words. Real **298,019-byte proofs** for 256 and zero
declared constructors verify in fresh processes. Changed public statements,
malformed envelopes and four locally valid recomputed count, index, ID and
sorted-record substitutions reject. Every one of the 512 comparison bits is
tested independently; complete circuit tests cover counts 0, 1, 2, 255 and
256, duplicates, undeclared nonzero cells and recycled row padding. The
original program's **146 constructor IDs** also pass the complete circuit.

Setup took 2.728 seconds; honest witness evaluation plus proving took
0.393–0.709 seconds. The full adversarial/fresh-verifier test took 11.17 seconds
wall time and peaked at 2,585,128 KiB process RSS with four Rayon threads.

## Typed input and initialization

[`input_capture`](../flock-stage3/host/src/ixby/ixbf_decode/paged/input_capture/mod.rs)
consumes actual Input dispatcher events. Root values go directly to entry
locals. Every constructor or partial application reserves its field vector
in preorder, writes its value to the current destination, and fills children
in source order. Constructor events match all 512 ID bits and the field count
against authenticated declarations. Partial applications read the actual
function declaration and require fewer captures than its arity.

Five carried words contain the unfilled span, heap count, stack depth, pending
scalar kind and entry-function declaration. The stack stores only nonempty
remaining sibling spans, so a completed value needs at most one pop. Each
pop clears its stack cell. Completion requires an empty span, empty stack and
no unfinished scalar. Field reservations are monotonic, every destination
derives from the parsed forest, and all allocated fields are filled before
initialization completes.

Scalars retain exact Nat128 magnitudes and fixed scalar bits. Bytes and
Strings point to authenticated ranges in the original Input byte bank;
String events additionally complete UTF-8 validation. The component requires
the Program context and initial memory root from the preceding admission
stages, including original byte-bank loading. Its physical bounds are 64
entry arguments/fields/captures, 65,536 input nodes and a 36-bit heap counter.

Each row has six ordered memory accesses: three declaration reads, a stack
read, a stack write/clear and a value write. The batch carries all 30 parser
words, five materialization words and two root words at each endpoint, plus
the source identity: **77 public words**. The fixed 32-row class has 32 leaves,
at most 255 parents, `nu=10`, `M=26` and 493,808 dense field words.

Two real **452,891-byte proofs** verify in fresh processes receiving only
expected statements and proof bytes. All 77 public-word substitutions and
malformed envelopes reject. Seven locally valid recomputed entry-arity,
constructor-ID, allocation, saved-frontier, natural, byte-range and resolved
constructor-index substitutions reject at Flock's wiring check. Setup took
4.326 seconds; honest witness evaluation plus proving took 0.366–0.670 seconds
per batch. The complete adversarial/fresh-verifier test took 18.10 seconds
wall time and peaked at 3,747,496 KiB process RSS with four Rayon threads.

The complete original **4,813,238-byte input** passes one circuit batch with
nine parser events and a **452,891-byte proof** that verifies in a fresh
process. That test took 17.13 seconds, including setup and verification. The
resulting memory root equals the complete native
execution image exactly. The native loader now reserves heap vectors in the
same preorder; nested constructor/PAP execution tests pass with that layout.
Tests also cover all scalar kinds, zero roots, empty objects/captures, 64-field
vectors, nested sibling spans and exact stack cleanup.

[`initialize`](../flock-stage3/host/src/ixby/ixbf_decode/paged/initialize.rs)
derives the three execution parameters, all 24 initial machine words and
clock zero from the actual Program context and completed Input state. It
checks the entry declaration/arity, exhausted frontier, heap count, exact
64-bit fuel budget and semantic limits. Frame copying, continuations,
dynamic-byte allocation and pending execution state start at zero. The
Nat128 execution class requires a semantic Nat limit of at least 128 bits.
The original initial state and parameters match the native loader exactly;
the final recursive composition must consume these initialization wires.

## Output bytes and exact termination

[`output_bytes`](../flock-stage3/host/src/ixby/ixbf_decode/paged/output_bytes/)
checks original `IXFO` results whose value is Bytes. It derives the canonical
header and minimal LEB128 length from the actual result descriptor, checks
exact EOF, and compares every payload window with authenticated execution
memory. Reads may cross both source chunks and memory cells. Empty results
have one checked zero-length window. Other result types require a separate
output profile.

Each fixed batch checks up to 32 consecutive 32-byte windows. The public
statement contains the source length/digest, read-only memory root, complete
result descriptor, and initial/final window indices: **9 words**. Completion
requires index zero through `max(1, ceil(length / 32))`. The first row must
advance; shared source identity, memory, result and every intermediate index
must match across batches. The class uses 40 memory leaves, 255 parents,
`nu=10`, `M=26` and 322,267 dense field words.

Two **351,259-byte proofs** (unaligned multi-chunk data and empty bytes) verify
in fresh processes. All nine expected-word changes and malformed envelopes
reject. Six locally valid recomputed header, result-pointer, window-index,
enabled-row and memory-byte substitutions fail Flock wiring verification.
Setup took 3.366 seconds; witness evaluation plus proving took 0.147–0.395
seconds. The adversarial test took 12.10 seconds wall time and peaked at
2,498,296 KiB process RSS with four Rayon threads.

The original **49-byte output**, containing a **34-byte Bytes result**, also
has a 351,259-byte proof verified in a fresh process. This test supplies the
result memory and descriptor; binding them to the completed original execution
still belongs to the final composition.

[`finalize`](../flock-stage3/host/src/ixby/ixbf_decode/paged/finalize.rs) checks
the actual halted frame, empty pending machine state, exact remaining/consumed
fuel sum, byte-array semantic limit and result range. Program and Input ranges
must lie inside their exact source lengths; dynamic ranges must lie inside
allocated byte cells. It derives the result and consumed steps from those
wires. Like initialization, finalization still needs to be consumed by the
recursive root.

## Original-byte commitment bridge

[`commitment_bridge`](../flock-stage3/host/src/ixby/ixbf_decode/paged/commitment_bridge/)
binds each original file to the existing artifact hash preimage:

```text
"IxBy/commit/v0" || 00 || domain || parentDigest[32] || originalFile
```

Domains 1, 2 and 3 are distinct verifier-owned setups. Each batch authenticates
original source chunks, constructs one complete prefixed chunk from their
actual words, and authenticates it to the expected artifact digest. The
48-byte prefix changes chunk alignment; the relation checks that shift and
both files' final-chunk padding. Both exact lengths are authenticated.
A complete chain covers every prefixed chunk from zero through EOF. Its parent
must be the profile digest for Program and the same Program digest for Input
and Output in the final composition. A raw digest alone cannot establish this
relation.

The bridge publishes **9 words**: raw source length/digest, parent digest,
artifact digest and two chunk indices. Its fixed Boolean-only class has
`nu=10`, `M=22` and 21,383 dense field words. Native source trees can own the
prefixed buffer, avoiding reconstruction for each batch.

Six **282,612-byte proofs**, covering first and final chunks under all three
domains, verify in fresh processes. Six locally valid recomputed length,
index, parent, source-word and final-padding substitutions fail at wiring.
All nine changed expected words and malformed envelopes reject. Warm witness
evaluation plus proving took 0.052–0.304 seconds per batch in that test.

All original bridge circuits pass: **993 Program batches, 4,701 Input batches,
and one Output batch**. Fresh proofs also pass for the first and final batch of
each file (five proofs total). These are circuit checks for all batches and
proofs for the boundaries, not yet an aggregated proof of the three complete
chains. The fixture's profile-parent digest is conditional; the final root
must supply and bind the approved profile.

## Proof interfaces and remaining work

`CompiledSourceBytes`, `CompiledCodeCapture`, `CompiledReferences`,
`CompiledConstructorIds`, `CompiledInputCapture`, `CompiledOutputBytes` and
`CompiledCommitmentBridge` expose fixed compilation,
proving, verification and verified child-replay inputs. Setup is compiled
before examining any source, statement, advice or proof. Replay objects are
native witness material; recursive composition must constrain the complete
child verifier and its inherited claims. Compilation also compares every
prover driver's matrices and wire schema with the compiled verifier registry.

The implemented final relation composes the admission, execution, output and
commitment chains, consumes initialization/finalization constraints, and binds
the approved profile, all source identities, memory/state boundaries and final
Exec statement digest. The original-format identity fixture has a complete
499,347-byte proof. Full CSLib execution proof generation remains.

## Reproduction

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  ixby::ixbf_decode::paged:: -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  source_bytes_prove_fresh_and_reject_recomputed_copies \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  code_capture_proves_fresh_and_rejects_recomputed_events \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  references_prove_fresh_and_reject_recomputed_reads \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  constructor_ids_prove_fresh_and_reject_recomputed_ids \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  input_capture_proves_fresh_and_rejects_recomputed_values \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  output_bytes_prove_fresh_and_reject_recomputed_ranges \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  bridges_prove_fresh_and_reject_recomputed_prefixes \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_program_all_code_batches_match_native_packing \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_program_all_reference_batches \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_program_all_constructor_ids \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_input_materializes_the_exact_initial_execution_image \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi \
IXBY_PAGED_OUTPUT=/path/to/expected.ixbo \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_artifacts_complete_commitment_bridge_circuits \
  -- --ignored --nocapture --test-threads=1
```
