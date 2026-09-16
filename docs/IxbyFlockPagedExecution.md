# Paged execution consumers

These components are part of the full functional Stage 3 implementation in
progress. They do not yet provide an original-CSLib execution proof. The
existing fixed-capacity Exec profiles, statements, and setup keys are unchanged.

## Frames and continuations

[`paged_frame`](../flock-stage3/host/src/ixby/paged_frame/mod.rs) connects frame
transitions to the actual addresses, write flags, and values consumed by the
authenticated memory log. A frame has at most 128 locals, indexed by its
continuation depth, and the physical stack supports 1,024 continuations.
Function and block positions admit 1,024 functions and 256 blocks per function.
The original program's local and continuation limits are checked separately
against full 64-bit limits.

A call saves the caller's function, target, and local count. The caller's
locals remain in its own memory bank. Return pops the authenticated header
and writes the result at the caller's next local position. Over-application
uses a distinct continuation containing the remaining immutable argument
vector. Tail calls retain the current depth.

Entering a function or appending constructor fields copies a previously
resolved vector one cell at a time. The carried state includes its source,
count, position, and destination base. The next instruction cannot start
before the exact copy completes. Copy steps preserve fuel; each logical
Eval, Apply, or Return transition consumes one unit, including terminal
return. Halted padding preserves both state and fuel.

Every batch must bind all five frame words, the remaining/consumed fuel word,
and both memory-root words. Instruction consumers must produce the actual
action wires, and the caller must feed every returned access to the same
ordered memory-log check. The component's standalone proof test publishes its
action sequence explicitly; it does not establish that a program produced it.

## Code and values

[`paged_code`](../flock-stage3/host/src/ixby/paged_code/mod.rs) derives code,
operand, declaration, alternative, and local addresses from the constrained
frame and indices. It rejects high-bit aliases, wrong frame sizes, invalid
opcode/operand combinations, and reads outside the live local prefix. All
accesses are read-only. Unused accesses read the canonical zero cell.

Packed code records preserve functional instruction and primitive tags.
[`paged_value`](../flock-stage3/host/src/ixby/paged_value.rs) checks the new
32-byte physical values: Nat has an immediate 128-bit magnitude; constructor
and PAP values contain an admitted declaration index and a heap field range;
bytes and strings contain a range in an actual byte bank. Scalar field values
are canonical Goldilocks elements. Literals cannot forge constructor/PAP
values. Allocation and source-range authentication remain separate obligations.

| Memory bank | Cell address base | Contents |
| --- | ---: | --- |
| Functions | `1 << 36` | Arity, entry, block count |
| Blocks | `2 << 36` | Headers, operands, alternatives |
| Constructors | `3 << 36` | Full ID, member/tag magnitudes, field count |
| Locals | `4 << 36` | 128 cells per continuation depth |
| Continuations | `5 << 36` | Resume or remaining-arguments record |
| Scratch | `6 << 36` | Resolved operands |
| Heap | `7 << 36` | Immutable field vectors |
| Program bytes | `8 << 36` | Original source bytes |
| Input bytes | `9 << 36` | Original input bytes |
| Dynamic bytes | `10 << 36` | Runtime byte data |

Each cell is 32 bytes. Byte pointers include the five-bit offset within a
cell. All cell addresses fit the approved 40-bit memory depth. Physical
capacities are independent of the semantic limits in the original program.

`PackedProgram::from_artifact` is an untrusted advice generator. Its full
original CSLib census contains 56,592 cells, including the unchanged
1,016,587 source bytes, 681 functions, 6,763 blocks and 15,298 operands. Every
packed block and operand passes the corresponding constrained consumer's row
check. This does not prove source-to-code admission: the streaming parser
still needs to constrain the writes and complete semantic reference checks.

## Native initialization and original execution segments

`NativeImage::load` decodes the original program and input, packs the complete
code image, and places the unchanged input bytes in their own memory bank.
Byte and string values keep exact offsets into those source files. Nested
constructors and partial applications allocate immutable field vectors in
child-before-parent order, then populate the entry function's actual locals.
The entry frame, heap count and execution limits are derived from the decoded
files. This is untrusted witness preparation; its memory root still requires
constrained source admission.

`SparseMemory::from_cells` constructs the native sparse tree by populated
levels. It rejects duplicate and out-of-range addresses. Its roots, openings
and subsequent writes match the existing sequential constructor, including
depth 64 and explicit zero cells. This changes native advice generation only.

The original 1,016,587-byte CSLib program and 4,813,238-byte input load into
207,008 explicit memory cells in 273 milliseconds locally. The first 100
Compact batches pass the actual execution circuit and all boundary equalities:
726 microsteps, 173 logical steps and 45 allocated heap fields. Circuit
evaluation took 8.883 seconds after loading and setup. This is a prefix check,
not a completed run or a proving throughput estimate.

A longer run of 10,000 Compact batches also passes: 84,761 microsteps,
21,687 logical steps, 2,802 heap fields and 68 dynamic-byte cells. Its circuit
evaluation took 797.087 seconds after loading and setup. It checks every
batch boundary and uses the same original program and input.

An actual **419,091-byte proof** of batch 99 verifies in a fresh process
receiving only the expected statement and proof. It covers microsteps
719–726 and logical steps 171–173, starting from the expected memory root
produced by the original prefix. Compact has `M=26` and 354,407 dense field
words; setup took 3.644 seconds and proving 1.542 seconds with four Rayon
threads. All 57 changed expected words, a changed byte-limit lane, malformed
envelopes and two locally valid recomputed state/memory-clock attacks reject.
The prefix before this segment and source admission are not proved by it.

Three ordinary loader tests also cover all scalar kinds, exact byte offsets,
wide natural values, nested constructor/PAP field order, a circuit-checked
identity execution, truncation and physical-capacity rejection. The preceding
byte/hash implementation's complete regression suite passed 311 tests with
61 explicitly ignored proof/external-fixture tests.

## Instruction batches

[`paged_exec`](../flock-stage3/host/src/ixby/paged_exec/mod.rs) now combines
authenticated code fetch, operand resolution into scratch memory, numeric
primitives, copy/return/Bool/Nat control, direct/self/tail calls, constructor
creation/projection/cases, closures, application, byte primitives and BLAKE3,
frame copies, continuation return, and terminal halt. Instruction actions come from the
fetched code and resolved values. The proof does not publish a host-selected
action sequence.

The batch carries 24 state words, including all frame/fuel fields, allocation
counters, instruction header, resolution cursor, and pending immutable copy.
The finite Small, Compact, Objects, Bytes and SharedCompact factories reserve fixed quotas for each
operation. Their rows may be grouped by
operation: an exact permutation of complete state records proves one positive,
unbroken execution chain. Each memory timestamp is derived from that same
row's constrained clock and a fixed ordinal. Inactive rows are canonical zero;
integer clocks cannot wrap. Both memory roots, both full states/clocks and all
three static parameter words are verifier-bound. Those words pack the locals
and continuation limits; the fuel budget; and the Nat-bit and byte-array-byte
limits. Original source admission must derive these exact limits.

A genuine **399,571-byte instruction proof** verifies in a fresh process.
The fixture performs 20 physical transitions and seven logical steps, using
functions 680/671, Nat values above 64 bits, a call, argument copy, return to
the caller and final halt. The class has 74 memory request slots, 24 boundary
cells and 57 expected public words. Its dense witness is 313,833 field words
(`M=26`). Setup took 2.283 seconds and proving 1.343 seconds with four Rayon
threads. This is the Small v2 setup containing the byte tables and limit;
the earlier numeric/call-only v0 snapshot produced 378,667 bytes.

All 57 changed expected words reject. Eight locally valid recomputed attacks
against fetched headers, resolved operands, numeric results, call entries,
return values, fuel, state clocks and memory clocks reject at Flock's wiring
check. Truncated and extended proof envelopes reject. Four ordering tests also
cover gaps, duplicate clocks, forks, inactive padding and full-state equality.

The initial code root in this fixture is an independently expected memory
image. Connecting that root to the original IXBF source remains required.
This result covers a small instruction segment. The original CSLib execution
remains unproved.

### Execution with a shared memory tree

SharedCompact uses the same instruction quotas as Compact, with 16 boundary
cells, up to 192 internal tree nodes and `nu=10`. Its memory check uses the
[shared-path relation](IxbyFlockMemory.md#shared-tree-authentication). The
native batch stops before its parent-node quota as well as its cell and
instruction quotas; boundaries can therefore differ from Compact's.

An original-CSLib SharedCompact segment produces a **454,035-byte proof**
that verifies in a fresh process. It covers microsteps 410–417 and logical
steps 89–91. Setup took 3.615 seconds and proving 1.127 seconds with four
Rayon threads (`M=26`, 416,313 dense field words). All expected-word and
envelope changes, plus recomputed state-clock and memory-clock attacks,
reject. This proof still starts from an expected root whose source admission
is pending. It is not a full-run throughput measurement.

The object/application fixture and unaligned 3,073-byte hash also pass their
actual circuits across SharedCompact boundaries. They preserve all carried
state, final values and fuel; the object test reaches the same final memory
root as its whole-program fixture.

## Immutable objects and application

Constructors, closure captures and persistent application arguments reserve
an exact range at the current heap counter. Every copied field is an actual
authenticated read and write of the same canonical value. Sources must fit
the previously allocated heap prefix or the resolved scratch vector. Heap
reservations cannot wrap or overwrite a previous allocation. The 24-word
state carries both source vectors, the destination, copy position and pending
frame action. The result becomes available only after the last field is
copied. Zero-field objects still complete the logical instruction once.

Projection checks the constructor field index against the allocated vector.
Projection of Erased returns Erased. Constructor cases authenticate the
selected code alternative and require its declaration index to match the
value before appending the fields to the current frame. Whole-program source
admission must establish constructor-ID and alternative uniqueness.

Application handles empty arguments, Erased, partial applications, exact
applications and excess arguments. Partial application copies captures and
arguments into a new immutable vector. Function entry copies the required
prefix into scratch and records any remaining arguments in an authenticated
Apply continuation. Each semantic Apply transition consumes one fuel unit;
the individual copies preserve fuel.

`NativeMachine::batch` previews a step before changing memory or state. It
stops before any operation or distinct-cell quota is exceeded. Suspended
copies resume from the next batch's fully bound boundary state.

The **378,755-byte object instruction proof** covers 144 microsteps and 37
logical steps. Its program constructs and projects fields, selects a case,
creates closures, performs partial/exact/excess/tail application, uses Erased
and empty arguments, and halts with Nat 82. It touches 93 cells and allocates
12 immutable fields. The fixed Objects class provides 242 operation slots,
624 memory request slots and 96 boundary cells (`nu=13`, `M=28`, 1,922,205
dense field words). Setup took 2.561 seconds and proving 2.453 seconds with
four Rayon threads.

The proof verifies in a fresh process receiving only its 57 expected public
words and proof bytes. Every changed public word and malformed envelope
rejects. Nine independently recomputed, locally valid malicious rows changing
a copied field, heap counter, closure reference, argument splice, alternative
target, copy index, function arity, state clock or memory clock reject at
Flock's wiring check. The current Objects v1 setup includes the byte tables.
The preceding object-only v0 proof was 366,579 bytes. It required a 64 GiB
virtual-memory cap; a 32 GiB cap was insufficient. Current combined proof
suite measurements appear below.

Ordinary circuit tests also split the same computation across 15 Compact
batches, including six boundaries inside pending copy operations. They reach
the identical final state and memory root, and reject premature completion,
unallocated source spans, changed destinations, field bounds and invalid
application arities. Boundary tests cover zero and 64 fields, the final heap
cell, allocation overflow, empty application and recycled witness padding.

## Byte instructions and streaming BLAKE3

The execution circuit now supports all ten byte-related functional primitives:
Word32/field conversion in both directions, length, get, append, slice,
equality and BLAKE3. Scalar input types, exact arities, byte-array limits and
operation bounds are checked before results are produced. Field decoding
rejects a noncanonical Goldilocks value. Byte length rejects lengths that do
not fit Word32.

A constrained window reads up to 64 bytes from up to three authenticated
32-byte cells, at any byte alignment. Every unused output byte is zero. Slice
returns an exact subrange. Append reserves immutable dynamic-byte cells and
copies each output cell from its checked source ranges; the final cell has
zero padding. Equality can return false after an actual mismatching window;
true requires the entire equal-length range. Pending operations carry their
cursor, result range and old allocation counter across batch boundaries.

BLAKE3 uses the standard compression relation, sharing its table with memory
authentication. The circuit derives the chunk counter, block length,
ChunkStart/ChunkEnd/Parent/Root flags, chaining value and final output. A
separate scratch region stores intermediate tree digests. The carried merge
mask and level determine every stack read, combination and push. Each stack
read is preceded by this hash operation's corresponding write. Empty input,
exact block/chunk boundaries and incomplete final chunks use the same rules.

Two **378,755-byte proofs** verify independently in fresh processes:

- A byte program performs 87 microsteps and 17 logical steps, exercises every
  byte primitive, touches 68 cells and allocates five dynamic-byte cells.
- A BLAKE3 program hashes 1,025 bytes starting at byte offset 31, proving the
  second chunk and final tree merge against the authenticated source data.

The fixed Bytes class has 96 boundary cells, `nu=13`, `M=28` and 1,896,013
dense field words. The byte program's setup/prove times were 3.873/3.359
seconds; the chunk-tree program's were 2.798/2.496 seconds, with four Rayon
threads. All 57 expected-word mutations, a change to the byte-limit lane, and
truncated/extended envelopes reject. Eleven independently recomputed attacks
against byte pointers, allocations, conversions, copies, equality, limits,
chunk counters, root flags, merge masks and chaining values reject at Flock's
wiring check.

The combined four-proof suite, including numeric/call and object regressions,
all fresh receivers and 28 recomputed attacks, completed in 96.93 seconds.
GNU time reported 23,523,312 KiB peak process RSS with a 64 GiB virtual-memory
cap. This is a per-process maximum, not a simultaneous parent/child sum.

Ordinary tests exhaust all 32 alignments and lengths 0 through 64, check
semantic limits and canonical field decoding, and compare BLAKE3 with the
independent library for 17 lengths from 0 through 8,193 at two alignments.
A 3,073-byte hash also matches after 25 fixed batches, including 24 boundaries
inside unfinished hashing. Append tests cover full-cell joins and allocations
that resume in another batch. All inactive byte tables and recycled padding
are checked against their complete matrices.

These statements still start from independently expected code/input memory
roots. They do not establish original-source admission or the full CSLib run.

## Numeric and component evidence

The numeric dispatcher binds the functional primitive tag and exact arity to
the existing Word32 and Goldilocks consumers, or to a new immediate Nat128
consumer. Nat128 addition and multiplication reject physical overflow;
subtraction saturates at zero. Division and remainder constrain the full
256-bit quotient/product identity and a remainder below the divisor, with
explicit zero-divisor semantics. Equality and ordering produce canonical Bool
values. Byte primitives use the separate instruction consumers above;
they cannot be accepted as completed numeric operations. String operations
remain outside this execution profile.

- Three Nat128 tests compare boundary values with exact native arithmetic,
  constrain every quotient/remainder advice bit, reject low-half-only product
  identities, and check the complete matrices and recycled-buffer padding.
- Two primitive tests check all functional tags and arities, unused operands,
  type rejection, and combined numeric wiring against independent results.
  Nat128 addition and multiplication are also exercised by the genuine
  combined instruction proof above.

- Five ordinary frame tests cover calls, tail calls, over-application, copy
  completion, semantic/physical bounds, all state padding, native/Boolean
  differential checks, and the combined frame/fuel/memory wiring.
- Two genuine 309,235-byte frame/fuel/memory proofs verify in fresh processes.
  Each checks six physical steps, four logical transitions, 18 memory accesses,
  eight touched cells, and a 16-billion-step budget. The fixture exercises
  function 680, block 184, 74 locals, and continuation depth 648.
- All 48 changed expected public words reject. Five locally valid, recomputed
  attacks changing a target, depth, copied value, saved caller, or fuel row
  reject at Flock's wiring check. Truncated and extended envelopes reject.
- The complete proof test, including both honest proofs, malicious proofs and
  fresh receivers, took 23.98 seconds with four Rayon threads. GNU time reported
  maximum RSS of 2,163,944 KiB; this is a per-process maximum, not a simultaneous
  parent/child sum.
- Three ordinary code-consumer tests cover all functional instruction kinds,
  exact address derivation, literal and local values, immediate Nat128 values,
  pointer boundaries, and full-width declaration/alternative indices.

The memory advice generator uses a native overlay during a batch and computes
Merkle paths once per touched cell at commit. The circuit still checks every
ordered access through the exact permutation and authenticated boundaries.

## Remaining integration

Connect original source admission and input initialization; complete
execution boundaries and output serialization; and execution-proof aggregation.
Then prove representative original-CSLib segments and measure
the full run. None of the component results above substitutes for that run.

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml paged_frame:: \
  -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml paged_code:: \
  -- --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  frame_memory_proof_verifies_fresh_and_rejects_recomputed_steps \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  instruction_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  object_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows \
  -- --ignored --nocapture --test-threads=1
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml paged_exec::proof_tests \
  -- --ignored --nocapture --test-threads=1
# Explicit original files; these checks do not establish source admission.
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi IXBY_PAGED_BATCHES=100 \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_program_input_prefix_exercises_paged_execution \
  -- --ignored --nocapture --test-threads=1
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi IXBY_PAGED_PROOF_BATCH=99 \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_execution_segment_proves_with_fresh_memory_root_binding \
  -- --ignored --nocapture --test-threads=1
```
