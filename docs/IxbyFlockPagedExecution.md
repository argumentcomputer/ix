# Paged execution consumers

The current complete-functional interface uses **format 1, semantics 2** for
IXBF/IXFI/IXFO and the matching IXFP profile. The
[runtime handoff](CompilatrixRuntimeV2Handoff.md) documents scalar conversions,
persistent arrays, immutable builders, zero-copy byte slices, and exact limits.
The execution relation has 31 chip families and 53 microstep kinds. Packed
state transport now carries all collection scratch registers at full width.
Changed parser, execution, capture, and endpoint setups have new identities.

All measurements below describe their explicitly pinned earlier revisions.
They do not establish revision-2 CSLib performance or a complete CSLib proof.
The removed fixed-arena IXBY backend is not an alternative admission path.

The [revision-2 validation record](../flock-stage4/census/paged-execution-runtime-v2.json)
contains a 517,843-byte complete proof of a 15-step fixture covering every new
opcode, nested array updates, builders, and slicing. Independent Lean execution
matches its output. A fresh verifier accepts the root and rejects eleven
tampered statement/proof variants. This is a small correctness fixture;
compiler integration and a new CSLib measurement remain pending.

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
check. [Source-bound capture](IxbyFlockPagedAdmission.md) now constrains
these writes from actual parser events. Complete semantic reference and
constructor-ID checks now have component proofs. Their recursive composition
with input/initialization remains required. Typed input materialization now
has fresh component proofs and produces the exact initial execution image;
the initialization constraints derive all machine words and parameters.

## Native initialization and original execution segments

`NativeImage::load` decodes the original program and input, packs the complete
code image, and places the unchanged input bytes in their own memory bank.
Byte and string values keep exact offsets into those source files. Nested
constructors and partial applications reserve immutable field vectors in
preorder, then fill each value's assigned heap cell or entry local.
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

`CompiledPagedExecution::compile(class)` provides the production setup,
advice-checking, proving, verification and recursive-replay interface for all
thirteen fixed batch classes. `ExecutionStatement` binds exactly 57 field words
and requires strictly increasing, nonwrapping clocks. Setup checks every
Boolean table's complete matrices and input/output schema against its witness
driver, including the shared memory tree. The six original classes retain
their circuit layouts and transcript domains. The seven Boolean-routing
classes have separate approved setups and domains; the public statement and
proof envelope are unchanged.
The compiled setup retains immutable prover data and discards emission-only
canonicality queues, allowing workers to share it safely.

The four instruction/object/byte/hash proof tests now use this API, including
their fresh-process verifiers and 28 locally valid recomputed attacks. They
passed in 116.66 seconds. The original SharedCompact segment also passed
through this API, including its two recomputed clock attacks; it produced the
same 454,035-byte proof size. An ordinary test checks actual advice and complete
statement boundaries through the six original setups and both Boolean-routing
counterparts. The larger class has genuine proof checks. Clippy passes with warnings
denied.

## Complete endpoint binding

[`CompiledEndpoints`](../flock-stage3/host/src/ixby/ixbf_decode/paged/endpoints/mod.rs)
constrains the joins among eleven component statements: original Program
bytes, code capture, reference validation, constructor-ID uniqueness,
original Input bytes, input capture, execution, output bytes, and the three
artifact commitment bridges. Its conditional public statement contains all
283 component words followed by the two-word final digest. Every fact passes
through a committed table, including parser metadata checked in a child proof.

The circuit requires an empty initial memory tree, complete source and parser
boundaries, complete reference validation, matching program context and memory
roots, actual initialization, increasing execution clocks, terminal halt and
exact fuel accounting. It binds the returned Bytes value and final memory to
the complete output chain. The commitment bridges use the actual profile and
program digests, and the endpoint circuit computes both the profile hash and
`S = H(4, P || B || I || O)` with constrained BLAKE3.

The explicit `FunctionalProfile` encoding is **IXFP revision 0**, original
format 1, semantics 2. Its 184 bytes contain four little-endian header words,
ten 128-bit limits in original IXBF order, and a 64-bit fuel budget. Setup owns
these bytes; the captured program must have exactly the same limits and fuel.
It is a new descriptor, distinct from the earlier IXBP fixed-capacity codec.
Nat128, physical memory capacities and the supported execution operations still
limit this proving implementation. This does not claim the older IXBP
`Codec.Evaluates` theorem for original IXBF/IXFI/IXFO files; native constraint
refinement remains an additional obligation.

An original-format identity program returning a 34-byte Bytes value passes
every component circuit, and its **132,891-byte endpoint proof** verifies in
a fresh process receiving only the approved profile, expected statement and
proof. Setup took 2.564 seconds; witness construction and proving took
261 milliseconds with four Rayon threads (`M=22`). All 285 public words reject
both low-bit and high-bit changes. Six locally valid recomputed witnesses
changing parser metadata, source length, final clock, initial fuel, final
result and profile hashing reject at Flock's wiring check. Changed setup
profile and malformed proof envelopes also reject. The complete proof test
took 43.96 seconds, including construction and checking of all component
advice.

The endpoint proof alone remains conditional. The implemented
[closing recursive proof](IxbyFlockRecursion.md#complete-paged-execution-aggregation)
verifies every component chain, equates all 283 facts and exposes only `S`.
The original-format identity fixture now has a **499,347-byte complete proof**
that verifies in a fresh process with only the approved setup and expected
digest. A valid endpoint proof with changed parser metadata and unchanged `S`
rejects when joined to the original component root. The complete original
CSLib execution remains to be measured.

## Instruction execution relation

[`paged_exec`](../flock-stage3/host/src/ixby/paged_exec/mod.rs) now combines
authenticated code fetch, operand resolution into scratch memory, numeric
primitives, copy/return/Bool/Nat control, direct/self/tail calls, constructor
creation/projection/cases, closures, application, byte primitives and BLAKE3,
frame copies, continuation return, and terminal halt. Instruction actions come from the
fetched code and resolved values. The proof does not publish a host-selected
action sequence.

The batch carries 24 state words, including all frame/fuel fields, allocation
counters, instruction header, resolution cursor, and pending immutable copy.
The finite Small, Compact, Objects, Bytes, SharedCompact and Shared factories reserve fixed quotas for each
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

### Larger shared execution batch

The explicit `Shared` v0 class multiplies the Compact instruction quotas by
16. It reserves 688 microstep slots, 1,936 memory requests, 256 boundary cells
and 3,072 internal tree nodes at `nu=13`. Its transcript domain is
`IxBy/Flock/paged-execution:shared:v0`. The exact count pass requires 8,192
rows in its largest table and matches the compiled production setup. Its
commitment has `M=31`, 9,175,281 dense field words and three element tables.
The existing classes retain their domains, capacities and constraints.

A genuine original-CSLib batch covers microsteps 1,207–1,325 and logical
steps 292–324. Its **498,939-byte proof** takes 5.933 seconds after 8.123
seconds of setup with four Rayon threads. A fresh receiver verifies it;
changed expected words and proof envelopes reject, as do locally valid
recomputed state-clock and memory-clock rows. The complete test takes 33.87
seconds, with 24,785,868 KiB maximum process RSS. The parent releases its
proving graph before starting the fresh receiver. This segment starts from
an independently supplied memory root; it alone does not establish the full
original execution or source admission.

The [measurement record](../flock-stage3/profile/cslib-shared-execution-v0.json)
also pins a native prefix of 1,000 Shared batches: 150,607 microsteps and
38,746 logical steps in 8.172 seconds. A separate run compares every
accelerated calculation in that prefix to its Boolean plan. Native advice
timings exclude complete batch checks and proving. These results do not yet
establish practical throughput for the 2.268-billion-step workload.

### CPU server throughput and cost breakdown

The 32-core Intel Xeon 6975P-C server with 495 GiB RAM ran the Shared class
against the pinned original CSLib program and input. Each worker used the
same immutable compiled setup and its own Rayon pool. Every sample produced
an actual proof and passed the production verifier. Setup and native replay
are excluded from the worker times below; worker startup, verification and
retained proof writes are included.

| Workers × threads | Batch indices | Logical steps | Worker wall, seconds | Steps/second | Process peak RSS, GiB |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 × 4 | 0–15 | 567 | 79.540 | 7.128 | 22.862 |
| 8 × 4 | 0–31 | 1,181 | 37.336 | 31.631 | 141.020 |
| 16 × 2 | 0–63 | 2,378 | 68.399 | 34.767 | 276.663 |
| 8 × 4 | 9,990–10,021 | 1,234 | 37.207 | 33.166 | 141.571 |

The later window starts after 388,624 consumed logical steps. Replaying its
9,990 preceding native batches took 103.771 seconds. Each measured proof is
498,939 bytes. Including four separate phase-timing samples, 148 proofs
passed across 96 distinct batch indices. Fresh local processes also accepted
server proofs 63 and 9,990 with only the externally supplied expected boundary
and proof, after compiling the fixed Shared setup. These are conditional
segment proofs; neither the skipped prefix nor complete CSLib execution is
proved by this measurement.

The first 16-worker attempt reached a 448 GiB virtual-address cap while using
190.755 GiB resident memory. A new run passed with a 768 GiB address allowance
and a user service scope enforcing a separate 400 GiB physical-memory cap.
The failed attempt and successful retry are both retained in the
[measurement record](../flock-stage3/profile/cslib-server-proof-throughput-v0.json).

The exact table census identifies two structural costs:

- **Routing occupies 78.6% of the useful field data:** the three switching
  networks use 7,216,128 of 9,175,281 dense field words. These networks reorder
  complete execution states, timed memory records and shared-tree records.
- **The padded witness is 58.5 times the useful field data:** the union layout
  has 536,870,912 field words, or 8 GiB per padded buffer, for about 147 MB of
  useful data. The prover also maintains other witness and argument buffers.

The phase trace shows this cost before final commitment: in a warm sample,
Flock witness materialization took 1.098 seconds, Boolean consistency and
wiring took 1.118 seconds, element consistency took 0.346 seconds, commitment
took 0.156 seconds, and opening plus buffer return took 0.914 seconds.
Building the instruction-gate witness took another 0.779 seconds. These
measurements guide optimization; they do not establish a hardware bandwidth
ceiling or a full-workload rate.

The original Shared Fetch quota is 32. The independent reference profile records
1,956,519,385 Eval transitions, giving a quota-based floor of **61,141,231
execution leaves** when each Eval requires its instruction fetch. At the
observed leaf size that is about **30.5 TB**, before recursive nodes. A linear
extrapolation from the fastest short sample is about **755 days** for execution
leaves alone. This excludes native replay, admission, output and aggregation;
it is an estimate, not a measured full-run duration. An unbounded complete
CSLib proof job was not launched.

These measurements motivated the Boolean routing and larger fixed class
below. Further progress must be assessed in seconds and peak memory per guest
instruction, including recursive costs.

Reproduce the bounded throughput measurement with the existing test harness:

```sh
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi \
IXBY_PAGED_NATIVE_CLASS=shared \
IXBY_PROOF_BATCHES=32 IXBY_PROOF_SKIP=9990 \
IXBY_PROOF_WORKERS=8 IXBY_PROOF_THREADS=4 \
IXBY_PROOF_OUT=/path/to/new-segment-proof-directory \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 \
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock --lib \
  ixby::paged_exec::benchmark_tests::original_execution_proof_throughput \
  -- --ignored --exact --nocapture --test-threads=1

RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 \
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock --lib sizing::tests::paged_execution_table_costs \
  -- --ignored --exact --nocapture --test-threads=1
```

`IXBY_PROOF_OUT` is optional; supplied directories must be new. The harness
bounds sample size and worker count. `PCS_TRACE=1` enables the existing native
prover's phase timings. The checked-in record retains exact per-sample times,
artifact hashes, both fresh receiver receipts and the address-limit failure.

### Boolean routing and the 1,024-fetch class

`shared-compact-boolean` and `shared-boolean` retain the corresponding Shared
quotas and memory capacities, and express all three whole-record switching
networks as Boolean tables. Each selector is exactly zero or one, and every
bit of every state and memory word remains constrained. The packed witness
writer computes complete field words directly and is checked against the
table's sparse matrices. This preserves the existing proof protocol.

An entirely Boolean union can use Flock's support-aware working buffers.
Witness generation writes the useful rows and the final eight-row group;
it skips the remaining unused rows when the prover permits this. Clearing
the final group is necessary because the pinned x86 zerocheck kernel reads
512-bit units. Row domains smaller than 64 rows clear all padding because
those reads can span column gaps. Mixed Boolean/element unions continue to
write all padding. The Boolean Shared layout has 4 GiB per padded buffer,
compared with 8 GiB for the original Shared layout.

`shared-1024` uses this routing with **1,024 Fetch slots, 8,128 total
microstep slots, 2,048 distinct memory cells and 8,191 shared-tree parents**.
Its row capacity is 32,768, and its commitment has `M=33`. The exact useful
witness contains 59,381,425 field words; the padded address domain remains
16 GiB per buffer. These are reserved capacities, not guaranteed instruction
counts: a batch ends when any instruction family or memory capacity fills.
Logical Eval/Apply/Return steps differ from Fetch operations, and a batch may
contain either more or fewer than 1,024 logical steps.

The new transcript domains end in `shared-compact-boolean:v0`,
`shared-boolean:v0` and `shared-1024:v0`. Callers select the class explicitly,
including in the production CLI and recursive verifier setup. Existing class
identities remain compatible with previously generated proofs.

The final binary produced these verified server samples. Worker wall time
excludes setup and native replay, and includes verification and retained proof
writes. The first two rows cover identical execution boundaries.

| Class | Workers × threads | Batch indices | Logical steps | Worker wall, seconds | Steps/second | Peak RSS, GiB |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Shared | 1 × 4 | 0–7 | 252 | 36.137 | 6.973 | 19.772 |
| SharedBoolean | 1 × 4 | 0–7 | 252 | 32.742 | 7.697 | 8.493 |
| Shared1024 | 8 × 4 | 0–15 | 16,906 | 57.849 | 292.245 | 163.962 |

The larger sample averages **1,056.625 logical steps per proof**, versus
37.156 in the previous 64-batch Shared sample: **28.4 times as much work**.
Each larger proof is 612,155 bytes, versus 498,939 bytes. Its measured leaf
throughput is **8.4 times** the previous best of 34.767 steps/second on the
same server. The equal-capacity Boolean change alone cuts paired peak RSS
from 19.772 to 8.493 GiB, making larger batches affordable.

The [measurement record](../flock-stage3/profile/cslib-large-execution-v0.json)
retains all 96 proof samples, including four-worker and later-window runs,
exact per-family row usage, failed trials, binary hashes and fresh verification
receipts. Short-window leaf throughput excludes recursive aggregation and
does not establish a complete CSLib proving rate. Applying that rate to the
full reference trace would still project about 90 days for execution leaves
alone, before admission, output and recursion.

All three new classes pass genuine original-CSLib leaf proofs, fresh
verification, changed expected statements and malformed envelopes. Locally
valid recomputed state-clock and memory-clock witnesses reject at the wiring
check. A fresh receiver also accepts larger-class server batch 256, covering
logical steps 313,360–314,604, with only its expected statement and proof.
An old Shared proof remains verifiable with the updated implementation.

The first three larger CSLib leaves cover 14,359 microsteps and 3,604 logical
steps. Genuine recursive nodes joining two and three leaves verify, producing
389,443 and 376,467 bytes. The second level includes a recursive child and a
raw execution leaf. Repeated, reversed and skipped genuine segments reject.
The final node verifies in a fresh process, which also rejects low-bit and
high-bit changes independently in every one of its 57 public words.
The two nodes took 84.1 and 88.9 seconds locally for proving plus verification;
their setup and fresh receiver are additional costs. These are correctness
runs, separate from the server leaf-throughput measurements.
These remain conditional execution chains; they do not prove the preceding
source-admission obligations or the complete CSLib workload.

The switching networks remain the largest useful-data cost: 48,242,688 field
words, or 81.2% of the larger class. The improvement comes from cheaper
witness storage and generation, then amortizing fixed boundary work across
larger batches. A smaller ordering argument and specialized byte/hash quotas
remain opportunities for further improvement.

Use the bounded harness above with `IXBY_PAGED_NATIVE_CLASS=shared-1024`,
`IXBY_PROOF_SKIP=0`, `IXBY_PROOF_BATCHES=16`, `IXBY_PROOF_WORKERS=8` and
`IXBY_PROOF_THREADS=4` to reproduce the larger-class server sample. Resource
limits must accommodate both address reservations and resident memory; the
eight-worker run used a 1,536 GiB virtual-address allowance within a separate
400 GiB physical-memory cap on the 495 GiB server. This is a benchmark setting,
not a requirement for one worker. The complete CLI selects the same approved
class with `--class shared-1024`.

The independently checked 83-step countdown also passes the complete CLI
using this class: its 367 microsteps fit one execution leaf, all eleven
component proofs and the endpoint proof verify, and recursive aggregation
produces a **502,979-byte root**. A fresh process accepts it with only the
approved profile, independently expected digest and root proof. Complete
proving took 715.7 seconds on the server; fresh setup took 170.9 seconds and
verification 23.3 seconds. This small workload validates composition and the
padding fix; its timing does not measure large-workload throughput. See the
[complete countdown record](../flock-stage4/census/paged-execution-countdown-1024-v0.json).

### Exact packing of routing records

`shared-compact-packed` and `shared-packed-1024` keep the capacities of
`shared-compact-boolean` and `shared-1024`. They pack canonical record bits
before each switching network and unpack them before the existing audit.
Packing and unpacking are Boolean circuit gates: every omitted input bit and
every unused bit in the packed representation must be zero. The resulting
map is injective on accepted records, so the fixed network still establishes
an exact permutation of complete records. There is no hash, random
fingerprint, new permutation argument or change to the Flock protocol.

| Routed record | Original field words | Packed field words | Preserved data |
| --- | ---: | ---: | --- |
| Execution state | 26 | 15 | Clock, kind, both fuel limbs, all live state fields and full value/hash words |
| Timed memory | 5 | 3 | 40-bit address, 64-bit time, kind and both complete value words |
| Shared tree | 6 | 5 | Enabled flag, level and position, all four digest words |

The state representation uses 1,914 bits. It removes the frame header's
reserved bits, high padding in bounded counters and vectors, unused merge
control bits, and three reserved state words. Fuel retains both its budget
and usage counters. Hash chaining values and value payloads retain all 128
bits per field word. The exact masks are part of the approved packing
matrices in `state_record_layout`; a prover cannot choose a different mask.
This is an additional canonicality requirement of the new classes. The nine
earlier class identities, matrices and domains remain unchanged.

The larger packed class contains **43,718,321 useful field words**, down from
59,381,425: **26.4% less witness data**, including the packing gates. Routing
falls from 48,242,688 to 30,220,288 words; packing and unpacking add 2,359,296.
The padded address domain remains 16 GiB per buffer, with `M=33`. A packed
execution leaf is **540,251 bytes**, versus 612,155, a reduction of **11.7%**.
The compact packed class contains 357,685 useful field words and produces a
412,011-byte execution proof.

The new transcript domains end in `shared-compact-packed:v0` and
`shared-packed-1024:v0`. Select the latter with
`IXBY_PAGED_NATIVE_CLASS=shared-packed-1024` in the bounded benchmark, or
`--class shared-packed-1024` in the complete CLI. The verifier selects its
approved class before reading proof bytes, including for recursive children.

Packing tests check every removed input bit, every output bit, complete
round trips, and packed witness buffers against the sparse matrices. They
also cover recycled buffers and partial groups of eight rows. Execution
fixtures cover instruction, object, byte and multi-chunk hash states. Both
new classes pass actual CSLib segment proofs, isolated verification, changed
public statements and recomputed state-clock and memory-clock substitutions.

The server comparison used the same binary and byte-identical statements for
both 16-batch runs. As above, worker wall excludes native replay and setup,
and includes proof generation, verification and writes.

| Class | Workers × threads | Batch indices | Logical steps | Worker wall, seconds | Steps/second | Peak RSS, GiB |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Shared1024 | 8 × 4 | 0–15 | 16,906 | 60.793 | 278.091 | 163.756 |
| SharedPacked1024 | 8 × 4 | 0–15 | 16,906 | 48.973 | 345.213 | 119.402 |
| SharedPacked1024 | 8 × 4 | 256–263 | 9,932 | 24.852 | 399.648 | 119.418 |
| SharedPacked1024 | 16 × 2 | 0–31 | 36,418 | 87.560 | 415.918 | 172.800 |

Packing improves the controlled eight-worker throughput by **24.1%** and
reduces peak RSS by **27.1%**. The sixteen-worker sample covers more batches,
so its ratio to the eight-worker result does not isolate the effect of worker
count. It uses a 3,072 GiB virtual-address allowance within the same separate
400 GiB resident-memory cap. Every measured proof verifies. A fresh local
process accepts packed batch 256 using only its 912-byte statement and proof;
another accepts an old Shared1024 proof from the preceding implementation.

The [packed execution record](../flock-stage3/profile/cslib-packed-execution-v0.json)
retains all 72 benchmark samples, exact table costs, per-family row usage,
binary and source hashes, and verification receipts. The three traced baseline
proofs used to locate the cost are recorded separately. The affected tests
pass 81 checks, and both workspaces pass formatting and all-target Clippy with
warnings denied.

The first three packed CSLib leaves also pass two recursive levels, producing
394,035-byte and 381,059-byte nodes. The joins cover the same 14,359 microsteps
and 3,604 logical steps as the earlier large-class chain. Proving plus
verification took 46.3 and 59.5 seconds locally; setup is additional. Repeated,
reversed and skipped genuine leaves reject. The final node passes a fresh
receiver and all 114 independent low/high public-word mutations. These are
correctness checks, rather than a controlled recursive-throughput comparison.

The complete 83-step countdown produces a **509,475-byte root**, accepted by
a fresh process given only the approved profile, independently expected
digest and proof. It proves all eleven components plus endpoints, with one
540,251-byte execution leaf. Complete proving took 642.4 seconds; fresh setup
took 166.4 seconds and verification 20.0 seconds. The six packing tables add
twelve fixed-matrix claim families at the root, whose size grows from the
earlier 502,979 bytes. This fixture validates composition; it does not measure
complete CSLib throughput. Its pins and receipts are in the
[packed countdown record](../flock-stage4/census/paged-execution-countdown-packed-v0.json).

Routing still occupies **69.1%** of the packed class's useful field data.
Even the 32-batch leaf rate would project about **63 days** for the original
reference trace, before native replay, source admission, output and recursive
aggregation. This is not a full-run budget. Further reductions in routing and
instruction-family costs remain necessary; complete CSLib execution is unproved.

### Direct state linking

`shared-compact-linked` and `shared-linked-1024` keep the packed classes'
capacities and canonical record layouts. For `N` transition slots, they route
`N` after-states plus the initial boundary into `N` before-states plus the
final boundary. A fixed Beneš network establishes exact equality of these
multisets. Each output is compared with its target using one XOR residual per
complete field word, with every residual constrained to zero.

This halves the state network's lanes from `next_power_of_two(2N + 2)` to
`next_power_of_two(N + 1)`. The 1,024-fetch class uses 8,192 state lanes and 25
switching stages, replacing 16,384 lanes and 27 stages. Memory and shared-tree
routing are unchanged. No fingerprint or probabilistic multiset check replaces
the full records.

The existing preparation gate proves that every enabled transition advances
its 64-bit clock by one without overflow. Every disabled transition has zero
clock and zero before/after states. A new boundary gate requires two canonical
64-bit clocks with `initial < final`.

To see why matching proves a single chain, cancel the identical padding
records from both multisets. Let `c(t)` count enabled transitions with
before-clock `t`. Exact matching implies
`c(t) - c(t-1) = [t = initial] - [t = final]`, with `c(-1) = 0` and no clock
wraparound, where brackets are one when the condition holds and zero otherwise.
Thus there is exactly one transition at each clock from `initial`
through `final - 1`, and none elsewhere. At each shared clock, equality of the
complete record links the preceding after-state to the next before-state.
This excludes duplicate, missing and disconnected transitions. Positive
boundary progress excludes an empty chain.

The larger class uses **32,659,896 useful field words**, down from 43,718,321
for the packed class: **25.3% less**. Routing uses 21,185,280 words, ordering and
matching use 2,187,207, and packing uses 1,671,168. Other table-family costs are
unchanged. The dense commitment domain falls from `M=33` to `M=32`; the padded
union address domain stays at 16 GiB per buffer. The compact linked class
uses 305,374 words and produces a 389,043-byte execution proof.

The larger linked leaf is **607,299 bytes**, compared with 540,251 for the
packed class. The existing commitment layout now occupies 63 lanes of the
smaller domain, compared with 42 in the preceding domain. Its query openings
carry more lane values even though there are fewer committed words. The
existing Fast128 settings remain in force. Proof size depends on the commitment
layout as well as the number of witness words.

Setup also keeps the growing zero-constraint wire class as the first argument
to `ShapeBuilder::connect`. The builder appends the second class into the
first; reversing these arguments repeatedly copied the growing list. The
optimized construction preserves the same wire equivalence classes.

The new transcript domains end in `shared-compact-linked:v0` and
`shared-linked-1024:v0`. The verifier selects the class before reading proof
bytes. The eleven preceding classes retain their existing matrices and
domains.

#### Linked execution measurements

The same server executable proves the same 32 segment statements with both
layouts, using sixteen workers with two threads each. All corresponding
912-byte statements compare byte for byte. A later linked window checks
another eight segments with eight workers and four threads each.

| Class | Workers × threads | Batch indices | Logical steps | Worker wall seconds | Logical steps/second | Peak RSS GiB |
| --- | ---: | --- | ---: | ---: | ---: | ---: |
| SharedPacked1024 | 16 × 2 | 0–31 | 36,418 | 90.336 | 403.137 | 169.001 |
| SharedLinked1024 | 16 × 2 | 0–31 | 36,418 | 68.632 | 530.626 | 126.974 |
| SharedLinked1024 | 8 × 4 | 256–263 | 9,932 | 18.874 | 526.224 | 82.174 |

The paired worker rate improves **31.6%** and peak process memory falls
**24.9%**. Worker wall includes witness generation, proving, verification and
proof writes; it excludes native replay and setup. All **72** benchmark
proofs verify. The runs use the same 400 GiB resident-memory cap, no swap and
the existing Fast128 proof parameters.

The server executable predates the setup-copy fix described above. Its linked
setup took 78.435 seconds versus 20.696 for the packed class, making the whole
command slower: 154.59 versus 118.59 seconds. The final setup fix is measured
separately on the local machine: the same three linked segments take 44.510
seconds of setup before the fix and 38.443 after, a 13.6% reduction. Their
worker times are effectively unchanged at 28.536 and 28.639 seconds; whole
commands take 75.30 and 69.39 seconds. This is one sequential local pair,
without other heavy jobs. Final-code throughput has not been measured on the
server. Setup remains a cost to amortize across many batches.
The [linked execution record](../flock-stage3/profile/cslib-linked-execution-v0.json)
keeps the binary identities, per-segment times, row usage and measurement
limits explicit.

The four new state-ordering tests exercise every bit of complete record
equality, all high clock bits, zero-state transitions at clock zero, and
duplicate, missing, disconnected, disabled, empty and overflowing chains.
Both new classes pass genuine CSLib leaf proofs, all 57 public-word mutations,
a high byte-limit limb, malformed envelopes, and locally valid recomputed
state/memory-clock attacks. A fresh final-code process accepts server batch
256 using only its statement and proof; another accepts a retained packed
leaf from the preceding implementation.

Three genuine linked CSLib leaves pass two recursive levels, producing
**392,771-byte** and **430,603-byte** proofs. The final-code child process
accepts the three-leaf statement and proof and rejects all 114 independent
low/high public-word mutations. Repeated, reversed and skipped genuine leaves
reject at the constrained joins. Proving plus verification takes 46.3 and
59.3 seconds locally, with setup additional; these are correctness checks.

The complete original-format 83-step countdown produces a **510,115-byte**
root. A fresh final-code verifier accepts the earlier executable's root using
only the approved profile, independently expected digest and proof. Its setup
identity is unchanged. All eleven component counts are one; the execution
statement still covers 367 microsteps and 83 logical transitions. See the
[linked countdown record](../flock-stage4/census/paged-execution-countdown-linked-v0.json).

At this leaf size, the existing quota-based floor of 1,910,664 leaves implies
at least 1.16 TB of raw execution proofs before recursive nodes. Extending the
32-batch worker rate to the full reference trace would take about 49.5 days
for execution leaves alone. This is an extrapolation, not a practical full-run
budget; other quotas and the unmeasured workload can add substantial cost.
Complete CSLib execution remains unproved.

For changes to the work expressed by IxBy itself, see the
[runtime performance priorities](IxbyPerformance.md), which identify the
numeric conversion, persistent-array and byte-rope costs in the full reference
trace.

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
admission includes the separate full constructor-ID uniqueness proof;
source-bound code capture checks alternative uniqueness with a carried bitmap.

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

## Native advice generation

Common instruction and code-access advice now uses direct native calculations.
Production gate evaluation, complete Boolean matrices, witness schemas and
Flock verification retain their existing constraints. The direct calculations
supply untrusted advice. Test-mode machines compare every accelerated result
against the unchanged Boolean plan, including calls, returns, Nat branches,
object operations and byte/hash fixtures.

Shared-memory admission also counts exact parent paths from sorted addresses
and the same smallest-unused-address padding. It uses each pair's first common
ancestor and counts a dense padding prefix by level. Exhaustive small-address
subsets and wider 40/64-bit cases agree with explicit path enumeration,
including duplicate addresses, padding and capacity failures.

On the original 1,016,587-byte program and 4,813,238-byte input, 10,000
SharedCompact batches generate 33,212 microsteps and 8,352 logical steps.
Native generation takes **4.212 seconds**, compared with **6.525 seconds**
before these changes; the parent-count change alone takes 5.934 seconds.
These are advice timings without complete batch checks or proving. A separate
run compares every accelerated calculation in this prefix to its Boolean
plan. All 20 execution tests and six memory-log tests pass. The four real
execution proofs, fresh receivers and 28 recomputed attacks pass in 114.48
seconds, and the original SharedCompact segment still produces a verified
454,035-byte proof. The larger Shared measurement above uses a different
physical class; full-workload proving throughput remains unmeasured.

## Remaining integration

Source admission, initialization, exact finalization, output and commitment
binding now compose into one independently verified original-format execution
proof. Original-CSLib execution segments also have conditional proofs under
Compact, SharedCompact and Shared. Practical full-workload throughput, the
complete original CSLib execution and its final independent verification
remain. Native constraint refinement to the formal semantics is a separate
obligation.

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
IXBY_PAGED_PROGRAM=/path/to/cslib.ixby \
IXBY_PAGED_INPUT=/path/to/cslib.ixbi IXBY_PAGED_PROOF_BATCH=9 \
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml \
  original_shared_execution_segment_proves_fresh \
  -- --ignored --nocapture --test-threads=1
```
