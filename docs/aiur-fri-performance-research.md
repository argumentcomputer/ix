# CPU execution and GPU performance for initial Aiur FRI proving

Status: proposed experiments, 2026-11-16. Full word streams are the main
source-level candidate; adoption depends on measured execution and proving
time. The figures below are existing measurements, with their original scope.

## 1. Objective and decisions

Reduce fresh `ix prove` latency for IxVM claims and their Goldilocks/FRI
aggregation on one GPU. Include CPU execution, advice preparation, witness
population, GPU proving, recursive parents, root wrapping and independent
acceptance. Preserve BLAKE3, the production security parameters, the expected
environment statement and bounded record/witness residency.

The [single GPU performance design](aiur-single-gpu-performance.md) records
the original critical path and the implemented preparation improvements.
This design extends it with the compression research through November 16 and
gives full word streams an explicit experiment and acceptance plan.

The immediate decisions are:

- Profile native execution on a representative leaf and a real aggregation
  join. Distinguish hint dispatch, memoized calls, memory interning, fixed-table
  counting and generated arithmetic before choosing the first full port.
- Evaluate full word streams across a complete input, parser and hash path.
  Four-byte hints alone are a useful smaller experiment, not a prerequisite
  whose result decides whether fewer list allocations would help.
- Evaluate grouping with the representation change. Measure both the current
  proof and the execution/proving of its recursive parent.
- Preserve the existing preparation optimization and streaming pipeline.
  Test further host and GPU improvements separately to keep attribution clear.

Compression starts from an already produced IxVM root. The November 16 L3
measurement of **167.192 s** covers wrapping and compression after that root;
it is not a timing of initial `ix prove`. Its techniques are relevant, but its
timing reductions cannot be assigned to the initial prover. See the
[compression architecture][architecture] and [L3 measurement][l3].

## 2. Evidence and remaining bottlenecks

### Initial prover measurements

The [preparation comparison](measurements/aiur-single-gpu-preparation.json)
used native executors, one RTX PRO 6000 Blackwell, 32 available logical CPUs
and unchanged proof parameters. Each version executed once and produced
three fresh proofs of the retained record.

| Metric | Control | Preparation candidate | Interpretation |
|---|---:|---:|---|
| Init leaf execution | 92.20 s | 91.45 s | One execution per version; no execution improvement established |
| Init leaf proof generation median | 49.34 s | 41.63 s | 15.6% reduction after execution |
| Init leaf host depth preparation median | 7.60 s | 3.05 s | Row parallelism reduces the prepass |
| Init leaf repeated validation median | 9.05 s | About 7 microseconds | Immutable prepared records replace whole-record scans |
| Init leaf witness stalls median | 9.83 s | 3.38 s | Overlaps other work; do not add phase savings |
| Init leaf peak RSS | 42.75 GiB | 44.54 GiB | About 1.8 GiB more observed host residency |
| Saved-root verifier proof generation median | 2.263 s | 2.101 s | 7.1% reduction; this is not a two-child aggregation join |

The leaf owns 18,698 constants and records 232,362,784 queries. Its 22 trace
shards require 43 witness supplies under regenerate retention. All twelve
paired proofs verified, with matching digests within each workload. The
preparation candidate is the baseline for subsequent execution experiments;
both sides must retain it so its benefit is not counted again.

The earlier whole-Init command took 591.31 s, including a 482 s controller
interval. At least 159 s of that controller interval was exposed waiting for
initial, join or root execution. About 109 s was outside the controller timer.
Final acceptance is a candidate contributor, but that difference does not
attribute all 109 s to acceptance. The earlier design contains the timeline.

### Findings from compression

| Technique and evidence | Established observation | Transfer to initial FRI |
|---|---|---|
| [Word streams experiment][word-counts] | Packed BN verifier padded main cells 147.5M to 105.3M, with the same consumed transcript/digest bytes; count-only | Fewer input/list/transcript operations could reduce CPU and trace work; no Goldilocks timing prediction |
| [Word streams and regrouping][bn-stages] | Steady-state padded cells 213.9M before the port, 256.0M with old grouping, then 175.5M after regrouping | Representation and grouping need joint evaluation |
| [Normalized wrapper experiment][wrap-results] | The following CompressGL execution fell from 44.29 to 29.10 s on the changed predecessor proof | Proof geometry can reduce the next verifier's CPU work |
| [Fixed predecessor key tables][fixed-key] | Parsed graph nodes, roots, lookup descriptors and shapes come from program tables; runtime key hashing/parsing is removed for the specialized relation | Applicable to known IxVM child keys in aggregation |
| [Parallel trace preparation][stage-study] | Compression trace time reported as 22.4 to 8.8 s after parallel filling and sharding | Inspect remaining serial initial-prover preparation; preserve incremental population |
| [Early stage setup and export caches][pipeline] | Predecessor-independent construction/loading runs while another stage executes; layout exports are reused by content identity | Hide genuinely independent setup and avoid reconstruction, within memory reservations |

These observations come from different experiments and are not additive.
The compression tree remains based on `4e27c5fcd` plus uncommitted changes.
The [research evidence record](measurements/aiur-fri-research-2026-11-16.json)
captures the cited source hashes and selected measurements; a commit hash
alone does not identify that working tree.

## 3. CPU execution research

### 3.1 Measure the current native workload

Use the existing [profiling driver](../crates/ix-prover/examples/profile_proof.md)
and phase reports. Sample the native execution interval separately from
statement construction, model advice, binding, trace preparation and proving.
Record CPU samples and available hardware counters, especially cache misses
and instruction-cache pressure. Profile overhead belongs to the diagnostic
run; reported speedups come from unprofiled comparisons.

The initial prover already has native executors, closed-form byte-table
handlers, flat query storage and bounded dense indices for eligible keys.
The compression checkout has no new changes to `native.rs`, `query.rs` or
the native code generator relative to its base. There is no new generic
native-executor patch to adopt from it.

Candidate host changes depend on the profile:

- Reduce work in `Runtime::begin` and `QueryTable::lookup`, including hashing,
  probing, insertion and unnecessary work on dense-index hits.
- Reduce pointer chasing and repeated bookkeeping in `Runtime::count_map`.
  Any prebound access must remain valid when query storage grows.
- Reduce memory interning and allocation overhead, preserving exact key
  equality, stable row/address order and counted storage reservations.
- Tune generated hot-code size and selective inlining. Removing a call can
  increase code size or lose useful memoization; evaluate both effects.

Preserve pending-query/cycle rejection, overflow checks, multiplicities,
depths, errors and resource cancellation. Native-only changes to an unchanged
program should preserve its complete record and proof bytes. Host-native
BLAKE3 cannot replace an Aiur call while omitting the execution evidence its
constraints need. The [native execution design](formal-aiur-native-execution.md)
describes the existing runtime contract and historical profiles.

### 3.2 Batch four byte hints

[IxByteStream](../IxVM/IxVM/Source/IxByteStream.lean) already handles four bytes
per recursive source call, but that branch invokes `ixvm.io.read` four times.
[KzgIO][kzg-io] uses one four-element hint. The existing
[`StreamAdvice::register_read`](../crates/aiur/src/library/advice.rs) supports
fixed-size reads; the IxVM binder currently registers the scalar reader.

Add a four-byte reader through that interface, retaining the existing byte
list, paired byte range checks and the scalar cases for the last one to three
bytes. This isolates dispatch and repeated offset/bounds-check overhead.
It does not eliminate the four list nodes or their memory operations. A small
gain here would not bound the benefit of the full representation change.

### 3.3 Full word streams

The proposed representation stores a checked four-byte word in each list
node and keeps a byte cursor. For sixteen bytes:

```text
Byte list:  b0 -> b1 -> b2 -> ... -> b15
Word list: [b0 b1 b2 b3] -> [b4 b5 b6 b7] -> ... -> [b12 b13 b14 b15]
```

There are four stream nodes instead of sixteen. Each word still contains
four checked bytes; this does not imply four times less total memory or four
times faster execution. The intended savings are fewer node allocations,
pointer operations, memoized calls and associated proof lookups.

Use the compression implementation's `Input = (Words, byte_offset)` as the
starting design. Its short leading word places the first one to three bytes
after an unused prefix, so the represented stream ends on a word boundary.
The cursor offset is in `0..3`; an empty stream has offset zero. Unused prefix
bytes are outside the logical stream and never enter parsing or hashing.
Specify and check the relation between physical words, offset and byte length.

Operations should include byte reads, aligned and unaligned word reads,
fixed-size address reads, bounded substreams, finish checks, transcript
absorption and hashing. Aligned word reads advance one node; unaligned reads
combine the relevant bytes of adjacent words. A bounded blob must have its
own exact endpoint so a parser cannot consume the following field.

The complete path is:

```text
compact host bytes
  -> checked word reads
  -> word cursor used by parser and hash
  -> word-oriented transcript operations
  -> the same serialized bytes and BLAKE3 challenges
```

Keep word form through the hot path. Rebuilding a whole byte list before
each parser or hash would restore much of the allocation cost. BLAKE3 should
consume sixteen words per 64-byte block, reusing its existing compression
arithmetic, counters and flags. A few byte operations for tags or tails are
acceptable. The [word transcript][kzg-transcript] and [word hash driver][kzg-hash]
provide concrete patterns, including partial-word handling.

#### Field and byte semantics

All bytes remain range-checked. A 32-bit word fits in Goldilocks, but arbitrary
64-bit wire values do not: decode them as checked limbs and retain canonical
field checks before conversion. Do not reduce a serialized 64-bit value modulo
the field and then treat it as a canonical input.

Length arithmetic must be bounded integer arithmetic. For an input of fewer
than `2^32` bytes, a decomposition `length = 4*q + r` needs `r` in `0..3`
and a suitable bound on `q` such as `q < 2^30`; these bounds prevent modular
wraparound. Audit the BN helper's termination/bound arguments before reusing
them over the smaller Goldilocks field. Preserve each channel's existing
length limits. Numeric metadata channels, such as reducibility tags, must
not be truncated into byte channels.

The parser and hash must consume the same constrained data. Separate host
hints for a parsed object and its digest do not establish that relationship.
The proposed specification is that decoding the word cursor yields exactly
the original byte stream, parsing preserves its values and endpoint, and
word hashing yields the reference hash of those decoded bytes. Transcript
absorption order, rejection sampling, squeezed bytes and challenge order must
match the verifier's existing protocol.

Keep these operations in shared Aiur source. Rust supplies advice through the
existing bounded interfaces; it does not replace constrained verification with
a host check. The verified compiler establishes the compiled meaning of the
new source, not its equivalence to the old parser or hash implementation;
that equivalence requires its own specification and validation.

#### Port boundaries

Evaluate IxVM and aggregation independently:

- **IxVM:** `IxByteStream`, the used `IxonDeserialize`/`IxonSerialize` paths,
  and hashing of the same serialized constants, claims, bindings and model
  payloads. Complete a path through both parsing and hashing before measuring
  a full-word variant. Preserve the kernel's semantic checks.
- **Aggregation:** `StarkIO`, key and claim deserialization, transcript
  construction and byte-list hash adapters. The actual proof parser already
  has indexed eight-byte reads in `ProofDeserialize::read_u64_at`, and
  `verify_batch_at` uses the indexed parser. Preserve those fast paths;
  do not assume every proof byte currently creates a byte-list node.

The native profiles determine the first full port. A saved-root verifier is
useful for parser/hash validation, but adoption for aggregation requires a
real two-child join, including structural-discharge work. IxVM's much larger
execution remains a separate measurement target.

Source changes require new certified artifacts, native-executor fingerprints,
trace writers where used, and independently selected key identities. Compare
the same logical claim and reference outputs across versions. Internal record
shapes, instruction counts and newly generated outer proofs may change. For
verification of the same child proof, its transcript bytes must agree; a new
outer proof's transcript need not match the old circuit's transcript.

### 3.4 Preprocess fixed child keys in aggregation

The current [aggregation source](../MultiStark/MultiStark/Modules/Aggregation.lean)
loads, hashes and parses child systems in `aggr_load_sys`. Memoization can
share the work within one execution; it does not make the parsed key persist
across separately proven jobs.

Reuse [KzgPackedTerminal's approach][fixed-key]: parse the known predecessor
key at export and put graph nodes, roots, lookup descriptors and shapes into
fixed tables committed by the new program's key. Read graph nodes directly
by index and validate equivalence with the generic reader/evaluator.

Start with the known IxVM child key. Retain a generic self-recursive branch;
embedding the aggregator's own new key would create a circular dependency.
Changing the key allowlist and the outer public statement must be explicit.
Keep dynamic proof shapes where fixed capacities would impose unnecessary
padding or reject intended workloads. This can improve aggregation execution,
but does not accelerate the leaf's kernel execution.

## 4. Initial GPU proving research

### 4.1 Preserve and extend bounded preparation

Carry forward the validated preparation object and row-parallel depth pass
from the isolated performance worktree. The active compression checkout did
not contain that patch at the research snapshot. Its backend refactoring must
be reconciled without restoring per-supply scans or weakening validation.

The initial streaming writer already fills function rows in parallel and
uses zeroed allocations. Its ROM-row population loop remains serial. Reuse
the compression writer's chunked row-filling pattern for independent ROM
rows, preserving row order, multiplicities, addresses and padding. Measure
the affected phase before assigning it priority.

Further depth work is conditional on its remaining cost: compute only the
columns needed by depth slots, or cache bounded depth results if that wins.
Charge caches to the host budget, complete table counts before commitment,
and count each host/device row exactly once. Avoid another full trace copy.

Relevant code is
[`streaming.rs`](../crates/aiur/src/trace/stark/streaming.rs),
[`witness.rs`](../crates/aiur/src/trace/stark/witness.rs) and the
[compression witness writer][kzg-witness]. These are preparation changes,
not improvements to native VM execution.

### 4.2 Tune grouping and shard geometry for recursive cost

Measure executed rows, group widths, padding, main/lookup/quotient cells,
opened elements per query, proof bytes and the next verifier's cost. Group
functions with compatible widths and frequencies; a rare wide member can
make every row of a hot group expensive. The compression word-stream
regression demonstrates why unpadded counts are insufficient.

Select candidates using the combined cost of the child and its recursive
parent. The normalized-wrapper experiment reduced downstream execution by
changing proof geometry, while some lower-cell layouts increased opened
columns enough to lose overall. Its fitted timings are specific to that
compression workload and must be recalibrated for Goldilocks aggregation.

Separate two decisions: partitioning environment claims changes execution
dependencies and frontier work; partitioning one execution into trace shards
changes proof geometry. The baseline used 20–22 leaf trace shards, and the
planner's nominal cell limit was 1.5 billion. A larger limit may lower shard
count, but planner fallback can choose a smaller layout; inspect the actual
selected plan and limiting budget.

Use the existing certified grouping passes and existing quotient-aware
lookup grouping. Lookup batching, device-derived lookup generation and
sliding-window LDE overlap already exist; do not count them as new gains.

### 4.3 Compare population providers

Compare CPU, generated GPU and matching compiled GPU population on a fixed
layout. Record actual per-circuit coverage and fallback reasons, not just a
mode flag. IxVM's compiled bundle registration does not establish compiled
coverage for aggregation or for regenerated word-stream artifacts.

Measure upload, device range counting, host remainder, witness stalls,
device/host peaks and total proof wall time. A GPU writer that consumes the
space needed by proving can lose through smaller shards or spilling. Preserve
the bounded witness feed and record/device admission. These writers consume
an execution record; selecting them does not move VM execution onto the GPU.

### 4.4 Retention and device memory

Compare retain/regenerate policies only where the plan and runtime support
both. The measured 22-shard leaf regenerated witnesses; the saved-root case
retained one shard. Report the resulting number of supplies and actual memory
traffic rather than assuming a policy flag took effect.

Measure the interaction between the planner's device budget and multi-stark's
memory reserve, including spills, restores, host staging and allocation peaks.
The existing zero-reserve experiment is not an adopted default. Spare sampled
VRAM alone does not justify removing admission margins.

### 4.5 Profile the cryptographic backend after host gaps are separated

Capture one GPU timeline separating CPU launch work, transfers, commitments,
lookups, quotient evaluation, polynomial openings and FRI. The reported
non-stall backend timer includes host orchestration; it is not kernel time.
Choose kernel-level work only after identifying an exposed phase.

Possible experiments include reuse of stable device allocations, further
transfer/compute overlap with accounted pinned buffers, and launch batching
for repeated shapes. Preserve phase admission and streaming bounds. The
existing LDE overlap is the starting point, so additional streams or CUDA
Graphs need evidence of residual transfer or launch gaps. Keep the production
FRI query count, blowup, proof-of-work and hash choices fixed in these studies.

## 5. Scheduling and whole command costs

The initial controller already overlaps claim execution with proving,
prioritizes ready joins and overlaps the two intermediate joins. Its exposed
waits remain after that scheduling. Increasing execution slots alone cannot
help a workload with only four ready claims.

Smaller first-wave claims could start the GPU earlier and expose more CPU
parallelism. Compare this against duplicated frontier/binding work and extra
joins on the actual critical path. Keep one GPU proving lane initially.

The compression pipeline demonstrates early preparation of independent stage
state. Apply it only where there is actual unhidden work: artifact checking,
key/plan construction or immutable metadata preparation can run alongside
execution if memory reservations cover both. The initial prover's registry
already shares programs and systems within a command. Reuse compatible
proving backends and layouts where their identities allow it; avoid rebuilding
what is already resident. Persistent layout/export caches must include the
exporter identity, input/artifact identity, parameters and layout policy, and
their output must still satisfy trusted key checks.

Instrument environment loading, role/model preparation, independent expected
statement construction, constant auditing and final verification. Reuse
independently derived metadata keyed by the environment and final manifest.
Runtime bisection can change that manifest, so recompute affected statements.
Keep independent coverage and proof checks; the controller's reported claim
is not their replacement.

If revisiting `--binding-proof`, compare both fresh proof creation and reuse
of an existing binding proof. Count extra assumptions, root discharge and
recursive proof work along with avoided leaf checks. The accepted final
environment claim must remain unconditional. Treat this as a separate policy
experiment rather than attributing its effects to word streams.

Root compaction is another explicit policy experiment. The earlier tail was
`9 -> 3 -> 2 -> 1` trace shards; its 53 seconds included the root proof as well
as wrap execution/proving. Compare a verified batch root with a compact root
only for consumers that accept both, including downstream verification and
compression costs. Do not silently change the output contract.

## 6. Changes to defer

Packed SHPLONK, fixed-base G1 optimizations, BN254 non-native arithmetic and
raw gnark proving-key loading address other backends. Their curve-point or
load-time reductions are not initial-FRI speedups.

The new Lean-exported wide/narrow layouts are useful infrastructure, but
their current compression adapters are not replacements for the initial
streaming prover. [WideBackend][wide] materializes stage-one traces before
conversion and proves a normalized single shard. Porting its circuit source
requires an incremental witness path and an explicit capacity/key policy.

A fully narrow layout can reduce opened width while increasing rows and FFT
work. The compression study's estimate of roughly 580M rows for fully narrow
CompressGL was a model, not a measured Goldilocks result. Evaluate selective
tiling against child-plus-parent cost before a wholesale backend change.
Likewise, unrolling BLAKE3 in the trace layout does not by itself accelerate
the native executor that produced the record.

A GPU VM executor or replacement transcript hash is outside the first
implementation sequence. The existing CPU/source and population machinery
provide smaller experiments with established reference paths.

## 7. Experiment plan

### Variants and workloads

| Variant | Change | Question |
|---|---|---|
| Baseline | Current native path plus the measured preparation optimization | Where does execution time go now? |
| Batched hints | Four-byte IxVM hint, existing byte lists and parsers | How much do dispatch and read checks cost? |
| Full words | Complete word path, closest valid carry-forward grouping | Does removing byte-list work improve execution and record size? |
| Full words with regrouping | Same source semantics, grouping tuned from counts | Does the execution gain survive padding and GPU proving? |
| Independent host or GPU candidate | ROM parallelism, provider or geometry change, one at a time | What extra gain remains after representation changes? |

Use the same real Init manifest leaf, a real two-child aggregation join and
the saved-root verifier for focused comparisons. The leaf needs the model
advice sidecar used by the normal CLI. Loading an `.ixe` alone omits that
advice. Record its identity and account for model preparation in fresh-command
timings. Use representative small fixtures for frequent semantic checks.

For each source variant, regenerate and independently pin its artifact,
native executor and keys. Verify that the native executor actually ran.
Do not weaken fingerprint enforcement to make an old generated kernel run.
The old host-only comparison rejects differing keys/layouts intentionally;
source/layout experiments need a separate comparison of the same logical
statement with explicit per-variant identities.

### Correctness checks

Check the word representation against a simple byte reference for all cursor
offsets and length residues. Include empty inputs, short streams, unaligned
fields, nested bounded blobs, 31/32/33-byte values, 63/64/65-byte blocks and
1023/1024/1025-byte BLAKE3 chunk boundaries. Cover XOF refill boundaries,
absorb/squeeze ordering and rejected Goldilocks challenge samples.

Exercise malformed tags, lengths, trailing bytes, out-of-range byte hints and
noncanonical field encodings. Match the specified parser acceptance behavior;
audit any existing permissive reads separately instead of silently changing
their semantics. Internal BLAKE3 padding must not become implicit padding of
a truncated serialized input.

For each new program, compare native execution with its interpreter/reference
on focused successful and failing cases. Verify real leaf and join proofs
against the expected statement, including changed-statement rejection.
Changing representation is allowed to change the record and proof. A host-only
optimization of an unchanged program should retain record/proof parity.

### Performance measurements

Record separately:

- Input, model and advice preparation; native binding; execution; destruction.
- Logical instructions, distinct queries/cache hits where available, hint
  dispatches, ROM objects, fixed-table calls and accounted record capacity.
- Executed and padded cells, widths, active circuits, selected shards,
  opened elements per query, retention, supplies and actual population providers.
- Initial validation, depth counting, population, transfers, stalls, backend
  phases, serialization and verification, with their timing boundaries.
- Host RSS, tmpfs usage, device peaks, staging, spills and pool/admission waits.
- Parent execution/proving and final independent acceptance.

The current driver's `samples` repeats proving of one retained execution.
It does not repeat CPU execution. Execution comparisons need fresh processes
or fresh records for every measured execution, with matched allocator,
inputs, model advice and settings. Alternate baseline/candidate order and
report individual observations and distributions, separating cold setup from
steady work. Three fresh executions per version are a starting comparison;
expand only if noise prevents a decision.

Reuse an immutable record for host-only preparation experiments, generating
fresh witnesses/proofs each time. Do not reuse old records for word-stream
variants or credit proof-cache hits as proving improvements. For differing
source/layouts, hold resource budgets and security parameters fixed, let valid
plans differ, and report the resulting memory and parent costs.

Builds, profiling and measurements are separate future steps. Heavy work runs
only when the host and GPU are free, checked outside a sandbox that hides GPU
or process state. Use the machine's default CPU width, one proving GPU and
isolated build outputs on disk. Never silently cap threads. Preserve partial
results if competing work requires stopping a run; restart measurements from
a clean comparison rather than treating an interrupted sample as complete.

The existing representative leaf costs roughly two to three minutes for a
fresh execution and one proof, excluding builds. The historical full Init
command costs about ten minutes, so a before/after pair is about twenty
minutes before builds or separate verification. Re-estimate those costs from
the current binaries before scheduling broader runs. Mathlib follows a
successful narrow comparison and fresh Init validation.

### Decision gates

Advance full word streams beyond the prototype only after a verified
candidate reduces execution or combined execution/proving beyond observed
variation, with a clear account of any memory tradeoff. Fewer cells or hints
alone do not pass. A claimed CPU improvement requires repeated execution
timings. Adoption as a default requires a lower fresh full-command time at
matched resource limits, preserving independent acceptance and including any
changed parent work. A CPU gain alone is insufficient if proving or the next
verifier loses the saving.

If batched hints help, they can ship independently. If they do not, full
words still merits its separate allocation/record experiment. If execution
improves but padding loses the gain, evaluate regrouping before rejecting
the representation. If neither execution nor total proving improves, retain
the baseline and use the native profile to choose the next runtime hotspot.

## 8. Implementation order

1. Preserve the preparation patch; capture native CPU profiles and the real
   join workload with current phase instrumentation.
2. Specify the word cursor, byte equivalence and transcript behavior in
   shared Aiur source. Implement the focused hint comparison and the first
   complete word path selected by the profiles.
3. Regenerate matching artifacts/executors, pass semantic checks and compare
   fresh executions. Inspect padding before selecting a small grouping set.
4. Compare execution plus GPU proving and the recursive parent. Port the
   other application path independently if its profile supports it.
5. Evaluate remaining ROM population, GPU providers, residency and geometry
   candidates using the measured bottlenecks. Measure acceptance and useful
   setup overlap alongside the whole-command study.
6. Validate fresh Init, then a larger environment, before changing production
   defaults or making an end-to-end performance claim.

## Research sources

The local compression references below identify the source/evidence snapshot
behind this proposal. Their hashes are in the research evidence record.
`target/` files are local experiment artifacts rather than tracked fixtures.

[architecture]: aiur-compression-architecture.md
[l3]: measurements/aiur-compression-l3.json
[word-counts]: ../target/streams-experiment/summary.json
[bn-stages]: measurements/aiur-packed-bn-stages.json
[wrap-results]: ../target/wrap-normalized/summary.json
[fixed-key]: ../MultiStark/MultiStark/BN/KzgPackedTerminal.lean
[stage-study]: aiur-compression-stage-study.md
[pipeline]: ../target/e2e-l3/run.sh
[kzg-io]: ../MultiStark/MultiStark/BN/KzgIO.lean
[kzg-transcript]: ../MultiStark/MultiStark/BN/KzgTranscript.lean
[kzg-hash]: ../MultiStark/MultiStark/BN/KzgBlake3.lean
[kzg-witness]: ../crates/proof-compression/src/aiur_backend/kzg/witness.rs
[wide]: ../crates/aiur/src/trace/stark/wide.rs
