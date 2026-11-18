# Single-GPU performance for Aiur proving

Status: design with an initial host implementation. The source study and
whole-Init baseline date from 2026-11-13; focused correctness checks and GPU
comparisons on 2026-11-14 are recorded in §§7–8. The preparation changes cut
median proof-generation time by 15.6% on one Init claim and 7.1% on a saved-root
verifier workload. Full-command and execution speedups remain unmeasured.

The [CPU execution and initial FRI research plan](aiur-fri-performance-research.md)
extends this design with the compression findings through 2026-11-16, a full
word-stream experiment, native execution profiling and the remaining GPU
work. It gives the next experiment order; §§7–8 below retain the completed
preparation work and its measurements.

## 1. Goal and scope

Reduce the elapsed time of fresh `ix prove` for IxVM environment claims and
their Goldilocks/FRI aggregation on one GPU. CPU execution, record preparation,
witness generation, GPU proving, recursive wrapping and final acceptance are
all in scope. GPU utilization is a diagnostic, not the objective: making the
GPU busier by doing more proof work is not an improvement.

Keep the current proof protocol, BLAKE3 transcript and production security
parameters. Reuse existing Aiur execution, incremental population, certified
compiler passes and multi-stark primitives. Distinguish host implementation
changes, which can preserve proof bytes, from source/layout changes, which
require regenerated artifacts and key identities.

BN254 KZG and PLONK compression are outside the timing target. Their recent
experiments supply techniques to evaluate, not interchangeable speedup figures.
The initial implementation uses one proving lane and the available CPU width;
it does not depend on a second GPU or concurrent prover lanes sharing a device.

## 2. Baseline and evidence

### Fresh Init run

The [recorded fresh Init run](measurements/aiur-compression-fresh-init-bn.json)
on 2026-11-13 proves 56,312 constants in four environment claims before running
compression. Only its proving phase is the baseline here:

- `prove-time`: **591.31 s**; controller reports **482 s**.
- Separate environment/manifest verification: **101.77 s**, excluded from
  `prove-time`.
- One GPU, one prover lane, `--max-ram 180`; native IxVM and aggregation
  executors matched their pinned artifacts.
- `--fresh --no-cache --no-index`: no prior proofs reused.
- Record pool: 116.0 GiB peak granted, zero growth waits, zero contention
  retries. Four claims execute concurrently, despite 32 available execution
  slots; the slot count does not imply 32 active executions.
- Source snapshot: `a3e2a04331e097928ff967ef1aea68a14a9bd444` plus the recorded
  working-tree diff. Binary, libraries and artifact hashes are in the JSON.
  The inspected active worktree is based on `4e27c5fcd` with additional work;
  do not attribute its unmeasured changes to the captured binary.

The original paths in the record name `/tmp/ix.aiur-compression-stages`.
That worktree now lives on NVMe at `~/repos/ix.aiur-compression-active`, and
the `/tmp` path is a symlink to it. The active worktree retains the
[run log](../target/aiur-bn-bench/fresh-init-pinned-grouped/run.log),
[invocation](../target/aiur-bn-bench/fresh-init-pinned-grouped/invocation.json)
and [GPU samples](../target/aiur-bn-bench/fresh-init-pinned-grouped/gpu.csv).
These `target/` links are local research artifacts, not tracked fixtures.

The critical path reconstructed from the controller's rounded timestamps is:

| Controller interval | Work on the critical path | Approximate wall time |
|---|---|---:|
| 0–100 s | Initial claim execution before the first GPU proof | 100 s |
| 100–304 s | Four claim proving slots, including preparation and population | 204 s |
| 304–337 s | First intermediate join proof; other join executes concurrently | 33 s |
| 337–365 s | Wait for the other join's execution | 28 s |
| 365–398 s | Second intermediate join proof | 33 s |
| 398–429 s | Root execution | 31 s |
| 429–482 s | Root proof and subsequent wraps | 53 s |
| Outside the controller timer | Loading/setup and final acceptance, not separately timed | 109 s |
| Total command | | **591 s** |

The four leaf executions each take 100.6–104.8 s, but overlap; adding them
would not describe elapsed time. The two intermediate joins execute for about
60 s each, partly hidden behind GPU work. At least 159 s of the controller
timeline is exposed waiting for initial, join or root execution, before
counting execution inside the wrapping tail.

The proof summaries total 204.9 s of backend time excluding witness stalls,
and 46.0 s of witness stalls. The backend time includes host orchestration;
it is not a GPU event measurement. `trace_seconds` includes preparation and
witness builds, including work overlapped with proving, so it must not be
added to `proving_seconds` to obtain command time. See
[streaming timing](../crates/aiur/src/trace/stark/streaming.rs).

The sampled GPU utilization averages approximately 31% over the window
10–600 s after the outer benchmark launch, with a peak sampled allocation of
67,365 MiB. This window approximates the proving command; it is not aligned
to individual kernels, and utilization is not SM occupancy. A separate host
probe found one RTX PRO 6000 Blackwell with about 96 GiB VRAM and 32 available
CPUs. These observations motivate measurement of CPU gaps and memory policy;
they do not establish how much additional device workspace is safe.

### Relevant existing techniques

| Evidence | Established result | Relevance here |
|---|---|---|
| [Word streams](../target/streams-experiment/summary.json) | Packed BN verifier: 147.5M → 105.3M padded main cells; transcript/digest bytes preserved | Source representation can reduce execution and trace work together; no Goldilocks timing claim yet |
| [Native execution](formal-aiur-native-execution.md) | Historical profiles identify table counting, generated-code footprint and memoized calls as remaining costs | Native execution and closed-form byte-table evaluation already exist; optimize their remaining work |
| [Batch preparation](formal-aiur-gpu-preparation.md), [ROM reuse](formal-aiur-rom-reuse.md) | Removing redundant reconstruction and copying improved earlier adapters | Apply the same principle to repeated record validation and depth preparation |
| [Certified grouping](formal-aiur-grouping-tuning.md) | Fewer columns/proof bytes, but some large-input trace timings regressed | Optimize measured execution/proving and next-verifier cost, not columns alone |
| [Incremental traces](formal-aiur-streaming-traces.md) | Packed shards and a bounded witness feed already avoid whole-trace residency | Extend the existing pipeline; do not reintroduce full-trace intermediates |

## 3. Measurement contract

Expose per-job timings and counts through the existing `PopulationReport`
and controller reporting path. The hot path should aggregate counters and
emit summaries, not log every row or query.

Record separately:

- Environment loading, statement preparation and final independent acceptance.
- Advice preparation/binding, VM execution, record finalization and destruction.
- Planning, full record validation, depth-range counting and device upload.
- Per-round witness allocation/fill, provider selection and witness stalls.
- Backend commitment, lookup, quotient, opening/FRI and proof serialization.
- Each root wrap's execution/proving time and its input/output shard counts.

Also capture native-executor fingerprints, actual host/generated/compiled
population coverage and fallback reasons, record bytes, padded/committed cells,
shard counts, pool waits, host RSS, device peak and spill/restore traffic.
Record tmpfs usage alongside RSS. On the measurement host `/tmp` is a 125 GB
tmpfs that counts against RAM: a session was OOM-killed on 2026-11-13 partly
because a worktree and large outputs lived there. Keep worktrees, `target/`
and run artifacts on NVMe.
Use a common monotonic timeline to distinguish resource contention from lack
of ready work. Do not infer a component's cost by subtracting overlapping
phase medians.

Begin with CPU counters for one representative leaf and one join and an
Nsight Systems timeline for a representative proving interval. Use kernel
profiling only after the timeline identifies a GPU bottleneck. NVIDIA's
[profiling guidance](https://developer.nvidia.com/blog/understanding-the-visualization-of-overhead-and-latency-in-nsight-systems/)
distinguishes CPU launch, transfer and GPU execution overhead; profiler
overhead itself must be excluded from reported speedups.

## 4. Proposed work

### A. Validate immutable records once and reduce depth preparation

`timed_witness` calls `validate_record_shape` on every supply. Despite its
name, that check scans every function's depth array, not just dimensions.
It also runs during planning through `record_rows` and other entry points.
See [streaming.rs](../crates/aiur/src/trace/stark/streaming.rs) and
[trace.rs](../crates/aiur/src/trace.rs).

With the current regenerate schedule, a K-shard proof supplies witnesses
`2K - 1` times: round one retains its last commitment for the beginning of
round two. The retention choice is made in
[streaming.rs](../crates/aiur/src/trace/stark/streaming.rs)
(`RetentionPolicy::Regenerate`, `requires_regeneration`), and each supply
goes through `timed_witness`. A 20-shard claim therefore performs at least 39 whole-record
shape checks through this path. The ten proofs in the baseline require
240 supplies in total. This is an avoidable factor proportional to the
shard count; its elapsed cost has not been isolated.

Introduce a validated preparation object tied to the exact trace plan and
the lifetime of an immutable execution record. Its private construction
performs full validation once and caches row counts/member spans. Planning
candidates and witness suppliers consume that object. Retain cheap plan
identity and shard-local checks at API boundaries, including rejection when
a prepared record is passed to a different backend. No public unchecked
entry point should replace the validation contract.

The depth-range prepass is another candidate. `depth_ranges` fills every
gapped function row to count fixed-table uses, parallel across functions
but serial within each function. Ordinary population fills those rows again.

First parallelize row chunks with worker-local scratch/counts and an exact
reduction. Then evaluate a depth-only population plan that computes only
guards and arguments needed by the depth slots. If caching depth results is
useful, charge the cache to the host budget and store only the required
columns/counts, not a second full trace. Counts must be complete before the
fixed-table commitment, and GPU-counted rows must not also be counted on the
host. Parallel ROM-row population is a further small candidate if its phase
timing warrants it.

This is a low-risk candidate: bounded scope, existing reference writers, and
no required circuit or protocol change. Its expected gain may be small: the
repeated scans compare depth values over the rows, so even 39 scans per claim
may cost only seconds. Stage 0's timeline decides whether it comes first;
low risk alone doesn't put it ahead of the exposed execution waits (§I) or
the unattributed acceptance time (§F).

### B. Evaluate word streams for IxVM and Goldilocks aggregation

The [word-stream design](aiur-fri-performance-research.md#33-full-word-streams)
specifies the representation, correctness conditions and measurement matrix
for both applications. Four-byte hints are a smaller ablation; their result
does not decide whether removing byte-list allocations is worthwhile.

[StarkIO](../MultiStark/MultiStark/Modules/StarkIO.lean) currently performs a
hint, recursive call and list allocation per byte. Key deserialization and
[transcript construction](../MultiStark/MultiStark/Modules/Transcript.lean)
also manipulate byte lists. The BN experiment replaces that representation
with range-checked UInt32 words and a byte cursor, while preserving the
bytes consumed by BLAKE3 and the native verifier.

Port that design to aggregation's key, proof, claim and transcript paths.
Use UInt32 words or explicitly checked limbs: an arbitrary UInt64 is not
automatically a canonical Goldilocks field element. Specify byte order,
length, partial final words, cursor transitions and out-of-range reads.
Preserve transcript rejection sampling and every byte absorbed or squeezed;
untrusted wider hints must be constrained just as the byte hints are.

The intended benefit is fewer VM calls, memory cells, query-table operations
and trace rows. Smaller child proofs can then reduce parent execution and
proving again. The BN experiment's roughly 29% cell reduction is evidence
for the technique, not a promised speedup on this path.

The BN result motivates this port but doesn't predict its effect: the
decision gate is a measured reduction in execution plus proving time on one
representative aggregation join, not a cell count.

Validate native and Aiur parsing/hash/challenge results against the existing
implementation, including malformed encodings and all tail lengths. Source
changes alter bytecode and circuits: regenerate native kernels, trace writers
and key identities explicitly. Equality of consumed proof/transcript bytes
does not imply equality of the newly generated outer proof bytes. Evaluate
IxVM and aggregation separately, using their profiles to choose port order.
Preserve the aggregation proof parser's existing indexed batched reads.

### C. Target native execution's remaining hot operations

The baseline already uses native IxVM and aggregation executors. Closed-form
byte-table evaluation and flat query storage are also implemented. Do not
credit those existing mechanisms as proposed gains.

The historical native-execution profile reports 73M of 195M retired
instructions in `Runtime::begin` for one small IxVM claim, and instruction-cache
pressure in generated BLAKE3 code. These are useful leads, not current
whole-Init percentages. Profile fresh leaf and join executions separately.

Candidates, conditional on those profiles:

- Prebind access to fixed-table counters instead of repeatedly traversing
  runtime/query/map structures in `count_map`.
- Reduce generated hot-code footprint, retaining compact error paths and
  evaluating repeated sequences against instruction-cache measurements.
- Reduce memo lookup/probe/insertion overhead in `Runtime::begin` and
  `QueryTable`, including unnecessary work before dense-index hits.

Preserve exact key equality, pending-query/cycle handling, multiplicities,
depth recording, rejection behavior and storage reservations. Host-native
hashing cannot simply replace an Aiur hash call without producing all the
queries and counts its proof needs. Compare complete records and proofs
with the interpreter/reference path. Earlier constant-arity unrolling gave
inconsistent results, and small historical variations of up to roughly 15%
were attributable to code layout; use paired measurements, not one run.

### D. Choose shard geometry for total recursive cost

The baseline's leaves have 20–22 trace shards, intermediate joins 13–14,
and the first root proof nine. The planner starts from a fixed
`AIUR_TRACE_SHARD_MAX_CELLS = 1.5e9`; host workspace is derived from that
bound. Every additional child shard increases the parent's proof input and
verification work, not just the current proof's overhead.

Evaluate geometry against:

```text
total cost = leaf execution/proving
           + join execution/proving
           + root execution/proving/wrapping
```

Using one retained execution record, compare planned layouts under a small
set of justified cell/workspace budgets before proving candidates. Report
which constraint selected each layout. Account for planner halving: raising
an initial cap can trigger a smaller fallback candidate, so a larger flag
does not necessarily produce larger shards. Test the resulting child proof
in its parent before accepting a local proving improvement.

Review the interaction between Aiur's device budget and multi-stark's
standing 25% free-memory reserve. The local
`~/repos/multi-stark.zero-reserve` experiment removes that standing reserve
while retaining phase admission; it is not a validated default. Measure
spill/restore traffic, phase peaks and host spill capacity before changing
it. Retain device admission and host reservations, and avoid treating sampled
peak VRAM as a complete allocation bound.

Changes to environment partitioning need a separate whole-run comparison.
More claims can expose CPU parallelism and start the GPU earlier, but also
duplicate frontier/binding work and add joins. The baseline already starts
all four claims and has no pool contention; increasing `--exec-jobs` alone
does not address its idle intervals.

### E. Exercise existing GPU population before adding new machinery

The recorded build enables `parallel,cuda,native-executors,net`, but omits
`formal-compiled-trace`. Without an explicit population override, that build
uses host population. The captured feature list alone does not prove the
actual runtime provider; future baselines must record it explicitly.

First compare host population with `AIUR_GPU_TRACE=generated` using the
existing CUDA build and a fixed layout. Evaluate compiled writers only with
matching generated artifacts. The controller currently registers IxVM's
bundle; aggregation needs its own coverage or generated fallback.

Record per-circuit selection and `device_layout` refusals: the planner can
retain host population when the uploaded record would not fit the host-chosen
layout. A mode flag is not evidence that expensive circuits moved to the GPU.
Include upload and range-counting costs and memory pressure in the comparison.
The earlier [GPU guide](aiur-gpu-proving.md) reports only about 2% overall
improvement from compiled population on Init; it is not a forecast for this
binary or layout.

The pinned multi-stark revision `bcf3fc8e902b1f7176254f6e87a1101ed785248f`
already includes sliding-window LDE overlap. Device-derived lookups and the
bounded witness feed are also present. Further transfer overlap or CUDA
Graphs should follow a timeline showing residual transfer or launch gaps.
[NVIDIA's transfer guidance](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/)
requires suitable pinned buffers and streams for host/device overlap; adding
streams without admission and staging accounting is not the proposed change.

### F. Reuse independent acceptance preparation

About 109 s of the baseline command lies outside the controller timer. The
log shows final coverage acceptance after the controller returns, and a
separate verification command takes 101.77 s, but there is no measurement
that attributes all 109 s to one function.

[FormalAggregate.accept](../Ix/Cli/FormalAggregate.lean) reloads the environment
and manifest, reconstructs the expected statement, audits constants and
verifies the returned proof. Cache independently derived environment metadata
within the process, including parsed constant classification and ownership
data, and reuse it where possible. Instrument loading, reconstruction and
audit separately before choosing the exact implementation.

Acceptance must still use the actual final manifest: runtime bisection can
change it. Bind reusable data to environment/manifest identities and rebuild
the affected statement when the partition changes. Never replace independent
coverage or proof verification with the controller's reported result.

### G. Make root compaction an explicit output policy

The lane controller wraps toward a single trace shard even when the consumer
can verify a batch. The baseline's root follows `9 → 3 → 2 → 1`; its 53-second
tail includes the original root proof, wrap execution and wrap proving.
The whole 53 s is not removable wrapping overhead.

Measure an explicit choice between a verified batch root and a compact root.
Keep the same expected claim and perform independent verification in both
cases. Report proof size and downstream verification/compression cost as well
as saved proving time. Do not silently change the default or force a consumer
that requires a compact shape to accept a different representation. This is
a policy experiment after wrap timings are available, not a claimed speedup.

### H. Reuse certified grouping and specialization selectively

Retune grouping on representative leaf and recursive workloads using padded
cells, population time, quotient work and next-verifier cost. The earlier
grouping results demonstrate that fewer columns can coexist with slower
population, so a column-only objective is inadequate.

For stages with a fixed predecessor key and shape, the preferred route is a
preprocessed verifier plan: fixed tables committed in the stage's own key,
read by an adapted Aiur verifier whose equivalence to the generic path is checked
([aiur-structural-gap.md](aiur-structural-gap.md) §5a). It applies only where
the key dependency is acyclic, such as a verifier of a fixed IxVM key. Pinning
a self-recursive aggregator's own newly generated key creates a circular
dependency; a staged key ladder is a distinct design. Source-to-source
specialization of verifier programs is not part of this plan. Retain dynamic
shapes where fixing them would add costly normalization.

Packed KZG/SHPLONK, Fq arithmetic and terminal PLONK gate optimizations address
other stages. Their dramatic curve-point savings do not directly accelerate
the Goldilocks/FRI prover. A new GPU VM executor or a new transcript hash is
not part of the initial work.

### I. Reduce exposed execution latency

VM execution is the largest exposed cost in the baseline:

- **Waiting:** at least 159 s of the controller timeline waits for leaf,
  join or root execution.
- **Idle GPU:** the GPU averages about 31% sampled utilization.
- **Few executions:** only four claims execute concurrently, with 32
  execution slots available.

Section C's native-execution profiling addresses per-instruction cost. Two
structural levers belong here as well:

- **Improve dependency order where evidence permits.** The controller
  already dispatches ready joins first, and both intermediate joins overlap
  proving in the baseline. The 159 s is the residual wait after that overlap,
  not a pool of time recovered by enabling it. A scheduling change must
  identify a ready task that could run earlier and show how that shortens
  the critical path; initial execution and root dependencies remain.
- **Partition for an earlier GPU start.** Smaller first-wave claims begin
  proving sooner and spread execution across more cores. This trades against
  duplicated frontier/binding work and extra joins (§D), so measure it as a
  whole-run comparison.

Scheduling alone can preserve proof bytes. Repartitioning changes leaf
claims, frontiers, the aggregation tree and proof identities; the invariant
is the final expected environment statement. Fresh records and verified
proofs of that statement are still required.

## 5. Rollout and validation

| Stage | Deliverable | Decision gate |
|---|---|---|
| 0 | Per-job timeline and provenance; isolate one leaf, one join and one wrap | Distinguish VM, preparation, stalls, backend and acceptance costs |
| 1 | The largest exposed cost from stage 0: candidates are acceptance reuse (§F), execution overlap and partitioning (§I), and validate-once preparation with row-parallel depth counting (§A) | Host-only changes: same records and layouts, verified byte-identical proofs. Scheduling changes: verified proofs of the expected statement. Both need a measured reduction beyond noise |
| 2 | Full word streams for IxVM and Goldilocks aggregation | Parser/transcript parity and regenerated artifacts. Measure fresh executions, padding, proving and parent costs separately for each application |
| 3 | Profile-guided native changes and remaining stage-1 candidates | Preserve reference behavior and independent acceptance; gains exceed observed noise |
| 4 | Geometry, residency and population-provider comparisons | Improve child-plus-parent cost within host/device budgets |
| 5 | Optional root policy, broader grouping or preprocessed verifier plans | Demonstrate total pipeline benefit and explicit identity/output-policy changes |

For local host changes, execute once and reuse an immutable record to compare
preparation/proving with identical layouts and parameters. Generate a fresh
witness and proof each time; do not count proof-cache hits as a speedup.
For executor changes, use fresh records and report cold-start and steady
behavior separately. For geometry or source changes, verify the same expected
claim and measure changed parent costs rather than requiring identical bytes.

Use focused correctness checks for malformed records, wrong-plan preparation,
depth/count mismatches, padding, stream bounds, canonical decoding and
transcript edge cases. Preserve CPU/CUDA verification parity. Preserve native
fingerprint enforcement and record-pool/device admission. No security
parameter reduction or weaker acceptance check qualifies as an optimization.

Measure full fresh Init only after a candidate passes the narrow comparison.
Then validate a larger environment, preferably Mathlib, because recursion
depth, frontier duplication and contention can change the ranking. Record
before/after distributions, the critical path, memory, proof size and all
changed artifact/backend identities. Do not add speedups from overlapping
optimizations or extrapolate BN cell reductions into Goldilocks wall time.

The baseline costs about ten minutes per fresh Init proof command, so one
before/after pair is roughly twenty minutes before extra verification or
builds. Cold artifact/native/CUDA generation can add minutes. State the
estimated cost and obtain agreement before long builds, full runs or sweeps.
Once authorized, use the machine's default CPU parallelism; do not silently
cap jobs, Rayon threads or affinity. Record other activity and run paired
performance samples on an otherwise idle device and host.

Acceptance for an adopted change requires a verified proof of the expected
statement, measured elapsed-time improvement beyond run-to-run variation,
bounded memory without new contention failures, and no hidden transfer of
work into a downstream stage. The preparation candidate has passed the
narrow comparisons in §8. The next profiling, word-stream and GPU experiments
follow the [extended research plan](aiur-fri-performance-research.md);
execution and full-command improvements require their own measurements.

## 6. Phase reporting

`IX_PROVER_PROFILE=1` enables JSON records on stderr with prefix
`[prover-profile]` and schema `ix-prover-profile/1`. The usual progress output
and stdout proof address retain their formats. Detailed provider/candidate
reports are serialized only when profiling is enabled.

The aggregate backend emits:

- `execution`: advice/witness and hint preparation, the executor that
  actually ran, VM elapsed time, instruction/query counts, charged record
  bytes and binding-release time.
- `proof`: planning, encoding, backend wall time excluding witness stalls,
  the population report, actual population providers and host fallback
  causes, and planner candidates/budgets.
- `record_release`: elapsed time to destroy an execution record after proving.

Rust events carry `call_id`, the hash of the entry and canonical public
arguments, and elapsed time since the resident backend was created. A root
and its wraps can share a call ID; use event order and controller task logs
to distinguish those attempts. This elapsed clock is local to that backend,
not a timestamp to compare across separate processes.

The population report separates layout checks, full record validation,
metadata preparation, device upload, host depth-range counting and auxiliary
counts. Per-shard and per-round totals also expose repeated validation time.
Upload includes the device's range-counting work; the separate depth-range
phase covers the remaining host work and merging counts. Preparation phases
are sequential, while witness allocation/fill thread-seconds can overlap.

The Lean acceptance path emits `acceptance` with manifest/loading,
statement reconstruction, constant audit, native verification and total
durations. These retain all independent acceptance checks. Together with
the controller timer, they distinguish VM/proving costs from the final
host audit. Store captured stderr on disk rather than in a large tmpfs run
directory. Profiling data diagnoses candidates; use unprofiled paired runs
to establish the final speedup.

For a narrow measurement without rebuilding the Lean CLI, use the
[single-proof driver](../crates/ix-prover/examples/profile_proof.md). It
profiles a pinned program on a real manifest leaf, a saved invocation or an
exported STARK, with explicit record/workspace limits and the CLI's allocator.
It retains one execution across fresh proof samples, verifies every result
and records input hashes and detailed population timings. It does not replace
the full controller/acceptance measurement.

## 7. Preparation candidate

The working implementation binds each `PreparedRecord` to a private identity
of the backend that validated it. Repeated witness supplies check that identity
and their local dimensions instead of rescanning the immutable record's depth
arrays. The identity survives moving the backend, and preparations from a
different backend are rejected even when its verifying key is identical:
placements and device allocations belong to the preparing backend.

Full record validation remains at preparation, and public planning methods
still validate records received without a preparation. Preparation derives its
row counts from the already validated record, avoiding another scan there.
This removes the per-supply whole-record scan; it does not claim to remove
every repeated check across independent planning API calls.

Depth-range counting now distributes rows within each gapped function, using
worker-local scratch and histograms. Reductions combine exact integer counts
and release completed histograms without retaining one result per function.
A minimum task grain amortizes histogram initialization; the Rayon thread
count remains unchanged. The serial implementation remains available.

Focused regressions cover rejection of preparations from another backend,
reuse after the owner moves, rejection of out-of-field recorded depths, and
reference-trace parity for a recursive execution spanning multiple row batches.
Existing streaming tests compare complete proofs against the independent
full-trace path across layouts and retention policies. On 2026-11-14, all 16
streaming tests passed with `parallel`, and all 16 passed in the serial
`stark` configuration. The integrated profiling example passed `cargo check`
with `parallel` and a release build with `cuda,native`. The modified Lean
acceptance module also typechecked against the existing dependency artifacts.
These are focused checks; no full workspace suite or fresh whole-Init
comparison has been run for this implementation.

## 8. Initial measurements

The [measurement record](measurements/aiur-single-gpu-preparation.json) contains
the individual samples, input and binary hashes, parameters, execution counts,
plan summaries and memory measurements. Full JSONL reports remain under
`target/single-gpu-research/` in the isolated `perf/aiur-single-gpu` worktree.
The base is `4e27c5fcdaef0a7258e4e42693c695881a19e5e9`. The control has the same
instrumentation and profiling driver; only the preparation implementation in
`stark.rs` and `streaming.rs` differs within each comparison.

Two inputs were measured:

- **Init claim:** original manifest shard 0, with 18,698 owned constants
  reported by the driver. Native IxVM execution produces 232,362,784 query
  rows. Its plan has 22 trace shards, regenerate retention and pipelined
  population: 43 witness supplies per proof.
- **Saved-root verifier:** `MultiStark::verify_multi_stark_proof` checks the
  exported Init root STARK. Native verifier execution produces 7,370,239 query
  rows. Its outer proof uses one retained trace shard and one witness supply.
  This exercises recursive verification, not a two-child aggregation join or
  its structural discharge.

Each version executes its input once and then generates three fresh witnesses
and proofs from the immutable record. The control runs before the candidate.
Sample 0 is the first proof in that process; later samples reuse execution and
backend setup. They do not reuse witnesses or proofs. All 12 proofs verify,
and proof digests match across all six samples of each workload. Program/key
identities, security parameters, instruction/query counts, exact layouts,
retention and population providers also match. The claim proof remains
37,328,905 bytes, and the verifier proof remains 5,232,186 bytes.

Runs use one RTX PRO 6000 Blackwell, all 32 available logical CPUs, the CLI's
mimalloc allocator, host trace population (`AIUR_GPU_TRACE=cpu`) and device
lookups (`AIUR_TRACE_ONLY_LOOKUPS=1`). Limits are 64 GiB for counted records,
about 24.3 GiB for proving workspace and 1.5 billion committed cells per shard.
An external host/GPU check gates heavy work and stops it if competing work
starts. No profiler or thread cap is applied during the paired samples.

All times below are seconds; proof-phase values are medians of three samples.
The timers overlap, so the rows must not be added.

| Metric | Init control | Init candidate | Verifier control | Verifier candidate |
|---|---:|---:|---:|---:|
| Proof-generation wall time | 49.341 | 41.627 | 2.263 | 2.101 |
| Preparation before supplying witnesses | 9.215 | 4.470 | 0.230 | 0.073 |
| Host depth-range counting | 7.599 | 3.045 | 0.190 | 0.028 |
| Summed per-supply validation | 9.050 | 0.0000068 | 0.0021 | <0.000001 |
| Witness stalls | 9.829 | 3.384 | 0.552 | 0.553 |
| Backend time excluding witness stalls | 30.325 | 33.621 | 1.472 | 1.472 |

The Init claim's wall-time reduction is **7.714 s (15.6%)**. Its control
samples span 49.269–49.370 s; candidate samples span 41.482–41.671 s. The
saved-root verifier's reduction is **0.161 s (7.1%)**, mostly from depth
preparation. These compare the combined preparation changes, not an ablation
that isolates each optimization's contribution.

The Init non-stall backend counter rises even as total wall time falls. It
includes host orchestration and reflects the changed overlap with population;
it is not a GPU-event measurement. The removed scans' nine seconds and the
depth reduction cannot be summed into a predicted wall-time saving. A GPU
timeline would be needed to attribute the backend-counter change further.

Init peak RSS rises from **42.75 to 44.54 GiB**. Counted record-pool peaks are
identical at 30.25 GiB, and both reservations return to zero after release.
The verifier's peak RSS is approximately 8.27 GiB in both versions. Thus the
claim timing gain carries about 1.8 GiB more observed host residency; it is
not a demonstrated memory saving. The configured record/workspace limits
are accounting and planning bounds, not a process-wide RSS cap.

Execution takes **92.20 / 91.45 s** for the control/candidate Init claim and
**3.242 / 3.244 s** for the verifier. These are single observations from
unchanged executors, not evidence of an execution optimization. Proof timings
exclude input/model preparation, program setup, execution, verification,
serialization and destruction. A fresh full `ix prove` comparison, an actual
aggregation join and Mathlib remain unmeasured.

The leaf driver must load model advice separately: `.ixe` deliberately omits
it, while the Lean CLI generates and attaches it before execution. The
`profile-proof-models` helper exports that existing Lean advice; the driver
hashes and decodes it through the ordinary Rust loader. An initial attempt
without the sidecar failed on a missing modeled-block hint before proving and
is excluded from the measurements. Model export and environment loading took
about eight seconds together in the helper; reuse of that input must not be
credited as an improvement to a fresh command.

The next performance work should profile native execution on a leaf and a
real aggregation join, and collect the newly instrumented independent
acceptance phases. The claim still spends roughly 92 seconds executing before
GPU proving can begin. Preserve this host improvement, but use those profiles
to choose between native hot operations, word streams, acceptance reuse and
partitioning. A paired full fresh Init run is the gate for an end-to-end claim;
the narrow samples do not establish that result.
