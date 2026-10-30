# A single automatic proving heuristic for Aiur

Status: proposed implementation and validation plan, based on research on
2026-10-30. No implementation or benchmark run is authorized by this document.
Implementation target: `kzg-bn254`, reviewed at `2f956090`. This plan uses
that branch's `multi_gpu` scheduler and integrated checking-to-PLONK
terminology. [Retained calibration evidence](../Benchmarks/BackendResults/aiur-sharding-20261030/README.md)
includes successful runs, the failed Init attempt and FLT's per-leaf data.

Use the CUDA heuristic as the starting point: its calibration comes from real
Mathlib proofs. Combine it with dependency-aware partitioning, measured trace
shapes, and the existing memory admission machinery. The result should be one
automatic policy for `ix shard` and `ix prove`, without requiring users to
choose shard counts or select between competing cost models.

## Resource policy

Initial environment partitioning must use **total physical system RAM**, read
from `MemTotal`, and the GPUs selected for the run. It must not use transient
`MemAvailable` or the benchmark's cgroup cap. The cgroup limit is a separate
runtime constraint: it limits admitted work and protects the machine.

| Machine | GPUs | System RAM | Runtime cap for validation |
| --- | ---: | ---: | ---: |
| Current g7e.8xlarge | 1 | 256 GiB advertised; about 249.69 GiB in `MemTotal` | 230 GiB |
| g7e.24xlarge | 4 | 1,024 GiB advertised; use actual `MemTotal` | Proposed 920 GiB |

AWS specifies 96 GB GPU memory per GPU, so these machines have similar host
RAM per GPU. Read actual device capacity at runtime; do not treat advertised
GB as GiB. Instance specifications are from the
[AWS G7e instance table](https://aws.amazon.com/ec2/instance-types/g7e/).

With approximately the same RAM per GPU, the initial partition should remain
in approximately the same size range on these two machines. Four GPUs should
primarily allow more concurrent proving, rather than making environment
shards four times larger. Smaller workloads may need additional subdivision
for useful parallelism, but only when the expected benefit exceeds duplicated
dependency work and aggregation overhead.

Do not cap Rayon or other CPU thread pools. Keep normal CPU parallelism and
control the number of resident executions/proofs through memory admission.

## Evidence and current inconsistencies

The current CUDA seed in `crates/kernel/src/shard.rs` is approximately:

```text
shards = round(78 × serialized_block_bytes / 1,468,041,216
                  × 41.4 GiB / target_record_share)
```

It is clamped to the number of available work blocks. This is a useful seed,
not a bound on peak memory. Dependency overlap, arithmetic-heavy checks,
retained execution records, and recursive verification can change the cost.

| Evidence | What it establishes |
| --- | --- |
| September Mathlib: 78 environment shards, four GPUs | A useful measured calibration point. One run took 36min00s; 102 shards with different execution concurrency took 36min20s. More shards were not automatically faster. |
| October Mathlib: 80 environment shards | Records averaged 25.14 GiB, with a 37.45 GiB maximum. This is the current scale to preserve approximately. |
| Historical Init: 3 environment shards | The count was chosen automatically from about 66.71 MB of block bytes, a 200 GiB planning budget, and a 49.9 GiB record share. It was not a manually selected count. |
| Fresh Init rerun: 3 environment shards | Failed after 17min07.47s at the 128 GiB record ceiling during root wrapping. It did not hit the 230 GiB cgroup cap or an OOM event. Matching environment shard count did not reproduce the successful internal trace behavior. |
| Historical FLT: 572 environment shards | Mean record size was about 32.05 GiB, but the largest was 174.24 GiB. Serialized bytes alone miss expensive arithmetic tails. |

Simply substituting total RAM into the current formula is insufficient. For
the October Mathlib input, the recorded 180 GiB budget produced 80 shards;
230 GiB would produce about 61, and this host's `MemTotal` about 55. Those last
two numbers are arithmetic evaluations, not new benchmark results. Changing
the resource input requires recalibrating the reference and reservation model.

Several paths currently disagree:

- `ix shard` without a profile requires a shard count or RAM argument, while
  the profiled path can default to total system RAM.
- Static planning defaults to three execution jobs. The multi-GPU executor
  defaults to CPU cores divided by GPU count.
- The shared trace-cell accessor defaults to zero, while multi-GPU proving
  defaults to 1.5 billion cells. Planning can therefore omit workspace that
  proving actually reserves.
- Runtime budget discovery uses 85% of `MemAvailable`. The failed Init run
  consequently used an effective budget of about 202.2 GiB inside a 230 GiB
  cgroup.
- The profiled RAM-to-cost path retains coefficients calibrated for ZisK.
  It is not a current Aiur calibration, despite using total RAM by default.

## Proposed changes

### 1. Share resource discovery and planning

Consolidate policy in the existing Rust modules and expose the same result to
the CLI and executor. No new crate is needed. Resolve once:

- Physical host RAM, selected devices, and each device's actual VRAM.
- Trace-generation mode, lookup-witness mode, and effective trace-cell limit.
- Persistent process memory: the loaded environment, ownership/frontier
  structures, shared tables, caches, and allocator/runtime allowance.
- Per-device workspace, retained-record allowance, and recursive-work reserve.
- Initial environment partition target and runtime admission limits.

Use a stable physical-resource model for partitioning. Apply the cgroup cap
and any explicit runtime memory limit when admitting work. A lower cap should
reduce concurrency before forcing a different environment partition. If an
individual unit cannot fit, automatically refine it where possible or report
the specific unsplittable constraint before committing to a long proof.

Keep distinct fields for physical resources and enforced limits; reporting
one ambiguous "RAM budget" makes these failures hard to diagnose. Make the
normal CLI invocation automatic rather than requiring `--shards` or
`--max-ram` to obtain a partition.

Use one plan-and-prove entry point for every automatically selected shard
count. A one-shard partition is the smallest instance of the same scheduler,
record pool, memory admission and trace-sizing policy used for larger
partitions. Remove the `nonempty == 1` dispatch to `proveOneShardRoot`; the
user should never select a single-shard versus multi-shard execution path.
For one leaf, the scheduler has no binary joins to schedule, while root
wrapping and final compression follow the same resource policy. Runtime
refinement can turn one initial shard into several within that same pipeline.

Implement this in the Rust scheduler before removing the CLI dispatch. The
current scheduler requires the root plan operation to be a binary join and
waits for both `root_left` and `root_right` to become ready. Represent
the root input explicitly as either one proven leaf or a join. A singleton
must wrap its IxVM proof into the expected aggregate claim using the shared
record pool and workspace policy, without inventing a second child or
re-executing an already completed leaf.

Persist the actual refined manifest and expose its location as part of the
run's output. Test singleton completion, one-to-many refinement, restart from
the refined partition, and independent verification against that partition.
Require exact coverage, no unresolved assumptions, and agreement between the
final claim and the verifier's reconstruction. Tests must exercise the real
root scheduling path, including a leaf with multiple internal trace shards.

### 2. Recalibrate the CUDA seed and retain dependency-aware partitioning

Start with the existing byte-based seed and dependency-aware min-cut
partitioner. Refit the target record size and reservation assumptions using
the current Mathlib representation and measured records. Do not copy the old
41.4 GiB share unchanged into a different memory model, or encode special
cases for named corpora.

Use a provisional **70–100 Mathlib shards** as a regression review range around
the validated roughly 80-shard result. This is an acceptance signal, not a
hard-coded output. A result outside the range needs an explanation supported
by memory and end-to-end measurements.

The heuristic should retain one environment shard when the workload fits and
subdivision offers no demonstrated benefit. Nat and Array are regression
examples of this decision, not named special cases. Init's historical three
shards are a comparison point, not a requirement; its count is also selected
automatically.

If an execution profile exists, use it to refine this same model. Historical
FLT data suggest arithmetic counters are useful: adding `nat_arith` improved
record-size prediction, including the largest observed shard. Other tails
were still underestimated by roughly 2×. Validate such features on held-out
workloads before adopting coefficients, and retain runtime memory checks.

Remove the legacy ZisK coefficients from the active Aiur selection path.
Retain useful dependency/frontier accounting and measured shape calculations
without restoring the old research planner framework.

### 3. Plan internal traces and recursive work together

Environment shards and trace shards solve different problems. An environment
shard selects checks and their dependencies. Trace shards divide the resulting
trace into GPU-sized proofs. Excessive trace subdivision increases the number
of proofs that recursion must verify.

Use `peak_prove_bytes`, `shard_host_workspace`, and `plan_shards_within` to
validate predicted GPU and host allocations against actual padded circuit
shapes. Recheck their allocation assumptions against the current prover.

Resolve lookup-witness behavior consistently. `AIUR_TRACE_ONLY_LOOKUPS=1`
avoids materializing CPU lookup payloads; CUDA derives them from the committed
trace. This can work with CPU-generated main traces. It is separate from
`AIUR_GPU_TRACE=generated`, which requires the generated-trace build feature.
Validate the lookup mode independently before deciding whether generated main
traces should become the default.

The failed Init run reduced claim trace limits to 375 million cells and join
limits to 187.5 million. Its root accumulated 476 trace shards before root
wrapping exceeded the record ceiling. A successful planner must account for
the consequences of those reductions, not merely show that each leaf fits.

Include joins and root wrapping in the same admission and sizing policy.
Specify separate recovery actions for execution records and recursive
verification records. The current scheduler can bisect an oversized
environment claim; it cannot fix an oversized join or root by applying that
same operation. Memory admission can serialize work, but cannot make an
individual oversized recursive execution fit.

Use bounded groups of trace proofs for recursive verification when a direct
join or wrap is predicted to exceed its record allowance. Reuse or generalize
the existing range-tree wrapping machinery so each group and each subsequent
join has its own admission and size check. Its current leaf-wrapping support
does not by itself provide this fallback for aggregate roots. Preserve the
original statement, complete trace coverage and lookup residual accounting
through the grouped verification; do not discard shards or weaken the claim.

If a group's measured execution exceeds its allowance, release that failed
record and reduce the group width before retrying. Retain completed independent
proofs. If the smallest group still cannot fit, report the unsplittable unit
and required resource floor rather than repeatedly rebuilding it.

Repeated self-wrapping must make measurable progress toward a compressible
root. Under a fixed resource configuration, require a reduction in the batch
shard count or a validated alternative verifier-work estimate. A round that
does not contract must trigger bounded grouping or an explicit infeasibility
result; do not silently hand a non-contracting batch to the next stage.
Check feasibility before committing to an expensive full-batch wrap where
the available shape/profile data allow it.

Add a regression case with hundreds of child trace shards, including the
476-shard shape observed in Init. Exercise an oversized direct wrap, the
bounded-group fallback, a non-contracting wrap, and the smallest infeasible
group. Assert bounded retry behavior, reservation release, unchanged statement
and lookup validity, and independent verification of the completed root.

Review the fixed 128 GiB record ceiling: derive a safe allowance from the
active resource plan or refine oversized work as above. Do not simply raise
the ceiling to make the failing case pass.

### 4. Keep runtime safety independent of prediction accuracy

Reservations are accounting commitments, not eager RAM allocations. They
limit how much additional memory the scheduler can promise to active work.
Use an explicit accounting boundary:

```text
persistent process memory
  + record reservations
  + peak concurrent host workspace
  + safety headroom
  <= effective runtime host limit
```

Include the loaded environment, ownership/frontier structures, shared tables
and caches in persistent process memory. Estimate their loading/preparation
peak before large allocations, measure the baseline after preparation, and
account for subsequent growth. A generic percentage is not a substitute for
this workload-dependent term: the cited FLT run reported about 65 GiB of
environment residency outside the record pool, while the current 10% allowance
would be only 23 GiB under a 230 GiB cap. Remeasure this with the current
representation; 65 GiB is evidence of the category, not a universal constant.

Subtract existing usage once. When the budget starts from an absolute runtime
limit, deduct the resident baseline before assigning capacity. If runtime
admission instead starts from measured remaining headroom after loading, that
baseline is already excluded. Keep resident bytes and outstanding reservations
distinct so neither gets counted twice. These runtime adjustments do not
change the initial partition's physical-resource input.

Reuse the existing record pool, workspace reservations, and cgroup detection.
Protect capacity for recursive work within the accounting above so retained
leaves cannot consume everything needed to finish. Charge each allocation
once, including workspace already reserved for the same worker. Test loading,
preparation, allocation growth and failure paths for deadlocks and
oversubscription. The cgroup limit remains the final enforcement mechanism.

For four GPUs, count shared environment/process memory once and reserve the
workspace of every concurrently active device. Share the remaining record
capacity. Admission should respond to actual record and persistent-state
growth and completed work. CPU core count alone should not determine how many
large executions can remain resident.

## Validation plan

Run the following in order. Expensive builds and proving runs require
separate authorization; this plan does not start them.

| Phase | Checks | Acceptance criteria |
| --- | --- | --- |
| Archived-data replay | Evaluate the proposed seed and reservations against retained Nat, Array, Init, Mathlib, and FLT records. Separate fitting and held-out inputs. | Explain selected counts, predicted memory, and worst underestimates. Mathlib stays near the validated range without corpus-specific rules. |
| Focused unit tests | Vary total RAM, cgroup limits, GPU count, device VRAM, defaults, profile availability, and heuristic outcomes of one or several shards; exercise unary-root and binary-root scheduling. | Both outcomes use the same scheduler and admission path. Transient free RAM and cgroup caps do not change the initial seed. Runtime admission respects the cap. Host RAM is never multiplied by GPU count. Planner and executor resolve the same defaults. |
| Memory and scheduling tests | Environment loading/preparation and persistent-state growth; absolute-limit versus remaining-headroom accounting; record growth; a constrained one-shard plan, one-to-many refinement and restart from its persisted manifest; simultaneous device workspace; retained children plus a join; nested cgroups; oversized atomic work. | Baseline memory is charged once, shared data is not multiplied by GPU count, and all active allocations have capacity. No deadlock or unreserved allocation path; feasible work completes and infeasible work produces an actionable error. Singleton/refined runs retain shared admission and independently verify with exact coverage and no unresolved assumptions. |
| Recursive recovery tests | An Init-like 476-shard batch, oversized direct join/wrap, bounded range groups, non-contracting self-wrap, and smallest infeasible group. | Group widths decrease on retries, failed records release their reservations, repeated wraps make progress or fail explicitly, and successful grouped proofs preserve the expected statement and lookup accounting. |
| CUDA mode tests | CPU main traces with shape-only lookups, generated main traces where supported, padded shapes, and device ownership. | Proof verification and lookup accounting remain correct; memory estimates distinguish the modes accurately. |
| One-GPU pilots | Paired baseline/candidate fresh Nat and Array runs; fresh Init through final PLONK under the 230 GiB cgroup. | Automatic partitioning; independent verification; no OOM; no recurrence of Init's recursive trace explosion; both the checking/aggregation and E2E performance gates below pass. |
| Four-GPU pilot | Fresh Init and enough automatically partitioned Mathlib heavy units on g7e.24xlarge to keep all four devices active, using detected total RAM and the agreed cgroup cap. | Correct proofs for the tested scope; overlapping proving on all four GPUs; record growth and retained children/joins alongside simultaneous workspaces; no host-RAM double counting. Init alone is insufficient if it selects only three leaves. |
| Mathlib validation | Inspect the automatic full-corpus plan, prove representative heavy units, then run the full pipeline on both one and four GPUs. | Partition remains approximately comparable to 80 shards; memory predictions survive the tail; complete verified proof without OOM; E2E timings include all aggregation and compression and are compared with the corresponding baseline. |
| FLT follow-up | Replay arithmetic-heavy profiles first; schedule proving only after the preceding gates pass. | Identify heavy outliers automatically and demonstrate safe refinement or clear infeasibility without manual shard counts. |

Add focused cases to existing suites. Do not introduce a second benchmark
framework or a CI workflow. Do not force a particular shard count in the
acceptance runs.

For performance comparisons, pin input identities, toolchains, build features,
prover dependencies, hardware, enforced caps, trace-generation/lookup modes
and cache conditions. Keep changes outside the heuristic fixed; treat intended
mode/default changes as explicitly named comparison configurations. Let the
heuristic choose counts and concurrency, and record those outputs.

For the separately authorized Nat and Array comparisons, use at least three
fresh runs per baseline/candidate configuration. Compare two wall-time
intervals separately:

- Checking and aggregation: from the start of checking execution to the final
  verified aggregate root, including admission waits, trace proving, joins and
  root wrapping. Exclude downstream root normalization and compression.
- E2E: the existing complete proving interval through saving the final PLONK
  proof, including all checking, aggregation and compression stages.

Use a provisional **10% maximum median regression in each interval** on
workloads that already complete. A larger slowdown in either requires an
explicit tradeoff review; an unchanged E2E total cannot conceal a regression
in checking and aggregation. The recorded Nat run spent about 11.5 s of its
271 s total in those stages, and Array about 22.6 s of 299 s. Doubling them
would increase E2E by only about 4.2% and 7.6%, respectively, passing an
E2E-only 10% gate despite a large regression in the work affected by sharding.

Treat smaller differences within observed run variation as inconclusive.
The historical 78-versus-102-shard Mathlib comparison changed concurrency and
RAM together and differed by about 1%; it does not isolate a shard-count
speedup. Retain stage boundaries and timings with the results so the two
performance intervals can be audited without summing overlapping workers.

For expensive full-corpus runs, retain a matched baseline and candidate when
authorized, label single observations `n=1`, and review regressions before
acceptance. If only archived or differently configured evidence is available,
mark performance acceptance provisional. A timeout or failed baseline is not
a successful timing: Init's first gate is verified completion. Similar shard
counts and zero OOM events alone do not establish acceptable performance.

For measured runs, retain the input and source identities, physical RAM,
cgroup cap, active GPUs, resolved modes, environment/trace shard counts,
execution concurrency, record sizes, measured persistent baseline and its
growth, loading/preparation peaks, reserved versus observed workspace,
peak RSS/VRAM, cgroup OOM events, and stage wall times. Record admission waits
and GPU idle periods to distinguish memory pressure from insufficient work.
Use fresh proofs for end-to-end results; label any replay separately.

## Completion criteria

The normal proving command chooses a partition without manual tuning and
uses the same execution and admission path whether it selects one shard or
many. Init completes through PLONK on this machine and the four-GPU machine
under their enforced caps. Mathlib remains near the validated partition range
unless measurements justify a change, and its four-GPU validation exercises
all four devices. Every acceptance run verifies independently and records
zero OOM events. Performance comparisons meet both regression gates or receive
an explicit tradeoff review. Regression tests cover resource-policy agreement,
persistent-memory accounting, unary-root scheduling, refined-manifest
verification, trace fragmentation, bounded recursive recovery and progress
toward a root that final compression accepts.

## Research references

- Shared policy sources: `Ix/Cli/ShardCmd.lean`, `crates/ffi/src/kernel.rs`,
  `crates/kernel/src/shard.rs` and `crates/ffi/src/aiur/protocol.rs`.
- Scheduler and resource limits: `crates/ffi/src/aiur/aggregate/multi_gpu.rs`
  and `multi_gpu/limits.rs`; singleton CLI dispatch: `Ix/Cli/ProveCmd.lean`,
  on `kzg-bn254` at `2f956090`.
- Existing memory machinery: `crates/aiur/src/{synthesis.rs,shard.rs,record_pool.rs}`.
- CUDA seed history: `6377ece4c410058a714619dc91916dc9aa7f69be` and its integration
  through `2ff0e5ce` / PR #643.
- Historical planner research: `origin/sb/aiur-planner`, particularly
  `9427ae7532a8f3bf3284cad62e80115426fb9b53` and
  `e82f0474de30bcb9184717c745442d10e00fc59a`. Useful measurements and admission
  ideas do not imply adopting the entire old implementation.
- September Mathlib records at `13feef0f33ea78f73b35073f875ed4d1c9ca424d`:
  `bench/mathlib-seed-2026-09-15/README.md` and
  `bench/mathlib-lanes4-metrics-2026-09-17/README.md`.
- Historical FLT residency at the same `13feef0f` revision:
  `bench/flt-lanes4-2026-09-18/README.md`, including environment memory outside
  the record pool.
- [Calibration data and source notes](../Benchmarks/BackendResults/aiur-sharding-20261030/README.md).
- October partition logs: [Init](../Benchmarks/BackendResults/aiur-sharding-20261030/init-partition.log)
  and [Mathlib](../Benchmarks/BackendResults/aiur-sharding-20261030/mathlib-partition.log).
- Successful aggregate-root logs: [Init](../Benchmarks/BackendResults/aiur-sharding-20261030/init-root.log)
  and [Mathlib](../Benchmarks/BackendResults/aiur-sharding-20261030/mathlib-root.log).
- Failed fresh Init attempt: [summary](../Benchmarks/BackendResults/aiur-sharding-20261030/init-attempt.json)
  and [log](../Benchmarks/BackendResults/aiur-sharding-20261030/init-attempt.log).
- [Nat/Array stage timings](../Benchmarks/BackendResults/aiur-sharding-20261030/small-workloads.json)
  underlying the separate checking/aggregation and E2E gates.
- [FLT per-leaf records and profile features](../Benchmarks/BackendResults/aiur-sharding-20261030/flt-leaves.csv)
  for replaying heavy-tail predictions.
