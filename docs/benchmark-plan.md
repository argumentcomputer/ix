# Benchmark plan

Written 2026-09-09; delivery links updated 2026-09-10. This document
specifies workloads, comparison rules, measurement, and result artifacts. The
[roadmap](roadmap.md#performance-measurement) owns delivery state, priorities,
and acceptance gates. The [implemented protocol](../benchmarks/protocol.md)
provides all six comparison adapters and the compiled workflow. The
[first full reference](performance/native-reverse-2026-09-09/README.md) delivers
PERF1 and the scoped C3 measurements, with retained samples and independent replay.

The first suite compares Compilatrix's emitted x86-64 code with **Lean 4,
CakeML, CompCert, GCC, and Clang**. OCaml is the first additional functional
baseline. The initial reference measures the existing parameterized native
reversal. Broader workloads follow actual source and native acceptance.

## Questions and current evidence

The suite should answer five questions:

1. How much time and memory does an accepted computation use relative to
   other native toolchains, under a stated input and ownership contract?
2. How much of that cost comes from representation, allocation, RC/reuse,
   validation, calls, or emitted instructions?
3. What do checked optimizations change in runtime, code size, and compiler
   work, including cases where the optimization rejects or falls back?
4. What does compilation and certificate checking cost as the source closure,
   control flow, analysis evidence, and dependency graph grow?
5. Can another process and another operator reproduce the artifacts and the
   measurement procedure, including unfavorable results?

| Existing instrument | Available observation | Benchmark boundary |
| --- | --- | --- |
| [N2 runtime reversal](source-native-runtime.md) | One emitted reversal/release pair, caller-supplied lists, actual linked execution | First full reference delivered; synthetic source schema, unique ownership, at most 64 elements |
| [Counter-level thesis evidence](thesis-counter-evidence.md) | Exact allocation, reclamation, and RC counts for mode pairs | Interpreter counters; retain as explanatory evidence |
| [Borrowed runtime calls](source-borrow-runtime.md) | Structural source/physical proofs and two fewer RC operations | Native selection is still missing; native timing remains unavailable |
| [Upstream source coverage](source-coverage.md) | Three accepted closure entries through baseline IxIR₂; two unchanged computational ELF entries and precise rejected neighbors | C3 compile/check, artifact/memory and native call measurements delivered; broader native workloads require N3/source extensions |
| [Scalar native coverage](source-coverage.md) | Small closed scalar entries | Useful for entry/driver calibration; insufficient as a computational performance result |

E1 local instruction proofs, [E2 stream/object proofs](x86-stream-objects.md),
and the linked native gates support measurement of the actual emitted binaries.
Reference ISA agreement and system linker/loader behavior retain their recorded
boundaries. A timing result establishes an observation on the recorded machine;
it does not extend a compiler theorem.

## Comparison groups and toolchains

Keep two comparison groups visible in every report.

**Language/runtime comparison:** implement the same mathematical computation
and consuming input contract using each language's ordinary list representation
and optimized native compiler. Compilatrix, Lean, and CakeML belong here.
Different object layouts, integer representations, allocation, and reclamation
strategies are part of this result and must be described.

**Matched C implementation:** write one reference implementation of the current
arena algorithm, entry validation, counters, and release. Compile the same C
source with CompCert, GCC, and Clang and use the same driver as Compilatrix.
This comparison controls the representation and boundary work more closely.
Differences can still include source-level expression and instruction selection;
it is not a theorem that the compilers received identical IR.

| Toolchain | Initial build policy | Required record |
| --- | --- | --- |
| Compilatrix | Actual checked N2 source compilation and native selection | Source and IxIR₁ identities, policies, complete emitted objects, selected path, linked executable |
| Lean 4 | Native executable using the repository's `lean-toolchain` pin; optimized generated C and runtime | Lean version, source/IR, C compiler and flags, runtime and link closure |
| CakeML | Pinned bootstrapped x86-64 compiler with its normal optimizing configuration | Source revision, bootstrap archive digest, compiler options, runtime/GC configuration, assembler/linker |
| CompCert | Pinned x86-64 `ccomp`, explicit speed optimization `-O` | Compiler/configuration, preprocessed kernel, runtime libraries, assembly and object |
| GCC | Same C kernel, `-O3`, declared x86-64 target, no LTO/PGO initially | Exact version, target and optimizer flags, assembly and object |
| Clang | Same C kernel, `-O3`, same declared target and LTO/PGO policy | Exact version, target and optimizer flags, assembly and object |
| OCaml | Follow-on native `ocamlopt` adapter | Version, optimizer build/options, representation, GC configuration, runtime closure |

Lean already optimizes reference counting, borrowing, and reuse of exclusive
objects. Inspect its compiled IR and diagnose uniqueness in a separate compiled
run; a retained driver alias must not manufacture a slow baseline. The
[Lean reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/)
describes these mechanisms and the diagnostic limitations of `#eval`.

CakeML supplies [bootstrapped x86-64 distributions](https://cakeml.org/download.html);
the first suite can pin an existing distribution without bootstrapping the
compiler locally. CompCert's [compiler manual](https://compcert.org/man/manual003.html)
defines its C/object interface and speed optimization options. OCaml's
[native compiler manual](https://ocaml.org/manual/native.html) is the adapter
reference. Resolve exact versions and digests when implementing the toolchain
lock; a moving `latest` URL is not a reproducible pin.

Use each compiler's ordinary optimized configuration. Record effective defaults
as well as supplied flags. Initially target a common x86-64 instruction baseline
and record the generated ISA requirements; host-specific tuning, LTO, PGO, and
alternative allocators form separate named profiles. Keep the common C driver
and linker configuration fixed across the four arena implementations. Verify
that the CompCert row actually links the object produced by `ccomp`; using a
GCC-built driver is not a reason to compile that kernel with GCC.

## Workload specification and admission

Every workload needs a versioned record containing:

- Mathematical operation, result observations, source origin, and all source
  files/roots. Label unchanged upstream exports, synthetic Ixon schemas, and
  handwritten comparison programs separately.
- Input format, integer domain, size dimensions, deterministic generator and
  seeds, full correctness cases, and expected normalized results.
- Ownership and alias contract, representation, allowed effects, entry and
  release behavior, sufficient resource bounds, and failure cases.
- Per-toolchain implementation, build profile, accepted compiler stage,
  optimization selection/fallback, and exact executable/object digests.
- Timing boundary, batch construction, output sink, reclamation policy, and
  any adapter or representation differences.

Use runtime inputs loaded or generated after compilation. For N2 all datasets
must use the same emitted object pair. Input hashes belong to the benchmark
manifest; they must not turn into per-input native specialization. Do not time
an evaluator, compiler invocation, or constant result in place of the emitted
computation.

Missing language support, rejection, timeout, resource exhaustion, correctness
failure, and missing measurement permissions are distinct statuses. None is a
zero runtime or an omitted inconvenient sample. A checked fallback is eligible
only when its actual resulting artifact is supported and identified. The N2
selector currently needs static reuse, so disabling reuse does not automatically
produce a native comparison partner.

### First workload: consuming list reversal

Use `native-reverse/1`: consume a finite list, return its values in reverse
order, consume the result, and relinquish all owned input/result storage.
The current source computes `fun xs => reverseOnto nil xs`.

| Dimension | Initial coverage |
| --- | --- |
| Length | Every length 0–64 for correctness; timing rows at 0, 1, 2, 4, 8, 16, 32, 48, 63, 64 |
| Payloads | Zero, repeated values, ascending/descending values, alternating values, deterministic random values |
| Primary payload domain | Nonnegative integers below `2^30`, represented exactly in every implementation |
| Representation stress | Separate rows containing `2^63 - 1`, `2^63`, and `2^64 - 1`; exact values, with boxing/layout differences recorded |
| Ownership | One consuming owner, no retained input-list alias; immutable scalar input data may be retained outside the list |
| Arena capacity | `C = n + 2` for primary timing; correctness also exercises other admitted capacities up to 66 |
| Entry failures | Existing malformed-input matrix, length 65, insufficient capacity, and adapter rejection outside the exact-Word domain |

Use one frozen mix of the primary payload patterns for each timing length,
with identical logical inputs across implementations. Keep individual pattern
cases in correctness checks; add separate timing rows only to investigate a
declared effect. Representation-stress timing starts at lengths 1, 16, and 64.
This keeps the first suite bounded without selecting only favorable payloads.

The primary Lean implementation uses `List Nat`, and the CakeML implementation
uses nonnegative integer lists, with the same accumulator-reversal algorithm.
An idiomatic library implementation may be used after inspecting its pinned
definition. Word-specialized variants can be added as separately named profiles;
do not silently compare wrapping arithmetic with exact Nat arithmetic. Reversal
copies payloads without arithmetic, which keeps the first semantic comparison
small. Later arithmetic workloads need their own range/overflow contracts.

The Compilatrix arena has an 80-byte header and 32-byte cells. Its initial
`n + 1` cells are caller-built. Reversal allocates one accumulator, reuses `n`
cells, and performs zero RC operations; release reclaims every live cell. The
complete entry also validates the header and every input cell. Keep those
guards and counter updates in the primary timed object. The local evaluator's
step formulas are explanatory counters, never inferred processor cycles.

The C implementation must match the arena's externally observable result,
header counters, clearing/release behavior, and supported rejection behavior.
Review its integer and pointer operations for defined behavior under the same
mapped, aligned, nonwrapping memory preconditions. An arbitrary unmapped pointer
is outside the current contract. GCC/Clang sanitizer runs can supplement the
correctness checks in separate builds; their instrumentation stays outside
timed executables.

Uniqueness must survive the driver. Each prepared list is consumed once; remove
the owning input slot/reference before the call, and do not retain the original
list for expected-output checking. Compute expectations from independent scalar
data. Reversing the same permanently shared list repeatedly would change the
Lean workload. Retaining outputs for checking also needs an explicit bound.

### Broader workload families

Admit each family only after the actual checked compiler emits it. The table
specifies intended coverage, not support already present.

| Family | Parameters and contrasting cases | Required boundary |
| --- | --- | --- |
| Runtime scalar arithmetic and control | Exact Nat/Word arithmetic, branch bias, joins, direct calls, range and overflow neighbors | N3 arithmetic/control contracts; A1/F1 when calls or spills need them |
| Larger unique list traversals | Reverse, map, fold; lengths growing geometrically beyond 64; cache-resident and streaming working sets | Extended native ABI/selector and occupied-space capacity contract; the current N2 bound stays in force |
| Shared and borrowed traversals | Hot/cold/mixed reuse, shared aliases, borrowed readers, direct/PAP wrappers, non-tail calls | Native shared heap/RC and call support, borrowing contracts, F1 |
| Trees and persistent structures | Balanced/skewed trees, shared leaves, retained versions, rebuild/update density | Accepted recursive source/native families and exact alias/reclamation contracts |
| Higher-order code | Closure capture size, direct versus PAP/application paths, specialization and fallback | Actual native closure/application support and bounded specialization |
| Unchanged upstream programs | A named computational C3 entry with runtime inputs, followed by a small diverse corpus | C3 source acceptance plus required N3/runtime extensions |
| Bounded checker/codec | Valid/invalid byte inputs, certificate size, rejection position, dependency count | X1 and the needed byte-buffer, allocation, and native interfaces |
| Large exact integers | Small/boxed transitions, growing limbs, allocation and release | N3's later bignum gate; separate from fixed-width arithmetic |

Choose sizes from the intersection of admitted domains and expose each
implementation's maximum supported size separately. Grow source families before
presenting a suite-wide ranking. Threads, floating point, other ISAs, and zk
costs keep their existing roadmap activation gates and separate protocols.

## Timing boundaries and lifetime accounting

Every result row names one timing profile. Do not mix these profiles in a ratio.

| Profile | Timed work | Work outside the interval |
| --- | --- | --- |
| `entry` | Calls to reversal, including its actual validation, allocation, counter updates, and bounded result handoff | Input preparation; result traversal/checking and release after the timed chunk |
| `lifecycle` | Input allocation/construction, reversal, an order-sensitive result consumer, and normal reclamation over repeated operations | Pre-generated scalar datasets, process startup, compilation, diagnostic serialization |
| `release` | Result teardown on prepared outputs, where the runtime exposes a meaningful boundary | Preparation and reversal; report unavailable for runtimes without a separable release operation |
| `startup` | Process/runtime startup and one complete operation | Compilation; a separate application-latency experiment |

`entry` measures the cost at the exported operation. Allocation or GC triggered
by that call remains inside its time, even if setup preceded it. Use a bounded
pool of independently owned inputs and bounded output slots; keep the resulting
working set and root lifetimes in the manifest. If output handoff cannot be
isolated consistently, label the row `entry+handoff` and describe the difference.
Do not silently force a collection before every entry or stop the timer around
collections that occur inside it.

`lifecycle` is the primary language/runtime throughput comparison. Include
malloc/free or the declared arena pool's costs, input construction, result
consumption, and runtime memory-management work. For tracing collectors, dropping
the last root makes an object collectible rather than immediately freed. Run
long enough to include representative collection cycles and demonstrate bounded
retained memory across batches; record collection counts and heap settings when
available. Report terminal collection separately if exposed and used. Do not
label root-dropping alone as measured complete reclamation.

Give every implementation the same result-consumer specification and ensure it
depends on order and payloads. Consumer work is part of `lifecycle`. Preserve a
fixed operation boundary in the primary reversal experiment so the compiler
cannot replace reversal plus a weak checksum with a simpler computation.
Whole-program fusion and tuned library implementations can have separate rows.

Report any arena-pool reuse as a separate storage profile from fresh allocation.
Warm runtime instruction/data state and application-level input sharing are
different dimensions. Declare the pool byte size, traversal order, and whether
the workload is cache-resident or streaming. The 64-element per-list limit does
not establish the size of a batch's aggregate working set.

Measure a minimal driver/call control to expose timer and handoff overhead.
Retain raw times as the primary result; blindly subtracting two noisy small
measurements can create misleading negative or exaggerated estimates. A
validation-free or counter-free Compilatrix variant requires its own compiler
policy, checks, artifact identity, and profile. It cannot replace the current
production artifact in the main result.

## Correctness before performance

Build once, check those exact objects/executables, and time their recorded
digests. Rebuilding with different flags requires checking the new artifacts.

For N2, start with the existing [native gate](source-native-runtime.md#artifact-identity-and-gate)
and [validation commands](development-plan.md#validation-commands). Extend the
benchmark checker to cover the workload's full input table and deterministic
seeds. Use an independent scalar reversal oracle and compare every result value,
length, and order. Reversal twice is useful but insufficient by itself.

For the arena implementations, check headers, normalized heap graphs, allocation
and reuse counts, complete release, saved registers, stack, and memory frames.
Keep the malformed-input/rejection checks outside the successful-input timing
table. Language runtimes need full output checks and their declared lifetime
observations; they need not expose the same arena counters.

Inspect generated IR/assembly for runtime inputs, the intended calls/traversal,
and the output sink. Keep the C kernel in a separate compilation unit without
LTO in the first suite. Give managed-language adapters an equivalent opaque
operation boundary where required. Avoid making the benchmark's data structure
volatile: the observation boundary should prevent dead-code removal without
disabling legitimate optimization inside the operation.

Full checking, ABI canaries, JSON output, uniqueness diagnostics, sanitizer
instrumentation, and counter collection added solely by the benchmark run in
separate correctness or diagnostic passes. Counters already present in the
emitted N2 code remain present in timing. Timed batches retain a bounded,
observable sink and validate its expected result outside the timing interval;
periodic full checks supplement the initial complete correctness run.

## Measurement protocol

Use x86_64 Linux first, matching the existing native runner. Hardware comparisons
need the same physical host and run configuration. Containers/VMs, shared hosts,
and emulated execution must be labeled; smoke runs on them are useful but should
not silently become the dedicated-host baseline.

1. **Record the environment.** CPU model/stepping and microcode, cores/cache
   topology, RAM, kernel, OS/Nix closure, compiler/runtime versions, timer,
   affinity, NUMA placement, governor/turbo policy, SMT state, and relevant
   environment variables. Record what could not be controlled.
2. **Build and verify.** Resolve pinned toolchains before measurement, save all
   commands and logs, run correctness, and verify executable hashes. Network
   access, compiler work, and background benchmark jobs stay outside timing.
3. **Pilot and freeze.** Calibrate a monotonic high-resolution elapsed timer;
   measure its resolution and the empty-driver control. Choose fixed operation
   counts giving at least 100 ms of aggregate measured work per sample, with
   bounded input/output memory. Entry samples may sum bounded timed chunks
   with preparation/release between them; record chunk sizes and timer-call
   counts, and require each chunk to dominate timer overhead. Extend GC
   workloads as needed. Use the same dataset schedule and operation count
   within a paired case; record deviations required by a declared resource
   limit. Freeze the schedule before collecting the reported samples.
4. **Warm and place.** Pin one worker to a recorded core where available, keep
   competing work off that core/SMT sibling, initialize runtimes, and warm with
   a fixed recorded policy. A starting policy is at least one second per
   executable before samples. Do not warm until a favorable time appears.
5. **Collect paired blocks.** A block runs every compared implementation on
   the same dataset/profile, in a deterministically randomized order. Start
   each implementation in a fresh process and collect several timed samples
   after its warm-up. Default to at least 30 blocks across three independent
   sessions. Rotate order to avoid systematically favoring one implementation
   during temperature or frequency drift.
6. **Validate and retain.** Check sinks, exit status, environment drift, and
   memory bounds. Preserve raw samples and reasons for invalidated blocks.
   Correctness failure stops publication for that row. Environmental invalidation
   rules are fixed before sampling; slow observations alone are not outliers
   to discard. Rerun invalidated comparisons as complete blocks.
7. **Analyze once under the recorded policy.** Retain the pilot separately,
   publish all valid measured blocks, and report uncertainty. If precision is
   inadequate, use a predeclared additional set of blocks and retain earlier
   observations. Do not stop sampling when a desired speedup appears.

Report elapsed nanoseconds per operation; also report nanoseconds per element
for nonempty lists and operations/elements per second where useful. Empty input
has no per-element result. These batches measure amortized operation time;
their percentiles are not single-request tail-latency percentiles.

Within each block, summarize each executable's samples using a declared statistic
(initially the median). Report the distribution across block summaries: median,
interquartile range, and a 95% confidence interval. Define speedup consistently
as `baseline time / Compilatrix time`, so values above one favor Compilatrix.
Calculate paired ratios within blocks and estimate uncertainty by resampling
complete paired blocks, preserving session grouping. Record the estimator,
bootstrap seed/count, sample count, and analysis-tool version. If session effects
dominate, collect more independent sessions and report that limitation.

Preserve per-workload results. A later geometric mean may summarize a declared
fixed common subset with equal workload-family weighting; show the members,
weights, missing rows, and uncertainty. Many lengths of one reversal function
must not masquerade as many independent application benchmarks. Never combine
hardware from different hosts into one speedup ratio.

Hardware counters are an additional diagnostic run: cycles, retired
instructions, branches/misses, cache misses, and page faults when supported.
Record event definitions, counter scope, multiplexing/scaling, and permissions.
Do not call wall-clock nanoseconds CPU cycles or treat unavailable counters as
zero. Profiling instrumentation and its overhead are identified separately.

## Memory, code size, and compiler cost

Report these observations alongside runtime where available:

| Observation | Required distinction |
| --- | --- |
| Allocation, free, reuse, and RC work | Logical/physical interpreter counts, emitted runtime counters, and separately instrumented runtime events have different sources |
| Application storage | Live bytes, reserved/occupied arena capacity, cumulative allocated bytes, allocator metadata, and peak values are separate quantities |
| Process memory | Runtime baseline, retained heap, peak RSS, and measurement method; allocator/GC reservation can exceed live application storage |
| Stack | Stack high-water/capacity observations where supported; the current leaf endpoints do not establish general call-stack costs |
| Code/artifact size | Kernel `.text`, data, metadata/provenance, object size, linked executable, and shared runtime dependencies; record stripping/link mode |
| Compiler work | Wall/CPU time, peak memory, checker/producer work, evidence bytes, and artifact/code growth for the named input and endpoint |

For N2 report both the observed live-cell counts and the supplied
`80 + 32 * C` arena bytes. Freed cells do not shrink that allocated arena.
The [F1 gate](roadmap.md#f1-finite-heap-and-stack) owns the occupied-space and
stack adequacy theorem. An observed RSS peak or cell count cannot replace it.
Unavailable runtime instrumentation is `unavailable`, with a reason; estimates
must identify their layout/version assumptions.

Compiler performance has three separate surfaces:

- **Compiler invocation:** structured ingress, source checking/erasure,
  addressing, lowering, analysis proposal/checking, optimization, native
  selection, encoding, and emission on a named admitted input. Record total
  time plus available stage timings; use a diagnostic run if instrumentation
  perturbs the total. Time artifact checking separately as well.
- **Dependency/cache scaling:** cold application cache, warm valid cache,
  one edited dependency, stale/corrupt entries, bounded fallback, certificate
  and closure-size growth. Record actual hits, misses, bytes read, and checked
  work. A filesystem cache and the HPT application cache are different states;
  use precise names rather than an unexplained `cold` label.
- **Building the compiler:** clean Lean elaboration/proofs, incremental rebuild,
  host C/link work, and any future self-hosting stages. Separate actual builds
  from Nix binary-cache substitution and previously cached Lake work.

Today the Compilatrix entry is Ixon, whereas the ordinary Lean toolchain starts
from Lean source. Report the input and output boundary for each number. A
source-to-executable comparison must include upstream export/frontend cost
where required; an Ixon-to-object time cannot silently compete with another
toolchain's full frontend/build time. Toolchain installation and bootstrapping
are separate setup costs.

For cache comparisons, bind accepted analysis roots or a deterministic producer
policy as required by [reproducible optimization](roadmap.md#reproducible-optimization-and-artifacts).
Different sound HPT facts can enable different code. If analysis choices change,
report different build inputs instead of attributing the runtime difference
solely to cache warmth. Verify complete deterministic artifact equality for the
cache configurations advertised as equivalent. Canonical independent IxIR₂
roots await I2; current IxIR₂ diagnostic JSON is not such an identity.

## Optimization experiments

Use paired builds of the same source and inputs, with one declared policy change
at a time. Start with existing interpreter/counter pairs; add native timing only
when both actual selected artifacts are supported. Candidate experiments include
static/dynamic reuse, borrowed versus owned calls, HPT consumers, specialization,
representation changes, and later checked scalar peepholes.

For every experiment retain:

- Exact before/after artifacts, source relation, pass policies, accepted
  evidence, fallback status, and full correctness results.
- Runtime distributions, code/data growth, compiler/checker time, evidence
  size, allocation/RC/occupied-space observations, and supported input domain.
- A case expected to benefit, a neutral or adverse neighbor, and an evidence
  rejection/budget-exhaustion case. Keep rejected proposals distinct from
  successful optimized execution.

Do not infer wall-clock savings from fewer logical instructions or RC operations.
An optimization can reduce allocation and still lose time or grow code. Use
measured costs to activate [M2d](roadmap.md#m2d-measured-specialization-and-representation)
and record the tradeoff even when the proposed optimization is declined.

## Repository artifacts and execution workflow

PERF1 followed this order; future suite versions retain these reviewable outputs.

| Step | Reviewable output |
| --- | --- |
| 1. Freeze the experiment | `native-reverse/1` specification, input generator/seeds, timing profiles, resource limits, and exact retrievable toolchain pins |
| 2. Build comparison adapters | Actual Compilatrix object pair, consuming Lean/CakeML implementations, and the same arena C source compiled with all three C compilers |
| 3. Check and instrument | Complete correctness results, inspected operation boundaries, bounded timing driver, schema/invalid-result checks, and deterministic analysis from recorded samples |
| 4. Pilot and measure | Frozen host/sampling policy followed by all required baseline rows, raw bundles, memory/size observations, and the first report |
| 5. Reproduce and retain | Independent artifact/check/report replay, documented measurement commands, correctness CI, and an archived reference run |

The `benchmarks/` directory contains the suite
manifest, exact toolchain lock, workload specifications/datasets, comparison
sources, and adapters. The runner/checker follows the repository's compiled
Lean convention, with small native timing bridges. It reuses existing native
artifact producers and independent checks. The correctness harness and timing
driver are separate consumers of the same emitted objects.

The workflow has explicit build, verify, pilot, measure, diagnose, analyze, and
reproduce operations, with fresh output directories. Resumption requires
matching manifest, executable, dataset, and environment identities; the current
runner rejects existing result directories. It must not append incompatible
samples to an existing result. The [implemented version-1 protocol](../benchmarks/protocol.md) documents
the compiled `benchmark` commands, six adapters, correctness/smoke gates,
frozen measurement policy, diagnostics, and independent environment replay.
The [first reference and retrieval procedure](performance/native-reverse-2026-09-09/README.md#retention-and-replay)
retain all 30 blocks, the independent rebuild/check/report replay, and a
digest-addressed archive whose extracted copy regenerates identical analysis.

Each run bundle contains:

| File or group | Contents |
| --- | --- |
| `manifest.json` | Protocol/schema version, source revision and complete dirty-tree snapshot digest, workload/input identities, policies, toolchain/runtime locks, exact commands and executable hashes |
| `environment.json` | Host and timing configuration, affinity/GC settings, limitations, start/end observations |
| `artifacts/` | Source/IR/provenance, native objects, executables, assembly, dependency closure or reproducible retrieval information |
| `correctness.json` | Case inventory, normalized results, lifetime/ABI checks, rejections, actual selected/fallback paths |
| `samples.jsonl` | Workload/profile, block/session/order, dataset seed, batch and chunk counts, elapsed time, sink, status, environment flags; lossless raw observations |
| `diagnostics/` | Build logs, stage timings, hardware counters, allocation/GC observations, memory and size measurements |
| `summary.json` and report | Analysis parameters, distributions/intervals/ratios, all missing/failed rows, interpretation and limitations |

Use versioned machine-readable schemas and reject missing required fields,
unit mismatches, invalid sample counts, mixed artifacts, and incompatible timing
profiles. Hash the complete result bundle for retrieval; elapsed times and host
details remain diagnostic data outside deterministic compiler identities.
Reproduction means exact prescribed build artifacts plus a repeatable statistical
procedure, not byte-identical timing samples.

Commit specifications, locks, sources, deterministic correctness fixtures, and
reviewed reports. Archive bulky raw bundles by digest with a durable retrieval
location. Reports must remain traceable to retained samples. Never silently
overwrite the reference result when a compiler, harness, input, or protocol
changes; issue a new version and rerun the compared implementations.

## Delivery and regression policy

The [2026-09-09 reference](performance/native-reverse-2026-09-09/README.md)
completed the following PERF1 gate on 2026-09-10. Dedicated timing thresholds
remain deferred until a controlled host has enough independent history.

[PERF1](roadmap.md#performance-measurement) closes with the complete first suite,
including Lean, CakeML, CompCert, GCC, and Clang, and a reproducible report on one
recorded x86_64 Linux host. Early subsets may be shared with explicit missing
baselines; they do not close that gate. First results need not show a speedup.

Before declaring it complete, require a clean result-directory replay by a
second operator or equivalent independent environment. Check source/toolchain
and object identities, correctness, analysis regeneration from raw samples, and
the documented procedure for a new measurement session. A second physical CPU
is a later portability experiment with its own ratios, not a requirement for
the initial numbers.

Normal CI builds/checks admitted benchmark artifacts, checks schemas and
correctness, exercises short runner smoke tests, and tests invalid-result
rejection. Do not put noisy host timing thresholds in the ordinary correctness
gate. Dedicated performance runs compare fixed workload/protocol versions on
the recorded host and retain history.

After establishing variability, select per-workload practical regression
thresholds from the pilot and baseline history. Flag a regression only when its
effect exceeds the declared threshold with the specified uncertainty criterion;
rerun it before changing a baseline or making a release decision. Include code
size, compiler/checker cost, and memory regressions even when runtime improves.
Use the same process to report sustained improvements.

The first report should contain per-length reversal time, full-lifecycle time,
memory/code-size tables, the matched C comparison, and explanatory counts. Its
text must name the small unique-list domain and separate measured observations
from hypotheses about their causes. Broader source families, input sizes, and
optimization results enter through PERF2/PERF3's roadmap gates.
