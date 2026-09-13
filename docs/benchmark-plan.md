# Benchmark design

This document defines comparison rules and expansion criteria. The
[implemented protocol](../benchmarks/protocol.md) owns commands, adapters,
formats, exact sampling parameters, and replay. [Performance reports](performance/README.md)
retain results and raw evidence; the [roadmap](roadmap.md#performance-measurement)
owns PERF2/PERF3 priorities.

The first suite, checked counter-fold comparison, and bounded
[compiler scaling protocol](../benchmarks/compiler-scaling.md) are delivered. Broader
benchmarks follow actual source/native support, rather than assuming a larger
compiler domain from the existing results.

## Questions

Measure runtime and memory on accepted computations, explain the contribution
of representation/ownership/code generation, and quantify the compiler work
needed to obtain an improvement. Include unfavorable cases, fallback, evidence
size, and dependency/cache scaling. A report should be reproducible from its
retained artifacts and samples.

## Comparison groups and toolchains

| Group | Implementations | What is controlled |
| --- | --- | --- |
| Language/runtime | Compilatrix, Lean 4, CakeML; OCaml in the broader suite | Same mathematical operation, exact input values, and ownership/lifetime contract; each uses its ordinary representation and optimized native toolchain. |
| Matched arena C | One C implementation compiled with CompCert, GCC, and Clang, compared with Compilatrix | Same algorithm, arena layout, entry validation, counters, release behavior, driver, and linker configuration. |
| Checked optimization | Baseline and selected Compilatrix artifacts | Same source/inputs, one declared policy change, and both actual artifacts supported and checked. |

Representation, integer boxing, allocation, and reclamation differences are
part of the language/runtime result. The C group controls those costs more
closely but still allows differences in source expression and instruction
selection. Report both groups separately.

Pin compiler source/binary versions, build options, runtime/GC configuration,
assembler/linker, target ISA, and dependency closure. The repository pins Lean;
CakeML uses a pinned bootstrapped x86-64 distribution. Verify that the CompCert
kernel object comes from `ccomp`, even when its driver uses another compiler.
Use ordinary optimizing configurations; host tuning, LTO/PGO, and alternative
allocators belong to separately named profiles.

Lean already performs ownership-sensitive reuse and borrowing. Inspect compiled
IR and diagnose uniqueness in a separate compiled run; retained input aliases
must not manufacture a slow baseline. See the
[Lean reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/),
[CakeML distribution](https://cakeml.org/download.html),
[CompCert manual](https://compcert.org/man/manual003.html), and
[OCaml native compiler manual](https://ocaml.org/manual/native.html).

## Workload specification and admission

Every versioned workload records its operation/result observations, source
origin and roots, input format/generator/seeds, exact numeric domain, ownership
and alias contract, representations, entry/release behavior, resource limits,
per-toolchain implementation, selected policy/fallback, and artifact digests.
Label unchanged upstream exports, synthetic schemas, and handwritten baselines.

Inputs arrive after compilation. Every N2 dataset uses the same emitted object
pair; input hashes belong to the benchmark manifest, not a per-input native
specialization. Check actual emitted code, rather than timing an evaluator or
compiler invocation as program execution.

Support gaps, compiler rejection, timeout, resource exhaustion, correctness
failure, and unavailable diagnostics have separate statuses. Keep them visible
in reports. A fallback is eligible only when its resulting artifact is
identified and supported. N2's native selector needs static reuse, so disabling
reuse does not automatically create a native comparison partner.

### First workload: consuming list reversal

`native-reverse/1` consumes a list, returns its values reversed, consumes the
result, and relinquishes all list storage. Its synthetic source is
`fun xs => reverseOnto nil xs`.

| Dimension | Contract |
| --- | --- |
| Size | Correctness covers every length 0–64. Primary timing uses 0, 1, 2, 4, 8, 16, 32, 48, 63, and 64. |
| Values | Primary nonnegative integers below `2^30`; separate exact-value stress at `2^63 - 1`, `2^63`, and `2^64 - 1`. |
| Patterns | Zero/repeated, ascending/descending, alternating, and deterministic random values; a frozen mixture for each primary timing length. |
| Representation | Lean `List Nat`, CakeML nonnegative integer lists, and the declared arena layout; word-specialized variants are separate profiles. |
| Ownership | Consume each prepared list once; clear the owning input slot before the call. Expected values come from independent scalar data. |
| Arena | 80-byte header plus `C` 32-byte cells; `n + 2 ≤ C ≤ 66`, with minimal sufficient capacity for primary timing. |
| Failures | Oversized/out-of-domain adapter inputs, insufficient capacity, and the existing malformed-input matrix, under the documented mapped-memory preconditions. |

Reversal copies values without arithmetic. Later arithmetic workloads must
specify exact Nat versus wrapping Word semantics, intermediate ranges, overflow,
underflow, and fallback; representation conversion may not silently change the
operation.

The primary Compilatrix artifact includes entry guards and counter updates.
The C kernel matches result graphs, counters, clearing/release, and supported
rejection behavior with defined integer/pointer operations. Sanitizers,
uniqueness checks, ABI canaries, and added instrumentation use separate runs.
A validation-free or counter-free policy needs its own checked artifact and
profile; the checked counter fold is a separately named option.

### Broader workload families

| Family | Dimensions | Admission gate |
| --- | --- | --- |
| Runtime arithmetic/control | Branch bias, joins, exact ranges, direct helpers, overflow neighbors | The accepted N3 scalar contract; general CFG extensions when needed |
| Larger unique traversals | Reverse/map/fold, geometric size growth, cache-resident and streaming sets | Extended ABI/selector and F1 occupied-space contract beyond the current 64-element bound |
| Shared/borrowed traversals | Hot/cold/mixed reuse, aliases, direct/PAP wrappers, suspended calls | Native shared heap/RC, borrowing/call contracts, and F1 |
| Trees/persistent structures | Shape, sharing, retained versions, update density | Accepted recursive source/native and reclamation contracts |
| Higher-order code | Capture size, direct versus PAP/application, specialization/fallback | Native closure/application support and bounded specialization |
| Unchanged upstream programs | Named computational entries with runtime inputs and varied work | C3 source coverage plus required N3/runtime extensions |
| Bounded checker/codec | Valid/invalid inputs, certificate size, rejection position, dependencies | X1 and required byte-buffer/native interfaces |
| Large exact integers | Small/boxed transitions, limb growth, allocation/release | The later bignum gate, separate from fixed-width arithmetic |

Compare the common admitted domain and report maximum supported sizes
separately. PERF2 adds OCaml and distinct computational families before any
suite-wide summary. Threads, floats, other ISAs, and zk costs retain their
separate roadmap gates.

## Timing boundaries and lifetime accounting

| Profile | Included work | Excluded work |
| --- | --- | --- |
| Entry plus bounded handoff | Reversal calls with actual guards, allocation, counters, and result handoff; any GC triggered during the call | Preparing input chunks, full output checking, and release between timed chunks |
| Lifecycle | Fresh input allocation/construction, reversal, order-sensitive result consumption, and normal memory management | Scalar dataset preparation, process startup, compilation, and diagnostic serialization |
| Release, where meaningful | Teardown of prepared results | Preparation/reversal; unavailable for runtimes without a separable release boundary |
| Startup | Process/runtime initialization and one complete operation | Compilation; report separately from steady-state throughput |

Do not mix profiles in a ratio. Bound retained inputs/outputs and record
working-set size, root lifetimes, and traversal order. Warm caches and shared
application inputs are separate dimensions. Arena pooling is a separate storage
profile from fresh allocation.

For tracing GC, dropping the last root makes storage collectible. Lifecycle
runs must include representative collection cycles and bounded retained memory;
record heap settings and collection observations where available. Terminal
forced collection, if exposed, is a separate observation. Never pause timing
around a collection triggered inside the interval or claim immediate complete
reclamation from root-dropping alone.

The result consumer depends on order and payloads. Keep an observable operation
boundary so reversal plus a weak checksum cannot collapse into another
computation. Whole-program fusion or tuned library variants may have separate
rows. Avoid volatile data structures that suppress legitimate internal
optimization. Measure a minimal call/driver control; primary results retain raw
times rather than blindly subtracting noisy overhead estimates.

## Correctness before performance

Build, check, and time the same recorded artifact digests. New build flags
require checking the new executable. Reuse existing source/native gates and
an independent scalar oracle; compare every output value, order, and length.
Reversal twice is an additional check, not a sufficient oracle.

Arena checks include normalized graphs, headers, counts, full release, saved
registers, stack, and memory frames. Runtime adapters verify their stated output
and lifetime observations without inventing arena-equivalent counters. Keep
malformed-input checks separate from successful-input timing.

Inspect generated IR/assembly for runtime inputs, the intended operation, and
the output sink. Full diagnostics run separately; timed samples retain an
observable bounded sink checked outside the interval. Wrong results, schema or
artifact mismatches, and failed processes stop publication for that row.

## Measurement and analysis policy

The [protocol](../benchmarks/protocol.md) fixes the current timer, chunk sizes,
pilot, warm-up, block/session counts, randomization, bootstrap seed, and failure
rules. Future protocols retain these principles:

- Compare implementations on the same recorded host, core placement, dataset,
  and timing profile. Record CPU/microcode, topology, memory, kernel/toolchain,
  frequency/SMT/NUMA settings, timer, and uncontrolled conditions.
- Finish builds/network setup before timing. Calibrate and freeze operation
  counts in a separate pilot; each timed chunk must dominate timer overhead.
  Use bounded chunks when preparing enough fresh inputs for one large interval
  would distort memory use.
- Collect randomized paired blocks with fresh worker processes and fixed warm-up.
  Retain all valid observations, pilot data, invalidated blocks, and reasons.
  Slow samples alone are not grounds for exclusion; do not stop on a desired win.
- Report nanoseconds per operation and, for nonempty lists, per element. These
  are amortized batch measurements, not single-request tail-latency percentiles.
- Summarize within blocks, then report distributions and uncertainty across
  blocks. Define speedup as `baseline time / Compilatrix time`. Resample paired
  blocks with their session structure; record the estimator and analysis version.
  Collect more independent sessions if session effects dominate.
- Keep per-family results. Any later geometric mean names its common subset,
  weights, missing rows, and uncertainty. Multiple lengths of one function are
  not independent application benchmarks; different hosts do not share one ratio.

Cycles, retired instructions, branches/misses, cache events, and page faults
are optional diagnostic runs. Record event scope, multiplexing, availability,
and profiling overhead. Nanoseconds are not processor cycles; unavailable
counters are not zero. The existing shared-host references do not establish
between-day stability or a dedicated regression threshold.

## Memory, code size, and compiler cost

| Observation | Keep distinct |
| --- | --- |
| Heap work | Interpreter counts, counters already in emitted code, and separately instrumented runtime events |
| Application storage | Live bytes, reserved/occupied capacity, cumulative allocation, metadata, and peaks |
| Process memory | Runtime baseline, retained GC heap, RSS/current/peak measurements, and method |
| Stack | Observed high-water use, supplied capacity, and proved sufficiency |
| Code/artifacts | Kernel text, data, provenance, objects, linked executable, runtime dependencies, and stripping mode |
| Compiler work | Total/stage wall and CPU time, peak memory, proposal/checking work, evidence size, and output growth |

For N2 retain both live-cell observations and `80 + 32 * C` supplied arena
bytes. Freed cells do not shrink the arena. [F1](roadmap.md#f1-finite-heap-and-stack)
owns capacity adequacy; observed RSS or node counts do not replace that theorem.
Label estimates and unavailable instrumentation explicitly.

Measure compiler invocation, dependency/cache behavior, and building the
compiler separately. Invocation covers ingress through emission on a named
input; diagnostic stage timing and independent artifact checking are separately
identified. Building the compiler distinguishes proof elaboration, incremental
rebuilds, host compilation/linking, and cache substitution.

Cache experiments include cold/warm application cache, dependency edits,
stale/corrupt records, widening/fallback, and evidence growth. Record actual
hits/misses, read bytes, and checker work; distinguish HPT cache state from
filesystem page-cache state. Commit analysis roots or a deterministic producer
policy under the [reproducibility contract](roadmap.md#reproducible-optimization-and-artifacts).
Different sound facts can select different code. Equivalent cache configurations
must reproduce complete deterministic artifacts. Canonical independent IxIR₂
identity uses the delivered [I2 snapshot contract](ixir2-wire.md).

The compiler scaling suite varies declaration count, call depth, branches,
allocation work, and supplementary checked-IxIR₂ joins under fixed defaults.
It records source construction/admission failures as well as successful stages,
coverage database counts, serialized HPT evidence, snapshots and ELF growth.
Fresh processes compare absent/persisted HPT stores and a single dependency
edit; source certification still runs each time. Stage clocks, repeated
diagnostics, whole-process costs and raw memory observations have explicit
separate scopes. The [reference report](performance/compiler-scaling-2026-09-12/README.md)
retains all observations and exact rejection boundaries. Its CI smoke checks
correctness, corrupted records and artifact/analysis replay without thresholds.

The [modular assembly suite](../benchmarks/assembly-scaling.md) retains the
source-unit cold/unchanged/dependency-edit/literal-premise-edit matrix and
separates assembly's main phases. It compares indexed IxIR₁ addressing with
the original list builder on the same raw program, requiring complete
artifact equality and the unchanged semantic certificate predicates. Its
width series reaches the same 611-source-declaration closure, with retained
proof recovery and fresh-process checks under the existing limits.

Name input/output boundaries when comparing compiler times. Compilatrix starts
from Ixon; a source-to-executable comparison includes required upstream
frontend/export work. Toolchain installation and bootstrapping are setup costs.

## Optimization experiments and reporting

A paired experiment changes one policy on the same source/inputs. Both actual
native artifacts must select; interpreter/counter pairs remain useful at their
own boundary. Retain checked evidence, exact artifacts, source relation,
fallback, runtime distributions, memory/RC observations, code growth, and
compiler/checker cost. Include a case expected to benefit, a neutral/adverse
neighbor, and invalid-evidence or exhausted-budget fallback.

Fewer RC operations or allocations need not reduce elapsed time. Use measured
tradeoffs to activate [M2d](roadmap.md#m2d-measured-specialization-and-representation),
including a decision to decline an optimization. The unchanged baseline remains
a reproducible comparison input.

Version specifications, source/toolchain locks, datasets, adapters, schemas,
and reports. Retain full raw samples, environment, correctness/build logs,
executable identities, analysis parameters, and missing/failed rows. Archive
large bundles by digest with durable retrieval and replay instructions; exact
artifact/analysis reproduction does not require identical timing samples.
Resuming a run must reject incompatible artifacts, inputs, profiles, or metadata.
Host timings remain outside deterministic compiler identities.

Normal CI checks artifacts, correctness, schemas, short runner behavior, and
invalid-result rejection. Dedicated performance runs establish variability
before choosing practical regression thresholds. Confirm a flagged change with
repeated measurements and the declared uncertainty criterion before changing
its reference. Track memory, size, and compiler-cost regressions alongside
runtime. New protocol/toolchain versions retain their predecessors and rerun
all compared implementations.
