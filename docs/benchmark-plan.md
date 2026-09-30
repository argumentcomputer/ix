# Benchmark design

This document defines comparison rules. The [roadmap](roadmap.md) owns the
benchmark ladder and targets. [Performance reports](performance/README.md)
retain earlier results. The first-wave [fixtures](../benchmarks/fixtures/README.md)
and the optional [runner](../benchmarks/runner/README.md) implement these rules for
the `compilatrix`, `lean-clang` and `clang-idiomatic` rows. The `compilatrix`
row compiles each K1 fixture's frozen closure (`fixtures/ixon-v3/bench-k1`)
with the `compilatrix` executable; the runner times every row in the process
(startup) profile and, for `Nat` entries, in the entry profile with
calibrated repetition counts, and adds two diagnostic rows for attribution
(the K1 algorithms on the compiled value representation, and MEAS-4's
hand-written Lir kernels). The earlier reversal-only runner and its protocol
are on branch `jcb/ixby-archive`.

## Questions

For each accepted computation:
- measure runtime, memory and code size;
- explain how representation, ownership and code generation each contribute;
- quantify the compiler and checker work behind an improvement.

Include unfavourable cases, fallbacks and evidence size. A report must be
reproducible from its retained artifacts and samples.

## Rows

| Row | Definition | Question |
| --- | --- | --- |
| `compilatrix` | The certified production artifact | The primary result |
| `lean-clang` | The same Lean source through Lean's compiler and its bundled Clang at `leanc -O3` (Lean's defaults, including its runtime) | Competitiveness with the incumbent |
| `clang-idiomatic` | A natural C or C++ twin (for example Koka's C++ benchmarks, Lean's `std::map` twins, BLAKE3's portable C) at `-O2` and `-O3` | Distance from what a C programmer gets |
| `lean-clang-nix` | Lean's generated C through the pinned Nix Clang with our flags | Separates compiler-version effects |
| GCC, CompCert, CakeML, OCaml, Koka | Reference toolchains | Context |

- Compile the driver identically, with Clang, for every row, and record the
  hardening flags.
- From the first real-source rung on, the Compilatrix and Lean rows compile
  the *same* Lean source file.
- Pin compiler versions, build options, runtime configuration, assembler,
  linker, ISA and dependency closure.
- Host tuning, LTO/PGO and alternative allocators are separately named
  profiles.

## Workloads

**Every versioned workload records:**
- its operation and observations;
- its source origin and roots;
- its input generator and seeds;
- its exact numeric domain;
- its ownership and alias contract;
- its entry and release behaviour;
- its resource limits;
- its variant (upstream, total, annotated or synthetic);
- per-row implementations and artifact digests.

**Rules:**
- Label unchanged upstream sources, total rewrites, annotated twins and
  synthetic inputs, and never present synthetic inputs as real-program
  results.
- Inputs arrive after compilation.
- Keep compiler rejection, timeout, resource exhaustion, correctness failure
  and unavailable diagnostics as separate, visible statuses.
- Arithmetic workloads specify exact `Nat` versus wrapping semantics,
  intermediate ranges, overflow and fallback. A representation change may not
  silently change the operation.

## Attribution

- **Gap to a baseline:** Compilatrix time divided by baseline time; above 1
  is slower. Published reports use speedup, `baseline / Compilatrix`.
- **Split each gap** into more instructions versus lower IPC, using
  instructions, cycles and branch misses per operation.
- **Compare IR against IR.** Put Lean's final compiler IR beside Compilatrix's
  ownership and control-flow IRs for the same function.
  - Differences in allocations, reference-count operations or calls attribute
    the gap to the middle end.
  - Equal IR with more instructions attributes it to the backend.

## Timing boundaries

| Profile | Included | Excluded |
| --- | --- | --- |
| Entry | The operation with its guards, allocation and result handoff | Input preparation, full output checking, release |
| Lifecycle | Fresh input construction, the operation, order-sensitive result consumption, normal memory management | Dataset preparation, process startup, compilation |
| Release | Teardown of prepared results, where separable | Preparation and the operation |
| Startup | Process and runtime initialisation plus one operation | Compilation |

- Never mix profiles in a ratio.
- Bound retained inputs and outputs, and keep an observable, order-sensitive
  result sink so that the operation cannot collapse into a weaker
  computation.
- For tracing collectors, include representative collection cycles, and
  never pause timing around a collection triggered inside the interval.

## Correctness before performance

- **Artifacts:** build, check and time the same recorded digests.
- **Oracle:** each workload has an independent oracle, such as upstream
  expected output, known constants or official test vectors. Compare every
  output value, its order and its length.
- **Inspection:** inspect generated IR and assembly for runtime inputs, the
  intended operation and the output sink.
- **Failures:** wrong results, schema or artifact mismatches and failed
  processes stop publication of that row.

## Measurement policy

- **Same conditions:** compare implementations on the same host, core
  placement, dataset and profile. Record CPU, topology, memory, kernel,
  toolchains, frequency and SMT settings, the timer, and any uncontrolled
  conditions.
- **Calibration:** finish builds before timing, and calibrate operation
  counts in a separate pilot. Each timed chunk must dominate timer overhead.
- **Blocks:** collect randomised paired blocks with fresh worker processes
  and fixed warm-up. Retain every valid observation and every invalidated
  block with its reason, and never stop on a desired result.
- **Reporting:** report nanoseconds per operation, summarised within blocks,
  with uncertainty across blocks from a hierarchical bootstrap.
  - Keep per-family results.
  - A geometric mean names its common subset, weights and missing rows.
  - Never form a ratio across hosts.
- **Hardware counters** are optional diagnostic runs; an unavailable counter
  is not zero.

**Tiers:**
- *CI:* correctness and deterministic step counts from the x86 model.
- *Local:* paired A/B runs on the development machine, pinned to one core
  type.
- *Reference:* runs at phase exits.

Regression thresholds wait for a dedicated host with established variability.

## Memory, size and compiler cost

**Keep distinct:**
- live bytes, occupied capacity, cumulative allocation, allocator metadata
  and peaks;
- process RSS;
- observed stack high-water mark and supplied capacity;
- text and data size per function and per object;
- compiler time per stage, checker time, peak memory and evidence size.

**Compiler invocation** runs from Ixon ingress to emission. A comparison with
source-to-executable toolchains names the upstream frontend and export work
it includes.

## Optimisation experiments

**A paired experiment changes one policy** on the same source and inputs. It
retains:
- the checked evidence and exact artifacts;
- the fallback behaviour;
- runtime distributions;
- memory and reference-count observations;
- code growth and compiler or checker cost.

**It includes three cases:** one expected to benefit, a neutral or adverse
neighbour, and an invalid-evidence or exhausted-budget fallback.

Fewer reference-count operations or allocations need not reduce elapsed time,
and a measured decision to decline an optimisation is a valid outcome.

**Version and retain:**
- specifications, locks, datasets, adapters and schemas;
- raw samples;
- environments;
- analysis parameters.

Host timings stay outside deterministic compiler identities.
