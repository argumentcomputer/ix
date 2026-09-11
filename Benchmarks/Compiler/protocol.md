# Native reversal suite protocol, version 1

The manifest freezes one synthetic runtime-input Compilatrix function and
handwritten comparison programs. `Benchmarks/Compiler/Data.lean` defines every scalar
input and its independent expected reversal. Inputs are read after compilation;
all Compilatrix cases use the same checked reversal and release object pair.

The dataset contains every length 0–64 with six primary patterns and three
large-integer patterns. Primary values are below `2^30`. Stress values are
`2^63-1`, `2^63`, and `2^64-1`, each repeated for its list. The arena checker
also visits every capacity from `n+2` to 66, for 19,305 case/capacity pairs.
The existing N2 gate supplies the original malformed-input and ABI matrix.
The Nat-to-Word adapter rejects integers at least `2^64` before conversion;
its input type excludes negative integers. Dataset padding and trailing bytes
must be canonical, and JSON observations must match the nonnegative oracle.

The binary format is exactly eight ASCII bytes `CPBN001\n`, an unsigned
little-endian 64-bit case count, and 585 fixed 544-byte records. A record has
four little-endian 64-bit words: length, pattern index, domain index, and
generator seed. Sixty-four payload words follow; words after the list's length
are zero. Record index is `9*length+pattern`. Patterns 0–5 are primary; patterns
6–8 have domain indices 1–3 respectively. The file has 318,256 bytes and the
manifest pins its BLAKE3. JSON diagnostics retain decimal integers exactly.

The timing schedule has eight ASCII bytes `CPBS001\n`, followed by five
little-endian 64-bit words: row count, samples per row, warm-up nanoseconds,
chunk operations, and mode (0 smoke, 1 pilot, 2 measurement). Each row contains
five more words: stable row ID, length, domain, profile, and operation count.
Row IDs index `timingCases` in the dataset generator. Profiles 0 and 1 mean
`entry+handoff` and `lifecycle`. The row order may change between paired blocks;
all implementations receive identical schedule bytes within a block. Pilot and
smoke records are excluded from the reference analysis.

Both profiles use fresh allocation. For `entry+handoff`, prepare 4,096
independently owned lists, clear each owning input slot before calling reversal,
and retain at most 4,096 outputs. Calls and handoff are timed; preparation,
full result checks, the digest, and release occur between timed chunks. At the
largest arena size, the list storage occupies 8,978,432 bytes per chunk, plus
the fixed input/output slots and allocator metadata. Only one list allocation
is live at a time during lifecycle work. No application arena pool substitutes
for fresh allocation; the system allocator can recycle its freed storage.

Lifecycle timing includes input list construction, reversal, an order- and
payload-sensitive result digest, and normal release. Immutable scalar datasets
are prepared in each language's scalar representation before timing. Sharing
those scalar values does not share the list spine. Each list digest folds the
returned payload words using the manifest's 64-bit recurrence, and a sample
sums its operation digests modulo `2^64`. Full correctness checks every value;
the timing digest supplements those checks. Operation boundaries remain visible
in generated code. Diagnostic instrumentation uses separate executions.

Lean uses consuming `List Nat` arguments and explicit RC release, compiled
through `leanc` with Lake's ordinary release flags (`-O3 -DNDEBUG`) and pinned
GCC. Its compiled
diagnostic inspects exclusive input spines and reused cons addresses. CakeML
uses ordinary nonnegative integer lists, its default optimizing register
allocator, and its simple copying collector with a 64 MiB heap and an 8 MiB
stack. Collection-triggering allocations stay inside the timed interval.
Separate GC diagnostics establish collection cycles, post-collection occupancy,
and bounded process memory; a terminal forced collection is a distinct result.
Dropping the final root is not reported as immediate reclamation.

The pilot records timer resolution and a minimal driver control, chooses common
operation counts, and freezes them before the 30 blocks in three sessions.
Each implementation starts a fresh process for each block, warms for at least
one second, and collects three samples for every scheduled row. Each sample
must accumulate at least 100 ms of timed work, and chunks must dominate clock
overhead. No outlier rule removes an observation merely for being slow.
Compilation and network setup finish before measurement. The run records core
placement, host limitations, executable identities, raw samples, and failures.

A retained C launcher forks each timed worker from a small process image before
executing it. Linux can preserve the pre-exec high-water RSS of the large Lean
runner; this extra fork prevents that inherited memory from appearing as the
worker's peak. Launcher startup is outside the native sample intervals. Current
RSS still comes directly from the worker's `/proc/self/statm`, and peak RSS from
its `getrusage(RUSAGE_SELF)` record.
The reference invocation also pins the controller to a different core from the
worker and its SMT sibling. Both affinity masks are retained in the environment.

Analysis takes the median within a block, then reports the distribution across
blocks. Speedup means baseline time divided by Compilatrix time. Bootstrap
resampling first draws three sessions with replacement, then ten complete
paired blocks within each selected session. The same 10,000 index vectors
apply to every implementation and within-block ratio, using seed 2671931027.
Quantiles interpolate linearly at `(n-1)*p`. Sessions consist of ten consecutive
blocks; a fixed 60-second idle interval separates them. They share one host and
one continuous run, so three session clusters give limited evidence about between-day variation.
There is no suite-wide ranking of
these lengths as if they were independent application workloads. A shared-host
run does not establish a dedicated performance-regression baseline.

The pilot targets 200 ms per aggregate sample to provide headroom above the
100 ms acceptance floor. A block invalidates on drift in boot, CPU identity or
topology, kernel, affinity/NUMA permissions, governor/turbo policy, clocksource,
or declared environment variables; a sample below the timer/chunk floors or
above 2 GiB peak RSS also invalidates its whole block. The runner retains up to
three complete attempts. Wrong results, schemas, artifacts, or process exits
stop publication. Slow observations, page faults, context switches, load, and
instantaneous frequency changes remain in the data. The protocol does not
reserve the host or SMT sibling.

The separate CakeML diagnostic runs length 64 in all four payload domains,
five samples each, using frozen operation counts. Every sample must include a
natural collection, and observed post-collection live data must stay below
8 MiB in the configured 64 MiB heap. It reports sample-envelope GC events,
the pinned runtime's GC clock, current RSS, and one terminal collection with
its own monotonic interval. Compiler wall/CPU/RSS envelopes and actual serialized
IR/HPT evidence sizes accompany native text and executable/dependency sizes.
The terminal request reads `Runtime.fullGC` through a runtime array because the
pinned optimizer folds the directly inlined constant request. The diagnostic
accepts only an actual additional GC event; `gc-smoke` checks this boundary in CI.

Two unchanged upstream entries, `applyClosed` and `letClosed`, use the same
sessions and block count for a separate opaque native-call profile. They return
3 and 4 without runtime arguments; their successors and four direct calls remain
in the emitted object. Full source/baseline heap observations, complete release,
supplied-state call certificates, ABI checks, and precise fallback neighbors are
retained. No runtime-input or general N3 claim follows from these closed rows.

## Commands and replay

Build the runner and producer/checker seeds in the pinned repository environment:

```sh
lake build compiler-benchmark compiler-source-native-runtime compiler-check-source-native-runtime \
  compiler-source-native-upstream compiler-check-source-native-upstream
```

Use fresh directories for each command. The four compiler paths must resolve
the exact lock in `toolchains.json`; CakeML's `basis_ffi.c` must be beside `cake`.
The Nix correctness check builds that pinned bootstrap and all six adapters.

```sh
.lake/build/bin/compiler-benchmark build BUILD --gcc GCC_PATH --clang CLANG_PATH \
  --compcert CCOMP_PATH --cakeml CAKE_PATH
.lake/build/bin/compiler-benchmark verify BUILD VERIFY
.lake/build/bin/compiler-benchmark smoke BUILD SMOKE 2
.lake/build/bin/compiler-benchmark gc-smoke BUILD GC-SMOKE 2
.lake/build/bin/compiler-benchmark analysis-self-check
taskset --cpu-list 0 .lake/build/bin/compiler-benchmark pilot BUILD VERIFY PILOT 2
taskset --cpu-list 0 .lake/build/bin/compiler-benchmark measure BUILD VERIFY PILOT MEASURED 2
.lake/build/bin/compiler-benchmark diagnose BUILD PILOT MEASURED/diagnostics 2
.lake/build/bin/compiler-benchmark analyze BUILD MEASURED MEASURED/analysis
.lake/build/bin/compiler-benchmark reproduce BUILD MEASURED REPLAY
```

Replace `2` with an available core before the pilot; later commands must use
that same core. `smoke` can choose the first permitted core when omitted.
Network setup, builds, correctness, and any concurrent benchmark jobs finish
before the pilot/reference measurement. The runner retains partial raw output
as it arrives. It does not append to an old run or silently resume a partial one.

`reproduce` extracts and validates every source file into a new directory,
starts processes with an empty environment plus the recorded build variables,
uses the retained hashed producer/checker/compiler seeds, rebuilds every kernel
and executable, checks byte equality and complete correctness, and regenerates
the analysis from the original raw records. A separate Nix check rebuilds the
project and runs correctness/smoke in its sandbox. Reproduction does not require
new clock readings to equal old ones or claim a second physical CPU.

The build retains source and tool identities, Nix closure paths, a source
archive including the dirty tree, commands/logs, actual objects, executables,
and the runner/checker seeds. The source study retained reference bundles under `benchmarks/runs/`
with digest-addressed archives; reviewed reports record their exact local
retrieval path and digest. Copy the entire archive when moving a result to
another storage service; temporary build directories are not its retention copy.
