# Compile

Test libraries for the Ix compiler

- [Init, Std, and Lean libraries](https://github.com/leanprover/lean4)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [Imperial College London FLT project](https://github.com/ImperialCollegeLondon/FLT)
- [Anthropic FLT proof artifact](https://github.com/anthropics/fermats-last-theorem)
- Every native TruthMines member, independently, through the generated
  `TruthMines/Members/<Qualifier>.lean` fidelity drivers
- [Palomar.ix](https://github.com/argumentcomputer/Palomar.ix) as one aggregate
  library (its colliding constituent projects remain in isolated workspaces)

## Usage

First ensure the Lean version used to build Ix matches the `Benchmarks/Compile/lean-toolchain` version (check against `ix --version`). Then run

`ix compile /path/to/Compile<Lib>.lean` # replace `<Lib>` with `Init`, `InitStd`, `Lean`, `Mathlib`, `FLT`, or `AnthropicFLT`

To retry only the Ix compiler using existing, up-to-date import artifacts:

```sh
lake exe ix compile Benchmarks/Compile/CompileAnthropicFLT.lean --no-build --verbose
```

Run this from the repository root. `--no-build` skips the target's Lake
build/cache step, including checks for generated C files. The input source is
still elaborated; missing imports fail, and stale imports are not rebuilt.
The outer `lake exe` may still rebuild the Ix executable itself.

For allocation-failure diagnostics, set `IX_MEMORY_DIAG=1` to log process
RSS, virtual memory, swap, system memory availability, and mapping counts
every five seconds during Ix compilation. `IX_LOG_IND_GROUPS=1` also logs
each inductive-validation group's entry/exit; unmatched `BEGIN` lines show
which groups were active if the process aborts. Both are opt-in and leave
the compilation algorithm unchanged.

Ix pins the [mimalloc Rust fork](https://github.com/argumentcomputer/mimalloc_rust)
with mimalloc v3.5.1 in `Cargo.toml`. This fixes v3.3.x rejecting its own
metadata for 16 GiB arenas and eventually exhausting `vm.max_map_count`
despite available RAM and swap ([upstream issue #1309](https://github.com/microsoft/mimalloc/issues/1309)).

Inductive-flag validation (setup stage 4) uses adaptive admission on Linux.
The Rayon pool keeps its configured size, but validation starts with two
active jobs and ramps up while memory is healthy. The controller samples
`MemAvailable`, visible cgroup-v2 ancestor limits, swap growth, and memory
stall pressure every 250 ms. It stops admissions and cancels excess attempts
under pressure; those attempts return normally, drop their scratch data, and
retry once alone after other work finishes. Completed validations are retained.
When retained data leaves limited headroom, validation continues one job at a
time while the safety reserve is available and the system is not reclaiming
memory. Low headroom alone does not keep resetting the recovery delay.
Expression walks preserve DAG sharing and check cancellation within the walk.

This is a soft safety mechanism, not a hard allocation limit: an individual
allocation, lazy import fetch, or destruction cannot be interrupted. A lone
attempt that exhausts the safety reserve returns `resourceLimit`, not an
invalid-proof error.
Non-Linux hosts without telemetry retain ordinary parallel validation.

`--verbose` reports `[validate_memory]` admission/pressure progress.
`IX_LOG_IND_GROUPS=1` distinguishes `END`, `CANCEL`, and `ERROR` with stable
group IDs. Optional controls:

- `RAYON_NUM_THREADS`: the pool-size ceiling, not a fixed active-job count.
- `IX_VALIDATE_MEMORY_GIB`: an additional process RSS-plus-swap soft budget
  during validation; system/cgroup headroom still applies. Swap is not
  counted as extra available RAM.
- `IX_VALIDATE_ADAPTIVE=0`: disable admission control (cannot be combined
  with an explicit memory budget). DAG-preserving walks remain enabled.

The main dependency scheduler also uses adaptive admission on Linux. It
starts with up to two active blocks and samples the same memory signals
every 250 ms, plus a ten-second forecast of recent memory growth. It raises
concurrency only after completed work and sufficient headroom, stops new
admissions under pressure, and waits five seconds after recovery before
resuming. Stable retained output can continue growing with one active block
while the safety reserve remains available. Main-stage expression transforms
also preserve DAG sharing instead of repeatedly copying shared subexpressions.

Unlike validation, main-stage blocks publish shared metadata during their
execution, so active blocks are **not cancelled or retried**: they finish and
release their scratch before the slot is reused. This is a soft safeguard,
not a hard memory cap; one large block can still exhaust memory. If no block
is active and admission cannot resume for 30 seconds, compilation returns
`resourceLimit`. The gate covers the main block scheduler, not graph setup,
final serialization, or other work outside that scheduler. Without Linux
telemetry, the scheduler retains fixed concurrency.

`--verbose` reports `[compile_memory]` limits, active blocks, admissions,
memory, and growth forecasts. Compilation progress shows recent completions,
active blocks, and time since the last completion instead of a lifetime-average
ETA or a `STALLED` label. Optional main-stage controls:

- `IX_COMPILE_WORKERS`: the worker-count ceiling (bounded by available CPUs).
- `IX_COMPILE_MEMORY_GIB`: an additional process RSS-plus-swap soft budget
  during main compilation; system/cgroup headroom still applies.
- `IX_COMPILE_ADAPTIVE=0`: use fixed admission (cannot be combined with
  `IX_COMPILE_MEMORY_GIB`). DAG-preserving transforms remain enabled.

The Anthropic artifact is also registered as the on-demand `AnthropicFLT`
benchmark environment. After building its oleans, benchmark the Ix compiler
and Rust kernel from the repository root with:

```sh
cd Benchmarks/Compile
lake build +CompileAnthropicFLT:olean
cd ../..
ix bench run --backend compile --env AnthropicFLT
ix bench run --backend ooc --env AnthropicFLT --ixe AnthropicFLT.ixe
```

For a TruthMines constituent, use the nested fidelity workspace, for example:

`ix validate Benchmarks/Compile/TruthMines/Members/Cli.lean`

The native member wrappers import the canonical generated TruthMines drivers,
so the catalog records remain the only source of dependency pins. Run the
complete sweep with `lake exe truthmines validate`; use `--only Cli,Palomar`
to select libraries.

> [!NOTE]
> Compiling Mathlib and the Imperial FLT project currently requires a
> multi-core CPU and >64 GB RAM. Anthropic reports that building its FLT
> artifact from scratch peaked at 153 GB RAM and used about 67 GB under
> `.lake/`, plus roughly 220 GB of generated C files. The `olean` facet above
> skips native object compilation, but Lean still emits those C files.
