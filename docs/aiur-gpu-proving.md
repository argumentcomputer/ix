# Proving on GPUs: multi-GPU scheduling, device traces, and how to benchmark them

Everything in this document builds on prover-level trace sharding
([aiur-trace-sharding.md](aiur-trace-sharding.md)): one execution of a
claim is proven as a batch of trace shards that each fit a device, and the
aggregation tree joins the claims' proofs into one root. This document
covers what the CUDA build adds: proving several claims at once on several
devices from one process, populating main traces on the device instead of
the host, and the settings and measurements a benchmark needs.

The scheduler is the aggregate controller (`crates/aggregate-controller`),
described in [formal-aiur-unified-controller.md](formal-aiur-unified-controller.md).

## 1. Building for CUDA

| Feature | Lake switch | What it compiles |
|---|---|---|
| `cuda` | `IX_CUDA=1` | multi-stark's CUDA backend: device LDEs, Merkle trees, lookup and quotient kernels, with sppark for every NTT. Proofs are the same Goldilocks/BLAKE3 protocol the CPU verifies. |
| `cuda-trace-codegen` | `IX_CUDA_TRACE_CODEGEN=1` | The CUDA row writers generated from the compiled bytecode (§4), their Rust seed packers, and the registry the trace runtime binds against. Implies `cuda`. |
| `formal-compiled-trace` | `IX_FORMAL_COMPILED_TRACE=1` | The `cuda` feature of `crates/formal-generated`: the CUDA row writers that `lake build ix` generates for formal IxVM (`AIUR_GPU_TRACE=compiled`; only IxVM's bundle is registered). Implies `cuda` and needs `nvcc`. |

The multi-GPU scheduler (§3) needs only `cuda`; generated traces are an
optional provider inside it. On the host the ordinary `ix` binary runs
everything else unchanged.

Build on a GPU host:

```sh
IX_CUDA_TRACE_CODEGEN=1 lake build ix
```

Before Cargo runs, `lake build ix` generates the formal native executors and,
in a CUDA build (`cudaEnabled` in `lakefile.lean`), the formal CUDA trace
writers into `.lake/build/formal-generated/`, loading the three certified
programs from the artifact cache (`.lake/aiur`) and compiling misses
concurrently ([code generation](formal-aiur-codegen.md)). A linked executor
whose fingerprint does not match the selected program is reported and that
program runs on the interpreter, with identical records and proofs.

The build detects the installed GPUs and compiles only their distinct SM
architectures. Set `MULTI_STARK_CUDA_ARCHS` explicitly for cross builds or
hosts without a GPU (`120` is Blackwell, `80` is the CI target).

The lakefile compiles the C units Cargo builds as C17: with glibc 2.38 or newer headers in C23 mode, mimalloc's
`strtol` would become `__isoc23_strtol`, which the link-time glibc of
Lean's bundled toolchain does not provide, and the final link would fail on
`libix_ffi_net.a`. No `CFLAGS` setting is needed. If `nvcc` is not on
`PATH`, set `NVCC` or `CUDA_HOME`.

CUDA-enabled Lean executables load `libmulti_stark_cuda.so` from `../lib` relative
to the executable; `ix` also loads `libix_bn254_cuda.so`, the KZG and PLONK
kernels compression uses. Both libraries are built
with a private static GNU C++ runtime and unwinder; only the C interface
is exported.
Lean keeps its bundled libc++. When copying an executable out of the build
tree, also copy the shared libraries in `.lake/build/lib` into the matching `lib/`
directory.

A binary linked by the Nix Rust toolchain runs on Nix glibc, whose loader
never searches `/usr/lib/x86_64-linux-gnu`; the statically linked CUDA
runtime then fails to open `libcuda.so.1` and reports "CUDA driver version
is insufficient" (error 35). Give it the driver library and the matching
`libstdc++`, nothing else, so libc is not mixed:

```sh
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export LD_LIBRARY_PATH="$(dirname "$(gcc -print-file-name=libstdc++.so.6)"):$LD_LIBRARY_PATH"
```

Binaries built with the host's own toolchain need neither.

A single proof selects a device with `--gpu-device N`, or with `IX_CUDA=1`
at run time and the device from `MULTI_STARK_CUDA_DEVICE` (default 0).
Verification and key export run on the CPU; the device does not enter the
verifying key or the proof. An explicit device request to a CPU-only build
fails.

## 2. The pipeline, end to end

With the `.ixe` compiled and the CUDA binary built, a whole environment
proves in three commands. Every `.ixe` is checked relative to a role
binding. A file without one is normalized in memory with the default
binding and handed to the Rust prover as an environment handle, so Lean and
Rust check the same bytes without a normalized copy on disk.

No sizing flags are needed. Both commands derive the same numbers from the
machine (`prover-resource-defaults.md`): a host budget of `MemTotal` less
20%, one lane per visible GPU, and shards sized so that three executions
per GPU plus each lane's queued and proving records fit in that budget.

```sh
# 0. Partition for the budget and GPUs `ix prove` will use.
ix shard mathlib.ixe --out mathlib.ixes

# 1. Prove every claim and every join on every visible GPU. Each claim's
#    proof is persisted as it lands; a join runs as soon as both children
#    exist; the root is verified and its address printed on stdout.
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$PWD/cache
ix prove --ixe mathlib.ixe --ixes mathlib.ixes --aggregate \
  --out-ixes mathlib-proven.ixes > prove.out 2> prove.err

# 2. Verify the root against the partition that was actually proven.
ix verify --aggregate --ixe mathlib.ixe \
  --ixes mathlib-proven.ixes "$(tail -1 prove.out)"
```

The prover reads neither free memory nor cgroup limits. To prove under a
memory cap, such as a benchmark harness's cgroup, set the cap outside the
process and pass the same budget to both commands (`--max-ram G`, the
whole process's budget in GiB) so the partition and the run agree.

Claims join directly, and every join is structural by default
(`--structural-above 0`). `ix verify` must use the same value as proving;
a root proved with `--structural-above 4096` verifies only with
`--structural-above 4096`. The fold never wraps a single claim; `--range`
is rejected. `--wrap-root` on `ix aggregate` wraps the root until it is
one trace shard.

Rerunning the same command resumes: completed claim proofs and join
subtrees are reused from the cache directory, and a bisected partition is
picked up from its checkpoint. `--out-ixes` matters because bisection
changes the partition, and `ix verify --ixes` must see the one the proofs
belong to.

The same work can be split across processes:
`ix prove --trace-shards --shards <ids>` proves a set of claims, and
`ix aggregate --trace-shards --subtree <slot>` proves one subtree of the
plan (`ix aggregate --plan-only` prints the slots). `--lanes` is the
one-process equivalent.

## 3. Multi-GPU: one resident prover per device

`ix prove --aggregate` builds one resident prover per visible GPU
(`--lanes N` overrides the count) and runs the controller over them
(`crates/aggregate-controller/src/lanes.rs`):

- **One execution pool.** Claims and ready joins execute on the host
  through one bounded queue, joins first, on executor threads that share
  the cores (`--exec-jobs` optionally caps them per GPU). A prepared record
  goes to whichever device is free, so no packing is decided ahead of time.
- **Admission by predicted record.** An execution starts only when the
  record pool admits it. Up to three per GPU (the count shards are sized
  for) are admitted as before, whenever one record share `s` is free.
  Beyond that, each is charged its predicted record (the `ix shard` record
  model over its owned and frontier bytes, corrected by the records
  measured so far in the run, or the size a previous run measured), and is
  admitted only while the running executions' charges, the records waiting
  for or in proof, its charge and one share kept free for overshoot fit
  the pool. Light claims therefore run many at once and heavy ones no more
  than fit; the controller never runs fewer than the fixed three per GPU.
- **Overshoot.** An execution that outgrows its charge grows into the free
  share without stopping anything. Past one share over its charge it waits
  behind the oldest waiting execution and never takes memory promised to
  another running execution; admission beyond three per GPU freezes until
  an execution finishes. Only when every execution waits and no record is
  draining is the youngest cancelled and requeued. Accurate predictions and
  a single overshoot of up to one share never freeze or cancel; the worst
  case is many light-predicted claims turning out heavy together, which a
  run's first measurement and the counted proving records bound
  (`prover-resource-defaults.md` §5.5 has the rule and its simulation).
- **Record reservations.** Each execution reserves its record's bytes from
  one pool: the process budget less each lane's prover workspace. The
  reservation follows the record through both proving rounds and is
  released when the proof lands.
- **Learning.** `--out-ixes` writes each executed claim's measured record
  into the partition it saves; a rerun on it admits those claims by their
  measured size. The log reports each claim's prediction and charge at
  dispatch, its record against the prediction at completion, and an
  `admission:` summary at the end: the measured/predicted distribution,
  overshoots, the most executions at once, frozen time, and cancellations
  with the executor-seconds they discarded.
- **The record ceiling.** An environment claim whose record would exceed
  128 GiB (`AIUR_RECORD_MAX_BYTES` overrides it) is stopped, its leaf
  bisected into two claims, and the partition checkpointed; the halves are
  proven and joined like any other leaves. The ceiling guards against a
  single claim starving the pool; it is not a performance setting.
- **Aggregation inside the run.** The plan is cut into subtrees from the
  root while a frontier node holds more leaves than the target; a subtree
  is proven as one task once its leaves exist, upper joins once both
  children are published, and the root is verified at the end.

Memory is governed by the process budget: the pool admits an execution
only while its predicted record fits. Records are tens of GiB, so starting
executions without regard to their records only makes them stall each
other and get cancelled (32 at once on Mathlib finished one at a time and
discarded ten); execution is usually what the GPU waits for.

On a host without GPUs, or with `--jobs`, `ix prove --aggregate` runs the
same controller on CPU lanes.

## 4. Device trace population

`AIUR_GPU_TRACE` selects how stage-one main traces are populated. Unset,
it is `compiled+generated` in a CUDA build that registers compiled writers
(`IX_FORMAL_COMPILED_TRACE=1`) with device lookups, and `cpu` otherwise.
Compiled writers fill the depth pass's columns; gap limbs' range-table
uses are counted at record upload by the interpreter's pass for every
device circuit. Memory stores and loads run on the device too: the record
upload holds the ROM cells of each width that a device circuit's stores or
loads access, in address order, with the same hash index as callee
queries. A store's address is the cell its values find, a load reads the
cell at its address. Compiled writers above 1 MiB of CUDA source are not
emitted (nvcc's time grows superlinearly with a straight-line function), so
those circuits are interpreted. With `AIUR_RECORD_REFS=1`, CUDA provers record, during execution, each
row's references: the callee rows its calls resolved to and the ROM cells
its stores and loads touched (`crates/aiur/src/refs.rs`, grouped per 256 rows
once execution ends). When the whole device record does not fit beside a
shard's proving, a proof uploads one shard image at a time instead: the shard's own device rows plus the rows and cells
their references name, gathered on the host while the previous shard proves
and uploaded by the shard's first tile, with hash indexes over just those
rows (a lookup that finds its key there finds the whole table's row, since
keys are unique). The planner charges the largest image, bounded by counting
each reference once per row block. Gap-slot range counts are taken shard by
shard at preparation. Recording costs execution time (7–12% on Init) and
about 8% more record, so it is off by default; a record without references
uploads the whole record as before. When the device record does not fit
beside the host layout's shards, the planner admits device circuits greedily in order of host
population saved per device byte (stage-one cells over the bytes of the
tables they read and their launch workspaces), skipping any that would
break the fit or the pipelining; the others report `device_layout`. The
record is charged at its allocations' sizes, without a margin: each
`cudaMalloc` above 1 MiB takes whole 2 MiB pages and smaller ones share
pages (measured; the model stays within 1% above an upload's measured
footprint). Launch workspaces are pooled so that compiled writers hold only
minimal ones and only interpreted circuits hold scratch, which the model
charges once per concurrent interpreted call rather than once per
concurrent call. On
Init (4 claims, one RTX PRO 6000) claims admitting about 189 of IxVM's 249
eligible circuits (a 21 GB record) populate in 11 s instead of 27 s, and
the run takes 7:03 against 7:29 with stores and loads on the host.

| Value | Population |
|---|---|
| `cpu` | Every circuit on the host. |
| `generated` | Function circuits whose population plans read only recorded calls, ROM cells, byte tables and word hints are filled on the device by `crates/aiur/cuda/population.cu`, which interprets the same compiled plans and group placements as the host writer. The record tables they read are uploaded once per proof, so the execution record can be dropped before proving. |
| `compiled` | Circuits covered by the compiled writers (`IX_FORMAL_COMPILED_TRACE=1`) run them; the rest stay on the host. |
| `compiled+generated` | Compiled writers where they exist, the interpreter for the remaining eligible circuits. |

Circuits with stream hints or maps outside the U8 library (outside a
compiled writer's closed forms), ROMs and fixed tables keep host rows. Proof bytes are identical in every mode. The planner chooses
the layout host population would get and populates on the device only if
the device record and its workspaces also fit there; otherwise that record
keeps host population (`device_layout` in the plan's host causes). Device
population therefore never changes a planned layout or a proof. Device modes need
device lookups, which are the CUDA default: the prover derives lookup
messages from the committed rows with multi-stark's graph evaluator.
`AIUR_TRACE_ONLY_LOOKUPS=0` builds host lookup buffers instead and rejects
the device modes; CPU builds always build host buffers.

`AIUR_GPU_TRACE_CIRCUITS=a,b` restricts device population to the listed
circuits, named by circuit or by member function. A generated source asked
to release its device state frees the uploaded record and re-uploads it on
the next tile. A streamed proof lends the device record its execution
record, which it holds for host population anyway, so the re-upload reads
that record and the host keeps no copy of the upload; device population
therefore never raises the planned host peak, and admission is bounded by
device memory alone. Without a lent record (direct callers of the
incremental witness API) the first release copies the record to host
memory. Multi-stark asks only when a phase's admission is short of device
memory, so the planner does not reserve the record beside the proving
peak. `AIUR_GPU_TRACE_RELEASE=0` pins the record instead and has the
planner charge it on the device.

`tools/ixvm/check-formal.sh` with `IX_TEST_CUDA=1` is the hardware gate:
it compares CPU and CUDA proofs and keys byte for byte across retention
policies and lookup modes, and verifies every proof on the CPU. Its CPU
controls run in ordinary CI. [formal-aiur-migration.md](formal-aiur-migration.md)
gives the commands.

## 5. Settings

| Variable or flag | Meaning |
|---|---|
| `AIUR_TRACE_SHARD_MAX_CELLS` | Committed cells per trace shard the planner cuts to on CUDA, default `1500000000`. That fits a 96 GB device at `log_blowup = 2`; the sizing rule is §7.1 of the trace-sharding document. |
| `--shard-rows N` | Maximum rows per circuit per trace shard (power of two). The default 0 lets the planner choose the largest shards that fit. Small caps multiply recursive verification work. |
| `AIUR_GPU_TRACE` | Main-trace population (§4). |
| `AIUR_TRACE_ONLY_LOOKUPS=0` | Host lookup buffers instead of device-derived lookups. |
| `AIUR_RECORD_MAX_BYTES` | The record ceiling (§3), default 128 GiB. Size it from the pool before a large run rather than relying on the default. |
| `AIUR_LANES_CACHE_DIR` | Where completed claim proofs, join subtrees and the partition checkpoint live between runs. |
| `--retention retain\|regenerate\|auto` | What a batch keeps between its two rounds. Multi-shard batches regenerate to bound device residency; single-shard batches can retain their commitment. |
| `--structural-above N` | Structural joins above N subject leaves, default 0 (every join). Verify with the same value. |
| `MULTI_STARK_CUDA_DEVICE` | Device for a single proof when `--gpu-device` is not given. |
| `--texray` or `IX_TEXRAY=1` | Per-phase wall and RSS lines on stderr, as on the CPU. The environment switch also enables TeXRay output for compression. |

Every proof uses the production STARK parameters: `log_blowup` 2, 100 FRI
queries and 20-bit query proof of work (`Parameters::DEFAULT` in
`crates/aiur/src/trace/stark.rs`), which meet the enforced security floor
([stark-parameters.md](stark-parameters.md)). The aggregate cache key includes
them, so a parameter change never reuses a cached proof.

## 6. Benchmarking a multi-GPU run

The unit of measurement is one complete `.ixe`/`.ixes` pair under one
command, recorded with its identities. The script below writes the
provenance, samples the devices, runs the one command under the cap, and
keeps the exit status.

Set `RUNS_DIR` to fast local storage for this script's outputs and proof cache.
For subsequent KZG compression, see
[the compression guide](../crates/proof-compression/README.md#proving-and-verification)
for output and cache placement. `RUNS_DIR` does not configure KZG cache paths.

```sh
#!/bin/bash
# run-multi-gpu.sh <label> [extra ix prove flags]
set -u
LABEL=$1; shift
# MAX_RAM (GiB) and MEM_MAX: set both to run under a cap; unset, the prover
# plans for MemTotal less 20% and no cgroup cap is applied.
MAX_RAM=${MAX_RAM:-}; MEM_MAX=${MEM_MAX:-}
IXE=${IXE:-mathlib.ixe}; IXES=${IXES:-mathlib.ixes}
BIN=${BIN:-$HOME/repos/ix/.lake/build/bin/ix}
OUT=${RUNS_DIR:-runs}/$LABEL; mkdir -p "$OUT/cache"
[ -n "${RECORD_MAX_GIB:-}" ] && export AIUR_RECORD_MAX_BYTES=$((RECORD_MAX_GIB << 30))
export AIUR_GPU_TRACE=${AIUR_GPU_TRACE:-generated} AIUR_LANES_CACHE_DIR=$OUT/cache
unset RUST_LOG
{
  echo "started $(date -u +%FT%TZ)  host $(hostname)"
  echo "ix $(sha256sum "$BIN" | cut -d' ' -f1)"; sha256sum "$IXE" "$IXES"
  echo "driver $(nvidia-smi --query-gpu=driver_version --format=csv,noheader | head -1)"
  echo "thp $(cat /sys/kernel/mm/transparent_hugepage/enabled) / $(cat /sys/kernel/mm/transparent_hugepage/defrag)"
  echo "flags ${MAX_RAM:+--max-ram $MAX_RAM} $*  cap ${MEM_MAX:-none}"
  env | grep -E '^(AIUR|MULTI_STARK)_' | sort
} > "$OUT/meta.txt"
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu \
  --format=csv,noheader,nounits --loop-ms=1000 > "$OUT/gpu.csv" 2>/dev/null &
SMI=$!
CAP=(); [ -n "$MEM_MAX" ] && CAP=(systemd-run --user --scope -q -p MemoryMax="$MEM_MAX" --)
"${CAP[@]}" /usr/bin/time -v "$BIN" prove --ixe "$IXE" --ixes "$IXES" --aggregate \
    ${MAX_RAM:+--max-ram "$MAX_RAM"} "$@" \
    > "$OUT/prove.out" 2> "$OUT/prove.err"
echo "exit $?" >> "$OUT/meta.txt"; kill $SMI 2>/dev/null
```

Before comparing two runs, hold fixed: the inputs by hash, the binary by
hash and feature list, the multi-stark pin, the settings in `meta.txt`, a
fresh cache directory, and the transparent-huge-page setting (`always`
with `defer+madvise`; neither survives a reboot). Overlapping CPU and GPU
phase totals must not be added as wall time, and sampled device memory is
a sample, not a high-water mark.

What to read off, and where:

| Quantity | Source |
|---|---|
| Wall and peak RSS | `/usr/bin/time -v` in `prove.err` |
| Per-claim and per-join execution time, record bytes, proof time, pool grants, waits, bisections | `[lanes]` lines in `prove.err` |
| Device utilization and memory over time | `gpu.csv` |
| Root address and verdict | last line of `prove.out`; `ix verify --aggregate` |

The latest whole-environment measurement predates role binding.
`formal-aiur-perf` at `b8e708a35` proved Init (`Init-230.ixes`, 3 shards,
from `ix shard Init.ixe --max-ram 230 --exec-jobs 3`) on one RTX PRO 6000
Blackwell with `--exec-jobs 3 --max-ram 230`, direct joins,
`--structural-above 0` and the production parameters in 7:30.2, at
131.8 GiB peak RSS. The root was `cf5b813b…`, covering all 56,810
constants. IxVM has since gained role binding, so the current code produces
a different root, and the figure has not been re-measured since. The device
was busy 32% of the run: the 3-shard partition is seeded for a 4-GPU host
and gives one GPU little overlap between execution and proving.

Two lessons from earlier large runs still apply. Size the record ceiling
from the pool before the run: a leaf whose record exceeds the ceiling is
bisected, and a core that still does not fit stalls the run until it is
restarted with a larger ceiling. And the scheduler dispatches leaves in
manifest order without size information, so a heavy leaf last is pure
tail.
