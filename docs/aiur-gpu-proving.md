# Proving on GPUs: lanes, device traces, and how to benchmark them

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

| Switch | What it compiles |
|---|---|
| `IX_CUDA=1` | The `cuda` feature: multi-stark's CUDA prover (device LDEs, Merkle trees, lookup and quotient kernels, sppark NTTs) and device trace population (`crates/aiur/cuda/population.cu`). Proofs are the same Goldilocks/BLAKE3 protocol the CPU verifies. |
| `IX_FORMAL_COMPILED_TRACE=1` | The `formal-compiled-trace` feature: CUDA row writers compiled for the exported IxVM artifact (`AIUR_GPU_TRACE=compiled`). Implies `cuda` and needs the artifacts `ix prepare` exports. |

Build on a GPU host:

```sh
ix prepare --cuda          # compile the IxVM, verifier and aggregation programs once per revision
IX_CUDA=1 MULTI_STARK_CUDA_ARCHS=120 CFLAGS=-std=gnu17 lake build ix
```

`ix prepare` records the artifacts in `.lake/aiur/native-kernels.env`; the
next `lake build ix` compiles the native executors generated from them
(see `formalNativeArtifacts` in `lakefile.lean`). Without them, execution
runs on the interpreter, with identical records and proofs. `ix prepare
--cuda` also builds the CUDA one-shot `stark-verifier` host that catalog
aggregation (`ix aggregate --ixc`) proves on.

`MULTI_STARK_CUDA_ARCHS` names the SM architecture (`120` is Blackwell,
`80` the CI container's Ampere). `CFLAGS=-std=gnu17` is required with
glibc 2.43 headers: in C23 mode mimalloc's `strtol` becomes
`__isoc23_strtol`, which the sysroot of Lean's bundled `clang`/`ld.lld`
does not provide, and the final link fails on `libix_ffi_net.a`. If `nvcc`
is not on `PATH`, set `NVCC` or `CUDA_HOME`.

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
Rust check the same bytes without a normalized copy on disk. The whole process goes under one cgroup cap, since one process
holds every worker and the record pool is what grows.

```sh
# 0. Partition. The CUDA build seeds the shard count from the per-lane
#    record share (--max-ram, --exec-jobs and the device cell budget).
ix shard mathlib.ixe --max-ram 230 --exec-jobs 3 --out mathlib.ixes

# 1. Prove every claim and every join on four devices. Each claim's proof
#    is persisted as it lands; a join runs as soon as both children exist;
#    the root is verified and its address printed on stdout.
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$PWD/cache
systemd-run --user --scope -q -p MemoryMax=920G -- \
  ix prove --ixe mathlib.ixe --ixes mathlib.ixes --trace-shards \
    --lanes 4 --exec-jobs 3 --max-ram 230 --out-ixes mathlib-proven.ixes \
    > lanes.out 2> lanes.err

# 2. Verify the root against the partition that was actually proven.
ix verify --aggregate --ixe mathlib.ixe \
  --ixes mathlib-proven.ixes "$(tail -1 lanes.out)"
```

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

The controller cannot yet discharge a role binding: `--assume-binding` and
`--binding-proof` are rejected with `--lanes`, `--aggregate` and
`ix aggregate`. Claims proved with `ix prove --ixe --ixes --assume-binding`
verify with `ix verify --binding-proof`.

## 3. Lanes: one resident prover per device

`ix prove --lanes N` builds one resident prover per device and runs the
controller over them (`crates/aggregate-controller/src/lanes.rs`):

- **One execution pool.** Claims and ready joins execute on the host
  through one bounded queue, joins first, `--exec-jobs` executions at a
  time per lane. A prepared record goes to whichever device is free, so no
  packing is decided ahead of time.
- **Record reservations.** Each execution reserves its record's bytes from
  a pool sized by `--max-ram` per lane; the reservation follows the record
  through both proving rounds and is released when the proof lands. Under
  pressure, executions wait for capacity; if waiters block each other, the
  youngest is cancelled so the selected one can finish.
- **The record ceiling.** An environment claim whose record would exceed
  128 GiB (`AIUR_RECORD_MAX_BYTES` overrides it) is stopped, its leaf
  bisected into two claims, and the partition checkpointed; the halves are
  proven and joined like any other leaves. The ceiling guards against a
  single claim starving the pool; it is not a performance setting.
- **Aggregation inside the run.** The plan is cut into subtrees from the
  root while a frontier node holds more leaves than the target; a subtree
  is proven as one task once its leaves exist, upper joins once both
  children are published, and the root is verified at the end.

Memory is governed by three numbers: `--max-ram` (the record pool per
lane), `--exec-jobs` (records in flight per lane), and the cgroup cap as
the backstop.

`ix prove --aggregate` runs the same controller on CPU lanes (`--jobs`).

## 4. Device trace population

`AIUR_GPU_TRACE` selects how stage-one main traces are populated:

| Value | Population |
|---|---|
| `cpu` (default) | Every circuit on the host. |
| `generated` | Function circuits whose population plans read only recorded calls, byte tables and word hints are filled on the device by `crates/aiur/cuda/population.cu`, which interprets the same compiled plans and group placements as the host writer. The record tables they read are uploaded once per proof, so the execution record can be dropped before proving. |
| `compiled` | Circuits covered by the compiled writers (`IX_FORMAL_COMPILED_TRACE=1`) run them; the rest stay on the host. |
| `compiled+generated` | Compiled writers where they exist, the interpreter for the remaining eligible circuits. |

Circuits with memory stores, loads or stream hints, ROMs and fixed tables
keep host rows. Proof bytes are identical in every mode. Device modes need
device lookups, which are the CUDA default: the prover derives lookup
messages from the committed rows with multi-stark's graph evaluator.
`AIUR_TRACE_ONLY_LOOKUPS=0` builds host lookup buffers instead and rejects
the device modes; CPU builds always build host buffers.

`AIUR_GPU_TRACE_CIRCUITS=a,b` restricts device population to the listed
circuits, named by circuit or by member function. With
`AIUR_GPU_TRACE_RELEASE=1`, a generated source asked to release its device
state copies the uploaded record to host memory once and re-uploads it on
the next tile; by default it stays resident, because releasing re-uploads it
about twice per shard on an Init leaf and costs more than the LDE spills it
avoids.

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
| `--texray` | Per-phase wall and RSS lines on stderr, as on the CPU. |

Every proof uses the production STARK parameters: `log_blowup` 2, 100 FRI
queries and 20-bit query proof of work (`Parameters::default` in
`crates/aiur/src/trace/stark.rs`). The aggregate cache key includes them,
so a parameter change never reuses a cached proof.

## 6. Benchmarking a multi-GPU run

The unit of measurement is one complete `.ixe`/`.ixes` pair under one
command, recorded with its identities. The script below writes the
provenance, samples the devices, runs the one command under the cap, and
keeps the exit status.

```sh
#!/bin/bash
# run-lanes.sh <label> [extra ix prove flags]
set -u
LABEL=$1; shift
LANES=${LANES:-4}; EXEC_JOBS=${EXEC_JOBS:-3}; MAX_RAM=${MAX_RAM:-230}; MEM_MAX=${MEM_MAX:-920G}
IXE=${IXE:-mathlib.ixe}; IXES=${IXES:-mathlib.ixes}
BIN=${BIN:-$HOME/repos/ix/.lake/build/bin/ix}
OUT=runs/$LABEL; mkdir -p "$OUT/cache"
[ -n "${RECORD_MAX_GIB:-}" ] && export AIUR_RECORD_MAX_BYTES=$((RECORD_MAX_GIB << 30))
export AIUR_GPU_TRACE=${AIUR_GPU_TRACE:-generated} AIUR_LANES_CACHE_DIR=$OUT/cache
unset RUST_LOG
{
  echo "started $(date -u +%FT%TZ)  host $(hostname)"
  echo "ix $(sha256sum "$BIN" | cut -d' ' -f1)"; sha256sum "$IXE" "$IXES"
  echo "driver $(nvidia-smi --query-gpu=driver_version --format=csv,noheader | head -1)"
  echo "thp $(cat /sys/kernel/mm/transparent_hugepage/enabled) / $(cat /sys/kernel/mm/transparent_hugepage/defrag)"
  echo "flags --lanes $LANES --exec-jobs $EXEC_JOBS --max-ram $MAX_RAM $*  cap $MEM_MAX"
  env | grep -E '^(AIUR|MULTI_STARK)_' | sort
} > "$OUT/meta.txt"
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu \
  --format=csv,noheader,nounits --loop-ms=1000 > "$OUT/gpu.csv" 2>/dev/null &
SMI=$!
systemd-run --user --scope -q -p MemoryMax=$MEM_MAX -- \
  /usr/bin/time -v "$BIN" prove --ixe "$IXE" --ixes "$IXES" --trace-shards \
    --lanes "$LANES" --exec-jobs "$EXEC_JOBS" --max-ram "$MAX_RAM" "$@" \
    > "$OUT/lanes.out" 2> "$OUT/lanes.err"
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
| Wall and peak RSS | `/usr/bin/time -v` in `lanes.err` |
| Per-claim and per-join execution time, record bytes, proof time, pool grants, waits, bisections | `[lanes]` lines in `lanes.err` |
| Device utilization and memory over time | `gpu.csv` |
| Root address and verdict | last line of `lanes.out`; `ix verify --aggregate` |

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
