# Proving on GPUs: lanes, generated traces, and how to benchmark them

Everything in this document builds on prover-level trace sharding
([aiur-trace-sharding.md](aiur-trace-sharding.md)): one execution of a
claim is proven as a batch of trace shards that each fit a device, and the
Stage 2 aggregation tree joins the claims' proofs into one root. This
document covers what the GPU build adds on top: proving several claims at
once on several devices from one process, generating the main traces on
the device instead of the host, and the knobs and measurements a benchmark
of either needs.

## 1. What the GPU build is

Three layers, each a Cargo feature over the previous one:

| Feature | Lake switch | What it compiles |
|---|---|---|
| `cuda` | `IX_CUDA=1` | multi-stark's CUDA backend: device LDEs, Merkle trees, lookup and quotient kernels, with sppark for every NTT. Proofs are the same Goldilocks/BLAKE3 protocol the CPU verifies. |
| `cuda-trace-codegen` | `IX_CUDA_TRACE_CODEGEN=1` | The CUDA row writers generated from the compiled bytecode (§4), their Rust seed packers, and the registry the trace runtime binds against. Implies `cuda`. |

The lanes scheduler (§3) needs only `cuda`; generated traces are an
optional provider inside it. On the host the ordinary `ix` binary runs
everything else unchanged.

Build on a GPU host:

```sh
IX_CUDA_TRACE_CODEGEN=1 MULTI_STARK_CUDA_ARCHS=120 CFLAGS=-std=gnu17 lake build ix
```

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

## 2. The pipeline, end to end

With `mathlib.ixe` compiled and the GPU binary built, a whole environment
proves in four commands. The run directory holds the inputs and the
caches; the whole process goes under one cgroup cap, since one process now
holds every worker and the record pool is the thing that grows.

```sh
# 0. Partition. The CUDA build seeds the shard count from the per-worker
#    record share (--max-ram, --exec-jobs and the cell budget below).
ix shard mathlib.ixe --max-ram 230 --exec-jobs 3 --out mathlib.ixes

# 1 + 2. Stage 1 and Stage 2 on four devices. Every claim's proof is
#    persisted as it lands; joins run as soon as their children exist;
#    the root is wrapped until it is a single trace shard, verified,
#    and its address printed on stdout.
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$PWD/cache
systemd-run --user --scope -q -p MemoryMax=920G -- \
  ix prove --ixe mathlib.ixe --ixes mathlib.ixes --trace-shards \
    --lanes 4 --exec-jobs 3 --max-ram 230 --out-ixes mathlib-proven.ixes \
    > lanes.out 2> lanes.err

# 3. Verify the root against the partition that was actually proven.
ix verify --aggregate --structural-above 0 --ixe mathlib.ixe \
  --ixes mathlib-proven.ixes "$(tail -1 lanes.out)"
```

Rerunning the same command resumes: completed claim proofs and join
subtrees are reused from the cache directory, and a bisected partition is
picked up from its checkpoint. `--out-ixes` matters because bisection
changes the partition, and `ix verify --ixes` must see the one the proofs
belong to.

The same two stages can still be driven by hand, one device per process,
with `ix prove --trace-shards --shards <ids>` for a lane's claims and
`ix aggregate --trace-shards --subtree <slot>` for its subtree; the lanes
scheduler is the one-process equivalent and is what the measurements in
§6 used.

## 3. Lanes: one resident prover per device

`ix prove --lanes N` builds an `AiurSystem` pair per device from the two
compiled systems (nothing is copied across the FFI; the verifying keys do
not depend on the device, and every cache key and claim binding derives
from them) and runs one scheduler over them:

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
  proven and joined like any other leaves. The ceiling is a guard against a
  single claim starving the pool, not a performance setting.
- **Stage 2 inside the run.** The aggregation plan is cut into subtrees
  from the root while a frontier node holds more leaves than the target;
  a subtree is proven as one task once its leaves exist, upper joins once
  both children are published, and the root is wrapped and verified at
  the end.

Memory is governed by three numbers and nothing else: `--max-ram` (the
record pool per lane), `--exec-jobs` (records in flight per lane, so the
cold wave and the speculative execution concurrency), and the cgroup cap
as the backstop. On a 4-GPU, 1 TiB host, `--max-ram 230 --exec-jobs 3`
keeps Mathlib's largest records (about 45 GiB) inside one lane's share and
the process peak under 750 GiB; `--exec-jobs 4` is 5% faster at the cost
of the pool running at 99%.

## 4. Generated traces

With `AIUR_GPU_TRACE=generated`, the main trace of every constrained
function is written on the device from a compact seed instead of being
built on the host and uploaded. The compiler derives, per function, a
**trace plan** from the compiled bytecode: which SSA values each row
needs, the seed words an execution records for it, and the column spans
it writes. From the plan it emits matching Rust seed packers and CUDA row
writers, and a registry with the program's fingerprint; at proving time
the runtime binds the registry after checking the fingerprint, and any
circuit the registry does not cover falls back to the CPU builder.

Seeds carry a **typed schema**: one width per word (`u8`, `u16`, `u32` or
full) derived from exclusive value bounds, so a byte-table operand costs a
byte on the wire. Round-two seeds stay resident on the device (bounded by
`AIUR_GPU_SEED_CACHE_BYTES`, 16 GiB by default) so regeneration does not
re-upload them; memory-table rows stay on the host unless
`AIUR_GPU_TRACE_MEMORY=1`, because a memory seed is the row minus one
column and generating them bought nothing on Init.

The generated units are checked in and regenerated like the executors:

```sh
lake exe ix codegen --trace-bundle          # regenerate the three programs' units
lake exe ix codegen --trace-bundle --check  # CI: fail on a stale unit
lake exe ix codegen --trace-report --target ixvm   # the plan inventory as JSON
lake exe IxTests aiur-trace-plan            # planner fixtures
cargo test -p aiur trace_codegen            # Rust parity, no GPU needed
```

The fixtures the Rust parity tests compile against are produced by the
same generator from two test programs:

```sh
lake exe trace-fixtures          # regenerate crates/aiur/src/trace_codegen/tests/* and cuda/generated/*
lake exe trace-fixtures --check  # fail on a stale fixture
```

The GPU-side parity tests and the two-round generated proof need a device:

```sh
NVCC=/usr/local/cuda-13.3/bin/nvcc MULTI_STARK_CUDA_ARCHS=120 \
  AIUR_TEST_GPU_DEVICES=0,1,2,3 \
  cargo test -p aiur --release --features cuda-trace-codegen
```

## 5. Knobs

The ones a run needs, then the ones a measurement might.

| Variable or flag | Meaning |
|---|---|
| `AIUR_TRACE_ONLY_LOOKUPS=1` | The lookup witness carries dimensions only; the device derives multiplicities and arguments from the committed trace. Required by every GPU trace provider and by trace sharding on the device. |
| `AIUR_TRACE_SHARD_MAX_CELLS` | Committed cells per trace shard the planner cuts to. `1500000000` fits a 96 GB device at `log_blowup = 2` with headroom; the sizing rule is §7.1 of the trace-sharding document. |
| `AIUR_MAX_PIECE_LOG_HEIGHT=24` | Caps a piece's trace height, so a tall circuit is cut shorter than the room alone requires, at one activation per extra piece. |
| `AIUR_GPU_TRACE=cpu\|generated` | Main-trace provider (§4); `cpu` is the reference builder and the default. |
| `AIUR_RECORD_MAX_BYTES` | The record ceiling (§3), default 128 GiB. Size it from the pool: 256 GiB at a 731 GiB pool held FLT's 174 GiB leaf without waits. |
| `AIUR_LANES_CACHE_DIR` | Where completed claim proofs, join subtrees and the partition checkpoint live between runs. |
| `--retention retain\|regenerate\|auto` | What a batch keeps between its two rounds. Every real GPU plan runs `regenerate`: round two rebuilds each shard from its seeds, which the resident seed cache makes cheap. |
| `MULTI_STARK_CUDA_MIN_FREE_BYTES` | Device headroom the backend keeps by spilling LDEs to the host; default a quarter of the card. |
| `MULTI_STARK_CUDA_MEMORY_LOG=1` | Logs stage-1 placement and per-lookup-job budget and free bytes to stderr. |
| `MULTI_STARK_CUDA_TRACE_FORCE_SPILL=1`, `MULTI_STARK_CUDA_LOOKUP_TRACE_TILE_ROWS=3` | Validation only: spill every LDE and regenerate from tiny tiles, to exercise the recovery path. |
| `AIUR_METRICS=<path.jsonl>`, `AIUR_METRICS_RUN_ID` | Lightweight per-piece and per-execution summaries (§6). |
| `AIUR_PROFILE=<path.jsonl>` | Timestamped span events, per-circuit witness time included. Heavier than metrics; not for timing runs. |
| `--texray` | Per-phase wall and RSS lines on stderr, as on the CPU. |

## 6. Benchmarking a multi-GPU run

The unit of measurement is one complete `.ixe`/`.ixes` pair under one
command, recorded with its identities. The script that produced the
measurements below does only this: write the provenance, sample the
devices, run the one command under the cap, and keep the exit status.

```sh
#!/bin/bash
# run-lanes4.sh <label> [extra ix prove flags]
set -u
LABEL=$1; shift
EXEC_JOBS=${EXEC_JOBS:-3}; MAX_RAM=${MAX_RAM:-230}; MEM_MAX=${MEM_MAX:-920G}
IXE=${IXE:-mathlib.ixe}; IXES=${IXES:-mathlib.ixes}
BIN=${BIN:-$HOME/repos/ix/.lake/build/bin/ix}
OUT=runs/$LABEL; mkdir -p "$OUT/cache"
[ -n "${RECORD_MAX_GIB:-}" ] && export AIUR_RECORD_MAX_BYTES=$((RECORD_MAX_GIB << 30))
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$OUT/cache
export AIUR_METRICS=$OUT/metrics.jsonl AIUR_METRICS_RUN_ID=$LABEL
unset AIUR_PROFILE RUST_LOG MULTI_STARK_CUDA_MEMORY_LOG
{
  echo "started $(date -u +%FT%TZ)  host $(hostname)"
  echo "ix $(sha256sum "$BIN" | cut -d' ' -f1)"; sha256sum "$IXE" "$IXES"
  echo "driver $(nvidia-smi --query-gpu=driver_version --format=csv,noheader | head -1)"
  echo "thp $(cat /sys/kernel/mm/transparent_hugepage/enabled) / $(cat /sys/kernel/mm/transparent_hugepage/defrag)"
  echo "flags --lanes 4 --exec-jobs $EXEC_JOBS --max-ram $MAX_RAM $*  cap $MEM_MAX"
  env | grep -E '^(AIUR|MULTI_STARK)_' | sort
} > "$OUT/meta.txt"
nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu \
  --format=csv,noheader,nounits --loop-ms=1000 > "$OUT/gpu.csv" 2>/dev/null &
SMI=$!
systemd-run --user --scope -q -p MemoryMax=$MEM_MAX -- \
  /usr/bin/time -v "$BIN" prove --ixe "$IXE" --ixes "$IXES" --trace-shards \
    --lanes 4 --exec-jobs "$EXEC_JOBS" --max-ram "$MAX_RAM" "$@" \
    > "$OUT/lanes.out" 2> "$OUT/lanes.err"
echo "exit $?" >> "$OUT/meta.txt"; kill $SMI 2>/dev/null
```

Before comparing two runs, hold fixed: the inputs by hash, the binary by
hash and feature list, the multi-stark pin, the knobs in `meta.txt`, a
fresh cache directory, and the transparent-huge-page setting (`always`
with `defer+madvise`; neither survives a reboot). Overlapping CPU and GPU
phase totals must not be added as wall time, and sampled device memory is
a sample, not a high-water mark.

What to read off, and where:

| Quantity | Source |
|---|---|
| Wall and peak RSS | `/usr/bin/time -v` in `lanes.err` |
| Per-claim and per-join execution time, record bytes, proof time | `metrics.jsonl`, one JSON line per execution and proving piece, with the `AIUR_*` knobs in the `summary` record |
| Pool grants, waits, bisections | `[lanes]` lines in `lanes.err` |
| Device utilization and memory over time | `gpu.csv` |
| Root address and verdict | last line of `lanes.out`; `ix verify --aggregate` |

Measured on 4× RTX PRO 6000 Blackwell (96 GB each), 96 CPUs, 1 TiB, CUDA
13.3, with the knobs above (`--exec-jobs 4` for the second column):

| | Mathlib, 78 shards, first-party kernels | Mathlib, 78 shards, sppark | Anthropic FLT, 572 shards |
|---|---:|---:|---:|
| Wall | 37:59 | 36:00 | 5:35 (after a restart, see below) |
| Claim proof, mean / total | 59.3 s / 4,623 s | 54.5 s / 4,249 s | 55.7 s / 31,799 s |
| Join proof, mean / total | 28.2 s / 2,253 s | 25.5 s / 2,041 s | 23.4 s / 13,444 s |
| Claim record, mean / max | 28 / 44 GiB | 28 / 44 GiB | 32 / 174 GiB |
| Peak process RSS | 733 GiB | 697 GiB | 527 GiB |

Execution sets the pace in both: the claim phase is execution-bound, and
the GPUs are busy about half the time. Proving itself got 8 to 9% cheaper
on sppark for the same records.

The FLT run hit the ceiling: one leaf's record was 174 GiB against the
128 GiB default, and after four bisection rounds the core still would not
fit, so the run was restarted with `RECORD_MAX_GIB=256`, which reused the
571 finished claims and seven join subtrees and proved the leaf whole in
20 minutes. Two lessons for the next large environment: size the ceiling
from the pool before the run rather than from the default, and know that
the scheduler dispatches leaves in manifest order without size
information, so a heavy leaf last is pure tail. The out-of-circuit profile
predicts record size well enough to order by (bytes plus `nat_arith`
count, correlation 0.8 over the 572 leaves), and reordering the manifest
by predicted size is a few lines over `.ixes`; it is not part of `ix shard`
yet.
