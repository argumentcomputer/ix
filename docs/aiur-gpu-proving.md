# Proving on GPUs: lanes, generated traces, and how to benchmark them

For the current implementation checkpoint, compatibility design, and remaining
work, see the [2026-10-08 proof reuse handoff](lean-proof-reuse-handoff.md).

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
Proving automatically uses all visible GPUs and available CPU threads.
Omit `--max-ram` to detect the host budget from available RAM and remaining
cgroup capacity; `--max-ram 0` is equivalent. The 920 GiB cgroup cap below
is an example for a 1 TiB host and should match the job's resource allowance.

```sh
# 0. Seed the partition with the 78-leaf Mathlib cut measured in §6.
#    Oversized claims can be split during proving.
ix shard mathlib.ixe --shards 78 --out mathlib.ixes

# 1 + 2. Stage 1 and Stage 2 on all visible devices. Every claim's proof is
#    persisted as it lands; joins run as soon as their children exist;
#    the root is wrapped while its trace-shard count decreases, verified,
#    and its address printed on stdout. Check K=1 separately (see §7).
export AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_TRACE_SHARD_MAX_CELLS=1500000000
export AIUR_GPU_TRACE=generated AIUR_LANES_CACHE_DIR=$PWD/cache
systemd-run --user --scope -q -p MemoryMax=920G -- \
  ix prove --ixe mathlib.ixe --ixes mathlib.ixes \
    --out-ixes mathlib-proven.ixes \
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

Full-manifest `ix prove` uses every visible CUDA device by default;
`--lanes N` overrides the device count. It builds an `AiurSystem` pair per
device from the two compiled systems (nothing is copied across the FFI; the verifying keys do
not depend on the device, and every cache key and claim binding derives
from them) and runs one scheduler over them:

- **One execution pool.** Claims and ready joins execute on the host
  through one bounded queue, joins first, using the available CPU threads.
  `--exec-jobs` overrides the executions per lane. A prepared record goes
  to whichever device is free, so no packing is decided ahead of time.
- **Record reservations.** Each execution reserves its record's bytes from
  a shared pool sized from the detected host budget after workspace and
  headroom are reserved; the reservation follows the record
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

Automatic budgeting considers available host RAM and remaining capacity
under every visible cgroup ancestor. It reserves workspace per GPU and
10% headroom before admitting records. `--max-ram N` remains an optional
override for a fixed allowance: a positive value requests N GiB per GPU
lane, still bounded by remaining cgroup capacity. It is a planning budget;
the cgroup limit is the operating system's hard backstop. Concurrent records
share capacity, and host workspace planning can reduce trace-shard sizes.

The historical 4-GPU, 1 TiB measurements in §6 used
`--max-ram 230 --exec-jobs 3`: Mathlib's largest records were about 45 GiB
and the process peak stayed under 750 GiB. Those overrides identify the
measured configuration; normal runs use the automatic defaults above.

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
| `--texray` | Per-phase wall and RSS lines on stderr, as on the CPU. |

## 6. Benchmarking a multi-GPU run

The unit of measurement is one complete `.ixe`/`.ixes` pair under one
command, recorded with its identities. The script below preserves the
explicit settings used for the historical measurements. It writes the
provenance, samples the devices, runs the command under the cap, and keeps
the exit status. Use the automatic defaults in §2 for new runs unless a
comparison specifically requires these settings.

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
unset RUST_LOG MULTI_STARK_CUDA_MEMORY_LOG
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
| Per-claim and per-join execution time, record bytes, proof time, pool grants, waits, bisections | `[lanes]` lines in `lanes.err` |
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

## 7. Single L40S measurements and handoff (2026-10-06)

Init and ISLB (Init + Std + Lean + Batteries) both completed with a single
trace shard in the final proof, K=1, and native aggregate verification of
every included constant with zero undischarged assumptions. The source was
`6e2d1ae0bb60e51a87f7a8d61710ec48983382bf`; no prover changes were needed.

| Quantity | Init | ISLB |
|---|---:|---:|
| Unique environment constants | 56,810 | 184,450 |
| Environment shards | 8 | 24 |
| Input `.ixe` bytes | 143,891,360 | 426,164,672 |
| Owned block bytes in manifest | 66,709,356 | 183,237,200 |
| Generated-trace proving, through K=3 | 686.18 s | 2,033.36 s |
| Terminal K=3 → K=1 invocation | 35.33 s | 35.65 s |
| **Combined successful proving** | **12m01.51s** | **34m29.01s** |
| Final proof payload bytes | 5,603,962 | 5,602,266 |
| Peak process RSS | 124.42 GiB | 190.86 GiB |
| Peak sampled GPU memory | 38.55 GiB | 38.83 GiB |
| Input compilation, separately timed | 13.26 s | 28.00 s |
| Final native verification, external wall | 2.25 s | 2.64 s |

Combined proving is the sum of two separately timed invocations. It excludes
builds, input compilation, sharding, external verification, failed attempts,
and idle gaps. GPU measurements are one-second samples; RSS is GNU time's
process high-water mark. These are single successful runs, without a variance
estimate or matched Blackwell run. Worker intervals include host work and
persistence; overlapping phase totals are not additive wall time.

The [portable summary](benchmarks/l40s-2026-10-06/summary.json) includes
hardware, protocol parameters, input sizes, final proof addresses and hashes,
and the Mathlib extrapolation. Detailed evidence is preserved byte-for-byte:

- [Init generated-trace phase](benchmarks/l40s-2026-10-06/init-generated.json)
  ends at K=3; [Init terminal compression](benchmarks/l40s-2026-10-06/init-k1.json)
  supplies the K=1 result and combined total.
- [ISLB results](benchmarks/l40s-2026-10-06/islb.json) include the failed first
  attempt, successful retry, terminal compression, and native verification.
- [Init verification](benchmarks/l40s-2026-10-06/init-k1-verify.txt) and
  [ISLB verification](benchmarks/l40s-2026-10-06/islb-k1-verify.txt) record full
  coverage. The [artifact index](benchmarks/l40s-2026-10-06/artifact-index.json)
  records the original paths and SHA256 hashes of the copied evidence.

Absolute paths inside these historical JSON files identify the original
machine. Proof objects, compiled environments, caches, and build artifacts
are not included in this handoff.

### Native toolchain and measured settings

The host had one NVIDIA L40S, compute capability 8.9, 46,068 MiB visible
VRAM, driver 595.91.07, 32 logical CPUs (AMD EPYC 7R13), and 248 GiB host
RAM. The native build used CUDA 13.3.73, Lean 4.34.1, and Rust 1.99.0 via
`RUSTUP_TOOLCHAIN=stable`, outside a Nix dev shell. `stable` is a moving
selector; record the actual Rust version on the receiving machine.
The multi-stark pin was `acfc370a2e74affcb7e8ee218fbbaf80b9da1eef` and the
Batteries pin was `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`.

From the repository root, with native Lean 4.34.1 on `PATH`:

```sh
export CUDA_HOME=/usr/local/cuda-13.3 CUDA_PATH=/usr/local/cuda-13.3
export PATH="$CUDA_HOME/bin:$PATH"
export NVCC="$CUDA_HOME/bin/nvcc" CFLAGS=-std=gnu17
export RUSTUP_TOOLCHAIN=stable
export IX_CUDA_TRACE_CODEGEN=1 MULTI_STARK_CUDA_ARCHS=89
lake build ix
```

The measured native build took 438.84 seconds; cold dependency work on another
machine is additional. Leave build and CPU execution parallelism at their
defaults. Compile the supplied [Init](benchmarks/l40s-2026-10-06/Init.lean) or
[ISLB](benchmarks/l40s-2026-10-06/ISLB.lean) driver with `ix compile --no-build`
after its imports' oleans are available. ISLB needs Batteries built. Keeping
these drivers under the root project avoids resolving the unrelated FLT
dependencies of `Benchmarks/Compile`.

Both measured runs used `CUDA_VISIBLE_DEVICES=0`, `--trace-shards --lanes 1`,
32 default CPU execution threads, `MemoryMax=220G`, `MemorySwapMax=0`, and:

```sh
export AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1
export AIUR_TRACE_SHARD_MAX_CELLS=600000000 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_GPU_SEED_CACHE_BYTES=4294967296
export MULTI_STARK_CUDA_MEMORY_LOG=1
```

Use a fresh `AIUR_LANES_CACHE_DIR` for a timed cold proof. Init was explicitly
partitioned with `ix shard --shards 8` and proved with `--max-ram 180`; ISLB
used `--shards 24` and `--max-ram 100`. Always preserve `--out-ixes` and verify
against that final partition. Transparent huge pages were `always`, with
`defer+madvise` defragmentation. Both leaf and recursion proofs used
`logBlowup=2`, `capHeight=0`, and FRI parameters `logFinalPolyLen=0`,
`maxLogArity=1`, `numQueries=100`, `commitProofOfWorkBits=0`,
`queryProofOfWorkBits=20`. Older results with different query counts are not
matched baselines.

### Host memory and terminal compression

ISLB's first attempt used `--max-ram 180` and hit the 220 GiB host cgroup
limit after 44.746 seconds, before any completed claim proof. The successful
retry reduced only that budget to 100 GiB, retaining default CPU concurrency.
Its observed cgroup memory peak was 191.03 GiB. `--max-ram` governs scheduler
reservations; it is not a bound on actual process RSS. Execution arenas and
dependency byte buffers add memory outside logical record accounting.

At the 600-million-cell cap, both generated-trace runs stopped improving at
K=3. The current wrap loops accept a verified non-shrinking batch, so command
success alone does not establish K=1. The measured terminal fallback reused
the verified K=3 root with these settings:

```sh
export AIUR_GPU_TRACE=cpu AIUR_TRACE_ONLY_LOOKUPS=0
unset AIUR_TRACE_SHARD_MAX_CELLS AIUR_MAX_PIECE_LOG_HEIGHT
# Aggregate flags: --direct-joins --structural-above 0 --trace-shards
#                  --max-ram 180 --wrap-root --texray
```

This retains the CUDA backend, with large matrices placed on the host.
Materialized lookups (`AIUR_TRACE_ONLY_LOOKUPS=0`) are necessary for that
fallback. Simply raising the generated-trace cell cap does not make the
terminal matrix fit the L40S.

To resume through `ix aggregate`, the measured procedure used a separate
`AIUR_AGGREGATE_CACHE_DIR` containing the original root-slot cache key, with
its value set to the verified K=3 proof address. The original lanes cache
points to the unwrapped root. Supply the active leaf proof addresses and
the exact `.ixe` and final `-proven.ixes`; preserve the existing cache.
This requires the corresponding leaf proof objects and K=3 root in the
local Ix store: cache indexes contain addresses only. `--reprove-slot`
returns before root wrapping on this revision and is unsuitable here.

After compression, check that the batch preamble has exactly one header
and run `ix verify --aggregate --structural-above 0` against the final
manifest. Native verification establishes header/body count agreement,
cryptographic validity, full coverage, and absence of undischarged
assumptions. The terminal wrap took 32.8 seconds internally for each corpus;
the external invocation times above also include setup and persistence.

### Mathlib estimate and next-machine comparison

The predicted Mathlib proving time on this same L40S and host is **3.5–4
hours**, with a **3–5 hour planning range**, including aggregation and K=1
compression. No Mathlib proving run was performed for this estimate.

The documented canonical Mathlib corpus has 1,121,703,681 stored constant
bytes, versus ISLB's 183,237,200 owned block bytes: approximately 6.12 times
the data, giving `2069.01 s × 6.12 ≈ 3h31m`. Init independently scales to
about 3h22m. Stored constant bytes and manifest block bytes are closely
related but not identical because projection constants belong to their
home blocks; the documented Mathlib corpus also predates these runs.
The inputs and exact arithmetic are in `summary.json`.

This range assumes execution stays within host RAM. Mathlib's heavier
execution and dependency frontiers can increase work, and its larger
partition can occupy all 32 executors in the initial wave. Successful ISLB
admission does not establish that Mathlib fits. Review memory admission and
shard sizing before a full Mathlib run; smaller shards also increase join
work. Peak RAM should not be multiplied by the corpus-size ratio.

For a single RTX PRO 6000 Blackwell comparison, build for `sm_120` and first
match the source, inputs, protocol, partition, one-lane setting, and
600-million-cell cap. Record host hardware and use cold caches. A separate
96 GB configuration can then measure the benefit of larger trace shards.
The historical four-GPU Mathlib run in §6 has different corpus/settings and
host resources. The Blackwell arithmetic retained in the Init JSON is an
unmeasured sensitivity scenario, not an established per-GPU slowdown.

## 8. CSLib benchmark handoff (2026-10-07)

The run must certify CSLib at the v4.34.1 release, then certify two actual
later upstream main snapshots using the preceding catalog as `--base`.
Each export contains the Mathlib declarations CSLib imports; a separate
proof of all Mathlib is not a prerequisite. Completion requires verified
catalog certificates for all three snapshots and measured incremental reuse.
A cold proof followed only by an identical-snapshot repeat is insufficient.

The release input was built and exported locally. The later snapshots were
pinned and inspected, but their builds, exports and cross-toolchain proving
compatibility remain prerequisites. No CSLib proof has been generated.

### Pinned inputs and measured scope

| Input | Identity |
|---|---|
| CSLib `v4.34.1` | `7c8f6c0f67015df29b152fdcffaf7850db2e9185` |
| Mathlib dependency | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Lean toolchain | `leanprover/lean4:v4.34.1` |
| CSLib Lake manifest SHA256 | `c514c3beaef90c5dc4d58ceed377a17d93e6e926f6213ed48a5a288e5c9e7be8` |
| Ixon format | 4 |
| CSLib constants root | `f80bbc527eed7892206d4e6cf552dd21a33b723c569f43a698915aee39be2d30` |
| Original full CSLib `.ixe` SHA256 | `f8261c4521eb3b1e514474697d3e4153720ac28bc9975f3a51e8a39cc24015bc` |

The [revision manifest](benchmarks/cslib-2026-10-07/revisions.json) pins
the full commit IDs, timestamps, toolchains and complete Lake manifests:

| Stage | Upstream commit | Purpose | Lean / Mathlib |
|---|---|---|---|
| A | [`7c8f6c0`](https://github.com/leanprover/cslib/commit/7c8f6c0f67015df29b152fdcffaf7850db2e9185), Sep 24 | Cold v4.34.1 release catalog | 4.34.1 / `d13f23b` |
| B | [`3f4ec26`](https://github.com/leanprover/cslib/commit/3f4ec2623bd8c7c554167da2dc9e80fa75fcbd6b), Sep 25 | First main commit after the release, using A | 4.35.0-rc2 / `1cae91f` |
| C | [`255a404`](https://github.com/leanprover/cslib/commit/255a404cd12bab901c5c3e87fa2dbf7655196d8e), Sep 25 | Circuit output tuple refactor, using B | 4.35.0-rc2 / `1cae91f` |

A was released from a side branch and is not an ancestor of B. Main had
already moved to 4.35.0-rc2 before the release. Although B's own commit only
changes CODEOWNERS, A → B includes earlier main changes and different Lean
and Mathlib versions; it is not a no-change control. B → C is a direct parent
transition with identical dependency manifests and a real library refactor.
Report these transitions separately. Do not cherry-pick the changes onto A
or edit their toolchain pins: that would benchmark different snapshots.

Use the supplied [CompileCslib.lean](benchmarks/cslib-2026-10-07/CompileCslib.lean).
It uses a classic `import Cslib`, without a `module` header or seed filter,
so the export includes private declarations and the entire imported
environment. Compiling CSLib's own root module can select a different scope.
The separate `CslibTests` modules are outside this import scope.

| Measured quantity | CSLib import | Full Mathlib import |
|---|---:|---:|
| Requested Lean constants | 441,356 | 783,115 |
| Named Ixon entries | 445,875 | 790,417 |
| Unique anonymous constants | 385,304 | 689,374 |
| Ungrounded constants | 0 | 0 |
| Full environment bytes | 1,037,346,098 | 2,360,309,573 |
| Anonymous environment bytes | 519,496,338 | 1,194,407,419 |
| Export command wall time | 60.47 s | 146.83 s |
| Export peak process-tree RSS | 9.36 GiB | 17.83 GiB |

The verified union contains 704,001 unique constants: 370,677 shared,
14,627 present only in CSLib, and 318,697 present only in Mathlib. This
overlap establishes possible content reuse, not measured saved proving
time. The first CSLib proof must cover all 385,304 of its constants.

The [measurement summary](benchmarks/cslib-2026-10-07/summary.json),
[compile report](benchmarks/cslib-2026-10-07/cslib.report.json),
[dependency manifest](benchmarks/cslib-2026-10-07/cslib-lake-manifest.json),
and [artifact index](benchmarks/cslib-2026-10-07/artifact-index.json) are
portable evidence. Absolute paths inside reports identify the local machine.
Large environments and proof objects are not checked into Git.

### Exporter compatibility and input preparation

Use an immutable Ix checkout containing this handoff. The implementation
baseline is `5a5ef1cd84b3fac5444620f87734d8c0ac298370`; record the receiving
checkout's actual commit and build a fresh GPU binary using §7. Use SM 89
for L40S or SM 120 for the Blackwell machines. This binary, `IX_BIN` below,
must contain `catalog prove` and remain unchanged for all proving and
verification. Record its SHA256, toolchain versions and hardware.

The release exporter needs Lean 4.34.1; B and C need a separate Ix frontend
compatible with Lean 4.35.0-rc2, called `IX_EXPORT_RC2` below. Merely installing
that Lean toolchain does not make a 4.34.1-linked Ix frontend compatible with
its oleans. Build or port that exporter in a separate checkout and validate
it before the full GPU run. Changing the proving binary between A and B
invalidates the current catalog profile; use the frontend only to export B
and C, and keep `IX_BIN` for the serialized Ixon and proofs. Matching Ixon
format numbers alone does not establish compatibility with the prover's
primitive definitions and checking semantics.

The existing local export binary is recorded in `provenance.json`; it does
not contain the newly committed catalog driver. Neither a fully linked build
of that driver nor a 4.35.0-rc2 exporter has been validated locally.

The following Bash commands start in the Ix checkout after that GPU build.
They require Git, jq, GNU time and Lean/Lake 4.34.1 on `PATH`.
Keep this isolated checkout out of the larger `Benchmarks/Compile` project.

```bash
set -euo pipefail
IX_REPO=$PWD
IX_BIN="$IX_REPO/.lake/build/bin/ix"
mkdir -p "$IX_REPO/.lake/benches"
RUN_DIR=$(mktemp -d "$IX_REPO/.lake/benches/cslib-gpu.XXXXXXXX")
git rev-parse HEAD > "$RUN_DIR/ix.commit"
sha256sum "$IX_BIN" > "$RUN_DIR/ix-binary.sha256"

git init "$RUN_DIR/src"
git -C "$RUN_DIR/src" remote add origin https://github.com/leanprover/cslib
git -C "$RUN_DIR/src" fetch --depth 1 origin 7c8f6c0f67015df29b152fdcffaf7850db2e9185
git -C "$RUN_DIR/src" checkout --detach FETCH_HEAD
cd "$RUN_DIR/src"
test "$(git rev-parse HEAD)" = 7c8f6c0f67015df29b152fdcffaf7850db2e9185
test "$(cat lean-toolchain)" = leanprover/lean4:v4.34.1
cmp lake-manifest.json "$IX_REPO/docs/benchmarks/cslib-2026-10-07/cslib-lake-manifest.json"
lake exe cache get
lake build Cslib
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612

mkdir -p .lake/ix-benchmark
cp "$IX_REPO/docs/benchmarks/cslib-2026-10-07/CompileCslib.lean" .lake/ix-benchmark/
/usr/bin/time -v -o "$RUN_DIR/compile.time" \
  "$IX_BIN" compile .lake/ix-benchmark/CompileCslib.lean --no-build \
  --out "$RUN_DIR/cslib.ixe" --report "$RUN_DIR/cslib.report.json" \
  > "$RUN_DIR/compile.out" 2> "$RUN_DIR/compile.err"
jq -e '.written == true and .allowPartial == false and
  .ixeFormatVersion == 4 and .ungroundedCount == 0 and
  .uniqueAnon == 385304 and
  .root == "f80bbc527eed7892206d4e6cf552dd21a33b723c569f43a698915aee39be2d30"' \
  "$RUN_DIR/cslib.report.json"
sha256sum "$RUN_DIR/cslib.ixe" > "$RUN_DIR/cslib.sha256"

cd "$RUN_DIR"
"$IX_BIN" catalog assemble A.ixc cslib.ixe --labels Cslib \
  --toolchains leanprover/lean4:v4.34.1 \
  --pins git:https://github.com/leanprover/cslib@7c8f6c0f67015df29b152fdcffaf7850db2e9185
"$IX_BIN" catalog verify A.ixc --deep > A.catalog-verify.out
"$IX_BIN" catalog info A.ixc > A.catalog.json
```

After the compatible rc2 exporter is available, build and export the exact
B and C commits. The commands below use elan's toolchain selection, not a
fixed-version Nix `lake`. `IX_EXPORT_RC2` must be an absolute executable path.

```bash
: "${IX_EXPORT_RC2:?Set the absolute path to a validated Lean 4.35.0-rc2 Ix exporter}"
test -x "$IX_EXPORT_RC2"
PINS="$IX_REPO/docs/benchmarks/cslib-2026-10-07/revisions.json"
sha256sum "$IX_EXPORT_RC2" > "$RUN_DIR/ix-export-rc2.sha256"
for ID in B C; do
  REV=$(jq -r --arg id "$ID" '.revisions[] | select(.id == $id) | .commit' "$PINS")
  TOOLCHAIN=$(jq -r --arg id "$ID" '.revisions[] | select(.id == $id) | .toolchain' "$PINS")
  git init "$RUN_DIR/src-$ID"
  git -C "$RUN_DIR/src-$ID" remote add origin https://github.com/leanprover/cslib
  git -C "$RUN_DIR/src-$ID" fetch --depth 1 origin "$REV"
  git -C "$RUN_DIR/src-$ID" checkout --detach FETCH_HEAD
  (
    cd "$RUN_DIR/src-$ID"
    test "$(git rev-parse HEAD)" = "$REV"
    test "$(cat lean-toolchain)" = "$TOOLCHAIN"
    cmp lake-manifest.json "$IX_REPO/docs/benchmarks/cslib-2026-10-07/main-lake-manifest.json"
    elan run "$TOOLCHAIN" lake exe cache get
    elan run "$TOOLCHAIN" lake build Cslib
    test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = 1cae91f0957ccf8847f22a6239fa0c032a9e28c6
    mkdir -p .lake/ix-benchmark
    cp "$IX_REPO/docs/benchmarks/cslib-2026-10-07/CompileCslib.lean" .lake/ix-benchmark/
    /usr/bin/time -v -o "$RUN_DIR/$ID.compile.time" \
      elan run "$TOOLCHAIN" "$IX_EXPORT_RC2" compile .lake/ix-benchmark/CompileCslib.lean \
      --no-build --out "$RUN_DIR/$ID.ixe" --report "$RUN_DIR/$ID.report.json" \
      > "$RUN_DIR/$ID.compile.out" 2> "$RUN_DIR/$ID.compile.err"
  )
  jq -e '.written == true and .allowPartial == false and
    .ixeFormatVersion == 4 and .ungroundedCount == 0 and
    .leanToolchain == "4.35.0-rc2" and .uniqueAnon > 0' "$RUN_DIR/$ID.report.json"
  sha256sum "$RUN_DIR/$ID.ixe" > "$RUN_DIR/$ID.sha256"
  "$IX_BIN" catalog assemble "$RUN_DIR/$ID.ixc" "$RUN_DIR/$ID.ixe" \
    --labels Cslib --toolchains "$TOOLCHAIN" \
    --pins "git:https://github.com/leanprover/cslib@$REV"
  "$IX_BIN" catalog verify "$RUN_DIR/$ID.ixc" --deep > "$RUN_DIR/$ID.catalog-verify.out"
done
```

Each single-member catalog records one snapshot and its dependency closure.
The two-member Mathlib/CSLib comparison catalog is unnecessary. Catalog
verification checks artifact integrity, not a typing proof. Stop on a root
mismatch for A, an ungrounded export, or a format mismatch. Record B and C's
roots and counts from their own reports; A's measurements do not predict them.

Review the axiom declarations in all three exports and freeze one address
allowlist, `$RUN_DIR/axioms.txt`, covering the accepted declarations before
proving A. Changing the policy afterwards changes the proof profile. Do not
automatically approve the addresses printed by an unapproved-axiom error.
With a full import environment, declarations unrelated to a particular
theorem are also present; reviewing its axiom inventory is distinct from
showing which axioms that theorem uses.

Before the expensive baseline, exercise a small real A → B → C catalog
chain with the same prover and policy: use `ix shard extract` on each
export with `--consts Cslib.Circuits.Circuit.id`, assemble separate smoke
catalogs, and run the prove/base/verify sequence below. This declaration
exists in all three snapshots and is changed by C's wiring refactor. Check
that the C smoke plan has new subjects. Preserve smoke artifacts separately
and record their cache contribution; use a fresh worker account or isolated
worker filesystem for the timed cold baseline without deleting shared caches.

### Catalog baseline and real incremental revisions

Use `ix catalog prove` from A onward so the baseline has a `proving.json`,
cumulative corpus, partition and leaf inventory. The GPU driver uses all
visible devices and pipelines leaf proving and aggregation through the
shared record pool. A naked lane root cannot be supplied as `--base`.

The example below uses the trace settings from the v4.34.1 CSLib run on
two 96 GiB Blackwell devices and a 500 GiB host, with a 440 GiB process
limit. For L40S devices, use a 600-million-cell cap and a 4 GiB seed cache.
The host budget is detected automatically; omit `--max-ram` and leave CPU
execution and build parallelism at their defaults. The 64 initial shards
are a starting partition, not a measured memory bound. Validate exporter
and checker compatibility before attempting B or C on a newer Lean version.

```bash
unset CUDA_VISIBLE_DEVICES RUST_LOG MULTI_STARK_CUDA_MEMORY_LOG
export AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1
export AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_MAX_PIECE_LOG_HEIGHT=24
export AIUR_GPU_SEED_CACHE_BYTES=17179869184
test -f "$RUN_DIR/axioms.txt"
PREVIOUS=
for ID in A B C; do
  BASE_ARGS=()
  SHARD_ARGS=()
  if [[ -n "$PREVIOUS" ]]; then
    BASE_ARGS=(--base "$RUN_DIR/$PREVIOUS.ixc")
  else
    SHARD_ARGS=(--shards 64)
  fi
  COMMON_ARGS=("$RUN_DIR/$ID.ixc" "${BASE_ARGS[@]}" "${SHARD_ARGS[@]}"
    --allow-axioms "$RUN_DIR/axioms.txt" --structural-above 0
    --json)
  "$IX_BIN" catalog prove "${COMMON_ARGS[@]}" --plan-only \
    > "$RUN_DIR/$ID.plan.json" 2> "$RUN_DIR/$ID.plan.log"
  systemd-run --user --scope -q -p MemoryMax=440G -p MemorySwapMax=0 -- \
    /usr/bin/time -v -o "$RUN_DIR/$ID.prove.time" \
    "$IX_BIN" catalog prove "${COMMON_ARGS[@]}" \
    > "$RUN_DIR/$ID.result.json" 2> "$RUN_DIR/$ID.prove.log"
  /usr/bin/time -v -o "$RUN_DIR/$ID.verify.time" \
    "$IX_BIN" catalog verify-proof "$RUN_DIR/$ID.ixc" \
    --allow-axioms "$RUN_DIR/axioms.txt" --structural-above 0 --json \
    > "$RUN_DIR/$ID.verify.json" 2> "$RUN_DIR/$ID.verify.log"
  "$IX_BIN" catalog prove "${COMMON_ARGS[@]}" \
    > "$RUN_DIR/$ID.repeat.json" 2> "$RUN_DIR/$ID.repeat.log"
  jq -e '.status == "verified"' "$RUN_DIR/$ID.verify.json"
  jq -e '.status == "reused" and .newProofs == 0' "$RUN_DIR/$ID.repeat.json"
  PREVIOUS=$ID
done
```

On a runner without a user systemd manager, apply equivalent memory and
swap limits through the container or job runtime. Choose the hard limit
for that host; the detected budget accounts for the remaining capacity
under it. GPU runs reduce trace sizes to fit workspace and bisect
splittable claims that exceed the execution-record ceiling, checkpointing
the new partition and reusing completed proofs. A failed trace-plan search,
an oversized indivisible block, or an oversized aggregation record can
still stop the run. Repeating `--shards` with a different value does not
replan an existing pending catalog.

For a 32 GiB RTX 5090, a 300-million-cell cap and 2 GiB seed cache are
experimental starting settings. Qualify device fit on a small input first;
terminal compression needs separate qualification, even with host traces.

Accept A only after catalog proof verification covers all 385,304 snapshot
constants and native aggregate verification reports full corpus coverage
with zero undischarged dependency assumptions. B and C must each verify
against their own catalogs and cumulative corpora; their corpus counts can
exceed current snapshot counts because historical declarations are retained.
This is typechecking relative to the accepted axiom declarations, not a
claim that those axioms were proved. See
[incremental-catalog-proving.md](incremental-catalog-proving.md).
Neither result by itself proves that the pinned source generated this Ixon
snapshot; the build/export provenance must be authenticated separately.

Report final trace-shard count K alongside the proof address and size.
K=1 is a separate compression result, not a requirement for catalog reuse.
The catalog driver does not request terminal wrapping. If compressing a
root separately, keep the original certified record and caches intact;
do not overwrite `rootProof` by hand. Verify the compressed proof against
that catalog's recorded corpus and partition and record it as an additional
artifact. Measure compression separately from incremental proving.

### Resume, evidence and completion

Retain all three catalog directories, their `proving.json`, cumulative
`corpus.ixe`, pending state, original/final partitions, all reports/logs,
and the worker's `~/.ix/store` and `~/.ix/cache`. Preserve a custom aggregate
cache too if `AIUR_AGGREGATE_CACHE_DIR` was set. Cache indexes contain
addresses, not the proof objects. Keep this state on durable storage before
an ephemeral runner is destroyed, together with the exact prover binary,
exporter build identities and frozen axiom policy.

For interruption recovery, rerun the same catalog command with its original
`--base`, profile and caches. A pending record is not a certificate. The
driver publishes `proving.json` only after final verification; a subsequent
snapshot must use that completed catalog as its base.

For each transition, report new subjects, retained claims and changed base
claims from the plan; compare leaf claim/proof addresses in the two completed
records to count evidence actually reused. Retained-plan counts alone do
not establish a cache hit. Preserve the prover's reuse messages and aggregate
cache-hit messages. Separately report export/preparation, base verification,
leaf proving, aggregation and final verification time where observable, plus
end-to-end wall time, one-second GPU memory samples, process/cgroup peaks
and artifact sizes. A smaller declaration delta does not guarantee a
proportional runtime saving; old leaf proofs still undergo verification.

Completion means A, B and C each have a verified certificate, B was proved
using A and C using B, and repeats perform no new proving. A → B measures
the release-to-main transition including toolchain/dependency churn; B → C
measures an actual refactor with stable pins. Report errors or cache misses
explicitly. A successful cold proof alone does not complete this handoff.
