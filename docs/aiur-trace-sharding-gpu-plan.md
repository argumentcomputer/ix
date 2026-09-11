# Running trace-sharded Aiur proofs on GPU: plan

> Superseded by `aiur-gpu-plan-status.md` (measured ladder, settled design,
> handoff). The numbers in §1 here are the pre-optimization baseline.

Companion to `docs/aiur-trace-sharding.md`, written against
`sb/aiur-trace-sharding-design` (ix `ab627cd6`, multi-stark `2042565b`) on
2026-09-10. Everything in §1 was measured on the 32-core / 249 GiB box with
one RTX PRO 6000 Blackwell (96 GB, driver 595.71, CUDA 13.2).

## 1. What already works (measured today)

`IX_CUDA=1 lake build ix` links on the branch, multi-stark's 14 batch tests
and 23 of 24 aiur tests pass on the CUDA backend, and **Init proven as a single
claim** (no env shards) goes end to end on the GPU:

| Quantity | Value |
|---|---|
| Init execution (one claim, 55,385 blocks) | 6.3 min, 85 GiB peak, record 80.5 GB |
| Whole-execution CPU prover peak (model) | 3.4 TB — unprovable unsharded |
| Plan (`AIUR_TRACE_SHARD_MAX_CELLS=1.5e9`, `AIUR_MAX_PIECE_LOG_HEIGHT=24`) | K = 40 |
| STARK batch (`stark/prove_batch`, Regenerate) | 625 s |
| Whole `ix prove` wall (execute + plan + prove + store) | 16:45 |
| Host peak RSS | 112 GiB |
| VRAM peak (nvidia-smi, 1 s samples) | 66.5 GB — fully resident, no spill |
| Proof bytes | 53.8 MB (40 shards) |
| Native `ix verify` | ok, 11.6 s |

Per-shard span means (n = 40 shards; witness and stage-1 run twice under
Regenerate):

| span | mean | share of 625 s |
|---|---:|---:|
| `aiur/witness` ×2 | 2.4 s | 31 % |
| `stark/stage1_commit` ×2 | 3.4 s | 44 % |
| `stark/lookup_construction` | 1.7 s | 11 % |
| `stark/quotient` | 0.9 s | 6 % |
| `stark/fri_open` | 1.0 s | 6 % |

Two conclusions drive the plan. First, witness building (CPU) and stage-1
commit are 75 % of the batch and both are paid twice under Regenerate; the
stage-1 commit is real GPU work (its LDE volume is ~6× the quotient's) but
an nsys profile of round 1 shows its kernels take ~1.2 s of a 3.4 s commit,
the rest being CUDA memory management: `cudaMallocManaged` of a control
block per LDE (1.1 s each, it synchronizes the device), `cudaMallocAsync`
re-mapping pool memory the driver released after every sync (up to 3.8 s),
and `cudaHostRegister`/`Unregister` of every large trace (~1 s + ~0.8 s,
per-page pinning on 4 KiB pages). Second, **1.5e9 committed cells ≈ 66 GB
resident**, i.e. ~44 B/cell including FRI workspace, so the 96 GB card's
practical budget is about 1.6–1.7e9 cells, not the 1.8e9 the design doc
projected from 40 B/cell.

Planner sweep on Init's row counts (offline `plan_file` test, cells = budget):

| cells | cap 2^22 | cap 2^24 | cap 2^25 | cap 2^26 |
|---|---|---|---|---|
| 1.0e9 | K 84, Σwidth 30.8k, pad 14 % | K 55, 25.4k, 23 % | K 56, 25.1k, 24 % | same |
| 1.5e9 | K 68, 30.2k, 14 % | K 40, 24.8k, 25 % | K 40, 24.2k, 29 % | K 38, 24.1k, 29 % |
| 1.8e9 | K 63, 30.1k, 14 % | K 36, 24.6k, 25 % | K 30, 23.8k, 29 % | K 34, 23.9k, 29 % |

(monolithic active width 12.8k; padded cells 4.2e10 real.) K is driven by
the tallest circuits, not by the budget: the width-16 memory table has 181 M
rows and the 925-wide blake3 compressor 12 M, and two pieces of one circuit
never share a shard, so the piece cap sets a floor on K.

## 1.1 Host setup that the numbers depend on

Transparent huge pages must be `always`. The §1 run was taken at the box
default (`madvise`) and paid 402 M minor page faults and 1,014 s of system
time; the query map madvises its own segments, but the witness matrices and
the CUDA backend's host buffers do not, so `madvise` leaves all of the
prover's allocations on 4 KiB pages. Pinning for `cudaHostRegister` is also
per page, so huge pages cut the registration cost the profile shows (~1 s
per large trace, plus ~0.8 s to unregister) by the same factor. The user
measured ~1.5× on CPU proving from this setting alone.

```
sudo sh -c 'echo always > /sys/kernel/mm/transparent_hugepage/enabled'
sudo sh -c 'echo defer+madvise > /sys/kernel/mm/transparent_hugepage/defrag'
```

`defrag` stays at `defer+madvise`; `always` there can stall allocations on
compaction. The setting does not survive a reboot: add
`transparent_hugepage=always` to the kernel command line for the prover
AMI. Without root, `MIMALLOC_ALLOW_LARGE_OS_PAGES=1` gets the allocator's
arenas (but not CUDA's host buffers) onto huge pages, and
`MIMALLOC_PURGE_DELAY=-1` stops freed shard buffers from being returned to
the OS and re-faulted by the next shard.

## 2. Memory placement (host vs device)

The split the question in the thread asks for is already the one the code
makes, and it is the right one:

- **Host only, never uploaded:** the query record (80 GB for Init), the
  per-shard `SystemWitness` (traces + lookup witness, ~18 GiB per Init shard),
  and the byte-table sources. Under `Regenerate` the record lives for the whole
  batch and each shard's traces are rebuilt from it; the host peak is the
  record plus one shard's witness plus CUDA pinned staging (112 GiB measured
  against the 158 GiB the CPU model projected).
- **Device, one shard at a time:** the committed matrices of the shard being
  proven (main, stage-2, quotient LDEs and their Merkle trees, FRI layers).
  With `Regenerate` only the 32-byte stage-1 caps survive the barrier, so VRAM
  never scales with K. `Retain` would pin K `CudaMmcsData`s on the device and
  is wrong on a GPU box; `retention_for` must never choose it when a device
  budget is in force.
- **PCIe traffic** is one bulk upload of each committed round per shard
  (~6 GB main + ~3 GB stage 2 + quotient per Init shard) plus the opened rows
  back. That is ~0.5 s per shard at PCIe 5 rates and is not the bottleneck.
  The latency hazard is elsewhere: multi-stark's *hybrid* commit path, which
  engages when `lde + minimum_free > free` and then streams LDE height groups
  across PCIe during quotient and FRI. That is the 2× vs 8× gap in the design
  doc. The rule is therefore: size shards so every committed round is resident
  (§3.1) and treat any `[multi-stark/cuda] ... host fallback` line as a plan
  failure, not a slow path.
- Under CUDA the lookup messages are evaluated on the device from the
  constraint graph (`lookup job k: graph=true`), so the host-side
  `LookupValues` in `Stage1` are dead weight on this backend; dropping them
  from the witness under `cuda` is a free host-RAM win (~a third of the
  witness bytes).

## 3. Plan

### 3.1 Make the device budget first-class (small, do first)

Today the cell budget is an undocumented env var that is only consulted
when the *host* peak exceeds `--max-ram`. Replace with:

- `ix prove --vram <GiB>` (and `ix aggregate --vram`), default auto from
  `cudaMemGetInfo` when the binary is CUDA-built — needs multi-stark to make
  `cuda::device_memory_info` public. Convert with the measured constant:
  `cells = 0.75 · VRAM / 44 B` (≈ 1.6e9 on 96 GB, 4e8 on 24 GB). Keep
  `AIUR_TRACE_SHARD_MAX_CELLS` as the override.
- With `--vram`, trace-shard whenever the plan has K > 1 regardless of the
  host gate; `--max-ram` becomes the host gate it already models under
  Regenerate (record + one shard + headroom). Force `Regenerate` when a device
  budget is set.
- Fix `plan_shards_within`'s infeasible-budget path: at 40 GiB (below Init's
  80 GB record floor) it ran the halving loop to zero cells, where every row
  becomes a piece and first-fit is O(pieces × shards); it sat single-threaded
  for 30+ minutes before being killed. Return `Err(record_bytes + tables)` up
  front when the floor exceeds the budget, and stop halving once the room is
  below the widest circuit.
- Default `MAX_PIECE_LOG_HEIGHT` to 24 under a device budget (2^22 was a CPU
  cache calibration); expose it as `--piece-cap`. At 1.5e9 cells this is
  K 68 → 40 with 18 % less summed width.

### 3.2 Hide the CPU work (the 2–3× that is actually available)

Round 1 and round 2 are sequential `.map`s over shards inside
`prove_batch_with`; the GPU idles during every witness build and the CPU
idles during every FRI. Two changes, both inside the batch driver:

1. **Two-lane pipeline per device:** build witness `k+1` on the CPU while
   shard `k` commits/proves on the device (one bounded channel of depth 1).
   Round 1 becomes max(2.4, 3.4) ≈ 3.4 s/shard and round 2 ≈ 7 s/shard:
   625 → ~420 s on Init, with host peak +1 witness (~18 GiB).
2. **Stop paying for allocation in stage-1 commit** (profiled, §1): keep
   the stream-ordered pool's memory across syncs (release threshold →
   unlimited), recycle the managed control blocks from a slab, and let huge
   pages (§1.1) make `cudaHostRegister` cheap; if registration is still
   visible after that, upload through the persistent pinned staging buffers
   instead of pinning each trace. Kernel time bounds the commit at ~1.2 s
   per Init shard.
3. **Trace-only witness under CUDA:** the CUDA lookup path evaluates every
   message from the committed trace (`lookup job: graph=true`), so the host
   lookup witness is never read; skip writing it (`AIUR_TRACE_ONLY_LOOKUPS`
   today, automatic once multi-stark exposes a trace-only `LookupValues`
   with a host fallback).

The second stage-1 commit under Regenerate remains GPU time even once the
witness is hidden; a header-only round 1 (LDE + hash, nothing retained) is
the follow-up if it shows in the profile after the above.

### 3.3 Multi-GPU (protocol needs nothing; the driver does)

multi-stark is one device per process (`MULTI_STARK_CUDA_DEVICE`), no
device-per-config API, and residency decisions read a global
`cudaMemGetInfo` with no reservation, so two provers on one device fight.
The cheapest correct topology is **one process per GPU, shards striped by
index**:

- `ix prove --trace-shards --lane g/G --round 1` executes, plans (the plan
  is a pure function of the record), commits shards `k ≡ g (mod G)`, writes
  the K/G headers; a coordinator (or the same CLI with `--round 2 --headers
  dir`) assembles the preamble and each lane finishes its shards. Each lane
  re-executes (6.3 min, 85 GiB host) — acceptable for G ≤ 3 on a 512 GiB box;
  serializing the record (raw arena dump) removes it later.
- In-process G-thread variant needs multi-stark to expose
  `GoldilocksBlake3Config::with_device(id)` (`CudaDft::new` exists but is
  unreachable from the config). Do that second.

### 3.4 Aggregation on GPU and the proof-size trade

The 40-shard proof is 53.8 MB against ~11.5 MB for a monolithic Init proof
(the summed active width is 1.9×, per-shard fixed costs the rest), and
`ix_aggr` wrap cost is proportional to child bytes. Measure next:

```
IX_CUDA=1 ... ix aggregate --trace-shards --vram 96 --max-ram 200 --jobs 1
```

on this leaf (the wrap's own execution is trace-sharded by the same path).
Expect the wrap to cost ~4–5× a monolithic wrap in circuit rows; levers, in
order of payoff: fewer shards (piece cap 2^25, budget 1.6–1.7e9), the q=50
recursion parameters from `HANDOFF-recursion-fri-params.md` (halves every
byte), and §13.2's range-sum recursion (verifies shard ranges instead of
wrapping whole batches). Decide the recursion shape only after this
measurement.

### 3.5 Scaling past Init

Init needs no env shards on one 96 GB GPU. Mathlib is ~25× Init in committed
cells (~1,000 shards at 1.5e9) and its single record is several TB, so it is
gated by §13.3 (distributed execution), not by the prover. Until then the
production shape is: **env shards sized to the host record budget** (e.g.
`ix shard --max-ram 300` on a 512 GiB box, ~40–80 leaves instead of 239) each
proven as a GPU trace-shard batch, then `ix aggregate` on the same box. The
lookahead-execute thread from the metal-48xl handoff (execute leaf `n+1`
while leaf `n` proves) is worth more on GPU than on CPU because proving is
now shorter than execution.

### 3.6 Tests and hygiene

- `padding_memory_rows_cannot_carry_multiplicities` fails under `--features
  cuda`: the CUDA path evaluates lookups from the constraint graph, so the
  forged `LookupValues` are ignored and the (trace-valid) proof verifies. Not
  a soundness gap; gate the test on `not(feature = "cuda")` with that note.
- Add a K = 4 batch CPU/CUDA byte-identity test (multi-stark's smoke covers
  single proofs only), and run `cargo test -p aiur --features cuda` in the
  smoke script.
- `docs/aiur-trace-sharding.md:745` still says the aggregate wrap is
  unsharded; it landed in `88c2e5b1`.
- VRAM is sampled nowhere; add a `cudaMemGetInfo` reading to the
  `stark/batch_round_*` spans once `device_memory_info` is public.

## 4. Order and cost

| step | effort | payoff |
|---|---|---|
| 3.1 `--vram`, planner floor fix, cap 24 | 1–2 days | correctness + usability; K 68→40 |
| 3.2.1 two-lane pipeline | 1–2 days | ~1.5× on the batch |
| 3.2.2 stage-1 commit profile/fix | 1–3 days | up to another ~1.4× |
| 3.4 wrap measurement | half a day (run) | decides recursion shape |
| 3.3 multi-process lanes | 2–3 days | ~G× on a multi-GPU box |
| 3.6 tests/docs | 1 day | — |

Reproduction of §1 (all inputs in `~/benchdata/trace-shards-gpu/`):

```
IX_CUDA=1 LIBCLANG_PATH=/usr/lib/llvm-18/lib lake build ix
ix compile Benchmarks/Compile/CompileInit.lean --out init.ixe
ix shard --shards 1 --out init-1.ixes init.ixe
AIUR_TRACE_SHARD_MAX_CELLS=1500000000 AIUR_MAX_PIECE_LOG_HEIGHT=24 \
MULTI_STARK_CUDA_MEMORY_LOG=1 \
  ix prove --ixe init.ixe --ixes init-1.ixes --shard 0 --max-ram 200 \
    --trace-shards --retention regenerate --texray --no-index
ix verify --ixe init.ixe --ixes init-1.ixes <proof address>
```
