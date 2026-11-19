# Aggregate prover performance plan

What limits Mathlib aggregate proving after the November 17 runs, and the
designs proposed to remove each limit: a per-shard GPU record, GPU hint
channels, and a faster execution index.

- Branch: `ci-merge-tests` (uncommitted work).
- Hardware: 1× RTX PRO 6000 (~102 GB usable), 32 logical CPUs, 250 GB RAM.

## 1. Where we are

Mathlib (63 claims, 684,697 constants) aggregate proving. All three November 17
runs verify the same root, `e9ade9ab…`.

| Run | Command wall | Start to root verified | Main change |
|---|---|---|---|
| Nov 5 baseline | 2:04:27 | n/a | Earlier controller |
| prove3 | n/a: process killed by signal 15 at 6:21:30, after the root verified | 8125 s | Prediction-based admission |
| prove4 | 2:08:17 | 7563 s | Trace preparation on executors, ROM on device, early acceptance |
| prove5 | **2:00:45** | **7110 s** | Device record released without a host copy (lent record) |

Start to root verified is the comparable column across November 17 runs.
prove3 reached its root at +8125 s, then hung after verification until it was
killed.

Final compression, for context: Init 143.6 s (median of three warm runs) and
Mathlib 168.1 s (one warm run, earlier binary). Both keep the 864-byte PLONK
proof and report 285,614 gas for the verifier call. Aggregate execution and
trace delivery dominate end to end, not compression. Measurements:
`docs/measurements/aiur-compression-l3-ladder.json`
(Init) and `…/aiur-compression-mathlib-l3-ladder.json` (Mathlib).

Since prove5, not yet measured on Mathlib:

- The 25% GPU safety margin is removed.
- Launch workspaces are no longer over-charged about 16× for the one
  interpreted circuit.

With both, every Init claim admits all of its device circuits at the default
layout.

## 2. Where the time goes

One GPU worker proves claims and aggregations in turn. Executors run claims and
aggregations on the CPU and hand their records to the worker. In prove5:

| Worker timeline | Seconds |
|---|---|
| Proving (claims 2,952 + aggregations 1,577) | 4,529 |
| Waiting for trace shard witnesses (stall) | 757 |
| Other time inside proof items (preparation, verification, publishing) | ~389 |
| Idle between items, waiting for executions | ~1,440 |

"Proving" is the prover's wall time minus witness waits, not GPU kernel time:
it includes host work the prover does between kernels. Claims executing at
once: about 3 (memory-bound). The machine has 32 logical CPUs, and the
controller runs 32 executor threads, most of them waiting on record memory.

There are two separate limits:

- **Stall** is latency on the GPU's critical path: the host can't build the
  next trace shard as fast as the GPU proves the current one. Moving trace
  population to the GPU removes it.
- **Idle** is execution throughput. Each claim executes single-threaded, and
  records of 40–90 GiB against a 180 GiB pool allow only about three at once.
  CPU cores are mostly idle. Freeing CPU doesn't help here; faster execution or
  smaller records do.

Subtracting today's stall suggests the run would fall to roughly
6,000–6,500 s before execution throughput alone limits it. That is a
projection, not a measured floor. Moving population to the GPU also changes
GPU work, uploads, record lifetimes and admission. Treat the range as a guide
to which limit comes next, and measure it.

## 3. Large-claim stall (partly fixed)

A claim's trace is cut into n shards of about 1.5 billion cells. With
regeneration, the prover asks for 2n−1 shard witnesses: one commit round over
every shard, then a second round over shards 1…n−1. A producer builds the next
witness while the GPU works on the current one. Circuits whose record data is
on the GPU are filled there. The host fills every other circuit on every
supply.

GPU memory must hold two things:

- one shard's proving data, which is fixed by the shard size;
- the uploaded device record, which grows with the claim.

A small claim's record fits whole. A large one doesn't, so admission keeps only
part of it on the GPU, and the host fills the rest on every supply:

| Claim shards | Host time per supply | GPU per supply | Stall |
|---|---|---|---|
| 17 | 0.37 s | ~1.0 s | 2.4 s |
| 24 | 0.80 s | ~1.0 s | 10 s |
| 34 | 1.18 s | ~1.0 s | 28 s |
| 41 | 1.36 s | ~1.0 s | 43 s |

Fixed so far:

- **Release copy charged to the host** (in prove5). Admission was capped by
  host memory for a host copy of the device record that a streamed proof never
  needs. The proof now lends its execution record to the device record
  (`DeviceRecord::attach`). Claim stall went from 981 s to 722 s.
- **25% device margin and a 16× workspace charge** (since prove5). The record
  model now uses CUDA's measured allocation granularity. It is an upper bound
  within 1% of real uploads. Room for the record beside proving grows from
  about 23 GB to about 29 GB.
- **Smaller shards for large claims** (removed). Under a constrained budget on
  Init, claims ran 8–16% faster, but the extra shards slowed aggregation by as
  much. End to end it was neutral, and per-shard device records (§4) make full
  admission the norm.

Mathlib device records are about 0.72× the host record, so 35–66 GB. That still
exceeds 29 GB for the largest claims.

## 4. Per-shard device record (milestone 1 built, off by default)

**Built so far (gather and hash):** execution records each row's references
(`crates/aiur/src/refs.rs`), compacted per 256-row block, sorted and without
repeats, so per-row order is gone. Each shard image is the shard's own rows
plus the referenced rows and cells (and, for depth slots, rows with the same
key in functions sharing the callee's chip), with GPU hash indexes built over
just those rows; the kernels still hash and probe, now over the small image.
Direct references (`refs[next++]`, no lookups), as designed below, are a
separate later step: they need a per-row representation in execution order
and their own validation of that order against the fill plans' nodes.
`AIUR_SHARD_IMAGE_REPORT=1 ix prove --exec-only --shard K --gpu-device 0`
prints each shard's planned bound and gathered image beside the whole record.

Upload only what each shard's device rows read: their own rows, plus a
gathered, deduplicated block of the callee rows and ROM cells they reference.
This happens in two milestones:

- **Milestone 1, gather and hash (built; `AIUR_RECORD_REFS=1`).** Execution records which
  callee rows and ROM cells each block of 256 rows reads, compacted per block
  (sorted, deduplicated). Each shard's upload is the gathered subset, and the
  GPU keeps its hash lookups over that smaller record. This alone lets large
  claims fit on the GPU.
- **Milestone 2, direct references (later, separate).** Kernels read
  `refs[next++]` instead of probing. Block compaction drops per-row order, so
  this needs a per-row representation and its own validation.

### Measurement

A diagnostic ran every device-eligible row of each shard through the host fill
and counted the distinct callee rows and ROM cells each shard reads. It has
since been removed. Review found an undercount in a later version of it (16
bytes of referenced ROM reported as 8). The numbers below come from the
earlier version, but they should be re-measured with a corrected, reproducible
tool before they are relied on.

| Claim | Whole device record | Per shard (own + reads) | Share |
|---|---|---|---|
| Init claim 0 (16 shards × 8.4M rows) | 21.6 GB | 1.1–3.6 GB | 5–17% |
| Mathlib claim 30 (81 shards × 4.2M rows) | 56.3 GB | 0.3–2.5 GB | 1–4.5% |

- Mathlib's whole record is 42.7 GB of tables, 8.7 GB of hash indexes and
  5.0 GB of ROM.
- A shard reads 1.2–2.6× its own rows, and no shard touches more than 16% of
  ROM.
- Reads scale with the shard, not the claim.
- The proving run uses 41 shards of 8.4M rows. Merging adjacent measured pairs
  bounds those shards at about 1.2–4.6 GB each.

### Design

1. **Record references at execution.** The executor already resolves every call
   to a callee row: a memo hit, or a new row inserted before its body runs. It
   also resolves every ROM load and store to a cell. Record these as `u32`
   references and compact them per 256-row block. Do it in both the
   interpreter and the native runtime, which must produce identical records.
2. **Gather per shard on the host.** For each device circuit's slice, gather its
   own rows, the referenced rows (outputs and depths), and the referenced
   cells. Also gather rows of other functions that share the circuit's chip
   and match. Uploads overlap the previous shard's proving.
3. **Kernels.** Milestone 1 keeps the GPU hash lookups (`find_query`,
   `find_row`) over the gathered record. Milestone 2 replaces them with direct
   references. Either way, arithmetic and placement stay identical, so proof
   bytes don't change.
4. **Depth range counts.** Today they come from one pass over every real row at
   upload, because fixed range tables are committed first. They move to a
   counting pre-pass or to the executor, with exact equality.
5. **Planning.** The device term becomes the largest per-shard image. Greedy
   partial admission stays as a fallback.

### Costs and checks

- **Record memory.** Record memory limits execution concurrency, so this is the
  main risk. Gates: growth at most about 10%, slowdown at most about 5%.
  - *Final size:* compacted references measure 2.05 GB on Init claim 0, about
    8% of the record.
  - *Peak:* compaction allocates its destination before freeing the raw
    references, so the peak during execution is higher than the final size. The
    peak is what limits concurrency, so it must be measured too.
- **Execution slowdown.** Init claim 0 executes in 105–124 s with recording,
  across iterations, against 96–99 s without, so 7–9% slower. That is over the
  5% gate. Init proving wall went from 6:35 to 7:00–7:05 in the first
  end-to-end runs.
- **Estimator bound.** Admission without a device margin relies on the
  per-shard estimate being an upper bound on the gathered image. The estimate
  must count alias rows from functions that share a chip. A regression test
  should compare estimated against gathered sizes on a real record.
- **Upload per proof.** A 41-shard claim's supplies alone need roughly
  80–375 GB across 81 supplies, about 0.05–0.2 s each over PCIe, against about
  1 s of GPU work per supply. The depth-count prepass gathers and uploads every
  shard image a second time, which this estimate does not include yet.

## 5. Hints on the GPU (`ixvm.io.read` done)

A hint is a host-side Rust closure registered per channel. Trace generation
calls it again for each row instead of storing its answers. A GPU fill admits a
function only if every hint it uses has a GPU implementation. A function that
fails takes the rest of its circuit group to the host with it. The GPU
implements `u32.bytes`, `u32.sub`, `u32.add`, `u32.add3`, `u32.lt` and
`bytes_le`.

| Program | Host circuits | Blocking channels | What they read |
|---|---|---|---|
| IxVM claims | 7 of 256 | `ixvm.io.read`, `ixvm.io.tag`/`info`/`claim` | Input bytes from four dense arenas (constants, blobs, roles, models), and sparse metadata |
| Aggregation | 10 of 61 | `stark.io.read1`/`read8`/`address`/`digest`/`info`, `goldilocks.inverse` | Child proof bytes, and field inversion |

- `IxByteStream::read_byte_stream` reads 4 bytes per row through
  `ixvm.io.read`. It takes its group (`ixvm_group_02`) to the host.
- That is the remaining ~1.7 s stall per Init claim: 35 thread-seconds per
  claim, and 57–59 s across Mathlib.
- The fix is to upload each claim's arenas once per proof as bytes, and add
  kernel cases for these channels.
- Each channel must match the host provider exactly. The host-versus-GPU fill
  tests check that.

### Result

`ixvm.io.read` and `stark.io.read*` now fill on the device from arenas uploaded
once per proof (about 30 MB per Init claim). `ixvm.io.tag`/`info`/`claim` stay
on the host: they are sparse lookups keyed by addresses and would need a device
hash map.

| Init | Before | After |
|---|---|---|
| Wall | 6:27.7 | 6:27.8 |
| Claim stall (mean) | 1.65 s | 1.45 s |
| IxVM / aggregation circuits on host | 7 / 10 | 6 / 6 |
| Claim device peak | 100–101 GB | 95–96 GB |

The stall attribution above was wrong. `read_byte_stream` was a small part of
it. Per claim, the host fill per round is now about 1.5 s:

- `<ROM:3>`, 1.2 s. It is the one device-capable circuit that doesn't fit
  beside proving (the whole record is 31.7 GB, 22.1 GB admitted).
- `ixvm_group_19`/`18`/`00`/`33`, 0.1–0.5 s each, blocked by the sparse hints.

On Init this stall is about 6 s of a 388 s run, so it no longer matters there.
It matters on large Mathlib claims, where admission is partial.

## 6. Execution profile

Profiled with perf: Init claim 0's native execution, 96.5 s, 232M queries,
16.1G Aiur instructions, reference recording off. Execution thread only:

| Category | Share | Functions |
|---|---|---|
| Call memoization | 50% | `Runtime::begin<N,M>`, index `find`, `finish` |
| ROM interning (stores) | 13% | `Memory::intern` |
| Generated function bodies | 13% | The IxVM program's own computation |
| ROM loads | 5.5% | `load<N>`, `bump_rom` |
| Index growth | 5% | `reserve_rehash`, `insert` |
| Kernel (page faults) | 4.5% | First touch of fresh record memory |

- Instructions per cycle are 1.35, and TLB walks are negligible. Huge pages
  made no difference.
- In `begin<2,1>`, 48% of samples sit on the compare of hashbrown's control
  bytes (a cache miss on the probe). Another 23% sit on the store of a new
  row's arguments.
- `intern` has the same shape: 48% on control bytes, 15% on loading the index
  entry.

Execution is bound by memory latency in hash lookups, not by computation.

## 7. Bucketed index (done)

### Today

Each query table and ROM width has a `hashbrown::HashTable<Entry>`. An `Entry`
is a `u32` row and a `u32` hash tag; the arguments live in the row arena.
hashbrown keeps entries and control bytes in two arrays of one allocation:

```
[ entry N-1 | … | entry 1 | entry 0 ][ ctrl 0 | ctrl 1 | … | ctrl N-1 ]
   8 bytes per slot, stored backwards    1 byte per slot (7 hash bits or EMPTY)

slot i:  ctrl at base + i,  entry at base − 8·(i+1)   → about 1 GB apart at 2^27 slots
```

- **Memo hit** (60% of calls on Init): three dependent misses. First the
  control group, then the entry (tag check), then the row (argument compare and
  outputs). The multiplicity bump can overlap the row load.
- **New query** (40%): the probe sees EMPTY in the control group and stops
  after one miss. The insert then writes the control byte, the entry and the
  row. Those are stores, which the CPU buffers rather than stalling on.

### Proposal

```
one 64-byte bucket, cache-line aligned:
[ tag0 … tag6 | row0 … row6 | meta ]
   7 × u32       7 × u32       occupancy, overflow
```

- **Hit:** load one bucket (miss 1), compare 7 tags with SIMD, then load the
  row (miss 2). The entry miss is gone.
- **Overflow:** probes the adjacent bucket, which is the next cache line and
  usually prefetched already.
- **New query:** still one miss to probe. The insert writes into the line it
  already loaded.
- **Growth:** rehashes from tags without touching rows.
- **Determinism:** row numbers come from insertion order, not the index, so
  records, traces and proofs are unchanged.
- **Memory:** 64 bytes per 7 slots is 9.1 bytes per slot, the same as
  hashbrown. Actual use depends on load factor and growth policy.

### Estimate

Memoization takes about 48 s of 96 s, an average of about 65 ns per call (some
lines are cached, and the core overlaps some misses).

- **Hits:** removing one of three serial misses saves about a third of their
  lookup cost, 48 × 0.6 × ⅓ ≈ 10 s.
- **ROM interning:** about 12.5 s of time, of which the same change saves
  roughly 3–4 s.
- **Total:** about 10–15% faster execution.

**Decision rule.** hashbrown is heavily tuned. Prototype the new index in
`QueryTable` and `Memory` and check that records are identical. Measure it
against the 96.5 s baseline, and keep it only if it saves at least 8%.

### Result

The index is `crates/aiur/src/index.rs`: 64-byte buckets of 8 tags and 8 rows
(row + 1, so zeroed memory is empty), sized exactly like hashbrown, with an AVX2
tag match.

| Init claim 0, `--exec-only` | Mean exec | Peak RSS |
|---|---|---|
| hashbrown | 95.8 s | 31.5 GB |
| Bucketed index | 88.2 s (−8%) | 31.5 GB |
| Bucketed index, pre-sized from a sizes file | 85.7 s (−10.5%) | 31.2 GB |

- Records are byte-identical (BLAKE3 record digest), and index bytes match
  hashbrown's to within 100 KB.
- Full Init proof: 6:27.7 against 6:35–6:39, with the root unchanged.
- The saving is right at the 8% bar. The scalar match was slower than
  hashbrown, so the AVX2 path matters. Both `target-cpu=native` and the Nix
  `x86-64-v3` builds enable it.
- Pre-sizing needs a production hint source. Today the only hint is
  `AIUR_INDEX_SIZES`, a sizes file from an earlier run of the same claim.

### Related options

- **Pre-size indexes** from the record model's per-claim prediction. This
  avoids the rehash cascade (about 5% of execution) and the transient doubling
  of index memory.
- **Prefetch** the probe bucket in generated code once the arguments are known.
  Uncertain, because the hash is usually computed right before the lookup.
- **Smaller records** raise execution concurrency directly. The record is about
  70% query payload and 17% index; growth slack is only about 5%.

## 8. Order of work

| Work | Status | Limit it addresses | Validation |
|---|---|---|---|
| Lent device record; margin and workspace charge removed | done | Stall | Init root unchanged; 135 aiur tests pass |
| Per-shard device record, milestone 1 (gather and hash) | built, off by default: recording costs 7–12% execution and +8% record, a loss on Init where every device record fits | Stall (large claims) | Estimate ≥ gathered size on real records; peak and final record growth; slowdown ≤ 5%; Init default and constrained budget; growth on Mathlib claim 30 (exec-only) |
| Per-shard device record, milestone 2 (direct references) | not started | GPU fill cost | Per-row reference order checked against the fill plans |
| Bucketed index | done (−8% exec) | Execution throughput | Identical records; Init root unchanged |
| Index pre-sizing from the record model | not started (−2.6% with a sizes file) | Execution throughput, peak RSS | Per-table hint from per-function row shares |
| GPU hint channels: `ixvm.io.read`, `stark.io.read*` | done (Init stall 1.65 → 1.45 s) | Stall (all claims) | Host versus GPU fill tests; Init root unchanged |
| Sparse hints (`ixvm.io.tag`/`info`/`claim`), `<ROM:3>` admission | not started | Remaining ~1.5 s fill per claim | Per-circuit host fill report |
| Validate a prepared record once per backend (§10) | not started; measured −15.6% proof generation on an older base | Proving host preparation | Init root unchanged; Init end to end against 362 s |
| Next Mathlib proving run | after the above | All | Wall against 2:00:45; stall, idle, peak RSS |

The per-shard record, the index and the hint channels all touch the executor or
`gpu.rs` and `population.cu`. They run one at a time in the shared worktree
rather than in parallel.

## 9. Execution concurrency is bound by record size

In prove5, no more than 3 executions ever ran at once, on 32 CPUs. Time spent
at each level of concurrency:

| Executing | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| Share of the run | 2.6% | 15.8% | 25.9% | 55.7% |

- The record pool (about 180 GiB) holds the executing, queued and proving
  records.
- Claim records are large: p50 45.7 GiB, p90 55.5, max 87.0. Join records are
  p50 26.3 GiB.
- So memory, not CPUs, limits concurrency. Smaller records mean more claims
  executing at once and less GPU idle time (about 1,330 s in prove5).
- Executor time in prove5: claims 12,838 s (63 claims), joins 3,622 s
  (61 joins), root 72 s.

Init claim 0 storage, for reference: query payload 13.84 GB, query vectors
16.49 GB, query index 3.19 GB, ROM payload 1.90 GB, ROM vectors 4.93 GB, ROM
index 1.21 GB.

- Each ROM cell carries about 40 B of metadata: a 32 B `Slot` plus an 8 B
  bucket entry.
- Counts, depths and the dense index are 8 B per row and grow by doubling.

### Aggregation execution profile (Init tail)

- Joins take 46–48 s to execute and the root 30 s. That is 77 s of the 142 s
  tail after the last claim, with the GPU idle.
- In join and root execution, 36% of samples are in `f_4`. That is a run of
  224 byte XORs through the 8-bit XOR static map. The time goes to the
  per-call multiplicity increments (`count_map`) and value conversions.
- `f_4` is the BLAKE3 compression. Each call makes 192 closed-form map
  calls (maps 307, 308, 312 and 313) and 32 u32-add hints. Each map is
  65,536 rows. At `u64` counts the four maps hold 2 MiB of counters, the
  size of a core's L2. The record streams through the same L2 at about
  0.5 GB/s, so the random counter read-modify-writes miss to L3. The address
  chain to the counters (runtime → table → static map → counts, plus
  bounds and overflow checks) is about 10 extra instructions per call.

### Fixed-table tallies (done)

Generated code no longer calls `Runtime::count_map`. Each basic block
gets the counters of the closed-form maps it counts once, with
`rt.tally::<ROWS>(map)`. Each call is then one
`t_<map>.bump(row)`: a `u16` increment, plus a `u64` carry on wrap.

- The `u16` counters and `u64` carries live outside the record. They are
  reached only through raw pointers, so a handle stays valid while
  generated code borrows the runtime. When execution succeeds they are
  added into the map's `u64` counts, with checked additions.
- At `u16`, the four hot maps take 512 KiB. The carry array is touched
  once per 65,536 calls to a row.
- The generator already proves `a < radix && b < radix`, and `ROWS` is the
  product of the radixes, so LLVM removes `bump`'s `row < ROWS` assert. The
  hot path is `incw (base,row,2); jne`.
- A total cannot overflow `u64` within one execution (2^64 calls).
  `merge_tallies` still reports an overflow as a failure. Unlike the old
  per-call check, it reports it at `<native>`, not at the call site.
- The records, counts, traces and proofs are unchanged. The fingerprint
  scheme is unchanged: generated code binds to the runtime at compile time.

Measured with the join and root invocations from an Init run, executed
alone (`compact advice → bind_native::<Aggregation>`). Times are run 1 /
run 2; record digests matched in every case:

| Variant | Join 2 | Root |
|---|---|---|
| Before (`count_map`) | 46.2 / 43.1 s | 30.0 / 27.3 s |
| Hoisted handle, `u64` counters | 45.2 / 40.4 s | 29.5 / 26.0 s |
| Hoisted, `u8` + carry | 39.2 / 35.0 s | 24.8 / 22.0 s |
| **Hoisted, `u16` + carry** | **38.5 / 34.0 s** | **24.7 / 21.6 s** |

Hoisting alone saves about 5%; the smaller cache footprint saves the rest.

- **Init (full run):** joins 47.4 / 46.9 s → 40.7 / 38.4 s, root 28.8 →
  24.6 s. End to end 388 → 369 s, wall 6:38.7 → 6:20.0, root
  `7b5eb654…` unchanged.
- **IxVM claims:** IxVM has 401 tallied sites. Init claim 0 exec-only:
  89.2 → 86.6 s, digest `08c71b56…a0c4` unchanged.
- **Profile after the change (join, native thread):** `f_4` is 18% (was
  36%), `begin::<129, 32>` 8%, `Memory::intern` 8%. About 19% of the time
  is in the kernel, mostly page faults as the 20 GiB record grows. The
  first run in a process is 3–5 s slower than the second, which bounds
  what pre-faulting could recover.

### Record compaction (done)

| Change | Claim 0 saving |
|---|---|
| Query counts and depths as u32, in chunked storage | −2.78 GB |
| ROM cells: 16 B slot, per-width chunked words, u32 buckets | −2.03 GB |
| Chunked query rows (no doubling slack), u32 `dense_index` | −0.12 GB |

- **Init claim records:** 26.6–27.8 GB → 20.8–22.9 GB (−18 to −22%). Joins
  −11%, root −7%.
- **Init proof:** pool peak 149.5 → 126.9 GiB, peak RSS 115.8 → 105.0 GB.
  Records, the digest and the root are unchanged.
- **Wall:** 6:40.5 and 6:36.9 over two runs, inside the 6:28–6:40 spread of
  earlier runs. Exec-only time is flat.
- **Model:** admission applied `RECORD_STORAGE_FACTOR = 0.83`, fitted on Init.

### Static-width query rows (done)

Each query table's column widths are fixed by its function's bytecode types
(`Layout::narrow_words`). There is no format change.

- `Ptr` columns are `u32`s. Pointers are ROM addresses, below `MAX_ROWS`
  (`u32::MAX`).
- Enum tag columns are `u32`s.
- An enum payload word is a `u32` only if every constructor puts a pointer
  or tag there, or pads it with zero. If any constructor puts a `Field`
  there, it is a full field element.
- `Field` columns are full field elements. Tuples flatten.

Row storage depends only on the types, never on the data:

- **No `u32` column:** the table stores rows of field elements. It hands out
  borrowed rows, inputs and outputs, and copies them with a `memcpy`.
- **Any other table:** each row is packed into one run of `u32` words. First
  come the low 32 bits of every column in row order (inputs, then outputs).
  Then come the high 32 bits of each field-element column.
- A per-column table gives each column's high-word slot and mask. The mask is
  zero for `u32` columns, so their high word reads as zero.
- The memo compare, decode and encode are single passes in row order, inside
  one row.
- An argument with high bits in a `u32` column matches no row.
- An earlier variant kept the `u32` and element columns in two separate
  stores, with an index map. It touched two rows per access and ran 5.2%
  slower (92.5/92.7 s).
- A value of 2^32 or more in a `u32` column is an execution error, never a
  truncation. A failed `start` leaves the table unchanged; a failed `finish`
  leaves the row pending.
- **GPU upload:** all-element tables and all-`u32` tables are staged chunk by
  chunk. Mixed tables are unpacked row by row into canonical words. Traces,
  proofs, the record digest and the root are unchanged.

| Init claim 0, exec-only | All 64-bit | Static widths |
|---|---|---|
| Query payload | 13.84 GB | 11.25 GB |
| Query vectors | 15.64 GB | 13.04 GB |
| Charged record (query + ROM) | 22.94 GB | 20.34 GB |
| Peak RSS | 28.67 GB | 25.62 GB |
| Exec time | 88.0 s | 89.2 / 89.3 s |

- The column types predicted this record: values are 62.6% `Field`, 37.1%
  pointers and 0.3% tags, about 20.35 GB.
- **Init proof:** claims 20.8–22.9 → 18.4–20.3 GB (−12%), joins 22.7/22.9 →
  22.1/22.3 GB, root 15.1 → 14.8 GB. Pool peak 88.7 GiB, peak RSS 105.0 →
  93.0 GB, wall 6:36.9 → 6:35.0. Host validation is 3.86 s summed over 10
  proofs, against 5.23 s with 64-bit values.
- **Model:** `RECORD_STORAGE_FACTOR` 0.58 → 0.74. Every Init claim measured
  0.730–0.736 against the 0.83-era layout.
- **Mathlib confidence: moderate.** Savings depend on the pointer share of
  each workload's rows, not on value sizes. Mathlib has not been measured
  under this layout.

#### Earlier: runtime narrow/wide switch (replaced)

Every table started as `u32`s and was converted to field elements the first
time a value of 2^32 or more arrived. No Init claim 0 table converted.
Smaller, but its layout depended on the data:

| Init claim 0 | Before | After |
|---|---|---|
| Query payload | 13.84 GB | 6.92 GB |
| Query vectors | 15.64 GB | 8.71 GB |
| Charged record (query + ROM) | 22.94 GB | 16.00 GB |
| Exec-only peak RSS | 28.67 GB | 20.48 GB |
| Exec-only time | 88.0 s | 84.7 s |

- **Init proof:** claims 20.8–22.9 → 14.5–16.0 GB (−30%), joins 22.7/22.9 →
  13.8/14.0 GB (−39%), root 15.1 → 9.1 GB. Pool peak 126.9 → 88.7 GiB, peak
  RSS 105.0 → 74.5 GB, wall 6:36.9 → 6:27.6.
- **Model:** `RECORD_STORAGE_FACTOR` 0.83 → 0.58 (every Init claim shrank by
  0.698–0.707 against the 0.83 layout). Mathlib shard 1, exec-only, is
  charged 16.74 GB against 37.13 GB for claim 1 in prove5 (0.45), so the
  factor looks conservative there; one shard is thin evidence.
- **Next:** per-column u8/u16 packing. Init claim 0's values are 66.5% u8,
  5.4% u16 and 28.1% u32, so ideal per-value widths would take the payload
  from 6.92 to about 3.3 GB; per-column widths would save less.

### Prefetched record chunks (done)

The `ix` binary allocates with mimalloc, and THP is `always` on the dev host.
Measured with that allocator, about 9% of join and root execution is kernel
time: page faults on fresh record memory, while the record grows at about
0.8 GB/s. Each one is a 2 MiB transparent huge page that the kernel zeroes,
for about 0.2 ms per fault. The earlier 19% and the 3–5 s run-1 penalty were
measured with a glibc-malloc harness. With mimalloc, run 1 is only about 1 s
slower than run 2.

- **Fault timeline (join):** most of the 156k faults per run land in the
  first 1.5 s. They are 4 KiB faults on the native stack and on early index
  tables, and cost about 0.3 s. After that, a steady ~400 faults/s (huge
  pages) costs ~9% of the thread's time. Run 2 is fault-free for its first
  ~6 s only, because mimalloc purges freed arena memory about 4 s after a
  free.
- **Change:** when a store (`Chunks`) starts a full chunk of at least
  64 KiB, it asks a background thread (`aiur-prefetch`) for the next one.
  The thread allocates the chunk and writes one byte per page. The store
  takes the chunk when it fills the current one. If the chunk is not ready
  yet, the store allocates its own and keeps the request for the following
  chunk, so execution never waits on the thread.
- **Budget:** a prefetched chunk is charged when it is requested and counts
  as capacity. When execution finishes, the unused requests are dropped and
  their charge is released, so finished records have exactly the old
  capacity. During execution, the charge can be at most one extra chunk per
  growing store.
- **Thread lifetime:** the thread exits after 250 ms idle. Its mimalloc
  pages are then abandoned, so blocks freed later return to the arena
  normally.

Exec-only measurements (`stark_verifier::prepare →
bind_native::<Aggregation>`, mimalloc harness). Times are run 1 / run 2, and every digest matched:

| Variant | Join 2 | Root |
|---|---|---|
| Baseline | 36.6 / 35.6 s | 23.3 / 22.0 s |
| `MIMALLOC_ALLOW_THP=0` | 42.9 / 37.4 s | – |
| `MIMALLOC_PURGE_DELAY=-1` (bound) | 36.6 / 33.7 s | – |
| **Prefetched chunks** | **33.4 / 33.9 s** | **21.2 / 21.2 s** |
| Same build, prefetch off | 36.9 s | – |

- **THP off:** run 1 is 17% slower, with 6.3M faults. RSS falls by 4.9 GB,
  which is the THP rounding of sparse index tables and partly filled
  chunks.
- **Never purging:** run 2 drops to 33.7 s, the fault-free bound. Run 1 is
  unchanged, and the process keeps freed records resident. Not adopted.
- **Prefetching:** run 1 reaches that bound, and the thread runs on an idle
  core. Join RSS +80 MB, root +60 MB. Charged storage after execution is
  identical (`RecordStorage` equal with prefetch on and off).
- **Not tried:**
  - Larger chunks or `MAP_POPULATE`. They move the same zeroing onto the
    executing thread.
  - glibc `M_MMAP_THRESHOLD`/`M_TRIM_THRESHOLD`. glibc malloc is not the
    allocator in `ix`.
  - Pre-sizing index growth. Index faults are a small share of the early
    4 KiB burst.
- **Init claim 0, exec-only:** 86.6 → 84.9 s, digest `08c71b56…a0c4`
  unchanged. Peak RSS 25.62 → 25.75 GB. The query vectors are identical;
  the ROM vectors are 576 B larger.
- **Init proof:** wall 6:20.0 → 6:13.4, end to end 369 → 363 s. Joins
  40.7/38.4 → 36.8/37.3 s, root 24.6 → 22.2 s, claims 0.1–1.9 s faster.
  Peak RSS 93.0 → 93.3 GB, pool peak 113.1 GiB unchanged, root `7b5eb654…`
  unchanged.
- **Concurrency:** one thread serves every execution in the process. By
  estimate (about 10 GB/s of zeroing against 0.8 GB/s per execution), it
  keeps up with about ten executions; Init ran four at once. Past that point
  stores fall back to allocating their own chunks, which is the old
  behaviour.

### Claim execution: ROM by address and early prefetches (done)

Profile of Init claim 0 exec-only before this change (perf, flat, the
`aiur-native` thread only; 84.5 s):

| Category | Share |
|---|---|
| `begin` (memo probe, compare, insert) | 46.4% |
| `Memory::intern` and `store` | 18.7% |
| Generated function bodies | 11.5% |
| ROM loads (`load`, `Memory::get`, `bump_rom`) | 8.5% |
| Index growth (`rehash`, budget) | 4.1% |
| `finish` | 2.9% |
| Hints, chunk pushes, shape checks, kernel | 5.3% |

In `begin::<2, 1>`, 71% of samples sit on the first use of the index
bucket: the probe's cache miss. Execution is still bound by dependent
misses, so both changes shorten or overlap miss chains rather than cut
instructions.

- **ROM by address.** The ROM index holds each cell's width-local address
  instead of its record index, and each width keeps a cell's record index
  and count side by side (`Bucket::cells`, stride 2). A cell is then
  reached from its address alone. A repeated store was index → `Slot` →
  words; it is now index → words. A load was address → record index →
  `Slot` → words; it is now words and count, two independent loads. One
  index serves every width: an entry of another width compares this
  width's cell at that address (bounds-checked), and a match is correct
  either way, because a width holds each encoding once. `Slot` loses its
  count (12 → 8 B), so the charge per cell is unchanged.
- **Early prefetches.** Codegen finds, in each basic block, the calls,
  stores and loads whose operands are final before an earlier call, store
  or load of the block, and emits `rt.prefetch_call/store/load` right after
  their last operand is written. The prefetch computes the key's hash and
  touches its index bucket (or dense-index slot, or ROM cell), so the miss
  overlaps the work in between. IxVM gets 2,101 call, 1,691 store and 91
  load prefetches. Weighted by the rows of each function, about 19% of
  call sites and 23% of store sites qualify.

Init claim 0, exec-only. Each variant is measured alone on top of the one
before it; every digest is `08c71b56…a0c4`:

| Variant | Exec |
|---|---|
| Baseline | 84.5 s |
| **ROM by address** | **78.9 s** |
| **+ early prefetches** | **76.8 / 76.8 s** |
| + inlined probe loop (rejected) | 77.0 / 77.5 s |

- **Rejected: inlined probe loop.** `QueryTable::lookup`'s key compare runs
  as an out-of-line closure (`lookup::{closure#0}`, 2% of the thread).
  Iterating the bucket's candidates in the caller instead, so the compare
  sees the fixed width, made no difference.
- **Not tried:** skipping the second probe on insert (its bucket is
  already cached), and cheaper key hashing (a few multiplies against a
  ~100 ns miss).
- **Profile after** (same method, seconds of the native thread under
  perf, 86.9 → 79.8 s): `begin` 40.3 → 37.1 s, ROM loads 7.4 → 3.3 s,
  `intern` with its pushes 17.5 → 16.7 s, generated bodies 10.0 → 11.3 s
  (they now hash and issue the prefetches). The bucket miss in `begin`
  remains the largest single cost.
- **Aggregation** (mimalloc harness, run 1 / run 2, digests unchanged):
  join 2 33.5 / 33.6 → 31.9 / 32.1 s, root 21.0 / 21.4 → 20.3 / 20.4 s.
  The aggregation program gets 270 call, 112 store and 43 load prefetches.
- **Storage:** query storage is identical. ROM vectors +0.8 MB (2,893.9 →
  2,894.7 MB: two-word cell chunks round differently), ROM index unchanged.
  Peak RSS 25.75 → 25.71 GB.
- **Init proof:** wall 6:13.4 → 6:02.8, end to end 363 → 352 s. Claims
  93.4–97.2 → 85.1–87.7 s, joins 36.8/37.3 → 37.1/35.2 s, root 22.2 →
  21.6 s. Records +0.1–1.0 MB each, pool peak 113.1 GiB unchanged, peak
  RSS 93.3 → 93.7 GB, root `7b5eb654…` unchanged.
- **Risk:** the ROM index now resolves an entry through whichever width is
  being looked up. That is sound only because each width interns an
  encoding once; a change that let one width hold duplicates would need
  per-width indexes. Prefetches are hints and never change results.

### Memory outside the host budget (measured)

prove7 and prove8 reached about 222 GiB RSS and were killed by the host OOM
killer. This section measures how far RSS can exceed what the budget
accounts for: the pool's grants, every lane's workspace and the resident
bytes.

- **Sampler:** `AIUR_MEMORY_TRACE=<seconds>` logs one `[memory]` line per
  sample: `VmRSS`, `RssAnon`, `RssFile`, `RssShmem`, `AnonHugePages`, the
  pool's grants and used bytes, records held, executions running, and
  `untracked` = RSS − (grants + workspace + resident). A positive
  `untracked` is memory the budget does not see.
- **Conditions:** Init at `--max-ram 80`, so the pool is 53.9 GiB and holds
  three executing claims (peak grants 53.9 GiB, one growth wait of 31 s).
  Samples every 2 s. Every run verified root `7b5eb654…`.

| Variant | Wall | Peak RSS | Peak untracked | Untracked > 5 GiB | RSS − used during execution |
|---|---|---|---|---|---|
| Baseline | 6:12 | 68.5 GiB | +19.1 GiB | 18 samples | 10.5 GiB |
| `MIMALLOC_PURGE_DELAY=0` | 6:15 | 68.5 GiB | 0.0 | 0 | 9.9 GiB |
| Prefetch off | 6:20 | 68.4 GiB | +11.3 GiB | 10 | 10.3 GiB |
| `MIMALLOC_ALLOW_THP=0` | 7:01 | 59.6 GiB | +7.2 GiB | 3 | 1.5 GiB |
| `mi_collect(true)` after each record drop | 6:11 | 68.5 GiB | +6.5 GiB | 7 | 10.4 GiB |

"RSS − used during execution" is RSS less the pool's used bytes and the
1.7 GiB resident, with three claims executing and no proof running. The
`mi_collect` variant called it from the sampler thread within 2 s of each
drop.

There are two separate gaps.

- **Freed records stay resident (mimalloc purge delay).**
  - When a proof ends, the pool releases the record's grant at once. RSS
    stays flat for 10–20 s, then falls by about the record's size.
  - In the baseline, every `untracked` peak follows a record drop. The
    largest is +19.1 GiB, right after claim 0's 18.9 GiB record was
    freed.
  - Cause: mimalloc v3 frees record pages back to its arena and schedules
    a purge after `purge_delay × arena_purge_mult` (1 s × 4). The purge
    only runs when some thread next collects.
  - With `MIMALLOC_PURGE_DELAY=0`, RSS falls in the same sample as the
    drop and `untracked` never goes positive. Wall time and execution times
    are unchanged (claims 85.3–87.7 s against 84.1–88.1 s; joins 35.2/36.7
    s against 35.7/36.3 s).
  - `mi_collect(true)` after a drop only partly closes this gap.
  - In Mathlib a proof ends every 20–40 s, and claim records are 18–35
    GiB. So roughly one record is resident outside the budget for most of
    the run.
- **THP rounding of allocator size classes.**
  - With three claims executing, RSS exceeds the used bytes by 10.5 GiB.
    That is about 19% of the executing records, and it grows with them.
    It persists while executed records wait for proof (about 9 GiB with
    four held). With THP off it is 1.5 GiB.
  - A microbenchmark shows the mechanism. Allocate 8 GiB in blocks of
    mimalloc's large classes and touch only the requested bytes:
    - 288 KiB requests (rounded up to 320 KiB blocks) give RSS +19% with
      THP and +0% without.
    - 352 KiB requests (rounded up to 384 KiB) give +17%.
    - 72 KiB requests give +19%.
    - Exact 512 KiB requests give +1%.
  - With 4 KiB pages, a block's untouched tail is never faulted in. With
    THP, it is part of a 2 MiB page that the kernel zeroes.
  - `Chunks` sizes chunks as a power of two rows × stride × element size,
    up to 512 KiB, so most strides land between mimalloc's size classes.
    The pool charges the requested bytes, so this rounding is never
    charged.
  - In Init this gap hides inside the idle workspace headroom (negative
    `untracked`). In Mathlib the lane is busy, so it is real overrun.
- **Not contributors:**
  - **Prefetch:** the execution gap is unchanged with prefetch off. Its
    lower peak `untracked` is the same purge delay with different timing.
    Executions are 1–2 s slower without it.
  - **Abandoned pages:** no retention remains once the purge delay is 0,
    so abandoned pages and cross-thread frees retain nothing beyond it.
  - **Other memory:** `RssFile` (0.3 GiB) and `RssShmem` (≤ 0.3 GiB) stay
    flat, so GPU-driver host memory and upload staging are small.
  - **Lane memory between proofs:** after a claim proof, the lane keeps
    roughly 15 GiB until its next proof. That stays within the 24.2 GiB
    workspace it is charged.
- **THP off is not the fix.** Claims execute 28% slower (109.6–113.8 s
  against 84.1–88.1 s) and the wall time grows 13%.
- **Purge delay fixed in `ix`:** `main` calls
  `Ix.Runtime.configureAllocator`, which sets `mi_option_purge_delay` (index
  15 in v3.5.1's `mi_option_t`) to 0 unless `MIMALLOC_PURGE_DELAY` is set.
  An Init run with no environment override shows `untracked` never above 0
  (peak −0.2 GiB), as with `MIMALLOC_PURGE_DELAY=0`.

#### Size-class slack, confirmed and removed

mimalloc v3.5.1 (from source): blocks above 10 KiB and up to ~84 KiB go
in 512 KiB pages, larger ones up to 512 KiB in 4 MiB pages, and anything
larger is a singleton rounded to 64 KiB slices (256 KiB above 2 MiB). Bins
are four per power of two, so a block is up to 25% above the request, and a
page holds `⌊page / block⌋` blocks with the tail unused. A 288 KiB request
takes a 320 KiB block, 12 per 4 MiB page: 4096 / 3456 = +18.5%, which is the
microbenchmark's +19%. A power-of-two block of at most 512 KiB is its own
class and divides its page exactly.

Measured on Init (`--max-ram 80`, three claims executing, `[alloc]`
lines from a temporary counting allocator that bins every live allocation
of at least 8 KiB by `mi_usable_size`). "Page" is the block's share of its
mimalloc page, or its slices for a singleton:

| Live allocations | Requested | Blocks | Pages | Pages / requested |
|---|---|---|---|---|
| Chunks a power of two rows (before) | 53.9 GiB | 61.5 GiB | 63.3 GiB | 1.174 |
| Chunks a power of two bytes (after) | 54.0 GiB | 56.1 GiB | 56.2 GiB | 1.040 |

Before, 14.2 GiB sat in the 384 KiB class at 1.27, with the 96, 112, 192,
320 and 448 KiB classes at 1.18–1.22. The predicted 9.4 GiB of slack
matches the measured 9.9 GiB execution gap.

**Change.** `Chunks` now gives a full chunk as many rows as fit the
largest power of two bytes not above its `chunk_bytes`, instead of a power
of two rows. A query store's chunk is sized for 4096 rows rounded up to a
power of two bytes (at most 512 KiB). A row's chunk is found by a multiply
(Lemire's division by a constant) rather than a shift. Microbenchmark
(8 GiB of chunks, THP on): 288 KiB → +19.6%, against 512 KiB of 72-byte
rows → +0.9%. 176 KiB → +11.8% against 256 KiB → +0.9%. 144 KiB → +14.8%
against 256 KiB → +0.9%.

| Init `--max-ram 80`, purge delay 0 | Wall | Peak RSS | Exec gap (max / mean) | Claims 0–2 | Claim 3 | Joins |
|---|---|---|---|---|---|---|
| `mem-purge0` (old binary) | 6:15 | 68.5 GiB | 9.9 / 6.1 GiB | 85.3–87.7 s | 117.2 s | 35.2 / 36.7 s |
| Power-of-two rows, multiply lookup | 6:27 | 68.1 GiB | 9.9 / 6.2 GiB | 87.4–90.2 s | 122.5 s | 36.9 / 38.0 s |
| Power-of-two bytes (the change) | 6:26 | 60.7 GiB | 2.7 / 1.3 GiB | 87.2–90.6 s | 121.7 s | 36.9 / 37.9 s |

The exec gap is RSS less the pool's used bytes and 1.7 GiB resident while
three claims execute. All three runs verify root `7b5eb654…`. The second
and third rows are one binary that switched sizing by an environment
variable and also ran the counting allocator.

- **Memory:** the gap falls from 19% to 5% of the executing records,
  and peak RSS falls by 7.4 GiB.
- **Time:** the sizing alone costs nothing (rows two and three match).
  Both runs of that binary execute 2–4% slower than `mem-purge0`. The
  likely cause is the multiply in each row lookup, which a
  microbenchmark puts at 0.1–1.5 ns per random or sequential row access
  over a shift. The counting allocator is the other difference, and a
  clean binary has not been timed.
- **What remains (about 2.1 GiB of the 2.7 GiB):** `RowIndex` allocations
  of `(9·2^k + 1) · 64` bytes. They take the 80 KiB class (1.33), the
  160 KiB class (1.28) and singletons rounded to 64 KiB–1 MiB (1.08,
  19.8 GiB live). Sizing indexes to powers of two would change their
  growth points, so they are left as they are.
- **Recommended:**
  - Keep the purge delay at 0 and power-of-two-byte chunks.
  - Time a clean binary on Init against `mem-purge0`. If the 2–4% holds
    and matters more than 7 GiB, fall back to power-of-two rows only for
    strides whose power-of-two chunk already fits a class within ~2%.
  - The budget should treat about 4% of held record bytes as uncharged,
    down from 20%.

## 10. Validate a prepared record once (todo)

Every witness supply still calls `validate_record_shape`
(`crates/aiur/src/trace/stark/streaming.rs`, `timed_witness`), which reads
every recorded depth of every table (`crates/aiur/src/trace.rs`). The record
is immutable after preparation and `prepare_host_parts` has already run the
full `validate_record` over it, so each supply repeats a whole-record scan.
An Init claim makes 43 supplies per proof.

Commit `5184ad11c` on `perf/aiur-single-gpu` removed this scan: a prepared
record carries the identity of the backend that validated it, and a supply
checks that identity and its own dimensions instead. On base `4e27c5fcd` it
cut the summed per-supply validation from 9.05 s to almost nothing and
median Init-claim proof generation from 49.3 s to 41.6 s (−15.6%), with
identical proof bytes ([single-GPU plan §§7–8](aiur-single-gpu-performance.md)).
The same commit's parallel depth-range counting already has an equivalent
here (`depth_ranges`); only the validate-once half is missing.

The gain on this branch is unmeasured. Depths are now u32 columns, and
population overlaps proving, so the scan may cost less or sit partly off the
critical path; merged Init reports 2.8 s of witness stall in total.

- **Change:** keep the per-table shape checks on a supply of a prepared
  record and skip the per-row depth loop; reject a preparation made by
  another backend or plan. Port the commit's regression tests (another
  backend's preparation rejected, reuse after the owner moves, out-of-field
  depths rejected).
- **Gate:** Init root unchanged and Init end to end against 362 s. Keep it
  only if the gain clears 5%.
- **Optional:** the commit's `profile_proof` example and
  `PreparationTimings` (about 500 lines) time a single proof's preparation
  phases; port them only if this or later preparation work needs them.
