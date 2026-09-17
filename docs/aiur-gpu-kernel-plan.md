# GPU kernel and pipeline plan

2026-09-16. The device-side companion to the
[proving performance plan](aiur-gpu-performance-plan.md). Numbers come from
the CUPTI profiles in
[`bench/prover-profile-2026-09-15`](../bench/prover-profile-2026-09-15/README.md):
join 33 (27.9 s proving, 16.3 s of kernel time) and the representative claim
9 (66.2 s proving, 37.1 s of kernel time), both before packed seeds. The
kernel mix is what matters here and packing did not change it. Kernel
seconds are unions of intervals on one device, not sums across streams.

## Where kernel time goes

| Kernel family | Join 33 | Share | Claim 9 | Share |
| --- | ---: | ---: | ---: | ---: |
| NTT stages (`radix8_dif_stage`, `radix2_dif_stage`, `radix4`) | 7.22 s | 44% | 18.08 s | 49% |
| BLAKE3 Merkle hashing (leaf rows, short rows, digest pairs) | 3.56 s | 22% | 7.37 s | 20% |
| `evaluate_quotient` | 2.09 s | 13% | 4.88 s | 13% |
| `accumulate_reduced_opening` | 1.18 s | 7% | 1.93 s | 5% |
| `lookup_messages_graph` | 0.69 s | 4% | 1.62 s | 4% |
| `gather_resident_lde_group` | 0.39 s | 2% | 0.86 s | 2% |
| Generated BLAKE3 trace rows | 0.42 s | 3% | 0.30 s | 1% |

Time with no kernel running: 11.6 s of the join's 27.9 s and 29.0 s of the
claim's 66.2 s. Of that, host-to-device copies with no kernel account for
2.9 and 2.3 s, the first shard's witness at each round start for 2.8 and 4.8
s, stage-one commit for 6.8 and 13.8 s in total, and FRI and opening for 1.1
and 5.2 s.

## Ranked work

Estimates are derived from the shares above and the kernel shapes read in
`cuda/kernels.cu`; none has been measured. Each item is gated by the CUPTI
profile's kernel-family seconds and by identical proof bytes.

### K1. Fused shared-memory NTT

`launch_dif` runs one global-memory pass per radix-8 stage, eight passes for
a height of 2^24, each streaming the whole matrix in and out, then a separate
`bit_reverse_scale_and_shift` pass. Widths below eight (the width-2 quotient
and FRI codewords) fall to radix-2 passes: 4,096 launches and 1.5 s in the
join, 9,665 launches and 6.2 s in the claim. Goldilocks NTT is
memory-bound, so passes are the cost.

Do: a kernel that keeps 2^10 to 2^12 rows of a column group in shared memory
and runs all their butterfly stages before writing back, so a 2^24 height
takes two or three passes; radix-8 fused stages for narrow widths by mapping
columns across lanes; fold the bit-reversal, scale and coset shift into the
first or last pass; and in the coset LDE's forward transform skip the three
quarters of zero-padded inputs in the first stage, or run it as four
size-`n` coset transforms with per-coset twiddle scaling.

Estimate: 2 to 3x on 44 to 49% of kernel time, so 15 to 25% of kernel time.
Cost: one to two weeks including a randomized test against the CPU DFT at
every height and width the prover uses. Highest value, highest effort.

### K2. Merkle leaf hashing at full lane utilization

`blake3_hash_rows_kernel` gives one warp to one leaf row and one lane to
each 1 KiB chunk of it. Most committed matrices are narrow: a 533-column row
is 4,264 bytes, five chunks, so 27 of 32 lanes idle, and rows of a few
columns hit the one-thread-per-row short path. Rows wider than 32 KiB are
hashed on the host.

Do: map lanes to chunks across many rows in one pass and reduce each row's
chunk values in a second pass, or size the warp's row group to fill 32
chunks; extend the device path to rows wider than 32 KiB with a two-level
reduction so no height group is hashed on the host; and batch the
`blake3_hash_digest_pairs_kernel` levels of one tree into fewer launches
(21,000 launches in the claim).

Estimate: 3x on 20 to 22% of kernel time, so 13 to 15%. Cost: three to five
days, with the existing CPU height-group hash as the oracle.

### K3. Compiled, coalesced quotient and lookup evaluators

`evaluate_quotient`, `evaluate_constraint_graph` and `lookup_messages_graph`
interpret a node list per row: a switch per node, every intermediate through
shared memory. Adjacent lanes take adjacent natural rows, whose storage rows
are bit-reversed, so each column read touches 32 scattered 8-byte words per
warp. Quotient is already 98% kernel-active, so only the kernel itself can
get faster.

Do: emit one CUDA function per circuit from the Lean `ConstraintGraph`,
the way `TraceCuda.lean` already emits row writers, with intermediates in
registers; evaluate in storage order so a warp reads 32 consecutive rows and
permute the selector and output indexing instead; and load each LDE row's
referenced columns once per node group.

Estimate: 2x on 17% of kernel time, so 8 to 9%. Cost: one to two weeks; the
compiled kernel must agree cell for cell with the interpreter on every
circuit, which the existing quotient tests can drive.

### K4. Coalesce the reduced-opening accumulation

`accumulate_reduced_opening` gives one thread one row and loops over every
column of a row-major LDE: lane `t` reads row `t`, so a warp's loads are
`width * 8` bytes apart. Do: one warp per row with lanes over columns and a
shuffle reduction, or a block tile that reads coalesced row segments.
Estimate: 3 to 5x on 5 to 7% of kernel time, so 4 to 5%. Cost: one day.
The cheapest item here; do it first as the calibration of the method.

### K5. Overlap copies with kernels

Everything runs on `cudaStreamPerThread`; a prover thread's uploads,
kernels and downloads serialize. `staged_upload` copies a chunk into one
pinned 64 MiB slot, uploads it and synchronizes before the next chunk. There
are 5,500 synchronous `cudaMemcpy` calls per join, mostly `copy_to_host`
and Merkle sibling gathers, and 46 `cudaHostRegister` pairs.

Do: double-buffer the staging slot on a dedicated transfer stream with
events, so the host `memcpy` of chunk `k+1` and the upload of chunk `k`
overlap the kernels of the previous matrix; make digest and opening copies
asynchronous on the same stream with one event wait where the host needs the
value; and keep CPU-built trace matrices pinned for their lifetime instead of
registering per commit.

Estimate: most of the 2.3 to 2.9 s of copy time with no kernel running per
proof, which is 8 to 10% of the join's proving time. Cost: three to five
days, no protocol change.

### K6. Fill the pipeline at round boundaries

The longest kernel-idle gaps are the first shard's witness at each round
start: 1.8 s and 1.0 s in the join, 2.6 s and 2.2 s in the claim. Round two
cannot start before the barrier, but building its first shard's traces does
not depend on the challenge. Do: start round two's first witness during
round one's last shard, and order shards so a small one leads each round.
Estimate: 2 to 4 s per proof of idle GPU. Cost: two to three days in the
`consume_ahead` pipeline.

### K7. FRI and opening host gap

FRI and opening had 5.2 s with no kernel in the claim. The likely causes are
the deterministic proof-of-work grind on the host (20 query bits) and
sibling gathers; the profile cannot separate them. Do: add spans for grind
and gather; if the grind dominates, run each window's candidate check as one
kernel and take the window minimum on the device, which preserves the
smallest-witness semantics `DeterministicPow` defines. Estimate: unknown
until the spans exist. Cost: one day to measure, two to three to move.

### K8. Two proofs per device

Live device allocation peaks at 63.6 GiB, so two unrestricted provers do not
fit in 96 GiB. Everything above shortens the critical path; this is the item
that fills the gaps that remain. Do: reduce the peak by releasing quotient
staging and retained traces earlier and by lowering the shard cell budget
for a second lane, then admit two lanes under one device memory budget with
the peaks staggered. Estimate: up to the remaining idle fraction, which the
other items shrink first. Cost: a week; measurement-dependent.

## Sequence

1. K4 in a day, to calibrate estimates against the profile.
2. K5 and K6, pipeline work with no kernel algorithm risk.
3. K2, then K1, the two largest kernel families.
4. K3, once the generated-kernel toolchain has proven itself on rows.
5. K7 as its spans direct; K8 last.

After each step: rerun the CUPTI join replay, compare kernel-family seconds
and the no-kernel total, and require the same proof digest.
