# Collapsing the recursive KZG stage and the PLONK wrapper

Review of the BN254 KZG → PLONK pipeline on `sb/bn254`, with sizing of the
FRI-retune alternative and a survey of upstream Plonky3 since the pinned
revision. Measurements are the branch's own benchmark records unless stated
otherwise (October 2026, one RTX PRO 6000 Blackwell, 48 logical CPUs).

## Summary

- **Security requirement.** Preserve the current proven security bound.
  Performance improvements and stage removal must not lower it; preserving
  only a conjectured bound is insufficient.
- **Not as one proof, on the available evidence.** Scaling the wrapper's
  measured component costs to the first KZG proof gives 250M to 385M
  constraints, and even its variable-base MSM terms alone exceed the 67M
  rows that gnark PLONK on BN254 can reach (`4N` must fit the field's `2^28`
  two-adicity). This is an extrapolation; the compile-and-size gate the
  architecture doc asks for remains the way to close it.
- **Yes as one process, with a bounded win.** A persistent GPU worker holding
  both stages is estimated to remove about 30 to 35 s of a 212 s pipeline;
  the retained-worker path has not been measured.
- **The real collapse is upstream.** Shrinking the first KZG stage until its
  proof can be wrapped directly removes the recursive stage. Sizing from the
  checked-in Init key shows the first stage's cost is almost entirely per
  query, and that 65% of it was an opening-reduction implementation that
  rebuilt shared products per query. Restructuring that reduction (patch in
  the working tree, verifier tests passing) halves the translated circuit:
  at 100 queries the lowered layout drops from nine `2^24` computation
  partitions to five, or three at `2^25`; at 40 queries it fits one `2^25`
  trace. Measured on the GPU, the warm first stage goes from 135 s to 93 s
  and from 175 GiB to 114 GiB under both development and Ignition
  parameters; the warm recursive stage stays at about 41 s and verifies the
  patched proof. The warm Ignition pipeline from saved FRI proof to
  recursive packet is 134 s against the README's 181 s, and 121 s with the
  lazy-nibble multi-stark change measured below. The 40-query
  configuration lowers the proven bound and is therefore excluded; its
  sizing results are diagnostic only. Fewer rows do not by themselves make
  the first proof wrappable: KZG commits per column, and the
  four BLAKE3 custom traces leave a one-partition first proof with about 360
  commitments, estimated above the `2^26` wrapper ceiling. Merging those
  traces into one brings the estimate to about 60M constraints, just under
  the ceiling, so removing the recursive stage rests on exporting such a
  packet and compiling the adapted wrapper; column packing in the first
  stage's PCS is the fallback if that compile does not fit.

## The pipeline as it stands

Warm BN254 Init figures with admitted Ignition parameters. Each stage is a
separate process.

| Stage | Prover | Output | Wall time | Share |
| --- | --- | --- | ---: | ---: |
| FRI compression | Goldilocks CUDA worker, root key's own parameters | 1.4 MB FRI proof | ~60 s | — |
| First KZG | ix Plonkish prover, BN254 CUDA, 19 partitions of `2^24` | 32,869 B proof, 583-term opening MSM | 136 s | 64% |
| Recursive KZG | Same prover, one `2^26` trace, 61M frontend rows | 1,917 B envelope, two deferred pairing points | 45 s | 21% |
| gnark PLONK | Go helper, CUDA MSM, FFT and fused quotient | 584 B proof, 320,091 gas on Anvil | 32 s process, 11.4 s core | 15% |

Shares are of the 212 s from saved FRI proof to PLONK proof. Of the PLONK
stage's 32 s, about 20 s is decoding the 1 GB proving key in a fresh process.

The recursive stage verifies the first proof inside a custom Plonkish circuit
with byte-table lookups, then exposes its two pairing operands as public
values. The PLONK wrapper verifies that small packet with gnark's emulated
BN254 arithmetic and performs both pairing checks in-circuit.

## Why one gnark proof over the first KZG proof is out of reach

The wrapper today verifies 15 variable points, 19 fixed commitments and 2
deferred points. The branch's component sizing (baseline GLV variant, 17.99M
total) attributes the cost as follows; the production classic-GLV variant fits
`2^24` with 2.09M rows of headroom.

| Wrapper component (recursive packet) | Constraints |
| --- | ---: |
| Point validation and public binding | 168,592 |
| BLAKE3 transcript replay, 1.9 KB packet | 4,914,403 |
| Opening MSMs, 35 terms | 9,735,484 |
| Outer pairing check | 1,588,862 |
| Deferred pairing check | 1,588,278 |
| Classic-GLV total, separate pairings | 14,689,440 |

Verifying the first proof directly means 583 MSM terms and a 33 KB
transcript. Scaling only those two components:

| Component of a direct relation | Estimate |
| --- | ---: |
| Opening MSMs, 592 terms at 0.28M to 0.5M each | 165M – 300M |
| BLAKE3 transcript, about 17× the bytes | ~85M |
| One pairing check instead of two | ~1.6M |
| **Estimated direct relation** | **250M – 385M** |
| gnark PLONK ceiling on BN254 (`4N ≤ 2^28`) | `N = 2^26` = 67M |
| Ignition G1 points available | 100.8M |

The branch's PLONK adapter already rejects domains above `2^26` for this
reason. These are scaled component costs, not a compiled lower bound: the
wrapper folds equal, opposite and small-multiple fixed bases before its MSM
(`circuit.go`, `foldFixedBases`), handles constant scalars separately, and a
packet's byte length is not its transcript's compression count. The margin
is nevertheless large. The measured first proof has 326 variable and 247
fixed commitments plus ten opening witnesses. Counting only the 336
variable-base points at the current wrapper's blended 0.28M constraints per
term (a baseline-GLV component figure that already includes its cheap
fixed-base terms) gives about 94M constraints before any transcript or
pairing work, or about 77M after scaling by the production classic-GLV
ratio (14.69M / 18.00M), still over the 67M ceiling. The recursive circuit exists
because it is about six times denser per MSM term than gnark's emulated
arithmetic: 77k lookup-backed rows per term against roughly 500k gnark
constraints. The same arithmetic rules out the reverse direction, proving the
61M-row recursive relation with standard PLONK gates. The architecture doc's
"compile and size both relations" gate should stay; the figures above say
what result to expect from it.

## What does make sense, ranked by payoff

1. **Shrink the first KZG stage** (removes a stage). Start with the
   opening-reduction change measured below, which halves the circuit with no
   parameter or protocol change. The retune steps after it are
   implementation work, not parameter selection: the
   in-circuit verifier rejects folding arity above one and nonzero Merkle
   caps (`fri/plan.rs`, `validate_parameters`; `fri/pcs.rs`,
   `FixedPcsShape`), the first-stage and recursive workers enforce at least
   eleven partitions (`pipeline/first.rs`, `MIN_PARTITIONS`;
   `pipeline/wrap/saved.rs`), and the PLONK exporter and Go circuit hardcode
   the two-circuit recursive packet with its deferred pairing operands
   (`wrap/outer/relation/codegen.rs`, `tools/plonk-wrapper/circuit.go`).
   Every change re-derives the verifying keys and fixed preprocessing.
   Every candidate must preserve the current proven security bound under
   the same assumptions and accounting as the baseline.
2. **Fuse the recursive and PLONK stages into one warm worker** (estimated
   30 s; unmeasured). Both fit one GPU at the same time (59 GiB and 19 GiB
   of VRAM). A persistent helper holding the proving key, compiled circuit
   and CUDA context would take the PLONK stage from 32 s toward its 11.4 s
   core time. On the KZG side, authenticating the `2^26` Ignition cache
   (5.5 s, from the Ignition import record) and restoring fixed
   preprocessing (5.3 s, from the warm development rerun) are per-process
   costs that would disappear; the two figures come from different runs.
   The recursive verifier already separates compilation from request
   binding (`native_verifier/plan.rs`, `Plan::compile` and
   `Bindings::request_inputs`); `saved.rs` calls `Plan::build`, which does
   both per request, so the remaining work is retaining the compiled
   circuit across requests in the worker. The wrapper plan already lists
   the warm service as gate G6.
3. **Benchmark a faster proving-key load** (candidate, unmeasured). The
   helper writes the 1 GB key with gnark's `WriteTo`, which compresses
   points, and loads it with `ReadFrom` after verifying the file's SHA-256
   against the manifest. On BN254 G1 the subgroup check is only an on-curve
   check, so the unchecked reader alone would save little; the cost to
   measure is point decompression, one square root per point over about
   `2^24` points. The candidate is raw serialization (`WriteRawTo`, about
   twice the bytes) with the unchecked reader, keeping the hash check as the
   integrity gate. How much of the 20 s this recovers is not established.
4. **Drop PLONK where latency matters more than gas** (trade-off, with
   prerequisites). The recursive packet is 1,917 B and verifies natively in
   4 ms. The only like-for-like on-chain numbers are complete transactions:
   825,229 gas for the historical BLS Keccak v5 packet through the direct
   verifier against 320,091 gas for BN254 PLONK (the record's 757,950 figure
   is a conformance fixture's external-call cost without intrinsic or
   calldata gas). At the comparison's $2.859 per million gas the difference
   is about $1.44 per verification for 32 s of proving. A direct BN254 path
   does not exist yet: the Solidity exporter is BLS-only and requires the
   Keccak transcript, while BN254 packets use BLAKE3, so it would need a
   Keccak transcript variant for the recursive stage plus a BN254 exporter.

## FRI retune: what the sizing shows

The first-stage circuit depends only on the saved FRI key and its parameters,
so it can be re-sized without a proof. The `fri_sizing` example under
`crates/proof-compression/examples` loads the checked-in Init key
(`tests/fixtures/init-fri`), overrides the query count and optionally the
trace heights (`FRI_SIZING_MAX_LOG`), the circuit set (`FRI_SIZING_DROP`) or
individual circuit shapes (`FRI_SIZING_SET=index:log_height:main_width`),
builds the verifier, and counts the translated BN254 frontend with the same
counting pass the worker's `kzg size` preflight uses. With
`FRI_SIZING_LOWER=1` it also materializes the translated circuit and runs
the partitioning step of the production lowering
(`multi_stark_layout_with_max_height` at the chosen height), which gives the
computation-partition count including hash-bridge rows plus the custom
trace and table heights before production's table merging; that costs 47 GiB
and 54 s at 100 queries. The final circuit inventory is the computation
partitions plus ten auxiliary circuits (four BLAKE3 add-rotate traces, five
smaller custom traces, one merged table), which the stage metadata of the
GPU runs below confirms: 9 + 10 = 19 and 5 + 10 = 15.

With the committed reduction change (`ffd25b69`) the command below reports
57,233,358 gates at 100 queries. The unpatched baseline figures in this
section, 113,913,480 gates at 100 queries matching the README, come from the
parent commit `5761ef42`; check that out, or revert `ffd25b69`, to reproduce
them.

```sh
cargo build --release --locked -p ix-proof-compression \
  --no-default-features --features bn254,parallel --example fri_sizing
FRI_SIZING_LOWER=1 target/release/examples/fri_sizing \
  crates/proof-compression/tests/fixtures/init-fri 40,100 24
```

### Per-query cost and its attribution

Each query of the current circuit costs 1,125,583 translated gates, 312,920
lookups and 578 BLAKE3 compressions; the query-independent remainder is 1.35M
gates. Varying the key's shape splits the per-query cost:

| Experiment on the key | Gates per query | Compressions | What it prices |
| --- | ---: | ---: | --- |
| Baseline, 19 circuits, largest LDE `2^26` | 1,125,583 | 578 | — |
| Heights capped at `2^20` | 1,035,911 | 450 | one hash level ≈ 700 gates, 150 lookups |
| Heights capped at `2^16` | 961,673 | 345 | same, 703 gates per level |
| Without the four wide BLAKE3 circuits | 778,415 | 541 | one opened value ≈ 920 gates, 290 lookups |
| Only the seven FRI computation traces | 630,153 | 490 | same, ≈ 890 gates per value |

About 800 base-field values are opened per query across the 19 stage-3
circuits (seven FRI computation partitions at `2^24` with 44 each, four
BLAKE3 custom traces at `2^23` with about 70 each, and eight small tables),
so the opening reduction was about 65% of the per-query cost and hashing
about 36%.

### The opening reduction was an implementation cost

The reduction loop in `fri/pcs.rs` spent three extension multiplications
per opened value per query: advancing the alpha power, weighting the
difference by it, and multiplying by the opening denominator `1/(ζ_p − x)`.
The alpha powers and the alpha-weighted sums of the out-of-domain
evaluations are query-independent; the denominator depends on the query
point but is shared by every column of one (height, opening point). The
change folds the two query-independent quantities once per height, so each
query pays one extension-by-base product per opened value and one
denominator product per (matrix, point).
This is not a protocol change: the reduced value, the alpha index of every
column, the transcript and the proof bytes are identical, and the circuit
still constrains every input. It is the in-circuit port of the same
restructuring Plonky3 applied to its native FRI verifier in PR #2015
(commit `a724a1aec0acab47384b34efc2a4d163e0351251`, "hoist the
query-invariant alpha work out of open_inputs"), which is why its
description matches the figures here: one extension-by-base dot product
per opening point plus one multiply by `1/(z − x)`, instead of three
extension multiplies per column. The circuit changes, so the first-stage
verifying key regenerates. Measured with the same example:

| Circuit | Gates per query | Lookups per query | Gates at 100 queries | Lookups at 100 queries |
| --- | ---: | ---: | ---: | ---: |
| Current | 1,125,583 | 312,920 | 113,913,480 | 31,689,479 |
| Shared alpha powers, factored denominators | 554,220 | 141,070 | 57,233,358 | 14,643,377 |

The verifier integration tests (`plonkish_pcs`, `plonkish_plan`,
`plonkish_batch`, `plonkish_verifier_algebra`, `plonkish_verifier_security`,
`pipeline_root`, `root_profile`) pass against the patched circuit. After the
change the per-query cost is about 73% hashing, so folding arity and Merkle
caps become the next lever.

### Measured on the GPU

Both workers were built from the same tree with `bn254,parallel,cuda` for
SM 120, differing only in `fri/pcs.rs`, and run on the saved Init FRI fixture
with development parameters prepared beforehand (2^24 and 2^26, 46 s). Host:
32 logical CPUs, 249 GiB, one RTX PRO 6000 Blackwell (97 GB), local NVMe.
Settings follow the README's matched comparison: one device, 8 GiB resident,
2^24 MSM chunks, constraint passes on, SRS cache off, TeXRay on, default CPU
parallelism. Each stage ran under `tests/run_gpu_stage.py`; records are under
`/opt/dlami/nvme/ix-retune/runs/`. One run per cell, OS page cache
uncontrolled. For scale, the baseline cold first stage took 207 s on the
48-CPU reference host and 235 s here.

| First KZG stage | Baseline | Patched reduction | Change |
| --- | ---: | ---: | ---: |
| Cold fixed cache, wall time | 235.4 s | 148.9 s | −37% |
| Warm fixed cache, wall time | 135.2 s | 92.2 s | −32% |
| Peak host RSS | 175.3 GiB | 114.4 GiB | −35% |
| Sampled peak VRAM | 28.4 GB | 28.9 GB | — |
| Circuits | 9 × 2^24 + 10 small = 19 | 5 × 2^24 + 10 small = 15 | |
| Compact proof | 32,869 B | 27,365 B | −17% |
| Opening MSM terms (variable + fixed) | 326 + 247 | 286 + 179 | −19% |

Warm phase spans, baseline → patched: translate 36.2 → 23.2 s, prepare
28.6 → 20.0 s, prove 42.4 → 27.2 s (lookup construction 16.1 → 10.5 s,
quotient 14.3 → 8.8 s, openings 11.7 → 7.6 s), lowering 13.8 → 11.5 s.

| Recursive KZG stage | Over baseline first proof | Over patched first proof |
| --- | ---: | ---: |
| Wall time, cold fixed cache | 77.4 s | 76.2 s |
| Peak host RSS | 81.2 GiB | 78.6 GiB |
| Frontend rows / opening MSM terms | 61,151,005 / 583 and 9 | 50,627,679 / 475 and 9 |
| Padded computation trace | 2^26 | 2^26 |
| Native verification of the first proof, deferred pairings | pass | pass |
| Final packet | 1,909 B | 1,909 B |

The recursive stage natively verified the patched first proof and its
external pairings, which is the full-scale correctness check for the patched
circuit. Its own cost did not move because the frontend still pads to 2^26;
it would need to fall below 2^25 rows to halve. Those recursion figures are
cold-fixed-cache runs; the warm figure is below.

Under admitted Ignition parameters, patched worker, warm fixed caches, same
settings, one run per stage (`/opt/dlami/nvme/ix-retune/runs/ignition-opt/`):

| Stage, warm, Ignition | README reference host (48 CPUs) | Patched, 32-CPU host | Change |
| --- | ---: | ---: | ---: |
| First KZG | 135.9 s | 93.4 s | −31% |
| Recursive KZG | 44.6 s | 40.6 s | −9% |
| Total | 180.5 s | 134.0 s | −26% |

Peak RSS 114.4 GiB and 60.6 GiB; sampled VRAM 28.9 GB and 58.1 GB. Both
proofs verified natively with the deferred pairings; the first proof is
27,365 B and the recursive packet 1,909 B. The recursion's cold pass on the
same host took 75.6 s, so its 44.6 → 40.6 s warm change is within the
noise of a single run, while the first stage's reduction is the circuit
change.

Per circuit, the patched first proof's commitments are: five computation
partitions at 3 + 5 + 2 variable and 17 fixed each; four BLAKE3 add-rotate
traces at 32 to 40 main + 9 to 11 lookup + 2 quotient variable and 14 fixed
each; and six small traces. The four BLAKE3 traces alone hold 192 of the 286
variable commitments. A one-partition first proof would therefore still carry
about 246 variable and 111 fixed commitments.

### Exact lowered layouts

Lowering the translated circuit at the first stage's height cap gives the
real partition layout. The computation partitions below are followed in each
case by the same ten auxiliary circuits: four BLAKE3 add-rotate traces
(widths 32 to 40, `2^21` to `2^22` rows), five smaller custom traces and one
merged table.

| Circuit | Queries | Height cap | Computation partitions | Used rows |
| --- | ---: | ---: | --- | ---: |
| Current | 100 | `2^24` | 9 × `2^24` | 150,796,384 |
| Current | 80 | `2^24` | 7 × `2^24` + `2^22` | 120,993,524 |
| Current | 60 | `2^24` | 5 × `2^24` + `2^23` | 91,190,662 |
| Current | 40 | `2^24` | 4 × `2^24` | 61,387,802 |
| Optimized reduction | 100 | `2^24` | 5 × `2^24` | 77,070,160 |
| Optimized reduction | 100 | `2^25` | 2 × `2^25` + `2^24` | 77,070,160 |
| Optimized reduction | 40 | `2^24` | 2 × `2^24` | 32,254,358 |
| Optimized reduction | 40 | `2^25` | **1 × `2^25`** | 32,254,358 |
| Optimized, one `2^27` FRI trace and one `2^25` BLAKE3 trace in stage 3 | 100 | `2^25` | 2 × `2^25` + `2^19` | 67,620,479 |
| Optimized, same merged shape | 40 | `2^24` | 2 × `2^24` | 27,613,737 |

The nine-partition baseline matches the real run's 19 circuits (nine
computation plus ten auxiliary). The merged stage-3 shape rows are hypothetical
keys (the stage-3 prover has not produced them) and are included to show that
merging buys less than the reduction change did.

## Soundness accounting

`tests/fri_security_estimate.py` decodes a saved `outer-vk.bin`, derives the
instance facts from its circuit shapes, and prints every error term per
regime. Its unique-decoding, conjectured, ALI and DEEP formulas follow
`p3-security` at the pinned Plonky3 `3152b14a`; the Johnson column is
printed twice, in that revision's BCHKS25 form and in the DKT26 line-count
form of Plonky3 `main` at `4615dcd`, and the table shows the DKT26 value with
the pinned value in the limiting-terms column where they differ. The lookup
term is multi-stark's documented `(W + 2)·N / |F|`. For the checked-in key:
largest trace `2^24`, degree-2 Goldilocks extension (128 bits), BLAKE3 at 128
bits of collision resistance, 657 batched columns, 195 folded constraints,
maximum constraint degree 4, two opening points, `N = Σ height × lookups =
1,785,791,520`, `W = 8`. Hypothetical shapes recompute these: the single
`2^27` FRI trace raises `N` to 2,037,449,760 (lookup term 93.75) and drops
the batched columns to 441; adding the merged BLAKE3 trace gives `N =
1,970,340,896` (93.80) and 231 columns.

```sh
K=crates/proof-compression/tests/fixtures/init-fri/outer-vk.bin
python3 tests/fri_security_estimate.py $K
python3 tests/fri_security_estimate.py $K --queries 40
python3 tests/fri_security_estimate.py $K --drop 1,2,3,4,5,6 --set 0:27:3 --log-arity 3
python3 tests/fri_security_estimate.py $K --drop 1,2,3,4,5,6,11,12,13 --set 0:27:3,10:25:40 --log-arity 3
```

| Compression-stage shape | Proven, unique decoding | Proven, Johnson (DKT26; pinned BCHKS25) | Conjectured | Limiting terms |
| --- | ---: | ---: | ---: | --- |
| Current: `2^24`, blowup 4, 100 queries, 20 grinding bits, binary folding | 87.8 | 83.8 (81.2) | 93.9 | query / batching / lookup |
| `2^24`, folding arity 8 | 87.8 | 83.8 (81.2) | 93.9 | commit term falls 102.0 → 99.2 but does not bind |
| `2^24`, 40 queries | 47.1 | 59.9 (59.6) | 93.9 | query / query / lookup |
| One `2^27` FRI trace, arity 8, 100 queries | 87.8 | 81.4 (78.8) | 93.8 | query / batching / lookup; commit 96.2 |
| Same, 8 commit-grinding bits | 87.8 | 81.4 (78.8) | 93.8 | commit restored to 104.2 |
| One `2^27` FRI trace and one `2^25` BLAKE3 trace, arity 8, 100 queries | 87.8 | 82.3 (79.7) | 93.8 | query / batching / lookup |
| Same, 40 queries | 47.1 | 59.9 (59.5) | 93.8 | query / query / lookup |
| `2^24`, blowup 8, arity 8, 60 queries | 69.8 | 81.8 (78.7) | 93.9 | query / batching / lookup |

Bits of security; each cell is the minimum over ALI, DEEP, lookup, batching
(proven regimes), FRI commit, FRI query and collision terms; the script
prints each term. Three corrections to the earlier draft of this document:
the conjectured figure is bounded by the lookup term near 93.9 bits, not by
the FRI commit term at 101.7; folding arity
is not free, it costs `log2(2^a − 1)` bits in the commit term (2.8 bits at
arity 8), which binds nowhere here but should be re-checked per shape; and
the taller `2^27` trace costs 3 bits in the commit term and 3 bits in the
Johnson batching term. Merkle caps cost nothing.

**Required security floor:** the current proven security bound must not be
reduced further. Compare the baseline and each complete candidate shape
under the same proven assumptions and accounting, including all applicable
error terms. An unchanged conjectured bound does not satisfy this
requirement if the proven bound decreases.

The 40-query configurations above are therefore excluded, despite their
unchanged conjectured bound. Their sizing results remain useful diagnostics,
not admissible parameter choices. Keep 100 queries for the current
configuration; any alternative query count, blowup, folding schedule or
trace layout must first demonstrate that it preserves the proven bound.
Increasing blowup at stage 3 also faces the 192 GiB LDE-array guard in
`pipeline/root.rs`.

## Path to removing the recursive stage

Measured layouts, in the order the changes should land:

| Step | First stage at 100 queries | At 40 queries (sizing only) | Status |
| --- | --- | --- | --- |
| Today | 9 × `2^24` + 9 small circuits | 4 × `2^24` + 9 | measured |
| Opening reduction with shared alpha powers and factored denominators | 5 × `2^24`, or 2 × `2^25` + `2^24`, + 9 | 2 × `2^24`, or **1 × `2^25`**, + 9 | measured; patch uncommitted, tests pass, keys change |
| Plus folding arity 8 and Merkle cap 6 | ≈ 578 → 295 compressions per query, about −35% rows: projected 3 to 4 × `2^24` | projected 1 × `2^24` or `2^25` | blocked: in-circuit verifier asserts binary FRI and cap 0; multi-stark CUDA asserts the same; pinned p3-fri accepts a prover-chosen schedule (#2033) and has cap bugs (#2372, #2378) |
| Plus merged stage-3 shape (one `2^27` FRI trace, one BLAKE3 trace) | 2 × `2^25` + `2^19` measured on a hypothetical key, before arity | 2 × `2^24` | unmeasured stage-3 prover cost; smaller gain than the two rows above |

To preserve the proven security bound, the current configuration keeps 100
queries. The realistic landing point after the first two steps is about
three `2^25` computation partitions plus the ten auxiliary circuits, or two
if the merged shape pays off and preserves that bound. The measured
one-partition result at 40 queries is excluded from the implementation path
because it lowers the proven bound.

Fewer rows do not by themselves make the first proof wrappable. KZG commits
to every column separately, and the first stage's columns are dominated by
the BLAKE3 custom traces (32 to 40 main columns each) rather than by the
computation partitions (3 main columns each). Counting from the measured
stage metadata, a one-partition first proof still carries about 246 variable
commitments and 111 fixed ones (the four BLAKE3 traces alone hold 192
variable), against 15 and 19 in the recursive packet; its opened values and
transcript scale the same way.

| Wrapped packet | MSM terms | MSM estimate, baseline GLV at 0.28M/term | Scaled to classic GLV (×0.82) | With transcript (today's 4.9M scaled by packet bytes) |
| --- | ---: | ---: | ---: | ---: |
| Recursive packet (measured wrapper) | 35 | 9.7M | — | 14.7M total, compiled |
| Patched five-partition first proof, four BLAKE3 traces (measured compile) | 475 | — | — | **130.85M, domain `2^27`** |
| One-partition first proof, four BLAKE3 traces | ≈ 360 | ≈ 101M | ≈ 82M | over the 67M ceiling |
| One-partition first proof, one merged BLAKE3 trace | ≈ 179 | ≈ 50M | ≈ 41M | ≈ 60M |

The first of those rows is now a measurement. The PLONK exporter and the Go
circuit were generalized to any number of circuits, a claim schema and an
optional deferred pairing (`ix-compression-worker plonk export-first
<first-kzg-dir> <expected-statement.json> <out> [--dev-srs]`, then the
helper's `compile`). Exporting the patched 15-circuit first proof gives a
verifying key with 295 points, 560 scalars, 179 fixed commitments, 9 opening
groups and a 10,160-node scalar program; gnark compiles it to
**130,850,185 constraints, domain `2^27`**, in 121 s and 44 GiB. That is
twice the `2^26` ceiling, so wrapping the first proof as it stands is out.
The merged-trace row remains an estimate below the ceiling with no headroom
to speak of and none of the production constraints (CUDA path capped at
`2^24`, `2^25` CPU proving at 104 s) accounted for; sizing it needs a
first-stage key with that shape, which the stage-3 prover has not produced.

If that compile fails to fit `2^25` or `2^26`, the remaining route is for the
first stage to commit to fewer polynomials, for example by interleaving the
columns of a trace into one taller polynomial (the "fflonk-style packing"
the architecture doc already lists as a later PCS change). Until one of
these lands, the recursive stage stays as the commitment-packing step and
the measured win is the first stage's own time, 135 s to 92 s warm on the
GPU, with the recursive stage unchanged.

STIR does not help here. Its savings come from shrinking later rounds' query
counts, while the round-0 opening reduction and input Merkle paths that any
STIR or FRI verifier performs identically are most of this circuit.

## Where the rows go: gadget-level attribution

Two counting reports now live beside the gadgets and run with
`cargo test ... -- --ignored --nocapture`: `recursive::native_msm::cost_breakdown::report`
for the opening MSM and `fri::pcs::cost_breakdown::report` for the first-stage
verifier's per-query pieces. Rows are gates plus lookups in the builder's
counting mode.

### Recursive opening MSM

| Component | Rows | Notes |
| --- | ---: | --- |
| Fq multiplication | 164 | 108 gates, 56 lookups; a relation is about 130 rows of which 56 are 16-bit range lookups |
| Affine addition | 752 | one inverse hint plus four relations |
| Affine doubling | 536 | |
| 16-way point select, variable base | 360 | 15 selects of 8 limbs, 3 gates per limb |
| 16-way point select, fixed base | 232 | constant tables |
| Variable-base 16-entry table | 10,077 | 15 curve operations |
| Fixed-base 16-entry table | 637 | |
| Scalar to bits | 961 | per term |
| Per variable term, 64 windows | 82,445 | 64 × (360 + 752) + table + bits |
| Per fixed term, 64 windows | 64,781 | 64 × (232 + 752) + table + bits |
| Shared per MSM | 556,850 | 256 doublings and two 254-bit constant multiplications for the offset correction |

For the real first proof (296 variable and 179 fixed terms) this reproduces
the 37.75M-row MSM phase within 3%. The affine addition is 58% of a variable
term and 74% of a fixed term; the window selects are 28% and 23%. This is why
GLV cannot help: with doublings already shared, splitting each scalar into two
halves leaves the number of additions unchanged.

Widening the range-check limbs from 16 to 20 bits (`RANGE_BITS` in
`recursive/native_field.rs`, a `2^20`-row table instead of `2^16`) cuts an Fq
multiplication to 144 rows and an addition to 672, about 8% off every MSM
term. On the real first proof the recursive frontend goes from 50,628,004 to
47,662,557 rows with the witness and external pairings still passing; it
remains padded to `2^26`. The change is committed; the merged table trace
grows from `2^17` to `2^20` rows.

### First-stage verifier, per query, Goldilocks side

| Component | Rows | Compressions |
| --- | ---: | ---: |
| One Merkle level (order the pair, hash) | 736 | 1 |
| Same with an injected row hash | 864 | 2 |
| Hash 8 opened values | 608 | 1 |
| Hash 187 opened values | 11,348 | 25 |
| Encode one opened value to bytes | 60 | |
| Extension multiply | 10 | |
| FRI round 0 with a 25-level path | 21,284 | 26 |
| Sample 26 query bits | 192 | 1 |
| Sample an extension challenge | 4,084 | 4 |

A Merkle level was 736 rows of which 608 gates were the 64 byte selects that
place the sibling and the current digest in hash order: 9.5 gates per byte,
because `ByteGadgets::select` selected the value and both nibbles. The
compact BLAKE3 lowering only consumes the value, so two thirds of that work
was dead. With about 455 levels per query these selects were roughly 300k of
the 349k Goldilocks gates per query, the single largest first-stage cost
after the opening reduction fix.

### Lazy byte nibbles in multi-stark

multi-stark `d8c950be` (branch `sb/kzg-core`, on top of `416be66`)
makes `ByteValue`'s nibble decomposition optional: `select`
produces a value-only byte, and the generic paths that read nibbles (XOR,
word packing, comparisons) materialize them on demand with the same
nibble-hint-and-lookup constraints they always had. Measured with the sizing
example against the same change on the previous `sb/kzg-core` base:

| First stage, 100 queries | Before | Lazy nibbles |
| --- | ---: | ---: |
| Translated gates per query | 554,220 | 389,868 |
| Translated gates | 57,233,358 | 40,750,830 |
| Lookups | 14,643,377 | 14,646,161 |
| Used rows | 77,070,160 | 60,590,416 |
| Computation partitions at `2^24` | 5 | **4** |

This repository pins that revision. A CUDA worker built against the
change, with the 20-bit range limbs, ran the same warm Ignition sequence:

| Stage, warm, Ignition | README reference | Reduction patch | Plus lazy nibbles |
| --- | ---: | ---: | ---: |
| First KZG | 135.9 s | 93.4 s | **80.6 s** |
| Recursive KZG | 44.6 s | 40.6 s | 40.3 s |
| Total | 180.5 s | 134.0 s | **120.9 s** |
| First-stage peak RSS | 175.3 GiB | 114.4 GiB | 99.3 GiB |
| First-stage circuits | 9 + 10 | 5 + 10 | 4 + 10 |
| First proof | 32,869 B | 27,365 B | 25,989 B |
| Recursive frontend rows | 61,151,005 | 50,628,004 | 45,179,819 |
| Recursive MSM terms | 583 and 9 | 475 and 9 | 448 and 9 |

Both proofs verified natively with the deferred pairings under the admitted
setup; the recursive packet is unchanged at 1,669 B. Warm first-stage spans:
translate 16.6 s, lower 10.7 s, prepare 20.3 s, prove 24.1 s. The
recursion still pads to `2^26`, so its time did not move; its merged table
trace is now `2^21` rows because of the wider range table. All FRI,
first-stage and recursive gadget tests passed against the change.


## Refreshed terminal PLONK proof and Solidity verification

The optimized Ignition recursive packet now has a regenerated PLONK key and
GPU proof. The wrapper remains at 14,689,440 constraints and domain `2^24`,
with both pairing checks retained. One fresh prover process took 33.872 s,
including 11.557 s of core proving, on the same 32-CPU GPU host. One-time
key preparation took 495.843 s and is excluded from proving time.

An independent CPU helper verified the proof and rejected a changed claim
and corrupted proof. The refreshed Solidity verifier and claim-digest adapter
passed all 47 Anvil checks; the adapter transaction used 320,091 gas. Proof
sizes remain 584 bytes native, 624 bytes enveloped and 864 bytes in Solidity
encoding. The PLONK verifying-key SHA-256 is
`32b357a1090e6508aae17b2925af2162079a2d133c1702516618a24705da2fac`.

Combining the separately measured 120.9 s KZG stages
with this 33.9 s wrapper gives about 155 s from saved FRI proof to PLONK;
this is a sum of stage measurements, not a new end-to-end run.

## Upstream Plonky3 since the pin

The pin is 31 August 2026; `main` is 18 October 2026, 362 commits later.
Relevant to this pipeline:

- **Soundness fixes that matter for arity.** #2033 derives the FRI folding
  schedule from configuration instead of trusting the prover; the pinned
  verifier only checks that arities sum correctly, so two schedules can pass.
  Harmless at binary folding, which is all ix uses, but mandatory before
  enabling arity. #2372 and #2378 fix Merkle cap handling.
- **Security crate.** Legacy conjectured regime, the DKT26 Johnson bound,
  grinding-difficulty checks against the model, and composition of
  multi-STARK soundness with PCS budgets. A per-stage security report for the
  ix pipeline could be built on it directly.
- **Breaking transcript changes.** A typed Fiat-Shamir layer now drives FRI,
  STIR and WHIR, and the proof-of-work search squeezes the transcript first
  (#2199, #2200). Upgrading the pin changes proof bytes, so the in-circuit
  transcript and the recursive verifier would need re-deriving. This is the
  main cost of moving the pin.
- **Prover and verifier performance.** Concurrent commit LDEs (#2397),
  packed multi-round fold and cheaper opening quotient (#2204), closed-form
  fold rows and the hoisted verifier alpha ladder (#2015; the latter is what
  the first-stage circuit change above ports),
  Goldilocks scalar and packed arithmetic (#2098, #2116), Merkle trees built
  in subtree blocks (#2335). These speed the CPU paths; multi-stark's CUDA
  backend has its own kernels. No GPU work landed upstream.
- **New protocols.** STIR is wired into the full pipeline with its own
  schedule derivation, WHIR gained hiding and binary-domain variants, and a
  multilinear SuperSpartan-style `p3-multi-stark` crate with buses, LogUp*
  and binary-field backends has grown to 65k lines. These are
  architecture-level alternatives, not drop-in improvements for the current
  KZG path.

## Review notes

- The PLONK CUDA library is a second, independently built sppark
  instantiation with renamed symbols so it can coexist with the KZG kernels.
  The split-bucket MSM fix for structured witnesses lives only there. The KZG
  prover's main-trace columns are also byte-structured, so its MSMs may show
  the same bucket concentration.
- The driver's saved-FRI path never passes the terminal PLONK flag, so the
  benchmarked PLONK runs were produced by invoking the helper by hand. The CLI
  help text still describes the flag as BLS12-381 and Filecoin.
- The PLONK cache identity hashes both the Rust worker and the Go helper
  executables, so any rebuild of either triggers the six-minute key
  preparation. The benchmark doc already flags this.
- Recursive-stage phase timings for the GPU run are not recorded in the repo,
  only the CPU run's. The split of the 45 s between witness generation,
  commitment and quotient decides how much the fused worker is worth.

Sources: `crates/proof-compression/README.md`,
`docs/proof-benchmark-comparison.md`, the pipeline, recursive verifier and
wrapper sources, multi-stark `416be66` and `d8c950be`, and Plonky3
`3152b14a` and `main` at `4615dcd`.
