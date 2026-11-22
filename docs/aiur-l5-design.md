# Aiur compression L5: a narrow Goldilocks stage (design study)

> **Dropped (2026-11-16).** The estimated gain over L4 (−16 to +12 s) is
> within L3's benchmark spread, the configurations that come out ahead need
> fork-only shared fixed slots or a host-streaming GPU prover, and the 2^25
> narrow shard does not fit the 96 GB card. Kept as the record of the
> measured counts and the reasons.

Status: phase 1 (design and counts), 2026-11-16. No implementation. Counts
are measured by executing the real verifier program and lowering it with
the production template backend. Prover times are predictions from measured
runs of comparable stages, and every one is labelled "est.".

Baseline: L3, warm Init, 167.2 s (`target/e2e-l3/bench-v5`, run 1):

| Stage | Time |
|---|---:|
| wrap | 11.6 s |
| CompressGL | 77.9 s exposed. Execution 32.6 s single-threaded, trace 9.7 s, commit 14.5 s, open 8.6 s. |
| narrow BN | 54.5 s exposed |
| terminal and PLONK | 23.2 s exposed |

L4 (L3 with the wrap key fixed in CompressGL, `MultiStark/MultiStark/CompressGLFixed.lean`)
is estimated at 157–159 s, which puts CompressGL at about 68 s.

## 1. What L5 changes

CompressGL's cost is dominated by work that scales with the opened elements
per query `E` of the proof it verifies. In the GL model
(`target/root-width/model.py`), on the raw root, of 1,022M unpadded cells:
- leaf hashing, which scales with `q·E`, is 560M;
- reduced openings, which scale with `q·V`, are 259M;
- Merkle paths are 5M;
- key parsing and constraint evaluation are 151M;
- fixed work is 47M.

The two measured points (E 5,598 → 126.7 s, E 3,262 → 83.7 s) fit
`t ≈ 23.6 s + 18.4 ms·E`.

L5 puts a narrow-layout Goldilocks proof in front of CompressGL. A narrow
template proof opens per query, per shard:
- `W` main columns;
- the fixed columns;
- `2·stage2` (the LogUp accumulators are degree-2 extension columns);
- `2·quotient` chunks.

Plus two compact table circuits. At `W = 8` that is `8 + 42 + 12 + 4 = 66`
per shard, plus about 27 for the tables. The wrap opens 3,202 (layout v3).

## 2. Options

### (a) Insert narrowGL: wrap → narrowGL → CompressGL′

- **narrowGL** is a Goldilocks Aiur program verifying the normalized wrap
  proof, laid out by the narrow template backend on Goldilocks FRI.
  `log_blowup` 2, 100 queries and 20 PoW bits are unchanged.
- **Program.** `CompressWrap::verify_root` applied to the wrap proof works
  today with the wrap key as data (this is what was counted). A fixed-key
  form is `CompressGLFixed`'s template (L4) over the native Goldilocks
  libraries instead of `Field.Goldilocks.Emulated`. It saves the key hashing
  (about 12M rows). A full verifier plan would also drop
  `SystemDeserialize::read_nodes_n` (14.3M rows).
- **CompressGL′** verifies the narrowGL proof with the narrowGL key fixed
  (the L4 mechanism). It maps the narrowGL claim back to the root statement:
  the template claim chunks carry `H(wrap key digest, wrap claims digest)`,
  and the wrap claims carry the root statement. This is Aiur source in
  CompressGL′ and a two-level `WrapPolicy`.
- **The input shape is fixed.** The wrap's proof shape is fixed by its
  normalized layout, so narrowGL needs only small headroom (+0–5%) for
  data-dependent rows.

### (b) Narrow wrap: root → narrowWrap → CompressGL′

This replaces the wide wrap with a narrow layout of the same program on the
root.
- **Counted rows:** 478.9M (W=8, h0), 1.49× option (a), because the root
  opens 5,598 elements instead of 3,202. Root shape variation needs the
  wrap's +15% per-height headroom on top.
- **Saves:** the 11.6 s wrap.
- **Costs:** about 1.5–1.7× narrowGL's prove, so it is dominated by (a)
  unless narrowGL costs less than about 20 s.
- **Also dropped:** the wide wrap's normalization role. Narrow capacities
  normalize by construction, but they would carry the root's variability.

### (c) Mixed layout

- **Layout:** `Blake3::compress` as one wide unit, the rest narrow
  (`Periodic.mixed_heap_sound`, Goldilocks corollary exists). Compress is
  57% of narrow rows (§3), but as a wide circuit it opens 732 elements
  per query.
- **Narrow part:** 138.3M rows, 5 shards at `2^25`.
- **Cost:** E ≈ 920–1,090, committed ≈ 4.8B cells. CompressGL′ is about
  41–44 s (fit) and narrowGL about 23–30 s (est.), so the net is about 0
  against L4.

### (d) Variants that do not help

- **Wider `W`.** W=12 and W=16 cut rows (223.0M, 180.3M) but not committed
  cells (7.5B, 8.5B), and they add fixed columns (62, 83).
- **Re-grouping the wide wrap for lower E.** Explored in
  `target/root-width` and `aiur-structural-gap.md` §5b. Union-of-columns
  grouping does not go much below about 3,200 without large cell growth.

## 3. Measured counts

**Tool.** `target/l5-study/glcount` (`l5-glcount PACKAGE KEY CLAIMS PROOF
KEY_BLAKE3 HEADROOM LOG_SHARD W OUT`). It works in two steps:

1. It executes `CompressWrap::verify_root` natively over Goldilocks on the
   given proof, with the production wrapper artifact
   `target/wrap-normalized/policies/m16384w64.ixa` and its groups cleared.
2. It lowers the same bytecode with the template v2 backend (BN254 code
   path):
   - the modulus is replaced, so the templates depend only on graph
     structure;
   - constants above `p/2` are mapped to their negatives, so `±1`
     special cases match;
   - capacities are this execution's instances;
   - an unrolled compress counts one compression per instance.

Outputs are in `target/l5-study/*.json`. The wrap proof is
`target/e2e-l3/run-allLean/wrap/out` (v3).

**narrowGL: `CompressWrap::verify_root` on the wrap proof** (key as data).
The wide execution takes 4.4 s and has 570M unpadded wide main cells,
against 816M for the wrap on the root.

| W | headroom | template rows | `2^24` | `2^25` | `2^26` | `2^27` |
|---|---|---:|---:|---:|---:|---:|
| 8 | 0 | **321.0M** | 20 shards | 10 shards | 5 shards | 3 shards |
| 8 | +5% | 337.1M | | | 6 shards | |
| 12 | 0 | 223.0M | | 7 shards | | |
| 16 | 0 | 180.3M | | 6 shards | | |

| Top functions (W=8) | instances | rows/instance | rows | share |
|---|---:|---:|---:|---:|
| `Blake3::compress` (unrolled) | 72,467 | 2,521 | 182.7M | 56.9% |
| `Pcs::rows_pop` | 310,705 | 69 | 21.4M | 6.7% |
| `Pcs::ro_fold` | 594,541 | 33 | 19.6M | 6.1% |
| `StarkHash::b3_rows_chunks` | 40,841 | 382 | 15.6M | 4.9% |
| `SystemDeserialize::read_nodes_n` (key parsing) | 44,733 | 319 | 14.3M | 4.4% |

Leaf hashing of 3,202 elements × 100 queries is about 40K of the 72.5K
compressions; Merkle and FRI paths are most of the rest. Key-related rows
are 16.0M parsing, 3.2M IO and about 12M hashing. Fixed-key estimates:
about 308M rows with the L4-style key (parsing kept) and about 292M with a
full plan. Both are still 5 shards at `2^26` with +5%.

**Narrow wrap on the root** (option b): 478.9M rows, 101,384 compressions,
15 shards at `2^25`.

**Shapes and E** (W=8, 321M rows). Per row the shard commits
`8 + 2·6 + 2·2 = 24` base cells. The tables in E are the two Lean compact
tables, about 27; the Rust stacked tables would be about 365.

| Shards × height | committed cells per proof | fixed matrix | E, one shared fixed matrix | E, fixed matrix per shard (pinned multi-stark) |
|---|---:|---:|---:|---:|
| 1 × `2^29` | 12.9B | 22.5B | 93 | 93 |
| 3 × `2^27` | 9.7B | 5.6B | 141 | 225 |
| 5 × `2^26` | 8.05B | 2.8B | 189 | 357 |
| 10 × `2^25` | 8.05B | 1.4B | 309 | 687 |
| 20 × `2^24` as batch-shard proofs | 8.05B | 0.7B | — | about 1,347 (20 proofs) |

For comparison, the wrap commits 1.62B cells with E 3,202. NarrowGL commits
**5.0×** the wrap's cells for a verification job 30% smaller than the wrap's
own, which is about 7× wide cells for the same work. This is the expected
template blowup, mostly from BLAKE3: 20K cells per compression narrow
against about 5.8K wide.

**Security at unchanged FRI parameters** (model.py port of `FriSecurity.lean`):
- **Unique decoding:** 87.8 bits, the same as the root.
- **Conjectured:** 92.6 bits; the LogUp term over `GF(p²)` with
  `Σ height·lookups ≈ 2^31.8` binds it, and the root's is 92.4.
- **Johnson regime:** 80.1 / 82.7 bits, against the root's 81.1 / 83.7. It
  falls about 1 bit from the taller traces (`2^26`) and about 2 bits at
  `2^29`.

No parameter changes, but the derived bits move slightly.

## 4. Predicted times

**CompressGL′** (verifies narrowGL, key fixed):
- **Fit:** `23.6 + 0.0184·E` gives 27 s at E=189, 30 s at E=357, 48 s at
  E=1,347, plus per-proof path, FRI and OOD work for K separate proofs.
- **GL model:** unpadded cells at E=189 are about 83M (fixed 47, leaf 19,
  ro 7, path 7, key about 3), against about 626M on the v3 wrap. Scaling the
  measured phases (execution 32.6 s, trace 9.7 s, commit plus open 23.1 s)
  by that and keeping setup and SRS (about 8 s) gives about 15–20 s.
- **Range used: 15–27 s** for E ≤ 360, and **45–55 s** for the 20-proof
  layout.

**narrowGL** (est.):
- **Execution:** 4.4 s (measured, the wide interpreter).
- **Witness:**
  - The BN narrow stage measured 5.3 s for 30.0M rows (0.18 µs per row),
    which would be 56 s for 321M rows at BN cost.
  - Goldilocks words are 8 B against 32 B, and the field multiplication is
    native, so the estimate is **15–30 s**.
- **Prove:**
  - The wrap measured 1.62B committed cells in 3.5 s on the GPU (about
    0.46B cells/s, everything resident).
  - 8.05B cells would be **17–25 s** if it streamed at that rate.
  - **Memory:** at `log_blowup` 2 the CUDA backend needs about
    `40 B × (committed + fixed)` resident. Per `2^25` shard that is
    `66 × 2^25 × 40 B` = 88 GB, against a 72 GB budget on the 96 GB card
    (`aiur-trace-sharding.md` §7.1).
  - One proof is about 380 GB (9.5B cells), over the device and over the
    249 GB host.
  - Feasible today: `2^24` batch shards (20 proofs, about 2 s each), or
    `2^25`/`2^26` shards with the fixed LDE streamed from the host, which is
    new prover work in multi-stark CUDA.
- **Total: about 37–60 s.**

**End to end** (L4 ≈ 158 s, CompressGL in L4 ≈ 68 s):

| Configuration | narrowGL | CompressGL′ | Init (est.) | vs L4 |
|---|---:|---:|---:|---:|
| (a) 5 × `2^26`, one shared fixed matrix (shared-fixed slots), resident or streamed | 37–45 s | 15–27 s | 142–162 s | −16 to +4 |
| (a) 5 × `2^26`, fixed matrix per shard (pinned multi-stark), fixed LDE streamed | 40–50 s | 20–30 s | 150–170 s | −8 to +12 |
| (a) 20 × `2^24` batch proofs (fits today's GPU without new prover work) | 45–60 s | 45–55 s | 180–205 s | +22 to +47 |
| (b) narrow wrap on the root, 8 × `2^26`, no wide wrap | 55–75 s | 15–27 s | 148–180 s | −10 to +22 |
| (c) mixed: wide compress + narrow rest | 23–30 s | 41–44 s | 154–164 s | −4 to +6 |

The L3 benchmark spread is 156.8–187.8 s (median 167.9 s). No configuration
has a predicted gain outside that noise. The best case, which needs
crypto-layer work, is about −10 s.

## 5. What is missing

**Rust template backend** (`crates/proof-compression/src/aiur_backend/template/v2.rs`,
2.7K lines, and `v2/lean.rs`, 1.2K lines) is BN254- and KZG-specific:
- `Scalar`, `KzgConfig` extension parameters (D=1) for LogUp grouping and
  quotient degree, and `kzg::Compiler` over `TracePlan<Bn254>`;
- witness generation from BN wide traces.

It needs a field- and PCS-generic version: Goldilocks `TracePlan`, the
`aiur::trace::stark` Rust lowering, `GoldilocksBlake3Config`, D=2. The
logic itself (templates, numbering, periodic shards, compact tables, copy
labels) is field-agnostic. The `ts = tag + 4·sub` packing and labels below
2^62 fit under `p ≈ 2^64`; the exporter's bound check is `≤ 2^63`.

**multi-stark (pinned `bcf3fc8`)** has preprocessed traces, LogUp and the
batch protocol (`multi_stark::batch`) on Goldilocks. Missing for a
multi-shard narrow layout:
- **Shared fixed slots** (`System::new_shared`, fork `formal-aiur/shared-fixed`
  only), so periodic shards commit and open one fixed matrix. Without them
  each shard circuit carries its own copy: E 189 becomes 357 at 5 shards,
  and the cached fixed commitment grows 5×.
- **Or** one shard whose ids and labels are offset by a public per-shard
  value under the batch protocol. That is a change to the verified layout
  (`Periodic*` numbering), not only to multi-stark.
- **Prover-side:** streaming the fixed LDE (and possibly stage 1) from the
  host, so a `2^25`/`2^26` narrow shard fits 96 GB.
- **Fixed matrix size:** 42 columns at `2^26` is 2.8B cells, about 90 GB as
  an LDE. The L3 fixed-commitment cache (by layout digest) stores the
  commitment, but the prover still rebuilds the LDE every run (BN: 8–11 s
  for 1.4B cells).

**Lean.**
- **The narrow theorem exists over Goldilocks:**
  `Aiur.Tiling.Goldilocks.narrow_heap_sound_compact_goldilocks`, with the
  static hypotheses discharged in `Compiled.lean` (section
  `GoldilocksCompiled`). `mixed_heap_sound_goldilocks` and the wide and
  grouped Goldilocks corollaries also exist. The field hypotheses become
  `bound ≤ 2^63` and `cfg.bits ≤ 24` (multiplicity sums `≤ 2^63 < p`).
  NarrowGL's sizes fit: rows `≤ 2^39`, labels about `1.5·10^9`.
- **`tiling_export2`** (`MultiStark/Examples/TilingExport2.lean`) fixes
  `F := ZMod BN254.modulus`. It needs:
  - the `field` selector that `wide_export` already has;
  - Goldilocks `Ixa.decodeChecked`;
  - bound checks against `2^63`;
  - the Goldilocks corollary's hypothesis list.
- **Exporter scale.** It runs on 10.7× the rows of the BN stage: about
  3–6 min cold against 31 s, with memory not yet measured. Warm runs replay
  the export cache.
- **LogUp and Schwartz–Zippel over `GF(p²)`** are crypto-layer obligations
  (outside Lean by policy, as for the wrap and root). The challenge field is
  `BinomialExtensionField<Goldilocks, 2>` (`multi_stark::types::ExtVal`).
  The model's lookup term is 92.6 bits (above). The existing narrow
  soundness notes (`aiur-template-backend.md`, copy wiring and keyed
  chunks) assume a large field. Their per-message arguments are
  field-generic, but the collision bounds must be restated for `p²`
  instead of BN254 `r`.
- **New Aiur source:**
  - the narrowGL entry, `CompressWrapFixed` over native Goldilocks
    libraries, from `CompressGLFixed`'s template;
  - CompressGL′'s claim mapping from template claim chunks;
  - a two-level policy.

  Not proved, like the other verifier programs.

## 6. Recommendation: no-go for L5 now

- **Gain within noise.** The predicted Init time is 142–205 s by
  configuration, against L4's about 158 s and noise of ±15 s. The only
  configurations with a predicted gain need shared fixed slots in the
  crypto layer or a host-streaming CUDA prover. Even then the gain is about
  −10 s (best −16 s).
- **The template blowup cancels the CompressGL saving.** The saving
  (68 → 15–27 s) is real, but the narrow layout commits about 7× the wide
  cells for the same verification work. 57% of that is BLAKE3 compressions
  at 2,521 rows each, so narrowGL costs about as much as it saves.
- **New trusted surface:** the narrow layout over Goldilocks FRI,
  restated LogUp bounds for `p²`, and possibly shared fixed slots. L3/L4
  carry none of these.

**Cheaper ways to save the same seconds** (prover-side or source-only):
- CompressGL execution is 32.6 s single-threaded; parallel or streamed
  execution is prover-only.
- L4's key fixing.
- The PLONK `NewTrace` precompute (−5.6 s, pending a gnark pin decision).

**If L5 is revisited:**

1. **De-risk first** (1–2 days, one GPU run): a synthetic Goldilocks
   multi-stark proof of the narrow circuit shape (8 main, 42 fixed,
   11 lookups in groups of 2, degree 3) at `2^24`, `2^25` and `2^26`,
   measuring prove time and VRAM. This turns narrowGL's 37–60 s into a
   measurement. Pursue only if 5 × `2^26` proves in ≤ 20 s and fits.
2. **Template backend generic over field and PCS** (Rust): 4–6 days.
3. **`tiling_export2` field selector and Goldilocks bounds;** run the
   exporter at 321M rows under a memory cap: 1–2 days.
4. **Multi-shard fixed handling,** either shared fixed slots upstreamed to
   multi-stark (crypto surface and FV TODO) or a host-streamed fixed LDE:
   5–15 days.
5. **Aiur source:** `CompressWrapFixed` over Goldilocks, CompressGL′ claim
   mapping and policy: 2–4 days.
6. **Driver, caches, setup and rekeying, e2e, negatives:** 3–5 days.

The total is about 3–5 weeks.

**Risks:**
- device memory (the main blocker);
- fixed LDE size and rebuild time;
- exporter time and memory at 10× rows;
- CompressGL′ fixed costs (the fit's 24 s intercept against the model's
  about 10 s);
- per-proof overhead if batch proofs are used;
- −1 to −2 Johnson-regime bits from taller traces;
- every key after the wrap changes.
