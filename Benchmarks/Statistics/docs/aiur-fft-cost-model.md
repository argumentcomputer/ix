# Aiur FFT cost predictor

Predicts **Aiur FFT cost** (`Ix.Aiur.Statistics.computeStats.totalFftCost`) — the
quantity that drives Aiur prover work and RAM — for a full-closure typecheck of a
Lean constant, from **cheap out-of-circuit profiler features** (no Aiur prover
run). Companion to this directory's `aiur-cost-dataset.md` (which goes the other way: FFT
cost → exec/prove/RAM), and to the zkVM-cycle predictor in the `ix` repo
(`docs/zisk-cycle-cost-model.md`). **The Zisk and Aiur models do NOT transfer**
(§4).

Profiling inputs: `~/benchdata/prof/` (per-name native features) and
`~/benchdata/fft/` (per-circuit stats). Aiur FFT costs: `../data/aiur/cost.csv` here.
Measured 2026-06-26, 250 GiB host.

---

![profiled features vs FFT cost](../figures/aiur_features_vs_fft.png)

## 1. What FFT cost actually is (exact, from source)

`Ix/Aiur/Statistics.lean` → `computeStats`:

```
totalFftCost = Σ_circuit  width_c · height_c · log₂(max(height_c, 2))
```

- **726 circuits** (constrained Aiur functions + memory circuits), total width 33,765.
- `width_c = layout.totalWidth` — **structural, identical across all constants**
  (same compiled IxVM kernel). Only the heights vary.
- `height_c = queryCounts[c].uniqueRows` — the **deduplicated** (memoized) row
  count for that circuit during execute. (`cacheHits = totalHits − uniqueRows`;
  "saved cost" runs 35–42%.)
- **No power-of-two padding** — smooth `h·log₂h` on the raw unique-row count.

This sum reconstructs the printed `Total FFT cost` to **0.000%** for every
constant (verified). So FFT is *exactly* a function of the per-circuit height
vector; the only modelling question is predicting those heights.

Per-circuit breakdown for a constant:
`ix check --ixe <env>.ixe <NAME> --stats-out out.txt` (out-of-circuit execute, no
prove; OOMs on the heaviest constants — see `aiur-cost-dataset.md`).

---

## 2. Cost drivers (per-circuit decomposition)

A handful of circuits dominate, and each one's height is an almost-perfect linear
function of **one cheap native profiler counter** (`hb`/`subst`/`defeq`/`bytes`,
recorded out of circuit by the `ix` repo's `only_const_profile` example):

| family | top circuits | share | counter | per-circuit R² |
|---|---|--:|---|--:|
| **BLAKE3 hashing** (content-addressing) | `blake3_g_function` (w=224), `blake3_compress_*`, `read_byte`, `get_expr` | ~30% | `block_bytes` | **1.00** |
| **Expr instantiation** (substitution) | `expr_inst1`/`_walk`, `expr_inst_many`, `list_lookup`, `address_eq` | ~20% | `subst` | 0.99 |
| **Memory / dedup** | `memory[3]` | ~4% | `defeq` | 0.999 |
| **Big-Nat arithmetic** | `klimbs_*`, `u64_sub_with_borrow`, `compare_klimbs`, `bytes_to_u64_limb`, `get_u64_le` | ~0.5%* | **none** | **0.14** |

\* but **37%** for `Std.Time.Week.Offset.ofMilliseconds` (time-unit conversions do
multi-limb division). This one unpredicted family is the entire accuracy ceiling.

Why `block_bytes` is the strongest single feature: `blake3_g_function`'s height
≈ `block_bytes` (it hashes the serialized closure, ~1 g-call per byte) and it's
the #1 circuit. The FFT is *dominated by hashing the serialized env*.

---

## 3. The predictor model (cheap features → FFT)

Because FFT = `Σ w·h·log₂h`, the right functional form is **`n·log₂(n)`** in each
counter (a linear model under-predicts the expensive tail 2–3× by missing the
`log(height)` factor). Fit by weighted least squares (weights `1/fft²`, relative
error), n=55 paired constants, FFT 1.9 M – 61.8 B:

| model | R² | MAPE | note |
|---|--:|--:|---|
| linear `hb + bytes + defeq` | 0.93 | 18% | wrong form — under-predicts tail |
| `bytes·log₂bytes` **alone** | 0.966 | 10% | dead-simple, blake3-dominated |
| **`hb·log₂hb + bytes·log₂bytes + defeq·log₂defeq`** | **0.976** | **9%** | recommended cheap model |
| + (measured) nat-arith term | 0.993 | 6% | needs execute — see §5 |
| `Σ width·h·log₂h` (per-circuit heights) | **1.000** | 0% | exact; needs execute |

Recommended cheap predictor: **`bytes·log₂bytes + subst·log₂subst + defeq·log₂defeq`**
(≈ the three predictable driver families). Coefficients shift with n; regenerate
on the current paired data rather than hard-coding. Inputs are all from the `ix`
repo's `only_const_profile` (native, no Aiur run, no OOM).

The table above is the n=55 Init/Std development calibration. The deployed
pipeline (`python -m benchstats aiur-predictor`) fits this same form on the current **n=65** paired
set (52 Init + 10 Mathlib + 3 Std) at **MAPE 9.3%** — confirming it transfers
across libraries; see `aiur-predicted-vs-actual.md` for the per-constant table.

---

## 4. Why the Zisk cycle model does NOT transfer

Zisk full-closure cost is `cycles ≈ 0.67M + 94,300·hb + 4,390·subst`
(reduction-dominated; serialized `bytes` adds nothing). **Aiur FFT is the
opposite:**

- `subst` alone is **useless** for Aiur (R² 0.45; adds nothing to `hb`).
- serialized **`bytes` is dominant** (R² 0.91 alone).
- the **Aiur/Zisk-cycle ratio ranges 0.33–4.09** (mean 1.65) — not a constant.

**Mechanistic reason:** Aiur FFT ≈ circuit *width × height*. `bytes`/ingress sets
the **width** (how much env is ingested into the trace); `hb`/`defeq` set the
**height** (reduction depth). Zisk full-closure pays only for trace *rows*
(height/reduction), so bytes are irrelevant there. Aiur pays for both dimensions.

---

## 5. The ceiling: big-Nat arithmetic (`klimbs`)

The cheap model caps at **~0.98** purely because of the big-Nat arithmetic
circuits. They're negligible (~0.5%) for almost every constant but dominate
arithmetic-heavy ones (`Std.Time.*` conversions). No `hb`/`subst`/`defeq`/`bytes`
counter predicts them (R² 0.14). NB: the whole-model 0.98 is high *despite*
nat-arith being unmodeled — it is **not** a 0.98 model *of* nat-arith.

**Negative result — a native `nat_arith` counter does not work.** Experiment
(uncommitted, `ix` repo `kernel-riscv`): added `bump_nat_arith(work)` to
`crates/kernel/src/profile.rs` + `OpCounts` + `only_const_profile`, charging
op-weighted limb-work (`la·lb` for mul/div/mod/gcd, `max(la,lb)` for
add/sub/bitwise/shift) in `whnf.rs::compute_nat_bin`. Result: lifts the whole
model only **0.976 → 0.980**, and is *backwards* on the discriminating case
(`Week.Offset.ofMilliseconds` NAT=318 vs `Array.qsort` NAT=695 — the reverse of
their 37% vs 0.8% Aiur klimbs share).

Root cause: the **native kernel does big-Nat arithmetic in `BigUint`** (a few
`compute_nat_bin` calls), but the **Aiur kernel does it limb-by-limb in gadgets**
— its cost is dominated by per-limb deserialization/comparison/division rows with
*no native analog*. The quantity you'd need is "number of Aiur limb-rows," which
only exists once you run the Aiur kernel. So there is **no cheap native predictor
for klimbs cost**; the 0.993 above used the *measured* klimbs heights (i.e. it
required execute).

**Paths to R²→1.0:** (a) the exact model — per-circuit heights from execute
(`ix check --stats-out`); or (b) model the Aiur `klimbs` gadget cost directly from
the IxVM kernel circuit definitions (weighting div/deserialization correctly) —
untried, more involved.

---

## 6. Data & reproduce

```bash
# per-name native features (hb, block_bytes, subenv_bytes, subst, whnf, defeq[, nat])
#   in ~/ix (kernel-riscv):
IX_PROFILE_COUNTERS=1 cargo run -q --release -p ix-kernel --example only_const_profile -- \
  initstd.ixe Nat.add_comm Array.qsort String.split ...

# per-circuit Aiur FFT breakdown for one constant (width, height, fftCost per circuit)
#   in ~/ix-aiur:
ix check --ixe initstd.ixe <NAME> --stats-out stats.txt

# fit: join features with ../data/aiur/cost.csv, WLS on n·log₂n features (python, ad hoc)
```

- Per-name features: `~/benchdata/prof/onlyconst_feat_fc.tsv`, `new_feat.tsv`.
- Per-circuit stats: `~/benchdata/fft/circ/*.txt`, `~/benchdata/fft/stats_*.txt`.
- Aiur FFT + exec/prove/RAM dataset & shapes: this directory
  (`aiur-cost-dataset.md`, `../data/aiur/cost.csv`, `python -m benchstats`).

---

## TL;DR for a new agent
1. FFT = `Σ width·h·log₂h` over 726 circuits; widths fixed, heights from execute. Exact.
2. Cheap predictor: `n·log₂n` of `bytes` (BLAKE3), `subst` (instantiation), `defeq`
   (memory) → **R² ≈ 0.976**, MAPE ~9%. `bytes·log₂bytes` alone gets 0.966.
3. Do **not** reuse Zisk's `hb+subst` model — for Aiur, bytes dominate and subst is useless.
4. The unmodeled ~2% is big-Nat `klimbs` arithmetic (matters only for arithmetic-heavy
   constants like `Std.Time.*`); it has no cheap native proxy. Exact requires execute.
