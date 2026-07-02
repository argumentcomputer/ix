# Zisk cycle cost model

Predicts **Zisk guest cycles** (≈ RISC-V STEPS) and **prover RAM** for
typechecking a Lean environment — or one constant, or a shard — in the Ix zkVM.
Purpose: **shard sizing**, splitting a large environment into pieces that each
prove within the RAM cap while minimizing the number of pieces.

Measured on an RTX PRO 6000 (250 GiB host). Inputs, scripts, and raw data:
`~/benchdata/prof/`.

> **Version note.** All numbers below were measured on the Zisk v0.18-based
> `blake3-precompile` branch. On the v1.0.0-alpha port the cycle counts drift
> slightly from upstream zisklib/ROM changes (e.g. `nataddcomm.ixe`:
> 53,239,676 → 53,860,206 STEPS, ~+1.2%); the model's structure and
> coefficients remain a good approximation but have not been re-fit.

---

## Background

A compiled Lean program is an *environment* (`.ixe`): a set of *constants*.
Typechecking verifies them. The kernel runs from one Rust source both **out of
circuit** (native — used to *profile*) and **in circuit** (RISC-V, inside Zisk —
what gets *proven*). A large env can't prove in one piece, so it is split into
**shards** (planner: `crates/kernel/src/shard.rs`). The constants assigned to a
shard are its **members**; the constants they depend on may live in other shards.

The profiler (`crates/kernel/src/profile.rs`) records cheap per-constant
variables (the model's inputs) to predict in-circuit cost:
- **hb** (heartbeats) — kernel reduction steps (recursion fuel).
- **bytes** — serialized constant size (deserialization cost).
- **subst** — substitution-node visits (`instantiate_rev`); a finer measure of
  reduction *volume* than hb.

**STEPS vs COST — two different things:**
- **STEPS** = RISC-V instruction count → drives **prover RAM** (trace rows).
  This is what the model predicts; 1 step = 1 instruction, workload-independent.
- **COST** = Zisk's weighted proof-area → drives **prove time**.
  `COST = 293.6M base + 68·STEPS + opcodes + precompiles + memory`.
  **COST/STEPS is workload-dependent**: ≈100 for the Ix kernel, but ≈384 for a
  precompile-heavy blake3 program (its blake3 precompile is 67% of cost at almost
  no steps). So STEPS→RAM is portable; STEPS→prove-time needs a per-workload
  factor.

**What actually drives STEPS** (verified in the Zisk + kernel source). One
RISC-V instruction = exactly 1 step (`zisk .../emu.rs`), so cycles are the
kernel's total instruction count, and the kernel's instructions are
overwhelmingly **reduction** — `whnf` + `is_def_eq`. One heartbeat is one
reduction step past the memo caches (`tc.rs`, `whnf.rs`, `def_eq.rs`); `hb`
counts those steps, `subst` counts the substitution-DAG traversal inside them.
Three things are deliberately **not** step drivers, which is why the model
ignores them:
- **blake3 hashing** is a Zisk precompile — 1 step, 12,000 COST. A COST driver,
  not a STEP driver.
- **Memory traffic** is a COST term (`MEM_READ_COST` etc.), not steps.
- **Serialized literal content** (strings, byte blobs) is stored by reference in
  a separate `blobs` map and fetched lazily — **never walked into terms**. This
  is the mechanistic reason `bytes` doesn't predict cycles and a 1 MB string
  literal is ~free (confirmed both in source and by direct measurement).

---

## Cost models

For a shard, sum the variables over **only its own member constants** — not the
dependency closures they pull in (see Findings).

Fit quality is reported as **MAPE** (mean absolute percentage error — the average
of `|predicted − actual| / actual`, so "6%" means predictions land within ~6% of
measured cycles on average) and **R²** (fraction of variance explained, 1.0 =
perfect). Fits are weighted least squares minimizing *relative* error, the right
objective for a cost spanning 50M–9B cycles.

**Full-closure typecheck** — a self-contained closure: a small program, or a
constant checked with all its dependencies. Calibrated **cross-library** on
n=76: 12 small programs + 64 diverse constants checked full-closure via
`--consts`, spanning **Init (51), Std (3), and Mathlib (10)**:
```
cycles ≈ 0.68M + 96,989·hb + 4,151·subst        R² 0.987, MAPE 6%
```
Per-library MAPE is uniform (Init 6%, Std 6%, Mathlib 5%, programs 8%) — one
model across libraries, not Init-tuned.
Reduction-dominated: `hb` alone reaches R² 0.99, `subst` is the useful second
variable, serialized `bytes` adds nothing.

**Per shard** — summed over the shard's member constants:
```
cycles ≈ 199M + 167,900·hb + 2,928·bytes                R² 0.974, MAPE 14%
       ≈ 180M + 162,300·hb +   652·bytes + 4,276·subst  R² 0.988, MAPE  9%
```
Same slopes as the full-closure model; the extra ~180M intercept is the
per-shard fixed floor plus the foreign-dependency ingress a shard re-pays. The
planner uses exactly these best-fit constants (`shard.rs`: `STEPS_PER_HEARTBEAT`
162,339, `STEPS_PER_SUBST` 4,276, `STEPS_PER_INGRESS_BYTE` 652,
`SHARD_STEP_FLOOR` 180M) — one definition, used for the `ix profile` breakdown,
per-shard prediction, and the packer's cap test. No conservatism is baked into
the slopes (that would distort packing); the cap's margin is `RAM_USABLE_FRAC`
plus the model's own ~1.1× over-prediction.

**Subject-only** (`--skip-deps`) — check one constant, trust its deps. A
separate, cheaper, **ingress-dominated** regime (`hb` near-useless):
```
cycles ≈ 0.39M + 6,740·block_bytes + 14·subenv_bytes + 4,070·subst   R² 0.96, n=36
```
Reserved for constants too expensive to full-closure-check that can't be sharded
(Finding 4).

**Measuring one constant.** `zisk-host --execute --ixe initstd.ixe --consts
<NAME>` resolves the name, builds just its closure sub-env (deps lazily faulted
in — no separate `.ixe`, no whole-env ingress), and checks it. Full-closure by
default (`Ix.Claim.check addr none`); add `--skip-deps` for subject-only. Same
`--consts` / `--skip-deps` vocabulary as `ix check`, `sp1-host`, and the Aiur
`bench-typecheck`.

---

## Prover RAM and prove time

Measured proving 7 Init shards on GPU, STEPS 0.27–3.79e9:
```
peak host RAM (GiB) ≈ 50 + 33·STEPS_billions     R² 0.99
GPU prove time (s)  ≈ 54 + 158·STEPS_billions     R² 0.98   (~6.3M steps/s)
```
Inverting the RAM model
at `RAM_USABLE_FRAC` = 0.85 gives a safe per-shard cap of **~3.6e9 steps** for a
200 GiB target (`shard.rs:cycle_cap_for_ram`).

**Validated end-to-end.** Proving + aggregating all of `mergesort`
(an 8.94e9-cycle env) under a ~180 GiB cap produced 3 shards (actual
2.77/2.45/2.20e9 cycles), **147 GiB peak RAM** (predicted ~153), folding to one
unconditional proof in **~23.5 min** (1281 s leaf proving + 13 s aggregation).
Per-shard actuals landed **~1.13× under** the model's prediction and peak RAM
matched — the cap and RAM models hold against real proving, on the conservative
side.

---

## Key findings

1. **Full-closure cost is reduction-dominated.** `hb + subst` predicts it
   (R² 0.99); serialized `bytes` adds nothing. Subject-only cost is the opposite
   — ingress-dominated, with `hb` near-useless.
2. **Cost a shard from its members only.** Sum the variables of the shard's
   *own* member constants (R² ≈0.95). Including their dependency closures — deps
   once, or deps per member — scores **negative R²**: it double-counts shared
   deps nonlinearly. So there is no shared-dep reuse to over-provision for.
3. **Sharding is bin-packing per-constant costs** under the RAM cap, *not*
   balancing. The cap planner (`partition_for_cycle_cap`) packs each shard as
   full as the cap allows — fewest shards (`≈⌈total/cap⌉`), each maximally
   performant — rather than equalizing per-shard work (which over-shards: every
   shard left partly empty). A fine min-cut pre-partition supplies a cut-coherent
   order so dependency overlap packs into the same shard (paid once, not
   re-ingressed). The cap test counts that cross-ingress, so a shard packed to
   the cap still executes under it. Each leaf pays the ~180M fixed floor and adds
   an aggregation node, so cheap constants are batched rather than proven one at
   a time. (`--shards N` still does balanced bisection, for manual control.)
4. **A few constants can't be proven as a single full-closure leaf on a 250 GiB
   box**: `Vector/Array.extract_append._proof_1`, the `instRxcHasSize_eq` family.
   This is a per-leaf ingress/RAM ceiling on the `--consts <name>` (full-closure,
   `Ix.Claim.check addr none`) mode — not a global unshardability. In
   env-sharding mode (`--shard-plan`) these same constants are fine: their
   subject checks fit in one work item and their deps are proved in other
   shards, folded in through the assumptions root. The only work unit the
   env-sharding planner truly can't split is a **mutual block** (`build_anon_work`
   emits one item per Muts block, checked atomically). The escape hatch in
   single-constant mode is `--skip-deps`: `Vector.extract_append` is the 143 GiB
   OOM case under full-closure but checks subject-only in 74M cycles. The
   planner flags these via `infeasible_atomic_floor`.
5. **The packing order comes from min-cut.** Whole-env profiling of
   Init/Std/**Mathlib** (mathlib = 631k blocks) shows Lean typecheck is uniformly
   reduction-dominated: own-bytes is only **2.6–7% of member cost** (mathlib
   lowest, at 2.6%). On Zisk that makes cross-ingress a ≤3% term, and a plain
   block-id order packs within ~2% of min-cut at ~1× the proving cost. min-cut
   remains the default because the same `.ixprof`/`.ixes` feeds **Aiur**
   (ingress-first), because it stays robust if an ingress-heavy env shifts that
   balance, and because it keeps each shard's injected closure under the 512 MB
   guest heap. The cap planner is order-agnostic, so the order is a pluggable
   choice; min-cut is the one that holds across both backends.

---

## Init coverage

Applying the cost model to every Init constant's native profile (51,003 blocks /
51,678 constants) vs a single-leaf cap: **~99.98% of Init typechecks on Zisk.**
Exactly **12 constants** exceed a single 250 GiB leaf
— all single atomic constants (un-shardable), `hb`-dominated. Listed by name
(all are `_private` proof terms; private prefix elided):

| constant | hb | pred. steps |
|---|--:|--:|
| `Int16.instRxcHasSize_eq` | 32,843 | 10.5e9 |
| `Int64.instRxcHasSize_eq` | 32,843 | 10.5e9 |
| `Int32.instRxcHasSize_eq` | 32,843 | 10.5e9 |
| `Vector.extract_append._proof_1` | 20,309 | 7.0e9 |
| `Array.extract_append._proof_1_1` | 20,210 | 6.9e9 |
| `Char.succ?_eq` | 18,226 | 5.9e9 |
| `Char.ofOrdinal_le_of_le` | 17,877 | 5.7e9 |
| `Vector.extract_extract._proof_1` | 16,258 | 5.7e9 |
| `ISize.instRxcHasSize_eq` | 16,425 | 5.3e9 |
| `Vector.extract_append_extract._proof_1` | 13,335 | 4.7e9 |
| `Array.extract_append_extract._proof_1_1` | 13,226 | 4.7e9 |
| `Char.ofOrdinal_ordinal` | 14,136 | 4.5e9 |

Each has a workaround — a bigger box, `--skip-deps`
(subject-only), or upstream proof restructuring — so 12 is an upper bound on
truly-stuck constants. At a 200 GiB cap the list grows to 16. Estimate uses the
planner's `block_step_cost` model (`162,339·hb + 4,276·subst + 652·bytes`, the
same single source of truth the packer uses); regenerate with
`python3 ~/benchdata/prof/over_cap.py [ram_gb]`.

---

## Data

### Init shards (12) — variables summed over member constants

| shard | blocks | hb | bytes | subst | cycles |
|---|---:|---:|---:|---:|---:|
| 803 | 3 | 3,117 | 23,174 | 6,785 | 771,527,739 |
| 806 | 6 | 4,586 | 32,062 | 10,479 | 810,732,054 |
| 502 | 2 | 4,057 | 24,927 | 15,452 | 1,034,769,720 |
| 68 | 37 | 2,806 | 115,271 | 67,589 | 1,127,754,269 |
| 957 | 278 | 2,672 | 397,663 | 145,185 | 1,382,497,091 |
| 290 | 19 | 4,540 | 72,883 | 75,048 | 1,397,057,638 |
| 383 | 87 | 3,370 | 162,554 | 170,516 | 1,584,528,514 |
| 870 | 311 | 4,151 | 255,573 | 173,497 | 1,773,123,833 |
| 273 | 101 | 4,911 | 159,997 | 227,820 | 1,782,171,986 |
| 815 | 428 | 3,823 | 378,779 | 253,556 | 2,526,432,086 |
| 634 | 1 | 32,843 | 2,308 | 513 | 5,695,914,962 |
| 630 | 1 | 32,843 | 2,309 | 513 | 5,697,160,198 |

Shards 630/634 are one atomic constant each (`Int*.instRxcHasSize_eq`): tiny
`bytes`/`subst` but huge cycles, driven by `hb` (deep nat-range def-eq) — the
"expensive atomic" case (Finding 4).

### Full-closure single constants — `--consts`, diverse shapes

One library constant each, checked full-closure (the constant and its whole
dependency closure). The 35 Init constants below (over `initstd.ixe`) are shown
in full; the cross-library fit adds **19 more Init/Std** (incl. `Std.Time.*`,
`ByteSlice`) and **10 Mathlib** (`Finset.*`, `Polynomial.eval`, `Multiset.sort`,
`Nat.fib`, …, over `compilemathlib.ixe`), plus 12 small programs — 76 points
total, all measured (`~/benchdata/prof/{onlyconst,new,mathlib,smallenv}_*.tsv`).
All ran with zero failures.

| constant | shape | hb | block_bytes | subst | cycles |
|---|---|--:|--:|--:|--:|
| `Nat` | inductive type | 3 | 113 | 0 | 975,244 |
| `Eq.rec` | recursor | 5 | 206 | 197 | 2,348,520 |
| `Array.toList` | array→list | 20 | 281 | 160 | 2,580,844 |
| `Acc.rec` | accessibility recursor | 10 | 315 | 770 | 5,105,888 |
| `Sum.elim` | sum eliminator | 15 | 693 | 745 | 6,618,130 |
| `Option.bind` | monadic bind | 30 | 945 | 1,052 | 7,440,608 |
| `Prod.map` | product map | 19 | 804 | 1,170 | 8,177,456 |
| `Nat.add` | function reduction | 61 | 1,889 | 1,074 | 10,606,339 |
| `WellFounded.fix` | well-founded fixpoint | 34 | 1,108 | 2,199 | 13,415,585 |
| `List.range` | list generator | 83 | 2,727 | 1,316 | 13,666,491 |
| `List.foldr` | list fold | 79 | 2,383 | 2,026 | 16,707,100 |
| `Int.add` | integer addition | 170 | 6,034 | 3,290 | 27,635,032 |
| `BitVec.toFin` | bitvec→fin | 176 | 5,913 | 3,055 | 28,681,028 |
| `USize.toNat` | fixed-width→nat | 198 | 8,391 | 3,652 | 35,811,906 |
| `Nat.add_comm` | arithmetic theorem | 360 | 6,908 | 3,998 | 53,239,676 |
| `Nat.decEq` | decidable equality | 266 | 8,116 | 6,747 | 57,411,966 |
| `Nat.decLe` | decidable order | 709 | 21,222 | 18,105 | 143,391,161 |
| `Nat.strongRecOn` | strong recursion | 764 | 24,974 | 28,682 | 190,849,758 |
| `Int.emod` | integer mod | 1,405 | 42,899 | 34,415 | 269,380,418 |
| `Array.foldl` | array fold | 1,284 | 41,477 | 38,282 | 278,537,034 |
| `Nat.sub_le_of_le_add` | order theorem | 1,915 | 54,845 | 48,701 | 373,184,538 |
| `Int.gcd` | integer gcd | 2,158 | 65,618 | 52,973 | 409,112,011 |
| `Array.map` | array map | 2,415 | 69,838 | 54,424 | 443,199,245 |
| `Lean.Name.hash` | name hashing | 2,451 | 82,181 | 57,157 | 447,441,591 |
| `Nat.repr` | number→string | 2,658 | 91,470 | 62,863 | 498,729,913 |
| `BitVec.umod` | bitvec modulo | 2,585 | 89,060 | 71,781 | 526,467,117 |
| `String.intercalate` | string join | 3,004 | 99,770 | 73,875 | 599,428,829 |
| `Char.toLower` | char case map | 3,588 | 115,675 | 82,453 | 665,920,824 |
| `Vector.append` | vector append lemma | 6,260 | 205,557 | 231,194 | 1,614,275,115 |
| `Int.emod_emod_of_dvd` | omega theorem | 11,951 | 345,084 | 226,571 | 2,201,588,182 |
| `Fin.foldl` | finite-range fold | 24,695 | 778,754 | 536,883 | 5,110,854,190 |
| `List.mergeSort` | merge sort | 32,915 | 912,942 | 642,232 | 6,706,906,294 |
| `Array.binSearch` | binary search | 34,358 | 891,352 | 646,852 | 6,785,827,470 |
| `Array.qsort` | quicksort | 41,060 | 1,001,670 | 739,383 | 7,199,288,749 |
| `String.split` | string splitting | 39,939 | 1,141,622 | 928,723 | 8,657,387,499 |

`Vector.extract_append` is omitted: its full-closure check exceeds the executor
(the un-shardable case); subject-only it is 74,135,524 cycles.

---

## Reproduce

```bash
# profile out of circuit (per-block hb/bytes/subst + delta graph): env.ixe →
# env.ixprof, and print the kernel-work breakdown + predicted Zisk leaf cost/RAM
lake exe ix profile env.ixe

# pack the .ixprof into shards under a RAM/cycle cap (offline, no kernel re-run)
lake exe ix shard env.ixprof --max-ram 256        # or --max-cycles C / --shards N

# measure guest cycles: a shard/env, or one named constant
cargo run --release --bin zisk-host -- --execute --ixe <env.ixe> \
  [--shard-plan <plan.ixes> --only-shard K]
cargo run --release --bin zisk-host -- --execute --ixe initstd.ixe \
  --consts "Nat.add_comm" [--skip-deps]        # full-closure / subject-only

# fits
python3 ~/benchdata/prof/fit_xlib.py         # full-closure model (76 pts, Init+Std+Mathlib)
python3 ~/benchdata/prof/fit_onlyconst.py    # subject-only model
python3 ~/benchdata/prof/compare.py          # members-only vs full-closure costing
```

The cost model is the single source of truth in `crates/kernel/src/shard.rs`
(`block_step_cost`, `partition_for_cycle_cap`, `cycle_cap_for_ram`), consumed by
both the `ix profile` breakdown and the `ix shard` packer. Counters in
`profile.rs` (`bump_subst_nodes`/`bump_whnf`/`bump_def_eq`) record on every
native profiling run and compile out on the zkvm target.

---

## Caveats

- The full-closure model is n=76 across Init/Std/Mathlib (per-library MAPE
  5–8%); the shard model is still n=12 and Init-derived, so the ~190M shard
  intercept is the term most likely to
  shift on Std/Mathlib — worth re-checking there.
- RAM/prove-time models are for one GPU.
- Cycle counts are deterministic for a fixed guest ELF; the profiler counters
  compile out on the zkvm target, so the proven ELF is unaffected.
- **Regimes have distinct coefficients and don't transfer.**
  `instRxcHasSize_eq` (a single-block atomic shard) is predicted at **1.00×** by
  the *shard* model (167,900·hb); applying the *full-closure* model to it
  underpredicts ~2× — a regime mismatch, not a model failure.
- **Edge: near-pure-substitution constants.** Auto-generated `*.mk.injEq` / `.inj`
  lemmas (huge `subst`, ~zero `hb`/`nat`) are *over*predicted ~1.3–1.6× by the
  full-closure model — pure substitution is cheaper per node than the
  mixed-calibration `subst` rate. Including such exemplars in the calibration
  tightens them to ≤1.3× (safe, over-provision direction). The within-set worst
  residual is 1.27×.
- **`nat_arith` does not help.** It is near-zero across all constants (the bignum
  binop path is rarely exercised; max ≈1,600 vs `hb`/`subst` in the 10⁴–10⁵
  range), and every outlier is substitution-bound, not arithmetic-bound — so
  reduction counters (`hb`, `subst`), which are 0.98–1.0 collinear on real code,
  remain the right and sufficient variables.
