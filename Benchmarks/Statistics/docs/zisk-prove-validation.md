# Validating the Zisk shard-planner cost model against real GPU proves

This checks the **actual load-bearing model** in the in-repo planner
(`crates/kernel/src/shard.rs`) against real measurements — it does **not** fit a
new function. The constants below are read straight from `shard.rs` by
`benchstats/shard_model.py`, so the plotted lines are the code's.

## The model (shard.rs, single source of truth)

| quantity | formula | shard.rs |
|---|---|---|
| guest STEPS / block | `162_339·hb + 4_276·subst + 652·bytes` | `block_step_cost` (L1633–1650) |
| per-shard STEP floor | `+ 180_000_000` | `SHARD_STEP_FLOOR` (L1638) |
| peak host RAM (GiB) | `50 + 33·B_steps` | `ram_gib_for_steps` (L1667–1676) |
| leaf prove time (s) | `54 + 158·B_steps` | `shard_prove_secs` (L1691–1696) |

`B_steps` = STEPS / 1e9. The RAM model is the *prediction*; the safety margin is
separate (`RAM_USABLE_FRAC = 0.85` in `cycle_cap_for_ram`).

## Real data (generated via the CLI, not Python)

For each single-subject env: real steps + peak RAM via the emulator, then a real
single-leaf GPU prove (RTX PRO 6000 Blackwell, 250 GB host) wrapped in
`/usr/bin/time -v` for peak RSS. The prover default is `--max-witness-stored 5`
— **the same setting the model was calibrated at**, so this is apples-to-apples.

```bash
# steps (safe, emulator RAM is setup-bound ~30 GB regardless of size):
zisk-host --execute --ixe <env>.ixe
# real leaf prove → steps, prove time; /usr/bin/time -v → peak RAM:
/usr/bin/time -v zisk-host --gpu --ixe <env>.ixe
```

`data/zisk/prove_real.csv` — **31 real leaves**, 0.055–4.69 B steps, `witness`
column = `--max-witness-stored`:

* **8 single-subject** leaves (`witness=5`): `nataddcomm` (54.6 M, 12.5 s, 40.0 GiB)
  … `natfoldsucc` (4.689 B, 809 s, **194.3 GiB** — the high-end anchor, proven
  under a watchdog). Self-contained programs, no per-shard floor/ingress.
* **6 mergesort shards** (`witness=5`, `kind=sharded`): the real planner regime —
  RAM-aware sharded via `ix shard --max-ram 130` → 6 leaves of 0.55–1.66 B, each
  carrying the 180 M floor + cross-ingress. They land on the **same** RAM/time
  envelope as the single-subject leaves (floor/ingress don't shift RAM).
* **17 leaves at `witness=10`**: 8 single-subject (re-proved, 0.055–4.69 B) +
  3 mergesort + 3 rbmap + 3 binsearch shards (0.15–1.66 B) — all clean (no OOM).

Multi-shard inputs are profiled (`ix profile`) and sharded RAM-aware
(`ix shard --max-ram`), then proved per leaf (`zisk-host --gpu --shard-plan
--only-shard k`). Also salvaged: `data/zisk/multishard_failed.csv` (see below).

## Result (`python3 -m benchstats zisk-prove-validate`)

![shard.rs model vs real GPU proves](../figures/zisk_prove_validation.png)

Over all 31 leaves: **RAM `50+33·B` R² = 0.88**, **time `54+158·B` R² = 0.95**
(single-subject leaves alone, with the 4.69 B anchor, give 0.92 / 0.98).

- **Peak RAM.** The **slope is dead-on**: single-subject envelope is
  `(194.3 − 40.0)/(4.689 − 0.055) ≈ 33.3 GiB/Bstep` vs the model's `33`. The gap
  is a constant **~12 GiB on the base** (model `50`, measured ≈ `38`) — a safe
  upper bound, ~18 % loose on the ~1 B sharded cluster, within ~5 % by 4.7 B. The
  deliberate `45+32 → 50+33` bump in `shard.rs` (after an Init shard sized for
  200 GB used 225 GB) is why the base is conservative.
- **Prove time.** The `158 s/Bstep` slope tracks closely from ~0.6 B up. The high
  MAPE is **entirely the `54 s` intercept**: a cold-start cost, but warm leaves
  prove in 12–30 s, so the model over-predicts small leaves while nailing large
  ones (4.69 B: model 795 s vs real 809 s). Wall time (incl. setup) sits between.

### `--max-witness-stored 10` adds a flat ~3 GiB, independent of leaf size

Re-proving **all 8 single-subject envs** (and 3 mergesort shards) at witness=10
raised peak RAM by a **constant ≈ 3.3 GiB** — the linear fit of the witness delta
is `Δ ≈ 3.3 + 0.0·Bsteps`, i.e. **no size dependence**. The decisive point is the
4.69 B `natfoldsucc` leaf: **194.3 GiB at w5 → 196.7 GiB at w10 (+2.4)**. The
witness queue depth is not the RAM driver — base trace memory is — so `50+33·B`
covers witness=10 within its ~12 GiB conservative base and **no recalibration is
needed**. (Leaf prove time is if anything marginally *lower* at w10 — witness
batching.) On the plot the w10 markers sit on top of the w5 ones.

### Failure modes (`multishard_failed.csv`) — library envs don't shard cleanly

Sharding the **whole initStd env** (the Vectors `initStd` target) is *not* clean:
its closure contains single atomic `Muts` blocks that can't be split:

* `hb=83063` (~13.5 B predicted steps): **crashes the prover** during EXECUTE
  (too large for one leaf — exceeds the MT-trace ceiling).
* `hb=14807` (~2.4 B predicted): EXECUTE ok, but proving **OOM'd at >235 GB** at
  witness=10 — the model predicts ~129 GB, **under-predicting ~2×** for this
  block (heartbeats badly underestimate its true trace).

So heavy *library* constants (the `.heavy` rows in `Vectors.lean`) can't be
cleanly multi-shard-proved on this box; the clean multi-shard data comes from the
baked programs (`mergesort`, `rbmap`, `binsearch`).

**Takeaway:** both load-bearing slopes (`33 GiB`, `158 s` per B-step) are
validated by real proves — across single-subject and sharded leaves, at
witness=5 and witness=10 — on the calibration hardware. The RAM base is ~12 GiB
conservative; the time intercept is a cold-start artifact; and the model
under-predicts pathological single-atomic-block shards (a planning limit, not a
slope error). `num_shards` and aggregation overhead are not separately measured.
