# Handoff: Aiur cost model, closure sweep, RAM-limited sharding (branch `bench-profile`)

Untracked scratch note for the agent continuing this work — delete before
merging. Rewritten 2026-07-28 after the closure-union packer fix landed and
the first Aiur shard proves succeeded.

## Branch state

Rebased on `main` @ `3312c3f` (#513 blowup-4 + 20-bit grinding regime).
Five commits, tree clean, all built (`nix develop -c lake build ix`),
clippy-clean (`cargo clippy -p ix-kernel -p ix-ffi --all-targets` in the
dev shell; repo rule: fix lints, never `#[allow]`), kernel tests green:

    f379d9ae shard: closure-union byte accounting for Aiur packing
    381f1380 profile: env-wide closure cost sweep (ix profile sweep)
    3527cc8c shard: calibrated Aiur cost model, profile/shard --backend aiur
    e5641787 profile: record memo-unique substitutions (.ixprof v2)
    0ee2c1e0 profile: per-metric block leaderboards (--top N, default 10)

Push: `git push --force-with-lease origin bench-profile` (rebase rewrote
the first commit's hash). NEVER push from an agent session — user runs it.

## What works (all validated end-to-end)

1. **`ix profile <env>.ixe [--backend all|aiur|zisk] [--top N]`** — whole-env
   kernel profile → `.ixprof` (v2: per-block hb/subst/subst_unique/whnf/
   def_eq/nat_arith + delta CSR + **reference-graph CSR**). Prints kernel
   totals, predicted Aiur single-run prove/RAM, predicted Zisk leaf, and
   per-metric top-N boards incl. "predicted Aiur prove ms (marginal)".
   Timing: Init 11 s, InitStd 20 s, Mathlib 6.7 min (all on this box).
   Old `.ixprof`s are rejected (v2) or lack the ref graph — regenerate.
2. **`ix profile sweep <env>.ixe [--prof P] [--out CSV] [--budget G]
   [--top-blocks M] [--reps K]`** — per-constant closure costing over one
   profile: CSV row per named root (closure blocks, all counters, predicted
   exec/prove time+RAM) + three reports (feasibility at budget with the
   cheapest prove-infeasible reproducers, min-root per hot block, diverse
   feature-mix representatives). Mathlib: 631,006 closures in ~15 s.
3. **`ix shard <prof>.ixprof --backend aiur --max-ram G [--out M.ixes]`** —
   RAM-budget packing with **closure-union byte accounting** (matches
   `shardCheckEnvClaim` semantics: a shard ingresses+hashes its owned
   blocks' full reference closure; frontier constants are assumptions, so
   hb/subst are owned-only). Writes the manifest + `<out>.costs.csv`
   sidecar (per-shard union_bytes/hb/subst + predictions). Reports honest
   per-block RAM floors and flags INFEASIBLE when a lone closure exceeds
   the cap. Requires a ref-graph-bearing `.ixprof`.
4. **`ix prove --ixe E.ixe --ixes M.ixes --shard K`** — per-shard STARK
   prove (also `ix check --ixes …` for check-only, `--jobs` bounds
   concurrency). **Acceptance result (Init, 24 GiB budget, 50 GB
   watchdog): shards predicted 21.3/21.6/21.5 GiB proved at
   20.9/31.7/19.3 GiB peak — 0.98×/1.46×/0.90×.** The same partition
   OOM'd under the pre-fix accounting.

## The models (crates/kernel/src/shard.rs, single source of truth)

`nlogn(x) = x·log₂(x+2)`, features are run-level aggregates; NO fft
intermediate anywhere (user directive):

    prove_s  = 1.43 + 2.38e-7·nlogn(bytes) + 9.06e-7·nlogn(subst)
    ram_gib  = 3.67 + 1.18e-6·nlogn(bytes) + 1.57e-5·nlogn(hb)
    exec_s   = 0.146 + 8.54e-8·nlogn(bytes) + 6.77e-8·nlogn(subst)
    exec_gib = 4.72 + 8.50e-8·nlogn(bytes)      (bytes-only; sole nonneg fit)
    cap      = budget × AIUR_RAM_USABLE_FRAC (0.7)

For a SHARD: bytes = closure-UNION serialized bytes; hb/subst = owned only.
For a CLOSURE (sweep/bench): all features are closure sums.

Calibration: n=13/14 bench-suite closures; features from `ix profile` per
closure (counters are regime-independent), targets from bencher.dev main @
`3312c3f` (2026-07-23/24). prove MAPE 12% (LOO 16%), RAM MAPE 15% (LOO
19%), exec RAM MAPE 6%. Cross-checks: BVDecide mutual extrapolation 530 GiB
(counters) vs 536 GiB (fft-linear); HashMap/DTreeMap out-of-sample RAM
+6%/+4%. #513 moved prove ~+25% / RAM ~+60% at identical fft — refit from
the latest bencher main report after ANY prover-params change:
`https://api.bencher.dev/v0/projects/ix/reports?branch=main&testbed=aiur-check-prove-x64-32x&per_page=1`
then `/reports/<uuid>`; per-benchmark `Prove Time` (s), `Peak RSS` (bytes),
`FFT Cost`; execute testbed likewise. Fit datasets (untracked, repo root):
`fresh_calibration.csv`, `bencher_prove_main.csv`, `bencher_exec_main.csv`.
Method: WLS with 1/y² weights + leave-one-out to guard small n; REQUIRE
non-negative coefficients (packer monotonicity) and ALWAYS keep bytes as a
feature (cross-shard duplication is pure bytes work — a bytes-free model
prices duplication at zero regardless of fit score).

## Known limits (stated, not hidden)

- **Klimbs blind spot**: no native counter tracks Aiur's big-Nat limb
  gadgets (PR 469 §5 proved `nat_arith` doesn't fix it). Closures/shards
  heavy in that family under-predict to ~0.55× (worst observed); the 0.7
  usable-frac absorbs ~1.43×. Acceptance shard 1 (1.46×) is this band.
- **Prove-TIME is CI-runner-calibrated**: ~4× under on this dev box
  (measured 20–29 s vs ~5 s predicted). RAM transfers across hosts well;
  time is advisory until a local refit.
- **Init's shard floor is ~175 GiB**: the `String.Slice.Pattern.Model.
  ForwardSliceSearcher` stack (6.4 MB, 4,341-block closure) must be fully
  ingressed by any shard containing it. Below that budget the planner
  correctly reports INFEASIBLE (best-effort shards still emitted). This
  stack is the #1 optimization target for small-box Init proving; the
  alternative is a runtime change (frontier-trusted ingress that avoids
  hashing the whole closure — soundness-sensitive, not attempted).
- `subst_unique` is recorded (`uniq subst` in the summary) but unused by
  the models — future calibration candidate.
- Board/sweep names: one representative per home block, preferring human
  names over `Ix.<64-hex>.` aux aliases.

## What's left, in priority order

1. **Widen shard-granularity calibration.** The 3 measured shard proves are
   the only shard-shaped calibration rows. Prove more shards across
   budgets/envs (each ~20–30 s; the `.costs.csv` sidecar makes
   predicted-vs-measured mechanical), refit — especially to pin the klimbs
   tail and decide whether 0.7 usable-frac can rise.
2. **Aggregation story.** Per-shard proofs + assumption roots + the agg
   tree exist in the manifest; Aiur recursive verification landed in #503.
   NOT verified: shard proofs folding into one composed proof with
   cross-shard assumptions discharged. Needed if "prove Init/Mathlib"
   means one proof rather than N independent ones.
3. **Attack the ForwardSliceSearcher floor** (or accept ≥~250 GiB boxes for
   full Init coverage). Mathlib will have its own floor — regenerate
   `Mathlib.ixprof` with the current binary (the existing one predates the
   ref graph), run `ix shard Mathlib.ixprof --backend aiur --max-ram G`,
   read `largest_block_ram`.
4. **Local prove-time refit** (advisory; sidecar predictions + measured
   walls are the dataset).
5. Optional: FM refinement post-pass for duplication. Delta-based
   cross-ingress measured 7–9%, but union-overlap packing changes the
   calculus — measure union overlap before building anything. Zisk paths
   untouched throughout; don't regress them.

## Repro / environment notes

- Build: `nix develop -c lake build ix` (cargo can't build ix-ffi outside
  the dev shell: lean-ffi bindgen needs libclang). Dev-shell builds OK to
  run solo+serial; ask before whole-flake `nix build`/`flake check`.
- Heavy runs: `.github/scripts/watchdog.sh <gb> <cmd>` (cgroup memory.max,
  OOM = SIGKILL/exit 137), sandbox off (needs systemd user bus), ≤50 GB,
  strictly serial. Peak-RSS measurement: poll `/proc/<pid>/status` VmHWM
  from OUTSIDE the watchdog scope (an in-scope poller dies with the OOM
  kill); there is no `/usr/bin/time` on NixOS.
- Artifacts (untracked): `Init.ixe`/`Init.ixprof`/`Init-sweep.csv`/
  `Init-aiur24.ixes`(+`.costs.csv`), `Mathlib.ixe`/`Mathlib.ixprof`(pre-
  ref-graph)/`Mathlib-sweep.csv` in the repo root; `InitStd.ixe`,
  `Lean.ixe` in `~/repos/ix-bench-plot-fixes`. Compile targets in
  `Benchmarks/Compile/` (`ix compile Benchmarks/Compile/CompileInit.lean
  --out Init.ixe`, 3 s; Mathlib 74 s). "Std alone" is not expressible
  (Std imports Init) — difference InitStd−Init, or filter the sweep CSV
  by namespace. Do NOT put artifacts in session tmp (`/tmp/claude-*` gets
  cleaned) — repo root or a worktree.
- Key source: shard semantics `Ix/IxVM/ClaimHarness.lean:279`
  (`shardCheckEnvClaim`); CLI `Ix/Cli/{ProfileCmd,ShardCmd,CheckCmd,
  ProveCmd}.lean`; models + packer `crates/kernel/src/shard.rs`; profile
  format `crates/kernel/src/profile.rs`; sweep + ref-graph builder + FFI
  `crates/ffi/src/kernel.rs`.
- Terminology (user rules): "parameters" = (backend × env × mode); "run" =
  one execution; never "cell". No benchmark numbers in code comments —
  numbers go in commit messages.
