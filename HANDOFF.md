# Handoff: Init E2E proving — Aiur shards → SP1 → Groth16 (branch `sb/sp1-shard-agg`)

Working note for the `~/ix.e2e-bench` worktree. Delete before merging anything.
State as of 2026-07-31 ~03:30 UTC.

## Branch layout

- **This worktree** (`~/ix.e2e-bench`, branch `sb/sp1-shard-agg`): `sb/measured-ingress`
  + cherry-picked `sp1-compress` batch pipeline (tip `dbdcb68`, 100% stock SP1
  v6.3.1) + the per-shard rebudget commit.
- **Main repo** (`~/ix`, branch `sb/measured-ingress`): 29 commits, PR-ready,
  unpushed. Untouched by this work except the untracked
  `docs/prover-perf-design.md` (gained the W4 rebudget section).
- The rebudget feature belongs on `sb/measured-ingress` eventually — it is
  sharding infrastructure, independent of SP1.

## Done: full Init proven in Aiur

- **All 72 shard proofs, verified + bound, composed verdict green** (disjoint
  cover). Proof store addresses cached in `~/.ix/cache/shard-proofs/<claim_digest>`
  (one file per shard, content = proof store address). Resume is free: the
  batch campaign (`ix prove --ixe Init.ixe --ixes <manifest>`) skips cached shards.
- Manifest: `~/benchdata/init-shard-prove/Init-touch-220-r57.ixes` (72 shards =
  220 GiB-budget repair-green manifest with shard 57 rebudget-split into 3).
- Campaign cost ~2.2 h CPU clean (~2.4 min/shard avg, heaviest-first, jobs=1).

## Done: Groth16 GPU pipeline measured (2/3/4/5-shard sweep, all verified)

Full pipeline `ix compress <proof-hex>… --mode groth16` with `SP1_PROVER=cuda`:
wall ≈ **1.4 min fixed + 7.0 min/shard** (2→15:25, 3→23:56, 4→29:35, 5→36:33;
r²≈0.999). Batch size is throughput-neutral; pick 8–12 for blast radius.
Full Init ≈ **8.4 GPU-h** serial on this box (RTX PRO 6000), ~65 min on 8 GPUs.
Onchain proof: 356 B Groth16, ~270k gas, vkey `0x00be8a22…`. Artifacts + logs:
`~/benchdata/init-shard-prove/e2e-{2,3,4,5}shard-groth16.{bin,log}`.

Gotchas:
- With `SP1_PROVER=cuda` the prebuilt `sp1-gpu-server` runs the gnark tail
  internally on **CPU** (no ICICLE in the released binary), and that is the
  campaign configuration: GPU STARKs + CPU gnark tail (~36 s/batch).
- GPU gnark via ICICLE was **evaluated and rejected, no code kept**: the
  `sp1-sdk/groth16-cuda` feature works but only engages when gnark runs
  in-process (without `SP1_PROVER=cuda`), which forces the STARK stages onto
  CPU. Measured on the demo: groth16 prove 10.6 s CPU → 7.5 s ICICLE — ~3 s
  per batch, once. Making it fire alongside GPU STARKs means building
  `sp1-gpu-server` from source with `groth16-cuda` (nvcc-13.2 miscompiles the
  kernels; CUDA 12.9's CMake breaks on nvToolsExt) — not worth ~3 s. The
  ICICLE libraries remain installed at `/usr/local/lib{,/backend}` if ever
  wanted (Blackwell NTT untuned: ingonyama-zk/icicle#1046, conservative skew).
- Host RAM per SP1 stream: <40 GB measured at 2 shards; growth with batch size
  unmeasured (bounded ≤ ~45 GB/shard linear by the 5-shard run completing).
  Sample RSS on the first full-size batch before fixing streams-per-box.

## Done: per-shard rebudget (`ix shard --rebudget`)

Shard 54 of the 250-budget manifest needed >248 GiB (box has 249); shard 57 of
the 220 manifest needed ~248 vs 148 predicted. Global re-sharding invalidates
every cached proof, so:

```
ix shard --rebudget K --manifest OLD.ixes --max-ram G --backend aiur \
  --out NEW.ixes <profile>.ixprof
```

splits ONLY shard K (packed at the child budget in the original cut-coherent
order); every other shard is copied **verbatim** → cached claims/proofs stay
valid (verified: costs-CSV rows byte-identical). First child keeps id K, rest
append. Children inherit the parent's escalated FULL ingress via
`ShardPromotion.extra_full` — CRITICAL: hand-unioning the promoted blocks
without the promotion mechanism drops their reference frontiers
(`invalid IO key: channel 2` on every child; cost one debug round).

## RAM-model finding (controlled measurement, 2026-07-31)

Escalation-coupled amplification confirmed:
- def_eq-heavy alone (shard 59: 354k def_eq, 0 escalations): 1.13× predicted — benign.
- def_eq-heavy + escalated FULLs (shard 57: 440k, 22 promotions): ≥1.62× — OOM.
- Child holding the hot blocks: ~1.6×; other children ~1.15×.

Mechanism: the Aiur replay reduces through promoted blocks along def-eq paths
the Rust recording shortcut — work invisible to the recorded-hb RAM model.
**Queued fix**: repair driver re-prices escalated shards ×1.5–1.7 (or adds a
def_eq×escalation term) so infeasible shards flag before proving. Also keep
pack budget ≤ box − 30 GiB.

## Next steps

1. **Groth16 batch campaign** over the 72 cached proofs (user-triggered):
   ~7 batches of 10–11, `ix compress … --mode groth16`, serially on this box
   (~8.4 GPU-h) or fanned out. Proof hexes: `cat ~/.ix/cache/shard-proofs/*`.
2. Optional single-final-proof topology: one `verify_sp1_proof` top-layer
   aggregation of the batch proofs (UNMEASURED — pilot a 2-proof top layer
   first), then one groth16 tail.
3. Escalation re-pricing in the repair driver (see above).
4. Upstream `--rebudget` to `sb/measured-ingress`.
5. Never run two provers concurrently (240 GB watchdog scripts in the session
   scratchpad; box OOM'd twice tonight without one).
