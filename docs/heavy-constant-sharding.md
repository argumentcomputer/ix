# Heavy constants: closure-shard proving

Some constants cannot be proved as a single claim on any reasonable
machine. `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual`
(the ~18B-step bitblast mutual block, 5659 constants in closure) is the
canonical example: its standalone prove measured **473.5 GiB peak** on a
495 GB box and OOM'd the 128 GB CI runner outright. This document
describes why, and the closure-shard strategy that makes such constants
provable at any RAM budget — measured at **no cost in wall clock or
total compute**.

## Why a standalone prove is the most expensive shape

A standalone claim (`Claim.check addr none`) carries **no assumptions**:
the kernel must re-derive the constant's entire transitive dependency
spine in-circuit — every definitional unfolding and def-eq down to the
`Nat` primitives. Nothing is shared with any other proof.

The env partition proves the same constant differently. A shard's
`CheckEnv` claim has a **thin frontier**: dependencies outside the shard
are *assumed* — named by content address and committed in a Merkle tree
(a few blake3 rows each) — not re-checked. Other shards' proofs cover
them, and the composed verdict glues the partition through the coverage
gate (every block owned exactly once, assumption roots matching).

Measured consequence: bitblast's standalone closure record costs more
than an *entire InitStd env shard* containing bitblast **plus 6655
neighboring blocks** (473.5 GiB / 5:43 standalone, vs 348.1 GiB / 3:13
for the whole shard). Hashing a frontier entry costs a few circuit rows;
re-deriving its body costs its whole checking cone.

## The strategy: shard the closure itself

Make the closure its own mini-env and partition *it*:

```bash
ix shard extract env.ixe --consts Foo.bar --out foo.ixe   # closure → standalone env
ix shard foo.ixe --max-ram 100 --out foo.ixes             # measured union-pricing cut
ix prove --ixe foo.ixe --ixes foo.ixes                    # prove ALL shards
```

The partition's thin frontiers are *internal to the closure*, so proving
every shard yields the same unconditional verdict as the standalone
claim — at per-shard RAM chosen by `--max-ram`. The all-shards prove
shares one env load across shards, verifies each proof and binds it to
its reconstructed claim, and persists progress in
`~/.ix/cache/shard-proofs/` keyed by claim digest — a killed run
resumes, and a repacked manifest re-proves only shards that changed.
`--consts` takes several names (their union closure extracts together);
a mutual-block member extracts its whole block; `--max-ram` defaults to
detected system RAM.

## Measured: bitblast, three ways (495 GB box, 64 cores)

| Prove             | Wall       | Total compute (exec+STARK) | Peak RAM      | Proofs      |
| ----------------- | ---------- | -------------------------- | ------------- | ----------- |
| Standalone        | 5:43       | 341.8 s                    | **473.5 GiB** | 1 × 23.5 MB |
| 2 shards (@480)   | **4:46**   | **284.0 s**                | 325.8 GiB     | 2 × ~24 MB  |
| 9 shards (@108)   | 5:40       | 333.5 s                    | **83.2 GiB**  | 9 × ~22 MB  |

| Execute           | Total kernel time | Peak RAM |
| ----------------- | ----------------- | -------- |
| Standalone        | 70.4 s            | 25.1 GiB |
| 2 shards (@480)   | 69.6 s            | 19.0 GiB |
| 9 shards (@108)   | 70.9 s            | 8.0 GiB  |

Two effects cancel to make splitting free (or better):

- **Frontier tax**: each shard re-derives frontier-adjacent context its
  claim assumes was elsewhere — total work rises with shard count.
- **Padding savings**: trace heights commit at `next_power_of_two`, so
  several short records often pad to lower power-of-two boundaries than
  one tall record — total work *falls* with shard count.

At 9 shards these wash (−2% net); at 2 shards padding wins outright
(−17% net, and less wall than standalone). RAM tracks the budget almost
linearly: 473 → 326 → 83 GiB.

Serial wall is the pessimistic case. The shards are independent proofs:
a fleet of small boxes (or `ix prove --jobs N` on one big box) proves
them concurrently, collapsing wall toward the slowest single shard
(~42 s here). The standalone prove has no such option — it is one
indivisible 473 GiB job. Closure-sharding converts a RAM-bound serial
prove into parallelizable units.

## CI integration

`ix bench run --backend aiur` routes **heavy-tier** `Vectors.csv`
constants through this pipeline automatically (`cutAiurClosureShards`:
extract → measured scan at the watchdog ceiling → one
`check`/`prove --shard K` spawn per shard). Each shard reports a
`<name>/shard-K` sub-row; the parent row aggregates (summed time — the
serial cost — max peak-rss, shard count, the manifest's total measured
fft) and lands only when every shard is green. Light-tier constants keep
the single-leaf spawn: cheap closures gain nothing from partition
overhead.

At the CI runner class (measured at a 108 GiB ceiling) bitblast proves
in 9 shards, 83.2 GiB peak, ~5.7 min serial — inside a 128 GB runner
with margin. Note `(bitblast, aiur, prove)` remains in
`benchExclusions` until a scheduled CI row is wanted; an explicit
`--consts` request always runs.

## Caveats

- **N proofs, not one.** The composed verdict is sound, but "a proof of
  Foo.bar" is a set of shard proofs until recursive aggregation lands
  (9 × ~22 MB vs 1 × 23.5 MB at the fine split).
- The bench cache (`aiurshards-<env>/<slug>.{ixe,ixes}`) is keyed by
  constant only, not budget: re-cutting at a different ceiling requires
  deleting the stale `.ixes` (the extracted `.ixe` is budget-independent
  and stays). The raw CLI has no such trap — outputs are named
  explicitly.
- A closure that fits the budget in one shard degenerates to exactly the
  standalone prove; there is no penalty for trying the pipeline first.
