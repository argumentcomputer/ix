# Training data: premise selection (Tier 1)

A premise-selection dataset extracted from compiled Lean declarations, keyed by Ixon content
address, curated by Lean functions, committed by a Merkle root, and used to train a typed
relevance model with `IxAICore.train`.

## Pipeline

| Step | Where | What |
|---|---|---|
| Scope | `IxAIData/Pipeline.lean` (`scopes`) | Modules imported, item module prefix, held-out modules. |
| Extract | `ix/premises/extract.sh`, `ix/premises/Extract.lean`, `ix/premises/lean341.sh` | Lean 4.34.1 imports the scope from the Mathlib build in `~/repos/ix.ixai-aiur` (private level, so proofs are present) and writes `decls.tsv`: modules and imports, every library theorem's statement shape (constant counts, node-kind counts, the head constants of the conclusion and of its last two arguments, leading binders and non-dependent hypotheses), and per scope theorem its proof-term constants, transitive axioms and direct native references. |
| Address | same script | `ix compile --consts-file seeds.txt` (every library theorem plus its closure) gives `scope.ixe` and `report.json`; `ix diff empty.ixe scope.ixe --verbose`, against a tiny environment compiled with `--anon` (no names), lists every named constant with its address (`names.tsv`). |
| Curate | `IxAIData/Rules.lean` | `acceptance`, `premiseRule`, `dedup` (`dedup_nodup`), `split` (`split_disjoint`, `split_addr_disjoint`), run by `IxAIData.curate` (`Dataset.lean`). `splitBy` generalises the split to any item predicate (`splitBy_disjoint`, `splitBy_addr_disjoint`; `split_eq_splitBy`). These list forms are the specifications; the pipeline runs hash-set forms proved equal to them (`dedupFast_eq`, `splitFast_eq`, `splitByFast_eq`, `disjointFast_eq`, `premiseRuleSet_eq`; `curate_spec` states that `curate` computes the specifications), so curation is near-linear. |
| Splits | `IxAIData/Pipeline.lean` (`splitOf`) | `module`: test = the theorems of `Mathlib.Order.Basic` and `Mathlib.Logic.Function.Iterate`, validation = `Mathlib.Logic.Relation` (`mathlib-full`: the modules whose name's FNV-1a is 0 mod 50, validation 1 mod 50; `Scope.sample`). `time`: test = the last fifth of every module's theorems by declaration order (`heldOutLate 1 5`); training = the earlier theorems of all modules that use no test theorem as a premise; validation = the same rule applied to training. Both are checked with `disjoint` on every run. |
| Features (MLP) | `IxAIData/Relevance.lean` | `stmtFeatures`: hashed constant counts bucketed by address bytes and node-kind counts. `pairFeatures`: optionally both statements' features, per-bucket overlap, and a `PairContext` (train-set prior, shared constant addresses, shared rare ones, same module, declaration distance). |
| Features (bilinear) | `IxAIData/Scorer.lean` | `sparseFeatures`: bias, 512 constant buckets by address, 3 × 128 head-constant buckets (conclusion, last two arguments), one-hot binder and hypothesis counts, log-scale node-kind counts. `pairContext`: shared constants (all, rare), IDF-weighted overlap and its share of each statement's IDF mass, head matches, same module and declaration distance, train-set prior (leave-one-out in training: a gold premise's count excludes the training theorem's own proof), premise size, the IDF baseline score. IDF is `⌊4 log₂ (N / df)⌋` over library statements. These are from addresses, so alpha- and rename-invariant. Name features (`nameToks`, `nameContext`): a declaration name is split into namespace components and the `_`-separated tokens of its last component, lowercased, primes dropped, `hAdd`-style `h` prefixes dropped, numeric and `_`-prefixed components skipped, each token hashed by 64-bit FNV-1a; `sparseFeatures` adds 256 name-token buckets; `pairContext` adds shared tokens (log count, Jaccard in sixteenths), shared namespace-prefix length, the IDF-weighted overlap of the premise's name tokens with the theorem's name tokens and the names of its statement's constants (absolute and as a share), whether the premise's last component is covered by the theorem's name or by its name and constants, and `nameScore` (the name analogue of `idfScore`, token IDF over library names). v3 pair features: neighbour votes (summed similarity, share of the largest vote, neighbour count, top-vote flag) from the `knn` training theorems most similar to the theorem (`similarity`: IDF-weighted Jaccard of constants plus that of name tokens), co-usage with the theorem's `coUse` IDF top candidates, the premise's argument heads matching the theorem's, its conclusion head among the theorem's argument heads, its hypothesis count, and the theorem's conclusion head among its constants. Votes, co-usage and the prior come from `Stats.build`, which for a training theorem leaves out its own proof (`LeaveOut.self`), its whole module (`.module`) or itself and later theorems of its module (`.later`); it looks references up through inverted indices (per module, constant, name token, premise; postings over `postingCap` propose no neighbours). Names come from `decls.tsv` (`lib` names) and `names.tsv` (each constant address's first name); they are metadata beside the addresses, so they change no address, but these features are not rename-invariant. |
| Commit | `IxAIData/Pipeline.lean` | `.truthmines/datasets/SCOPE.items.tsv` and the manifest `.truthmines/datasets/SCOPE.json` (source, environment root, policy, split, counts, roots, results). |
| Train (bilinear, default) | `IxAIData.trainScorer` | `s(x, p) = φ(x)ᵀ Eₛᵀ Eₚ ψ(p) + wᵀ c(x, p)` in `Fx16` (16 fractional bits, `IxAIData/Fx16.lean`), dim 16; either a pairwise hinge loss over (gold, negative) triples or a listwise softmax loss over each gold premise and the theorem's negatives (`Loss`; softmax through `exp2Neg`, a fixed cubic for `2^(−y)`, each probability-activation product rounded once), with hard negatives per theorem drawn from the highest by IDF overlap, the gold premises' modules, and all accessible theorems (mix chosen per split); optionally `residual`, which freezes the IDF feature's weight so only a residual over IDF is learned. Fixed shuffle schedule, exact batch gradients rounded once with `lr / batch` folded into one division (`Fx16.step`), every value and accumulation checked against `Bounds` (2^27 values, 2^55 accumulators); the IDF feature's weight starts at 1. Optional linear learning-rate decay (`decay`), update rounding to nearest (`nearest`), seed ensembles (`ensemble`). The v3 grid (`scorerGrid`, 48 configs per split): softmax with decay; negative mix (0 IDF + 4 module + 16 random, or 0 + 12 + 8), learning rate 4096 or 8192, residual or not, no votes or 8 neighbours with leave-module statistics, epochs 4, 8, 12; chosen by validation MRR, then retrained on the whole training split. `--grid NAME` runs the other grids of `namedGrid` (`v2`: the v2 grid of 192 configs; `stats`, `co`, `hard`, `schedule`, `diag`, `ens`, `ensd`: the v3 experiments), each logging validation full-ranking and IDF-top-30 reranking metrics. |
| Train (MLP, `--scorer mlp`) | `IxAIData.spec`, `IxAICore.train` | One `relevant : Bool` question over pairs: proof premises as positives, ReProver-style hard negatives (accessible, unused; half from the modules of the proof's premises). The featurizer and config are chosen from `grid` by R@10 on a validation module carved out of the training split, then the model is retrained on the whole training split. |
| Evaluate | `IxAIData.evalRanking` | Every accessible library theorem (imported, or earlier in the same module) is a candidate for each held-out theorem; micro and macro recall@1/5/10 and MRR of the first gold premise. Baselines: frequency (training-set use count), IDF (`idfScore`: the share of the premise's IDF mass the theorem covers, plus the overlap) and name-IDF (`nameRankScore`: `nameScore`, ties broken by `idfScore`). The MLP is ranked through a split scorer that is exactly `Model.outputs` (`fastScore_agrees`, checked each run). |

Commands (`mathlib-full`: `ixai premises run mathlib-full` curates, commits and splits; `ixai
bench mathlib-full module|time|rerank theorem` trains and evaluates): `ix/heavy.sh timeout 1800 .lake/build/bin/ixai premises extract SCOPE`, then
`ix/heavy.sh timeout 1800 .lake/build/bin/ixai premises run SCOPE [--scorer bilinear|mlp]
[--split module|time|both]` (defaults: bilinear, both).

## Definitions

- Item: a theorem of a module under the scope prefix, without an internal name; identified by the
  Ixon address of the theorem constant (type, proof and universe parameters, names stripped).
- Library: every theorem outside `Init`, `Std` and `Lean` in the environment.
- Premises: library theorems in the proof term, other than the theorem itself.
- Accessible: declared in a transitively imported module, or earlier in the same module.
- Dataset root: `merkleRootV2` of the sorted item addresses. Records root: `merkleRootV2` of
  `digestOf "premises/item" (address, module, premises, split)` in item order. `merkleRootV2`
  hashes the leaf count into the root (`IxAICommon/Merkle.lean`, `docs/verification.md`). Roots recorded
  before 2026-11-19 used `merkleRootV1`, which does not bind the count; the manifests keep them
  under `rootsV1`, recomputed from the same leaves, only to match older records.
- Acceptance refuses an item any of whose proof constants or axioms the extraction cannot address
  (`Refusal.unresolvedName`, `accepted_resolved`, `curate_spec`); no item is accepted with a
  shortened list. On `order-basic` and `mathlib-full` no name is unaddressed, so the counts are
  unchanged (re-curated 2026-11-19: 0 refused for an unresolved name).

## Datasets

| Scope | Modules | `lib` / `item` / `mod` rows | Names (`names.tsv`) | Status |
|---|---|---|---|---|
| `order-basic` | `Mathlib.Order.Basic`, `Mathlib.Logic.Relation`, `Mathlib.Logic.Function.Iterate` and imports | 1,858 / 1,595 / 1,365 | 16,649 | in `scopes`; curated, trained, evaluated |
| `mathlib-full` | all of `Mathlib` (`import Mathlib`) | 270,304 / 267,064 / 10,744 | 567,373 | in `scopes`; curated, split; trained by `ixai bench mathlib-full` |

`mathlib-full` (`.truthmines/datasets/mathlib-full/`, 2026-11-19) is the same extraction route
over the whole library: `ix/heavy.sh ix/premises/extract.sh mathlib-full Mathlib Mathlib`.
Source: Mathlib `d13f23b7` (v4.34.1), Lean 4.34.1, the Mathlib build in `~/repos/ix.ixai-aiur`
(fully up to date, nothing rebuilt), Ix `de597000` (`ix.ci-merge-tests`). Items are every
non-internal theorem of a module under `Mathlib` (8,530 modules); the library also contains
Batteries, Aesop, Qq, Plausible, ProofWidgets and ImportGraph theorems. Cost: extract 239 s,
`ix compile --consts-file` 444 s (562,311 seeds, 507,326 unique addresses, `scope.ixe` 1.9 GB,
`root dbc31eb9…`), names 12 s; 11 min 34 s wall, 57 GB peak RSS. BLAKE3 of every file is in
`blake3.txt` (`decls.tsv` `aa2147e3…`, `names.tsv` `89bebb19…`).

Checks: `readExtraction` loads it in 128 s (interpreted), with 0 unaddressed names. Every name in
`names.tsv` has the same address as in the whole-environment store compile
(`.truthmines/store/mathlib-d13f23b`, 567,373 of 567,373) and as in `order-basic` (16,649 of
16,649), so addresses are stable across scopes and compiles. `curate` on the first 5,000 items:
4,970 accepted (30 refused for a native reference), 4,657 after dedup, 2,779 with premises; on
the first 40,000: 39,456 accepted, 37,372 after dedup, 26,877 with premises. (Dry run: `.toolchain/bin/lake env lean --run ix/premises/Dry.lean
.truthmines/datasets/mathlib-full LIMIT TEST-MODULE…`, which runs `readExtraction`, `policyOf`,
then `curate` on the first LIMIT items.)

Curation (`ixai premises run mathlib-full`, which for this `large` scope curates, commits and
splits without training; compiled, 2026-11-19): 262,031 accepted (5,033 refused for a native
reference), 256,428 after dedup, 195,659 with premises; read and curate 28 s, everything
including the commit and both splits 43 s, 1.6 GB peak RSS (the list forms, interpreted, took
454 s on 40,000 items and extrapolated to about 5.6 h). Dataset root `2bdf59aa…`, records root
`1ac721e3…` (`merkleRootV2`; the version 1 roots of the same leaves, `5c110564…` and `c9bd3dfa…`,
are the ones recorded before 2026-11-19), `mathlib-full.items.tsv` BLAKE3 `0d97a979…`; manifest
`mathlib-full.json`.

| Split | Train | Test | Dropped (uses a test theorem) | Fit / validation |
|---|---|---|---|---|
| module (168 test modules, FNV-1a mod 50) | 184,881 | 3,445 | 7,333 | 178,038 / 3,399 |
| time (last fifth of every module) | 95,627 | 36,033 | 63,999 | 62,730 / 16,259 |

Both splits and both fit/validation splits are checked disjoint. On `order-basic` the hash-set
forms reproduce the dataset exactly (root `9481caa7…` in version 1, `a24c0fb8…` in version 2;
items BLAKE3 `638b2e4f…`) and `ixai bench
small` gives the same results file (`dea98701…`).

Training and evaluation at this size run in `ixai bench mathlib-full module|time|rerank RULE`
(`IxAIBench/Large.lean`; results in `plan.md`), not in `ixai premises run`. What changed for it,
none of which changes an `order-basic` result: negatives are drawn from a `Pool` (a theorem's
import ranges and earlier same-module theorems, indexed by binary search; `poolsAgree` checks it
against `candidates` every run) instead of a pass over the library; epochs are shuffled by
`shuffleArr` (`shuffleArr_eq`: the same swaps as the quadratic list `shuffle`); statistics are
built in parallel, their postings accumulate as lists, and postings over `postingCap` (256 here,
4,096 on `order-basic`) propose no neighbours; rankings are measured without sorting
(`ItemRank.ofOrder`, checked against the sorted ranking on the `order-basic` time split). Nothing
in the features or statistics is all-pairs: neighbour search goes through the per-constant and
per-token postings, the prior and co-usage through per-premise ones.

## Truth Mines store (`.truthmines/store/`)

These are Ix compiles of whole libraries, which future datasets can draw from. `store/index.tsv` lists
each one's scope, constant count, unique addresses, env root, `.ixe` size and BLAKE3, compile wall
time and peak RSS. Each directory has `report.json`, `compile.log`, `source.txt` (pins and patches),
and for Mathlib a `manifest.json`, `names.tsv` (790,175 names) and `check/` (IxC run).

| Store | Scope | Constants | Addresses | `.ixe` | Wall |
|---|---|---|---|---|---|
| `mathlib-d13f23b` | `import Mathlib`, whole env (core, Batteries, Aesop, Qq, Plausible, ProofWidgets, LeanSearchClient, ImportGraph, Mathlib) | 783,115 | 689,237 | 2.35 GB | 6:50 |
| `core-v4.34.1` | `import Init Std Lean` (includes `Std.Sat`, `Std.Tactic.BVDecide`) | 208,024 | 175,972 | 0.40 GB | 1:09 |
| `flt-v4.34.0` | FLT `v4.34.0`, `--module FLT,FermatsLastTheorem` plus closure | 150,259 | 137,038 | 0.47 GB | 1:27 |
| `cslib-v4.34.0` | CSLib `v4.34.0`, `--module Cslib` plus closure | 76,255 | 70,134 | 0.15 GB | 0:31 |
| `physlean-v4.34.1` | PhysLean `v4.34.1`, `--module Physlib,QuantumInfo` plus closure | 165,857 | 147,553 | 0.55 GB | 2:09 |

FLT and CSLib pin Mathlib `5ed29652` (v4.34.0), one toolchain-bump commit before `d13f23b7`, and
were built against `d13f23b7`. PhysLean pins `d13f23b7` itself; its `doc-gen4` requirement was
dropped because nothing imports it. The build workspaces were scratch copies and are not kept.
Not done: Carleson (only a `v4.34.0-rc2` tag), SampCert and Cedar (no 4.34 tags), formal-conjectures
(latest tag 4.33.1), and Ix's own 78-member TruthMines catalog (`lake exe truthmines build` in
`ix.ci-merge-tests`), which pins Mathlib `db584cd6` (v4.33.0) and would need a cold build.
