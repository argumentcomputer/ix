# Sharing corpus measurements on Mathlib

This document is workstream W5 of [`sharing-minimum.md`](sharing-minimum.md). It reruns the corpus harness
`Benchmarks/SharingStudy.lean` (`lake exe sharing-study`) on a Mathlib corpus instead of `Init`. The harness is the
merged version at `5f284b7a`. The Init numbers quoted for comparison come from
[`sharing-minimum-measurements.md`](sharing-minimum-measurements.md) (the eighth W3 run). Like that document,
this one reports measurements and does not choose a design.

The merged harness has eight measurements:

- P1.5 statistics;
- the production rebuild check;
- MSS (maximal structural sharing);
- the uniform-width classification and its components;
- the reference widths of the stored encoding;
- the Share-width schemes A–G.

It does **not** call the exact uniform or tiered optimizers (`optimizeSharingUniform`, `canonicalSharingTiered`).
Their results are therefore not measured here.

## Corpus

- **Command:** `lake exe ix compile Benchmarks/Compile/CompileMathlib.lean --out <scratchpad>/mathlib.ixe`, run
  from the worktree root (exact invocation under Reproduction). It exited 0. The dependencies went into the
  untracked `Benchmarks/Compile/.lake`, and `git status` afterwards showed no tracked or unignored changes.
  - `CompileMathlib.lean` is `import Mathlib`. It is a classic (non-`module`) file, so the compiled scope is the
    whole import environment (`Ix.EnvScope.defaultConstList`). That is the Lean core libraries, Mathlib and Mathlib's
    dependencies.
  - The other packages pinned in `Benchmarks/Compile/lakefile.toml` (FLT, TorchLean, TauCeti, …) were cloned during
    dependency resolution but are not imported by this file.
- **Output:** `mathlib.ixe`, **3,343,271,273 bytes** (Ixon format version 3).
  - `ix compile` printed `Total constants: 771129`. That is the number of Lean constants requested.
  - The compile report gives 778,344 named entries, 679,499 unique anonymous constants and **0 ungrounded**. The
    consts Merkle root is `0d7113f779cebbeda85886afe548433263db8ec51e9e5eb8e726055918ef5d23`.
  - The harness loads 679,499 stored constants (distinct addresses) and 778,344 names.
- **Wall time:** 7 min 29 s end to end, from GNU `time -v`.
  - That includes resolving and cloning the dependencies, building and running `lake exe cache get`, the
    `lake build CompileMathlib` replay and elaboration of the import environment.
  - The compile itself (source preparation, Rust compile and write) printed **152.42 s**.
  - The Mathlib cache needed no download: `Decompressing 8689 already-cached file(s)`, `No files to download`.
- **Peak memory:** GNU `time` maximum resident set size 19,107,692 kB. The `--json` tree-RSS sampler reported
  19,565,625,344 bytes, the same 18.2 GiB.
- **Relation to Init:** the corpus contains the Init corpus.
  - Matching rows on the 16-hex-digit address prefix in the two CSVs, 56,621 of the 56,622 `init.ixe` rows are rows
    of `mathlib.ixe`.
  - The missing row is `main`, the one-line program that `Benchmarks/CompileInit.lean` defines itself.
  - On the 55,385 shared rooted constants, the Mathlib run reproduces the Init MSS results: 50,173 smaller, 4,993
    equal (Init's 4,994 include `main`) and 219 larger.
  - So every Mathlib total below includes Init. Where useful, the 607,869 rooted constants that are **not** in
    `init.ixe` are reported separately.

## Headline: P1.5 distributions

All 679,499 stored constants were processed. None was skipped. 663,254 have at least one expression root (Init:
55,386 of 56,622). Values are over rooted constants. Each cell gives Init / Mathlib.

| | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| distinct subterms `N` | 1 / 1 | 86 / **147** | 470 / **692** | 2,015 / **3,052** | 27,628 / **95,110** | 215.50 / **329.91** |
| candidates after R1+R2 (`occ ≥ 2`, size > 1) | 0 / 0 | 34 / **69** | 232 / **432** | 1,187 / **2,029** | 22,458 / **81,833** | 109.96 / **196.76** |
| candidates with size > 3 | 0 / 0 | 25 / **56** | 193 / **390** | 1,113 / **1,941** | 22,224 / **81,726** | 94.42 / **177.67** |
| current heuristic table size | 0 / 0 | 26 / **58** | 203 / **376** | 1,096 / **1,901** | 22,088 / **81,565** | 96.21 / **177.14** |
| stored bytes (`rawBytes.size`) | 9 / 9 | 693 / **1,112** | 3,081 / **4,510** | 11,329 / **18,597** | 170,285 / **608,188** | 1,447.33 / **2,213.75** |
| MSS table size (`deg ≥ 2`, size > 1) | 0 / 0 | 12 / **20** | 102 / **122** | 437 / **541** | 5,146 / **21,461** | 42.35 / **54.57** |
| max telescope length | 0 / 0 | 6 / **8** | 10 / **15** | 17 / **27** | 95 / **112** | 6.59 / **8.82** |

**Candidate counts (R1+R2, `occ`-based), constants with at least one root:**

| candidates | Init | share | Mathlib | share |
|---|---:|---:|---:|---:|
| = 0 | 554 | 1.0% | 4,886 | 0.7% |
| ≤ 8 | 9,532 | 17.2% | 67,177 | **10.1%** |
| ≤ 16 | 16,600 | 30.0% | 121,321 | 18.3% |
| ≤ 32 | 26,799 | 48.4% | 206,933 | 31.2% |
| ≤ 64 | 37,298 | 67.3% | 318,883 | 48.1% |
| ≤ 128 | 45,372 | 81.9% | 439,602 | 66.3% |
| ≤ 256 | 50,438 | 91.1% | 542,987 | 81.9% |
| ≤ 1,024 | 54,673 | 98.7% | 642,850 | 96.9% |
| > 1,024 | 713 | 1.3% | 20,404 | 3.1% |
| > 4,096 | 80 | | 1,689 | |
| > 16,384 | 6 | | 66 | |
| > 65,536 | 0 | | 1 | |

- The rows "= 0", "≤ 256", "≤ 1,024" and "> 1,024" and the rows below them come from the CSVs. The rest are in the
  harness output.
- With the size > 3 cutoff instead: 15.1% of Mathlib's rooted constants are ≤ 8 and 29.8% (197,576) are above 128.
- **Two candidate notions.** The `occ`-based P1.5 count is far larger than the compact-indegree set (`deg ≥ 2`,
  the MSS stored set and the candidates of the uniform classification).
  - For the constant with the most `occ`-based candidates (81,833), the `deg`-based set has 21,461 members.
  - Over all rooted Mathlib constants the `deg`-based set totals 36,191,166 against 130,502,728 `occ`-based
    candidates.
- **Totals:**
  - Stored bytes are 1,468,890,902 over all rows. Of these, `defn`s hold 1,457,076,542 and 1,468,281,356 belong to
    rooted constants.
  - The heuristic's stored bytes exceed the unshared encoding for **20,237** rooted constants (Init: 600).
  - The aggregate unshared size (214,351,802,561,585 bytes) is dominated by a few compositional sizes and is not
    meaningful as a total (see "Limits and coverage").
- **Longest telescopes:**
  - App 106 (`Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_6`);
  - Lam 112 and All 106 (the `muts` row `Ix.54eed55d….Lean.Meta.Grind.Arith.Cutsat.DiseqCnstr.rec`, a block of 21
    recursors).

### Ten constants with the most candidates

| # | constant | kind | `N` | candidates (`occ`) | heuristic table | stored B | MSS table (`deg`) | MSS B | unshared B |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 95,110 | 81,833 | 81,565 | 608,188 | 21,461 | 349,429 | 1,406,312,108 |
| 2 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | defn | 70,414 | 61,641 | 61,496 | 447,246 | 11,700 | 273,355 | 87,682,564 |
| 3 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 78,913 | 59,202 | 58,798 | 471,381 | 13,054 | 298,739 | 41,940,708 |
| 4 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 66,025 | 52,066 | 51,767 | 398,085 | 10,555 | 239,810 | 82,279,088 |
| 5 | `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` | defn | 53,511 | 44,632 | 44,492 | 336,490 | 12,056 | 206,097 | 5,917,704,097 |
| 6 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 64,047 | 41,872 | 41,529 | 350,617 | 8,745 | 213,303 | 80,464,470 |
| 7 | `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 43,441 | 38,789 | 38,598 | 269,209 | 8,957 | 153,471 | 7,349,541,595,358 |
| 8 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 53,222 | 38,483 | 38,220 | 307,182 | 7,317 | 179,803 | 61,675,147 |
| 9 | `WeierstrassCurve.addSubMapCoeff_condition` | defn | 42,875 | 35,702 | 35,499 | 272,192 | 8,048 | 169,951 | 73,921,037 |
| 10 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 44,737 | 35,231 | 34,940 | 270,991 | 6,866 | 168,437 | 27,374,524 |

All ten are `defn`s. Init's ten had 9,614–22,458 candidates. Mathlib's have 35,231–81,833 candidates and stored
sizes of 271–608 KB. The MSS columns come from the CSV.

## Verification (rebuild mismatches and other checks)

- **Production rebuild:** **0 mismatches out of 679,499** (Init: 0 of 56,622).
  - For every constant the harness expanded the stored table and recovered the roots with
    `Ix.CompileM.constantInfoRootExprs`.
  - It then rebuilt the constant with `Ix.CompileM.buildConstantWithSharing` (Lean's heuristic) and compared
    `serConstant` byte for byte with `rawBytes`.
  - The corpus was written by the Rust compiler, so this also shows that Lean's heuristic reproduces Rust's bytes on
    the whole Mathlib import environment.
- **Decode/encode roundtrip:** 0 differences.
- **Unshared size:**
  - Compositional vs serialized: 678,880 equal, **0** different.
  - 619 not serialized, because their unshared roots exceed `--validate-max` = 16 MiB.
- **`occ` vs brute-force tree walk:**
  - 648,450 equal, **0** different.
  - 31,049 not walked, because their unshared roots exceed `--occ-check-max` = 64 KiB.
- **MSS:**
  - Built for all 679,499 constants. Each was decoded, re-encoded byte-identically and expanded, and its roots
    compared for exact structural equality with the original expanded roots: 679,499 ok, **0** failed.
  - The plan §2 witnesses gave 17 / 46 / 25 bytes as expected.
  - The three negative controls behaved as expected.
- **Uniform-width classification:**
  - 0 classification errors; no candidate met both certain conditions and none had `payloadMin > payloadMax`, for any
    `w`.
  - The fast component computation agrees with the literal brute force on all 623,572 rooted constants with
    ≤ 1,000 DAG nodes, with 0 differences for each `w`. 39,682 were not checked (more than 1,000 nodes).
- **Share counts:**
  - The Share nodes in the MSS encoding equal `Σ deg` over the MSS entries for all 663,254 rooted constants.
  - The scheme E, F and G index buckets sum to the scheme A count for all of them.
- **Exit status:** the harness exited 0. Its exit status is nonzero if any of the checks above fails or any constant
  is skipped.

## MSS vs heuristic vs unshared

Over rooted constants. Byte counts are exact serialized lengths.

| encoding | Init total bytes | Init vs heuristic | Mathlib total bytes | Mathlib vs heuristic |
|---|---:|---:|---:|---:|
| heuristic (stored `rawBytes`) | 80,161,846 | | 1,468,281,356 | |
| MSS | 68,547,873 | −11,613,973 (−14.5%) | 1,148,195,956 | **−320,085,400 (−21.8%)** |
| unshared | 1,069,954,757 | | 214,351,801,952,039 | |

**Per constant (MSS − heuristic):**

| outcome | Init | Mathlib | Mathlib bytes |
|---|---:|---:|---:|
| MSS smaller | 50,173 (90.6%) | **625,250 (94.3%)** | −320,096,419 |
| equal | 4,994 (9.0%) | 35,859 (5.4%) | 0 |
| MSS larger | 219 (0.4%) | **2,145 (0.3%)** | +11,019 |

- **Losses (Mathlib):** p50 3, p90 10, p99 33, max **112**, mean 5.14 bytes. Init: max 50, total 933.
- **Savings:** p50 132, p90 1,080, p99 6,352, max 258,759 bytes.
- **Signed Δ = MSS − heuristic:** min −258,759, p1 −6,139, p10 −1,006, p50 −117, p90 −4, p99 0, max +112.
- **Rooted constants not in `init.ixe`** (607,869; from the CSVs):
  - heuristic 1,388,119,806 bytes, MSS 1,079,648,379 bytes, **−22.2%**;
  - smaller 575,077, equal 30,866, larger 1,926.
- **MSS/heuristic by kind:**

  | kind | Init | Mathlib |
  |---|---:|---:|
  | defn | 85.5% | 78.2% |
  | recr | 83.2% | 76.7% |
  | muts | 96.6% | 89.1% |
  | axio | 99.4% | 99.4% |
  | quot | 100.0% | 100.0% |

- **Table sizes:**
  - MSS: median 20, p90 122, p99 541, max 21,461, 36,191,166 entries in total.
  - Heuristic: median 58, p90 376, p99 1,901, max 81,565, 117,489,057 entries in total.
- **Largest losses** are `Std.Http.Status` eliminators: `casesOn` +112 (61 heuristic entries vs 125 MSS entries),
  `rec` +110 and `recOn` +110. They are followed by `Std.Http.Status.toCode` +105, `.ctorElim` +103 and the
  `Std.Http.Method` eliminators (+64, +66).
- **Largest wins** are the largest constants: `isIso_ranCounit_app_of_isDenseSubsite` −258,759 (608,188 →
  349,429).

### Where MSS loses

These facts come from the CSV. They are correlations, not a measured decomposition, as on Init.

- **All 2,145** constants where MSS is larger have more than 8 MSS entries, so some of their Share references are
  2 bytes wide.
  - 2,134 of them have more MSS entries than heuristic entries.
  - 1,240 have at most 8 heuristic entries but more than 8 MSS entries. On Init those counts were 219 of 219, 217
    and 116.
- Over all rooted Mathlib constants, MSS has more entries than the heuristic for 31,946 constants (Init: 4,484).

### MSS larger than unshared: 26 constants (Init: 0)

The §12.2 observation that MSS was "never larger than unshared" does **not** hold on Mathlib. **26** rooted
constants have MSS bytes above their unshared bytes, by 188 bytes in total and at most 38. All 26 have more than 8
MSS entries, and none of them is in `init.ixe`. The full list, from the CSV:

| constant | heuristic B | MSS B | unshared B | MSS − unshared | heuristic table | MSS table | MSS refs < 8 / 8–255 |
|---|---:|---:|---:|---:|---:|---:|---|
| `Std.Http.Status.casesOn` | 3,005 | 3,117 | 3,079 | +38 | 61 | 125 | 18 / 234 |
| `Std.Http.Status.recOn` | 2,999 | 3,109 | 3,073 | +36 | 61 | 124 | 18 / 232 |
| `Std.Http.Method.recOn` | 1,879 | 1,943 | 1,925 | +18 | 36 | 76 | 18 / 136 |
| `contMDiffWithinAt_finset_prod` | 1,199 | 1,231 | 1,220 | +11 | 8 | 26 | 28 / 40 |
| `contMDiffWithinAt_finset_sum` | 1,199 | 1,231 | 1,220 | +11 | 8 | 26 | 28 / 40 |
| `ContMDiff.along_snd` | 1,218 | 1,254 | 1,247 | +7 | 8 | 27 | 42 / 56 |
| `contMDiffWithinAt_finset_prod'` | 1,244 | 1,274 | 1,268 | +6 | 8 | 25 | 31 / 38 |
| `contMDiffWithinAt_finset_sum'` | 1,244 | 1,274 | 1,268 | +6 | 8 | 25 | 31 / 38 |
| `ContMDiff.along_fst` | 1,218 | 1,251 | 1,246 | +5 | 8 | 26 | 42 / 54 |
| `contMDiff_finset_prod` | 1,151 | 1,177 | 1,172 | +5 | 8 | 23 | 28 / 35 |
| `contMDiff_finset_sum` | 1,151 | 1,177 | 1,172 | +5 | 8 | 23 | 28 / 35 |
| `ContMDiffAt.along_fst` | 1,264 | 1,300 | 1,296 | +4 | 8 | 27 | 45 / 57 |
| `Lean.Lsp.SymbolKind.casesOn` | 1,249 | 1,285 | 1,281 | +4 | 22 | 48 | 18 / 80 |
| `contMDiffAt_finset_prod` | 1,155 | 1,181 | 1,178 | +3 | 8 | 23 | 30 / 34 |
| `contMDiffAt_finset_sum` | 1,155 | 1,181 | 1,178 | +3 | 8 | 23 | 30 / 34 |
| `contMDiffOn_finset_prod` | 1,191 | 1,217 | 1,214 | +3 | 8 | 23 | 30 / 34 |
| `contMDiffOn_finset_sum` | 1,191 | 1,217 | 1,214 | +3 | 8 | 23 | 30 / 34 |
| `Lean.Lsp.CompletionItemKind.recOn` | 1,204 | 1,238 | 1,235 | +3 | 21 | 46 | 18 / 76 |
| `_private.Lean.Parser.Types.«0».Lean.Parser.withStackDrop` | 598 | 607 | 604 | +3 | 6 | 13 | 18 / 10 |
| `_private.Mathlib.Order.Notation.«0».Mathlib.Meta.linearOrderToMax` | 978 | 999 | 996 | +3 | 8 | 19 | 19 / 22 |
| `_private.Mathlib.Order.Notation.«0».Mathlib.Meta.linearOrderToMin` | 978 | 999 | 996 | +3 | 8 | 19 | 19 / 22 |
| `ContMDiffAt.along_snd` | 1,263 | 1,298 | 1,296 | +2 | 8 | 27 | 47 / 55 |
| `Lean.Lsp.SemanticTokenType.casesOn` | 1,159 | 1,191 | 1,189 | +2 | 20 | 44 | 18 / 72 |
| `Lean.Server.Completion.idCompletion` | 539 | 541 | 539 | +2 | 0 | 9 | 16 / 2 |
| `Lean.Parser.withResetCacheFn` | 997 | 1,007 | 1,006 | +1 | 8 | 17 | 17 / 18 |
| `_private.Lean.Meta.Basic.«0».Lean.Meta.mkFreshExprMVarAtCore` | 1,007 | 1,015 | 1,014 | +1 | 2 | 12 | 23 / 8 |

None of them has a Share index ≥ 256.

## Uniform-reference-width classification and components

The candidates are the `deg ≥ 2`, size > 1 terms: 36,191,166 of them, equal to the MSS entry total. The
definitions are unchanged from the Init document. Init's percentages are in parentheses.

| w | certain-stored | certain-excluded | uncertain |
|---:|---:|---:|---:|
| 1 | 31,975,849 (**88.4%**; Init 80.5%) | 0 (0%; Init 0%) | 4,215,317 (11.6%; Init 19.5%) |
| 2 | 25,708,230 (**71.0%**; Init 64.1%) | 3,712,253 (10.3%; Init 14.9%) | 6,770,683 (18.7%; Init 21.0%) |
| 3 | 20,941,150 (**57.9%**; Init 54.4%) | 8,690,905 (24.0%; Init 24.3%) | 6,559,111 (18.1%; Init 21.3%) |

**Uncertain nodes per constant and largest uncertain component (Mathlib; Init in parentheses):**

| w | uncertain nodes: median / p90 / p99 / max | > 1,024 | largest component: median / p90 / p99 / max | ≤ 8 | > 32 |
|---:|---|---:|---|---:|---:|
| 1 | 1 / 15 / 82 / 3,480 (Init 2 / 21 / 95 / 970) | 38 (Init 0) | 1 / 2 / 4 / **45** (Init 1 / 2 / 4 / 45) | 662,872 = 99.9% (Init 99.9%) | 4 (Init 2) |
| 2 | 4 / 24 / 90 / 2,670 (Init 3 / 22 / 84 / 736) | 20 (Init 0) | 1 / 3 / 5 / **44** (Init 1 / 3 / 5 / 44) | 662,851 = 99.9% (Init 99.9%) | 3 (Init 1) |
| 3 | 3 / 24 / 102 / 3,077 (Init 2 / 22 / 98 / 978) | 35 (Init 0) | 1 / 3 / 5 / **44** (Init 1 / 3 / 6 / 44) | 662,118 = 99.8% (Init 99.7%) | 3 (Init 1) |

- **Constants keep many uncertain nodes but small components.** Some constants have thousands of uncertain nodes,
  yet the largest component does not grow with the corpus.
  - The largest components are the same as Init's: 45 at w = 1 and 44 at w = 2 and 3, in `Lean.Grind.Config.mk.injEq`
    (which is in `Init`).
  - Next come `Lean.Meta.Grind.Arith.Linear.Struct.mk.injEq` (42 / 41 / 41) and
    `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.mk.injEq` (36 / 35 / 35).
  - At w = 1, excluding the six Lean, Std and Init constants that lead the list, the largest component is 28, in
    `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle`.
- **The constant with the most candidates** (`isIso_ranCounit_app_of_isDenseSubsite`, 21,461 `deg`-based
  candidates) has 3,077 uncertain nodes at w = 3, and its largest component has 3 nodes (CSV).
- **Literal `headdeg` reading:** reading `headdeg` as "not the function child of an App" for any `t` changes the
  class of 1,511, 2,371 and 4,068 candidates for w = 1, 2 and 3, out of 36,191,166.

## Share-width schemes on the MSS encoding (tier-scheme comparison)

There are 159,110,515 Share references in the MSS encodings. Constant bytes under a scheme are
`MSS bytes − refbytes(A) + refbytes(scheme)`.

| scheme | reference bytes | MSS constant bytes | Δ vs A | Mathlib Δ / MSS total | Init Δ / MSS total | MSS below heuristic (Mathlib, derived) |
|---|---:|---:|---:|---:|---:|---:|
| A (Tag4 index tiers) | 298,286,517 | 1,148,195,956 | 0 | | | 21.80% |
| B (2 or 3 per constant) | 325,217,289 | 1,175,126,728 | +26,930,772 | +2.35% | +2.07% | 19.97% |
| C (1, 2 or 3 per constant) | 323,081,186 | 1,172,990,625 | +24,794,669 | +2.16% | +1.69% | 20.11% |
| D (fixed per constant, nibble index) | 314,797,020 | 1,164,706,459 | +16,510,503 | +1.44% | +0.93% | 20.68% |
| E (< 15 / < 4,111; not realizable) | 260,743,267 | 1,110,652,706 | −37,543,250 | −3.27% | −3.10% | 24.36% |
| F (< 8 / < 1,032 / beyond) | 280,471,878 | 1,130,381,317 | **−17,814,639** | **−1.55%** | −1.45% | 23.01% |
| G (< 14 / < 270 / beyond) | 283,411,489 | 1,133,320,928 | −14,875,028 | −1.30% | −1.21% | 22.81% |

The last column is `1 − scheme bytes / 1,468,281,356`.

**Per constant (better / equal / worse vs A):**

| comparison | Init | Mathlib |
|---|---|---|
| B vs A | 829 / 555 / 54,002 | 12,165 / 4,900 / 646,189 |
| C vs A | 829 / 22,271 / 32,286 | 12,165 / 181,451 / 469,638 |
| D vs A | 9,773 / 22,271 / 23,342 | 127,316 / 181,451 / **354,487** |
| E vs A | 33,116 / 22,270 / 0 | 481,817 / 181,437 / 0 |
| F vs A | 1,352 / 54,034 / 0 | 23,301 / 639,953 / **0** |
| G vs A | 33,116 / 22,270 / 0 | 481,817 / 181,437 / **0** |

- **Width classes under D:** 296,310 constants at 1 byte, 366,880 at 2 bytes and 64 at 3 bytes (Init: 31,200 /
  24,180 / 6). 342 constants have more than 2,048 MSS entries (width 3 under B and C; Init 20).
- **Restricted to the 111,351 constants whose heuristic table exceeds 255 entries:** D − A = +4,213,286 bytes
  (+0.70% of their MSS bytes). On Init the same restriction gave −299,355 (−1.18%), so on Mathlib D is worse than
  the index tiers even on large tables. B − A is +8,646,111 (+1.44%), against −84,068 on Init.
- **TagN:**
  - `tagNWidth` (`Ix/Sharing/Exact/Tiered.lean`) is 1 byte below index 8, 2 below 1,032 and 3 below 66,568.
  - The largest MSS table in Mathlib has 21,461 entries. So scheme F's column is exactly the TagN price of the MSS
    table in MSS priority order, for every constant.
  - That is not the output of `canonicalSharingTiered tagN`, which chooses its own table and order; the harness
    does not run it.
- **Largest scheme losses and gains:**
  - The ten largest losses are the same ten constants under B and D, with 5,768–21,461 MSS entries. They are
    led by `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` +32,968 and
    `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` +32,894.
  - The ten largest gains under D come from constants with 3,009–4,011 MSS entries, led by
    `WeierstrassCurve.ofJNe0Or1728_Δ` −23,273.
  - The largest gain under F is `WeierstrassCurve.variableChange_Δ` −25,496.
  - The ten of each are in the harness output below.

### Reference widths in the current stored (heuristic) encoding

| stored table entries | constants | refs to 0–7 | refs to 8–255 | refs to ≥ 256 | loss under a uniform width |
|---|---:|---:|---:|---:|---|
| 1–8 | 77,332 | 834,671 | 0 | 0 | (not requested) |
| 9–255 | 456,938 | 8,413,579 | 46,923,657 | 0 | w = 2: 8,413,579 B (0.57% of stored bytes; Init 0.97%) |
| > 255 | 111,351 | 4,535,443 | 55,312,965 | 81,989,876 | w = 3: 64,383,851 B (4.38%; Init 3.99%) |

Total Share references are 198,010,191, over 1,468,890,902 stored bytes.

The harness labels references at index ≥ 256 as 3 bytes. That is not exact on Mathlib (see the next section).

## Limits and coverage

No constant was skipped and no step failed or timed out. The harness has no per-constant time or resource limit. The
slowest constant took 2.71 s
(`_private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.«0».WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three`),
and 5 constants took more than 2 s. The harness's deliberate verification limits left these constants unchecked:

- **Unshared size not validated by serialization: 619 constants** (Init: 7).
  - Their unshared roots exceed 16 MiB, so their unshared sizes rely on the compositional function only. 37 of them are
    at least 2^30 bytes.
  - The largest is `_private.Mathlib.Condensed.Light.Sequence.«0».InternalProjectivityProof.aux`:
    206,476,428,890,489 unshared bytes (about 2.1·10^14), stored in 54,261 bytes.
  - The next are `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` (7.3·10^12) and
    `IsEvenlyCovered.toTrivialization_apply` (1.4·10^11).
  - The twenty largest are named in the harness output below. All 619 (unshared bytes, kind, stored bytes, name) are
    listed in the scratchpad file `w5/not-validated-619.txt`.
  - Because of these constants the aggregate unshared total and the "stored/unshared" ratio (printed as 0.0%) are
    meaningless.
- **`occ` not checked by the brute-force tree walk: 31,049 constants** (unshared roots > 64 KiB; Init 1,232).
- **Component brute force not run: 39,682 rooted constants** (more than 1,000 DAG nodes; Init 1,734).
- **One stored table exceeds the 3-byte Tag4 index range.**
  - `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` stores 81,565 heuristic entries.
    `putTag4` writes `1 + byteCount(n)` bytes for `n ≥ 8`, so a Share index ≥ 65,536 costs 4 bytes.
  - The harness's syntactic reference-width table counts all 146,926 of this constant's references to indices ≥ 256
    in the "3 B" column. The number at indices ≥ 65,536 was not measured.
  - So the w = 3 loss figure above omits a 1-byte difference for each such reference: at most 146,926 bytes,
    0.23% of that figure.
  - Its stored bytes are exact, as the rebuild check confirms.
  - No MSS table reaches 65,536 entries (max 21,461), so the MSS scheme pricing (A–G) is exact.
- **Not measured at all:**
  - the exact uniform and tiered optimizers (not in the merged harness);
  - the width-state DP oracle;
  - the 9 other `Benchmarks/Compile` targets.

## Reproduction

The worktree is `/home/jcb/projects/ix-sharing-w5`, branch `ix-sharing-w5`, at `5f284b7a` (the harness is unchanged
from `ix-sharing`). The scratchpad is
`S=/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad`. Every command was run
from the worktree root and detached with `setsid nohup … > log 2>&1 &`. The `time` command is
`/run/current-system/sw/bin/time` (GNU time 1.9).

```text
nix develop --command bash -c 'lake build ix sharing-study'
#   -> Build completed successfully (843 jobs).

nix develop --command bash -c "time -v lake exe ix compile Benchmarks/Compile/CompileMathlib.lean \
    --out $S/mathlib.ixe --verbose --json $S/w5/mathlib-compile.json --report $S/w5/mathlib-report.json"
#   -> exit 0, 7:29.18 wall, max RSS 19,107,692 kB; "Total constants: 771129";
#      "Compiled and wrote 3.1 GB env to …/mathlib.ixe in 152.42s"; report: 0 ungrounded.

nix develop --command bash -c "time -v lake exe sharing-study $S/mathlib.ixe \
    --md $S/w5/mathlib-results.md --csv $S/w5/mathlib-sharing.csv --progress 20000"
#   -> exit 0, 1:33:50 wall (5,572 s user), max RSS 4,709,872 kB;
#      "processed 679499 constants, skipped 0, mismatches 0 in 4101800 ms (total 4106730 ms)"
```

- **Compile flags:** `--verbose`, `--json` and `--report` only add progress logging and the two JSON files. The
  required command is the one in the first bullet of "Corpus".
- **Compile process tree:** it used 435% CPU, 1,781 s user.
- **Harness timing:**
  - The harness is single-threaded. Its internal timer gives 4.9 s to load the 3.3 GB file and 4,101.8 s to
    measure. Init's eighth run took 295.0 s for 12× fewer constants.
  - The remaining ~25 minutes of process wall time are lake startup plus the work after the measurement loop
    (summary tables over 679,499 rows and the CSV). They were not broken down further.
- **Machine load:** a W3 `sharing-study` run on `init.ixe` was running on the same machine at the same time.
- **CSV:** the per-constant CSV is 139,383,903 bytes, with 679,499 rows plus a header and the same 55 columns as the
  Init CSV. It is too large to track and is kept at `$S/w5/mathlib-sharing.csv`.
- **Other files** in `$S/w5/`:
  - `compile.log` and `study.log`;
  - `mathlib-report.json` and `mathlib-compile.json`;
  - `not-validated-619.txt`;
  - `mss-gt-unshared.txt`;
  - `csvcheck.awk` and `overlap.awk`, the gawk scripts behind the CSV-derived numbers. `csvcheck.awk` reproduces the
    Init document's CSV-derived counts on the Init CSV.

---

The rest of this document is the harness's `--md` output from this run, unedited.

## Results

- Corpus: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe` (3343271273 bytes), 679499 stored constants (distinct addresses), 778344 names.
- Constants processed: 679499; skipped: 0; with at least one expression root: 663254.
- Harness wall time: load 4930 ms, measurement 4101800 ms, total 4106730 ms.
- Production rebuild (`buildConstantWithSharing` on expanded roots, then `serConstant`) differs from `rawBytes`: **0** constants.
- Decode/encode roundtrip (`serConstant ∘ get`) differs from `rawBytes`: 0 constants.
- Compositional unshared size checked against `serConstant` of the real unshared Constant: 678880 equal, 0 different, 619 not checked (unshared roots > 16777216 bytes).
- `usageCount` (occ) checked against a brute-force walk of the fully expanded roots: 648450 equal, 0 different, 31049 not checked (unshared roots > 65536 bytes).
- Constants whose stored (heuristic) bytes exceed their unshared bytes: 20237.
- Total `rawBytes.size`: 1468890902; total unshared Constant bytes: 214351802561585.

### Constants whose unshared size was not validated by serialization

| constant | kind | unshared bytes | stored bytes |
|---|---|---:|---:|
| `_private.Mathlib.Condensed.Light.Sequence.«0».InternalProjectivityProof.aux` | defn | 206476428890489 | 54261 |
| `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 7349541595358 | 269209 |
| `IsEvenlyCovered.toTrivialization_apply` | defn | 139464075123 | 44235 |
| `_private.Mathlib.CategoryTheory.Functor.TypeValuedFlat.«0».CategoryTheory.FunctorToTypes.fromOverFunctorElementsEquivalence._proof_19` | defn | 133910934629 | 85056 |
| `groupCohomology.H1InfRes_exact` | defn | 34706856435 | 150010 |
| `Rep.instMonoidalCategory._proof_14` | defn | 21664521473 | 55700 |
| `AlgebraicGeometry.isIso_fromTildeΓ_of_presentation` | defn | 17730160456 | 36910 |
| `LieModule.Cohomology.d₂₃._proof_12` | defn | 8161802819 | 41764 |
| `_private.Mathlib.Condensed.Light.Sequence.«0».InternalProjectivityProof.cocone._proof_1` | defn | 7065129700 | 47350 |
| `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` | defn | 5917704097 | 336490 |
| `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator._proof_19` | defn | 5065316295 | 36721 |
| `CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.pentagon` | defn | 5050666179 | 80968 |
| `LieModule.Cohomology.d₂₃._proof_11` | defn | 4899565702 | 34946 |
| `RootPairing.GeckConstruction.equivRootSystem._proof_2` | defn | 4194198945 | 29707 |
| `AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth` | defn | 4106683646 | 149885 |
| `retractionKerCotangentToTensorEquivSection._proof_20` | defn | 3562698142 | 191668 |
| `CategoryTheory.PreOneHypercover.sieve₁_inter` | defn | 3396754573 | 116317 |
| `_private.Mathlib.RingTheory.Extension.Cotangent.Basis.«0».Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentHom_tmul` | defn | 3043638137 | 28730 |
| `Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_blastDivSubtractShift_q` | defn | 3026502579 | 39708 |
| `AlgebraicGeometry.Scheme.Hom.toNormalization_app_preimage` | defn | 2989993634 | 42047 |

### Distributions over constants with at least one root (663254)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| `N` (distinct subterms) | 1 | 147 | 692 | 3052 | 95110 | 329.91 |
| `occ ≥ 2` (R1 only) | 0 | 78 | 443 | 2041 | 81846 | 204.48 |
| candidates (R1+R2: occ ≥ 2, size > 1) | 0 | 69 | 432 | 2029 | 81833 | 196.76 |
| candidates with size > 2 | 0 | 65 | 417 | 1998 | 81779 | 189.88 |
| candidates with size > 3 | 0 | 56 | 390 | 1941 | 81726 | 177.67 |
| current table size | 0 | 58 | 376 | 1901 | 81565 | 177.14 |
| `rawBytes.size` | 9 | 1112 | 4510 | 18597 | 608188 | 2213.75 |
| unshared Constant bytes | 9 | 1344 | 19354 | 695929 | 206476428890489 | 323182071.95 |
| max telescope length | 0 | 8 | 15 | 27 | 112 | 8.82 |
| roots | 1 | 2 | 2 | 2 | 105 | 2.01 |

### Distributions over all processed constants (679499, projections included)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| `N` (distinct subterms) | 0 | 142 | 679 | 3011 | 95110 | 322.03 |
| `occ ≥ 2` (R1 only) | 0 | 74 | 435 | 2015 | 81846 | 199.59 |
| candidates (R1+R2: occ ≥ 2, size > 1) | 0 | 66 | 424 | 2004 | 81833 | 192.06 |
| candidates with size > 2 | 0 | 62 | 409 | 1974 | 81779 | 185.34 |
| candidates with size > 3 | 0 | 53 | 382 | 1915 | 81726 | 173.43 |
| current table size | 0 | 55 | 369 | 1874 | 81565 | 172.91 |
| `rawBytes.size` | 9 | 1076 | 4433 | 18368 | 608188 | 2161.73 |
| unshared Constant bytes | 9 | 1285 | 18604 | 675228 | 206476428890489 | 315455655.65 |
| max telescope length | 0 | 8 | 15 | 26 | 112 | 8.61 |
| roots | 0 | 2 | 2 | 2 | 105 | 1.96 |

### Candidate-count buckets (R1+R2), constants with at least one root (663254), cumulative

| candidates | constants | share |
|---|---:|---:|
| ≤ 8 | 67177 | 10.1% |
| ≤ 16 | 121321 | 18.3% |
| ≤ 24 | 167737 | 25.3% |
| ≤ 32 | 206933 | 31.2% |
| ≤ 64 | 318883 | 48.1% |
| ≤ 128 | 439602 | 66.3% |
| > 128 | 223652 | 33.7% |

### Candidates with size > 3, constants with at least one root, cumulative

| candidates | constants | share |
|---|---:|---:|
| ≤ 8 | 100264 | 15.1% |
| ≤ 16 | 159579 | 24.1% |
| ≤ 24 | 208288 | 31.4% |
| ≤ 32 | 247956 | 37.4% |
| ≤ 64 | 354426 | 53.4% |
| ≤ 128 | 465678 | 70.2% |
| > 128 | 197576 | 29.8% |

### Ten constants with the most candidates

| # | constant | kind | `N` | `occ≥2` | candidates | size>2 | size>3 | table | stored B | unshared B | max telescope |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 95110 | 81846 | 81833 | 81779 | 81726 | 81565 | 608188 | 1406312108 | 14 |
| 2 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | defn | 70414 | 61651 | 61641 | 61512 | 61497 | 61496 | 447246 | 87682564 | 27 |
| 3 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 78913 | 59211 | 59202 | 59037 | 58936 | 58798 | 471381 | 41940708 | 25 |
| 4 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 66025 | 52077 | 52066 | 51977 | 51873 | 51767 | 398085 | 82279088 | 21 |
| 5 | `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` | defn | 53511 | 44642 | 44632 | 44569 | 44517 | 44492 | 336490 | 5917704097 | 23 |
| 6 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 64047 | 41883 | 41872 | 41767 | 41664 | 41529 | 350617 | 80464470 | 23 |
| 7 | `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 43441 | 38801 | 38789 | 38728 | 38645 | 38598 | 269209 | 7349541595358 | 14 |
| 8 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 53222 | 38494 | 38483 | 38369 | 38302 | 38220 | 307182 | 61675147 | 42 |
| 9 | `WeierstrassCurve.addSubMapCoeff_condition` | defn | 42875 | 35713 | 35702 | 35640 | 35564 | 35499 | 272192 | 73921037 | 10 |
| 10 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 44737 | 35240 | 35231 | 35079 | 34981 | 34940 | 270991 | 27374524 | 24 |

### Totals by ConstantInfo kind

| kind | constants | `rawBytes.size` | unshared bytes | stored/unshared | table entries | candidates | stored > unshared |
|---|---:|---:|---:|---:|---:|---:|---:|
| defn | 650712 | 1457076542 | 214351766595551 | 0.0% | 116718903 | 129616997 | 19579 |
| recr | 6007 | 5897999 | 22276690 | 26.5% | 528580 | 596911 | 571 |
| axio | 13 | 784 | 787 | 99.6% | 9 | 9 | 1 |
| quot | 4 | 311 | 312 | 99.7% | 1 | 1 | 0 |
| muts | 6518 | 5305720 | 13078699 | 40.6% | 241564 | 288810 | 86 |
| iPrj | 6093 | 225441 | 225441 | 100.0% | 0 | 0 | 0 |
| cPrj | 8481 | 322278 | 322278 | 100.0% | 0 | 0 | 0 |
| rPrj | 209 | 7733 | 7733 | 100.0% | 0 | 0 | 0 |
| dPrj | 1462 | 54094 | 54094 | 100.0% | 0 | 0 | 0 |
| **all** | 679499 | 1468890902 | 214351802561585 | 0.0% | 117489057 | 130502728 | 20237 |

### Longest telescopes

- App spine: 106 (`Lean.Meta.Grind.Arith.Cutsat.EqCnstr._sizeOf_6`)
- Lam telescope: 112 (`Ix.54eed55de1373a2e13e71412efee3d619b0412a27feb0098a1d4caaabc828770.Lean.Meta.Grind.Arith.Cutsat.DiseqCnstr.rec`)
- All telescope: 106 (`Ix.54eed55de1373a2e13e71412efee3d619b0412a27feb0098a1d4caaabc828770.Lean.Meta.Grind.Arith.Cutsat.DiseqCnstr.rec`)

### Slowest constants in this harness (all steps above, per constant)

| constant | kind | ms | `N` | stored B |
|---|---|---:|---:|---:|
| `_private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.«0».WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three` | defn | 2711 | 50027 | 264421 |
| `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 2375 | 78913 | 471381 |
| `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` | defn | 2274 | 23888 | 141541 |
| `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 2144 | 95110 | 608188 |
| `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` | defn | 2127 | 37207 | 227587 |

## Maximal structural sharing (MSS)

Rule: store exactly the subterms with compact-DAG indegree `deg ≥ 2` (edges with multiplicity plus root occurrences) and unshared size > 1; every occurrence of a stored term is a Share; order by priority topological order (largest `deg`, then smaller blake3 hash bytes). Built with `Ix.Sharing.buildSharingEntries`/`rewriteExprs`, placed with the production root cursor helpers, serialized with `serConstant`.

### Witnesses from the plan (§2)

| fixture | unshared B | heuristic B | MSS B | expected MSS | MSS decode/expand check | MSS bytes | heuristic bytes |
|---|---:|---:|---:|---|---|---|---|
| `T2 → T2` | 20 | 19 | 17 | 17 (plan: exact minimum `d200009117b0b001921700170000000100`) | ok | `d200009117b0b001921700170000000100` | `d200009117b1b10291170000911700b0000100` |
| `T16 → T16` | 78 | 81 | 46 | 46 (plan: feasible improvement) | ok | `d200009117b0b0019810170017001700170017001700170017001700170017001700170017001700170000000100` | `d200009117b80eb80e0f921700170000911700b0911700b1911700b2911700b3911700b4911700b5911700b6911700b7911700b808911700b809911700b80a911700b80b911700b80c911700b80d000100` |
| `A → A → B → B`, `A = Prop → Prop`, `B = Prop → Type` | 28 | 25 | 25 | 25 (plan: minimum, two tied orders) | ok | `d200009317b117b117b0b00291170001911700000002000100` | `d200009317b117b117b0b00291170001911700000002000100` |

Negative controls for the MSS decode/expand/equality check:

- `T2 → T2` MSS bytes vs roots `T2 → T2'` (one leaf `Sort 0` replaced by `Sort 1`): behaves as expected
- `T2 → T2` MSS bytes vs roots `T16 → T16`: behaves as expected
- `T2 → T2` MSS bytes vs its own roots (must be accepted): behaves as expected

### Corpus verification

- MSS built for 679499 constants; decode, re-encode (byte-identical), table expansion and exact pointer-memoized structural equality of the expanded roots with the original expanded roots: 679499 ok, **0** failed.

### Totals over the 663254 constants with at least one root

| encoding | total bytes | vs heuristic |
|---|---:|---:|
| heuristic (stored `rawBytes`) | 1468281356 | |
| MSS | 1148195956 | -320085400 (−21.8%) |
| unshared | 214351801952039 | 214350333670683 |

### MSS − heuristic per constant

| outcome | constants | share | bytes |
|---|---:|---:|---:|
| MSS smaller | 625250 | 94.3% | −320096419 |
| equal | 35859 | 5.4% | 0 |
| MSS larger | 2145 | 0.3% | +11019 |

- Losses (MSS − heuristic) over the 2145 larger constants: p50 3, p90 10, p99 33, max 112, mean 5.14.
- Savings (heuristic − MSS) over the 625250 smaller constants: p50 132, p90 1080, p99 6352, max 258759, mean 511.95.
- Signed Δ = MSS − heuristic over all 663254 rooted constants: min -258759, p1 -6139, p10 -1006, p50 -117, p90 -4, p99 0, max 112.
- MSS larger than unshared: 26 constants, total excess 188 bytes, max 38. (Heuristic larger than unshared: 20237.)

### Table sizes (rooted constants)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| MSS table size | 0 | 20 | 122 | 541 | 21461 | 54.57 |
| heuristic table size | 0 | 58 | 376 | 1901 | 81565 | 177.14 |
| MSS continuation-only entries | 0 | 1 | 23 | 143 | 7348 | 10.28 |
| … with MSS entry payload ≤ 2 | 0 | 0 | 0 | 4 | 32 | 0.20 |
| … with unshared payload ≤ 2 | 0 | 0 | 0 | 0 | 10 | 0.01 |

- Total MSS entries 36191166; heuristic entries 117489057.
- Continuation-only entries (never a root; every occurrence is the function child of an App for an App term, or the body of a Lam/All for a Lam/All term): 6817060 in total; with MSS entry payload ≤ 2: 132031; with unshared payload ≤ 2: 5144.
- Constants with at least one continuation-only entry of MSS payload ≤ 2: 64527; of these, MSS larger than heuristic: 191, equal: 160, smaller: 64176.
- Of the 2145 constants where MSS is larger, 191 have such an entry; of the 625250 where MSS is smaller, 64176.

### MSS by ConstantInfo kind (rooted constants)

| kind | constants | heuristic B | MSS B | unshared B | MSS/heuristic | MSS smaller | equal | MSS larger |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| defn | 650712 | 1457076542 | 1138945739 | 214351766595551 | 78.2% | 614858 | 33769 | 2085 |
| recr | 6007 | 5897999 | 4522578 | 22276690 | 76.7% | 5989 | 6 | 12 |
| axio | 13 | 784 | 779 | 787 | 99.4% | 3 | 10 | 0 |
| quot | 4 | 311 | 311 | 312 | 100.0% | 0 | 4 | 0 |
| muts | 6518 | 5305720 | 4726549 | 13078699 | 89.1% | 4400 | 2070 | 48 |

### Ten largest MSS losses (MSS − heuristic)

| # | constant | kind | heuristic B | MSS B | Δ | unshared B | heuristic table | MSS table | cont. p≤2 |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `Std.Http.Status.casesOn` | defn | 3005 | 3117 | 112 | 3079 | 61 | 125 | 0 |
| 2 | `Std.Http.Status.rec` | recr | 14932 | 15042 | 110 | 27670 | 67 | 122 | 0 |
| 3 | `Std.Http.Status.recOn` | defn | 2999 | 3109 | 110 | 3073 | 61 | 124 | 0 |
| 4 | `Std.Http.Status.toCode` | defn | 2999 | 3104 | 105 | 3368 | 6 | 61 | 0 |
| 5 | `Std.Http.Status.ctorElim` | defn | 5689 | 5792 | 103 | 6935 | 18 | 75 | 2 |
| 6 | `Std.Http.Method.rec` | recr | 6437 | 6503 | 66 | 11283 | 41 | 74 | 0 |
| 7 | `Std.Http.Method.recOn` | defn | 1879 | 1943 | 64 | 1925 | 36 | 76 | 0 |
| 8 | `Lean.Lsp.instToJsonSymbolKind` | defn | 1408 | 1465 | 57 | 1555 | 6 | 25 | 0 |
| 9 | `_private.Mathlib.Tactic.Linter.DirectoryDependency.«0».Mathlib.Linter.DirectoryDependency.allowedImportDirs` | defn | 3996 | 4048 | 52 | 6356 | 75 | 78 | 0 |
| 10 | `Std.Packages.LinearPreorderOfOrdArgs.noConfusionType` | defn | 2469 | 2519 | 50 | 2836 | 57 | 95 | 0 |

### Ten largest MSS wins (heuristic − MSS)

| # | constant | kind | heuristic B | MSS B | Δ | unshared B | heuristic table | MSS table | cont. p≤2 |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 608188 | 349429 | -258759 | 1406312108 | 81565 | 21461 | 0 |
| 2 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | defn | 447246 | 273355 | -173891 | 87682564 | 61496 | 11700 | 0 |
| 3 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 471381 | 298739 | -172642 | 41940708 | 58798 | 13054 | 0 |
| 4 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 398085 | 239810 | -158275 | 82279088 | 51767 | 10555 | 0 |
| 5 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 350617 | 213303 | -137314 | 80464470 | 41529 | 8745 | 0 |
| 6 | `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq` | defn | 336490 | 206097 | -130393 | 5917704097 | 44492 | 12056 | 0 |
| 7 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 307182 | 179803 | -127379 | 61675147 | 38220 | 7317 | 0 |
| 8 | `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 269209 | 153471 | -115738 | 7349541595358 | 38598 | 8957 | 2 |
| 9 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` | defn | 249369 | 141129 | -108240 | 5810447 | 31536 | 5768 | 0 |
| 10 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 270991 | 168437 | -102554 | 27374524 | 34940 | 6866 | 0 |

## Uniform-reference-width classification

Candidates are the subterms with compact `deg ≥ 2` and unshared size > 1 (the MSS stored set). For `w ∈ {1, 2, 3}` each candidate is CERTAIN-STORED if `g(deg, headdeg, payloadMin) > 0`, CERTAIN-EXCLUDED if `g(occ, occ, payloadMax) < 0` or it is a leaf with `(occ−1)·size < occ·w`, and UNCERTAIN otherwise, where `g(n, H, b) = (n−1)·b + (H−1)·hdr − n·w`. `payloadMin` is the width-aware recursive lower bound (a candidate child costs at most `w`, a non-candidate child its own recursive minimum; continuation children without their header). `headdeg` treats only an App in App-function position and a Lam/All in same-kind body position as continuations. Uncertain nodes are in one component when a directed DAG path whose intermediate nodes are not certain-stored joins them (transitively). Arithmetic is exact; `occ` is not capped.

- Classification errors: 0.
- Witnesses (cs/ce/unc/largest component for w = 1 | 2 | 3):
  - `T2 → T2`: 1/0/0/0 | 1/0/0/0 | 0/0/1/1 (candidates 1)
  - `T16 → T16`: 1/0/0/0 | 1/0/0/0 | 1/0/0/0 (candidates 1)
  - `A → A → B → B`: 2/0/0/0 | 0/0/2/1 | 0/2/0/0 (candidates 2)
- Candidates over the 663254 rooted constants: 36191166 (MSS table entries: 36191166).

### w = 1

- Totals: certain-stored 31975849 (88.4% of candidates), certain-excluded 0 (0.0%), uncertain 4215317 (11.6%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 1511.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 623572 equal, **0** different, 39682 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 18 | 108 | 466 | 17981 | 48.21 |
| certain-excluded | 0 | 0 | 0 | 0 | 0 | 0.00 |
| uncertain | 0 | 1 | 15 | 82 | 3480 | 6.36 |
| largest uncertain component | 0 | 1 | 2 | 4 | 45 | 0.84 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 261942 | 39.5% | 261942 | 39.5% |
| ≤ 8 | 556250 | 83.9% | 662872 | 99.9% |
| ≤ 16 | 605069 | 91.2% | 663190 | 100.0% |
| ≤ 32 | 637224 | 96.1% | 663250 | 100.0% |
| > 32 | 26030 | 3.9% | 4 | 0.0% |
| > 128 | 3053 | 0.5% | 0 | 0.0% |
| > 1024 | 38 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 1):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 236 | 0 | 124 | 45 |
| 2 | `Lean.Meta.Grind.Arith.Linear.Struct.mk.injEq` | defn | 3259 | 359 | 239 | 0 | 120 | 42 |
| 3 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.mk.injEq` | defn | 2657 | 331 | 217 | 0 | 114 | 36 |
| 4 | `_private.Init.Data.String.Decode.«0».UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` | defn | 1056 | 296 | 192 | 0 | 104 | 35 |
| 5 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 164 | 0 | 92 | 31 |
| 6 | `_private.Lean.Meta.Tactic.Grind.EMatch.«0».Lean.Meta.Grind.EMatch.processUnassigned.congr_simp` | defn | 1293 | 144 | 88 | 0 | 56 | 29 |
| 7 | `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle` | defn | 9677 | 1897 | 1303 | 0 | 594 | 28 |
| 8 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.insert` | defn | 1250 | 151 | 73 | 0 | 78 | 27 |
| 9 | `CategoryTheory.Bicategory.Adjunction.comp_right_triangle_aux` | defn | 11168 | 2145 | 1491 | 0 | 654 | 26 |
| 10 | `Lean.Meta.Grind.Arith.Cutsat.State.mk.injEq` | defn | 1648 | 237 | 163 | 0 | 74 | 25 |

### w = 2

- Totals: certain-stored 25708230 (71.0% of candidates), certain-excluded 3712253 (10.3%), uncertain 6770683 (18.7%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 2371.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 623572 equal, **0** different, 39682 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 12 | 86 | 430 | 18738 | 38.76 |
| certain-excluded | 0 | 3 | 15 | 41 | 279 | 5.60 |
| uncertain | 0 | 4 | 24 | 90 | 2670 | 10.21 |
| largest uncertain component | 0 | 1 | 3 | 5 | 44 | 1.38 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 122093 | 18.4% | 122093 | 18.4% |
| ≤ 8 | 450454 | 67.9% | 662851 | 99.9% |
| ≤ 16 | 551626 | 83.2% | 663228 | 100.0% |
| ≤ 32 | 620707 | 93.6% | 663251 | 100.0% |
| > 32 | 42547 | 6.4% | 3 | 0.0% |
| > 128 | 3074 | 0.5% | 0 | 0.0% |
| > 1024 | 20 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 2):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 148 | 91 | 121 | 44 |
| 2 | `Lean.Meta.Grind.Arith.Linear.Struct.mk.injEq` | defn | 3259 | 359 | 155 | 88 | 116 | 41 |
| 3 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.mk.injEq` | defn | 2657 | 331 | 153 | 78 | 100 | 35 |
| 4 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 103 | 64 | 89 | 30 |
| 5 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.insert` | defn | 1250 | 151 | 60 | 59 | 32 | 28 |
| 6 | `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle` | defn | 9677 | 1897 | 1432 | 2 | 463 | 26 |
| 7 | `Lean.Meta.Grind.Arith.Cutsat.State.mk.injEq` | defn | 1648 | 237 | 112 | 56 | 69 | 24 |
| 8 | `Lean.Meta.Grind.Arith.Cutsat.ToIntInfo.mk.injEq` | defn | 1500 | 210 | 92 | 53 | 65 | 24 |
| 9 | `Std.Http.Config.mk.injEq` | defn | 1501 | 208 | 88 | 52 | 68 | 24 |
| 10 | `PEquiv.toMatrix_swap` | defn | 6523 | 1782 | 1160 | 16 | 606 | 23 |

### w = 3

- Totals: certain-stored 20941150 (57.9% of candidates), certain-excluded 8690905 (24.0%), uncertain 6559111 (18.1%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 4068.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 623572 equal, **0** different, 39682 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 8 | 69 | 378 | 18281 | 31.57 |
| certain-excluded | 0 | 7 | 32 | 79 | 799 | 13.10 |
| uncertain | 0 | 3 | 24 | 102 | 3077 | 9.89 |
| largest uncertain component | 0 | 1 | 3 | 5 | 44 | 1.32 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 140469 | 21.2% | 140469 | 21.2% |
| ≤ 8 | 478592 | 72.2% | 662118 | 99.8% |
| ≤ 16 | 562292 | 84.8% | 663194 | 100.0% |
| ≤ 32 | 620176 | 93.5% | 663251 | 100.0% |
| > 32 | 43078 | 6.5% | 3 | 0.0% |
| > 128 | 4257 | 0.6% | 0 | 0.0% |
| > 1024 | 35 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 3):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 145 | 92 | 123 | 44 |
| 2 | `Lean.Meta.Grind.Arith.Linear.Struct.mk.injEq` | defn | 3259 | 359 | 151 | 91 | 117 | 41 |
| 3 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.mk.injEq` | defn | 2657 | 331 | 150 | 80 | 101 | 35 |
| 4 | `_private.Init.Data.String.Decode.«0».UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` | defn | 1056 | 296 | 154 | 42 | 100 | 31 |
| 5 | `_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.DateBuilder.insert` | defn | 1250 | 151 | 48 | 61 | 42 | 31 |
| 6 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 100 | 65 | 91 | 30 |
| 7 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 44737 | 6866 | 5487 | 165 | 1214 | 28 |
| 8 | `Batteries.UnionFind.link._proof_6` | defn | 2188 | 595 | 333 | 54 | 208 | 26 |
| 9 | `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle` | defn | 9677 | 1897 | 1389 | 8 | 500 | 26 |
| 10 | `CategoryTheory.Bicategory.Adjunction.comp_left_triangle_aux` | defn | 11254 | 2168 | 1565 | 10 | 593 | 25 |

### Reference-width loss in the current stored encoding

Share references counted syntactically in the stored roots and stored table entries of every constant (current heuristic encoding). The largest stored table has 81565 entries, so every index ≥ 256 is 3 bytes.

| stored table entries | constants | refs to 0–7 (1 B) | refs to 8–255 (2 B) | refs to ≥ 256 (3 B) | loss under the uniform width |
|---|---:|---:|---:|---:|---|
| 1–8 | 77332 | 834671 | 0 | 0 | (not requested; 834671 if these cost 2 B) |
| 9–255 | 456938 | 8413579 | 46923657 | 0 | w = 2: **8413579** bytes |
| > 255 | 111351 | 4535443 | 55312965 | 81989876 | w = 3: 2·4535443 + 55312965 = **64383851** bytes |

- Total stored bytes over all constants: 1468890902; total Share references: 198010191.

## Share-width schemes on the MSS encoding

Every occurrence of an MSS entry is a Share. Scheme A: the current tiers by index in MSS order (1 byte below index 8, 2 below 256, 3 below 65536). Scheme B: one width per constant, 2 bytes if the MSS entry count (= candidate count) is ≤ 2048, else 3. Scheme C: as B, but 1 byte if the count is ≤ 8. Scheme D: one width per constant using the tag byte's whole low nibble: 1 byte if the count is ≤ 16, 2 if ≤ 4096, else 3. Scheme E: position tiers with a nibble escape, by index in MSS order: 1 byte below index 15, 2 below 15 + 4096, else 3 (as specified; not realizable with a 4-bit Share flag). Scheme F: realizable position tiers with two marker bits: 1 byte below index 8, 2 below 8 + 1024, else 3. Scheme G: realizable position tiers with nibble values 14 and 15 as escapes: 1 byte below index 14, 2 below 14 + 256, else 3. Constant bytes under a scheme are MSS bytes − refbytes(A) + refbytes(scheme). Share nodes are counted on the materialized MSS encoding.

- Share nodes in the MSS encoding vs `Σ deg` over MSS entries: 663254 equal, **0** different.
- Share nodes counted in the scheme-F and scheme-G index buckets vs the scheme-A buckets: 663254 equal totals, **0** different.
- Share nodes counted in the scheme-E index buckets vs the scheme-A buckets: 663254 equal totals, **0** different.
- Rooted constants: 663254; Share references in their MSS encodings: 159110515; constants with more than 2048 MSS entries (width 3 under B and C): 342; with at most 8 entries (width 1 under C): 181437.

| scheme | reference bytes | MSS constant bytes | Δ vs A | Δ / MSS total (A) | Δ / heuristic total |
|---|---:|---:|---:|---:|---:|
| A (index tiers) | 298286517 | 1148195956 | 0 | +0.00% | +0.00% |
| B (2 or 3 per constant) | 325217289 | 1175126728 | 26930772 | +2.35% | +1.83% |
| C (1, 2 or 3 per constant) | 323081186 | 1172990625 | 24794669 | +2.16% | +1.69% |
| D (nibble: ≤ 16 / ≤ 4096 / more) | 314797020 | 1164706459 | 16510503 | +1.44% | +1.12% |
| E (index tiers < 15 / < 4111 / more) | 260743267 | 1110652706 | -37543250 | −3.27% | −2.56% |
| F (index tiers < 8 / < 1032 / more) | 280471878 | 1130381317 | -17814639 | −1.55% | −1.21% |
| G (index tiers < 14 / < 270 / more) | 283411489 | 1133320928 | -14875028 | −1.30% | −1.01% |

Totals for reference: MSS bytes (scheme A, the real encoding) 1148195956; heuristic stored bytes 1468281356.

| comparison | better (fewer bytes) | equal | worse |
|---|---:|---:|---:|
| B vs A | 12165 | 4900 | 646189 |
| C vs A | 12165 | 181451 | 469638 |
| D vs A | 127316 | 181451 | 354487 |
| E vs A | 481817 | 181437 | 0 |
| F vs A | 23301 | 639953 | 0 |
| G vs A | 481817 | 181437 | 0 |

Width classes under D: 1 byte (≤ 16 entries) 296310 constants, 2 bytes (17–4096) 366880, 3 bytes (> 4096) 64.

### Ten largest losses under B (B − A)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | B ref bytes | Δ (B − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 8745 | 68717 | 4149 / 24670 / 39898 | 173183 | 206151 | 32968 | 213303 |
| 2 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 13054 | 80694 | 5330 / 22234 / 53130 | 209188 | 242082 | 32894 | 298739 |
| 3 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 7317 | 57191 | 4182 / 21260 / 31749 | 141949 | 171573 | 29624 | 179803 |
| 4 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 21461 | 107147 | 3579 / 21725 / 81843 | 292558 | 321441 | 28883 | 349429 |
| 5 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` | defn | 5768 | 47121 | 2777 / 20109 / 24235 | 115700 | 141363 | 25663 | 141129 |
| 6 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 10555 | 72590 | 3442 / 16268 / 52880 | 194618 | 217770 | 23152 | 239810 |
| 7 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 6866 | 45784 | 3225 / 15909 / 26650 | 114993 | 137352 | 22359 | 168437 |
| 8 | `sum_eight_sq_mul_sum_eight_sq` | defn | 7281 | 55565 | 2359 / 16346 / 36860 | 145631 | 166695 | 21064 | 167951 |
| 9 | `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` | defn | 9848 | 50271 | 3841 / 13063 / 33367 | 130068 | 150813 | 20745 | 168683 |
| 10 | `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 8957 | 45764 | 4469 / 11700 / 29595 | 116654 | 137292 | 20638 | 153471 |

### Ten largest gains under B (A − B)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | B ref bytes | Δ (B − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve.twoTorsionPolynomial_discr` | defn | 1857 | 12676 | 409 / 2416 / 9851 | 34794 | 25352 | -9442 | 45260 |
| 2 | `WeierstrassCurve.Jacobian.addX_eq'` | defn | 1824 | 11970 | 256 / 2304 / 9410 | 33094 | 23940 | -9154 | 42502 |
| 3 | `Real.Wallis.W_eq_factorial_ratio` | defn | 1934 | 12333 | 543 / 2227 / 9563 | 33686 | 24666 | -9020 | 48150 |
| 4 | `CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle` | defn | 1897 | 10236 | 145 / 1104 / 8987 | 29314 | 20472 | -8842 | 36578 |
| 5 | `CartanMatrix.E₈_off_diag_nonpos` | defn | 1672 | 14559 | 845 / 4260 / 9454 | 37727 | 29118 | -8609 | 53536 |
| 6 | `CategoryTheory.ExactPairing.tensor._proof_1` | defn | 2011 | 12191 | 605 / 2465 / 9121 | 32898 | 24382 | -8516 | 40062 |
| 7 | `_private.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree.«0».WeierstrassCurve.expCoeff_rec` | defn | 2038 | 13602 | 1231 / 2875 / 9496 | 35469 | 27204 | -8265 | 48306 |
| 8 | `WeierstrassCurve.Affine.cyclic_sum_Y_mul_X_sub_X` | defn | 1742 | 10924 | 591 / 2101 / 8232 | 29489 | 21848 | -7641 | 40804 |
| 9 | `WeierstrassCurve.Projective.negAddY_smul` | defn | 1859 | 11980 | 226 / 3908 / 7846 | 31580 | 23960 | -7620 | 40125 |
| 10 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_reverse._proof_1` | defn | 1908 | 10516 | 314 / 2309 / 7893 | 28611 | 21032 | -7579 | 36602 |

### B − A restricted to constants whose current heuristic table exceeds 255 entries

- Constants: 111351; their MSS bytes 599562304, heuristic bytes 846898448; MSS entries: min 14, max 21461; with more than 2048 MSS entries: 342.
- Reference bytes: A 233802244, B 242448355; Δ (B − A) 8646111 (+1.44% of their MSS bytes, +1.02% of their heuristic bytes).
- B vs A: better 12165, equal 14, worse 99172.

### Ten largest losses under D (D − A)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | D ref bytes | Δ (D − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 8745 | 68717 | 4149 / 24670 / 39898 | 173183 | 206151 | 32968 | 213303 |
| 2 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 13054 | 80694 | 5330 / 22234 / 53130 | 209188 | 242082 | 32894 | 298739 |
| 3 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 7317 | 57191 | 4182 / 21260 / 31749 | 141949 | 171573 | 29624 | 179803 |
| 4 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 21461 | 107147 | 3579 / 21725 / 81843 | 292558 | 321441 | 28883 | 349429 |
| 5 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` | defn | 5768 | 47121 | 2777 / 20109 / 24235 | 115700 | 141363 | 25663 | 141129 |
| 6 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 10555 | 72590 | 3442 / 16268 / 52880 | 194618 | 217770 | 23152 | 239810 |
| 7 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual` | defn | 6866 | 45784 | 3225 / 15909 / 26650 | 114993 | 137352 | 22359 | 168437 |
| 8 | `sum_eight_sq_mul_sum_eight_sq` | defn | 7281 | 55565 | 2359 / 16346 / 36860 | 145631 | 166695 | 21064 | 167951 |
| 9 | `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` | defn | 9848 | 50271 | 3841 / 13063 / 33367 | 130068 | 150813 | 20745 | 168683 |
| 10 | `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective` | defn | 8957 | 45764 | 4469 / 11700 / 29595 | 116654 | 137292 | 20638 | 153471 |

### Ten largest gains under D (A − D)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | D ref bytes | Δ (D − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve.ofJNe0Or1728_Δ` | defn | 3543 | 28414 | 1162 / 2817 / 24435 | 80101 | 56828 | -23273 | 108259 |
| 2 | `ModularForm.discriminant_T_invariant` | defn | 4011 | 28243 | 746 / 3973 / 23524 | 79264 | 56486 | -22778 | 104503 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 3640 | 22811 | 497 / 4776 / 17538 | 62663 | 45622 | -17041 | 76309 |
| 4 | `WeierstrassCurve.variableChange_b₈` | defn | 3306 | 25347 | 408 / 7876 / 17063 | 67349 | 50694 | -16655 | 80704 |
| 5 | `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul` | defn | 3694 | 20163 | 641 / 2722 / 16800 | 56485 | 40326 | -16159 | 75612 |
| 6 | `WeierstrassCurve.Jacobian.negAddY_neg` | defn | 3109 | 21886 | 525 / 4921 / 16440 | 59687 | 43772 | -15915 | 72842 |
| 7 | `Cubic.discr_eq_prod_three_roots` | defn | 3009 | 20253 | 530 / 3412 / 16311 | 56287 | 40506 | -15781 | 70534 |
| 8 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 3236 | 21512 | 1001 / 4190 / 16321 | 58344 | 43024 | -15320 | 72208 |
| 9 | `Real.log_five_near_10` | defn | 3523 | 25534 | 2316 / 5909 / 17309 | 66061 | 51068 | -14993 | 122313 |
| 10 | `_private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.«0».PeriodPair.analyticAt_relation_zero` | defn | 3721 | 20483 | 1194 / 3288 / 16001 | 55773 | 40966 | -14807 | 80992 |

### Ten largest losses under E (E − A)

| # | constant | kind | MSS entries | Share refs | refs < 15 / 15–4110 / ≥ 4111 | A ref bytes | E ref bytes | Δ (E − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `ADEInequality.A` | defn | 1 | 4 | 4 / 0 / 0 | 4 | 4 | 0 | 260 |
| 2 | `ADEInequality.A'` | defn | 3 | 15 | 15 / 0 / 0 | 15 | 15 | 0 | 387 |
| 3 | `ADEInequality.A'.eq_1` | defn | 4 | 18 | 18 / 0 / 0 | 18 | 18 | 0 | 501 |
| 4 | `ADEInequality.D'` | defn | 3 | 13 | 13 / 0 / 0 | 13 | 13 | 0 | 382 |
| 5 | `ADEInequality.D'.eq_1` | defn | 4 | 16 | 16 / 0 / 0 | 16 | 16 | 0 | 495 |
| 6 | `ADEInequality.E'` | defn | 6 | 19 | 19 / 0 / 0 | 19 | 19 | 0 | 459 |
| 7 | `ADEInequality.E'.eq_1` | defn | 7 | 22 | 22 / 0 / 0 | 22 | 22 | 0 | 572 |
| 8 | `ADEInequality.E6` | defn | 1 | 2 | 2 / 0 / 0 | 2 | 2 | 0 | 253 |
| 9 | `ADEInequality.E7` | defn | 1 | 2 | 2 / 0 / 0 | 2 | 2 | 0 | 253 |
| 10 | `ADEInequality.E8` | defn | 1 | 2 | 2 / 0 / 0 | 2 | 2 | 0 | 253 |

### Ten largest gains under E (A − E)

| # | constant | kind | MSS entries | Share refs | refs < 15 / 15–4110 / ≥ 4111 | A ref bytes | E ref bytes | Δ (E − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve.variableChange_Δ` | defn | 9233 | 72021 | 1295 / 49848 / 20878 | 209949 | 163625 | -46324 | 239709 |
| 2 | `WeierstrassCurve.Projective.negDblY_eq'` | defn | 7073 | 52123 | 992 / 41198 / 9933 | 150943 | 113187 | -37756 | 174025 |
| 3 | `CategoryTheory.Bicategory.mateEquiv_vcomp` | defn | 8940 | 57952 | 3439 / 36485 / 18028 | 163709 | 130493 | -33216 | 185171 |
| 4 | `WeierstrassCurve.isHomogeneous_addSubMapCoeff` | defn | 10150 | 68764 | 2224 / 43483 / 23057 | 190766 | 158361 | -32405 | 230946 |
| 5 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | defn | 11700 | 80765 | 2566 / 39116 / 39083 | 228613 | 198047 | -30566 | 273355 |
| 6 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | defn | 10555 | 72590 | 5039 / 42663 / 24888 | 194618 | 165029 | -29589 | 239810 |
| 7 | `WeierstrassCurve.Projective.dblX_eq'` | defn | 5478 | 39250 | 766 / 34336 / 4148 | 111434 | 81882 | -29552 | 130353 |
| 8 | `WeierstrassCurve.addSubMapCoeff_condition` | defn | 8048 | 49738 | 1556 / 35793 / 12389 | 139044 | 110309 | -28735 | 169951 |
| 9 | `WeierstrassCurve.c_relation` | defn | 4531 | 34835 | 1078 / 32246 / 1511 | 98375 | 70103 | -28272 | 117505 |
| 10 | `WeierstrassCurve.instMulActionVariableChange._proof_1` | defn | 4831 | 34728 | 638 / 31535 / 2555 | 99272 | 71373 | -27899 | 116499 |

### Scheme F vs A

- Constants worse than A under F: **0**; largest per-constant Δ (F − A): 0.

Ten largest gains under F (A − F):

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–1031 / ≥ 1032 | A ref bytes | F ref bytes | Δ (F − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve.variableChange_Δ` | defn | 9233 | 72021 | 938 / 29734 / 41349 | 209949 | 184453 | -25496 | 239709 |
| 2 | `CartanMatrix.E₈_det` | defn | 6878 | 47812 | 1833 / 18142 / 27837 | 136215 | 121628 | -14587 | 160092 |
| 3 | `WeierstrassCurve.Projective.dblX_eq'` | defn | 5478 | 39250 | 539 / 19585 / 19126 | 111434 | 97087 | -14347 | 130353 |
| 4 | `WeierstrassCurve.Projective.negDblY_eq'` | defn | 7073 | 52123 | 695 / 17793 / 33635 | 150943 | 137186 | -13757 | 174025 |
| 5 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | defn | 11700 | 80765 | 1849 / 22928 / 55988 | 228613 | 215669 | -12944 | 273355 |
| 6 | `WeierstrassCurve.instMulActionVariableChange._proof_1` | defn | 4831 | 34728 | 451 / 15917 / 18360 | 99272 | 87365 | -11907 | 116499 |
| 7 | `WeierstrassCurve.isHomogeneous_addSubMapCoeff` | defn | 10150 | 68764 | 1300 / 24557 / 42907 | 190766 | 179135 | -11631 | 230946 |
| 8 | `WeierstrassCurve.c_relation` | defn | 4531 | 34835 | 827 / 15583 / 18425 | 98375 | 87268 | -11107 | 117505 |
| 9 | `CartanMatrix.E₇_det` | defn | 4377 | 29903 | 1216 / 13722 / 14965 | 83876 | 73555 | -10321 | 101188 |
| 10 | `Cubic.discr_eq_prod_three_roots` | defn | 3009 | 20253 | 530 / 12466 / 7257 | 56287 | 47233 | -9054 | 70534 |

### Scheme G vs A

- Constants worse than A under G: **0**; largest per-constant Δ (G − A): 0.

Ten largest gains under G (A − G):

| # | constant | kind | MSS entries | Share refs | refs < 14 / 14–269 / ≥ 270 | A ref bytes | G ref bytes | Δ (G − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `String.firstDiffPos_loop_eq._unary` | defn | 3458 | 22509 | 4968 / 5013 / 12528 | 55587 | 52578 | -3009 | 83347 |
| 2 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | defn | 21461 | 107147 | 5927 / 19688 / 81532 | 292558 | 289899 | -2659 | 349429 |
| 3 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | defn | 13054 | 80694 | 7357 / 20515 / 52822 | 209188 | 206853 | -2335 | 298739 |
| 4 | `_private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'` | defn | 7317 | 57191 | 6135 / 19677 / 31379 | 141949 | 139626 | -2323 | 179803 |
| 5 | `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` | defn | 9848 | 50271 | 6047 / 10955 / 33269 | 130068 | 127764 | -2304 | 168683 |
| 6 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | defn | 8745 | 68717 | 5925 / 23341 / 39451 | 173183 | 170960 | -2223 | 213303 |
| 7 | `Function.Exact.splitSurjectiveEquiv._proof_12` | defn | 3012 | 21723 | 5648 / 7003 / 9072 | 49064 | 46870 | -2194 | 63079 |
| 8 | `Coalgebra.TensorProduct.assoc._proof_3` | defn | 2174 | 20269 | 5700 / 5938 / 8631 | 45584 | 43469 | -2115 | 54699 |
| 9 | `Function.Exact.splitInjectiveEquiv._proof_10` | defn | 3146 | 22977 | 5165 / 7632 / 10180 | 53072 | 50969 | -2103 | 68162 |
| 10 | `_private.Mathlib.Geometry.Manifold.VectorField.LieBracket.«0».VectorField.mpullbackWithin_mlieBracketWithin_aux` | defn | 2598 | 24507 | 4964 / 11409 / 8134 | 54205 | 52184 | -2021 | 74857 |

### D − A restricted to constants whose current heuristic table exceeds 255 entries

- Constants: 111351; width classes under D: 1 byte 7, 2 bytes 111280, 3 bytes 64.
- Reference bytes: A 233802244, D 238015530; Δ (D − A) 4213286 (+0.70% of their MSS bytes, +0.50% of their heuristic bytes).
- D vs A: better 12450, equal 14, worse 98887.
