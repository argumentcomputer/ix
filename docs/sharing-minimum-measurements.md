# Sharing corpus measurements (plan gate P1.5)

Measurements for gate P1.5 of [`sharing-minimum.md`](sharing-minimum.md), taken on the
`Init` corpus with the harness `Benchmarks/SharingStudy.lean` (`lake exe sharing-study`).
The plan says these numbers decide P3's design. This document reports them and does not
choose a design.

## Headline

Over the 55,386 stored constants that have at least one expression root (all 56,622
stored constants of `init.ixe` were processed and none were skipped):

| | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| distinct subterms `N` | 1 | 86 | 470 | 2,015 | 27,628 | 215.50 |
| candidates after R1+R2 (`occ ≥ 2`, size > 1) | 0 | 34 | 232 | 1,187 | 22,458 | 109.96 |
| candidates with size > 3 | 0 | 25 | 193 | 1,113 | 22,224 | 94.42 |
| current heuristic table size | 0 | 26 | 203 | 1,096 | 22,088 | 96.21 |
| stored bytes (`rawBytes.size`) | 9 | 693 | 3,081 | 11,329 | 170,285 | 1,447.33 |

- Cumulative candidate counts (R1+R2): 17.2% of rooted constants have ≤ 8, 30.0% ≤ 16,
  48.4% ≤ 32, 67.3% ≤ 64 and 81.9% ≤ 128. 10,014 constants (18.1%) have more than 128.
  From the CSV: 554 have zero candidates, 50,438 have ≤ 256, 54,673 have ≤ 1,024, 713 have
  more than 1,024 and 80 have more than 4,096.
- With the size > 3 cutoff instead: 25.5% are ≤ 8, 84.8% are ≤ 128 and 15.2%
  (8,405) are above 128.
- The ten constants with the most candidates are all `defn`s, mostly private `_proof_` terms
  from `Init.Data.{Vector,Array}.Extract` and string-pattern lemmas. They have 9,614 to
  22,458 candidates, stored sizes of 77 to 170 KB and unshared sizes of 3.5 to 45.7 MB.
- Totals: stored bytes 80,208,288 and unshared complete-Constant bytes 1,070,001,199.
  The stored bytes are 7.5% of the unshared bytes. `defn`s hold 79,781,914 of the stored
  bytes.
- For 600 rooted constants (567 defn, 29 recr, 3 muts, 1 axio), the current heuristic's stored
  bytes are larger than the unshared encoding. The excess totals 4,649 bytes and is at most
  70 bytes per constant: `String.Slice.Pattern.Model.IsLongestRevMatchAtChain.below.casesOn`
  stores 1,005 bytes with a 101-entry table but is 935 bytes unshared. All 600 unshared sizes
  were confirmed by serializing the real unshared Constant.
- Longest telescopes: 95 for App, Lam and All (`Lean.Grind.Config.mk.inj` /
  `.mk.noConfusion`). For rooted constants the p99 of the per-constant maximum is 17.

For comparison with the P1.5 criterion: candidate counts are small (≤ 8, where a subset state
space is at most 256) for about one constant in six. They are in the hundreds or more for
about one in five, and in the tens of thousands at the top.

## Verification of the harness

- **Production rebuild: 0 mismatches out of 56,622.** For every constant, the harness
  expanded the stored table and recovered the ordered roots with
  `Ix.CompileM.constantInfoRootExprs`. It then rebuilt the Constant with
  `Ix.CompileM.buildConstantWithSharing` (Lean `Ix.Sharing.applySharing`) and compared
  `Ixon.serConstant` byte-for-byte with `LazyConstant.rawBytes`. All were identical. The
  corpus was written by the Rust compiler (`ix compile` → `rsCompileEnvBytesFFI`), so this
  also shows that Lean's heuristic reproduces Rust's bytes on all of `Init`.
- Plain decode/encode roundtrip (`serConstant (get lc) = rawBytes`): 0 differences.
- Compositional unshared size vs `serConstant` of the actual unshared Constant (same info
  fields, refs and univs, expanded roots, empty table): 56,615 equal and 0 different. The
  7 constants whose unshared roots exceed 16 MiB were not serialized (listed below); their
  unshared sizes rely on the compositional function only.
- `occ` (the heuristic's `SubtermInfo.usageCount`) vs an independent brute-force walk of the
  expanded roots as trees (every shared pointer revisited): 55,390 constants equal and 0
  different. The remaining 1,232 constants have unshared roots above 64 KiB and were not walked.
- Structural checks: every stored table used backward references only (entry `i` refers to
  `j < i`), and every root reference was in range. There were 0 expansion errors and 0
  skipped constants.

## Definitions

- **Rows** are the distinct constant addresses in `env.consts` (56,622). This is not the
  66,621 names in the file, nor the 65,995 "Total constants" printed by `ix compile`.
  Declarations that share an address are measured once. A mutual block is one row, named by
  its least projection name with a `[block]` suffix. Projection constants (`iPrj`, `cPrj`,
  `rPrj`, `dPrj`; 1,236 rows) have no roots. They appear only in the "all processed"
  distribution and the totals.
- **Expansion:** the stored table is expanded left to right. Each `Share j` is replaced by the
  single in-memory expansion of entry `j`, so repeated indices reuse one subtree. The
  expanded roots are therefore a DAG that is linear in the stored bytes, with no `Share`
  leaves.
- **`N`:** the number of distinct subterms of all expanded roots of the constant together,
  leaves and whole roots included. It is computed by `Ix.Sharing.analyzeBlock`.
- **`occ(t)`:** `SubtermInfo.usageCount`. `countRootUsages` adds 1 per root occurrence, and
  `propagateUsageCounts` then adds each parent's count to each child entry of its `children`
  array, in reverse traversal order. That is the number of occurrences of `t` in the fully
  expanded forest, counted through every DAG edge with multiplicity, as §4.1 defines `occ`.
  The brute-force check above confirms this reading.
- **`size(t)`:** the standalone unshared `putExpr` length of `t`. It is computed on the DAG
  with a `Nat` accumulator:
  - An App spine of `k` arguments costs `Tag4(k)` plus its head plus its arguments.
  - A Lam or All telescope of `k` binders costs `Tag4(k)`, plus one contract byte and the
    type for each binder, plus the body.
  - Prj, Let and leaves cost their node header (`putNodeHeader`) plus their children.
- **Candidates:** `occ ≥ 2 ∧ size > 1` (R1 and R2 of §4.1). The size > 2 and size > 3 columns
  apply stricter size cutoffs to the same set.
- **Unshared bytes:** the complete Constant with an empty sharing table (one `Tag0` byte for
  the count), the expanded roots inline, and all other fields unchanged. It is computed as
  `rawBytes.size − Tag0(table size) − Σ|stored entry| − Σ|stored root| + 1 + Σ size(root)`.
- **Max telescope length:** the largest `Tag4` count written for any App spine or Lam/All
  telescope in the constant.
- **Percentiles** are nearest-rank (`p`-th value is the sorted element at
  `⌈p·n/100⌉ − 1`). Means are rounded to two decimals.

## Caveats

- **Hash equality is treated as structural equality.** Subterm identity is the blake3
  Merkle hash of `Ix.Sharing.computeNodeHash` (node header bytes plus child hashes), as in
  the production heuristic. The structural keys of §3.2 are not computed and collisions are
  not checked.
- Candidate counts apply only R1 and R2. No dominance, decomposition or other reduction has
  been applied. The counts measure the set the exact search would face under the reductions
  already proved in §4.1. They do not measure DP states, transitions or time, which W1's
  optimizer must report.
- The corpus is `Init` only (Rust-compiled `init.ixe`). `Std`, `Lean` and Mathlib were not
  measured.
- For the 7 constants above 16 MiB unshared, the unshared size is compositional and was not
  serialized. For the 1,232 constants above 64 KiB, `occ` rests on the code reading plus the
  55,390 checked cases.
- Timings are for this single-threaded harness. They include two hash-consing passes per
  constant (one for the measurement and one inside the production rebuild), plus the
  validation serializations. They are not optimizer timings.

## Reproduction

Worktree `/home/jcb/projects/ix-sharing-w3`, branch `ix-sharing-w3`, and corpus
`/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe`
(195,387,870 bytes). The corpus was not regenerated.

```text
cd /home/jcb/projects/ix-sharing-w3
nix develop --command bash -c 'lake build sharing-study'
#   -> Build completed successfully (96 jobs).
S=/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad
nix develop --command bash -c "lake exe sharing-study $S/init.ixe \
    --md $S/w3-results.md --csv $S/sharing-minimum-measurements.csv"
#   -> exit 0; defaults --validate-max 16777216 --occ-check-max 65536
```

Wall time for the run:

- Harness-internal: 146.8 s in total, of which 0.24 s was loading the `.ixe` through
  `Ixon.deEnvAnon` and 146.5 s was measuring 56,622 constants.
- End to end including `nix develop` and `lake exe` startup: about 152 s (started at
  18:24:07; the log was last written at 18:26:39).
- The slowest single constant took 0.96 s.

The per-constant CSV is 6,186,320 bytes (56,622 rows plus a header), which is too large to
track here. It is kept at
`/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/sharing-minimum-measurements.csv`.
Its columns are:

```text
addr (first 16 hex digits), name, kind, members (muts: i/c/r/d counts), roots, N,
occ_ge2, cand, cand_gt2, cand_gt3, table, raw_bytes, unshared_bytes, rebuild_ok,
roundtrip_ok, unshared_validated, occ_checked, max_app, max_lam, max_all, us (harness µs)
```

Rerunning the command above regenerates it.

---

The rest of this document is the harness's `--md` output, unedited.

## Results

- Corpus: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe` (195387870 bytes), 56622 stored constants (distinct addresses), 66621 names.
- Constants processed: 56622; skipped: 0; with at least one expression root: 55386.
- Harness wall time: load 239 ms, measurement 146528 ms, total 146767 ms.
- Production rebuild (`buildConstantWithSharing` on expanded roots, then `serConstant`) differs from `rawBytes`: **0** constants.
- Decode/encode roundtrip (`serConstant ∘ get`) differs from `rawBytes`: 0 constants.
- Compositional unshared size checked against `serConstant` of the real unshared Constant: 56615 equal, 0 different, 7 not checked (unshared roots > 16777216 bytes).
- `usageCount` (occ) checked against a brute-force walk of the fully expanded roots: 55390 equal, 0 different, 1232 not checked (unshared roots > 65536 bytes).
- Constants whose stored (heuristic) bytes exceed their unshared bytes: 600.
- Total `rawBytes.size`: 80208288; total unshared Constant bytes: 1070001199.

### Constants whose unshared size was not validated by serialization

| constant | kind | unshared bytes | stored bytes |
|---|---|---:|---:|
| `WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix` | defn | 85713622 | 39575 |
| `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 45668977 | 170285 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 32655304 | 154009 |
| `Vector.attach_append` | defn | 31288165 | 20827 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 27720363 | 156535 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 26030750 | 156976 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 17519911 | 142164 |

### Distributions over constants with at least one root (55386)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| `N` (distinct subterms) | 1 | 86 | 470 | 2015 | 27628 | 215.50 |
| `occ ≥ 2` (R1 only) | 0 | 40 | 240 | 1196 | 22467 | 115.78 |
| candidates (R1+R2: occ ≥ 2, size > 1) | 0 | 34 | 232 | 1187 | 22458 | 109.96 |
| candidates with size > 2 | 0 | 29 | 209 | 1138 | 22317 | 100.63 |
| candidates with size > 3 | 0 | 25 | 193 | 1113 | 22224 | 94.42 |
| current table size | 0 | 26 | 203 | 1096 | 22088 | 96.21 |
| `rawBytes.size` | 9 | 693 | 3081 | 11329 | 170285 | 1447.33 |
| unshared Constant bytes | 9 | 781 | 8587 | 193603 | 85713622 | 19318.14 |
| max telescope length | 0 | 6 | 10 | 17 | 95 | 6.59 |
| roots | 1 | 2 | 2 | 2 | 20 | 2.01 |

### Distributions over all processed constants (56622, projections included)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| `N` (distinct subterms) | 0 | 83 | 463 | 1994 | 27628 | 210.80 |
| `occ ≥ 2` (R1 only) | 0 | 39 | 236 | 1178 | 22467 | 113.25 |
| candidates (R1+R2: occ ≥ 2, size > 1) | 0 | 33 | 227 | 1169 | 22458 | 107.56 |
| candidates with size > 2 | 0 | 28 | 204 | 1117 | 22317 | 98.43 |
| candidates with size > 3 | 0 | 24 | 189 | 1092 | 22224 | 92.36 |
| current table size | 0 | 25 | 198 | 1075 | 22088 | 94.11 |
| `rawBytes.size` | 9 | 674 | 3043 | 11216 | 170285 | 1416.56 |
| unshared Constant bytes | 9 | 756 | 8290 | 188708 | 85713622 | 18897.27 |
| max telescope length | 0 | 6 | 9 | 17 | 95 | 6.45 |
| roots | 0 | 2 | 2 | 2 | 20 | 1.96 |

### Candidate-count buckets (R1+R2), constants with at least one root (55386), cumulative

| candidates | constants | share |
|---|---:|---:|
| ≤ 8 | 9532 | 17.2% |
| ≤ 16 | 16600 | 30.0% |
| ≤ 24 | 22267 | 40.2% |
| ≤ 32 | 26799 | 48.4% |
| ≤ 64 | 37298 | 67.3% |
| ≤ 128 | 45372 | 81.9% |
| > 128 | 10014 | 18.1% |

### Candidates with size > 3, constants with at least one root, cumulative

| candidates | constants | share |
|---|---:|---:|
| ≤ 8 | 14105 | 25.5% |
| ≤ 16 | 21566 | 38.9% |
| ≤ 24 | 27435 | 49.5% |
| ≤ 32 | 31682 | 57.2% |
| ≤ 64 | 40729 | 73.5% |
| ≤ 128 | 46981 | 84.8% |
| > 128 | 8405 | 15.2% |

### Ten constants with the most candidates

| # | constant | kind | `N` | `occ≥2` | candidates | size>2 | size>3 | table | stored B | unshared B | max telescope |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 27628 | 22467 | 22458 | 22317 | 22224 | 22088 | 170285 | 45668977 | 17 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 26943 | 19293 | 19283 | 19198 | 19178 | 19176 | 156535 | 27720363 | 11 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 26754 | 19102 | 19091 | 19005 | 18984 | 18983 | 156976 | 26030750 | 11 |
| 4 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 26494 | 19027 | 19017 | 18932 | 18912 | 18915 | 154009 | 32655304 | 11 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 24658 | 17300 | 17290 | 17201 | 17181 | 17184 | 142164 | 17519911 | 11 |
| 6 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 24507 | 17151 | 17140 | 17050 | 17029 | 17031 | 141015 | 16595260 | 11 |
| 7 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 18802 | 13290 | 13281 | 13193 | 13177 | 13168 | 109553 | 14841104 | 10 |
| 8 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 16156 | 11705 | 11692 | 11643 | 11602 | 11542 | 90971 | 3538954 | 24 |
| 9 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 19523 | 11465 | 11454 | 11370 | 11349 | 11349 | 104173 | 12235507 | 11 |
| 10 | `_private.Init.Data.Array.Extract.«0».Array.extract_add_left._proof_1_2` | defn | 13362 | 9625 | 9614 | 9530 | 9509 | 9502 | 77260 | 15196324 | 11 |

### Totals by ConstantInfo kind

| kind | constants | `rawBytes.size` | unshared bytes | stored/unshared | table entries | candidates | stored > unshared |
|---|---:|---:|---:|---:|---:|---:|---:|
| defn | 54358 | 79781914 | 1069502355 | 7.5% | 5306842 | 6064401 | 567 |
| recr | 500 | 240228 | 301965 | 79.6% | 18237 | 21747 | 29 |
| axio | 13 | 784 | 787 | 99.6% | 9 | 9 | 1 |
| quot | 4 | 311 | 312 | 99.7% | 1 | 1 | 0 |
| muts | 511 | 138609 | 149338 | 92.8% | 3415 | 4357 | 3 |
| iPrj | 501 | 18537 | 18537 | 100.0% | 0 | 0 | 0 |
| cPrj | 710 | 26980 | 26980 | 100.0% | 0 | 0 | 0 |
| rPrj | 3 | 111 | 111 | 100.0% | 0 | 0 | 0 |
| dPrj | 22 | 814 | 814 | 100.0% | 0 | 0 | 0 |
| **all** | 56622 | 80208288 | 1070001199 | 7.5% | 5328504 | 6090515 | 600 |

### Longest telescopes

- App spine: 95 (`Lean.Grind.Config.mk.inj`)
- Lam telescope: 95 (`Lean.Grind.Config.mk.noConfusion`)
- All telescope: 95 (`Lean.Grind.Config.mk.noConfusion`)

### Slowest constants in this harness (all steps above, per constant)

| constant | kind | ms | `N` | stored B |
|---|---|---:|---:|---:|
| `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 960 | 24507 | 141015 |
| `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 530 | 18802 | 109553 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 439 | 26754 | 156976 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 439 | 19523 | 104173 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_add_left._proof_1_2` | defn | 431 | 13362 | 77260 |
