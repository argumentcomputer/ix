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

## Maximal structural sharing (MSS) follow-up

This is a candidate linear-time canonical rule, measured on the same corpus through the
same harness (`mssBuild` in `Benchmarks/SharingStudy.lean`). It is the rule the
coordinator defined:

1. `deg(t)` is the number of incoming edges of `t` in the compact hash-consed DAG, counted
   with multiplicity (`App(x,x)` contributes 2), plus the number of roots equal to `t`.
   This is the compact indegree, not the expanded `occ` used in P1.5.
2. MSS stores exactly the terms with `deg ≥ 2` and unshared standalone size > 1. Every
   occurrence of a stored term, in roots and in other entries, becomes a Share.
3. The table is in priority topological order. Among stored terms whose stored body
   dependencies (stored terms reachable through unstored nodes) have been emitted, MSS emits
   the one with the largest `deg`, breaking ties by the smaller blake3 hash bytes. The
   emitted set is always closed under stored proper subterms (by induction on emission), so
   this is the same order as the "all stored proper subterms first" formulation.
4. Entries and roots are built with the production helpers
   `Ix.Sharing.buildSharingEntries` and `Ix.Sharing.rewriteExprs`, driven by the MSS order.
   The roots are put back into the ConstantInfo with the production cursor helpers
   (`updateRecursorRules`, `updateMutConsts`), and the constant is serialized with
   `serConstant`. All MSS byte counts below are exact serialized lengths.

### Checks

- **Plan §2 witnesses:**
  - `T2 → T2`: MSS gives **17 bytes**, exactly the plan's minimum
    `d200009117b0b001921700170000000100`. The heuristic gives 19 bytes, which are the
    plan's `d200009117b1b10291170000911700b0000100`, and unshared is 20.
  - `T16 → T16`: MSS gives **46**, the heuristic 81 and unshared 78. These are the three
    numbers in the plan's table.
  - The plan's closed `A → A → B → B` fixture: MSS gives 25, the plan's stated minimum, the
    same as the heuristic. Unshared is 28.
- **Every MSS constant (56,622) was checked:** decoded, re-encoded byte-for-byte, its table
  expanded, and its roots compared with the original expanded roots by exact structural
  equality (memoized on pointer pairs, not on hashes). There were **0 failures**.
- **Negative controls:** the check rejects the `T2 → T2` bytes against roots that differ in
  one leaf, and against the `T16 → T16` roots.

### Results over the 55,386 constants with at least one root

| encoding | total bytes | vs heuristic |
|---|---:|---:|
| heuristic (stored `rawBytes`) | 80,161,846 | |
| MSS | 68,547,873 | −11,613,973 (−14.5%) |
| unshared | 1,069,954,757 | +989,792,911 |

- **Per constant:**
  - MSS is smaller than the heuristic for 50,173 constants (90.6%), equal for 4,994
    (9.0%) and larger for 219 (0.4%).
  - Savings total 11,614,906 bytes; losses total 933 bytes.
  - The 219 losses have p50 3, p90 8, p99 27, max 50 and mean 4.26 bytes.
  - The savings have p50 53, p90 384, p99 3,083 and max 65,763 bytes.
- **Signed Δ = MSS − heuristic per constant:** min −65,763, p10 −348, p50 −45, p90 −1,
  p99 0, max +50.
- **MSS vs unshared:** MSS is larger than unshared for **0** constants. For comparison, the
  heuristic is larger than unshared for 600.
- **By kind (MSS as a share of heuristic bytes):** defn 85.5%, recr 83.2%, muts 96.6%,
  axio 99.4%, quot 100.0%.
- **Table sizes:**

  | table size | median | p90 | p99 | max | mean | total entries |
  |---|---:|---:|---:|---:|---:|---:|
  | MSS | 12 | 102 | 437 | 5,146 | 42.35 | 2,345,582 |
  | heuristic | 26 | 203 | 1,096 | 22,088 | 96.21 | 5,328,504 |

### Where MSS loses

These are derived from the CSV and describe correlations on this corpus. They are not a
measured decomposition of the losses.

- **Every** one of the 219 constants where MSS is larger has more than 8 MSS entries, so
  some of its Share references are 2 bytes wide. None of the losers has 8 or fewer MSS
  entries.
  - 217 of the 219 have more MSS entries than heuristic entries.
  - 116 have at most 8 heuristic entries but more than 8 MSS entries.
- Over all rooted constants, MSS has more entries than the heuristic for 4,484 constants.
- **Largest losses** (the ten are listed in the harness output below):
  - `noConfusionType` definitions of structure-like types, led by
    `Std.Packages.LinearPreorderOfOrdArgs.noConfusionType` (+50 bytes: 2,469 → 2,519, with
    57 heuristic entries vs 95 MSS entries);
  - `Float.exactlyRepresentablePowersOfTen` and its `eq_1` (+27 and +31);
  - `Lean.Grind.CommRing.Mon.revlex*` functions (+13 to +15).
- **Continuation-only MSS entries:**
  - *Definition used here:* a stored term that is never a root and whose every DAG
    occurrence is a same-family telescope continuation. That means the function child of
    an App for an App term, or the body of a Lam (All) for a Lam (All) term.
  - *Interpretation:* I read "function child of an App" as applying only when the stored
    term is itself an App, since only then does the Share cut a telescope. A non-App head
    under an App is not counted.
  - *Counts:* there are 567,668 continuation-only entries. Of these, 22,588 have an MSS
    entry body of ≤ 2 bytes after the Tag4 header, and 781 have an unshared payload of
    ≤ 2 bytes.
  - *Spread:* 11,192 rooted constants have at least one entry of the first kind (MSS
    payload ≤ 2). Only 41 of them are among the 219 losers; 11,112 are MSS wins and 39
    are ties.

### Caveats for MSS

- Ties in `deg` are broken by blake3 hash bytes, a stand-in for the structural IDs of §3.2.
  A different ID assignment can change the table order, and so which Shares are 2 bytes
  wide. It cannot change the stored set.
- MSS is not claimed to be optimal. It attains the plan's certified minimum on `T2 → T2` and
  the stated 25-byte minimum on `A → A → B → B`, and matches the 46-byte feasible
  improvement on `T16 → T16` (for which no minimum is certified). It was never larger than
  unshared on this corpus. Beyond that, these are plain byte counts compared with the
  heuristic and with unshared.

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
    --md $S/w3-results2.md --csv $S/sharing-minimum-measurements.csv"
#   -> exit 0; defaults --validate-max 16777216 --occ-check-max 65536
```

There were two full runs. The output below is from the second, which added MSS.

| run | harness-internal time | end to end |
|---|---|---|
| First (P1.5 only, commit `ecdd47ed`) | 146.8 s (0.24 s load + 146.5 s measuring) | about 152 s (18:24:07 → 18:26:39) |
| Second (P1.5 + MSS) | 185.2 s (0.23 s load + 185.0 s measuring) | 193.3 s measured by the shell, including `nix develop` and `lake exe` startup |

- The P1.5 sections of the second run's output are identical to the first run's except
  for the timing lines and the "slowest constants" table. This was checked with `diff`.
- The slowest single constant took 1.2 s in the second run, including MSS construction
  and its check. The harness is single-threaded.

The per-constant CSV is 7,051,432 bytes (56,622 rows plus a header), which is too large to
track here. It is kept at
`/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/sharing-minimum-measurements.csv`.
Its columns are:

```text
addr (first 16 hex digits), name, kind, members (muts: i/c/r/d counts), roots, N,
occ_ge2, cand, cand_gt2, cand_gt3, table, raw_bytes, unshared_bytes, rebuild_ok,
roundtrip_ok, unshared_validated, occ_checked, max_app, max_lam, max_all, us (harness µs),
mss_bytes, mss_table, mss_ok, mss_cont, mss_cont_p2, mss_cont_p2u
```

Rerunning the command above regenerates it.

---

The rest of this document is the harness's `--md` output from the second run, unedited.

## Results

- Corpus: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe` (195387870 bytes), 56622 stored constants (distinct addresses), 66621 names.
- Constants processed: 56622; skipped: 0; with at least one expression root: 55386.
- Harness wall time: load 229 ms, measurement 185013 ms, total 185242 ms.
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
| `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 1202 | 24507 | 141015 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 652 | 26754 | 156976 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 628 | 24658 | 142164 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 593 | 26494 | 154009 |
| `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 581 | 18802 | 109553 |

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

- MSS built for 56622 constants; decode, re-encode (byte-identical), table expansion and exact pointer-memoized structural equality of the expanded roots with the original expanded roots: 56622 ok, **0** failed.

### Totals over the 55386 constants with at least one root

| encoding | total bytes | vs heuristic |
|---|---:|---:|
| heuristic (stored `rawBytes`) | 80161846 | |
| MSS | 68547873 | -11613973 (−14.5%) |
| unshared | 1069954757 | 989792911 |

### MSS − heuristic per constant

| outcome | constants | share | bytes |
|---|---:|---:|---:|
| MSS smaller | 50173 | 90.6% | −11614906 |
| equal | 4994 | 9.0% | 0 |
| MSS larger | 219 | 0.4% | +933 |

- Losses (MSS − heuristic) over the 219 larger constants: p50 3, p90 8, p99 27, max 50, mean 4.26.
- Savings (heuristic − MSS) over the 50173 smaller constants: p50 53, p90 384, p99 3083, max 65763, mean 231.50.
- Signed Δ = MSS − heuristic over all 55386 rooted constants: min -65763, p1 -2886, p10 -348, p50 -45, p90 -1, p99 0, max 50.
- MSS larger than unshared: 0 constants, total excess 0 bytes, max 0. (Heuristic larger than unshared: 600.)

### Table sizes (rooted constants)

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| MSS table size | 0 | 12 | 102 | 437 | 5146 | 42.35 |
| heuristic table size | 0 | 26 | 203 | 1096 | 22088 | 96.21 |
| MSS continuation-only entries | 0 | 2 | 25 | 132 | 1950 | 10.25 |
| … with MSS entry payload ≤ 2 | 0 | 0 | 1 | 5 | 16 | 0.41 |
| … with unshared payload ≤ 2 | 0 | 0 | 0 | 0 | 9 | 0.01 |

- Total MSS entries 2345582; heuristic entries 5328504.
- Continuation-only entries (never a root; every occurrence is the function child of an App for an App term, or the body of a Lam/All for a Lam/All term): 567668 in total; with MSS entry payload ≤ 2: 22588; with unshared payload ≤ 2: 781.
- Constants with at least one continuation-only entry of MSS payload ≤ 2: 11192; of these, MSS larger than heuristic: 41, equal: 39, smaller: 11112.
- Of the 219 constants where MSS is larger, 41 have such an entry; of the 50173 where MSS is smaller, 11112.

### MSS by ConstantInfo kind (rooted constants)

| kind | constants | heuristic B | MSS B | unshared B | MSS/heuristic | MSS smaller | equal | MSS larger |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| defn | 54358 | 79781914 | 68212975 | 1069502355 | 85.5% | 49405 | 4737 | 216 |
| recr | 500 | 240228 | 199955 | 301965 | 83.2% | 494 | 6 | 0 |
| axio | 13 | 784 | 779 | 787 | 99.4% | 3 | 10 | 0 |
| quot | 4 | 311 | 311 | 312 | 100.0% | 0 | 4 | 0 |
| muts | 511 | 138609 | 133853 | 149338 | 96.6% | 271 | 237 | 3 |

### Ten largest MSS losses (MSS − heuristic)

| # | constant | kind | heuristic B | MSS B | Δ | unshared B | heuristic table | MSS table | cont. p≤2 |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `Std.Packages.LinearPreorderOfOrdArgs.noConfusionType` | defn | 2469 | 2519 | 50 | 2836 | 57 | 95 | 0 |
| 2 | `Float.exactlyRepresentablePowersOfTen.eq_1` | defn | 1448 | 1479 | 31 | 1663 | 9 | 26 | 0 |
| 3 | `Float.exactlyRepresentablePowersOfTen` | defn | 1332 | 1359 | 27 | 1545 | 8 | 23 | 0 |
| 4 | `Std.Packages.PreorderOfLEArgs.noConfusionType` | defn | 1684 | 1710 | 26 | 1866 | 44 | 72 | 0 |
| 5 | `Lean.Data.AC.Context.noConfusionType` | defn | 623 | 644 | 21 | 683 | 8 | 22 | 0 |
| 6 | `Std.PreorderPackage.noConfusionType` | defn | 556 | 573 | 17 | 612 | 8 | 19 | 0 |
| 7 | `Ix.6f88b4848716a9da0ed22405a07425464335ba158bd5650c013ff4578a796818.Std.Packages.LinearPreorderOfOrdArgs` | muts | 1385 | 1400 | 15 | 1485 | 19 | 33 | 0 |
| 8 | `Lean.Grind.CommRing.Mon.revlexFuel._sunfold` | defn | 919 | 934 | 15 | 938 | 8 | 17 | 0 |
| 9 | `Lean.Grind.CommRing.Mon.revlexFuel._unsafe_rec` | defn | 887 | 902 | 15 | 906 | 8 | 17 | 0 |
| 10 | `Lean.Grind.CommRing.Mon.revlexWF._unsafe_rec` | defn | 760 | 773 | 13 | 777 | 8 | 15 | 0 |

### Ten largest MSS wins (heuristic − MSS)

| # | constant | kind | heuristic B | MSS B | Δ | unshared B | heuristic table | MSS table | cont. p≤2 |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 170285 | 104522 | -65763 | 45668977 | 22088 | 4874 | 0 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 156535 | 104331 | -52204 | 27720363 | 19176 | 5136 | 0 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 156976 | 105389 | -51587 | 26030750 | 18983 | 5146 | 0 |
| 4 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 154009 | 102666 | -51343 | 32655304 | 18915 | 4919 | 0 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 142164 | 97145 | -45019 | 17519911 | 17184 | 4703 | 0 |
| 6 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 141015 | 96716 | -44299 | 16595260 | 17031 | 4678 | 0 |
| 7 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 109553 | 72208 | -37345 | 14841104 | 13168 | 3236 | 0 |
| 8 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 90971 | 53900 | -37071 | 3538954 | 11542 | 2712 | 1 |
| 9 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 104173 | 76309 | -27864 | 12235507 | 11349 | 3640 | 0 |
| 10 | `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.defaultImplementation` | defn | 70419 | 43015 | -27404 | 4186174 | 9332 | 2407 | 1 |
