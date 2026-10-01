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

## Uniform-reference-width classification follow-up

This measurement tests whether an exact algorithm for the uniform-reference-width cost
model could be tractable. The model fixes a Share width `w ∈ {1, 2, 3}`, charges `w`
bytes for every Share and ignores the table-count prefix. It is implemented in
`classify`, in `Benchmarks/SharingStudy.lean`.

**Candidates.** The candidates are the subterms with compact `deg ≥ 2` and unshared size
> 1. This is exactly the MSS stored set: 2,345,582 candidates over the rooted constants,
the same total the MSS builder produced, computed independently.

**Classification.** Each candidate is classified with the gain
`g(n, H, b) = (n−1)·b + (H−1)·hdr − n·w`:

| class | condition |
|---|---|
| CERTAIN-STORED | `g(deg, headdeg, payloadMin) > 0` |
| CERTAIN-EXCLUDED | `g(occ, occ, payloadMax) < 0`, or a leaf with `(occ−1)·size < occ·w` |
| UNCERTAIN | neither |

**Components.** Two uncertain nodes are in one component if a directed DAG path joins
them whose intermediate nodes are not certain-stored; components are the transitive
closure of that relation.

### Change note: corrected `payloadMin`

The first run of this section used the coordinator's first specification of
`payloadMin`: scalar bytes plus 1 byte per child. At `w ≥ 2` that bound is too weak,
because a stored child costs `w` bytes as a reference, not 1. The numbers below use the
corrected specification, a width-aware recursive lower bound computed bottom-up on the
compact DAG for each `w`:

| node | `payloadMin` | `inlineMin` | `cmin` (head use) | `cminCont` (continuation use) |
|---|---|---|---|---|
| leaf | — | its size | `min(w, size)` if a candidate, else `size` | — |
| internal | `scalar + Σ childCost` | `hdr + payloadMin` | `min(w, inlineMin)` if a candidate, else `inlineMin` | `min(w, payloadMin)` if a candidate, else `payloadMin` |

- `childCost` is `cmin` for a head-position child and `cminCont` for a
  continuation-position child: the function child of an App when that child is an App,
  or the body of a Lam (All) when that body is a Lam (All).
- The certain-excluded test, the component definition and everything else are unchanged.
- The previous numbers were reported in commit `0b2ccbb3`:

  | w | certain-stored (previous) | uncertain (previous) | largest component, median / p90 / p99 / max (previous) |
  |---:|---:|---:|---|
  | 1 | 1,698,177 | 647,405 | 1 / 4 / 8 / 87 |
  | 2 | 408,749 | 1,586,970 | 5 / 46 / 253 / 3,585 |
  | 3 | 23,501 | 1,751,949 | 4 / 65 / 361 / 5,059 |

  The certain-excluded counts are unchanged: 0, 349,863 and 570,132.

### Implementation notes and interpretations

- **`headdeg`.** I kept my non-literal reading. An occurrence is a non-head only when `t`
  is an App in the function position of an App, or a Lam (All) in the body position of a
  Lam (All). Roots are heads.
  - The same rule decides continuation positions in `payloadMin`.
  - The literal reading ("NOT (function child of an App)" for any `t`) changes the class of
    100, 100 and 92 candidates for w = 1, 2 and 3 respectively, out of 2,345,582.
- **`scalar`:** App 0; Lam, All and Let 1 (the contract byte; the Let flags, ≤ 3, sit in
  its one-byte Tag4 header); Prj `Tag0(type index)`.
- **`payloadMax`** is the unshared size minus the node's own Tag4 header. For App, Lam and
  All that is the header of the maximal telescope it heads.
- **Header approximation.** `hdr = 1` for every internal node, although a Prj with field
  index ≥ 8, or a telescope of 8 or more nodes, has a 2-byte header. As a lower bound this
  is on the safe side.
- **Arithmetic** is exact (`Nat`/`Int`). `occ` is not capped.
- **Sanity checks:** no candidate has `payloadMin > payloadMax`, and none met both certain
  conditions, for any `w`.
- **Component check.** The fast union-find computation agrees with a literal brute force
  (a walk from every uncertain node through all non-certain-stored nodes) on every rooted
  constant with at most 1,000 DAG nodes (53,652 of 55,386), with 0 differences for each
  `w`. The first version of the fast computation merged components through a shared leaf;
  the `A → A → B → B` witness and the brute force exposed it, and it was fixed before any
  numbers were reported.
- **Witnesses**, checked by hand (certain-stored / certain-excluded / uncertain / largest
  component, for w = 1 | 2 | 3). The harness output matches.
  - **`T2 → T2`: 1/0/0/0 | 1/0/0/0 | 0/0/1/1.** The one candidate is `T2 = All(P, T1)`, with
    `deg 2`, `headdeg 1` (its body occurrence continues the root's All telescope).
    - `T1` is not a candidate and is a continuation child, so it costs its payload 3.
    - So `payloadMin(T2) = 1 + 1 + 3 = 5` and `g = 5 − 2w`, which is 3 and 1 for w = 1 and
      2 (stored) and −1 for w = 3.
    - The upper bound at w = 3 is `g(2, 2, 5) = 0`, which is not negative, so `T2` is
      uncertain.
  - **`T16 → T16`: stored for every w.** `payloadMin(T16) = 33` and `g = 33 − 2w > 0`.
  - **`A → A → B → B`: 2/0/0/0 | 0/0/2/1 | 0/2/0/0.**
    - `A` has `headdeg 2` and `payloadMin 3`, so `g = 4 − 2w`.
    - `B` has `headdeg 1` and `payloadMin 3`, so `g = 3 − 2w`.
    - The upper bounds `g(2, 2, 3) = 4 − 2w` are 0 at w = 2 (uncertain) and −2 at w = 3
      (excluded).
    - `A` and `B` are not joined by a DAG path, so the largest component at w = 2 is 1.

### Results over the 55,386 constants with at least one root

**Class totals and counts of uncertain nodes per constant:**

| w | certain-stored | certain-excluded | uncertain | uncertain per constant: median / p90 / p99 / max |
|---:|---:|---:|---:|---|
| 1 | 1,887,527 (80.5%) | 0 | 458,055 (19.5%) | 2 / 21 / 95 / 970 |
| 2 | 1,504,278 (**64.1%**) | 349,863 (14.9%) | 491,441 (21.0%) | 3 / 22 / 84 / 736 |
| 3 | 1,276,154 (**54.4%**) | 570,132 (24.3%) | 499,296 (21.3%) | 2 / 22 / 98 / 978 |

Percentages are of the 2,345,582 candidates.

**Largest uncertain component per constant:**

| w | median / p90 / p99 / max | ≤ 8 | ≤ 16 | ≤ 32 | > 32 |
|---:|---|---:|---:|---:|---:|
| 1 | 1 / 2 / 4 / 45 | 55,332 (99.9%) | 55,382 | 55,384 | 2 |
| 2 | 1 / 3 / 5 / 44 | 55,328 (99.9%) | 55,384 | 55,385 | 1 |
| 3 | 1 / 3 / 6 / 44 | 55,228 (99.7%) | 55,378 | 55,385 | 1 |

**Constants by number of uncertain nodes (cumulative except the first and last columns):**

| w | = 0 | ≤ 8 | ≤ 16 | ≤ 32 | > 32 |
|---:|---:|---:|---:|---:|---:|
| 1 | 13,486 | 43,174 | 48,357 | 52,353 | 3,033 |
| 2 | 11,593 | 39,615 | 47,353 | 52,492 | 2,894 |
| 3 | 14,878 | 40,386 | 47,612 | 52,174 | 3,212 |

- **Why w = 1 has no certain-excluded candidates.** At w = 1 the maximal-gain bound is
  never negative when `occ ≥ 2`:
  - an internal node has `(occ−1)·(payloadMax + 1) − occ ≥ 2·occ − 3 > 0`;
  - a leaf of size ≥ 2 has `(occ−1)·size − occ ≥ occ − 2 ≥ 0`.
- **The largest components** are 45 at w = 1 and 44 at w = 2 and 3, all in
  `Lean.Grind.Config.mk.injEq`. The next are `Lean.Meta.Simp.Config.mk.injEq` (30–31) and
  `UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` (35 at w = 1, 31 at w = 3). The ten
  largest for each `w` are in the harness output below.

### Share-width loss in the current stored encoding

This part does not depend on `payloadMin` and is unchanged from the previous run. Share
references are counted syntactically in the stored roots and table entries (the current
heuristic encoding). The largest stored table has 22,088 entries, so every index ≥ 256
costs 3 bytes today.

| stored table entries | constants | refs to 0–7 (1 B now) | refs to 8–255 (2 B) | refs to ≥ 256 (3 B) | loss under uniform width |
|---|---:|---:|---:|---:|---|
| 9–255 | 37,610 | 776,978 | 3,298,554 | 0 | w = 2: **776,978 B** |
| > 255 | 4,335 | 202,727 | 2,795,056 | 3,328,853 | w = 3: 2·202,727 + 2,795,056 = **3,200,510 B** |
| 1–8 (extra) | 11,367 | 119,925 | 0 | 0 | not requested |

- **Scale:** the corpus stores 80,208,288 bytes, with 10,522,093 Share references.
- **Derived arithmetic:** the Share references occupy 23,273,409 bytes. The w = 2 loss is
  0.97% of the stored bytes, the w = 3 loss 3.99%, and the two together 3,977,488 bytes
  (4.96%).

## Share-width schemes on the MSS encoding follow-up

This section prices the Share references of each rooted constant's MSS encoding under
seven width schemes. It is implemented in `schemeReport`.

- **References.** Every occurrence of an MSS entry is a Share. The harness counts the
  Share nodes in the materialized MSS table and roots, grouped by index. For all 55,386
  rooted constants the count equals `Σ deg(t)` over the MSS entries, which confirms
  `refcount(t) = deg(t)`.
- **The seven schemes:**

  | scheme | Share width |
  |---|---|
  | A | the current tiers, by index in MSS priority order: 1 byte below 8, 2 below 256, 3 below 65,536. This is the real MSS encoding. |
  | B | one width per constant: 2 bytes (11-bit index) if the MSS entry count, which is the candidate count, is ≤ 2048; otherwise 3 bytes (19-bit index) |
  | C | as B, but 1 byte (3-bit index) when the entry count is ≤ 8 |
  | D | one width per constant, with the Share tag byte's whole low nibble holding index bits: 1 byte (4-bit index) for ≤ 16 entries, 2 bytes (12-bit) for ≤ 4,096, 3 bytes (20-bit) above |
  | E | position tiers with a nibble escape, by index in MSS priority order: 1 byte for index < 15, 2 bytes for index < 15 + 4,096 = 4,111, 3 bytes beyond. **Not realizable:** with a 4-bit Share flag, the first byte has only 4 bits and a "more bytes follow" marker costs some of them, so 2 bytes carry at most 10–11 index bits. It is kept for reference only. |
  | F | realizable position tiers with two marker bits (3-bit direct index, or 2 bits + 1 byte, or 2 bits + 2 bytes): 1 byte for index < 8, 2 bytes for index < 8 + 1,024 = 1,032, 3 bytes beyond |
  | G | realizable position tiers with nibble values 14 and 15 as escapes: 1 byte for index < 14, 2 bytes for index < 14 + 256 = 270, 3 bytes beyond |

- **Constant bytes under a scheme** are `MSS bytes − refbytes(A) + refbytes(scheme)`.
  Nothing else in the encoding changes.

### Results over the 55,386 rooted constants

There are 9,297,007 Share references in total. 20 constants have more than 2,048 MSS
entries and so take width 3 under B and C. 22,270 have at most 8 entries and take
width 1 under C.

| scheme | reference bytes | MSS constant bytes | Δ vs A | Δ / MSS total | Δ / heuristic total |
|---|---:|---:|---:|---:|---:|
| A (index tiers) | 17,568,850 | 68,547,873 | 0 | | |
| B (2 or 3 per constant) | 18,990,396 | 69,969,419 | +1,421,546 | +2.07% | +1.77% |
| C (1, 2 or 3 per constant) | 18,724,875 | 69,703,898 | +1,156,025 | +1.69% | +1.44% |
| D (1, 2 or 3 per constant, nibble index) | 18,207,733 | 69,186,756 | +638,883 | +0.93% | +0.80% |
| E (index tiers < 15 / < 4,111 / beyond; not realizable) | 15,442,797 | 66,421,820 | −2,126,053 | −3.10% | −2.65% |
| F (index tiers < 8 / < 1,032 / beyond) | 16,577,564 | 67,556,587 | **−991,286** | −1.45% | −1.24% |
| G (index tiers < 14 / < 270 / beyond) | 16,741,559 | 67,720,582 | **−827,291** | −1.21% | −1.03% |

The MSS total is 68,547,873 bytes and the heuristic total is 80,161,846 bytes (rooted
constants). Derived arithmetic: the MSS total stays below the heuristic total by 12.71% under B
(1 − 69,969,419 / 80,161,846), 13.05% under C, 13.69% under D, 17.14% under E, 15.72% under F and 15.52% under G.

**Per constant:**

| comparison | better | equal | worse |
|---|---:|---:|---:|
| B vs A | 829 | 555 | 54,002 |
| C vs A | 829 | 22,271 | 32,286 |
| D vs A | 9,773 | 22,271 | 23,342 |
| E vs A | 33,116 | 22,270 | 0 |
| F vs A | 1,352 | 54,034 | 0 |
| G vs A | 33,116 | 22,270 | 0 |

- All 829 constants that improve under B are among the 4,335 below.
- **Largest losses under B:**
  - `Nat.digitChar_iff_aux` +17,274: 2,763 entries, so width 3; A 43,371 → B 60,645
    reference bytes.
  - `…ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` +13,382 (4,874 entries).
  - `…Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` +10,675
    (2,712 entries).
- **Largest gains under B:** all have 1,600–1,900 entries, just below the 2,048 cut.
  - `…Vector.extract_reverse._proof_1` −7,579 (1,908 entries).
  - `…Array.toList_extract._proof_1_1` −6,803.
  - `…Int.max_min_distrib_left._proof_1_1` −6,743.
- The ten of each are in the harness output below.

### Restricted to the 4,335 constants whose current heuristic table exceeds 255 entries

- **Totals:** their MSS bytes are 25,359,218 and their heuristic bytes 33,341,195. Their
  MSS entry counts range from 44 to 5,146, and 20 of them have more than 2,048 entries.
- **Reference bytes:** A 11,525,602 and B 11,441,534, so B − A = **−84,068 bytes**. That is
  −0.33% of their MSS bytes and −0.25% of their heuristic bytes.
- **Per constant, B vs A:** better 829, equal 1, worse 3,505.

### Scheme D in detail

- **Width classes under D:**

  | width | entries | constants |
  |---|---|---:|
  | 1 byte | ≤ 16 | 31,200 |
  | 2 bytes | 17–4,096 | 24,180 |
  | 3 bytes | > 4,096 | 6 |

- **Equal constants:** the 22,271 constants equal under D are the same count as under C:
  the 22,270 constants with at most 8 entries, plus 1. For a constant with 9–16 entries,
  D is never worse than A.
- **Largest losses under D** are the six constants with more than 4,096 entries:
  - `…ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` +13,382 (4,874 entries);
  - `…Vector.extract_append._proof_1` +7,936;
  - `…Vector.extract_extract._proof_1` +7,488;
  - `…Array.extract_append._proof_1_1` +6,363;
  - two more `extract_append_extract` proofs, at +5,867 and +5,727.

  After them come constants with 160–360 entries and many references to indices below 8,
  such as `…Nat.digitChar_ne.match_1_1` (+1,072, 199 entries).
- **Largest gains under D** come from constants with roughly 1,800–3,700 entries, which
  pay 3 bytes under A for every index ≥ 256:
  - `…Array.extract_extract._proof_1_1` −17,041 (3,640 entries);
  - `…Int.add_one_tdiv._proof_1_1` −15,320 (3,236);
  - `…Vector.extract_add_left._proof_1` −12,595 (2,854).
- The ten of each are in the harness output below.

**D restricted to the 4,335 constants whose heuristic table exceeds 255 entries:**

- Width classes: 0 at 1 byte, 4,329 at 2 bytes, 6 at 3 bytes.
- Reference bytes: A 11,525,602 and D 11,226,247, so D − A = **−299,355 bytes**. That is
  −1.18% of their MSS bytes (25,359,218) and −0.90% of their heuristic bytes
  (33,341,195).
- D vs A: better 843, equal 1, worse 3,491.

### Scheme E in detail

Scheme E is not realizable as specified (see the scheme table above). Its numbers are kept
only as a reference point for F and G.

- **Counting.** Share nodes are counted on the materialized MSS encodings in E's index
  buckets (< 15, 15–4,110, ≥ 4,111). For every rooted constant the three buckets sum to
  the same Share count as A's buckets.
- **E is never worse than A for any constant.** At every index E's width is at most A's:

  | indices | A | E |
  |---|---:|---:|
  | 0–7 | 1 | 1 |
  | 8–14 | 2 | 1 |
  | 15–255 | 2 | 2 |
  | 256–4,110 | 3 | 2 |
  | 4,111–65,535 | 3 | 3 |

  The measured counts agree: 33,116 better, 22,270 equal and 0 worse.
  - The 22,270 equal constants are exactly those with at most 8 MSS entries (checked from
    the CSV), which only use indices below 8.
  - Every constant with more than 8 entries references index 8, since every entry has
    `deg ≥ 2`, so it gains at least 2 bytes.
- **"Largest losses".** Because there are no losses, the harness's list of ten largest
  losses under E is ten ties at 0, in name order.
- **Largest gains under E** come from the big `Init.Data.{Vector,Array}.Extract` proofs,
  which have most of their references at indices 15–4,110:
  - `…Array.extract_append._proof_1_1` −21,634 (5,146 entries; 957 / 26,083 / 4,383 refs
    in E's buckets);
  - `…Vector.extract_append_extract._proof_1` −21,571;
  - `…Array.extract_append_extract._proof_1_1` −21,432.

  The ten are in the harness output below.
- **Totals:** E saves 2,126,053 bytes against the real MSS encoding. That is 3.10% of the
  MSS total and 2.65% of the heuristic total. Under E the MSS total is 17.14% below the
  heuristic total (derived: 1 − 66,421,820 / 80,161,846).

### Schemes F and G in detail (realizable position tiers)

- **Counting.** Share nodes are counted on the materialized MSS encodings in each scheme's
  index buckets: F < 8 / 8–1,031 / ≥ 1,032, and G < 14 / 14–269 / ≥ 270. For every
  rooted constant the buckets of each scheme sum to the same Share count as A's.
- **No constant is worse than A under F or under G.** The harness reports 0 worse
  constants and a largest per-constant Δ of 0 for both. This matches the widths:

  | indices | A | F | G |
  |---|---:|---:|---:|
  | 0–7 | 1 | 1 | 1 |
  | 8–13 | 2 | 2 | 1 |
  | 14–255 | 2 | 2 | 2 |
  | 256–269 | 3 | 2 | 2 |
  | 270–1,031 | 3 | 2 | 3 |
  | ≥ 1,032 | 3 | 3 | 3 |

- **F:** saves 991,286 bytes (−1.45% of the MSS total, −1.24% of the heuristic total).
  - 1,352 constants are better and 54,034 equal.
  - The better constants are exactly the 1,352 rooted constants with at least 257 MSS
    entries (checked from the CSV). Only those use indices 256–1,031.
  - Largest gains: `…Array.extract_append._proof_1_1` −6,490,
    `…Vector.extract_extract._proof_1` −6,279 and `…Int.add_one_tdiv._proof_1_1` −6,208.
- **G:** saves 827,291 bytes (−1.21% of the MSS total, −1.03% of the heuristic total).
  - 33,116 constants are better and 22,270 equal.
  - The better constants are exactly the rooted constants with more than 8 MSS entries:
    all of them reference indices 8–13, which drop from 2 bytes to 1.
  - Largest gains: `…Array.extract_extract._proof_1_1` −1,853,
    `…Vector.extract_reverse._proof_1` −1,265 and
    `…Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` −1,146.
- **MSS vs heuristic** (derived): under F the MSS total is 15.72% below the heuristic total
  (1 − 67,556,587 / 80,161,846), and under G 15.52% below.
- The ten largest gains for each scheme are in the harness output below.

## Exact uniform-width optimizer (W1) follow-up

This section runs W1's exact optimizer for the uniform-width cost model over the corpus.

- **Code.** The worktree was updated with `git merge ix-sharing`, a fast-forward to
  `bd3e7482` that brought in W1's `Ix/Sharing/Exact/*` and W2's Rust code. My three files
  merged unchanged.
- **Call.** For every rooted constant and `w ∈ {1, 2, 3}` the harness calls
  `Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing (constantInfoRoots c.info) limits`.
- **Limits:**
  - `maxStates` = 2^20 = 1,048,576, the suggested size of about 10^6;
  - everything else at W1's defaults: `maxCostEvals` 2^30, `maxNodes` 2^20, `maxDepth`
    2^14, `maxExprVisits` 2^26, `maxMaterialize` 2^26, `maxOutputBytes` 2^28.
- **Processing each certified result:**
  - the roots are placed with the production cursor helpers and serialized with
    `serConstant`, which gives the real length under the current Tag4 tiers;
  - the bytes are decoded, re-encoded, expanded and compared exactly with the original
    expanded roots;
  - the real length is checked to equal the fixed bytes plus W1's `variableBytes`;
  - the same table and roots are priced under scheme F widths;
  - the model length is the fixed bytes plus W1's `modelBytes`.
- **Wall time** is the optimizer call alone, single-threaded.

### Checks (every certified run, every `w`)

- **Outputs:** 0 decode/expand failures. The real length equals fixed + `variableBytes`
  in every case, and W1's distinct-subterm count equals this harness's `N` in every case.
- **Classes agree with an independent reimplementation.** The harness reimplements W1's
  classification on its own blake3 DAG (`classifyW1Mode`), with W1's rules:
  - certain-excluded: `(occ−1)·size < occ·w`, for every term;
  - candidates: `deg ≥ 2` and not certain-excluded;
  - bounds: W1's `inl⁻` / merged bounds with exact headers;
  - certain-stored: `g ≥ 2` with W1's three gain formulas;
  - components: as defined above.

  W1's reported counts of certain-stored, certain-excluded, uncertain and low-degree
  terms, its number of components and its largest component equal the reimplementation
  for **every** certified constant: 55,294, 55,358 and 55,338 at w = 1, 2 and 3, with 0
  differences.
- **Lower bound.** No measured encoding (heuristic, MSS, the three uniform outputs) is
  shorter than the w = 1 model optimum for any of the 55,263 constants certified at all
  three widths.

### Certification and failures

| w | certified | failed | of which `states` (2^20) | of which `costEvals` (2^30) |
|---:|---:|---:|---:|---:|
| 1 | 55,294 | 92 | 90 | 2 |
| 2 | 55,358 | 28 | 26 | 2 |
| 3 | 55,338 | 48 | 46 | 2 |

- **The two `costEvals` failures** at every width are `Lean.Grind.Config.mk.injEq`
  (largest component 45 / 44 / 44 under W1's definitions) and
  `Lean.Meta.Simp.Config.mk.injEq` (57 / 57 / 61). These six runs are the six slowest
  overall, at 83–108 s each.
- **Where the limit bites.** Joining the run-9 certification with the run-10
  reimplementation (from the CSVs):
  - every failing constant has a largest component of **at least 20**, with medians of
    25 / 23 / 24 and maxima of 57 / 57 / 61;
  - **every** constant with a component of 22 or more failed (83 / 24 / 33);
  - at 20–21, 17 / 4 / 3 constants certified;
  - the largest certified component is 21 / 20 / 20.

  So with `maxStates` = 2^20, the limit sits at a largest component of 20–21.

### Bytes, over each width's certified constants

| w | heuristic | MSS | uniform real (current tiers) | uniform, scheme F widths | uniform model | unshared |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 78,855,708 | 67,563,348 | 66,737,821 (−1.22% vs MSS) | 66,047,771 (−2.24%) | 59,469,841 | 987,599,557 |
| 2 | 79,830,766 | 68,297,958 | 67,593,621 (−1.03%) | 66,954,321 (−1.97%) | 68,379,047 | 1,038,467,344 |
| 3 | 79,849,102 | 68,301,284 | 68,216,736 (−0.12%) | 67,644,231 (−0.96%) | 74,603,766 | 1,061,642,946 |

The uniform real lengths are 15.37%, 15.33% and 14.57% below the heuristic on the same
constants.

**Per constant, uniform output (real length) vs MSS:**

| w | better | equal | worse | gains p50 / p90 / max | losses p50 / p90 / max |
|---:|---:|---:|---:|---|---|
| 1 | 31,245 | 23,833 | 216 | 10 / 39 / 2,670 | 1 / 4 / 46 |
| 2 | 21,751 | 6,098 | 27,509 | 14 / 61 / 5,252 | 5 / 14 / 929 |
| 3 | 12,687 | 3,526 | 39,125 | 14 / 75 / 5,398 | 9 / 29 / 1,523 |

- **Against the heuristic (better / equal / worse):** 50,302 / 4,938 / 54 at w = 1;
  46,968 / 3,003 / 5,387 at w = 2; 43,719 / 2,683 / 8,936 at w = 3.
- **Largest gains and losses vs MSS** (the ten of each per width are in the harness output
  below):
  - w = 1: gain `…Array.extract_append._proof_1_1` −2,670 (105,389 → 102,719); loss
    `Lean.Meta.Simp.Config.mk.inj` +46 (1,984 → 2,030).
  - w = 2: gain the same constant −5,252; loss `Std.Iter.step_flatMapAfterM` +929.
  - w = 3: gain `…Vector.extract_append_extract._proof_1` −5,398; loss
    `Std.Iter.step_flatMapAfterM` +1,523.

### Wall time (optimizer call, µs)

| w | median | p90 | p99 | max |
|---:|---:|---:|---:|---:|
| 1 | 249 | 2,964 | 182,154 | 108,188,764 |
| 2 | 210 | 2,517 | 47,081 | 98,799,418 |
| 3 | 179 | 2,578 | 58,856 | 103,226,807 |

The total over all 166,158 runs is 6,875,358 ms (1 h 55 min). All ten slowest runs are
failures: the six `costEvals` runs above, then four `states` failures at w = 1
(51–63 s).

### Lower-bound gap against the w = 1 model optimum

Under the current tiers every Share costs at least 1 byte. So, per W1's argument, the
w = 1 model optimum lower-bounds every tiered encoding. Over the 55,263 constants
certified at all three widths, Σ model(w = 1) = 59,370,988:

| encoding | Σ bytes | Σ (bytes − model w=1) | % of Σ model |
|---|---:|---:|---:|
| heuristic | 78,696,174 | 19,325,186 | +32.55% |
| MSS | 67,438,618 | 8,067,630 | +13.59% |
| uniform w = 1 output | 66,615,107 | **7,244,119** | +12.20% |
| uniform w = 2 output | 66,778,657 | 7,407,669 | +12.48% |
| uniform w = 3 output | 67,406,916 | 8,035,928 | +13.54% |
| best of these per constant | 66,331,917 | 6,960,929 | +11.72% |

### W1's classes vs this harness's own classification

Over the 55,263 constants certified at all widths. The two classifications are not
expected to agree, because the definitions differ:
- W1 uses `g ≥ 2` for certain-stored (mine uses `g > 0`).
- W1 applies `(occ−1)·size < occ·w` to every term (mine applies the `payloadMax` test to
  candidates only).
- W1 drops certain-excluded terms from the "may be stored" set when computing bounds.
- W1 uses exact header sizes.

Where the definitions coincide, that is with my reimplementation of W1's rules, they agree
exactly (above).

| w | own certain-stored | W1 | own uncertain | W1 | own max component | W1 |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1,842,180 | 1,437,377 | 444,030 | 848,833 | 16 | 21 |
| 2 | 1,460,911 | 1,189,917 | 480,307 | 751,301 | 14 | 20 |
| 3 | 1,235,457 | 1,063,687 | 486,863 | 658,633 | 19 | 20 |

## Integer repricing (TagN) follow-up

This section reprices every integer of the stored (heuristic) encoding of all 56,622
constants under three replacement codes. It is implemented in `ladConstant` and
`tagNReport`.

- **The walk.** The harness walks each encoding exactly as `putConstant`, `putExpr` and
  `putUniv` write it: App/Lam/All telescope counts are taken as the writers collect them,
  and a successor chain is one `Tag2`. Each integer is assigned to a field class.
- **The codes:**

  | code | replaces | 1 byte | 2 bytes | 3 bytes | 5 bytes | 9 bytes |
  |---|---|---|---|---|---|---|
  | TagN | every `Tag4` | below 8 | below 8 + 1024 | below 1032 + 65536 | below that + 2^32 | beyond |
  | TagN-byte (working name) | every `Tag0` | below 128 | below 128 + 16384 | below 16512 + 65536 | below that + 2^32 | beyond |
  | Tag2 variant of TagN | every `Tag2` | below 32 | below 32 + 4096 | below 4128 + 65536 | below that + 2^32 | beyond |

  The current costs are `tag4EncodedSize`, `tag0EncodedSize` and `putTag2`.
- **Check.** For **all 56,622** constants, the integer bytes plus the non-integer bytes
  (flag and contract bytes, addresses) equal `rawBytes.size`.
- **Cross-check.** The walk finds 10,522,093 Share indices occupying 23,273,409 bytes,
  the same figures as the earlier count of Share references by index.

### Results

The corpus stores 80,208,288 bytes:
- `Tag4` integers: 22,822,097, taking 36,407,507 bytes;
- `Tag0` integers: 3,486,829, taking 3,504,738 bytes;
- `Tag2` integers: 234,690, taking 234,690 bytes;
- other bytes: 40,061,353.

| repricing | family | bytes now | bytes after | change | % of stored bytes |
|---|---|---:|---:|---:|---:|
| TagN | `Tag4` | 36,407,507 | 34,361,119 | **−2,046,388** | −2.55% |
| TagN-byte | `Tag0` | 3,504,738 | 3,500,360 | −4,378 | −0.0055% |
| Tag2 variant | `Tag2` | 234,690 | 234,690 | 0 | 0 |
| TagN + TagN-byte | | | | −2,050,766 | −2.56% |
| all three | | | | −2,050,766 | −2.56% |

- **No integer gets longer** under any of the three codes: the bytes-lost column is 0 in
  every field class.
- **Where the savings come from:**
  - Share indices: −2,046,174 bytes. These are the indices 256–1,031, which go from 3
    bytes to 2.
  - Table counts: −4,330. Str/Nat indices: −214. Ref/Recur indices: −48.
  - Every other field class: 0. That covers Var indices, Sort levels, App argument
    counts, Lam/All binder counts, Ref/Recur universe-list lengths and universe indices,
    Prj fields and type indices, Let flags, ConstantInfo headers and scalar fields, and
    universe terms.
- **Current widths per tag family** (the full table, including the repriced widths, is in
  the harness output below):

  | family | 1 byte | 2 bytes | 3 bytes | 4–9 bytes |
  |---|---:|---:|---:|---:|
  | `Tag4` | 12,565,754 | 6,927,276 | 3,329,067 | **0** |
  | `Tag0` | 3,473,304 | 9,141 | 4,384 | **0** |
  | `Tag2` | 234,690 | 0 | 0 | **0** |

  **No integer in Init currently uses a 4-, 5-, 6-, 7-, 8- or 9-byte form, in any tag
  family.**

## Metadata and sharing follow-up (Init and Mathlib)

The owner asked whether metadata expressions should participate in sharing. This
section measures where the bytes of a whole `.ixe` go, and what `metaSharing`
contains, on Init (`init.ixe`, 195,387,870 bytes) and on Mathlib (`mathlib.ixe`,
3,343,271,273 bytes; the corpus of `sharing-minimum-measurements-mathlib.md`). It is
implemented as the harness's `--meta` mode.

### Method

- **Streaming scanner.** The harness reads the file section by section with the
  production readers (`getExprMetaDataIndexed`, `getExpr`, `getUniv`,
  `getFusedHint`, …). It mirrors `getEnv` and `getConstantMetaIndexed` exactly and
  records the byte range of every component. A constant is parsed only when a `Named`
  entry needs it.
- **Why not `deEnv` on Mathlib.** `deEnv` was used on Init but **not** on Mathlib. It
  materializes the whole environment, and the scanner already reads the full `Named`
  section without doing so.
- **Checks:**
  - On both files the byte categories sum **exactly** to the file size.
  - Every `Named` entry's metadata blob parses to exactly its length prefix.
  - On Init, every total the scanner reports equals a full `Ixon.deEnv` load: named
    entries, blobs, constants, non-empty `metaSharing`, its entries and their
    `serExpr` bytes, `metaRefs`, `metaUnivs`, entries with `original`, and `original`
    `metaSharing` entries.
- **`metaSharing` analysis.** The constant's primary sharing table, its primary roots
  and the `metaSharing` entries are expanded into one canonical DAG with W1's
  `Ix.Sharing.Exact.expand`.
  - **Which table is "primary".** A `Share` in an entry would index the primary table,
    as in `DecompileM.mkBlockCtx`. For a projection, the primary table is the block's,
    as in `DecompileM.decompileOne`.
  - **"Structurally equal"** is exact here, because W1's interner keys on the full node.
    Index-level equality is what a dictionary can exploit.
  - **Re-encoding.** Each entry is re-encoded optimally with the primary table as a fixed
    dictionary at its current index widths (`Prep.materializeWith`). The harness
    checks that the output re-expands (`reexpand`) to the same terms and that its
    `serExpr` bytes equal the predicted `C_M`.
  - **Deduplication.** "Deduplicated" counts each distinct entry of a constant's table
    once.
- **Names** of the constants with non-empty `metaSharing` come from the lazy
  `deEnvAnon` loader.

### Where the bytes go

| component | Init bytes | Init % | Mathlib bytes | Mathlib % |
|---|---:|---:|---:|---:|
| §2 anonymous constants (bodies, addresses, length prefixes) | 82,179,806 | 42.06% | 1,492,588,407 | 44.64% |
| §5 ExprMeta arenas (primary + `original`) | 83,050,319 | 42.51% | 1,436,611,288 | 42.97% |
| §5 everything else (keys, hints, ConstantMeta info, metaSharing, metaRefs, metaUnivs, univPatches, `original` header) | 2,559,387 | 1.31% | 41,384,722 | 1.24% |
| §4 names | 24,654,949 | 12.62% | 344,172,899 | 10.29% |
| §1 blobs | 2,834,610 | 1.45% | 27,209,569 | 0.81% |
| §3 anonymous hints, header, §6 comms | 108,799 | 0.06% | 1,304,388 | 0.04% |

- **Mathlib's non-constant bytes are 1,850,682,866 (55.36% of the file):**
  - 77.6% of them are ExprMeta arenas;
  - 18.6% are names.
- **The arena's App nodes are the largest single item.** An arena App node stores only
  its two child arena indices.

  | | App nodes | bytes | % of file | avg bytes per node |
  |---|---:|---:|---:|---:|
  | Mathlib | 219,151,448 | 1,153,185,700 | 34.49% | 5.26 |
  | Init | 13,111,962 | 66,602,568 | 34.09% | |

  The next largest arena node kinds in Mathlib are binder nodes (138.9 MB, 4.15%) and
  ref nodes (112.6 MB, 3.37%).
- **Full category tables.** The full per-category and per-node-kind tables for both
  files are in the generated fragments at the end of this document.

### `metaSharing`

- **Init:** no `Named` entry has a non-empty `metaSharing`, in either the primary or the
  `original` metadata, so there is nothing to share. Init has 2,363 `metaUnivs` entries
  and 0 `metaRefs`.
- **Mathlib:** 7 of 778,344 `Named` entries have a non-empty `metaSharing`, all
  `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_1` … `_7`. None of the 22,265
  `original` metadata has one. Mathlib has 413,181 `metaUnivs` entries and 0 `metaRefs`.

| Mathlib `metaSharing` | value |
|---|---:|
| tables / entries | 7 / 524 (30 to 114 per table) |
| serialized bytes of the entries | 42,929 (0.0013% of the file) |
| entries equal to a subterm of the primary term | 412 (34,613 bytes) |
| entries equal to a primary table entry | 288 |
| re-encoded optimally against the primary table | **5,495 bytes** (saves 37,434 = 0.0011% of the file) |
| deduplicated within each table (203 distinct entries) | 14,599 bytes |
| re-encoded and deduplicated | **2,586 bytes** (saves 40,343 = 0.0012% of the file) |
| `Share` nodes inside metadata expressions | **0** |

The current entries are stored fully unshared: their unshared size equals their stored
size.

### Not measured

- **Duplication inside ExprMeta arenas** was not measured, for example identical nodes
  or subtrees within a constant's arena. The arenas are not Ixon expressions, and the
  question was about `metaSharing`.
- **Not counted in the deduplication figure:**
  - sharing of subterms *between* `metaSharing` entries;
  - sharing across constants;
  - any change to the call-site entries' `sharingIdx` widths that deduplication would
    require.
- **The primary table was held fixed.** The re-encoding never adds entries for the
  metadata or reorders the primary table.
- **The `deEnv` cross-check was run on Init only.** On Mathlib the scanner is checked by
  the byte-sum and per-entry framing checks.

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

Worktree `/home/jcb/projects/ix-sharing-w3`, branch `ix-sharing-w3` (with `ix-sharing`
merged in), and corpus
`/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe`
(195,387,870 bytes). The corpus was not regenerated.

```text
cd /home/jcb/projects/ix-sharing-w3
nix develop --command bash -c 'lake build sharing-study'
#   -> Build completed successfully.
S=/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad
# Ninth run: everything, including the W1 uniform optimizer.
nix develop --command bash -c "lake exe sharing-study $S/init.ixe \
    --md $S/w3-results9.md --csv $S/sharing-minimum-measurements.csv --progress 2500"
# Tenth run: everything except the uniform optimizer.
nix develop --command bash -c "lake exe sharing-study $S/init.ixe --no-uniform \
    --md $S/w3-results10.md --csv $S/sharing-minimum-measurements.csv"
#   -> both exit 0; defaults --validate-max 16777216 --occ-check-max 65536,
#      --uni-max-states 1048576
```

There were ten full runs.

| run | measured | harness-internal time | end to end |
|---|---|---|---|
| First (commit `ecdd47ed`) | P1.5 only | 146.8 s | about 152 s |
| Second (commit `1598a9be`) | P1.5 + MSS | 185.2 s | 193.3 s |
| Third (commit `97824804`) | + uniform-width classification (first `payloadMin`) | 316.3 s | 335.0 s |
| Fourth (commit `ccebc800`) | same, with the corrected `payloadMin` | 379.5 s | 397.6 s |
| Fifth (commit `8c73b11a`) | + Share-width schemes A–C | 199.1 s | 210.0 s |
| Sixth (commit `74296aaf`) | + scheme D | 210.5 s | 222.0 s |
| Seventh (commit `7232adbe`) | + scheme E | 237.2 s | 262.0 s |
| Eighth (commit `43439654`) | + schemes F and G | 295.3 s | 315.7 s |
| Ninth (see note) | + W1 uniform optimizer, w = 1, 2, 3 | 7,125.3 s, of which 6,875.4 s in the optimizer | 7,140.9 s |
| Tenth (this commit) | + TagN repricing, `--no-uniform` | 374.7 s | 386.3 s |

- **Ninth run.** It was built from this commit's harness minus the TagN code and the last
  six CSV columns, which were added while it ran. Its sections that also appear in the
  tenth run are identical apart from the timing lines and the "slowest constants" table
  (checked with `diff`).
- **Timings vary with machine load.** The fifth to eighth runs did more work than the
  fourth yet took less time, so wall times should not be compared across runs.
- **CSVs.** Both are too large to track and are kept in the scratchpad:
  - the tenth run's CSV, 13,491,833 bytes, 94 columns:
    `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/sharing-minimum-measurements.csv`.
    Its `u{w}_*` columns are empty (`--no-uniform`); its `w1m{w}_comp` and `tagn*_change`
    columns are new.
  - the ninth run's CSV, 16,651,701 bytes, 88 columns, with the uniform columns
    (`u{w}_ok, u{w}_us, u{w}_cs, u{w}_ce, u{w}_unc, u{w}_comp, u{w}_states, u{w}_model,
    u{w}_real, u{w}_realF, u{w}_table`):
    `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/sharing-minimum-measurements-run9.csv`.
- **Earlier CSV columns:**

  ```text
  addr (first 16 hex digits), name, kind, members (muts: i/c/r/d counts), roots, N,
  occ_ge2, cand, cand_gt2, cand_gt3, table, raw_bytes, unshared_bytes, rebuild_ok,
  roundtrip_ok, unshared_validated, occ_checked, max_app, max_lam, max_all, us (harness µs),
  mss_bytes, mss_table, mss_ok, mss_cont, mss_cont_p2, mss_cont_p2u,
  w1_cs, w1_ce, w1_unc, w1_comp, w2_cs, w2_ce, w2_unc, w2_comp, w3_cs, w3_ce, w3_unc, w3_comp,
  refs_lt8, refs_8_255, refs_ge256,
  mss_refs_lt8, mss_refs_8_255, mss_refs_ge256, mss_deg_sum,
  mss_refs_lt15, mss_refs_15_4110, mss_refs_ge4111,
  mss_refs_lt8f, mss_refs_8_1031, mss_refs_ge1032, mss_refs_lt14, mss_refs_14_269, mss_refs_ge270
  ```

Rerunning the commands above regenerates both CSVs.

Metadata study (`--meta` mode, `ix-sharing` merged at `4cf8ba2e`):

```text
nix develop --command bash -c "lake exe sharing-study $S/init.ixe --meta --meta-crosscheck \
    --progress 0 --md $S/w3-meta-init.md"
#   -> exit 0; 57 s end to end, peak RSS 2.25 GB (including the deEnv cross-check)
nix develop --command bash -c "lake exe sharing-study $S/mathlib.ixe --meta \
    --progress 200000 --md $S/w3-meta-mathlib.md"
#   -> exit 0; 203 s end to end, peak RSS 4.75 GB; an earlier identical run gave the same output
```

---

The rest of this document is the harness's `--md` output from the tenth run, unedited.
It is followed by the uniform-optimizer section of the ninth run's output and by the
`--meta` outputs for Init and Mathlib, all unedited.

## Results

- Corpus: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe` (195387870 bytes), 56622 stored constants (distinct addresses), 66621 names.
- Constants processed: 56622; skipped: 0; with at least one expression root: 55386.
- Harness wall time: load 302 ms, measurement 374353 ms, total 374655 ms.
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
| `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 1853 | 18802 | 109553 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 1562 | 26494 | 154009 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4` | defn | 1440 | 11095 | 65930 |
| `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 1336 | 14521 | 76215 |
| `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_3` | defn | 1315 | 11281 | 67894 |

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

## Uniform-reference-width classification

Candidates are the subterms with compact `deg ≥ 2` and unshared size > 1 (the MSS stored set). For `w ∈ {1, 2, 3}` each candidate is CERTAIN-STORED if `g(deg, headdeg, payloadMin) > 0`, CERTAIN-EXCLUDED if `g(occ, occ, payloadMax) < 0` or it is a leaf with `(occ−1)·size < occ·w`, and UNCERTAIN otherwise, where `g(n, H, b) = (n−1)·b + (H−1)·hdr − n·w`. `payloadMin` is the width-aware recursive lower bound (a candidate child costs at most `w`, a non-candidate child its own recursive minimum; continuation children without their header). `headdeg` treats only an App in App-function position and a Lam/All in same-kind body position as continuations. Uncertain nodes are in one component when a directed DAG path whose intermediate nodes are not certain-stored joins them (transitively). Arithmetic is exact; `occ` is not capped.

- Classification errors: 0.
- Witnesses (cs/ce/unc/largest component for w = 1 | 2 | 3):
  - `T2 → T2`: 1/0/0/0 | 1/0/0/0 | 0/0/1/1 (candidates 1)
  - `T16 → T16`: 1/0/0/0 | 1/0/0/0 | 1/0/0/0 (candidates 1)
  - `A → A → B → B`: 2/0/0/0 | 0/0/2/1 | 0/2/0/0 (candidates 2)
- Candidates over the 55386 rooted constants: 2345582 (MSS table entries: 2345582).

### w = 1

- Totals: certain-stored 1887527 (80.5% of candidates), certain-excluded 0 (0.0%), uncertain 458055 (19.5%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 100.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 53652 equal, **0** different, 1734 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 10 | 81 | 341 | 4211 | 34.08 |
| certain-excluded | 0 | 0 | 0 | 0 | 0 | 0.00 |
| uncertain | 0 | 2 | 21 | 95 | 970 | 8.27 |
| largest uncertain component | 0 | 1 | 2 | 4 | 45 | 1.06 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 13486 | 24.3% | 13486 | 24.3% |
| ≤ 8 | 43174 | 78.0% | 55332 | 99.9% |
| ≤ 16 | 48357 | 87.3% | 55382 | 100.0% |
| ≤ 32 | 52353 | 94.5% | 55384 | 100.0% |
| > 32 | 3033 | 5.5% | 2 | 0.0% |
| > 128 | 332 | 0.6% | 0 | 0.0% |
| > 1024 | 0 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 1):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 236 | 0 | 124 | 45 |
| 2 | `_private.Init.Data.String.Decode.«0».UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` | defn | 1056 | 296 | 192 | 0 | 104 | 35 |
| 3 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 164 | 0 | 92 | 31 |
| 4 | `_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_cpopTree._unary` | defn | 2614 | 594 | 471 | 0 | 123 | 17 |
| 5 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 19523 | 3640 | 3062 | 0 | 578 | 16 |
| 6 | `_private.Init.Data.Nat.Internal.SOM.«0».Nat.Internal.SOM.Poly.add_denote.go` | defn | 1474 | 340 | 224 | 0 | 116 | 16 |
| 7 | `Lean.Meta.DSimp.Config.mk.injEq` | defn | 746 | 126 | 82 | 0 | 44 | 15 |
| 8 | `Std.IterM.toArray_map_mapM` | defn | 2933 | 432 | 326 | 0 | 106 | 15 |
| 9 | `Std.IterM.toList_map` | defn | 2506 | 404 | 314 | 0 | 90 | 15 |
| 10 | `Std.IterM.toList_mapM_mapM` | defn | 2891 | 413 | 312 | 0 | 101 | 15 |

### w = 2

- Totals: certain-stored 1504278 (64.1% of candidates), certain-excluded 349863 (14.9%), uncertain 491441 (21.0%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 100.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 53652 equal, **0** different, 1734 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 6 | 63 | 315 | 4455 | 27.16 |
| certain-excluded | 0 | 3 | 17 | 46 | 135 | 6.32 |
| uncertain | 0 | 3 | 22 | 84 | 736 | 8.87 |
| largest uncertain component | 0 | 1 | 3 | 5 | 44 | 1.51 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 11593 | 20.9% | 11593 | 20.9% |
| ≤ 8 | 39615 | 71.5% | 55328 | 99.9% |
| ≤ 16 | 47353 | 85.5% | 55384 | 100.0% |
| ≤ 32 | 52492 | 94.8% | 55385 | 100.0% |
| > 32 | 2894 | 5.2% | 1 | 0.0% |
| > 128 | 213 | 0.4% | 0 | 0.0% |
| > 1024 | 0 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 2):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 148 | 91 | 121 | 44 |
| 2 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 103 | 64 | 89 | 30 |
| 3 | `List.min_findIdx_findIdx` | defn | 932 | 234 | 135 | 22 | 77 | 15 |
| 4 | `Array.getD_getElem?` | defn | 359 | 76 | 41 | 9 | 26 | 14 |
| 5 | `Lean.Meta.DSimp.Config.mk.injEq` | defn | 746 | 126 | 53 | 31 | 42 | 14 |
| 6 | `List.getD_getElem?` | defn | 359 | 76 | 41 | 9 | 26 | 14 |
| 7 | `Vector.getD_getElem?` | defn | 392 | 77 | 50 | 8 | 19 | 14 |
| 8 | `Lean.Grind.AC.imp_eq` | defn | 130 | 30 | 10 | 5 | 15 | 13 |
| 9 | `Lean.Grind.AC.eq_simp_lhs_exact` | defn | 130 | 31 | 13 | 4 | 14 | 12 |
| 10 | `_private.Init.Data.Nat.Internal.SOM.«0».Nat.Internal.SOM.Poly.add_denote.go` | defn | 1474 | 340 | 182 | 44 | 114 | 12 |

### w = 3

- Totals: certain-stored 1276154 (54.4% of candidates), certain-excluded 570132 (24.3%), uncertain 499296 (21.3%); nodes meeting both certain conditions 0; candidates with `payloadMin > payloadMax` 0; candidates whose class changes when every function-child occurrence counts as a non-head 92.
- Largest component recomputed by the literal brute force (DAGs with ≤ 1000 nodes): 53652 equal, **0** different, 1734 not checked.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| certain-stored | 0 | 4 | 53 | 286 | 4392 | 23.04 |
| certain-excluded | 0 | 5 | 27 | 60 | 229 | 10.29 |
| uncertain | 0 | 2 | 22 | 98 | 978 | 9.01 |
| largest uncertain component | 0 | 1 | 3 | 6 | 44 | 1.37 |

| bucket | constants by `uncertain` | share | constants by largest component | share |
|---|---:|---:|---:|---:|
| = 0 | 14878 | 26.9% | 14878 | 26.9% |
| ≤ 8 | 40386 | 72.9% | 55228 | 99.7% |
| ≤ 16 | 47612 | 86.0% | 55378 | 100.0% |
| ≤ 32 | 52174 | 94.2% | 55385 | 100.0% |
| > 32 | 3212 | 5.8% | 1 | 0.0% |
| > 128 | 318 | 0.6% | 0 | 0.0% |
| > 1024 | 0 | 0.0% | 0 | 0.0% |

Ten constants with the largest uncertain component (w = 3):

| # | constant | kind | `N` | candidates | certain-stored | certain-excluded | uncertain | largest component |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Grind.Config.mk.injEq` | defn | 3512 | 360 | 145 | 92 | 123 | 44 |
| 2 | `_private.Init.Data.String.Decode.«0».UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` | defn | 1056 | 296 | 154 | 42 | 100 | 31 |
| 3 | `Lean.Meta.Simp.Config.mk.injEq` | defn | 1994 | 256 | 100 | 65 | 91 | 30 |
| 4 | `BitVec.getMsbD_setWidth` | defn | 1044 | 258 | 125 | 44 | 89 | 20 |
| 5 | `Lean.Grind.imp_eq` | defn | 249 | 56 | 19 | 11 | 26 | 19 |
| 6 | `_private.Init.Data.Order.PackageFactories.«0».Std.FactoryInstances.isGE_compare` | defn | 405 | 105 | 27 | 28 | 50 | 19 |
| 7 | `_private.Init.Data.Order.PackageFactories.«0».Std.FactoryInstances.isLE_compare` | defn | 359 | 99 | 27 | 24 | 48 | 19 |
| 8 | `BitVec.msb_neg` | defn | 1541 | 378 | 202 | 61 | 115 | 18 |
| 9 | `Std.LinearPreorderPackage.ofOrd._proof_1` | defn | 567 | 143 | 54 | 32 | 57 | 16 |
| 10 | `Std.LinearPreorderPackage.ofOrd._proof_9` | defn | 401 | 96 | 41 | 23 | 32 | 16 |

### Reference-width loss in the current stored encoding

Share references counted syntactically in the stored roots and stored table entries of every constant (current heuristic encoding). The largest stored table has 22088 entries, so every index ≥ 256 is 3 bytes.

| stored table entries | constants | refs to 0–7 (1 B) | refs to 8–255 (2 B) | refs to ≥ 256 (3 B) | loss under the uniform width |
|---|---:|---:|---:|---:|---|
| 1–8 | 11367 | 119925 | 0 | 0 | (not requested; 119925 if these cost 2 B) |
| 9–255 | 37610 | 776978 | 3298554 | 0 | w = 2: **776978** bytes |
| > 255 | 4335 | 202727 | 2795056 | 3328853 | w = 3: 2·202727 + 2795056 = **3200510** bytes |

- Total stored bytes over all constants: 80208288; total Share references: 10522093.

## Share-width schemes on the MSS encoding

Every occurrence of an MSS entry is a Share. Scheme A: the current tiers by index in MSS order (1 byte below index 8, 2 below 256, 3 below 65536). Scheme B: one width per constant, 2 bytes if the MSS entry count (= candidate count) is ≤ 2048, else 3. Scheme C: as B, but 1 byte if the count is ≤ 8. Scheme D: one width per constant using the tag byte's whole low nibble: 1 byte if the count is ≤ 16, 2 if ≤ 4096, else 3. Scheme E: position tiers with a nibble escape, by index in MSS order: 1 byte below index 15, 2 below 15 + 4096, else 3 (as specified; not realizable with a 4-bit Share flag). Scheme F: realizable position tiers with two marker bits: 1 byte below index 8, 2 below 8 + 1024, else 3. Scheme G: realizable position tiers with nibble values 14 and 15 as escapes: 1 byte below index 14, 2 below 14 + 256, else 3. Constant bytes under a scheme are MSS bytes − refbytes(A) + refbytes(scheme). Share nodes are counted on the materialized MSS encoding.

- Share nodes in the MSS encoding vs `Σ deg` over MSS entries: 55386 equal, **0** different.
- Share nodes counted in the scheme-F and scheme-G index buckets vs the scheme-A buckets: 55386 equal totals, **0** different.
- Share nodes counted in the scheme-E index buckets vs the scheme-A buckets: 55386 equal totals, **0** different.
- Rooted constants: 55386; Share references in their MSS encodings: 9297007; constants with more than 2048 MSS entries (width 3 under B and C): 20; with at most 8 entries (width 1 under C): 22270.

| scheme | reference bytes | MSS constant bytes | Δ vs A | Δ / MSS total (A) | Δ / heuristic total |
|---|---:|---:|---:|---:|---:|
| A (index tiers) | 17568850 | 68547873 | 0 | +0.00% | +0.00% |
| B (2 or 3 per constant) | 18990396 | 69969419 | 1421546 | +2.07% | +1.77% |
| C (1, 2 or 3 per constant) | 18724875 | 69703898 | 1156025 | +1.69% | +1.44% |
| D (nibble: ≤ 16 / ≤ 4096 / more) | 18207733 | 69186756 | 638883 | +0.93% | +0.80% |
| E (index tiers < 15 / < 4111 / more) | 15442797 | 66421820 | -2126053 | −3.10% | −2.65% |
| F (index tiers < 8 / < 1032 / more) | 16577564 | 67556587 | -991286 | −1.45% | −1.24% |
| G (index tiers < 14 / < 270 / more) | 16741559 | 67720582 | -827291 | −1.21% | −1.03% |

Totals for reference: MSS bytes (scheme A, the real encoding) 68547873; heuristic stored bytes 80161846.

| comparison | better (fewer bytes) | equal | worse |
|---|---:|---:|---:|
| B vs A | 829 | 555 | 54002 |
| C vs A | 829 | 22271 | 32286 |
| D vs A | 9773 | 22271 | 23342 |
| E vs A | 33116 | 22270 | 0 |
| F vs A | 1352 | 54034 | 0 |
| G vs A | 33116 | 22270 | 0 |

Width classes under D: 1 byte (≤ 16 entries) 31200 constants, 2 bytes (17–4096) 24180, 3 bytes (> 4096) 6.

### Ten largest losses under B (B − A)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | B ref bytes | Δ (B − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux` | defn | 2763 | 20215 | 4736 / 7802 / 7677 | 43371 | 60645 | 17274 | 52808 |
| 2 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 4874 | 29452 | 2013 / 9356 / 18083 | 74974 | 88356 | 13382 | 104522 |
| 3 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 2712 | 16793 | 1838 / 6999 / 7956 | 39704 | 50379 | 10675 | 53900 |
| 4 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 5136 | 31580 | 744 / 6448 / 24388 | 86804 | 94740 | 7936 | 104331 |
| 5 | `_private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq._unary` | defn | 2382 | 12573 | 1123 / 5400 / 6050 | 30073 | 37719 | 7646 | 44156 |
| 6 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 4919 | 31007 | 660 / 6168 / 24179 | 85533 | 93021 | 7488 | 102666 |
| 7 | `_private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq._unary` | defn | 2398 | 12299 | 1096 / 5199 / 6004 | 29506 | 36897 | 7391 | 43251 |
| 8 | `_private.Init.Data.Array.Lemmas.«0».Array.toList_reverse.go._unary` | defn | 2769 | 13884 | 1934 / 3454 / 8496 | 34330 | 41652 | 7322 | 50884 |
| 9 | `_private.Init.Data.String.Pattern.String.«0».String.Slice.Pattern.ForwardSliceSearcher.finitenessRelation._proof_2` | defn | 2327 | 12439 | 1216 / 4588 / 6635 | 30297 | 37317 | 7020 | 46275 |
| 10 | `String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.defaultImplementation` | defn | 2407 | 11882 | 1133 / 4231 / 6518 | 29149 | 35646 | 6497 | 43015 |

### Ten largest gains under B (A − B)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | B ref bytes | Δ (B − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_reverse._proof_1` | defn | 1908 | 10516 | 314 / 2309 / 7893 | 28611 | 21032 | -7579 | 36602 |
| 2 | `_private.Init.Data.Array.Lemmas.«0».Array.toList_extract._proof_1_1` | defn | 1786 | 9846 | 278 / 2487 / 7081 | 26495 | 19692 | -6803 | 34199 |
| 3 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_left._proof_1_1` | defn | 1815 | 9731 | 433 / 2122 / 7176 | 26205 | 19462 | -6743 | 33682 |
| 4 | `_private.Init.Data.Nat.Lemmas.«0».Nat.sub_max_sub_left._proof_1_1` | defn | 1884 | 10582 | 610 / 2725 / 7247 | 27801 | 21164 | -6637 | 35895 |
| 5 | `_private.Init.Data.BitVec.Lemmas.«0».BitVec.getMsbD_extractLsb._proof_1_4` | defn | 1702 | 9256 | 290 / 2070 / 6896 | 25118 | 18512 | -6606 | 32947 |
| 6 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_right._proof_1_1` | defn | 1760 | 9274 | 397 / 1956 / 6921 | 25072 | 18548 | -6524 | 32445 |
| 7 | `_private.Init.Data.Nat.Lemmas.«0».Nat.sub_min_sub_left._proof_1_1` | defn | 1816 | 9973 | 579 / 2589 / 6805 | 26172 | 19946 | -6226 | 34020 |
| 8 | `_private.Init.Data.Int.LemmasAux.«0».Int.min_max_distrib_left._proof_1_1` | defn | 1716 | 9026 | 425 / 1982 / 6619 | 24246 | 18052 | -6194 | 31434 |
| 9 | `_private.Init.Data.Int.LemmasAux.«0».Int.min_max_distrib_right._proof_1_1` | defn | 1687 | 8897 | 649 / 1765 / 6483 | 23628 | 17794 | -5834 | 30809 |
| 10 | `_private.Init.Data.Array.Extract.«0».Array.extract_reverse._proof_1_2` | defn | 1670 | 8901 | 313 / 2504 / 6084 | 23573 | 17802 | -5771 | 31386 |

### B − A restricted to constants whose current heuristic table exceeds 255 entries

- Constants: 4335; their MSS bytes 25359218, heuristic bytes 33341195; MSS entries: min 44, max 5146; with more than 2048 MSS entries: 20.
- Reference bytes: A 11525602, B 11441534; Δ (B − A) -84068 (−0.33% of their MSS bytes, −0.25% of their heuristic bytes).
- B vs A: better 829, equal 1, worse 3505.

### Ten largest losses under D (D − A)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | D ref bytes | Δ (D − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 4874 | 29452 | 2013 / 9356 / 18083 | 74974 | 88356 | 13382 | 104522 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 5136 | 31580 | 744 / 6448 / 24388 | 86804 | 94740 | 7936 | 104331 |
| 3 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 4919 | 31007 | 660 / 6168 / 24179 | 85533 | 93021 | 7488 | 102666 |
| 4 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 5146 | 31423 | 750 / 4863 / 25810 | 87906 | 94269 | 6363 | 105389 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 4703 | 28903 | 640 / 4587 / 23676 | 80842 | 86709 | 5867 | 97145 |
| 6 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 4678 | 28730 | 643 / 4441 / 23646 | 80463 | 86190 | 5727 | 96716 |
| 7 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_ne.match_1_1` | defn | 199 | 3103 | 1072 / 2031 / 0 | 5134 | 6206 | 1072 | 9309 |
| 8 | `_private.Init.Data.Iterators.Combinators.Monadic.FilterMap.«0».Std.Iterators.Types.Map.instProductivenessRelation._proof_2` | defn | 166 | 1262 | 528 / 734 / 0 | 1996 | 2524 | 528 | 4797 |
| 9 | `_private.Init.Meta.Defs.«0».Lean.Name.beq.match_1.eq_4` | defn | 163 | 1182 | 517 / 665 / 0 | 1847 | 2364 | 517 | 3772 |
| 10 | `Std.IterM.step_filterMapM` | defn | 362 | 2232 | 720 / 1279 / 233 | 3977 | 4464 | 487 | 7713 |

### Ten largest gains under D (A − D)

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–255 / ≥ 256 | A ref bytes | D ref bytes | Δ (D − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 3640 | 22811 | 497 / 4776 / 17538 | 62663 | 45622 | -17041 | 76309 |
| 2 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 3236 | 21512 | 1001 / 4190 / 16321 | 58344 | 43024 | -15320 | 72208 |
| 3 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 2854 | 16989 | 431 / 3532 / 13026 | 46573 | 33978 | -12595 | 57498 |
| 4 | `_private.Init.Data.Array.Extract.«0».Array.extract_add_left._proof_1_2` | defn | 2717 | 15681 | 452 / 4450 / 10779 | 41689 | 31362 | -10327 | 52203 |
| 5 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_3` | defn | 2477 | 13376 | 397 / 2928 / 10051 | 36406 | 26752 | -9654 | 46372 |
| 6 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4` | defn | 2294 | 13015 | 373 / 2645 / 9997 | 35654 | 26030 | -9624 | 45467 |
| 7 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_reverse._proof_1` | defn | 1908 | 10516 | 314 / 2309 / 7893 | 28611 | 21032 | -7579 | 36602 |
| 8 | `_private.Init.Data.Array.Lemmas.«0».Array.toList_extract._proof_1_1` | defn | 1786 | 9846 | 278 / 2487 / 7081 | 26495 | 19692 | -6803 | 34199 |
| 9 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_left._proof_1_1` | defn | 1815 | 9731 | 433 / 2122 / 7176 | 26205 | 19462 | -6743 | 33682 |
| 10 | `_private.Init.Data.Nat.Lemmas.«0».Nat.sub_max_sub_left._proof_1_1` | defn | 1884 | 10582 | 610 / 2725 / 7247 | 27801 | 21164 | -6637 | 35895 |

### Ten largest losses under E (E − A)

| # | constant | kind | MSS entries | Share refs | refs < 15 / 15–4110 / ≥ 4111 | A ref bytes | E ref bytes | Δ (E − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `Acc.brecOn` | defn | 8 | 22 | 22 / 0 / 0 | 22 | 22 | 0 | 298 |
| 2 | `Acc.casesOn` | defn | 6 | 14 | 14 / 0 / 0 | 14 | 14 | 0 | 233 |
| 3 | `Acc.inv` | defn | 6 | 15 | 15 / 0 / 0 | 15 | 15 | 0 | 200 |
| 4 | `Acc.inv_of_transGen` | defn | 8 | 16 | 16 / 0 / 0 | 16 | 16 | 0 | 294 |
| 5 | `Acc.ndrec` | defn | 5 | 11 | 11 / 0 / 0 | 11 | 11 | 0 | 174 |
| 6 | `Acc.ndrec.eq_1` | defn | 7 | 15 | 15 / 0 / 0 | 15 | 15 | 0 | 293 |
| 7 | `Acc.ndrecC` | defn | 5 | 11 | 11 / 0 / 0 | 11 | 11 | 0 | 174 |
| 8 | `Acc.ndrecC.eq_1` | defn | 7 | 15 | 15 / 0 / 0 | 15 | 15 | 0 | 293 |
| 9 | `Acc.ndrecOn` | defn | 5 | 11 | 11 / 0 / 0 | 11 | 11 | 0 | 174 |
| 10 | `Acc.ndrecOn.eq_1` | defn | 7 | 15 | 15 / 0 / 0 | 15 | 15 | 0 | 293 |

### Ten largest gains under E (A − E)

| # | constant | kind | MSS entries | Share refs | refs < 15 / 15–4110 / ≥ 4111 | A ref bytes | E ref bytes | Δ (E − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 5146 | 31423 | 957 / 26083 / 4383 | 87906 | 66272 | -21634 | 105389 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 4703 | 28903 | 838 / 25762 / 2303 | 80842 | 59271 | -21571 | 97145 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 4678 | 28730 | 827 / 25505 / 2398 | 80463 | 59031 | -21432 | 96716 |
| 4 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 4919 | 31007 | 823 / 27107 / 3077 | 85533 | 64268 | -21265 | 102666 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 5136 | 31580 | 982 / 26789 / 3809 | 86804 | 65987 | -20817 | 104331 |
| 6 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 3640 | 22811 | 1812 / 20999 / 0 | 62663 | 43810 | -18853 | 76309 |
| 7 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 4874 | 29452 | 2977 / 24384 / 2091 | 74974 | 58018 | -16956 | 104522 |
| 8 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 3236 | 21512 | 1342 / 20170 / 0 | 58344 | 41682 | -16662 | 72208 |
| 9 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 2854 | 16989 | 1587 / 15402 / 0 | 46573 | 32391 | -14182 | 57498 |
| 10 | `_private.Init.Data.Array.Extract.«0».Array.extract_add_left._proof_1_2` | defn | 2717 | 15681 | 1299 / 14382 / 0 | 41689 | 30063 | -11626 | 52203 |

### Scheme F vs A

- Constants worse than A under F: **0**; largest per-constant Δ (F − A): 0.

Ten largest gains under F (A − F):

| # | constant | kind | MSS entries | Share refs | refs < 8 / 8–1031 / ≥ 1032 | A ref bytes | F ref bytes | Δ (F − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 5146 | 31423 | 750 / 11353 / 19320 | 87906 | 81416 | -6490 | 105389 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 4919 | 31007 | 660 / 12447 / 17900 | 85533 | 79254 | -6279 | 102666 |
| 3 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 3236 | 21512 | 1001 / 10398 / 10113 | 58344 | 52136 | -6208 | 72208 |
| 4 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 4874 | 29452 | 2013 / 15285 / 12154 | 74974 | 69045 | -5929 | 104522 |
| 5 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 4678 | 28730 | 643 / 10243 / 17844 | 80463 | 74661 | -5802 | 96716 |
| 6 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 5136 | 31580 | 744 / 11862 / 18974 | 86804 | 81390 | -5414 | 104331 |
| 7 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 3640 | 22811 | 497 / 9707 / 12607 | 62663 | 57732 | -4931 | 76309 |
| 8 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_left._proof_1_1` | defn | 1815 | 9731 | 433 / 6942 / 2356 | 26205 | 21385 | -4820 | 33682 |
| 9 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 2854 | 16989 | 431 / 8267 / 8291 | 46573 | 41838 | -4735 | 57498 |
| 10 | `_private.Init.Data.Int.LemmasAux.«0».Int.min_max_distrib_left._proof_1_1` | defn | 1716 | 9026 | 425 / 6476 / 2125 | 24246 | 19752 | -4494 | 31434 |

### Scheme G vs A

- Constants worse than A under G: **0**; largest per-constant Δ (G − A): 0.

Ten largest gains under G (A − G):

| # | constant | kind | MSS entries | Share refs | refs < 14 / 14–269 / ≥ 270 | A ref bytes | G ref bytes | Δ (G − A) | MSS bytes (A) |
|---:|---|---|---:|---:|---|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 3640 | 22811 | 1794 / 4035 / 16982 | 62663 | 60810 | -1853 | 76309 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_reverse._proof_1` | defn | 1908 | 10516 | 956 / 2290 / 7270 | 28611 | 27346 | -1265 | 36602 |
| 3 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 2712 | 16793 | 2900 / 6021 / 7872 | 39704 | 38558 | -1146 | 53900 |
| 4 | `_private.Init.Data.BitVec.Lemmas.«0».BitVec.getMsbD_extractLsb._proof_1_3` | defn | 1337 | 7253 | 780 / 2335 / 4138 | 18989 | 17864 | -1125 | 25704 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 2854 | 16989 | 1469 / 2543 / 12977 | 46573 | 45486 | -1087 | 57498 |
| 6 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 4874 | 29452 | 2855 / 8698 / 17899 | 74974 | 73948 | -1026 | 104522 |
| 7 | `Std.Iter.step_flatMapAfterM` | defn | 1858 | 10970 | 2832 / 3106 / 5032 | 25141 | 24140 | -1001 | 35912 |
| 8 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux` | defn | 2763 | 20215 | 5628 / 6980 / 7607 | 43371 | 42409 | -962 | 52808 |
| 9 | `Std.IterM.toList_filterMapM_map` | defn | 1820 | 10539 | 2537 / 3265 / 4737 | 24198 | 23278 | -920 | 33661 |
| 10 | `Std.IterM.anyM_filterMapM` | defn | 1519 | 9132 | 2192 / 3289 / 3651 | 20559 | 19723 | -836 | 30148 |

### D − A restricted to constants whose current heuristic table exceeds 255 entries

- Constants: 4335; width classes under D: 1 byte 0, 2 bytes 4329, 3 bytes 6.
- Reference bytes: A 11525602, D 11226247; Δ (D − A) -299355 (−1.18% of their MSS bytes, −0.90% of their heuristic bytes).
- D vs A: better 843, equal 1, worse 3491.

## Integer repricing: TagN, TagN-byte and the Tag2 variant

The stored (heuristic) encoding of every constant is walked exactly as `putConstant`/`putExpr`/`putUniv` write it, and every integer is priced under the current codes (`tag4EncodedSize`, `tag0EncodedSize`, `putTag2`) and under TagN (replacing every `Tag4`: 1 byte below 8, 2 below 8 + 1024, 3 below 1032 + 65536, 5 below that + 2^32, 9 beyond), TagN-byte (replacing every `Tag0`: 1 byte below 128, 2 below 128 + 16384, 3 below 16512 + 65536, 5 below that + 2^32, 9 beyond) and the Tag2 variant of TagN (replacing every `Tag2`: 1 byte below 32, 2 below 32 + 4096, 3 below 4128 + 65536, 5 below that + 2^32, 9 beyond).

- Walker check: integer bytes + other bytes = `rawBytes.size` for 56622 of 56622 constants (**0** different).
- Stored bytes: 80208288. `Tag4` integers: 22822097 (36407507 bytes). `Tag0` integers: 3486829 (3504738 bytes). `Tag2` integers: 234690 (234690 bytes). Other bytes: 40061353.
- TagN alone: 34361119 bytes for the `Tag4` integers, change -2046388 (−2.55% of stored bytes; gained 2046388, lost 0).
- TagN-byte alone: 3500360 bytes for the `Tag0` integers, change -4378 (−0.01%; gained 4378, lost 0).
- Tag2 variant alone: 234690 bytes for the `Tag2` integers, change 0 (+0.00%; gained 0, lost 0).
- TagN and TagN-byte together: change -2050766 (−2.56%). All three: change -2050766 (−2.56% of stored bytes).

| field class | integers | current bytes | repriced bytes | change | bytes gained | bytes lost |
|---|---:|---:|---:|---:|---:|---:|
| Share indices (Tag4) | 10522093 | 23273409 | 21227235 | -2046174 | 2046174 | 0 |
| Var indices (Tag4) | 2680768 | 3394656 | 3394656 | 0 | 0 | 0 |
| Sort levels (Tag4) | 201291 | 201493 | 201493 | 0 | 0 | 0 |
| App argument counts (Tag4) | 6335600 | 6365386 | 6365386 | 0 | 0 | 0 |
| Lam/All binder counts (Tag4) | 620821 | 632681 | 632681 | 0 | 0 | 0 |
| Ref/Recur universe-list lengths (Tag4) | 2254605 | 2254605 | 2254605 | 0 | 0 | 0 |
| Prj fields (Tag4) | 6914 | 7010 | 7010 | 0 | 0 | 0 |
| Str/Nat indices (Tag4) | 124859 | 203121 | 202907 | -214 | 214 | 0 |
| Let flags (Tag4) | 18524 | 18524 | 18524 | 0 | 0 | 0 |
| ConstantInfo header: variant / mutual member count (Tag4) | 56622 | 56622 | 56622 | 0 | 0 | 0 |
| Ref/Recur indices (Tag0) | 2254605 | 2259158 | 2259110 | -48 | 48 | 0 |
| Ref/Recur universe indices (Tag0) | 990526 | 990526 | 990526 | 0 | 0 | 0 |
| Prj type indices (Tag0) | 6914 | 6914 | 6914 | 0 | 0 | 0 |
| table counts: sharing, refs, univs (Tag0) | 169866 | 183222 | 178892 | -4330 | 4330 | 0 |
| ConstantInfo scalar fields: lvls, params, indices, motives, minors, rule fields and counts, constructor counts and fields, cidx, projection idx (Tag0) | 64918 | 64918 | 64918 | 0 | 0 | 0 |
| universe terms: zero/succ-chain, max, imax, var headers (Tag2) | 234690 | 234690 | 234690 | 0 | 0 | 0 |

Integers by width (bytes), per tag family, now and repriced:

| width | `Tag4` now | TagN | `Tag0` now | TagN-byte | `Tag2` now | Tag2 variant |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 12565754 | 12565754 | 3473304 | 3473304 | 234690 | 234690 |
| 2 | 6927276 | 8973664 | 9141 | 13519 | 0 | 0 |
| 3 | 3329067 | 1282679 | 4384 | 6 | 0 | 0 |
| 4 | 0 | 0 | 0 | 0 | 0 | 0 |
| 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| 7 | 0 | 0 | 0 | 0 | 0 | 0 |
| 8 | 0 | 0 | 0 | 0 | 0 | 0 |
| 9 | 0 | 0 | 0 | 0 | 0 | 0 |

---

Uniform-optimizer section of the ninth run's harness output, unedited:

## Exact uniform-width optimizer (W1) on the corpus

Every rooted constant, w = 1, 2, 3: `Ix.Sharing.Exact.optimizeSharingUniformTable w c.sharing (constantInfoRoots c.info) limits` with maxStates 1048576, maxCostEvals 1073741824, maxNodes 1048576, maxDepth 16384, maxExprVisits 67108864, maxMaterialize 67108864, maxOutputBytes 268435456 (W1 defaults except maxStates). Output roots are placed with the production cursor helpers and serialized with `serConstant` (current Tag4 tiers); the bytes are decoded, re-encoded, expanded and compared exactly with the original expanded roots. Model length = fixed bytes + `modelBytes`; real = serialized size; F = the same table and roots with scheme F Share widths. Wall time is the optimizer call only.

### w = 1

- Certified: **55294** of 55386; failures: **92**.
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`: 90
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824`: 2
    - `_private.Init.Data.Vector.Extract.«0».Vector.extract_push._proof_1` (N 4007, 12804 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.String.Iterate.«0».String.Slice.ByteIterator.finitenessRelation._proof_1` (N 1231, 22521 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_eq_of._proof_1_23` (N 2728, 31625 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_left._proof_1` (N 2955, 10988 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Nat.Lemmas.«0».Nat.sub_add_sub_cancel._proof_1_1` (N 2183, 34483 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `BitVec.srem_zero_of_dvd` (N 852, 34022 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Range.Polymorphic.IntLemmas.«0».Int.size_rco._proof_1_1` (N 2537, 15576 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Range.Polymorphic.Nat.«0».Std.instLawfulRcoIntersectionNat_4._proof_1` (N 1412, 21473 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4` (N 11095, 12024 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.BitVec.Lemmas.«0».BitVec.toInt_allOnes._proof_1_2` (N 2438, 50360 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
- Output checks on certified constants: real length = fixed + `variableBytes` for 55294; decode/re-encode/expand/exact equality ok for 55294, **0** failed; W1 distinct subterms = this harness's `N` for 55294; class counts and components equal to this harness's reimplementation of W1's definitions for 55294, **0** different.
- Classes (W1, certified): certain-stored 1441164, certain-excluded 5759148, uncertain 851426, low degree 3655922; components 595302; lower count bracket chosen in 35 constants.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| largest uncertain component (W1) | 0 | 2 | 5 | 12 | 21 | 2.50 |
| search states | 0 | 16 | 229 | 9864 | 1044855 | 1128.67 |
| uniform table size | 0 | 10 | 81 | 337 | 4280 | 33.89 |
| optimizer wall time (µs), all runs | 5 | 249 | 2964 | 182154 | 108188764 | 66835.26 |

Totals over the 55294 certified constants:

| encoding | total bytes | vs heuristic | vs MSS |
|---|---:|---:|---:|
| heuristic (stored) | 78855708 | 0 (+0.00%) | 11292360 (+16.71%) |
| MSS (current tiers) | 67563348 | -11292360 (−14.32%) | 0 (+0.00%) |
| uniform w = 1, real (current tiers) | 66737821 | -12117887 (−15.37%) | -825527 (−1.22%) |
| uniform w = 1, scheme F widths | 66047771 | -12807937 (−16.24%) | -1515577 (−2.24%) |
| uniform w = 1, model length | 59469841 | -19385867 (−24.58%) | -8093507 (−11.98%) |
| unshared | 987599557 | 908743849 (+1152.41%) | 920036209 (+1361.74%) |

Uniform w = 1 (real) vs MSS per constant: better 31245, equal 23833, worse 216. Gains p50 10, p90 39, max 2670; losses p50 1, p90 4, max 46. Versus the heuristic: better 50302, equal 4938, worse 54.

Ten largest gains of uniform w = 1 over MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 156976 | 105389 | 102719 | -2670 | 4247 | 5146 | 12 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_reverse._proof_1` | defn | 51942 | 36602 | 35026 | -1576 | 1553 | 1908 | 20 |
| 3 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 156535 | 104331 | 102877 | -1454 | 4280 | 5136 | 12 |
| 4 | `_private.Init.Data.Array.Extract.«0».Array.extract_reverse._proof_1_2` | defn | 45291 | 31386 | 29943 | -1443 | 1284 | 1670 | 13 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 154009 | 102666 | 101274 | -1392 | 4127 | 4919 | 9 |
| 6 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_left._proof_1_1` | defn | 41952 | 33682 | 32406 | -1276 | 1476 | 1815 | 14 |
| 7 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 170285 | 104522 | 103264 | -1258 | 4076 | 4874 | 8 |
| 8 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 109553 | 72208 | 70982 | -1226 | 2782 | 3236 | 13 |
| 9 | `_private.Init.Data.BitVec.Bitblast.«0».BitVec.ssubOverflow_eq._proof_1_4` | defn | 40104 | 29919 | 28701 | -1218 | 1244 | 1549 | 12 |
| 10 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_min_distrib_right._proof_1_1` | defn | 38651 | 32445 | 31227 | -1218 | 1412 | 1760 | 16 |

Ten largest losses of uniform w = 1 against MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `Lean.Meta.Simp.Config.mk.inj` | defn | 2789 | 1984 | 2030 | 46 | 130 | 133 | 1 |
| 2 | `_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_eq_of._proof_1_16` | defn | 12097 | 8654 | 8670 | 16 | 334 | 377 | 7 |
| 3 | `instLawfulMonadAttachStateTOfLawfulMonad` | defn | 5055 | 3843 | 3854 | 11 | 149 | 178 | 5 |
| 4 | `Nat.pow_mod` | defn | 1771 | 1522 | 1531 | 9 | 42 | 56 | 5 |
| 5 | `Std.Iter.anyM_filterM` | defn | 3984 | 2904 | 2912 | 8 | 97 | 102 | 4 |
| 6 | `Std.Iter.toArray_map` | defn | 1970 | 1679 | 1687 | 8 | 38 | 40 | 2 |
| 7 | `Vector.mapIdx_setIfInBounds` | defn | 1614 | 1305 | 1313 | 8 | 41 | 43 | 4 |
| 8 | `Vector.map_reverse` | defn | 1456 | 1251 | 1259 | 8 | 36 | 38 | 4 |
| 9 | `StateT.run_controlAt` | defn | 2429 | 2026 | 2033 | 7 | 49 | 56 | 3 |
| 10 | `Std.IterM.all_filterM` | defn | 3293 | 2569 | 2575 | 6 | 61 | 63 | 1 |

### w = 2

- Certified: **55358** of 55386; failures: **28**.
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`: 26
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824`: 2
    - `Nat.Internal.Linear.ExprCnstr.denote_toNormPoly` (N 525, 27236 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Range.Polymorphic.IntLemmas.«0».Int.size_rco._proof_1_1` (N 2537, 10828 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `List.min_findIdx_findIdx` (N 932, 23713 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `List.cons_append_cons_perm` (N 226, 21623 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `List.zip_eq_append_iff` (N 439, 17922 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT` (N 3608, 25207 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Array.zip_eq_append_iff` (N 439, 18000 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Std.LinearPreorderPackage.ofOrd._proof_9` (N 401, 27134 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Array.Extract.«0».Array.push_extract_getElem._proof_1_1` (N 5459, 13407 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Int.fdiv_eq_ediv` (N 1262, 33021 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
- Output checks on certified constants: real length = fixed + `variableBytes` for 55358; decode/re-encode/expand/exact equality ok for 55358, **0** failed; W1 distinct subterms = this harness's `N` for 55358; class counts and components equal to this harness's reimplementation of W1's definitions for 55358, **0** different.
- Classes (W1, certified): certain-stored 1216713, certain-excluded 6417329, uncertain 766911, low degree 3473646; components 537949; lower count bracket chosen in 37 constants.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| largest uncertain component (W1) | 0 | 2 | 5 | 10 | 20 | 2.24 |
| search states | 0 | 15 | 171 | 3293 | 776614 | 483.15 |
| uniform table size | 0 | 7 | 66 | 321 | 4474 | 27.97 |
| optimizer wall time (µs), all runs | 2 | 210 | 2517 | 47081 | 98799418 | 21681.45 |

Totals over the 55358 certified constants:

| encoding | total bytes | vs heuristic | vs MSS |
|---|---:|---:|---:|
| heuristic (stored) | 79830766 | 0 (+0.00%) | 11532808 (+16.89%) |
| MSS (current tiers) | 68297958 | -11532808 (−14.45%) | 0 (+0.00%) |
| uniform w = 2, real (current tiers) | 67593621 | -12237145 (−15.33%) | -704337 (−1.03%) |
| uniform w = 2, scheme F widths | 66954321 | -12876445 (−16.13%) | -1343637 (−1.97%) |
| uniform w = 2, model length | 68379047 | -11451719 (−14.34%) | 81089 (+0.12%) |
| unshared | 1038467344 | 958636578 (+1200.84%) | 970169386 (+1420.50%) |

Uniform w = 2 (real) vs MSS per constant: better 21751, equal 6098, worse 27509. Gains p50 14, p90 61, max 5252; losses p50 5, p90 14, max 929. Versus the heuristic: better 46968, equal 3003, worse 5387.

Ten largest gains of uniform w = 2 over MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 156976 | 105389 | 100137 | -5252 | 4454 | 5146 | 12 |
| 2 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 142164 | 97145 | 92057 | -5088 | 4143 | 4703 | 9 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 141015 | 96716 | 91977 | -4739 | 4107 | 4678 | 9 |
| 4 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 154009 | 102666 | 98554 | -4112 | 4303 | 4919 | 9 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 156535 | 104331 | 100241 | -4090 | 4474 | 5136 | 12 |
| 6 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | defn | 170285 | 104522 | 100736 | -3786 | 4067 | 4874 | 6 |
| 7 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4` | defn | 65930 | 45467 | 42134 | -3333 | 1883 | 2294 | 10 |
| 8 | `_private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1` | defn | 109553 | 72208 | 69075 | -3133 | 2793 | 3236 | 7 |
| 9 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 104173 | 76309 | 73308 | -3001 | 3135 | 3640 | 15 |
| 10 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_3` | defn | 67894 | 46372 | 43458 | -2914 | 2012 | 2477 | 10 |

Ten largest losses of uniform w = 2 against MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `Std.Iter.step_flatMapAfterM` | defn | 62751 | 35912 | 36841 | 929 | 1634 | 1858 | 6 |
| 2 | `Std.IterM.toList_filterMapM_map` | defn | 56179 | 33661 | 34571 | 910 | 1623 | 1820 | 5 |
| 3 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux` | defn | 72333 | 52808 | 53537 | 729 | 2163 | 2763 | 2 |
| 4 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_ne.match_1_1` | defn | 16798 | 9309 | 9913 | 604 | 163 | 199 | 15 |
| 5 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 90971 | 53900 | 54484 | 584 | 2411 | 2712 | 5 |
| 6 | `Std.IterM.toList_mapM_eq_toList_filterMapM` | defn | 40698 | 25402 | 25922 | 520 | 1228 | 1396 | 7 |
| 7 | `Std.IterM.step_mapWithPostcondition` | defn | 15716 | 8652 | 9163 | 511 | 348 | 413 | 6 |
| 8 | `Std.IterM.step_filterMapWithPostcondition` | defn | 13584 | 8208 | 8711 | 503 | 368 | 419 | 3 |
| 9 | `Std.IterM.toList_map_eq_toList_mapM` | defn | 33801 | 21867 | 22363 | 496 | 1086 | 1233 | 9 |
| 10 | `Std.IterM.step_mapM` | defn | 17607 | 9869 | 10357 | 488 | 414 | 492 | 5 |

### w = 3

- Certified: **55338** of 55386; failures: **48**.
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`: 46
  - `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824`: 2
    - `List.findIdx?_eq_some_iff_findIdx_eq` (N 1175, 27030 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Std._aux_Init_Data_Slice_Notation___macroRules_term__[_]_1` (N 797, 35854 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Lean.Grind.Linarith.diseq_split` (N 699, 14031 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Lean.Grind.not_eq_prop` (N 278, 31494 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Range.Polymorphic.IntLemmas.«0».Int.size_rco._proof_1_1` (N 2537, 10632 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `List.min_findIdx_findIdx` (N 932, 25713 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Std.IterM.DefaultConsumers.forIn'_eq_forIn'._unary` (N 4675, 45419 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `List.eraseP_comm` (N 764, 38566 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `Lean.Grind.imp_eq` (N 249, 21377 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
    - `_private.Init.Data.Nat.Internal.SOM.«0».Nat.Internal.SOM.Mon.mul_denote.go` (N 1034, 35324 ms): `Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576`
- Output checks on certified constants: real length = fixed + `variableBytes` for 55338; decode/re-encode/expand/exact equality ok for 55338, **0** failed; W1 distinct subterms = this harness's `N` for 55338; class counts and components equal to this harness's reimplementation of W1's definitions for 55338, **0** different.
- Classes (W1, certified): certain-stored 1091768, certain-excluded 6903959, uncertain 672738, low degree 3209123; components 478828; lower count bracket chosen in 30 constants.

| Metric | min | median | p90 | p99 | max | mean |
|---|---:|---:|---:|---:|---:|---:|
| largest uncertain component (W1) | 0 | 1 | 5 | 11 | 20 | 2.08 |
| search states | 0 | 9 | 171 | 3680 | 1040448 | 582.86 |
| uniform table size | 0 | 5 | 55 | 293 | 4427 | 23.82 |
| optimizer wall time (µs), all runs | 2 | 179 | 2578 | 58856 | 103226807 | 35617.10 |

Totals over the 55338 certified constants:

| encoding | total bytes | vs heuristic | vs MSS |
|---|---:|---:|---:|
| heuristic (stored) | 79849102 | 0 (+0.00%) | 11547818 (+16.91%) |
| MSS (current tiers) | 68301284 | -11547818 (−14.46%) | 0 (+0.00%) |
| uniform w = 3, real (current tiers) | 68216736 | -11632366 (−14.57%) | -84548 (−0.12%) |
| uniform w = 3, scheme F widths | 67644231 | -12204871 (−15.28%) | -657053 (−0.96%) |
| uniform w = 3, model length | 74603766 | -5245336 (−6.57%) | 6302482 (+9.23%) |
| unshared | 1061642946 | 981793844 (+1229.56%) | 993341662 (+1454.35%) |

Uniform w = 3 (real) vs MSS per constant: better 12687, equal 3526, worse 39125. Gains p50 14, p90 75, max 5398; losses p50 9, p90 29, max 1523. Versus the heuristic: better 43719, equal 2683, worse 8936.

Ten largest gains of uniform w = 3 over MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1` | defn | 142164 | 97145 | 91747 | -5398 | 4097 | 4703 | 9 |
| 2 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1` | defn | 156976 | 105389 | 100158 | -5231 | 4403 | 5146 | 13 |
| 3 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1` | defn | 141015 | 96716 | 91536 | -5180 | 4059 | 4678 | 9 |
| 4 | `_private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_4` | defn | 65930 | 45467 | 41250 | -4217 | 1840 | 2294 | 10 |
| 5 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1` | defn | 156535 | 104331 | 100152 | -4179 | 4427 | 5136 | 13 |
| 6 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1` | defn | 154009 | 102666 | 98600 | -4066 | 4279 | 4919 | 7 |
| 7 | `_private.Init.Data.BitVec.Lemmas.«0».BitVec.getMsbD_extractLsb._proof_1_4` | defn | 48987 | 32947 | 29427 | -3520 | 1346 | 1702 | 20 |
| 8 | `_private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_3` | defn | 67894 | 46372 | 42946 | -3426 | 1967 | 2477 | 10 |
| 9 | `_private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1` | defn | 76215 | 57498 | 54434 | -3064 | 2464 | 2854 | 14 |
| 10 | `_private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1` | defn | 104173 | 76309 | 73358 | -2951 | 3121 | 3640 | 7 |

Ten largest losses of uniform w = 3 against MSS:

| # | constant | kind | heuristic B | MSS B | uniform real B | Δ (uniform − MSS) | uniform table | MSS table | largest comp. |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | `Std.Iter.step_flatMapAfterM` | defn | 62751 | 35912 | 37435 | 1523 | 1552 | 1858 | 6 |
| 2 | `Std.Iter.step_flatMapAfter` | defn | 34745 | 22093 | 23338 | 1245 | 993 | 1225 | 12 |
| 3 | `Std.IterM.toList_filterMapM_map` | defn | 56179 | 33661 | 34857 | 1196 | 1535 | 1820 | 3 |
| 4 | `_private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.«0».Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | defn | 90971 | 53900 | 54948 | 1048 | 2312 | 2712 | 5 |
| 5 | `Std.IterM.toList_filterMapWithPostcondition` | defn | 31006 | 20058 | 20928 | 870 | 878 | 1078 | 6 |
| 6 | `Std.Iter.step_filterMap` | defn | 35128 | 22728 | 23584 | 856 | 1024 | 1279 | 9 |
| 7 | `Std.IterM.toList_mapWithPostcondition` | defn | 25948 | 16960 | 17681 | 721 | 745 | 939 | 4 |
| 8 | `Std.IterM.toList_mapM_eq_toList_filterMapM` | defn | 40698 | 25402 | 26087 | 685 | 1139 | 1396 | 7 |
| 9 | `Std.IterM.toList_map_eq_toList_mapM` | defn | 33801 | 21867 | 22516 | 649 | 1026 | 1233 | 6 |
| 10 | `_private.Init.Data.Nat.ToString.«0».Nat.digitChar_ne.match_1_1` | defn | 16798 | 9309 | 9947 | 638 | 141 | 199 | 15 |

### Ten slowest optimizer runs (of 166158)

| # | constant | w | ms | certified | `N` | largest comp. | states | error |
|---:|---|---:|---:|---|---:|---:|---:|---|
| 1 | `Lean.Grind.Config.mk.injEq` | 1 | 108188 | false | 3512 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 2 | `Lean.Grind.Config.mk.injEq` | 3 | 103226 | false | 3512 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 3 | `Lean.Grind.Config.mk.injEq` | 2 | 98799 | false | 3512 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 4 | `Lean.Meta.Simp.Config.mk.injEq` | 2 | 90260 | false | 1994 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 5 | `Lean.Meta.Simp.Config.mk.injEq` | 1 | 87968 | false | 1994 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 6 | `Lean.Meta.Simp.Config.mk.injEq` | 3 | 82698 | false | 1994 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.costEvals) 1073741824 |
| 7 | `_private.Init.Data.Array.Extract.«0».Array.mem_extract_iff_getElem._proof_1_3` | 1 | 62649 | false | 3876 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576 |
| 8 | `_private.Init.Data.BitVec.Bitblast.«0».BitVec.addRecAux_eq_of._proof_1_21` | 1 | 57389 | false | 2298 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576 |
| 9 | `Nat.Internal.Linear.Poly.denote_eq_cancelAux` | 1 | 55674 | false | 2804 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576 |
| 10 | `_private.Init.Data.Int.LemmasAux.«0».Int.max_assoc._proof_1_1` | 1 | 51317 | false | 5794 | 0 | 0 | Ix.Sharing.Exact.SharingError.resourceExhausted (Ix.Sharing.Exact.Resource.states) 1048576 |

Total optimizer wall time over all runs: 6875358 ms.

### Lower-bound gap: real lengths minus the w = 1 model optimum

Over the 55263 rooted constants certified at w = 1, 2 and 3. Σ model(w = 1) = 59370988.

| encoding (current tiers) | Σ bytes | Σ (bytes − model w=1) | % of Σ model | constants below the model |
|---|---:|---:|---:|---:|
| heuristic (stored) | 78696174 | 19325186 | +32.55% | 0 |
| MSS | 67438618 | 8067630 | +13.59% | 0 |
| uniform w = 1 output | 66615107 | 7244119 | +12.20% | 0 |
| uniform w = 2 output | 66778657 | 7407669 | +12.48% | 0 |
| uniform w = 3 output | 67406916 | 8035928 | +13.54% | 0 |
| best of the above, per constant | 66331917 | 6960929 | +11.72% | 0 |

### W1 classes vs this harness's own classification (corrected `payloadMin`)

Totals over the constants certified at all three widths. The definitions differ (see the hand-written section), so equality is not expected.

| w | own certain-stored | W1 certain-stored | own certain-excluded (candidates) | W1 certain-excluded (all terms) | own uncertain | W1 uncertain | own max component | W1 max component |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1842180 | 1437377 | 0 | 5748024 | 444030 | 848833 | 16 | 21 |
| 2 | 1460911 | 1189917 | 344992 | 6340304 | 480307 | 751301 | 14 | 20 |
| 3 | 1235457 | 1063687 | 563890 | 6827490 | 486863 | 658633 | 19 | 20 |

---

Metadata study output (`--meta`) for Init, unedited:

## Metadata study: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe`

- File: 195387870 bytes; blobs 26836; anonymous constants 56622; names 344786; Named entries 66621 (2000 with `original`); comms 0. Scan time 18290 ms.
- Byte categories sum to 195387870 bytes: **equal to the file size**.
- Cross-check against a full `Ixon.deEnv` load: named 66621 vs 66621, blobs 26836 vs 26836, constants 56622 vs 56622, non-empty metaSharing 0 vs 0, metaSharing entries 0 vs 0, metaSharing expression bytes (`serExpr`) 0 vs 0, metaRefs 0 vs 0, metaUnivs 2363 vs 2363, entries with `original` 2000 vs 2000, original metaSharing entries 0 vs 0: **all equal**.

| component | bytes | % of file |
|---|---:|---:|
| header: version, consts Merkle root, main, assumptions | 35 | 0.00% |
| §1 blobs: count, addresses, length prefixes | 885986 | 0.45% |
| §1 blobs: payload | 1948624 | 1.00% |
| §2 constants: count, addresses, length prefixes | 1971518 | 1.01% |
| §2 constants: bodies (the anonymous constants) | 80208288 | 41.05% |
| §3 anonymous hints | 108763 | 0.06% |
| §4 names: count and addresses | 11033156 | 5.65% |
| §4 names: components (tag, parent address, string/number bytes) | 13621793 | 6.97% |
| §5 Named: count, name and constant keys | 460240 | 0.24% |
| §5 Named: per-name hints | 66621 | 0.03% |
| §5 Named: metadata blob length prefixes | 161358 | 0.08% |
| §5 ConstantMeta info (variant fields, name indices, root indices) | 1379169 | 0.71% |
| §5 ExprMeta arena | 82418893 | 42.18% |
| §5 metaSharing expressions (with count) | 66621 | 0.03% |
| §5 metaRefs (with count) | 66621 | 0.03% |
| §5 metaUnivs (with count) | 80359 | 0.04% |
| §5 univPatches (with count) | 84608 | 0.04% |
| §5 original: tag and address | 130621 | 0.07% |
| §5 original ConstantMeta info | 54031 | 0.03% |
| §5 original ExprMeta arena | 631426 | 0.32% |
| §5 original metaSharing expressions | 2000 | 0.00% |
| §5 original metaRefs | 2000 | 0.00% |
| §5 original metaUnivs | 2324 | 0.00% |
| §5 original univPatches | 2814 | 0.00% |
| §6 comms | 1 | 0.00% |

- Section totals: §2 constants 82179806 (42.06%); §5 Named 85609706 (43.82%); §4 names 24654949 (12.62%); §1 blobs 2834610 (1.45%).

ExprMeta arena by node kind (primary metadata; `original` metadata in the last two columns):

| node kind | nodes | bytes | % of file | original nodes | original bytes |
|---|---:|---:|---:|---:|---:|
| leaf | 505548 | 505548 | 0.26% | 18649 | 18649 |
| app | 13111962 | 66602568 | 34.09% | 81026 | 270371 |
| binder | 1184509 | 8547545 | 4.37% | 41186 | 272337 |
| letBinder | 18979 | 199890 | 0.10% | 480 | 4055 |
| ref | 1340653 | 6265979 | 3.21% | 14117 | 63294 |
| prj | 5879 | 35254 | 0.02% | 63 | 315 |
| mdata | 12445 | 159222 | 0.08% | 5 | 52 |
| callSite | 0 | 0 | 0.00% | 0 | 0 |
| etaCallSite | 0 | 0 | 0.00% | 0 | 0 |

### metaSharing

- Named entries with non-empty `metaSharing`: 0 of 66621; with non-empty `original` metaSharing: 0. Entries per non-empty table: min 0, median 0, p90 0, p99 0, max 0.
- metaRefs entries: 0; metaUnivs entries: 2363.
- Analysis errors (constants not analysed): 0.

| metadata | constants | entries | current bytes | unshared bytes | re-encoded against the primary table | distinct entries | current, deduplicated | re-encoded, deduplicated | entries equal to a primary subterm | equal to a primary table entry | Share nodes in entries |
|---|---:|---:|---|---:|---:|---:|---:|---:|---|---:|---:|
| primary `ConstantMeta` | 0 | 0 | 0 (0.00% of file) | 0 | 0 | 0 | 0 | 0 | 0 (0 B) | 0 | 0 |
| `Named.original` | 0 | 0 | 0 (0.00% of file) | 0 | 0 | 0 | 0 | 0 | 0 (0 B) | 0 | 0 |

---

Metadata study output (`--meta`) for Mathlib, unedited:

## Metadata study: `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe`

- File: 3343271273 bytes; blobs 341233; anonymous constants 679499; names 4811656; Named entries 778344 (22265 with `original`); comms 0. Scan time 181501 ms.
- Byte categories sum to 3343271273 bytes: **equal to the file size**.

| component | bytes | % of file |
|---|---:|---:|
| header: version, consts Merkle root, main, assumptions | 35 | 0.00% |
| §1 blobs: count, addresses, length prefixes | 11264011 | 0.34% |
| §1 blobs: payload | 15945558 | 0.48% |
| §2 constants: count, addresses, length prefixes | 23697505 | 0.71% |
| §2 constants: bodies (the anonymous constants) | 1468890902 | 43.94% |
| §3 anonymous hints | 1304352 | 0.04% |
| §4 names: count and addresses | 153972996 | 4.61% |
| §4 names: components (tag, parent address, string/number bytes) | 190199903 | 5.69% |
| §5 Named: count, name and constant keys | 6146192 | 0.18% |
| §5 Named: per-name hints | 778344 | 0.02% |
| §5 Named: metadata blob length prefixes | 2063780 | 0.06% |
| §5 ConstantMeta info (variant fields, name indices, root indices) | 19467468 | 0.58% |
| §5 ExprMeta arena | 1419908472 | 42.47% |
| §5 metaSharing expressions (with count) | 821273 | 0.02% |
| §5 metaRefs (with count) | 778344 | 0.02% |
| §5 metaUnivs (with count) | 3185897 | 0.10% |
| §5 univPatches (with count) | 5842782 | 0.17% |
| §5 original: tag and address | 1490824 | 0.04% |
| §5 original ConstantMeta info | 649300 | 0.02% |
| §5 original ExprMeta arena | 16702816 | 0.50% |
| §5 original metaSharing expressions | 22265 | 0.00% |
| §5 original metaRefs | 22265 | 0.00% |
| §5 original metaUnivs | 49569 | 0.00% |
| §5 original univPatches | 66419 | 0.00% |
| §6 comms | 1 | 0.00% |

- Section totals: §2 constants 1492588407 (44.64%); §5 Named 1477996010 (44.21%); §4 names 344172899 (10.29%); §1 blobs 27209569 (0.81%).

ExprMeta arena by node kind (primary metadata; `original` metadata in the last two columns):

| node kind | nodes | bytes | % of file | original nodes | original bytes |
|---|---:|---:|---:|---:|---:|
| leaf | 8211930 | 8211930 | 0.25% | 252288 | 252288 |
| app | 219151448 | 1153185700 | 34.49% | 2376746 | 10230751 |
| binder | 17838297 | 138855710 | 4.15% | 621887 | 4679226 |
| letBinder | 313517 | 3757214 | 0.11% | 643 | 5488 |
| ref | 23053693 | 112639845 | 3.37% | 308953 | 1493213 |
| prj | 54934 | 358710 | 0.01% | 1120 | 7556 |
| mdata | 113930 | 1465345 | 0.04% | 40 | 1059 |
| callSite | 320 | 45304 | 0.00% | 0 | 0 |
| etaCallSite | 0 | 0 | 0.00% | 0 | 0 |

### metaSharing

- Named entries with non-empty `metaSharing`: 7 of 778344; with non-empty `original` metaSharing: 0. Entries per non-empty table: min 30, median 61, p90 114, p99 114, max 114.
- metaRefs entries: 0; metaUnivs entries: 413181.

| Named entry | §2 rank | metaSharing entries | bytes |
|---|---:|---:|---:|
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_6` | 240625 | 61 | 4970 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_5` | 225718 | 61 | 4970 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_1` | 36564 | 30 | 2342 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_4` | 299841 | 114 | 9435 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_3` | 212626 | 114 | 9435 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_2` | 563607 | 30 | 2342 |
| `Lean.Meta.Grind.Arith.Linear.EqCnstr._sizeOf_7` | 195384 | 114 | 9435 |

- Analysis errors (constants not analysed): 0.

| metadata | constants | entries | current bytes | unshared bytes | re-encoded against the primary table | distinct entries | current, deduplicated | re-encoded, deduplicated | entries equal to a primary subterm | equal to a primary table entry | Share nodes in entries |
|---|---:|---:|---|---:|---:|---:|---:|---:|---|---:|---:|
| primary `ConstantMeta` | 7 | 524 | 42929 (0.00% of file) | 42929 | 5495 | 203 | 14599 | 2586 | 412 (34613 B) | 288 | 0 |
| `Named.original` | 0 | 0 | 0 (0.00% of file) | 0 | 0 | 0 | 0 | 0 | 0 (0 B) | 0 | 0 |
