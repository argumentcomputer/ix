# Exact sharing: production performance (plan P4)

This document is the P4 deliverable of [`sharing-minimum.md`](sharing-minimum.md), "Production viability
measurements". It gathers in one place, for a PR reviewer, what has been measured on two corpora:

- `Init`, by W3, in [`sharing-minimum-measurements.md`](sharing-minimum-measurements.md);
- Mathlib, by W5, in [`sharing-minimum-measurements-mathlib.md`](sharing-minimum-measurements-mathlib.md);
- both corpora, by W2 in this document: the canonical tiered construction in Rust under both Share
  layouts, and the Lean/Rust differential.

The document reports measurements. The design decisions it refers to are recorded in the plan (§12).

**Canonical construction.** Since plan §12.11, phase 1 runs at each width w ∈ {1, 2, 3}. Each run goes
through phases 2 and 3, and the result with the fewest real layout bytes is kept ("best of three"). The
canonical numbers below are that rule's.

They were measured through the experiment hook `normalize_constant_sharing_tiered_at_width`
(`faf1a7c7`). That hook runs exactly the three candidate constructions the rule compares. The Rust and
Lean canonical entry points do not yet implement the rule; W1 and W2 are porting it.

Numbers for the earlier rule, which chose the width from the candidate count `K` ("K-based"), are marked
**superseded**. They are kept because they are what led to §12.11 and because the Lean/Rust parity and
timing runs used that rule.

**Pointers.** Every number carries a pointer in square brackets to the log or document it comes from;
the keys are listed under [Sources](#sources). A number derived from two sources, for example by a CSV
join, cites both.

## Contents

- [Summary](#summary)
- [Sources](#sources)
- [Corpora](#corpora)
- [What is measured](#what-is-measured)
- [Bytes](#bytes)
- [Certification and resource limits](#certification-and-resource-limits)
- [Wall time and memory](#wall-time-and-memory)
- [Phase statistics](#phase-statistics)
- [Slowest constants](#slowest-constants)
- [Lean/Rust parity](#leanrust-parity)
- [The phase-1 width experiment](#the-phase-1-width-experiment)
- [What is not covered](#what-is-not-covered)
- [Reproduction](#reproduction)
- [Appendix A: runner reports and joins](#appendix-a-runner-reports-and-joins)
- [Appendix B: differential tallies](#appendix-b-differential-tallies)

## Summary

- **Corpora.** Init has 56,622 constants and 80,208,288 stored bytes [W3]. Mathlib (the whole
  `import Mathlib` environment) has 679,499 constants and 1,468,890,902 stored bytes [W5].
- **Bytes, canonical (best of three), rooted constants** [X1] [X2]:

  | layout | corpus | vs heuristic | vs MSS at the same widths |
  |---|---|---:|---:|
  | TagN | Init | −16.92% | −1.41% |
  | TagN | Mathlib | −23.64% | −0.82% |
  | Tag4 | Init | −16.10% | −1.88% |
  | Tag4 | Mathlib | −22.70% | −1.15% |

  - **Never larger than unshared** on either corpus.
  - **Larger than MSS** for 5 Init and 903 Mathlib constants (TagN), and for 3 and 861 (Tag4).
  - **The largest loss** is one Mathlib outlier at +1,485 bytes (TagN; +1,468 with the Kahn order). It
    is a tie-break artifact of the Kahn order: MSS with the construction's tie rule (structural ID)
    gives the same 67,367 bytes as storing MSS's set, and over all of Mathlib storing every candidate is
    never larger than MSS under the same tie rule [X5] [X6] [P §12.15].
- **Rejected alternatives.**
  - The K-based width rule: on Mathlib it was larger than MSS in total (+0.46% TagN, +0.21% Tag4),
    larger on about a third of constants [J2]. This led to §12.11.
  - A fourth candidate storing every candidate ("best of four") saves only 2,896 bytes over Mathlib
    (TagN) [X4] [P §12.14].
- **Certification.**
  - Rust, with the reclassifying branch and bound: every constant of both corpora certifies at every
    width under both layouts with the default limits [X1] [X2].
  - The old subset enumeration failed `States` in phase 1 on 25 Init and 342 Mathlib constants [R1] [R2].
  - Lean and Rust, best of three: no exhaustion on any Init constant [D7].
- **Time and memory (Rust, best of three, TagN layout)** [X1] [X3]:
  - Init: 43.2 s on 8 threads, 414.9 s on 1 thread.
  - Mathlib: 1,094 s on 8 threads, peak RSS 4.8 GB.
  - For comparison, one K-based construction per constant took 184 s over Mathlib on 20 threads [R3].
  - The machine was shared, so these timings are indicative.
- **Lean/Rust parity:**
  - Best of three: identical bytes for all 56,622 Init constants under both layouts [D7].
    The Mathlib-sample run under the best of three [D8] was aborted without a result: it used the
    phase-2 order that §12.14 replaces.
  - K-based (superseded): 0 byte disagreements on all of Init, on a 20,263-constant Mathlib sample, and
    on half of Mathlib (339,749 constants) [D1]–[D6].
  - Every one-sided exhaustion was Lean's, and every one gave Rust's bytes once its limit was raised.
    With `maxMaterializeWork` = 2^36 (`3ddda798`) there are none.
- **Not covered:**
  - distance to the true minimum, because the width-state oracle runs on small inputs only;
  - serialized unshared sizes for 619 Mathlib constants;
  - serialized TagN bytes;
  - Lean on all of Mathlib;
  - best-of-three byte totals and Lean/Rust parity with the Kahn order beyond the first tier (the totals
    above predate it; see [X6] for the outlier).

## Sources

`$S` is the session scratchpad,
`/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad`. Its files are
not tracked. Each report and join this document cites is reproduced unedited in Appendix A, and each
differential tally in Appendix B.

Terms used in the table:

- **runner:** the Rust example `crates/ixon/examples/sharing_corpus.rs`, release build;
- **differential:** the Lean/Rust suite `exact-sharing-ffi` (`Tests/Ix/SharingExactFFI.lean`) in corpus
  mode;
- **search, old:** phase 1's uniform search used the subset enumeration;
- **search, new:** phase 1 used W1's reclassifying branch and bound (W1 `985de744`, Rust `0aca9b39`).

| key | what | code | search | file(s) |
|---|---|---|---|---|
| [P] | the plan, §0 and §12 | `6da48067` | | `docs/sharing-minimum.md` |
| [W3] | Init corpus harness (`sharing-study`), tenth run | see the doc | | `docs/sharing-minimum-measurements.md` |
| [W5] | Mathlib corpus harness (`sharing-study`) | `5f284b7a` | | `docs/sharing-minimum-measurements-mathlib.md` |
| [X1] | **best of three**, TagN layout, Init and Mathlib, 8 threads | `faf1a7c7` | new | `$S/w2/p4/wx_{init,ml}_tagN.{md,err,csv}`, `wx_*_tagN_{join,best}.txt` |
| [X2] | **best of three**, Tag4 layout, Init and Mathlib, 8 threads | `faf1a7c7` | new | `$S/w2/p4/wx_{init,ml}_tag4.{md,err,csv}`, `wx_*_tag4_{join,best}.txt` |
| [X3] | best of three, TagN layout, Init, 1 thread | `faf1a7c7` | new | `$S/w2/p4/wx_init_tagN_t1.{md,err,csv}` |
| [X4] | best of four (w = 1, 2, 3 and all candidates), both layouts, Init and Mathlib, 12 threads | `94882265` | new | `$S/w2/p4/wx4_{init,ml}_{tagN,tag4}.{md,err,csv}`, `wx4_*_{join,best}.txt` |
| [X5] | MSS (ties by structural ID and by blake3) against "all", all of Mathlib; entry-level diffs | `7b083108` | new | `$S/w2/p6/cmp_{id,blake3}.{md,err,csv}`, `outlier_diff2.md`, `diff_up7_blake3.md`, `diff_sample13_id.md` |
| [X6] | the outlier with the Kahn order, per width and "all", both layouts | `0ef72793` | new | `$S/w2/p5/outlier_kahn_{tagN,tag4}.csv` |
| [R1] | K-based, runner, Init, TagN layout, 16 threads | `2072a9bf` | old | `$S/w2/init_tiered.{md,err,csv}` |
| [R2] | K-based, runner, Mathlib, TagN layout, 20 threads | `2072a9bf` | old | `$S/w2/mathlib_tiered.{md,err,csv}` |
| [R3] | K-based, runner, Mathlib, TagN layout, 20 threads | `e4c0dead` | new | `$S/w2/mathlib_tiered_bb.{md,err,csv}` |
| [R4] | K-based, runner, Init, TagN layout, 20 threads | `e4c0dead` | new | `$S/w2/p4/init_tagN_t20.{md,err,csv}` |
| [R5] | K-based, runner, Init, Tag4 layout, 20 threads | `e4c0dead` | new | `$S/w2/p4/init_tag4_t20.{md,err,csv}` |
| [R6] | K-based, runner, Init, TagN layout, 1 thread | `e4c0dead` | new | `$S/w2/p4/init_tagN_t1.{md,err,csv}` |
| [R7] | K-based, runner, Mathlib, Tag4 layout, 20 threads | `e4c0dead` | new | `$S/w2/p4/ml_tag4_t20.{md,err,csv}` |
| [J1] | K-based, join of [W3]'s CSV with [R4] and [R5] | | | `$S/w2/p4/init_join.txt`, `init_byw.txt` |
| [J2] | K-based, join of [W5]'s CSV with [R3] and [R7] | | | `$S/w2/p4/ml_join.txt`, `ml_byw.txt` |
| [D0] | differential, Init, the 10 Lean-only constants, limit diagnosis | `86df8874` | old | `$S/w2/diag_init.log` |
| [D1] | differential, Init, all constants, 1 process | `871eef12` | old | `$S/w2/corpus_full.log` |
| [D2] | differential, Init, all constants, 6 processes | `e4c0dead` | new | `$S/w2/init_bb_s{0..5}.log` |
| [D3] | differential, Mathlib sample, 2 processes | `86df8874` | old | `$S/w2/mathlib_diff_{a,b}.log` |
| [D4] | differential, Mathlib sample, 4 processes | `e4c0dead` | new | `$S/w2/ml_bb_s{0..3}.log` |
| [D5] | differential, the Lean-only constants of [D2]/[D4] | `3ddda798` | new | `$S/w2/lo_s{0..3}.log`, `lo_init.log` |
| [D6] | differential, K-based, Mathlib, all constants in 6 address shards; 3 shards (339,749 constants) completed | `3ddda798` | new | `$S/w2/p4/lf_s{0,3,4}.log` (and the empty `lf_s{1,2,5}.log`) |
| [D7] | differential, **best of three**, Init, all constants, tiered-TagN and tiered-Tag4, 6 processes | `a80c16cf` | new | `$S/w2/p4/b3_init_s{0..5}.log` |
| [D8] | differential, **best of three**, Mathlib sample, tiered-TagN and tiered-Tag4, 4 processes; aborted, no tallies | `a80c16cf` | new | `$S/w2/p4/b3_ml_s{0..3}.log` |

Notes on the sources:

- **Code identity.** No file under `crates/` changed between `e4c0dead` and `8f0ffa04`. The runner binary
  for [R4]–[R7] was built at `e4c0dead`. The binary for [X1]–[X3] was built from `faf1a7c7`'s source
  before two lint-only edits to the runner; `faf1a7c7` itself refactors the canonical path into
  `tiered_at(…, None)` without changing it. The Lean side of [D5]/[D6] was built at `3ddda798`; later
  commits change only documentation and Rust. [X4] used a copy of the runner built at `94882265`. [X5] and [X6] used runner binaries
  built from the sources of `7b083108` and `0ef72793` before those were committed; only lint and
  documentation edits followed. [D7] and [D8]
  used `IxTests` built at `a80c16cf`, whose Lean side is W1's best of three (`3eb09b9c`).
- **The Mathlib sample** used by [D3]/[D4] has 20,263 constants: every 50th constant in address order,
  plus every constant with more than 2,000 R1/R2 candidates. It was written by the runner's
  `--select-out` during [R2].
- **The joins** ([J1], [J2], and the `*_join.txt` and `*_best.txt` files of [X1] and [X2]):
  - They match rows on the 16-hex-digit address prefix, as [W5] does, and are restricted to rooted
    constants.
  - They price MSS at TagN widths per constant as
    `mss_bytes − (lt8 + 2·[8,256) + 3·≥256) + (lt8f + 2·[8,1032) + 3·≥1032)`, using [W3]'s and [W5]'s
    reference counts (scheme F).
  - Their checks: 0 stored-bytes mismatches and 0 unshared-size mismatches between the study CSV and the
    runner CSV. The heuristic, MSS, scheme-F and unshared totals they compute equal those printed in [W3]
    and [W5].
  - The scripts (`join.awk`, `byw.awk`, `wxjoin.awk`, `bestjoin.awk`, `slowest.awk`) are in `$S/w2/p4/`.
- **Percentiles.** The runner and the joins use the nearest rank, rounded down (`xs[⌊(n−1)·p⌋]`). [W3] and
  [W5] use their own convention.
- **Machine.** All runs used one 24-core machine, shared throughout with other agents' builds and tests.
  Timings are therefore indicative, and no two runs had the same background load.

## Corpora

| | Init | Mathlib |
|---|---:|---:|
| file | `init.ixe` | `mathlib.ixe` |
| size | 195,387,870 B [W3 §Results] | 3,343,271,273 B [W5 §Corpus] |
| stored constants (distinct addresses) | 56,622 [W3 §Results] | 679,499 [W5 §Corpus] |
| names | 66,621 [W3 §Results] | 778,344 [W5 §Corpus] |
| constants with at least one root | 55,386 [W3 §Results] | 663,254 [W5 §Headline] |
| stored (heuristic) bytes, all constants | 80,208,288 [W3 §Results] | 1,468,890,902 [W5 §Results] |
| stored bytes, rooted constants | 80,161,846 [W3 §MSS] | 1,468,281,356 [W5 §MSS vs heuristic] |
| distinct subterms `N`: median / p99 / max | 86 / 2,015 / 27,628 [W3 §Headline] | 147 / 3,052 / 95,110 [W5 §Headline] |
| R1/R2 candidates: median / p90 / p99 / max | 34 / 232 / 1,187 / 22,458 [W3 §Headline] | 69 / 432 / 2,029 / 81,833 [W5 §Headline] |
| rooted constants with ≤ 8 candidates | 17.2% [W3 §Headline] | 10.1% [W5 §Headline] |

- **Init** is the production Lean compiler's output for `Benchmarks/CompileInit.lean`. Regenerate it with
  `lake exe ix compile Benchmarks/CompileInit.lean --out <path>` [P §0]. The production rebuild check
  reproduces all 56,622 stored constants byte for byte [W3 §Verification].
- **Mathlib** comes from `lake exe ix compile Benchmarks/Compile/CompileMathlib.lean --out <path>`, which
  does `import Mathlib` and so compiles the whole import environment [W5 §Corpus]:
  - exit 0, 7 min 29 s end to end, of which the compile itself took 152.42 s;
  - peak RSS 19,107,692 kB; 0 ungrounded constants.

  The production rebuild reproduces all 679,499 constants [W5 §Verification]. The corpus contains Init:
  56,621 of the 56,622 Init rows, all but `main` [W5 §Corpus].

## What is measured

- **Heuristic:** the stored bytes (`rawBytes`) written by the production compiler: `Ix.Sharing.applySharing`
  in Lean and its Rust twin.
- **MSS:** store every compact-DAG node with in-degree ≥ 2 and standalone size > 1, reference every
  occurrence, and order the table by priority topological order [W3 §MSS follow-up]. It is priced two
  ways:
  - in the current Tag4 format (scheme A: its real serialized length);
  - at TagN widths (scheme F: 1 byte below index 8, 2 below 1,032 and 3 beyond). For tables below 66,568
    entries this equals TagN [W5 §Share-width schemes].
- **Canonical tiered:** `canonicalSharingTiered` (Lean, `Ix/Sharing/Exact/Tiered.lean`) and
  `normalize_constant_sharing_tiered` (Rust) [P §12.8]. It has three phases:
  1. the exact uniform-model optimum at a width `w`;
  2. an exact maximum-reference first tier of 8 slots, then the pinned order;
  3. per-entry re-materialization under the layout's real widths.

  The two rules for `w` differ as follows:
  - **Best of three** [P §12.11]: run phases 1–3 at each `w ∈ {1, 2, 3}` and keep the result with the
    fewest layout bytes. Ties go to the lower `w`, then `setPrec`. Since each width yields one result,
    `setPrec` never decided in these runs.
  - **K-based (superseded)** [P §12.8]: `w = 1` if `K ≤ 8`, `2` if `K ≤ 256` (Tag4) or `K ≤ 1,032`
    (TagN), else `3`. Here `K` is the number of terms with in-degree ≥ 2 and unshared length ≥ 2.

  The construction runs under two layouts:
  - **Tag4:** the current Share encoding. Bytes are the real serialized length.
  - **TagN:** the nibble-bootstrapped Share code [P §12.7]. No serializer writes it yet, so bytes are the
    output priced with TagN Shares (`layout_bytes`); everything else is serialized exactly.
- **Unshared:** every root fully expanded, with an empty table, computed compositionally. Serialization
  confirmed it for all but 7 Init and 619 Mathlib constants, whose unshared roots exceed 16 MiB
  [W3 §Verification] [W5 §Verification].

## Bytes

### Canonical (best of three): totals over rooted constants

| encoding | Init | vs heuristic | Mathlib | vs heuristic |
|---|---:|---:|---:|---:|
| heuristic (stored) | 80,161,846 | | 1,468,281,356 | |
| MSS, Tag4 (scheme A) | 68,547,873 | −14.49% | 1,148,195,956 | −21.80% |
| MSS at TagN widths (scheme F) | 67,556,587 | −15.72% | 1,130,381,317 | −23.01% |
| **canonical, Tag4 layout** | **67,255,886** | **−16.10%** | **1,135,005,370** | **−22.70%** |
| **canonical, TagN layout** | **66,602,235** | **−16.92%** | **1,121,167,486** | **−23.64%** |
| unshared | 1,069,954,757 | | 214,351,801,952,039 | |

Sources: [X1] [X2]. The heuristic, MSS and unshared totals equal [W3 §MSS] and [W5 §MSS vs heuristic].
The scheme-F Mathlib total equals [W5 §Share-width schemes]. The Mathlib unshared total is dominated by a
few constants (the largest is 2.1·10^14 bytes) and is not meaningful as a total [W5 §Limits and coverage].

**Canonical against MSS at the same widths** [X1] [X2]:

| | Init | Mathlib |
|---|---:|---:|
| Tag4 layout − MSS (scheme A) | −1,291,987 (−1.88%) | −13,190,586 (−1.15%) |
| TagN layout − MSS (scheme F) | −954,352 (−1.41%) | −9,213,831 (−0.82%) |

**All constants**, including the rootless ones, which come out byte-identical to the stored bytes
(1,236 Init and 16,245 Mathlib constants) [X1] [X2]:

| | Init | Mathlib |
|---|---:|---:|
| stored | 80,208,288 | 1,468,890,902 |
| canonical, Tag4 layout | 67,302,328 (−16.09%) | 1,135,614,916 (−22.69%) |
| canonical, TagN layout | 66,648,677 (−16.91%) | 1,121,777,032 (−23.63%) |

### Canonical (best of three): per-constant distributions (rooted constants)

These are signed byte differences with nearest-rank percentiles [X1] [X2]. "TagN − heuristic" compares
TagN-priced bytes with the stored Tag4 bytes, so it includes the format change.

| difference | corpus | smaller / equal / larger | min | p1 | p10 | p50 | p90 | p99 | p99.9 | max |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Tag4 − heuristic | Init | 50,406 / 4,933 / 47 | −69,549 | −3,313 | −383 | −51 | −1 | 0 | 0 | 7 |
| | Mathlib | 627,129 / 35,622 / 503 | −262,502 | −6,433 | −1,031 | −125 | −4 | 0 | 0 | 36 |
| TagN − heuristic | Init | 50,406 / 4,933 / 47 | −74,928 | −3,566 | −383 | −51 | −1 | 0 | 0 | 7 |
| | Mathlib | 627,129 / 35,622 / 503 | −270,911 | −7,015 | −1,031 | −125 | −4 | 0 | 0 | 36 |
| Tag4 − MSS (A) | Init | 32,239 / 23,144 / 3 | −6,588 | −437 | −42 | −3 | 0 | 0 | 0 | 6 |
| | Mathlib | 405,933 / 256,460 / 861 | −22,505 | −361 | −31 | −3 | 0 | 0 | 1 | 266 |
| TagN − MSS (F) | Init | 32,236 / 23,145 / 5 | −7,794 | −150 | −41 | −3 | 0 | 0 | 0 | 6 |
| | Mathlib | 405,832 / 256,519 / 903 | −16,508 | −118 | −30 | −3 | 0 | 0 | 1 | 1,485 |

- **Never larger than unshared.** The canonical construction is not larger than the unshared encoding for
  any rooted constant of either corpus, under either layout [X1] [X2]. MSS is larger for 26 Mathlib
  constants [W5 §MSS larger than unshared]. The heuristic is larger for 600 Init and 20,237 Mathlib
  constants [W3 §Headline] [W5 §Headline].
- **Against MSS**, the remaining losses are few and small, except for one Mathlib constant (+1,485 bytes,
  TagN). It is described with its statistics in [The phase-1 width experiment](#the-phase-1-width-experiment).

### Superseded: the K-based width rule

These were the canonical numbers until §12.11. They are kept because they motivated the change [J1] [J2].

| encoding (rooted constants) | Init | vs MSS at the same widths | Mathlib | vs MSS at the same widths |
|---|---:|---:|---:|---:|
| K-based, Tag4 layout | 67,701,399 | −846,474 (−1.23%) | 1,150,611,314 | **+2,415,358 (+0.21%)** |
| K-based, TagN layout | 66,990,376 | −566,211 (−0.84%) | 1,135,611,532 | **+5,230,215 (+0.46%)** |

- **Per constant against MSS** [J1] [J2]:

  | layout | corpus | smaller / equal / larger | p99 | max |
  |---|---|---|---:|---:|
  | Tag4 | Init | 23,157 / 22,616 / 9,613 | 58 | 1,521 |
  | Tag4 | Mathlib | 244,165 / 199,801 / 219,288 | 261 | 9,103 |
  | TagN | Init | 23,132 / 22,616 / 9,638 | 59 | 1,293 |
  | TagN | Mathlib | 242,375 / 199,829 / 221,050 | 277 | 10,505 |
- **The excess sat in the constants whose K-based width was 2** [J1] [J2]. Mathlib under TagN against
  scheme F, by width:
  - w = 1: 181,437 constants, −2,905 B in total, 0 larger;
  - w = 2: 480,001 constants, **+5,841,564 B**, 220,221 larger;
  - w = 3: 1,816 constants, −608,444 B, 829 larger.

  The Tag4 split, against scheme A: w = 1 −2,905 B; w = 2 +3,521,148 B with 207,107 larger; w = 3
  −1,102,885 B over 23,301 constants. On Init the w = 2 class was still net smaller than MSS: −464,153 B
  (TagN), with 9,596 constants larger.
- **The K-based Tag4 layout did not even minimize Tag4 bytes** [J1] [J2] [R4] [R5] [R3] [R7].
  - The K-based TagN-layout construction, serialized in today's Tag4 format, was smaller than the
    K-based Tag4-layout construction: by 79,522 B on Init (67,621,877 vs 67,701,399) and by 2,582,709 B
    on Mathlib (1,148,028,605 vs 1,150,611,314).
  - Under Tag4, `K > 256` gave `w = 3` for 1,352 Init and 23,301 Mathlib constants; under TagN,
    `K > 1,032` gave it for 108 and 1,816.
- **Against the heuristic**, the K-based construction was larger on 438 Init and 3,722 Mathlib constants
  (Tag4 layout, at most 70 and 248 bytes) [J1] [J2]. The best of three is larger on 47 and 503,
  by at most 7 and 36 bytes [X2].
- **All constants** (K-based runner totals): Init Tag4 67,747,841 [R5], TagN 67,036,818 [R4]; Mathlib
  Tag4 1,151,220,860 [R7], TagN 1,136,221,078 [R3].

## Certification and resource limits

### Limits

**Rust** limits are `ExactSharingLimits::default()` in `crates/ixon/src/sharing_exact.rs`, used by every
runner run:

| limit | value |
|---|---:|
| `max_input_nodes` | 2^26 |
| `max_distinct_nodes` | 2^24 |
| `max_height` | 2^24 |
| `max_candidates` (width-state DP only) | 2^16 |
| `max_states` | 2^20 |
| `max_layer_states` | 2^18 |
| `max_transitions` | 2^28 |
| `max_work` | 2^36 |
| `max_output_bytes` | 2^32 |

**Lean** limits are `Ix.Sharing.Exact.Limits` in `Ix/Sharing/Exact/Basic.lean`, defaults at `9341656e`:

| limit | value |
|---|---:|
| `maxExprVisits` | 2^26 |
| `maxDepth` | 2^14 |
| `maxNodes` | 2^20 |
| `maxStates` | 2^20 |
| `maxTransitions` | 2^24 |
| `maxCostEvals` | 2^30 |
| `maxOutputBytes` | 2^28 |
| `maxMaterialize` (predicted output size) | 2^26 |
| `maxMaterializeWork` | 2^36 |

`maxMaterializeWork` was added in W1 `84dd662f`. Before it, the per-entry materialization work was
checked against `maxMaterialize`.

Exhausting a limit is an error, and limits never change the bytes of a success (the docstrings of both
limit types).

### Rust certification

| corpus | layout | old search, K-based | new search, K-based | new search, best of three (each of w = 1, 2, 3) |
|---|---|---|---|---|
| Init | TagN | 56,597 / 56,622; 25 `resource:States` [R1] | 56,622 / 56,622 [R4] [R6] | **56,622 / 56,622 at every w** [X1] |
| Init | Tag4 | not run | 56,622 / 56,622 [R5] | **56,622 / 56,622 at every w** [X2] |
| Mathlib | TagN | 679,157 / 679,499; 342 `resource:States` [R2] | 679,499 / 679,499 [R3] | **679,499 / 679,499 at every w** [X1] |
| Mathlib | Tag4 | not run | 679,499 / 679,499 [R7] | **679,499 / 679,499 at every w** [X2] |

- **The old failures were all in phase 1.** Between [R2] and [R3] only the uniform search changed. The new
  search returns the subset enumeration's set (Rust test
  `uniform_branch_and_bound_matches_subset_enumeration`), so phase 2 received the same input in both runs.
  On all 679,157 constants certified by both runs, the Tag4 and TagN bytes are identical.
- **Size of the old failures** [R1] [R2], from the CSV `status` column:
  - Init: 109–2,107 candidates (median 461); `N` 226–3,608.
  - Mathlib: 79–35,702 candidates (median 752); `N` 196–60,092.
  - Examples on Init: `Lean.Grind.Config.mk.injEq`, `Lean.Meta.Simp.Config.mk.injEq`.
  - Examples on Mathlib: `WeierstrassCurve.addSubMapCoeff_condition`,
    `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual`. All 342 are named in [R2].

### Lean certification

- **Old search, uniform optimizer alone** (W3, Init, `maxStates` 2^20):
  - certified 55,294 / 55,358 / 55,338 of 55,386 rooted constants at w = 1 / 2 / 3;
  - failures were `states` (90 / 26 / 46) and `costEvals` (2 at each width);
  - the limit sat at a largest component of 20–21 [W3 §Certification and failures].
- **New search, uniform at w = 2:** no exhaustion in Lean or Rust on any of the 56,622 Init or 20,263
  sampled Mathlib constants [D2] [D4].
- **New search, K-based tiered-TagN, before `maxMaterializeWork`:** Lean exhausted on 10 Init constants
  [D2] and 120 sampled Mathlib constants [D4].
  - Every one hit the cumulative materialization work check (`maxMaterialize` 2^26).
  - With the limit doubled until success, every one gave Rust's bytes.
  - Init needed 2^27–2^29 [D0].
  - Mathlib needed 2^27 (62 constants), 2^28 (29), 2^29 (16), 2^30 (7), 2^31 (5) and 2^32 (1,
    `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite`) [D4].
  - The needed limit grows with `k·N` (stored entries × DAG nodes), about 1.95·k·N on Init [D0] [R1].
- **At `3ddda798`** (`maxMaterializeWork` 2^36, all other limits at defaults), all 120 Mathlib and all 10
  Init constants succeed with Rust's bytes, the Init ones under both layouts [D5].
- **Old search, sample** [D3] [D4]. Two kinds of exhaustion in [D3] do not occur with the new search:
  - the 2 `maxCostEvals` cases (`mpullback_mulInvariantVectorField` and
    `mpullback_addInvariantVectorField`, in both modes);
  - 200 exhaustions on both sides (101 tiered-TagN, 99 uniform-w2).
- **K-based, half of Mathlib at `3ddda798`:** no exhaustion on either side in 339,749 constants [D6].
- **Best of three** (Lean `3eb09b9c`, Rust `a80c16cf`, default limits): no exhaustion on either side
  for any of the 56,622 Init constants under either layout [D7]. The Mathlib sample run [D8] was stopped after 2 h 5 min, before it had written any tally (its output is
  buffered); see [Lean/Rust parity](#leanrust-parity).

## Wall time and memory

### Rust runner

Column meanings:

- **processing:** the runner's own timer around the parallel loop;
- **wall:** GNU `time` for the whole process, including index parse, name table, CSV and report;
- **peak RSS:** GNU `time`'s maximum resident set size.

**Canonical, best of three** (three constructions per constant):

| corpus | layout | threads | processing | wall | peak RSS | source |
|---|---|---:|---:|---:|---:|---|
| Init | TagN | **1** | 414.9 s | 419.2 s | 311,764 kB | [X3] |
| Init | TagN | 8 | 43.2 s | 47.6 s | 485,008 kB | [X1] |
| Init | Tag4 | 8 | 44.8 s | 50.0 s | 460,272 kB | [X2] |
| Mathlib | TagN | **1** | not measured | | | |
| Mathlib | TagN | 8 | 1,094.1 s | 1,277.9 s | 4,838,516 kB | [X1] |
| Mathlib | Tag4 | 8 | 1,031.8 s | 1,176.3 s | 4,853,268 kB | [X2] |

**Superseded, K-based** (one construction per constant):

| corpus | layout | search | threads | processing | wall | peak RSS | source |
|---|---|---|---:|---:|---:|---:|---|
| Init | TagN | new | **1** | 83.1 s | 85.4 s | 307,708 kB | [R6] |
| Init | TagN | new | 20 | 7.7 s | 10.2 s | 619,440 kB | [R4] |
| Init | Tag4 | new | 20 | 7.8 s | 10.2 s | 618,880 kB | [R5] |
| Init | TagN | old | 16 | 30.6 s | 32.9 s | 571,680 kB | [R1] |
| Mathlib | TagN | new | 20 | 184.3 s | 315.9 s | 5,300,268 kB | [R3] |
| Mathlib | Tag4 | new | 20 | 209.6 s | 347.7 s | 5,263,200 kB | [R7] |
| Mathlib | TagN | old | 20 | 293.2 s | 424.7 s | 4,794,008 kB | [R2] |

A single-threaded K-based run over Mathlib was started and then stopped when §12.11 superseded the rule,
so it has no result. No single-threaded best-of-three run over Mathlib was made.

Both single-threaded Init runs shared the machine with other jobs. The best-of-three one also overlapped
the 8-thread Mathlib Tag4 experiment, which inflates its times (see [Slowest constants](#slowest-constants)).
The ratio between the two Init runs is therefore not a clean measurement of what the extra widths
cost.

Per-constant milliseconds, single-threaded:

| run | p50 | p90 | p99 | p99.9 | max |
|---|---:|---:|---:|---:|---:|
| Init, K-based [R6] | 0 | 2 | 13 | 90 | 2,261 |
| Init, best of three (sum of the three widths) [X3] | 1 | 10 | 77 | 570 | 8,801 |
| Mathlib, best of three | not measured | | | | |

### Lean and Rust in the differential

Each differential process is single-threaded and runs both implementations on every selected constant.

- **Lean Σ, Rust Σ:** sums of the per-call times the suite measures (the normalize call only).
- **Wall, peak RSS:** GNU `time` for each process. They cover both implementations, the loaded corpus,
  and any limit-diagnosis reruns.

**Best of three** (three constructions per constant and mode). These runs overlapped the 12-thread
best-of-four experiments and other jobs; the load average was 23.8 on 24 cores when they started. Their
times are therefore not directly comparable with the K-based rows below.

| corpus | constants | mode | Lean Σ | Rust Σ | processes, wall each | peak RSS each | source |
|---|---:|---|---:|---:|---|---:|---|
| Init | 56,622 | tiered-TagN | 5,415.2 s | 381.5 s | 6, 22:45–38:41 for both modes | 824,832–829,636 kB | [D7] |
| Init | 56,622 | tiered-Tag4 | 4,757.4 s | 384.6 s | (same processes) | | [D7] |

**K-based (superseded):**

| corpus | constants | mode | search | Lean Σ | Rust Σ | processes, wall each | peak RSS each | source |
|---|---:|---|---|---:|---:|---|---:|---|
| Init | 56,622 | tiered-TagN | old | 1,380.3 s | 137.1 s | 1, 4,536.4 s for 3 modes | not recorded | [D1] |
| Init | 56,622 | tiered-Tag4 | old | 1,560.2 s | 146.5 s | (same process) | | [D1] |
| Init | 56,622 | uniform-w2 | old | 1,207.0 s | 100.4 s | (same process) | | [D1] |
| Init | 56,622 | tiered-TagN | new | 435.7 s | 75.4 s | 6, 1:52–4:31 for both modes | 834,832–835,248 kB | [D2] |
| Init | 56,622 | uniform-w2 | new | 151.1 s | 31.2 s | (same processes) | | [D2] |
| Mathlib sample | 20,263 | tiered-TagN | old | 8,121.6 s | 925.0 s | 2, 3:08:16 and 3:23:14 for both modes | 4,723,896 and 4,729,316 kB | [D3] |
| Mathlib sample | 20,263 | uniform-w2 | old | 4,879.5 s | 399.7 s | (same processes) | | [D3] |
| Mathlib sample | 20,263 | tiered-TagN | new | 5,092.5 s | 703.4 s | 4, 1:01:54–1:37:49 for both modes | 4,704,176–4,717,480 kB | [D4] |
| Mathlib sample | 20,263 | uniform-w2 | new | 1,379.8 s | 89.3 s | (same processes) | | [D4] |
| Mathlib, the 120 Lean-only constants | 120 | tiered-TagN | new, `3ddda798` | 5,128.7 s | 257.6 s | 4, 17:20–28:39 | 4,732,112–4,735,896 kB | [D5] |
| Mathlib, half the corpus | 339,749 | tiered-TagN | new, `3ddda798` | 8,563.0 s | 1,091.0 s | 3, 53:12–55:03 | 4,724,964–4,731,392 kB | [D6] |

- The sample is heavy by construction (it includes every constant with more than 2,000 candidates), so
  its per-constant times are not corpus averages.
- **For context; these are not optimizer timings:**
  - W3's Lean uniform optimizer on Init (old search, w = 1, 2 and 3, single-threaded) took 6,875,358 ms
    over 166,158 calls, a median of 179–249 µs per call and a maximum of 108 s [W3 §Wall time].
  - W5's single-threaded `sharing-study` harness, which runs no optimizer, measured Mathlib in 4,101.8 s
    with 4,709,872 kB peak RSS [W5 §Reproduction].

## Phase statistics

The runner reports these statistics only for the K-based construction. The best-of-three runs record
bytes and stored counts per width, not search statistics, and that rule runs phase 1 three times, so the
table below describes one phase-1 run per constant.

The table covers all certified constants (rootless constants contribute zeros), with nearest-rank
percentiles:

- **uniform states:** the uniform search's states. Under the old search these are subsets evaluated by
  the enumeration; under the new search, branch-and-bound states.
- **first-tier states:** phase 2's branch and bound.
- **Uncertain terms and largest component** cannot be compared one to one between the searches. The new
  rules also changed the certain-stored threshold (θ = 1 when no table-count bracket is within reach).

| statistic | corpus, run | p50 | p90 | p99 | p99.9 | max |
|---|---|---:|---:|---:|---:|---:|
| uncertain terms | Init, old [R1] | 4 | 32 | 143 | 406 | 1,509 |
| | Init, new [R6] | 3 | 22 | 113 | 267 | 978 |
| | Mathlib, old [R2] | 6 | 37 | 147 | 418 | 5,756 |
| | Mathlib, new [R3] | 4 | 25 | 112 | 296 | 3,077 |
| largest component | Init, old [R1] | 2 | 5 | 10 | 16 | 20 |
| | Init, new [R6] | 1 | 3 | 7 | 13 | 57 |
| | Mathlib, old [R2] | 1 | 4 | 9 | 15 | 21 |
| | Mathlib, new [R3] | 1 | 3 | 6 | 13 | 57 |
| uniform states | Init, old [R1] | 15 | 168 | 3,233 | 79,914 | 776,614 |
| | Init, new [R6] | 12 | 90 | 486 | 1,094 | 5,503 |
| | Mathlib, old [R2] | 21 | 157 | 1,729 | 47,638 | 1,046,337 |
| | Mathlib, new [R3] | 16 | 102 | 475 | 1,231 | 12,358 |
| first-tier states | Init, new [R6] | 15 | 91 | 618 | 1,871 | 17,727 |
| | Mathlib, new [R3] | 20 | 128 | 789 | 2,673 | 30,126 |
| R1/R2 candidates | Init [R6] | 33 | 227 | 1,168 | 4,843 | 22,458 |
| | Mathlib [R3] | 66 | 424 | 2,004 | 6,370 | 81,833 |

- The old-search maxima cover certified constants only, so they exclude the failing constants, which are
  the ones with the largest components.
- **Phase-1 width under the K-based rule:**
  - TagN layout: Init {1: 23,506, 2: 33,008, 3: 108} [R6]; Mathlib {1: 197,682, 2: 480,001, 3: 1,816} [R3].
  - Tag4 layout: Init {1: 23,506, 2: 31,764, 3: 1,352} [R5]; Mathlib {1: 197,682, 2: 458,516, 3: 23,301}
    [R7].
- **Width chosen by the best of three** (rooted constants), see the experiment section: TagN w = 1 / 2 / 3
  wins 44,046 / 11,156 / 184 on Init and 505,671 / 156,170 / 1,413 on Mathlib [X1].
- **Uniform-model classes**, from the harness's own classification of the MSS candidate set:
  - certain-stored 80.5 / 64.1 / 54.4% on Init and 88.4 / 71.0 / 57.9% on Mathlib, at w = 1 / 2 / 3;
  - largest uncertain component ≤ 8 for 99.7–99.9% of constants, max 45
    [W3 §Uniform-reference-width classification] [W5 §Uniform-reference-width classification and
    components].

## Slowest constants

All tables use the TagN layout. Column meanings:

- `N`: distinct subterms;
- `cand`: R1/R2 candidates;
- `K`: the tiered candidate count;
- `w`: the phase-1 width.

**Mathlib, best of three** [X1] [R3]. Times are the sum of the three widths' times, measured in the
8-thread run with the machine shared, so they are inflated relative to an idle single thread.

| ms (sum of 3) | constant | N | cand | K | K-based w | best w | stored at w = 1 / 2 / 3 | ms at w = 1 / 2 / 3 |
|---:|---|---:|---:|---:|---:|---:|---|---|
| 163,721 | `CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite` | 95,110 | 81,833 | 21,461 | 3 | 2 | 18,653 / 18,877 / 18,440 | 74,674 / 44,791 / 44,256 |
| 84,389 | `WeierstrassCurve.variableChange_Δ` | 63,501 | 18,995 | 9,233 | 3 | 3 | 8,259 / 8,564 / 8,525 | 21,488 / 27,008 / 35,893 |
| 77,150 | `CategoryTheory.Bicategory.mateEquiv_vcomp` | 50,497 | 32,338 | 8,940 | 3 | 2 | 6,947 / 7,533 / 7,367 | 32,773 / 23,864 / 20,512 |
| 68,373 | `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux` | 64,047 | 41,872 | 8,745 | 3 | 1 | 7,165 / 7,335 / 7,006 | 13,860 / 22,620 / 31,893 |
| 52,355 | `AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective` | 66,025 | 52,066 | 10,555 | 3 | 3 | 8,980 / 9,284 / 8,981 | 9,839 / 22,778 / 19,738 |
| 49,194 | `Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual` | 78,913 | 59,202 | 13,054 | 3 | 1 | 10,696 / 11,065 / 10,482 | 15,014 / 17,136 / 17,043 |
| 37,653 | `_private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.0.WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three` | 50,027 | 26,233 | 10,413 | 3 | 3 | 8,545 / 8,943 / 8,673 | 10,723 / 14,022 / 12,908 |
| 37,075 | `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1` | 70,414 | 61,641 | 11,700 | 3 | 3 | 9,464 / 10,262 / 10,024 | 11,838 / 12,668 / 12,569 |
| 37,029 | `WeierstrassCurve.isHomogeneous_addSubMapCoeff` | 60,092 | 31,902 | 10,150 | 3 | 2 | 7,846 / 8,152 / 8,031 | 6,283 / 13,954 / 16,792 |
| 33,626 | `WeierstrassCurve.Affine.addPolynomial_slope` | 35,899 | 20,245 | 5,956 | 3 | 3 | 5,150 / 5,361 / 5,253 | 8,689 / 11,987 / 12,951 |


**Init, best of three, single thread** [X3] [R6]. This run overlapped the 8-thread Mathlib Tag4 experiment, so the per-width times are higher than [R6]'s for the same constant at its K-based width. For example, `…Vector.extract_append._proof_1` at w = 3 took 3,031 ms here and 1,133 ms in [R6].

| ms (sum of 3) | constant | N | cand | K | K-based w | best w | stored at w = 1 / 2 / 3 | ms at w = 1 / 2 / 3 |
|---:|---|---:|---:|---:|---:|---:|---|---|
| 8,801 | `_private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1` | 26,943 | 19,283 | 5,136 | 3 | 2 | 4,280 / 4,474 / 4,427 | 2,847 / 2,923 / 3,031 |
| 8,644 | `_private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1` | 26,754 | 19,091 | 5,146 | 3 | 2 | 4,247 / 4,454 / 4,403 | 2,901 / 2,828 / 2,915 |
| 8,028 | `_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | 27,628 | 22,458 | 4,874 | 3 | 2 | 4,076 / 4,067 / 3,785 | 2,654 / 2,806 / 2,569 |
| 6,252 | `_private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1` | 24,507 | 17,140 | 4,678 | 3 | 3 | 3,939 / 4,107 / 4,059 | 1,980 / 2,267 / 2,005 |
| 5,975 | `Lean.Grind.Config.mk.injEq` | 3,512 | 551 | 360 | 2 | 1 | 281 / 192 / 187 | 4,450 / 873 / 652 |
| 5,167 | `_private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1` | 24,658 | 17,290 | 4,703 | 3 | 3 | 3,981 / 4,143 / 4,097 | 1,616 / 1,719 / 1,831 |
| 5,165 | `_private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1` | 26,494 | 19,017 | 4,919 | 3 | 3 | 4,127 / 4,303 / 4,279 | 1,375 / 1,644 / 2,146 |
| 4,215 | `_private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1` | 19,523 | 11,454 | 3,640 | 3 | 3 | 3,108 / 3,135 / 3,121 | 1,420 / 1,363 / 1,432 |
| 2,631 | `_private.Init.Data.Int.DivMod.Lemmas.0.Int.add_one_tdiv._proof_1_1` | 18,802 | 13,281 | 3,236 | 3 | 3 | 2,782 / 2,793 / 2,740 | 740 / 782 / 1,109 |
| 2,469 | `_private.Init.Data.Vector.Extract.0.Vector.extract_add_left._proof_1` | 14,521 | 8,259 | 2,854 | 3 | 3 | 2,412 / 2,494 / 2,464 | 830 / 823 / 816 |


**Init, K-based (superseded), single thread** [R6]:

| ms | constant | N | cand | K | w | uncertain | components (largest) | uniform / first-tier states |
|---:|---|---:|---:|---:|---:|---:|---|---|
| 2,261 | `_private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1` | 26,494 | 19,017 | 4,919 | 3 | 587 | 555 (3) | 2,351 / 8,577 |
| 1,431 | `_private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1` | 26,754 | 19,091 | 5,146 | 3 | 687 | 651 (3) | 2,721 / 13,228 |
| 1,133 | `_private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1` | 26,943 | 19,283 | 5,136 | 3 | 660 | 621 (3) | 2,609 / 17,727 |
| 1,039 | `_private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1` | 24,658 | 17,290 | 4,703 | 3 | 557 | 517 (4) | 2,193 / 4,104 |
| 968 | `…ForwardSliceSearcher.Invariants.isValidSearchFrom_toList` | 27,628 | 22,458 | 4,874 | 3 | 978 | 826 (6) | 3,826 / 3,793 |
| 884 | `_private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1` | 24,507 | 17,140 | 4,678 | 3 | 571 | 530 (4) | 2,247 / 4,066 |
| 636 | `Lean.Grind.Config.mk.injEq` | 3,512 | 551 | 360 | 2 | 185 | 14 (44) | 4,177 / 199 |
| 593 | `…Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition'` | 16,156 | 11,692 | 2,712 | 3 | 349 | 299 (4) | 1,375 / 9,252 |
| 503 | `_private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1` | 19,523 | 11,454 | 3,640 | 3 | 454 | 435 (4) | 1,816 / 3,143 |
| 436 | `_private.Init.Data.Vector.Extract.0.Vector.extract_add_left._proof_1` | 14,521 | 8,259 | 2,854 | 3 | 332 | 310 (3) | 1,310 / 4,936 |

## Lean/Rust parity

How the differential counts:

- For each mode it compares the complete serialized constant from Lean and from Rust.
- A resource exhaustion on both sides counts as agreement of the error category.
- A one-sided exhaustion is reported. `diagnose` then reruns Lean with the limit that fired doubled, at
  most 12 times.

**Best of three** (the canonical rule, Lean W1 `3eb09b9c` and Rust `a80c16cf`):

| corpus | build | mode | same bytes | same error | Lean-only exhaustion | Rust-only | disagreements | source |
|---|---|---|---:|---:|---:|---:|---:|---|
| fixtures (§2), 7 modes | `a80c16cf` | | 89 | 0 | 0 | 0 | 0 | [D7] |
| 350 generated inputs × modes | `a80c16cf` | | 2,398 | 0 | 0 | 0 | 0 | [D7] |
| Init, all | `a80c16cf` | tiered-TagN | **56,622** | 0 | 0 | 0 | **0** | [D7] |
| | | tiered-Tag4 | **56,622** | 0 | 0 | 0 | **0** | [D7] |
| Mathlib sample | `a80c16cf` | tiered-TagN, tiered-Tag4 | aborted, no tallies | | | | | [D8] |

**K-based (superseded):**

| corpus | build | mode | same bytes | same error | Lean-only exhaustion | Rust-only | disagreements | source |
|---|---|---|---:|---:|---:|---:|---:|---|
| fixtures (§2), 7 modes | every build | | 89 | 0 | 0 | 0 | 0 | [D1]–[D6] |
| 350 generated inputs × modes | every build | | 2,398 | 0 | 0 | 0 | 0 | [D1]–[D6] |
| Init, all | old (`871eef12`) | tiered-TagN | 56,587 | 25 | 10 | 0 | **0** | [D1] |
| | | tiered-Tag4 | 56,583 | 29 | 10 | 0 | **0** | [D1] |
| | | uniform-w2 | 56,594 | 28 | 0 | 0 | **0** | [D1] |
| Init, all | new (`e4c0dead`) | tiered-TagN | 56,612 | 0 | 10 | 0 | **0** | [D2] |
| | | uniform-w2 | 56,622 | 0 | 0 | 0 | **0** | [D2] |
| Mathlib sample | old (`86df8874`) | tiered-TagN | 20,056 | 101 | 106 | 0 | **0** | [D3] |
| | | uniform-w2 | 20,162 | 99 | 2 | 0 | **0** | [D3] |
| Mathlib sample | new (`e4c0dead`) | tiered-TagN | 20,143 | 0 | 120 | 0 | **0** | [D4] |
| | | uniform-w2 | 20,263 | 0 | 0 | 0 | **0** | [D4] |
| the 120 + 10 Lean-only constants | `3ddda798` | tiered-TagN (and Tag4 for the 10 Init) | 120 + 10 (+ 10) | 0 | 0 | 0 | **0** | [D5] |
| **Mathlib, half the corpus** (3 of 6 address shards) | `3ddda798` | tiered-TagN | **339,749** | 0 | 0 | 0 | **0** | [D6] |

- **One-sided exhaustions.** After `diagnose` raised the limit that fired, every Lean-only exhaustion in
  every run gave bytes equal to Rust's [D0] [D3] [D4]. With `maxMaterializeWork` (`3ddda798` onwards)
  there were none in [D5]–[D7].
- **The aborted run [D8].** The best-of-three Mathlib-sample differential was stopped at the coordinator's
  request after 2 h 5 min, at 07:23 on 2026-10-01. It used the phase-2 order that §12.14 replaces, so the
  Kahn-order rerun would supersede it, and the CPU was needed by other worktrees' builds. Each
  process buffers its output until the end, so no tally was written. Each log ends with GNU `time`'s "Command terminated by signal 15", an
  elapsed time of 2:04:51–2:04:57 and the wrapper's `exit=143`.
- **The half-corpus run [D6].** The constants were split round-robin into 6 address shards, one process
  each. Three processes ended without writing anything beyond the build warnings and without the
  wrapper's exit line; the cause is unexplained. The other three covered 113,249 + 113,250 + 113,250
  constants (every constant whose position in the address list is 0, 3 or 4 mod 6).
- **Exit status of [D3].** Its two processes exited with status 1 after all groups had passed. The test
  driver then failed to spawn `lean`, which was not on their `PATH` [D3].
- **Rust-only tests.** `cargo test -p ixon` passes 392 tests at `a80c16cf`. Among them are the comparison
  of the branch and bound against the enumeration on 600 generated inputs, and the best-of-three selection
  rule against the forced-width candidates (`tiered_at_width_hook`).

## The phase-1 width experiment

This experiment led to plan §12.11. It was run with an experiment hook, before either implementation's
canonical entry point adopted the rule. The best-of-three figures in [Bytes](#bytes) come from it.

**Hypothesis.** The K-based rule picks the nominal width from `K`, but the optimum stores far fewer terms
than `K`, so the real references are narrower than modelled. With `K = 100`, for example, TagN gives
`w = 2`. If only 6 terms are stored, every reference costs 1 byte, and the `w = 2` model may have
excluded terms that pay at width 1.

**Method.**

- **The hook.** `normalize_constant_sharing_tiered_at_width` (`faf1a7c7`) runs phases 1–3 with the
  phase-1 width forced to `w`. Phases 2 and 3 are unchanged. At the K-based width it reproduces the
  canonical construction (test `tiered_at_width_hook`).
- **The runner.** `--width-experiment` runs the hook at `w = 1, 2, 3` for every constant and records the
  layout bytes of each width.
- **The choices compared:**
  - K-based (superseded);
  - best of three;
  - re-solve: take `w = uniform_width(stored count of the K-based run)` and solve once at that width;
  - one fixed `w` for every constant.
- **Pricing.** MSS is priced at the same widths, scheme F for TagN and scheme A for Tag4, over rooted
  constants.
- **Certification.** Every width certified every constant on both corpora under both layouts: 0 failures
  at `w = 1`, 2 and 3 [X1] [X2].

### TagN layout [X1]

| | Init bytes | vs MSS (F) | Mathlib bytes | vs MSS (F) |
|---|---:|---:|---:|---:|
| MSS (F) | 67,556,587 | | 1,130,381,317 | |
| K-based (superseded) | 66,990,376 | −566,211 (−0.84%) | 1,135,611,532 | +5,230,215 (+0.46%) |
| **best of three** | **66,602,235** | **−954,352 (−1.41%)** | **1,121,167,486** | **−9,213,831 (−0.82%)** |
| re-solve | 66,913,395 | −643,192 (−0.95%) | 1,134,824,013 | +4,442,696 (+0.39%) |
| `w = 1` for every constant | 66,771,574 | −785,013 (−1.16%) | 1,122,848,598 | −7,532,719 (−0.67%) |
| `w = 2` for every constant | 67,050,223 | −506,364 | 1,135,414,511 | +5,033,194 |
| `w = 3` for every constant | 67,791,486 | +234,899 | 1,151,346,211 | +20,964,894 |

Against the K-based rule, the best of three saves 388,141 B (−0.58%) on Init and 14,444,046 B (−1.27%) on
Mathlib.

| per constant | Init | Mathlib |
|---|---|---|
| best-of-three width (rooted): w = 1 / 2 / 3 | 44,046 / 11,156 / 184 | 505,671 / 156,170 / 1,413 |
| best of three vs K-based (all constants): better / equal | 20,651 / 35,971 | 297,121 / 382,378 |
| re-solve vs K-based (all constants): better / equal / worse | 7,339 / 48,569 / 714 | 64,033 / 600,933 / 14,533 |
| K-based vs MSS: smaller / equal / larger | 23,132 / 22,616 / 9,638 | 242,375 / 199,829 / 221,050 |
| **best of three vs MSS: smaller / equal / larger** | **32,236 / 23,145 / 5** | **405,832 / 256,519 / 903** |
| re-solve vs MSS: smaller / equal / larger | 27,370 / 23,365 / 4,651 | 263,473 / 225,637 / 174,144 |

**Remaining losses of the best of three against MSS (TagN)** [X1]:

- **Init**, all 5 losses, all with best `w = 1`:
  - +6: `…Std.Iterators.Types.FilterMap.instFinitenessRelation._proof_2` (K 241);
  - +4: `instLawfulMonadAttachStateTOfLawfulMonad` (K 178);
  - +3: `…ULiftIterator.instFinitenessRelation._proof_2` (K 246);
  - +1: `Std.IterM.length_uLift` (K 856);
  - +1: `Std.Iter.all_filterMap` (K 324).
- **Mathlib**, the ten largest of 903:
  - +1,485: the outlier below;
  - the other nine, all with best `w = 1`: `equalizerCondition_yonedaPresheaf` +37 (K 894),
    `SheafOfModules.Presentation.mk.injEq` +32 (K 553),
    `SheafOfModules.relationsOfIsCokernelFree._proof_2` +29 (K 822),
    `Algebra.Extension.CotangentSpace.map_comp` +26 (K 1,457), `SheafOfModules.Presentation.mk.inj` +25
    (K 487), `SheafOfModules.Presentation.noConfusionType` +23 (K 351),
    `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty` +21 (K 949),
    `CategoryTheory.MonoidalCategory.externalProductFlip._proof_8` +20 (K 340) and
    `Std.DTreeMap.Internal.Impl.link2.fun_cases` +18 (K 241).
  - 902 of the 903 losses are at most +37 bytes (p99.9 of best − MSS is +1).

### The outlier

`Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq`, address
`048653e65a77d222…`, a `defn`.

| quantity | value | source |
|---|---:|---|
| distinct subterms `N` | 19,417 | [W5] CSV, [R3] |
| R1/R2 candidates | 8,801 | [W5] CSV, [R3] |
| `K` (in-degree ≥ 2, unshared length ≥ 2) = MSS table size | 2,230 | [X1], [W5] CSV `mss_table` |
| heuristic: stored bytes / table entries | 96,389 / 8,591 | [W5] CSV |
| unshared bytes | 13,329,184 | [W5] CSV |
| MSS: Tag4 bytes / TagN-priced bytes | 72,195 / 63,779 | [W5] CSV, join |
| MSS Share references at indices < 8 / 8–1,031 / ≥ 1,032 | 1,101 / 13,699 / 4,149 (Σ deg 18,949) | [W5] CSV |
| tiered TagN at w = 1: stored / bytes | 1,924 / 65,444 | [X1] CSV |
| tiered TagN at w = 2: stored / bytes (best) | 1,895 / **65,264** | [X1] CSV |
| tiered TagN at w = 3 (= K-based): stored / bytes | 1,755 / 65,325 | [X1] CSV, [R3] |
| best of three − MSS (TagN) | **+1,485** | [X1] |
| K-based run: uncertain terms / components (largest) / uniform states / first-tier states | 421 / 347 (5) / 1,604 / 1,760 | [R3] |
| K-based run: Tag4-serialized bytes | 70,451 | [R3] |
| old search (K-based) | `resource:States` | [R2] |
| tiered TagN times at w = 1 / 2 / 3 (8 threads, shared) | 2,018 / 1,979 / 1,703 ms | [X1] CSV |
| Tag4 layout: bytes at w = 1 / 2 / 3, MSS (A) | 72,606 / **70,422** / 70,451; MSS 72,195 (best − MSS = −1,773) | [X2] CSV |

All three widths store 1,755–1,924 terms, fewer than MSS's 2,230, and all three end at least 1,485 bytes
above MSS. The best-of-four experiment below stores MSS's exact set as a fourth candidate.

### Tag4 layout [X2]

| | Init bytes | vs MSS (A) | Mathlib bytes | vs MSS (A) |
|---|---:|---:|---:|---:|
| MSS (A) | 68,547,873 | | 1,148,195,956 | |
| K-based (superseded) | 67,701,399 | −846,474 (−1.23%) | 1,150,611,314 | +2,415,358 (+0.21%) |
| **best of three** | **67,255,886** | **−1,291,987 (−1.88%)** | **1,135,005,370** | **−13,190,586 (−1.15%)** |
| re-solve | 67,592,721 | −955,152 (−1.39%) | 1,148,702,659 | +506,703 (+0.04%) |
| `w = 1` for every constant | 67,528,222 | −1,019,651 (−1.49%) | 1,138,024,409 | −10,171,547 (−0.89%) |
| `w = 2` for every constant | 67,694,849 | −853,024 | 1,148,160,385 | −35,571 |
| `w = 3` for every constant | 68,358,800 | −189,073 | 1,161,814,219 | +13,618,263 |

| per constant | Init | Mathlib |
|---|---|---|
| best-of-three width (rooted): w = 1 / 2 / 3 | 43,904 / 10,981 / 501 | 501,851 / 157,708 / 3,695 |
| best of three vs K-based (all constants): better / equal | 20,985 / 35,637 | 299,934 / 379,565 |
| re-solve vs K-based (all constants): better / equal / worse | 7,902 / 47,974 / 746 | 73,526 / 591,110 / 14,863 |
| **best of three vs MSS: smaller / equal / larger** | **32,239 / 23,144 / 3** | **405,933 / 256,460 / 861** |

**Remaining losses of the best of three against MSS (Tag4)** [X2]:

- **Init:** 3 losses, the same constants as the top three under TagN: +6, +4 and +3.
- **Mathlib:** 861 losses. The largest is +266, `Algebra.Extension.Cotangent.map_toInfinitesimal_bijective`
  (K 730, best `w = 1`). The next nine are +98 to +156: `Module.isBaseChange_map_of_finite_free` +156,
  `VectorField.DifferentiableWithinAt.pullbackWithin` +135, `LinearEquiv.image_closure_of_convex'` +129,
  `IsBaseChange.end` +125, `…Algebra.Generators.H1Cotangent.auxMemKer` +123, `TensorProduct.adjoint_map`
  +113, `RingHom.Flat.tensorProductMap` +109 (the only one with best `w = 3`),
  `LinearMap.tensorEqLocusEquiv._proof_3` +100 and
  `instOrderIsoClassContinuousLinearMapIdOfNonUnitalAlgEquivClassOfStarHomClassOfContinuousMapClass` +98.
  For all ten the K-based width was 3.
- **The TagN outlier** above is 1,773 bytes *smaller* than MSS under Tag4.

### Best of four (rejected, plan §12.14) [X4]

**Method.** A fourth phase-1 candidate, "all", stores every candidate: compact in-degree ≥ 2 and
unshared length ≥ 2, which is exactly MSS's set. Its bodies are materialized at uniform width 1 and
carried through phases 2 and 3 like the others (hook `Phase1Choice::AllCandidates`, `94882265`). The best
of four takes the fewest layout bytes, with ties going to w = 1, 2, 3 and then "all". No candidate failed
on any constant of either corpus under either layout.

| | Init, TagN | Mathlib, TagN | Init, Tag4 | Mathlib, Tag4 |
|---|---:|---:|---:|---:|
| best of four, rooted bytes | 66,602,218 | 1,121,164,590 | 67,255,871 | 1,135,003,221 |
| change vs best of three (all constants) | −17 | −2,896 | −15 | −2,149 |
| constants where "all" wins | 7 | 1,131 | 5 | 992 |
| best of four vs MSS: smaller / equal / larger | 32,237 / 23,149 / **0** | 405,889 / 257,363 / **2** | 32,240 / 23,146 / **0** | 405,989 / 257,170 / **95** |
| best of four − MSS, max | 0 | +1,485 | 0 | +266 |

- **The remaining losses.**
  - Mathlib TagN: the outlier (+1,485) and `Algebra.Extension.CotangentSpace.map_comp` (+26).
  - Mathlib Tag4: the ten largest are the same ten constants, with the same losses (+266 to +98), as
    under the best of three; for each of them the best candidate is still a uniform width.
- **Decision.** Not adopted [P §12.14]: 2,896 bytes over all of Mathlib (TagN) does not justify a fourth
  pass.
- **Cost.** Four candidates per constant took 1,021.8 s (TagN) and 1,141.4 s (Tag4) of processing over
  Mathlib on 12 threads, with peak RSS 4.87 and 5.02 GB [X4].

**The outlier, diagnosed (plan §12.14, resolved in §12.15).**

- Under "all", the outlier stores MSS's exact set (2,230 entries), yet ends at 67,367 bytes under TagN.
  That is worse than its own `w = 2` candidate (65,264) and 3,588 bytes worse than MSS (63,779) [X4] CSV.
  Under Tag4 "all" gives 72,065.
- §12.14 first attributed the gap to phase 2's pinned order beyond the first tier. Phase 2 now uses the
  Kahn priority order by reference count there (W1 `7a7113cf`, Rust `0ef72793`), and this does not
  close the gap [X6]:
  - TagN bytes at w = 1 / 2 / 3: 65,444 / 65,264 / **65,247**; "all" 67,367 (unchanged).
  - The best of three is now 65,247, +1,468 over MSS (was +1,485).
  - Tag4 at w = 1 / 2 / 3: 72,405 / **70,422** / 70,623; "all" 72,065.
- The cause is the **tie-break inside the Kahn order** [X5] [P §12.15]. Re-implemented in Rust, MSS
  (every candidate stored, Kahn order by in-degree, every occurrence a Share) gives on the outlier:

  | encoding | TagN bytes | Tag4 bytes | Shares at TagN widths 1 / 2 / 3 bytes |
  |---|---:|---:|---|
  | MSS, ties by blake3 hash (W3's `mssBuild` rule) | **63,779** | **72,195** | 1,101 / 13,699 / 4,149 |
  | MSS, ties by structural ID | 67,367 | 72,071 | 1,101 / 10,111 / 7,737 |
  | "all" (tiered phases 2 and 3 on MSS's set) | 67,367 | | 1,101 / 7,891 / 7,737 |

  - The blake3-tie MSS reproduces W5's MSS bytes and scheme-F price exactly.
  - The ID-tie MSS and "all" have the same table order (no entry at a different index) and the same
    total entry and root lengths (28,683 and 32,421).
  - "all" writes 2,220 occurrences of size-2 stored terms inline. A 2-byte Share and a 2-byte inline
    write cost the same, so the total is unchanged.
  - The two MSS orders differ for 2,175 of the 2,230 entries. With the table straddling the TagN 1,032
    boundary, the tie order decides which entries become available early and so reach the 2-byte rung.
  - Under Tag4 the ID order is the better of the two, by 124 bytes.

### Store-all against MSS under both tie rules (plan §12.15) [X5]

All 679,499 Mathlib constants, TagN prices. "all" is the all-candidates construction with the Kahn order.

| comparison | "all" larger | "all" smaller | equal | total difference |
|---|---:|---:|---:|---:|
| "all" − MSS with structural-ID ties | **0** | 157,438 | 522,061 | −1,227,943 B |
| "all" − MSS with blake3 ties | 206 (+22,185 B, max +3,588) | 166,865 | 512,428 | −1,602,326 B |

- **Totals:**
  - MSS with ID ties: 1,130,616,480 B.
  - MSS with blake3 ties: 1,130,990,863 B. This equals [W5]'s scheme-F rooted total plus the 609,546
    rootless bytes. Its Share bytes, 280,471,878, equal [W5]'s scheme-F reference bytes.
  - "all": 1,129,388,537 B.
- **Shares:** both MSS variants write 159,110,515 Shares; "all" writes 145,331,762. "all" writes
  13,778,893 occurrences of stored terms inline, in 239,559 constants.
- **Every "all" loss is a tie-break effect.** For each of the 206 constants where "all" is larger than
  blake3-tie MSS, ID-tie MSS is at least as large as "all".
- **The tie rule itself:**
  - ID ties are better than blake3 ties overall, by 374,383 B.
  - ID ties win on 36,846 constants, blake3 ties on 23,605, and 619,048 are equal.
  - The largest ID advantage is 6,980 B (`CartanMatrix.E₈_det`); the largest blake3 advantage is the
    outlier's 3,588 B.
  - Taking the better rule per constant would gain 119,735 B (0.011%).
- **Twenty constants examined entry by entry** (`--mss-diff`) where "all" and MSS differ by more than 1%:
  - The 7 where "all" exceeds blake3-tie MSS by more than 1%: in each, ID-tie MSS is at least as large as
    "all", and blake3 ties beat ID ties under TagN.
  - 13 random constants of the 8,440 where "all" is more than 1% below ID-tie MSS: "all" gains through
    the exact first tier, which puts more references in the 1-byte slots (for example 198 → 239 in
    `LinearMap.toMatrix₂`), and through phase 3 writing a stored term inline where its Share would cost
    at least as much.
- **Decision.** No rule change; structural-ID ties stay pinned [P §12.15]. The order beyond the first
  tier is a greedy rule. An exact maximum-weight closed set for the 1,032-entry second rung is a possible
  refinement, not adopted.
- **Against the best of three.** The best of three (`faf1a7c7`, before the Kahn order) is larger than
  ID-tie MSS on 902 constants, by +2,504 B in total and at most +37 bytes [X1] [X5].

### What the experiment shows

- **The hypothesis holds on these corpora.** The excess over MSS came from the nominal width. With the
  best of the three widths, 5 Init and 903 Mathlib constants remain larger than MSS (TagN), against 9,638
  and 221,050 under the K-based rule.
- **`w = 1` wins most often**, for 76% of rooted Mathlib constants.
- **Re-solving once from the stored count is not enough.** On Mathlib it stays above MSS (+0.39%) and is
  worse than the K-based rule on 14,533 constants.
- **Cost.** Three constructions per constant instead of one; see
  [Wall time and memory](#wall-time-and-memory).

## What is not covered

- **The exact width-state DP oracle beyond small inputs.** The §6 search, the full-key minimum over all
  tables in the real Tag4 widths, is only an oracle.
  - It is checked against exhaustive enumeration on small generated inputs and on the §2 fixtures (suite
    `exact-sharing`; Rust `optimizer_matches_exhaustive_oracle` and the tests around it).
  - It was not run over either corpus; Mathlib's median candidate count (69) is far beyond its reach
    [P §12.1] [W5 §Headline].
  - So no corpus number here is a distance to the true minimum.
  - The only proved lower bound measured on a corpus is W3's w = 1 uniform-model optimum on Init, under
    the old search. The best of the encodings W3 measured, per constant, is 11.72% above it
    [W3 §Lower-bound gap]. That bound was not recomputed for the best of three.
- **Unshared sizes of 619 Mathlib constants (and 7 Init) were not serialized**, only computed
  compositionally, because their unshared roots exceed 16 MiB [W5 §Limits and coverage]
  [W3 §Verification]. The runner's unshared sizes are compositional too, and they agree with the
  harness's for every row [J1] [J2].
- **The heuristic's own `occ` counts** were not brute-force checked for 31,049 Mathlib and 1,232 Init
  constants [W5 §Verification] [W3 §Verification].
- **The TagN Share encoding is not serialized.** TagN-layout bytes are prices (`layout_bytes`), not
  measured serializations. W4's selectable `ShareCodec` can write TagN Shares, but the current wire
  codec is still Tag4 (`ShareCodec::CURRENT`), and these runs predate it [P §12.8]. TagN for all integers
  [P §12.12] is not priced here.
- **Best of three, beyond the byte totals.**
  - The Rust byte figures come from the experiment hook, which runs the same three candidates that the
    canonical path (`a80c16cf`) compares. No full-corpus run of the canonical runner mode was repeated.
  - Lean/Rust parity under the best of three covers Init only [D7]; the Mathlib-sample run [D8] was
    aborted.
  - The phase statistics above are for one phase-1 run (the K-based width). Per-width search statistics
    (states, components) were not recorded.
- **The Kahn order beyond the first tier** (W1 `7a7113cf`, Rust `0ef72793`) is measured here only on the
  outlier [X6] and in the store-all comparison [X5]; the best-of-three byte totals above predate it.
- **Lean on all of Mathlib.** The K-based tiered-TagN differential over all 679,499 constants ran in 6
  address shards [D6]. Three shards (339,749 constants) completed with 0 disagreements. The other three
  processes ended without output, for reasons not explained. No best-of-three Lean run over all of
  Mathlib was made.
- **Lean wall time and memory.** Lean's single-threaded wall time per corpus is available only as the sum
  of per-call times inside the differential, whose processes also run Rust and the diagnosis reruns.
  Lean-only peak memory was not separated from the differential process.
- **Other corpora.** The 9 other `Benchmarks/Compile` targets, project fixtures, and synthetic families
  beyond the test generators were not measured [W5 §Limits and coverage].
- **Proofs.** Nothing here measures or checks optimality claims. Phase 1's uniform optimum is proved
  minimal and `setPrec`-least in Lean (`optimizeUniform_minimum`, `optimizeUniform_least`); phases 2 and
  3 and the best-of-three selection are tested, not proved [P §12.13].

## Reproduction

Run from the worktree root, with `S` as above:

```text
# Rust runner
nix develop --command bash -c 'cargo build --release -p ixon --example sharing_corpus'
R=./target/release/examples/sharing_corpus
time -v $R $S/init.ixe    --layout tagN --threads 8 --width-experiment --csv $S/w2/p4/wx_init_tagN.csv     # [X1]
time -v $R $S/mathlib.ixe --layout tagN --threads 8 --width-experiment --csv $S/w2/p4/wx_ml_tagN.csv       # [X1]
time -v $R $S/init.ixe    --layout tag4 --threads 8 --width-experiment --csv $S/w2/p4/wx_init_tag4.csv     # [X2]
time -v $R $S/mathlib.ixe --layout tag4 --threads 8 --width-experiment --csv $S/w2/p4/wx_ml_tag4.csv       # [X2]
time -v $R $S/init.ixe    --layout tagN --threads 1 --width-experiment --csv $S/w2/p4/wx_init_tagN_t1.csv  # [X3]
# best of four: the same mode at 94882265, which adds the "all" candidate and the best4 columns   # [X4]
time -v $R $S/mathlib.ixe --layout tagN --threads 12 --width-experiment --csv $S/w2/p4/wx4_ml_tagN.csv     # [X4]
time -v $R $S/init.ixe    --layout tagN --threads 1  --csv $S/w2/p4/init_tagN_t1.csv                       # [R6]
time -v $R $S/init.ixe    --layout tagN --threads 20 --csv $S/w2/p4/init_tagN_t20.csv                      # [R4]
time -v $R $S/init.ixe    --layout tag4 --threads 20 --csv $S/w2/p4/init_tag4_t20.csv                      # [R5]
time -v $R $S/mathlib.ixe --layout tagN --threads 20 --csv $S/w2/mathlib_tiered_bb.csv                     # [R3]
time -v $R $S/mathlib.ixe --layout tag4 --threads 20 --csv $S/w2/p4/ml_tag4_t20.csv \
    --select-out $S/w2/p4/ml_all.txt --select-stride 1                                                    # [R7]

# Joins (scripts in $S/w2/p4/); for Init use $S/sharing-minimum-measurements.csv ([W3]'s tenth-run CSV)
gawk -v layout=tagN -f bestjoin.awk $S/w5/mathlib-sharing.csv wx_ml_tagN.csv                    # [X1]
gawk -v layout=tagN -f wxjoin.awk   $S/w5/mathlib-sharing.csv wx_ml_tagN.csv                    # [X1]
gawk -f join.awk $S/w5/mathlib-sharing.csv $S/w2/mathlib_tiered_bb.csv ml_tag4_t20.csv          # [J2]
gawk -f byw.awk  $S/w5/mathlib-sharing.csv $S/w2/mathlib_tiered_bb.csv ml_tag4_t20.csv          # [J2]
gawk -f slowest.awk $S/w2/mathlib_tiered_bb.csv wx_ml_tagN.csv                                  # [X1]
gawk -v layout=tagN -v bestcol=best4 -f wxjoin.awk $S/w5/mathlib-sharing.csv wx4_ml_tagN.csv    # [X4]

# Lean/Rust differential (one process per address shard)
nix develop --command bash -c 'lake build IxTests'
IX_SHARING_CORPUS=$S/mathlib.ixe IX_SHARING_CORPUS_MODES=tiered-tagN \
IX_SHARING_CORPUS_SELECT=<shard of addresses> time -v ./.lake/build/bin/IxTests exact-sharing-ffi    # [D2]-[D8]
```

## Appendix A: runner reports and joins

Each block is the runner's report file, unedited, followed by the GNU `time` lines of its `.err` file.

<details><summary>[R6] Init, TagN layout, 1 thread, new search, K-based (<code>p4/init_tagN_t1.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants; 56622 processed); layout TagN
- wall: index 206 ms, processing 83.1 s with 1 threads; peak RSS 307508 KiB
- certified: 56622 / 56622; failed: 0
- failures by status: {}
- certified constants: stored (heuristic) 80208288 B; output under Tag4 67668319 B (-15.63%); under TagN 67036818 B (-16.42%)
- unshared (where it fits u64, 56622 constants): 1070001199 B; stored 80208288 B; Tag4 output 67668319 B
- Tag4 output - stored per constant: 49956 smaller, 6228 equal, 438 larger; min -67656 p1 -3220 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- TagN price - stored per constant: min -72624 p1 -3425 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- phase-1 width w: {1: 23506, 2: 33008, 3: 108}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 3 p90 22 p99 113 p99.9 267 max 978
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 3 p99 7 p99.9 13 max 57
- uniform search states per constant: min 0 p1 0 p10 0 p50 12 p90 90 p99 486 p99.9 1094 max 5503
- first-tier search states per constant: min 1 p1 1 p10 3 p50 15 p90 91 p99 618 p99.9 1871 max 17727
- R1/R2 candidates per constant (all): min 0 p1 0 p10 3 p50 33 p90 227 p99 1168 p99.9 4843 max 22458
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 0 p90 2 p99 13 p99.9 90 max 2261
- slowest 10:
  - 2261 ms _private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1 (89ed0e9889141575): defn ok, N 26494, cand 19017, k 4919, w 3, uncertain 587, components 555 (largest 3), states uniform 2351 first-tier 8577
  - 1431 ms _private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1 (e852d49c2b3a2ea7): defn ok, N 26754, cand 19091, k 5146, w 3, uncertain 687, components 651 (largest 3), states uniform 2721 first-tier 13228
  - 1133 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1 (d126ef57b21ab268): defn ok, N 26943, cand 19283, k 5136, w 3, uncertain 660, components 621 (largest 3), states uniform 2609 first-tier 17727
  - 1039 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1 (eed90987192d5160): defn ok, N 24658, cand 17290, k 4703, w 3, uncertain 557, components 517 (largest 4), states uniform 2193 first-tier 4104
  - 968 ms _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806a): defn ok, N 27628, cand 22458, k 4874, w 3, uncertain 978, components 826 (largest 6), states uniform 3826 first-tier 3793
  - 884 ms _private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514): defn ok, N 24507, cand 17140, k 4678, w 3, uncertain 571, components 530 (largest 4), states uniform 2247 first-tier 4066
  - 636 ms Lean.Grind.Config.mk.injEq (79a818e3bc347ced): defn ok, N 3512, cand 551, k 360, w 2, uncertain 185, components 14 (largest 44), states uniform 4177 first-tier 199
  - 593 ms _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.0.Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition' (f22512c397919b72): defn ok, N 16156, cand 11692, k 2712, w 3, uncertain 349, components 299 (largest 4), states uniform 1375 first-tier 9252
  - 503 ms _private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1 (b6be5c1a4db8c149): defn ok, N 19523, cand 11454, k 3640, w 3, uncertain 454, components 435 (largest 4), states uniform 1816 first-tier 3143
  - 436 ms _private.Init.Data.Vector.Extract.0.Vector.extract_add_left._proof_1 (5a362f9e99724cbf): defn ok, N 14521, cand 8259, k 2854, w 3, uncertain 332, components 310 (largest 3), states uniform 1310 first-tier 4936
- total wall 85.4 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tagN --threads 1 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/init_tagN_t1.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:25.43
	Maximum resident set size (kbytes): 307708
	Exit status: 0
exit=0
```

</details>

<details><summary>[R4] Init, TagN layout, 20 threads, new search, K-based (<code>p4/init_tagN_t20.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants; 56622 processed); layout TagN
- wall: index 318 ms, processing 7.7 s with 20 threads; peak RSS 620324 KiB
- certified: 56622 / 56622; failed: 0
- failures by status: {}
- certified constants: stored (heuristic) 80208288 B; output under Tag4 67668319 B (-15.63%); under TagN 67036818 B (-16.42%)
- unshared (where it fits u64, 56622 constants): 1070001199 B; stored 80208288 B; Tag4 output 67668319 B
- Tag4 output - stored per constant: 49956 smaller, 6228 equal, 438 larger; min -67656 p1 -3220 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- TagN price - stored per constant: min -72624 p1 -3425 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- phase-1 width w: {1: 23506, 2: 33008, 3: 108}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 3 p90 22 p99 113 p99.9 267 max 978
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 3 p99 7 p99.9 13 max 57
- uniform search states per constant: min 0 p1 0 p10 0 p50 12 p90 90 p99 486 p99.9 1094 max 5503
- first-tier search states per constant: min 1 p1 1 p10 3 p50 15 p90 91 p99 618 p99.9 1871 max 17727
- R1/R2 candidates per constant (all): min 0 p1 0 p10 3 p50 33 p90 227 p99 1168 p99.9 4843 max 22458
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 0 p90 3 p99 26 p99.9 183 max 2963
- slowest 10:
  - 2963 ms _private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1 (89ed0e9889141575): defn ok, N 26494, cand 19017, k 4919, w 3, uncertain 587, components 555 (largest 3), states uniform 2351 first-tier 8577
  - 2419 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1 (d126ef57b21ab268): defn ok, N 26943, cand 19283, k 5136, w 3, uncertain 660, components 621 (largest 3), states uniform 2609 first-tier 17727
  - 2381 ms _private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514): defn ok, N 24507, cand 17140, k 4678, w 3, uncertain 571, components 530 (largest 4), states uniform 2247 first-tier 4066
  - 2168 ms _private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1 (e852d49c2b3a2ea7): defn ok, N 26754, cand 19091, k 5146, w 3, uncertain 687, components 651 (largest 3), states uniform 2721 first-tier 13228
  - 2062 ms _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806a): defn ok, N 27628, cand 22458, k 4874, w 3, uncertain 978, components 826 (largest 6), states uniform 3826 first-tier 3793
  - 1895 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1 (eed90987192d5160): defn ok, N 24658, cand 17290, k 4703, w 3, uncertain 557, components 517 (largest 4), states uniform 2193 first-tier 4104
  - 1216 ms _private.Init.Data.Int.DivMod.Lemmas.0.Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb): defn ok, N 18802, cand 13281, k 3236, w 3, uncertain 424, components 406 (largest 4), states uniform 1696 first-tier 2748
  - 1048 ms _private.Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap.0.Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition' (f22512c397919b72): defn ok, N 16156, cand 11692, k 2712, w 3, uncertain 349, components 299 (largest 4), states uniform 1375 first-tier 9252
  - 1001 ms _private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1 (b6be5c1a4db8c149): defn ok, N 19523, cand 11454, k 3640, w 3, uncertain 454, components 435 (largest 4), states uniform 1816 first-tier 3143
  - 890 ms _private.Init.Data.Array.Lemmas.0.Array.toList_reverse.go._unary (c6ad8cd851ef627b): defn ok, N 12884, cand 8661, k 2769, w 3, uncertain 563, components 440 (largest 6), states uniform 2262 first-tier 6387
- total wall 10.2 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tagN --threads 20 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/init_tagN_t20.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:10.24
	Maximum resident set size (kbytes): 619440
	Exit status: 0
exit=0
```

</details>

<details><summary>[R5] Init, Tag4 layout, 20 threads, new search, K-based (<code>p4/init_tag4_t20.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants; 56622 processed); layout Tag4
- wall: index 209 ms, processing 7.8 s with 20 threads; peak RSS 619272 KiB
- certified: 56622 / 56622; failed: 0
- failures by status: {}
- certified constants: stored (heuristic) 80208288 B; output under Tag4 67747841 B (-15.54%); under TagN 67180528 B (-16.24%)
- unshared (where it fits u64, 56622 constants): 1070001199 B; stored 80208288 B; Tag4 output 67747841 B
- Tag4 output - stored per constant: 49956 smaller, 6228 equal, 438 larger; min -67656 p1 -3153 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- TagN price - stored per constant: min -72624 p1 -3344 p10 -363 p50 -46 p90 0 p99 0 p99.9 14 max 70
- phase-1 width w: {1: 23506, 2: 31764, 3: 1352}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 3 p90 22 p99 120 p99.9 271 max 978
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 3 p99 7 p99.9 14 max 57
- uniform search states per constant: min 0 p1 0 p10 0 p50 12 p90 90 p99 514 p99.9 1140 max 5503
- first-tier search states per constant: min 1 p1 1 p10 3 p50 15 p90 91 p99 572 p99.9 1702 max 17727
- R1/R2 candidates per constant (all): min 0 p1 0 p10 3 p50 33 p90 227 p99 1168 p99.9 4843 max 22458
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 0 p90 3 p99 23 p99.9 184 max 2636
- slowest 10:
  - 2636 ms _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806a): defn ok, N 27628, cand 22458, k 4874, w 3, uncertain 978, components 826 (largest 6), states uniform 3826 first-tier 3793
  - 2582 ms _private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514): defn ok, N 24507, cand 17140, k 4678, w 3, uncertain 571, components 530 (largest 4), states uniform 2247 first-tier 4066
  - 2176 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1 (d126ef57b21ab268): defn ok, N 26943, cand 19283, k 5136, w 3, uncertain 660, components 621 (largest 3), states uniform 2609 first-tier 17727
  - 2153 ms _private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1 (89ed0e9889141575): defn ok, N 26494, cand 19017, k 4919, w 3, uncertain 587, components 555 (largest 3), states uniform 2351 first-tier 8577
  - 1265 ms _private.Init.Data.Int.DivMod.Lemmas.0.Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb): defn ok, N 18802, cand 13281, k 3236, w 3, uncertain 424, components 406 (largest 4), states uniform 1696 first-tier 2748
  - 1210 ms _private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1 (eed90987192d5160): defn ok, N 24658, cand 17290, k 4703, w 3, uncertain 557, components 517 (largest 4), states uniform 2193 first-tier 4104
  - 1176 ms _private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1 (e852d49c2b3a2ea7): defn ok, N 26754, cand 19091, k 5146, w 3, uncertain 687, components 651 (largest 3), states uniform 2721 first-tier 13228
  - 1132 ms _private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1 (b6be5c1a4db8c149): defn ok, N 19523, cand 11454, k 3640, w 3, uncertain 454, components 435 (largest 4), states uniform 1816 first-tier 3143
  - 927 ms Lean.Grind.Config.mk.injEq (79a818e3bc347ced): defn ok, N 3512, cand 551, k 360, w 3, uncertain 195, components 17 (largest 44), states uniform 4388 first-tier 196
  - 905 ms _private.Init.Data.Vector.Extract.0.Vector.extract_add_left._proof_1 (5a362f9e99724cbf): defn ok, N 14521, cand 8259, k 2854, w 3, uncertain 332, components 310 (largest 3), states uniform 1310 first-tier 4936
- total wall 10.1 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tag4 --threads 20 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/init_tag4_t20.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:10.15
	Maximum resident set size (kbytes): 618880
	Exit status: 0
exit=0
```

</details>

<details><summary>[R3] Mathlib, TagN layout, 20 threads, new search, K-based (<code>mathlib_tiered_bb.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe (679499 constants; 679499 processed); layout TagN
- wall: index 10950 ms, processing 184.3 s with 20 threads; peak RSS 5282852 KiB
- certified: 679499 / 679499; failed: 0
- failures by status: {}
- certified constants: stored (heuristic) 1468890902 B; output under Tag4 1148638151 B (-21.80%); under TagN 1136221078 B (-22.65%)
- unshared (where it fits u64, 679499 constants): 214351802561585 B; stored 1468890902 B; Tag4 output 1148638151 B
- Tag4 output - stored per constant: 623331 smaller, 52448 equal, 3720 larger; min -258748 p1 -6169 p10 -952 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- TagN price - stored per constant: min -267397 p1 -6663 p10 -952 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- phase-1 width w: {1: 197682, 2: 480001, 3: 1816}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 4 p90 25 p99 112 p99.9 296 max 3077
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 3 p99 6 p99.9 13 max 57
- uniform search states per constant: min 0 p1 0 p10 0 p50 16 p90 102 p99 475 p99.9 1231 max 12358
- first-tier search states per constant: min 1 p1 1 p10 5 p50 20 p90 128 p99 789 p99.9 2673 max 30126
- R1/R2 candidates per constant (all): min 0 p1 0 p10 6 p50 66 p90 424 p99 2004 p99.9 6370 max 81833
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 1 p90 6 p99 49 p99.9 347 max 55050
- slowest 10:
  - 55050 ms CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite (bd34cbe632ec9a56): defn ok, N 95110, cand 81833, k 21461, w 3, uncertain 3077, components 2878 (largest 3), states uniform 12358 first-tier 18449
  - 26795 ms Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual (2b0491741df2ce98): defn ok, N 78913, cand 59202, k 13054, w 3, uncertain 2682, components 2284 (largest 4), states uniform 10570 first-tier 20977
  - 25508 ms AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective (4ece542b15e7b7a1): defn ok, N 66025, cand 52066, k 10555, w 3, uncertain 1707, components 1541 (largest 3), states uniform 6586 first-tier 8986
  - 22486 ms WeierstrassCurve.variableChange_Δ (0473473f736e639b): defn ok, N 63501, cand 18995, k 9233, w 3, uncertain 651, components 640 (largest 3), states uniform 2590 first-tier 25590
  - 19796 ms _private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.0.WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three (67e377956e9a5e65): defn ok, N 50027, cand 26233, k 10413, w 3, uncertain 1611, components 1562 (largest 4), states uniform 6381 first-tier 8729
  - 19704 ms _private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1 (159e2b0d36d95a7f): defn ok, N 70414, cand 61641, k 11700, w 3, uncertain 1627, components 1537 (largest 4), states uniform 6464 first-tier 10045
  - 17288 ms Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux (83b417c6e46f08e2): defn ok, N 64047, cand 41872, k 8745, w 3, uncertain 1688, components 1492 (largest 4), states uniform 6809 first-tier 7020
  - 16213 ms CategoryTheory.Bicategory.mateEquiv_vcomp (9b20bc429f4cd038): defn ok, N 50497, cand 32338, k 8940, w 3, uncertain 1899, components 1431 (largest 14), states uniform 7942 first-tier 15083
  - 14088 ms WeierstrassCurve.isHomogeneous_addSubMapCoeff (f2ce788af955876c): defn ok, N 60092, cand 31902, k 10150, w 3, uncertain 2015, components 1944 (largest 3), states uniform 7948 first-tier 8037
  - 13408 ms AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq (2d33bfe7c13b87fd): defn ok, N 53511, cand 44632, k 12056, w 3, uncertain 2146, components 1866 (largest 5), states uniform 8344 first-tier 30126
- total wall 314.6 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe --threads 20 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/mathlib_tiered_bb.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 5:15.88
	Maximum resident set size (kbytes): 5300268
	Exit status: 0
exit=0
```

</details>

<details><summary>[R7] Mathlib, Tag4 layout, 20 threads, new search, K-based (<code>p4/ml_tag4_t20.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants; 679499 processed); layout Tag4
- wall: index 6355 ms, processing 209.6 s with 20 threads; peak RSS 5246368 KiB
- certified: 679499 / 679499; failed: 0
- failures by status: {}
- certified constants: stored (heuristic) 1468890902 B; output under Tag4 1151220860 B (-21.63%); under TagN 1140753366 B (-22.34%)
- unshared (where it fits u64, 679499 constants): 214351802561585 B; stored 1468890902 B; Tag4 output 1151220860 B
- Tag4 output - stored per constant: 623329 smaller, 52448 equal, 3722 larger; min -258748 p1 -6072 p10 -952 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- TagN price - stored per constant: min -267397 p1 -6426 p10 -952 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- phase-1 width w: {1: 197682, 2: 458516, 3: 23301}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 4 p90 25 p99 115 p99.9 299 max 3077
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 3 p99 7 p99.9 13 max 57
- uniform search states per constant: min 0 p1 0 p10 0 p50 16 p90 102 p99 496 p99.9 1257 max 23682
- first-tier search states per constant: min 1 p1 1 p10 5 p50 20 p90 128 p99 735 p99.9 2622 max 30126
- R1/R2 candidates per constant (all): min 0 p1 0 p10 6 p50 66 p90 424 p99 2004 p99.9 6370 max 81833
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 1 p90 7 p99 53 p99.9 385 max 47306
- slowest 10:
  - 47306 ms CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite (bd34cbe632ec9a56): defn ok, N 95110, cand 81833, k 21461, w 3, uncertain 3077, components 2878 (largest 3), states uniform 12358 first-tier 18449
  - 43264 ms _private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1 (159e2b0d36d95a7f): defn ok, N 70414, cand 61641, k 11700, w 3, uncertain 1627, components 1537 (largest 4), states uniform 6464 first-tier 10045
  - 26452 ms Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual (2b0491741df2ce98): defn ok, N 78913, cand 59202, k 13054, w 3, uncertain 2682, components 2284 (largest 4), states uniform 10570 first-tier 20977
  - 25777 ms AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective (4ece542b15e7b7a1): defn ok, N 66025, cand 52066, k 10555, w 3, uncertain 1707, components 1541 (largest 3), states uniform 6586 first-tier 8986
  - 19717 ms WeierstrassCurve.variableChange_Δ (0473473f736e639b): defn ok, N 63501, cand 18995, k 9233, w 3, uncertain 651, components 640 (largest 3), states uniform 2590 first-tier 25590
  - 16886 ms WeierstrassCurve.Projective.negDblY_eq' (37cd1c7638fa9899): defn ok, N 45785, cand 14522, k 7073, w 3, uncertain 456, components 449 (largest 3), states uniform 1820 first-tier 13122
  - 16295 ms CategoryTheory.Bicategory.mateEquiv_vcomp (9b20bc429f4cd038): defn ok, N 50497, cand 32338, k 8940, w 3, uncertain 1899, components 1431 (largest 14), states uniform 7942 first-tier 15083
  - 15126 ms sum_eight_sq_mul_sum_eight_sq (0bd4b1175ac1d995): defn ok, N 49322, cand 10408, k 7281, w 3, uncertain 263, components 256 (largest 4), states uniform 1053 first-tier 7021
  - 14623 ms WeierstrassCurve.isHomogeneous_addSubMapCoeff (f2ce788af955876c): defn ok, N 60092, cand 31902, k 10150, w 3, uncertain 2015, components 1944 (largest 3), states uniform 7948 first-tier 8037
  - 14351 ms AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq (2d33bfe7c13b87fd): defn ok, N 53511, cand 44632, k 12056, w 3, uncertain 2146, components 1866 (largest 5), states uniform 8344 first-tier 30126
- total wall 346.7 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --layout tag4 --threads 20 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/ml_tag4_t20.csv --select-out /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/ml_all.txt --select-stride 1"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 5:47.70
	Maximum resident set size (kbytes): 5263200
	Exit status: 0
exit=0
```

</details>

<details><summary>[R1] Init, TagN layout, 16 threads, old search, K-based (<code>init_tiered.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants; 56622 processed); layout TagN
- wall: index 209 ms, processing 30.6 s with 16 threads; peak RSS 572040 KiB
- certified: 56597 / 56622; failed: 25
- failures by status: {"resource:States": 25}
  - FAILED Nat.Internal.Linear.ExprCnstr.denote_toNormPoly (069f4b6521a2da52): resource:States; N 525, cand 293, raw 3664 B, 4807 ms
  - FAILED _private.Init.Data.Range.Polymorphic.IntLemmas.0.Int.size_rco._proof_1_1 (1a9c503f0b3871c0): resource:States; N 2537, cand 1674, raw 14882 B, 2341 ms
  - FAILED List.min_findIdx_findIdx (25482ede969f4d9e): resource:States; N 932, cand 461, raw 5351 B, 4458 ms
  - FAILED List.cons_append_cons_perm (3ea9f1a9b25c2e70): resource:States; N 226, cand 109, raw 1300 B, 3780 ms
  - FAILED List.zip_eq_append_iff (53ceab4c4d118b7e): resource:States; N 439, cand 248, raw 2316 B, 2676 ms
  - FAILED Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT (63bcc228082342f2): resource:States; N 3608, cand 2003, raw 18781 B, 2193 ms
  - FAILED Array.zip_eq_append_iff (69037dee155a0c78): resource:States; N 439, cand 248, raw 2308 B, 2048 ms
  - FAILED Std.LinearPreorderPackage.ofOrd._proof_9 (74c94685bcbe1dbf): resource:States; N 401, cand 226, raw 2606 B, 2973 ms
  - FAILED Int.fdiv_eq_ediv (790ad4904df2cf4c): resource:States; N 1262, cand 551, raw 6871 B, 3505 ms
  - FAILED Lean.Grind.Config.mk.injEq (79a818e3bc347ced): resource:States; N 3512, cand 551, raw 8939 B, 16615 ms
  - FAILED USize.toUInt64_shiftRight (7fa9ab3277164432): resource:States; N 822, cand 397, raw 5348 B, 1724 ms
  - FAILED _private.Init.Data.Range.Polymorphic.IntLemmas.0.Int.size_roo._proof_1_1 (87f5bd76e627d460): resource:States; N 3423, cand 2107, raw 18960 B, 2290 ms
  - FAILED BitVec.getMsbD_setWidth (9ba8c88e4f376482): resource:States; N 1044, cand 580, raw 6292 B, 3333 ms
  - FAILED _private.Init.Data.String.Decode.0.UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte (a60acec5ca548536): resource:States; N 1056, cand 569, raw 6019 B, 5094 ms
  - FAILED Int.Internal.Linear.cooper_right (b3180268914b846b): resource:States; N 2365, cand 1160, raw 12378 B, 3176 ms
  - FAILED Lean.Meta.DSimp.Config.mk.injEq (b886b7d44989227c): resource:States; N 746, cand 185, raw 2228 B, 3200 ms
  - FAILED Lean.Grind.Ring.OfSemiring.right_distrib (c163676b7110408a): resource:States; N 1235, cand 668, raw 6747 B, 3260 ms
  - FAILED Lean.Grind.Ring.OfSemiring.mul_assoc (cacd32ba6398d117): resource:States; N 1372, cand 763, raw 7527 B, 4291 ms
  - FAILED _private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_cpopTree._unary (cc0455870fa49978): resource:States; N 2614, cand 1427, raw 15542 B, 2561 ms
  - FAILED Lean.Meta.Simp.Config.mk.injEq (cf72eed2b476eae8): resource:States; N 1994, cand 376, raw 5298 B, 10092 ms
  - FAILED Int.cooper_resolution_dvd_right (d264fc7a3b27308f): resource:States; N 1138, cand 451, raw 5635 B, 3074 ms
  - FAILED Std.LinearPreorderPackage.ofOrd._proof_1 (d6593f0cd64b97f6): resource:States; N 567, cand 297, raw 3329 B, 3318 ms
  - FAILED Lean.Meta.ExtractLetsConfig.mk.injEq (d7c4aa4ea0c241f0): resource:States; N 457, cand 122, raw 1489 B, 2970 ms
  - FAILED ISize.toInt_bmod_two_pow_numBits (e0027ad59db96616): resource:States; N 449, cand 265, raw 3290 B, 2016 ms
  - FAILED _private.Init.Data.Nat.Internal.SOM.0.Nat.Internal.SOM.Poly.add_denote.go (f933e2efb97ec29d): resource:States; N 1474, cand 606, raw 7574 B, 3830 ms
- certified constants: stored (heuristic) 80033614 B; output under Tag4 67531603 B (-15.62%); under TagN 66903767 B (-16.41%)
- unshared (where it fits u64, 56597 constants): 1067313418 B; stored 80033614 B; Tag4 output 67531603 B
- Tag4 output - stored per constant: 49931 smaller, 6228 equal, 438 larger; min -67656 p1 -3200 p10 -362 p50 -45 p90 0 p99 0 p99.9 14 max 70
- TagN price - stored per constant: min -72624 p1 -3407 p10 -362 p50 -45 p90 0 p99 0 p99.9 14 max 70
- phase-1 width w: {1: 23506, 2: 32983, 3: 108}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 4 p90 32 p99 143 p99.9 406 max 1509
- largest component per constant: min 0 p1 0 p10 0 p50 2 p90 5 p99 10 p99.9 16 max 20
- uniform search states per constant: min 0 p1 0 p10 0 p50 15 p90 168 p99 3233 p99.9 79914 max 776614
- first-tier search states per constant: min 1 p1 1 p10 3 p50 15 p90 91 p99 612 p99.9 1871 max 17727
- R1/R2 candidates per constant (all): min 0 p1 0 p10 3 p50 33 p90 227 p99 1169 p99.9 4843 max 22458
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 0 p90 2 p99 27 p99.9 375 max 2869
- slowest 10:
  - 16615 ms Lean.Grind.Config.mk.injEq (79a818e3bc347ced): defn resource:States, N 3512, cand 551, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 10092 ms Lean.Meta.Simp.Config.mk.injEq (cf72eed2b476eae8): defn resource:States, N 1994, cand 376, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 5094 ms _private.Init.Data.String.Decode.0.UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte (a60acec5ca548536): defn resource:States, N 1056, cand 569, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 4807 ms Nat.Internal.Linear.ExprCnstr.denote_toNormPoly (069f4b6521a2da52): defn resource:States, N 525, cand 293, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 4458 ms List.min_findIdx_findIdx (25482ede969f4d9e): defn resource:States, N 932, cand 461, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 4291 ms Lean.Grind.Ring.OfSemiring.mul_assoc (cacd32ba6398d117): defn resource:States, N 1372, cand 763, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 3830 ms _private.Init.Data.Nat.Internal.SOM.0.Nat.Internal.SOM.Poly.add_denote.go (f933e2efb97ec29d): defn resource:States, N 1474, cand 606, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 3780 ms List.cons_append_cons_perm (3ea9f1a9b25c2e70): defn resource:States, N 226, cand 109, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 3505 ms Int.fdiv_eq_ediv (790ad4904df2cf4c): defn resource:States, N 1262, cand 551, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 3333 ms BitVec.getMsbD_setWidth (9ba8c88e4f376482): defn resource:States, N 1044, cand 580, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
- total wall 32.9 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --threads 16 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/init_tiered.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:32.92
	Maximum resident set size (kbytes): 571680
	Exit status: 0
```

</details>

<details><summary>[R2] Mathlib, TagN layout, 20 threads, old search, K-based (all 342 failures listed) (<code>mathlib_tiered.md</code>)</summary>

```text
# sharing_corpus report
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants; 679499 processed); layout TagN
- wall: index 10735 ms, processing 293.2 s with 20 threads; peak RSS 4794008 KiB
- certified: 679157 / 679499; failed: 342
- failures by status: {"resource:States": 342}
  - FAILED Con.quotientQuotientEquivQuotient._proof_3 (0110da50b45f6d89): resource:States; N 691, cand 474, raw 3858 B, 2228 ms
  - FAILED CategoryTheory.Oplax.OplaxTrans.whiskerRight_naturality_naturality (024193d1504bae0e): resource:States; N 850, cand 706, raw 5261 B, 4328 ms
  - FAILED WeierstrassCurve.addSubMapCoeff_condition (02ae6cb3f3ccb488): resource:States; N 42875, cand 35702, raw 272192 B, 5346 ms
  - FAILED WeierstrassCurve.Projective.map_polynomial (039278bb56e318cf): resource:States; N 1373, cand 800, raw 8545 B, 6663 ms
  - FAILED Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq (048653e65a77d222): resource:States; N 19417, cand 8801, raw 96389 B, 4335 ms
  - FAILED CategoryTheory.CartesianMonoidalCategory.preservesLimit_pair_of_isIso_prodComparison (05076104ef79d59c): resource:States; N 723, cand 456, raw 4909 B, 2139 ms
  - FAILED CategoryTheory.Dial.associator_naturality (06625d954659cb4c): resource:States; N 3637, cand 2076, raw 20019 B, 3914 ms
  - FAILED Nat.Internal.Linear.ExprCnstr.denote_toNormPoly (069f4b6521a2da52): resource:States; N 525, cand 293, raw 3664 B, 3967 ms
  - FAILED Std.Tactic.BVDecide.BVExpr.bitblast.blastUmod.denote_go_eq_divRec_r (07629abd4b23b6b7): resource:States; N 2633, cand 1863, raw 15438 B, 5269 ms
  - FAILED Std.DTreeMap.Internal.Impl.maxKey!_eq_iff_getKey?_eq_self_and_forall (07925884a6266444): resource:States; N 468, cand 259, raw 2969 B, 2427 ms
  - FAILED mfderivWithin_projIcc_one (07c512baeb5f1c75): resource:States; N 5218, cand 1580, raw 21192 B, 51806 ms
  - FAILED Fin.snocOrderIso._proof_4 (0885f2f02c71285c): resource:States; N 445, cand 254, raw 2780 B, 4564 ms
  - FAILED CategoryTheory.OplaxFunctor.map₂_leftUnitor_app_assoc (08ac13e87cc8239f): resource:States; N 697, cand 516, raw 4346 B, 3089 ms
  - FAILED skyscraperPresheafCoconeOfSpecializes._proof_1 (0987bedec3054478): resource:States; N 786, cand 619, raw 5723 B, 3581 ms
  - FAILED CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle (09db0be7266c57e7): resource:States; N 9677, cand 5963, raw 50599 B, 7239 ms
  - FAILED _private.Mathlib.Logic.Function.Basic.0.Function.update_comm._proof_1_2 (0ac91487b6da0615): resource:States; N 969, cand 596, raw 5360 B, 5763 ms
  - FAILED List.prod_map_ite (0b2eb2da786365c1): resource:States; N 1156, cand 571, raw 6346 B, 3319 ms
  - FAILED CategoryTheory.Limits.Concrete.colimit_no_zero_smul_divisor (0b86766f0a8777ca): resource:States; N 5328, cand 4211, raw 33045 B, 5049 ms
  - FAILED WeierstrassCurve.Jacobian.negAddY_smul (0c1816c71ee7e564): resource:States; N 14839, cand 6369, raw 70068 B, 29478 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.iso._proof_6 (0ccbe0acfb8c01a0): resource:States; N 980, cand 716, raw 5913 B, 3784 ms
  - FAILED RootPairing.GeckConstruction.ω_mul_h (0cdd7bd7ad88811d): resource:States; N 3391, cand 2117, raw 20844 B, 3585 ms
  - FAILED Std.IO.Process.ResourceUsageStats.mk.injEq (0defcfa7db9298e3): resource:States; N 743, cand 183, raw 2236 B, 5117 ms
  - FAILED List.nextOr_eq_nextOr_of_mem_dropLast (0fe361de030d820f): resource:States; N 726, cand 259, raw 3406 B, 3229 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence._proof_5 (104ede10003f7b68): resource:States; N 708, cand 635, raw 5134 B, 2349 ms
  - FAILED WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis (10fd2472f34f75ee): resource:States; N 5675, cand 3434, raw 34984 B, 3360 ms
  - FAILED WeierstrassCurve.Projective.nonsingular_some (14382a0aa25acb7d): resource:States; N 5131, cand 2608, raw 28344 B, 6243 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.Hom.comm_assoc (1463099f94aacfe0): resource:States; N 939, cand 765, raw 6074 B, 1921 ms
  - FAILED _private.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree.0.WeierstrassCurve.natDegree_coeff_Φ_ofNat (14adbec3312d1ee7): resource:States; N 10152, cand 5547, raw 59028 B, 3838 ms
  - FAILED _private.Std.Time.Format.Basic.0.Std.Time.GenericFormat.DateBuilder.mk.injEq (151105c7790e6da0): resource:States; N 2657, cand 586, raw 8232 B, 29808 ms
  - FAILED Module.reflection_mul_reflection_pow_apply (15b19b23c225d5d4): resource:States; N 22807, cand 16190, raw 137496 B, 6815 ms
  - FAILED Chebyshev.sum_PrimePow_eq_sum_sum' (15d35cc887b44e74): resource:States; N 5255, cand 2678, raw 32060 B, 3978 ms
  - FAILED WeierstrassCurve.Jacobian.addX_smul (19c7000bbae96998): resource:States; N 7999, cand 3839, raw 39674 B, 9829 ms
  - FAILED _private.Init.Data.Range.Polymorphic.IntLemmas.0.Int.size_rco._proof_1_1 (1a9c503f0b3871c0): resource:States; N 2537, cand 1674, raw 14882 B, 1761 ms
  - FAILED AddCon.quotientQuotientEquivQuotient._proof_3 (1c83d0129c48b84a): resource:States; N 691, cand 474, raw 3833 B, 2345 ms
  - FAILED EuclideanGeometry.dist_le_of_wbtw_of_mem_perpBisector (1d53382ea7bed76e): resource:States; N 1764, cand 1126, raw 12062 B, 4254 ms
  - FAILED complEDS₂_mul_b (1de35f2369510380): resource:States; N 2963, cand 1785, raw 17395 B, 4182 ms
  - FAILED Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual (1f13644c31ee2c19): resource:States; N 44737, cand 35231, raw 270991 B, 42764 ms
  - FAILED CartanMatrix.C_off_diag_nonpos (2017e973fe83a45b): resource:States; N 525, cand 253, raw 2892 B, 3554 ms
  - FAILED Zsqrtd.decompose (24d6b3cfc3809d01): resource:States; N 327, cand 150, raw 2295 B, 4708 ms
  - FAILED List.min_findIdx_findIdx (25482ede969f4d9e): resource:States; N 932, cand 461, raw 5351 B, 4635 ms
  - FAILED Set.monotoneOn_or_antitoneOn_iff_uIcc (264ab42cdbcaa5c6): resource:States; N 1344, cand 920, raw 7531 B, 3528 ms
  - FAILED Polynomial.dvd_comp_X_sub_C_iff (273494d41fcaae3f): resource:States; N 602, cand 397, raw 4690 B, 2566 ms
  - FAILED zpow_eq_zpow_iff_of_ne_zero₀ (28553e75283e9a61): resource:States; N 594, cand 336, raw 4454 B, 6299 ms
  - FAILED CategoryTheory.Bicategory.Adjunction.isAbsoluteLeftKanLift._proof_4 (2909d930ae477950): resource:States; N 6847, cand 4708, raw 38796 B, 4953 ms
  - FAILED Prod.Lex.sumLexProdLexDistrib._proof_1 (292d41e89a00a4fa): resource:States; N 2507, cand 1591, raw 14197 B, 10043 ms
  - FAILED intervalIntegral.integral_comp_mul_right (2aada36dbd06cc8d): resource:States; N 1530, cand 929, raw 11444 B, 5194 ms
  - FAILED Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.insertUnitInvariant_insertUnit (2ab0e669a71f1cee): resource:States; N 15224, cand 10198, raw 86345 B, 3954 ms
  - FAILED CategoryTheory.Dial.braiding._proof_1 (2c26af64ab305430): resource:States; N 941, cand 594, raw 5979 B, 3398 ms
  - FAILED Prod.card_box_succ (2d19429c790de96d): resource:States; N 1880, cand 1048, raw 10287 B, 4692 ms
  - FAILED IsEllipticNet.atomRel_neg₄ (2d441e9a9d3af54a): resource:States; N 213, cand 113, raw 1561 B, 1973 ms
  - FAILED Lean.Meta.Grind.Arith.Linear.Struct.mk.injEq (2f66fbe26af9d61a): resource:States; N 3259, cand 604, raw 9267 B, 28252 ms
  - FAILED EReal.instPosMulMono (2fc524512bab92de): resource:States; N 628, cand 383, raw 4820 B, 3215 ms
  - FAILED _private.Std.Time.Date.Unit.Month.0.Std.Time.Month.Ordinal.days_gt_27.match_1_1 (30cce42f1e4c4f83): resource:States; N 960, cand 404, raw 4698 B, 4061 ms
  - FAILED Complex.one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (31ee93ae3848d2f9): resource:States; N 8914, cand 5531, raw 51729 B, 2504 ms
  - FAILED RelEmbedding.sumLexMap._proof_1 (32110f704abc33da): resource:States; N 665, cand 358, raw 3294 B, 3385 ms
  - FAILED _private.Mathlib.Combinatorics.Enumerative.Catalan.Basic.0.gosper_trick (325b041e7ba326e5): resource:States; N 7619, cand 3365, raw 41127 B, 4182 ms
  - FAILED WeierstrassCurve.Jacobian.map_polynomial (328ad9b48fc6ff72): resource:States; N 1379, cand 799, raw 8661 B, 6643 ms
  - FAILED Finset.affineCombination_apply_eq_lineMap_sum (3441a23edd3120c2): resource:States; N 1720, cand 1037, raw 10298 B, 2880 ms
  - FAILED CategoryTheory.Bicategory.Adjunction.isAbsoluteLeftKan._proof_5 (344e5652e6540022): resource:States; N 6756, cand 4715, raw 38383 B, 4881 ms
  - FAILED _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.0.PeriodPair.relation_mul_id_pow_six_eventuallyEq (368b4890271c9406): resource:States; N 6847, cand 3217, raw 39824 B, 3353 ms
  - FAILED WeierstrassCurve.Projective.map_addZ (37096382f74a4bd1): resource:States; N 1860, cand 974, raw 10302 B, 4963 ms
  - FAILED CategoryTheory.MonoidalCategory.tensor_associativity (3771515bb921dcd5): resource:States; N 13842, cand 7979, raw 72675 B, 2958 ms
  - FAILED Ordnode.Valid'.merge_aux (37cf400883f57aab): resource:States; N 1947, cand 809, raw 9546 B, 4491 ms
  - FAILED convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici (38fb1d954ee6758f): resource:States; N 3212, cand 2229, raw 18124 B, 3704 ms
  - FAILED IsEllipticNet.atomRel_abs₄ (39deaf6bfcbb2e33): resource:States; N 215, cand 115, raw 1596 B, 1962 ms
  - FAILED CategoryTheory.OplaxFunctor.casesOn (3b10a9dc9464ee19): resource:States; N 2052, cand 1589, raw 11070 B, 4081 ms
  - FAILED Ordnode.size_balance' (3b9bb4520c80dc3d): resource:States; N 471, cand 252, raw 2677 B, 3374 ms
  - FAILED WeierstrassCurve.Projective.map_negAddY (3c5b17d94e4c297e): resource:States; N 2850, cand 1426, raw 14727 B, 10894 ms
  - FAILED CategoryTheory.Pseudofunctor.leftZigzag_map (3ce5d1a68f3a06a7): resource:States; N 2183, cand 1246, raw 11834 B, 5512 ms
  - FAILED Std.Internal.UV.System.RUsage.mk.injEq (3d81b05e6de39948): resource:States; N 737, cand 177, raw 2159 B, 4901 ms
  - FAILED Std.DTreeMap.Internal.Impl.maxKeyD_eq_iff_getKey?_eq_self_and_forall (3ddaef4a3f7ea95c): resource:States; N 474, cand 261, raw 2958 B, 2238 ms
  - FAILED List.cons_append_cons_perm (3ea9f1a9b25c2e70): resource:States; N 226, cand 109, raw 1300 B, 3205 ms
  - FAILED Lean.Meta.Grind.Arith.CommRing.Ring.mk.injEq (3f0132438e01d6f4): resource:States; N 859, cand 239, raw 2849 B, 4114 ms
  - FAILED LinearIsometry.inner_map_map (3fc316ba4eddd12b): resource:States; N 1064, cand 818, raw 7655 B, 2973 ms
  - FAILED Set.Countable.isPathConnected_compl_of_one_lt_rank (3feaa9164eb44d85): resource:States; N 6576, cand 3723, raw 42734 B, 4605 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence._proof_7 (41b6e77508113e16): resource:States; N 1659, cand 1318, raw 10447 B, 3099 ms
  - FAILED Fin.partialProd_init (4400cf5c19bc4b7e): resource:States; N 290, cand 163, raw 1970 B, 2409 ms
  - FAILED List.prod_map_ite_eq (44e27887a64d4b41): resource:States; N 1341, cand 668, raw 7497 B, 2249 ms
  - FAILED CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.mk.noConfusion (44eef3b46444bd28): resource:States; N 613, cand 530, raw 4218 B, 1656 ms
  - FAILED NNReal.young_inequality_real (454dd605b1b8b067): resource:States; N 196, cand 103, raw 1698 B, 1728 ms
  - FAILED CategoryTheory.Bicategory.adjointifyCounit_left_triangle (45577bdac27616ef): resource:States; N 8186, cand 4661, raw 42017 B, 4193 ms
  - FAILED Polynomial.IsUnitTrinomial.irreducible_aux1 (464dd0e72bdf7500): resource:States; N 3207, cand 1453, raw 18983 B, 3209 ms
  - FAILED PMF.bindOnSupport_comm (47adcca9aeb07114): resource:States; N 1589, cand 1011, raw 9669 B, 3848 ms
  - FAILED Std.Http.Protocol.H1.Config.mk.injEq (48384b9de1b7b380): resource:States; N 946, cand 225, raw 2791 B, 6649 ms
  - FAILED Std.DTreeMap.Internal.Impl.balance!_eq_balanceₘ (4838899f29ca9e49): resource:States; N 30996, cand 16594, raw 157655 B, 2917 ms
  - FAILED _private.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree.0.WeierstrassCurve.expCoeff_rec (48ed6ea90d289946): resource:States; N 12101, cand 5735, raw 62490 B, 6282 ms
  - FAILED Sum.instLocallyFiniteOrder._proof_2 (4a06e3c04cd028c9): resource:States; N 1499, cand 678, raw 7585 B, 3510 ms
  - FAILED Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.denote_go_eq_divRec_q (4a2b19833f605648): resource:States; N 2631, cand 1861, raw 15449 B, 6338 ms
  - FAILED _private.Mathlib.Order.CompleteLattice.MulticoequalizerDiagram.0.Lattice.BicartSq.multicoequalizerDiagram._proof_1_1 (4a571917cd4ac2b0): resource:States; N 932, cand 489, raw 5550 B, 4133 ms
  - FAILED Int.bitwise_bit (4ad7a17ea5a63762): resource:States; N 1766, cand 773, raw 7970 B, 3936 ms
  - FAILED Std.DTreeMap.Internal.Impl.Const.minKeyD_alter_eq_self (4b4390df2f17f5bc): resource:States; N 964, cand 497, raw 5501 B, 2870 ms
  - FAILED Ordnode.dual_balanceL (4c69a982aae8a80d): resource:States; N 4830, cand 2058, raw 21823 B, 3876 ms
  - FAILED _private.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula.0.WeierstrassCurve.Affine.addPolynomial_slope._proof_1_1 (4c96fa973a83d04e): resource:States; N 2276, cand 1497, raw 14292 B, 2192 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.Hom.mk.noConfusion (4de92a6ba54f9c55): resource:States; N 890, cand 759, raw 6048 B, 1794 ms
  - FAILED Lean.Elab.Tactic.BVDecide.BVDecideConfig.mk.injEq (4f69cec71e94aba7): resource:States; N 580, cand 157, raw 1885 B, 3742 ms
  - FAILED RatFunc.mk_eq_localization_mk (4fab4f81cd92c405): resource:States; N 595, cand 449, raw 4227 B, 4087 ms
  - FAILED CategoryTheory.Cat.isLimitProdCone._proof_3 (5120c36d00a372fd): resource:States; N 694, cand 580, raw 4757 B, 3995 ms
  - FAILED MonoidAlgebra.mapRingHom_comp (51e789d353944203): resource:States; N 988, cand 738, raw 5847 B, 2785 ms
  - FAILED Real.rpow_eq_zero_iff_of_nonneg (523bb3d69d7c57ba): resource:States; N 515, cand 218, raw 3356 B, 2130 ms
  - FAILED Polynomial.coeff_divModByMonicAux_mem_span_pow_mul_span._unary (5242c51e3d3c751c): resource:States; N 6927, cand 4815, raw 43384 B, 3524 ms
  - FAILED SimpleGraph.completeBipartiteGraphCongr._proof_1 (52ade6ccdecf2bd7): resource:States; N 383, cand 205, raw 2264 B, 2891 ms
  - FAILED WeierstrassCurve.Projective.addZ_smul (5340e389e05d7f07): resource:States; N 7026, cand 3253, raw 35205 B, 11329 ms
  - FAILED Equiv.swapCore_swapCore (53ad081a101c55ff): resource:States; N 844, cand 339, raw 3167 B, 4476 ms
  - FAILED List.zip_eq_append_iff (53ceab4c4d118b7e): resource:States; N 439, cand 248, raw 2316 B, 2452 ms
  - FAILED QuaternionAlgebra.instRing._proof_1 (55446000b79f4511): resource:States; N 15545, cand 6985, raw 72343 B, 2854 ms
  - FAILED WeierstrassCurve.Projective.dblX_smul (55c2d089702c5ef0): resource:States; N 27252, cand 11090, raw 123591 B, 32153 ms
  - FAILED PFun.prodLift_fst_comp_snd_comp (57964025fca1850a): resource:States; N 545, cand 350, raw 3343 B, 3281 ms
  - FAILED hasSum_mellin_pi_mul₀ (57e841a4f099d987): resource:States; N 1780, cand 798, raw 11635 B, 4920 ms
  - FAILED Ix.584076a12b43fd689f05fe14444694fb4a065983980d5fe49e1ae1cc8c147d1b.CategoryTheory.FreeBicategory.Rel.below (584076a12b43fd68): resource:States; N 1598, cand 570, raw 6571 B, 3669 ms
  - FAILED SimplexCategory.δ_comp_σ_succ (5a7686636459de20): resource:States; N 1286, cand 782, raw 8285 B, 3842 ms
  - FAILED WithBot.instPreorder._proof_2 (5cfe4fad7787ca79): resource:States; N 1929, cand 829, raw 9020 B, 4728 ms
  - FAILED CategoryTheory.Bicategory.Adjunction.homEquiv₁._proof_4 (5d5fa428efcbd711): resource:States; N 5120, cand 3335, raw 27892 B, 5002 ms
  - FAILED WeierstrassCurve.Projective.addX_smul (5d6423d1dd0739d1): resource:States; N 9992, cand 4045, raw 46074 B, 13233 ms
  - FAILED UniqueFactorizationMonoid.normalize_normalized_factor (5da2c274d4614024): resource:States; N 842, cand 446, raw 4718 B, 2281 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.Hom.comm_assoc (5e94d03d6cb1eaef): resource:States; N 832, cand 688, raw 5705 B, 2647 ms
  - FAILED Lean.Lsp.ServerCapabilities.mk.injEq (60123ffe2bd5e279): resource:States; N 995, cand 264, raw 3195 B, 5565 ms
  - FAILED _private.Mathlib.Combinatorics.Additive.Corner.Roth.0.Corners.triangleIndices.instExplicitDisjoint (60c8412247e84115): resource:States; N 690, cand 279, raw 3458 B, 4467 ms
  - FAILED _private.Mathlib.NumberTheory.EllipticDivisibilitySequence.0.IsEllipticNet.atomRel_avg_sub._proof_1_4 (6188ae350b203b04): resource:States; N 3185, cand 2008, raw 18490 B, 3439 ms
  - FAILED CategoryTheory.GlueData.ofGlueData'._proof_7 (62166e0ed13f509c): resource:States; N 22638, cand 16419, raw 128142 B, 8276 ms
  - FAILED CategoryTheory.InjectiveResolution.descHomotopy (62592cafa5427743): resource:States; N 541, cand 337, raw 3321 B, 2547 ms
  - FAILED GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I (62de409bc332fe35): resource:States; N 3723, cand 2011, raw 26250 B, 2861 ms
  - FAILED Lean.Grind.Ring.OfSemiring.instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT (63bcc228082342f2): resource:States; N 3608, cand 2003, raw 18781 B, 3253 ms
  - FAILED AlgebraicGeometry.Scheme.Hom.appIso_inv_naturality_assoc (63beda518b4c3caf): resource:States; N 513, cand 379, raw 3483 B, 2158 ms
  - FAILED iteratedDeriv_vcomp_three (6647aed377ffb0e3): resource:States; N 1192, cand 767, raw 8749 B, 3814 ms
  - FAILED Int.strongNormalizationMonoid._proof_2 (6858a60214fe6666): resource:States; N 677, cand 428, raw 4940 B, 6303 ms
  - FAILED Array.zip_eq_append_iff (69037dee155a0c78): resource:States; N 439, cand 248, raw 2308 B, 2757 ms
  - FAILED AlgebraicGeometry.Scheme.Hom.appIso_hom_naturality_assoc (6a28b9864357fbfb): resource:States; N 501, cand 354, raw 3426 B, 2700 ms
  - FAILED CategoryTheory.OplaxFunctor.rec (6ac688d5ae5f21ac): resource:States; N 2042, cand 1584, raw 10990 B, 4130 ms
  - FAILED HomologicalComplex.biprodX_ext_to_iff (6be87f75e68863bd): resource:States; N 1299, cand 928, raw 7715 B, 3779 ms
  - FAILED ordinaryHypergeometricSeries_norm_div_succ_norm (6c7883918290488f): resource:States; N 6112, cand 3405, raw 35193 B, 4233 ms
  - FAILED Fin.cycleIcc.trans (6d1c00584b709bb1): resource:States; N 1091, cand 552, raw 5995 B, 4159 ms
  - FAILED Matrix.SpecialLinearGroup.diag_commute (6ebe53dc928fdd31): resource:States; N 3441, cand 2341, raw 20367 B, 4741 ms
  - FAILED Nat.pow_sub_one_mod_pow_sub_one (6ed252dbe1ca71c3): resource:States; N 2532, cand 1138, raw 14593 B, 4079 ms
  - FAILED Std.Http.Config.mk.injEq (6f07788f8a1f5f3d): resource:States; N 1501, cand 338, raw 4414 B, 15590 ms
  - FAILED WeierstrassCurve.map_preΨ₄ (6fdb27178066110b): resource:States; N 1953, cand 1050, raw 10793 B, 3908 ms
  - FAILED EReal.toReal_mul (70454a29d4ab18ce): resource:States; N 432, cand 203, raw 2886 B, 3328 ms
  - FAILED CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.noConfusionType (71ad05661ab480b3): resource:States; N 693, cand 400, raw 3838 B, 2666 ms
  - FAILED Ordnode.all_balance' (71dc41de18268698): resource:States; N 592, cand 313, raw 3337 B, 3307 ms
  - FAILED complEDS'_odd (72a8bac9942cd02e): resource:States; N 1221, cand 959, raw 8592 B, 3526 ms
  - FAILED CategoryTheory.Bicategory.postcomp₂._proof_2 (72f4feea510e0955): resource:States; N 946, cand 823, raw 6711 B, 1669 ms
  - FAILED CategoryTheory.OplaxFunctor.mk.injEq (7421c4335aeed7f5): resource:States; N 6774, cand 4665, raw 34342 B, 4644 ms
  - FAILED Std.LinearPreorderPackage.ofOrd._proof_9 (74c94685bcbe1dbf): resource:States; N 401, cand 226, raw 2606 B, 3442 ms
  - FAILED RelEmbedding.sumLiftRelMap._proof_1 (74ec13bbbbd22446): resource:States; N 690, cand 363, raw 3399 B, 3482 ms
  - FAILED QuadraticForm.tmul_comp_tensorComm (755b1be5631c5287): resource:States; N 6104, cand 5273, raw 38426 B, 3325 ms
  - FAILED Fin.insertNthOrderIso._proof_1 (762b4c08bd68c305): resource:States; N 474, cand 263, raw 2860 B, 2615 ms
  - FAILED Int.fdiv_eq_ediv (790ad4904df2cf4c): resource:States; N 1262, cand 551, raw 6871 B, 4768 ms
  - FAILED Equiv.sumCompl._proof_2 (7983bf016f96b11b): resource:States; N 224, cand 140, raw 1359 B, 2024 ms
  - FAILED Lean.Grind.Config.mk.injEq (79a818e3bc347ced): resource:States; N 3512, cand 551, raw 8939 B, 24075 ms
  - FAILED WeierstrassCurve.Jacobian.map_addX (7a238a3b165c8b98): resource:States; N 1957, cand 974, raw 10508 B, 7348 ms
  - FAILED ENNReal.zero_rpow_mul_self (7b060622585e6615): resource:States; N 338, cand 189, raw 2473 B, 3303 ms
  - FAILED complEDS_odd (7b88a7a0758d63f8): resource:States; N 5602, cand 2814, raw 30541 B, 4171 ms
  - FAILED WeierstrassCurve.Projective.negDblY_smul (7d2f95bea351a5d5): resource:States; N 34580, cand 13405, raw 157201 B, 20857 ms
  - FAILED AddMonoidAlgebra.mapDomainRingHom_comp (7e815adb73c746c8): resource:States; N 1053, cand 752, raw 6251 B, 3204 ms
  - FAILED Lean.Meta.Grind.Arith.Cutsat.State.mk.injEq (7ed8e8a1cfe80863): resource:States; N 1648, cand 470, raw 5927 B, 8226 ms
  - FAILED CompositionSeries.Equivalent.symm (7ef7db76725b1a60): resource:States; N 607, cand 477, raw 3922 B, 2989 ms
  - FAILED CategoryTheory.OplaxFunctor.mapComp_naturality_left_app_assoc (7f1bf500d933618e): resource:States; N 828, cand 647, raw 5140 B, 2959 ms
  - FAILED Multiset.prod_X_sub_X_eq_sum_esymm (7f4e5b344f37104f): resource:States; N 1425, cand 723, raw 8966 B, 1917 ms
  - FAILED USize.toUInt64_shiftRight (7fa9ab3277164432): resource:States; N 822, cand 397, raw 5348 B, 3004 ms
  - FAILED WeierstrassCurve.exists_isIntegral (7fef0608befcf277): resource:States; N 7647, cand 4615, raw 48721 B, 2883 ms
  - FAILED SimpleGraph.Walk.count_edges_takeUntil_le_one (805d1ef524524a07): resource:States; N 4032, cand 1683, raw 18086 B, 5986 ms
  - FAILED CategoryTheory.Pseudofunctor.presheafHom (809d4c861f7b0420): resource:States; N 613, cand 479, raw 4066 B, 2048 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence._proof_9 (80b23956e6c036a6): resource:States; N 810, cand 779, raw 6321 B, 1938 ms
  - FAILED Sum.instLocallyFiniteOrder._proof_4 (818a88a6c0522b21): resource:States; N 1473, cand 668, raw 7370 B, 4394 ms
  - FAILED CartanMatrix.B_off_diag_nonpos (81a6758ac9cb629b): resource:States; N 506, cand 246, raw 2837 B, 3428 ms
  - FAILED CommRingCat.tensorProdIsoPushout._proof_1 (82360661527d0711): resource:States; N 2794, cand 2206, raw 19522 B, 3053 ms
  - FAILED QuadraticForm.tmul_comp_tensorAssoc (824caddf19dcd99d): resource:States; N 12575, cand 10916, raw 78645 B, 7379 ms
  - FAILED ordinaryHypergeometricSeries_radius_eq_one (8251ca1dd406b1bc): resource:States; N 11252, cand 7786, raw 67264 B, 2579 ms
  - FAILED _private.Mathlib.Algebra.Jordan.Basic.0.aux2 (825a7f9d31cf57ef): resource:States; N 1095, cand 735, raw 7088 B, 2648 ms
  - FAILED Ix.838918e4fa0df72973acb0540729e5e272cef5a708a29fafa16d1bdea2a2a360.CategoryTheory.FreeBicategory.Rel (838918e4fa0df729): resource:States; N 1155, cand 473, raw 4546 B, 5404 ms
  - FAILED LinearIndependent.pair_add_smul_left_iff (83d7722edb43f607): resource:States; N 1250, cand 747, raw 7980 B, 6323 ms
  - FAILED _private.Mathlib.Condensed.Light.Sequence.0.InternalProjectivityProof.cocone._proof_1 (844e1dc8428f7713): resource:States; N 7457, cand 5572, raw 47350 B, 4527 ms
  - FAILED _private.Std.Http.Data.URI.Encoding.0.Std.Http.URI.hexDigit_isHexDigit (8497d40dd9ce756a): resource:States; N 1437, cand 631, raw 7923 B, 3736 ms
  - FAILED preNormEDS'_even (84d91e862b60c351): resource:States; N 962, cand 745, raw 6731 B, 2741 ms
  - FAILED Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable (85b5430e1902fb09): resource:States; N 4606, cand 2780, raw 28921 B, 5031 ms
  - FAILED _private.Init.Data.Range.Polymorphic.IntLemmas.0.Int.size_roo._proof_1_1 (87f5bd76e627d460): resource:States; N 3423, cand 2107, raw 18960 B, 3182 ms
  - FAILED NNReal.toReal_liminf (886e58834b680832): resource:States; N 1121, cand 470, raw 6533 B, 3859 ms
  - FAILED Lean.Meta.Config.mk.injEq (88a8fe1cee22f3a2): resource:States; N 953, cand 231, raw 2801 B, 7526 ms
  - FAILED Nat.even_mul (88e2e61a254db53c): resource:States; N 458, cand 254, raw 2737 B, 5206 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.Hom.rec (8954d7950abe8690): resource:States; N 750, cand 647, raw 5047 B, 2235 ms
  - FAILED IsEllipticNet.rel_eq (8aa86f0cff06f689): resource:States; N 2767, cand 1004, raw 13190 B, 6485 ms
  - FAILED Int.mul_mem_zero_one_two_three_four_iff (8c33c9187f000539): resource:States; N 17513, cand 7589, raw 80914 B, 4253 ms
  - FAILED hasFPowerSeriesAt_clog_one (8cec083c886dd675): resource:States; N 8705, cand 5496, raw 51933 B, 2389 ms
  - FAILED crossProduct._proof_5 (8e5bb3ed61584188): resource:States; N 767, cand 541, raw 5406 B, 2087 ms
  - FAILED AlgHom.mulLeftRightMatrix.inv_comp (8f4148a124e01826): resource:States; N 9612, cand 8372, raw 61875 B, 4344 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.instCategory._proof_2 (91cadc0732eec323): resource:States; N 1187, cand 883, raw 7273 B, 4485 ms
  - FAILED List.formPerm_apply_mem_of_mem (91d5657e420c6b08): resource:States; N 1072, cand 466, raw 5235 B, 3867 ms
  - FAILED associator_cocycle (92335d6c3c2d1ce3): resource:States; N 229, cand 126, raw 1567 B, 2429 ms
  - FAILED MonoidAlgebra.mapDomainRingHom_comp (962c3abe81315a60): resource:States; N 1052, cand 752, raw 6187 B, 2617 ms
  - FAILED LieModule.Cohomology.d₂₃._proof_6 (96d50dfc59abe333): resource:States; N 3512, cand 2567, raw 22225 B, 2343 ms
  - FAILED Std.DTreeMap.Internal.Impl.minKeyD_eq_iff_getKey?_eq_self_and_forall (9846ee4ba946bb09): resource:States; N 474, cand 261, raw 2961 B, 3127 ms
  - FAILED CategoryTheory.Bicategory.Adjunction.comp_right_triangle_aux (9a985ef3da377623): resource:States; N 11168, cand 6655, raw 58092 B, 7730 ms
  - FAILED List.permutations_take_two (9b5341fea812f904): resource:States; N 975, cand 442, raw 4623 B, 5758 ms
  - FAILED BitVec.getMsbD_setWidth (9ba8c88e4f376482): resource:States; N 1044, cand 580, raw 6292 B, 4424 ms
  - FAILED CategoryTheory.Pseudofunctor.CoGrothendieck.category._proof_2 (9d02d36fd8561096): resource:States; N 1615, cand 1206, raw 10852 B, 1344 ms
  - FAILED Algebra.TensorProduct.assoc._proof_3 (9e8a255342cc5aa2): resource:States; N 11531, cand 10252, raw 71709 B, 4943 ms
  - FAILED _private.Mathlib.Topology.Sheaves.Flasque.0.isFlasque_skyscraperSheaf_of_epi_from._proof_1_4 (9ee6d021052e769a): resource:States; N 763, cand 571, raw 5457 B, 3040 ms
  - FAILED CategoryTheory.Mat_.lift_additive (9f271d1cfda1de5d): resource:States; N 1269, cand 866, raw 7632 B, 4056 ms
  - FAILED ProbabilityTheory.IsRatStieltjesPoint.ite (9face6034105de96): resource:States; N 516, cand 274, raw 3281 B, 3229 ms
  - FAILED SkyscraperPresheafFunctor.map'._proof_1 (a05c52d70a2c238b): resource:States; N 1467, cand 1032, raw 8892 B, 2963 ms
  - FAILED RingCon.quotientQuotientEquivQuotient._proof_4 (a12d2e35e480f974): resource:States; N 629, cand 459, raw 3611 B, 2048 ms
  - FAILED Sum.instLocallyFiniteOrder._proof_1 (a176103b8d631c29): resource:States; N 1473, cand 668, raw 7415 B, 3255 ms
  - FAILED PosNum.cmp_swap (a265895219e25b2e): resource:States; N 622, cand 227, raw 2671 B, 4456 ms
  - FAILED Std.DTreeMap.Internal.Impl.minKey!_eq_iff_getKey?_eq_self_and_forall (a434dbaf11f008e7): resource:States; N 468, cand 259, raw 2967 B, 2730 ms
  - FAILED EisensteinSeries.D2_mul (a44779c68492889c): resource:States; N 4586, cand 2468, raw 31406 B, 3335 ms
  - FAILED Matrix.adjugate_fin_three (a55d6767308a54cc): resource:States; N 18499, cand 11522, raw 102293 B, 7902 ms
  - FAILED LinearIndependent.pair_add_smul_right_iff (a5e699aad818e70f): resource:States; N 1258, cand 749, raw 8072 B, 6233 ms
  - FAILED _private.Init.Data.String.Decode.0.UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte (a60acec5ca548536): resource:States; N 1056, cand 569, raw 6019 B, 5242 ms
  - FAILED PeriodPair.summable_weierstrassPExceptSummand (a6cd91e6b481b1ce): resource:States; N 10757, cand 5284, raw 71551 B, 3686 ms
  - FAILED preNormEDS_even (a6dd2dcc70523304): resource:States; N 5003, cand 2317, raw 27237 B, 3549 ms
  - FAILED SSet.Truncated.HomotopyCategory.homToNerveMk._proof_1 (ab9d7356862bfe33): resource:States; N 5673, cand 3628, raw 32402 B, 4502 ms
  - FAILED Turing.PartrecToTM2.tr_ret_respects (ad02ebc1e8923bfd): resource:States; N 4304, cand 2073, raw 23846 B, 2615 ms
  - FAILED HasMFDerivWithinAt.hcongr_24 (ad63aeb0a1436353): resource:States; N 6865, cand 1852, raw 23700 B, 39439 ms
  - FAILED UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero (adc2b066d2f6ba14): resource:States; N 1982, cand 1233, raw 14736 B, 3034 ms
  - FAILED _private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss.0.Polynomial.Chebyshev.sum_exp._proof_1_3 (aefeac3931c5554c): resource:States; N 1517, cand 1213, raw 11863 B, 3626 ms
  - FAILED _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.0.PeriodPair.relation_add_coe (af481bb774050c36): resource:States; N 643, cand 333, raw 4684 B, 1963 ms
  - FAILED _private.Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Lemmas.0.RootPairing.chainBotCoeff_mul_chainTopCoeff.aux_1 (af609e9270f1ac5f): resource:States; N 7945, cand 4124, raw 46232 B, 4113 ms
  - FAILED Interval.lattice._proof_3 (b06abafdc4498d03): resource:States; N 459, cand 250, raw 2829 B, 2895 ms
  - FAILED WithOne.unoneD_eq_iff (b1847519022b7343): resource:States; N 261, cand 86, raw 1656 B, 3599 ms
  - FAILED Polynomial.discr_of_degree_eq_two (b2338e6157a26a6a): resource:States; N 24649, cand 17277, raw 144709 B, 4915 ms
  - FAILED Set.nonempty_Ico_sdiff (b25c95dc784482a0): resource:States; N 1006, cand 512, raw 6385 B, 3790 ms
  - FAILED Int.Internal.Linear.cooper_right (b3180268914b846b): resource:States; N 2365, cand 1160, raw 12378 B, 5580 ms
  - FAILED WeierstrassCurve.Jacobian.map_negAddY (b4fe31f265e5e253): resource:States; N 3377, cand 1582, raw 17199 B, 10993 ms
  - FAILED ProbabilityTheory.hasFPowerSeriesAt_mgf (b674f4e1ebeeebef): resource:States; N 8228, cand 5286, raw 44888 B, 2720 ms
  - FAILED AlgebraicGeometry.Scheme.Hom.appIso (b72a5a839fdda20b): resource:States; N 211, cand 137, raw 1837 B, 2271 ms
  - FAILED WeierstrassCurve.Jacobian.nonsingular_some (b75b2fd142fe91ce): resource:States; N 5458, cand 2755, raw 30199 B, 4643 ms
  - FAILED _private.Mathlib.Algebra.Polynomial.Derivative.0.Polynomial.derivative_mul._proof_1_1 (b7a482017f422ce2): resource:States; N 625, cand 426, raw 4712 B, 1965 ms
  - FAILED CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext_iff (b827e40f63210cf9): resource:States; N 955, cand 820, raw 6656 B, 1780 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.isoMk._proof_3 (b8396b9a9da7ff22): resource:States; N 1468, cand 1127, raw 9302 B, 2707 ms
  - FAILED Real.mul_rpow (b845aaf952f8f741): resource:States; N 954, cand 482, raw 5826 B, 4687 ms
  - FAILED Lean.Meta.DSimp.Config.mk.injEq (b886b7d44989227c): resource:States; N 746, cand 185, raw 2228 B, 4610 ms
  - FAILED RootPairing.root_sub_root_mem_of_pairingIn_pos (b8c4ef4cdee56456): resource:States; N 6270, cand 3537, raw 35598 B, 3554 ms
  - FAILED Affine.Triangle.scalene_iff_dist_ne_and_dist_ne_and_dist_ne (b8c9578e19e2f25b): resource:States; N 9499, cand 2928, raw 39715 B, 3263 ms
  - FAILED WeierstrassCurve.Ψ_even (ba713e6a6083c231): resource:States; N 3955, cand 2681, raw 25234 B, 4576 ms
  - FAILED CategoryTheory.Bicategory.Adjunction.comp_left_triangle_aux (bb32cb6f221a5b09): resource:States; N 11254, cand 6637, raw 58366 B, 8380 ms
  - FAILED Path.truncate._proof_3 (bb5b22e2cb712f24): resource:States; N 845, cand 431, raw 5310 B, 3083 ms
  - FAILED List.sum_map_ite (bb9de0401d682b1c): resource:States; N 1248, cand 663, raw 7000 B, 3254 ms
  - FAILED LinearMap.uncurryMid._proof_1 (bc2f74815a170488): resource:States; N 1670, cand 1166, raw 9867 B, 3554 ms
  - FAILED Polynomial.hasseDeriv_comp (bc31dc5dbae349b7): resource:States; N 3271, cand 1656, raw 20269 B, 4298 ms
  - FAILED WeierstrassCurve.Projective.map_dblX (bce37c4863c98968): resource:States; N 7729, cand 2988, raw 35732 B, 45285 ms
  - FAILED Convex.isLittleO_alternate_sum_square (bd1f2c92a1695258): resource:States; N 9815, cand 6322, raw 59914 B, 6067 ms
  - FAILED OrderIso.sumCongr._proof_2 (bd2a1de85b70ef48): resource:States; N 669, cand 337, raw 3482 B, 3271 ms
  - FAILED WithBot.unbotD_eq_iff (bde54059d23daa38): resource:States; N 253, cand 79, raw 1564 B, 3993 ms
  - FAILED Polynomial.isLeftCancelMulZero_iff (bde6335bb10fe6a8): resource:States; N 1821, cand 946, raw 11007 B, 3598 ms
  - FAILED Matrix.diagonal_fin_three (bf8d4c6a163aab12): resource:States; N 1644, cand 798, raw 8680 B, 3312 ms
  - FAILED _private.Std.Time.Format.Basic.0.Std.Time.GenericFormat.DateBuilder.insert (bfcbe4ebde3e47d5): resource:States; N 1250, cand 248, raw 6803 B, 29399 ms
  - FAILED FirstOrder.Field.charP_iff_model_fieldOfChar (bfd93b81add0b86f): resource:States; N 1480, cand 874, raw 10017 B, 4309 ms
  - FAILED CategoryTheory.Bicategory.LeftLift.IsKan.adjunction._proof_2 (c01ca73d6bb69fb7): resource:States; N 5580, cand 3926, raw 31730 B, 4639 ms
  - FAILED _private.Std.Time.Date.Unit.Month.0.Std.Time.Month.Ordinal.cumulativeDays_le.match_1_1 (c0704b1f2bea457b): resource:States; N 961, cand 404, raw 4679 B, 5479 ms
  - FAILED CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.congr (c0f491950a0466c0): resource:States; N 671, cand 587, raw 4796 B, 1964 ms
  - FAILED Lean.Grind.Ring.OfSemiring.right_distrib (c163676b7110408a): resource:States; N 1235, cand 668, raw 6747 B, 3710 ms
  - FAILED Std.Time.DateFormatSymbols.mk.injEq (c173daf6bbd1887d): resource:States; N 1429, cand 335, raw 4256 B, 14042 ms
  - FAILED Std.Time.Month.Ordinal.difference_eq (c46a7632603ee8d6): resource:States; N 5269, cand 2903, raw 28842 B, 5054 ms
  - FAILED CategoryTheory.FreeBicategory.liftHom₂_congr (c539f83b65f53ec1): resource:States; N 3526, cand 1881, raw 17748 B, 4323 ms
  - FAILED CategoryTheory.Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_naturality_assoc (c56b24e1dad10ac3): resource:States; N 477, cand 341, raw 3149 B, 1501 ms
  - FAILED Std.Tactic.BVDecide.LRAT.Internal.DefaultFormula.rupAdd_result (c5e6fa6fd60b1721): resource:States; N 2370, cand 1269, raw 12344 B, 3588 ms
  - FAILED WeierstrassCurve.Projective.map_addX (c779138c95a72602): resource:States; N 2604, cand 1290, raw 13513 B, 10220 ms
  - FAILED IsOpenMap.pullbackObjIso_hom_naturality (c7c4650eb40566f9): resource:States; N 4106, cand 3358, raw 26358 B, 4745 ms
  - FAILED RBTree.RBNode.Path.Ordered.fill._f (c7f15b0db1e38d5f): resource:States; N 1035, cand 480, raw 4733 B, 5338 ms
  - FAILED preNormEDS_odd (c8ae888fffb97145): resource:States; N 5903, cand 2751, raw 31271 B, 2661 ms
  - FAILED CategoryTheory.Bicategory.LeftExtension.IsKan.adjunction._proof_2 (c9eba00a21e017ac): resource:States; N 5557, cand 3655, raw 30614 B, 6845 ms
  - FAILED _private.Mathlib.RingTheory.Polynomial.Resultant.Basic.0.Polynomial.sylvesterDeriv_of_natDegree_eq_three (cabce28d54f8e662): resource:States; N 32105, cand 14771, raw 156105 B, 4397 ms
  - FAILED Lean.Grind.Ring.OfSemiring.mul_assoc (cacd32ba6398d117): resource:States; N 1372, cand 763, raw 7527 B, 4849 ms
  - FAILED IsDiscreteValuationRing.toEuclideanDomain._proof_4 (cb687d8c6927e46e): resource:States; N 1148, cand 704, raw 7138 B, 4564 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData'.comm_assoc (cbac8bf1386f68b4): resource:States; N 996, cand 810, raw 6351 B, 2475 ms
  - FAILED _private.Init.Data.BitVec.Bitblast.0.BitVec.addRecAux_cpopTree._unary (cc0455870fa49978): resource:States; N 2614, cand 1427, raw 15542 B, 5006 ms
  - FAILED tendsto_order._to_dual_1 (cd028329a6247ea6): resource:States; N 452, cand 254, raw 2759 B, 2657 ms
  - FAILED OnePoint.map_smul (cd57d561038637e3): resource:States; N 2519, cand 1526, raw 14773 B, 3058 ms
  - FAILED GenLoop.transAt_distrib (cda6b3d6b619b4bf): resource:States; N 3975, cand 2784, raw 23171 B, 3294 ms
  - FAILED bihimp_triangle (ce0fd6874c8cb693): resource:States; N 260, cand 115, raw 1543 B, 2933 ms
  - FAILED Lean.Meta.Grind.Arith.Cutsat.ToIntInfo.mk.injEq (ce4ae3abeaa66b8d): resource:States; N 1500, cand 334, raw 4256 B, 18765 ms
  - FAILED Interval.lattice._proof_2 (ced9fb3d3e8f1fc4): resource:States; N 459, cand 250, raw 2825 B, 3077 ms
  - FAILED WeierstrassCurve.Affine.cyclic_sum_Y_mul_X_sub_X (cf04c82f6fa506a7): resource:States; N 10129, cand 6394, raw 57956 B, 3245 ms
  - FAILED RingCon.quotientQuotientEquivQuotient._proof_3 (cf5302a6ec1fbd44): resource:States; N 629, cand 459, raw 3598 B, 2097 ms
  - FAILED Lean.Meta.Simp.Config.mk.injEq (cf72eed2b476eae8): resource:States; N 1994, cand 376, raw 5298 B, 19592 ms
  - FAILED WeierstrassCurve.Projective.negAddY_smul (cfceec4f9760fc88): resource:States; N 10831, cand 4697, raw 50913 B, 16523 ms
  - FAILED Algebra.TensorProduct.tensorTensorTensorComm._proof_2 (d1bc3029e85ea857): resource:States; N 20808, cand 19243, raw 131570 B, 6341 ms
  - FAILED CategoryTheory.Bicategory.conjugateEquiv_comp (d20aa44b163acd92): resource:States; N 8370, cand 4571, raw 42814 B, 2343 ms
  - FAILED Int.cooper_resolution_dvd_right (d264fc7a3b27308f): resource:States; N 1138, cand 451, raw 5635 B, 2457 ms
  - FAILED QuaternionAlgebra.instStarRing._proof_2 (d35d55c802ac75a6): resource:States; N 5869, cand 2538, raw 28780 B, 4076 ms
  - FAILED _private.Lean.Elab.Tactic.Simp.0.Lean.Elab.Tactic.elabSimpConfigAux.evalConfigItem (d429aaec154add51): resource:States; N 1940, cand 407, raw 10168 B, 21340 ms
  - FAILED CommGroupWithZero.instStrongNormalizedGCDMonoid._proof_7 (d4dcb32ffada7b7e): resource:States; N 821, cand 430, raw 5000 B, 3278 ms
  - FAILED Std.LinearPreorderPackage.ofOrd._proof_1 (d6593f0cd64b97f6): resource:States; N 567, cand 297, raw 3329 B, 4035 ms
  - FAILED Fin.partialSum_init (d7a635877bd89d57): resource:States; N 290, cand 163, raw 1965 B, 2505 ms
  - FAILED LinearMap.uncurryLeft._proof_2 (d7be0a187b33fcf4): resource:States; N 1757, cand 1245, raw 10506 B, 2669 ms
  - FAILED Lean.Meta.ExtractLetsConfig.mk.injEq (d7c4aa4ea0c241f0): resource:States; N 457, cand 122, raw 1489 B, 3077 ms
  - FAILED CategoryTheory.CatEnriched.instBicategory._proof_11 (d84838fc1e6f8631): resource:States; N 877, cand 477, raw 4702 B, 4102 ms
  - FAILED Set.preimage_boolIndicator (d8c1f44a2ba8c077): resource:States; N 1021, cand 479, raw 5182 B, 2797 ms
  - FAILED Complex.cpow_eq_zero_iff (d90643da4951c497): resource:States; N 460, cand 192, raw 2908 B, 2520 ms
  - FAILED CategoryTheory.MonoidalCategory.rightUnitor_monoidal (d968b12135f9d92e): resource:States; N 2510, cand 1523, raw 13325 B, 3171 ms
  - FAILED RootPairing.Base.root_add_root_mem_of_mem_of_mem (da0c7f822e133391): resource:States; N 2819, cand 1715, raw 17917 B, 3932 ms
  - FAILED EisensteinSeries.eisSummand_SL2_apply (da7f69389d081e58): resource:States; N 5587, cand 3116, raw 34127 B, 2883 ms
  - FAILED AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth (daa5d7f02cabe4d9): resource:States; N 23605, cand 19006, raw 149885 B, 2051 ms
  - FAILED SimplexCategory.δ_comp_σ_self (dad509fef03e40d3): resource:States; N 1694, cand 1125, raw 11161 B, 3427 ms
  - FAILED HomologicalComplex.alternatingConst._proof_4 (db82d9db6b5caa43): resource:States; N 732, cand 411, raw 4089 B, 2559 ms
  - FAILED TopCat.GlueData.MkCore.t' (dbe062a0e0de18ee): resource:States; N 630, cand 468, raw 4649 B, 2319 ms
  - FAILED PMF.toOuterMeasure_bindOnSupport_apply (dc147f356655cded): resource:States; N 1098, cand 619, raw 6499 B, 4663 ms
  - FAILED IsEllipticNet.atomRel_avg_sub (dd3a57341da30718): resource:States; N 1335, cand 662, raw 6883 B, 6429 ms
  - FAILED List.Nodup.rotate_congr_iff (dd887cf3ac294df0): resource:States; N 395, cand 142, raw 2259 B, 4304 ms
  - FAILED PMF.bindOnSupport_bindOnSupport (de3fa84b83282950): resource:States; N 2529, cand 1709, raw 15279 B, 6255 ms
  - FAILED symmDiff_triangle (de462c19e0336823): resource:States; N 260, cand 115, raw 1546 B, 2383 ms
  - FAILED eq_or_eq_or_eq_of_forall_not_lt_lt (de94d7fccc323cf8): resource:States; N 369, cand 256, raw 2040 B, 2230 ms
  - FAILED _private.Mathlib.NumberTheory.Bernoulli.0.Bernoulli.pIntegral_bernoulli_even_term (def365185027508d): resource:States; N 4560, cand 2573, raw 30109 B, 4100 ms
  - FAILED ISize.toInt_bmod_two_pow_numBits (e0027ad59db96616): resource:States; N 449, cand 265, raw 3290 B, 3248 ms
  - FAILED Float.Model.UnpackedFloat.unpack_beq_unpack_iff (e0e9b5e9762b8f06): resource:States; N 338, cand 148, raw 2304 B, 2068 ms
  - FAILED CategoryTheory.Pseudofunctor.Grothendieck.Hom.noConfusionType (e18715b78d59b1ef): resource:States; N 615, cand 350, raw 3278 B, 2176 ms
  - FAILED Int.even_mul (e2abe704472c2b9f): resource:States; N 471, cand 266, raw 2939 B, 3431 ms
  - FAILED Sum.instLocallyFiniteOrder._proof_3 (e3966264d60b4ac7): resource:States; N 1499, cand 678, raw 7494 B, 4188 ms
  - FAILED Nat.WithBot.add_eq_three_iff (e44c3223c4d0ffd5): resource:States; N 940, cand 351, raw 4755 B, 3033 ms
  - FAILED WithBot.unbotD_eq_unbotD_iff (e4dd345b8a079d31): resource:States; N 320, cand 108, raw 1762 B, 3204 ms
  - FAILED LieModule.Cohomology.d₂₃_comp_d₁₂ (e69ea582cebe3fd1): resource:States; N 4768, cand 3417, raw 28024 B, 4091 ms
  - FAILED Std.DTreeMap.Internal.Impl.Const.maxKeyD_alter_eq_self (e6cd1281b1ee3725): resource:States; N 964, cand 497, raw 5440 B, 2573 ms
  - FAILED Polynomial.Chebyshev.one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T (e71cf5531f9a2562): resource:States; N 6334, cand 3439, raw 36248 B, 5061 ms
  - FAILED WeierstrassCurve.map_b₈ (e8379e4697f41312): resource:States; N 923, cand 567, raw 5802 B, 2610 ms
  - FAILED iteratedDeriv_scomp_three (e8422f86fcf5c6a5): resource:States; N 764, cand 562, raw 6219 B, 2973 ms
  - FAILED _private.Mathlib.Data.Finsupp.Single.0.Finsupp.update_comm._proof_1_1 (e91fd4241b3a641f): resource:States; N 654, cand 369, raw 3504 B, 3505 ms
  - FAILED WeierstrassCurve.Jacobian.polynomial_relation (ea93ed8e45d2ba10): resource:States; N 4947, cand 2320, raw 25558 B, 5106 ms
  - FAILED jacobiSum_nontrivial_inv (ea9487fda33c55f5): resource:States; N 3552, cand 2112, raw 22968 B, 5096 ms
  - FAILED WeierstrassCurve.Projective.map_negDblY (eac9493f9c619a72): resource:States; N 9567, cand 3594, raw 42548 B, 30753 ms
  - FAILED hasFPowerSeriesOnBall_inverse_one_add (ede5a9778252585c): resource:States; N 8655, cand 5536, raw 47130 B, 2369 ms
  - FAILED Batteries.UnionFind.parentD_linkAux (ee0bc3283dbfbfbb): resource:States; N 914, cand 531, raw 5046 B, 3066 ms
  - FAILED CategoryTheory.Bicategory.LeftExtension.isKanOfWhiskerLeftAdjoint._proof_1 (ee2a364990c758e7): resource:States; N 6588, cand 4361, raw 37219 B, 3588 ms
  - FAILED AlgebraicGeometry.continuousMapPresheaf._proof_2 (ef200218e86a63bf): resource:States; N 228, cand 200, raw 1933 B, 2618 ms
  - FAILED RBTree.RBNode.Path.ordered_iff (f0b1bded271bf0b9): resource:States; N 3170, cand 1406, raw 14964 B, 5280 ms
  - FAILED AddMonoidAlgebra.mapRingHom_comp (f0f4c81b4b62d6de): resource:States; N 989, cand 738, raw 5960 B, 3253 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.instCategory._proof_4 (f0f75fc624541337): resource:States; N 1500, cand 1067, raw 8745 B, 4411 ms
  - FAILED iteratedDeriv_comp_three (f254d5e3cdf89797): resource:States; N 611, cand 429, raw 4960 B, 3519 ms
  - FAILED Matroid.IsBase.inter_isBasis_iff_compl_inter_isBasis_dual (f2c497519d91bfe0): resource:States; N 243, cand 125, raw 1753 B, 1791 ms
  - FAILED WeierstrassCurve.isHomogeneous_addSubMapCoeff (f2ce788af955876c): resource:States; N 60092, cand 31902, raw 311874 B, 5187 ms
  - FAILED Polynomial.discr_of_degree_eq_three (f2e292bc76352c33): resource:States; N 21913, cand 12913, raw 121652 B, 3418 ms
  - FAILED MultilinearMap.uncurryRight._proof_1 (f3251295a942cfc4): resource:States; N 1664, cand 1196, raw 9966 B, 4171 ms
  - FAILED UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero (f3b428d7c560e3b3): resource:States; N 2102, cand 1637, raw 16752 B, 2836 ms
  - FAILED _private.Init.Data.Nat.Internal.SOM.0.Nat.Internal.SOM.Poly.add_denote.go (f933e2efb97ec29d): resource:States; N 1474, cand 606, raw 7574 B, 5413 ms
  - FAILED isCusp_SL2Z_iff (f9e2e7cb8c1f6dbb): resource:States; N 3624, cand 2170, raw 26662 B, 4731 ms
  - FAILED Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (fa3f37ad7b85b1cb): resource:States; N 10183, cand 6170, raw 60521 B, 1792 ms
  - FAILED UpperHalfPlane.σ_mul_comm (faa2c19f0849cb5c): resource:States; N 553, cand 385, raw 4582 B, 2738 ms
  - FAILED _private.Std.Time.Date.Unit.Month.0.Std.Time.Month.Ordinal.difference_eq.match_1_1 (fb0b602bce49e7da): resource:States; N 1375, cand 613, raw 6421 B, 1734 ms
  - FAILED VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt (fc01df351d858a80): resource:States; N 1083, cand 669, raw 7375 B, 1722 ms
  - FAILED NumberField.InfinitePlace.not_isUnramified_iff (fc28af1bac4b86bf): resource:States; N 870, cand 383, raw 4883 B, 2650 ms
  - FAILED _private.Mathlib.Probability.Distributions.Gaussian.Fernique.0.ProbabilityTheory.IsGaussian.integrable_exp_sq_of_conv_neg._proof_1_8 (fc47a6093d67ae77): resource:States; N 1254, cand 666, raw 8884 B, 2217 ms
  - FAILED List.triplewise_reverse (fd07b3643a377b6d): resource:States; N 559, cand 210, raw 2983 B, 3343 ms
  - FAILED CategoryTheory.Pseudofunctor.DescentData.iso._proof_8 (fedd85b0478390c2): resource:States; N 1006, cand 725, raw 5999 B, 3273 ms
  - FAILED _private.Mathlib.Combinatorics.Extremal.RuzsaSzemeredi.0.mem_triangleIndices (ff5f5f0197adc640): resource:States; N 470, cand 346, raw 3616 B, 2167 ms
- certified constants: stored (heuristic) 1461462148 B; output under Tag4 1143404637 B (-21.76%); under TagN 1131330711 B (-22.59%)
- unshared (where it fits u64, 679157 constants): 214339347746089 B; stored 1461462148 B; Tag4 output 1143404637 B
- Tag4 output - stored per constant: 622989 smaller, 52448 equal, 3720 larger; min -258748 p1 -6128 p10 -949 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- TagN price - stored per constant: min -267397 p1 -6607 p10 -949 p50 -114 p90 -1 p99 0 p99.9 12 max 248
- phase-1 width w: {1: 197682, 2: 479734, 3: 1741}
- uncertain terms per constant: min 0 p1 0 p10 0 p50 6 p90 37 p99 147 p99.9 418 max 5756
- largest component per constant: min 0 p1 0 p10 0 p50 1 p90 4 p99 9 p99.9 15 max 21
- uniform search states per constant: min 0 p1 0 p10 0 p50 21 p90 157 p99 1729 p99.9 47638 max 1046337
- first-tier search states per constant: min 1 p1 1 p10 5 p50 20 p90 127 p99 780 p99.9 2618 max 30126
- R1/R2 candidates per constant (all): min 0 p1 0 p10 6 p50 66 p90 424 p99 2004 p99.9 6392 max 81833
- milliseconds per constant (certified): min 0 p1 0 p10 0 p50 1 p90 5 p99 52 p99.9 473 max 46722
- slowest 10:
  - 51806 ms mfderivWithin_projIcc_one (07c512baeb5f1c75): defn resource:States, N 5218, cand 1580, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 46722 ms CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite (bd34cbe632ec9a56): defn ok, N 95110, cand 81833, k 21461, w 3, uncertain 5756, components 4422 (largest 9), states uniform 35812 first-tier 18449
  - 45285 ms WeierstrassCurve.Projective.map_dblX (bce37c4863c98968): defn resource:States, N 7729, cand 2988, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 42764 ms Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual (1f13644c31ee2c19): defn resource:States, N 44737, cand 35231, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 39439 ms HasMFDerivWithinAt.hcongr_24 (ad63aeb0a1436353): defn resource:States, N 6865, cand 1852, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 32153 ms WeierstrassCurve.Projective.dblX_smul (55c2d089702c5ef0): defn resource:States, N 27252, cand 11090, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 30753 ms WeierstrassCurve.Projective.map_negDblY (eac9493f9c619a72): defn resource:States, N 9567, cand 3594, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 30729 ms addInvariantVectorField_eq_mpullback (c9b66788cffa121e): defn ok, N 5769, cand 1692, k 711, w 2, uncertain 338, components 150 (largest 21), states uniform 668790 first-tier 1050
  - 29808 ms _private.Std.Time.Format.Basic.0.Std.Time.GenericFormat.DateBuilder.mk.injEq (151105c7790e6da0): defn resource:States, N 2657, cand 586, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
  - 29478 ms WeierstrassCurve.Jacobian.negAddY_smul (0c1816c71ee7e564): defn resource:States, N 14839, cand 6369, k 0, w 0, uncertain 0, components 0 (largest 0), states uniform 0 first-tier 0
- total wall 424.0 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --threads 20 --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/mathlib_tiered.csv --select-out /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/mathlib_select.txt"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 7:04.72
	Maximum resident set size (kbytes): 4794008
	Exit status: 0
exit=0
```

</details>

<details><summary>[X1] width experiment, Init, TagN layout (<code>p4/wx_init_tagN.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/../../init.ixe (56622 constants processed); layout TagN; phases 1-3 at w = 1, 2, 3
- wall: processing 43.2 s with 8 threads; peak RSS 487180 KiB
- failures by width: w=1 0, w=2 0, w=3 0; constants with all three ok: 56622
- layout bytes over those constants: K-based 67036818; best of three 66648677 (-388141); stored-count re-solve 66959837 (-76981)
- best-of-three width (ties to the lower w): w=1 45282, w=2 11156, w=3 184
- best of three vs K-based per constant: better 20651, equal 35971; change min -2304 p1 -180 p10 -30 p50 -8 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 7339, equal 48569, worse 714
- total wall 47.5 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/../../init.ixe --layout tagN --threads 8 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx_init_tagN.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:47.61
	Maximum resident set size (kbytes): 485008
	Exit status: 0
```

</details>

<details><summary>[X1] width experiment, Mathlib, TagN layout (<code>p4/wx_ml_tagN.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants processed); layout TagN; phases 1-3 at w = 1, 2, 3
- wall: processing 1094.1 s with 8 threads; peak RSS 4841540 KiB
- failures by width: w=1 0, w=2 0, w=3 0; constants with all three ok: 679499
- layout bytes over those constants: K-based 1136221078; best of three 1121777032 (-14444046); stored-count re-solve 1135433559 (-787519)
- best-of-three width (ties to the lower w): w=1 521916, w=2 156170, w=3 1413
- best of three vs K-based per constant: better 297121, equal 382378; change min -11597 p1 -504 p10 -115 p50 -15 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 64033, equal 600933, worse 14533
- total wall 1277.0 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --layout tagN --threads 8 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx_ml_tagN.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 21:17.93
	Maximum resident set size (kbytes): 4838516
	Exit status: 0
exit=0
```

</details>

<details><summary>[X2] width experiment, Init, Tag4 layout (<code>p4/wx_init_tag4.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants processed); layout Tag4; phases 1-3 at w = 1, 2, 3
- wall: processing 44.8 s with 8 threads; peak RSS 462596 KiB
- failures by width: w=1 0, w=2 0, w=3 0; constants with all three ok: 56622
- layout bytes over those constants: K-based 67747841; best of three 67302328 (-445513); stored-count re-solve 67639163 (-108678)
- best-of-three width (ties to the lower w): w=1 45140, w=2 10981, w=3 501
- best of three vs K-based per constant: better 20985, equal 35637; change min -1893 p1 -312 p10 -33 p50 -9 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 7902, equal 47974, worse 746
- total wall 49.9 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tag4 --threads 8 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx_init_tag4.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:50.00
	Maximum resident set size (kbytes): 460272
	Exit status: 0
exit=0
```

</details>

<details><summary>[X2] width experiment, Mathlib, Tag4 layout (<code>p4/wx_ml_tag4.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants processed); layout Tag4; phases 1-3 at w = 1, 2, 3
- wall: processing 1031.8 s with 8 threads; peak RSS 4853268 KiB
- failures by width: w=1 0, w=2 0, w=3 0; constants with all three ok: 679499
- layout bytes over those constants: K-based 1151220860; best of three 1135614916 (-15605944); stored-count re-solve 1149312205 (-1908655)
- best-of-three width (ties to the lower w): w=1 518096, w=2 157708, w=3 3695
- best of three vs K-based per constant: better 299934, equal 379565; change min -11153 p1 -530 p10 -128 p50 -15 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 73526, equal 591110, worse 14863
- total wall 1175.2 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --layout tag4 --threads 8 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx_ml_tag4.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 19:36.32
	Maximum resident set size (kbytes): 4853268
	Exit status: 0
exit=0
```

</details>

<details><summary>[X3] width experiment, Init, TagN layout, 1 thread (<code>p4/wx_init_tagN_t1.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants processed); layout TagN; phases 1-3 at w = 1, 2, 3
- wall: processing 414.9 s with 1 threads; peak RSS 313624 KiB
- failures by width: w=1 0, w=2 0, w=3 0; constants with all three ok: 56622
- layout bytes over those constants: K-based 67036818; best of three 66648677 (-388141); stored-count re-solve 66959837 (-76981)
- best-of-three width (ties to the lower w): w=1 45282, w=2 11156, w=3 184
- best of three vs K-based per constant: better 20651, equal 35971; change min -2304 p1 -180 p10 -30 p50 -8 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 7339, equal 48569, worse 714
- total wall 419.1 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tagN --threads 1 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx_init_tagN_t1.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 6:59.18
	Maximum resident set size (kbytes): 311764
	Exit status: 0
exit=0
```

</details>

<details><summary>[X4] best of four, Init, TagN layout (<code>p4/wx4_init_tagN.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants processed); layout TagN; phases 1-3 at w = 1, 2, 3
- wall: processing 44.2 s with 8 threads; peak RSS 455020 KiB
- failures by candidate: w=1 0, w=2 0, w=3 0, all 0; constants with all four ok: 56622
- best of four (w = 1, 2, 3, all; ties to the earlier): 66648660 (-17 vs best of three); all candidates stored: 67487013
- best-of-four winner: w=1 45275, w=2 11156, w=3 184, all 7; best of four vs best of three per constant: better 7, equal 56615
- layout bytes over those constants: K-based 67036818; best of three 66648677 (-388141); stored-count re-solve 66959837 (-76981)
- best-of-three width (ties to the lower w): w=1 45282, w=2 11156, w=3 184
- best of three vs K-based per constant: better 20651, equal 35971; change min -2304 p1 -180 p10 -30 p50 -8 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 7339, equal 48569, worse 714
- total wall 47.3 s

	Command being timed: "./target/release/examples/sharing_corpus /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tagN --threads 8 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx4_init_tagN.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:47.33
	Maximum resident set size (kbytes): 451608
	Exit status: 0
exit=0
```

</details>

<details><summary>[X4] best of four, Mathlib, TagN layout (<code>p4/wx4_ml_tagN.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants processed); layout TagN; phases 1-3 at w = 1, 2, 3
- wall: processing 1021.8 s with 12 threads; peak RSS 4873620 KiB
- failures by candidate: w=1 0, w=2 0, w=3 0, all 0; constants with all four ok: 679499
- best of four (w = 1, 2, 3, all; ties to the earlier): 1121774136 (-2896 vs best of three); all candidates stored: 1129388537
- best-of-four winner: w=1 520808, w=2 156147, w=3 1413, all 1131; best of four vs best of three per constant: better 1131, equal 678368
- layout bytes over those constants: K-based 1136221078; best of three 1121777032 (-14444046); stored-count re-solve 1135433559 (-787519)
- best-of-three width (ties to the lower w): w=1 521916, w=2 156170, w=3 1413
- best of three vs K-based per constant: better 297121, equal 382378; change min -11597 p1 -504 p10 -115 p50 -15 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 64033, equal 600933, worse 14533
- total wall 1203.0 s

	Command being timed: "/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/sharing_corpus_wx4 /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --layout tagN --threads 12 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx4_ml_tagN.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 20:05.59
	Maximum resident set size (kbytes): 4873620
	Exit status: 0
exit=0
```

</details>

<details><summary>[X4] best of four, Init, Tag4 layout (<code>p4/wx4_init_tag4.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe (56622 constants processed); layout Tag4; phases 1-3 at w = 1, 2, 3
- wall: processing 57.7 s with 12 threads; peak RSS 540732 KiB
- failures by candidate: w=1 0, w=2 0, w=3 0, all 0; constants with all four ok: 56622
- best of four (w = 1, 2, 3, all; ties to the earlier): 67302313 (-15 vs best of three); all candidates stored: 68443810
- best-of-four winner: w=1 45135, w=2 10981, w=3 501, all 5; best of four vs best of three per constant: better 5, equal 56617
- layout bytes over those constants: K-based 67747841; best of three 67302328 (-445513); stored-count re-solve 67639163 (-108678)
- best-of-three width (ties to the lower w): w=1 45140, w=2 10981, w=3 501
- best of three vs K-based per constant: better 20985, equal 35637; change min -1893 p1 -312 p10 -33 p50 -9 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 7902, equal 47974, worse 746
- total wall 61.3 s

	Command being timed: "/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/sharing_corpus_wx4 /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe --layout tag4 --threads 12 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx4_init_tag4.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:01.37
	Maximum resident set size (kbytes): 538600
	Exit status: 0
exit=0
```

</details>

<details><summary>[X4] best of four, Mathlib, Tag4 layout (<code>p4/wx4_ml_tag4.md</code>)</summary>

```text
# sharing_corpus width experiment (not the canonical construction)
- corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe (679499 constants processed); layout Tag4; phases 1-3 at w = 1, 2, 3
- wall: processing 1141.4 s with 12 threads; peak RSS 5024656 KiB
- failures by candidate: w=1 0, w=2 0, w=3 0, all 0; constants with all four ok: 679499
- best of four (w = 1, 2, 3, all; ties to the earlier): 1135612767 (-2149 vs best of three); all candidates stored: 1146903694
- best-of-four winner: w=1 517124, w=2 157688, w=3 3695, all 992; best of four vs best of three per constant: better 992, equal 678507
- layout bytes over those constants: K-based 1151220860; best of three 1135614916 (-15605944); stored-count re-solve 1149312205 (-1908655)
- best-of-three width (ties to the lower w): w=1 518096, w=2 157708, w=3 3695
- best of three vs K-based per constant: better 299934, equal 379565; change min -11153 p1 -530 p10 -128 p50 -15 p90 -2 p99 -1 p99.9 -1 max -1
- stored-count re-solve vs K-based per constant: better 73526, equal 591110, worse 14863
- total wall 1405.4 s

	Command being timed: "/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/sharing_corpus_wx4 /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe --layout tag4 --threads 12 --width-experiment --csv /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/p4/wx4_ml_tag4.csv"
	Elapsed (wall clock) time (h:mm:ss or m:ss): 23:26.59
	Maximum resident set size (kbytes): 5024656
	Exit status: 0
exit=0
```

</details>

<details><summary>[J1] join output (<code>p4/init_join.txt</code>)</summary>

```text
study rows 56622
joined rooted 55386, rootless 1236 (changed by the construction: 0), not ok in either run 0, study rows missing from runner 0
stored-bytes mismatches study vs runner: 0; unshared mismatches: 0; rooted rows with unvalidated unshared: 7
totals over rooted: heuristic 80161846, MSS(Tag4) 68547873, MSS(TagN price) 67556587, canonical Tag4 67701399, canonical TagN 66990376, TagN construction in Tag4 bytes 67621877, unshared 1069954757
canonical Tag4 vs MSS: smaller 23157 equal 22616 larger 9613; canonical TagN vs MSS(TagN): smaller 23132 equal 22616 larger 9638
canonical Tag4 vs heuristic: smaller 49956 equal 4992 larger 438
Tag4 construction vs TagN construction, both in Tag4 bytes: smaller 372 equal 54148 larger 866
larger than unshared: canonical Tag4 0, canonical TagN 0, MSS 0
canonical Tag4 - heuristic (n=55386): min -67656 p1 -3227 p10 -370 p50 -48 p90 -1 p99 0 p99.9 14 max 70
canonical TagN - heuristic (n=55386): min -72624 p1 -3547 p10 -370 p50 -48 p90 -1 p99 0 p99.9 14 max 70
canonical Tag4 - MSS (n=55386): min -6588 p1 -337 p10 -35 p50 0 p90 5 p99 58 p99.9 339 max 1521
canonical TagN - MSS(TagN price) (n=55386): min -7794 p1 -138 p10 -35 p50 0 p90 5 p99 59 p99.9 387 max 1293
Tag4 construction - TagN construction (Tag4 bytes) (n=55386): min -209 p1 0 p10 0 p50 0 p90 0 p99 33 p99.9 345 max 921
```

</details>

<details><summary>[J1] join output (<code>p4/init_byw.txt</code>)</summary>

```text
w=1  TagN run: 22270 constants, sum(canonical TagN - MSS TagN) -743, larger 0, smaller 700 | Tag4 run: 22270 constants, sum(canonical Tag4 - MSS) -743, larger 0, smaller 700
w=2  TagN run: 33008 constants, sum(canonical TagN - MSS TagN) -464153, larger 9596, smaller 22366 | Tag4 run: 31764 constants, sum(canonical Tag4 - MSS) -367450, larger 9332, smaller 21386
w=3  TagN run: 108 constants, sum(canonical TagN - MSS TagN) -101315, larger 42, smaller 66 | Tag4 run: 1352 constants, sum(canonical Tag4 - MSS) -478281, larger 281, smaller 1071
```

</details>

<details><summary>[J2] join output (<code>p4/ml_join.txt</code>)</summary>

```text
study rows 679499
joined rooted 663254, rootless 16245 (changed by the construction: 0), not ok in either run 0, study rows missing from runner 0
stored-bytes mismatches study vs runner: 0; unshared mismatches: 0; rooted rows with unvalidated unshared: 619
totals over rooted: heuristic 1468281356, MSS(Tag4) 1148195956, MSS(TagN price) 1130381317, canonical Tag4 1150611314, canonical TagN 1135611532, TagN construction in Tag4 bytes 1148028605, unshared 214351801952039
canonical Tag4 vs MSS: smaller 244165 equal 199801 larger 219288; canonical TagN vs MSS(TagN): smaller 242375 equal 199829 larger 221050
canonical Tag4 vs heuristic: smaller 623329 equal 36203 larger 3722
Tag4 construction vs TagN construction, both in Tag4 bytes: smaller 4258 equal 641798 larger 17198
larger than unshared: canonical Tag4 0, canonical TagN 0, MSS 26
canonical Tag4 - heuristic (n=663254): min -258748 p1 -6156 p10 -977 p50 -120 p90 -4 p99 0 p99.9 12 max 248
canonical TagN - heuristic (n=663254): min -267397 p1 -6770 p10 -979 p50 -120 p90 -4 p99 0 p99.9 12 max 248
canonical Tag4 - MSS (n=663254): min -22505 p1 -176 p10 -21 p50 0 p90 39 p99 261 p99.9 648 max 9103
canonical TagN - MSS(TagN price) (n=663254): min -16508 p1 -98 p10 -20 p50 0 p90 40 p99 277 p99.9 752 max 10505
Tag4 construction - TagN construction (Tag4 bytes) (n=663254): min -1055 p1 0 p10 0 p50 0 p90 0 p99 164 p99.9 497 max 2130
```

</details>

<details><summary>[J2] join output (<code>p4/ml_byw.txt</code>)</summary>

```text
w=1  TagN run: 181437 constants, sum(canonical TagN - MSS TagN) -2905, larger 0, smaller 2745 | Tag4 run: 181437 constants, sum(canonical Tag4 - MSS) -2905, larger 0, smaller 2745
w=2  TagN run: 480001 constants, sum(canonical TagN - MSS TagN) +5841564, larger 220221, smaller 238645 | Tag4 run: 458516 constants, sum(canonical Tag4 - MSS) +3521148, larger 207107, smaller 230317
w=3  TagN run: 1816 constants, sum(canonical TagN - MSS TagN) -608444, larger 829, smaller 985 | Tag4 run: 23301 constants, sum(canonical Tag4 - MSS) -1102885, larger 12181, smaller 11103
```

</details>

<details><summary>[X1] join output (<code>p4/wx_init_tagN_join.txt</code>)</summary>

```text
rooted constants compared 55386 (incomplete 0, missing from study 0)
totals: MSS(tagN widths) 67556587; K-based 66990376 (-566211 vs MSS); best of three 66602235 (-954352 vs MSS, -388141 vs K-based); re-solve 66913395 (-643192 vs MSS, -76981 vs K-based)
fixed widths: all w=1 66771574 (-785013 vs MSS); all w=2 67050223 (-506364); all w=3 67791486 (+234899)
best-of-three width wins (rooted): w=1 44046, w=2 11156, w=3 184
vs MSS per constant: K-based smaller 23132 equal 22616 larger 9638; best of three smaller 32236 equal 23145 larger 5; re-solve smaller 27370 equal 23365 larger 4651
best of three - MSS (n=55386): min -7794 p1 -150 p10 -41 p50 -3 p90 0 p99 0 p99.9 0 max 6
K-based - MSS (n=55386): min -7794 p1 -138 p10 -35 p50 0 p90 5 p99 59 p99.9 387 max 1293
re-solve - MSS (n=55386): min -7794 p1 -140 p10 -35 p50 0 p90 0 p99 57 p99.9 300 max 1272
  loss +6: "_private.Init.Data.Iterators.Combinators.Monadic.FilterMap.0.Std.Iterators.Types.FilterMap.instFinitenessRelation._proof_2" (K 241, K-based w 2, best w 1, stored at best 212, MSS 6035)
  loss +4: "instLawfulMonadAttachStateTOfLawfulMonad" (K 178, K-based w 2, best w 1, stored at best 149, MSS 3843)
  loss +3: "_private.Init.Data.Iterators.Combinators.Monadic.ULift.0.Std.Iterators.Types.ULiftIterator.instFinitenessRelation._proof_2" (K 246, K-based w 2, best w 1, stored at best 230, MSS 5529)
  loss +1: "Std.IterM.length_uLift" (K 856, K-based w 2, best w 1, stored at best 737, MSS 14680)
  loss +1: "Std.Iter.all_filterMap" (K 324, K-based w 2, best w 1, stored at best 299, MSS 7167)
  loss +0: "UInt16.zero_lt_one" (K 6, K-based w 1, best w 1, stored at best 4, MSS 477)
  loss +0: "EST.bind" (K 7, K-based w 1, best w 1, stored at best 4, MSS 267)
  loss +0: "Std.Iterators.PostconditionT.ctorIdx" (K 2, K-based w 1, best w 1, stored at best 2, MSS 136)
  loss +0: "Int32.toBitVec_div" (K 5, K-based w 1, best w 1, stored at best 5, MSS 496)
  loss +0: "Vector.find?_mk" (K 7, K-based w 1, best w 1, stored at best 7, MSS 412)
```

</details>

<details><summary>[X1] join output (<code>p4/wx_init_tagN_best.txt</code>)</summary>

```text
all constants 56622 (no best 0): best of three 66648677 vs stored 80208288 (-16.91%)
rootless 1236 (changed 0)
rooted 55386: heuristic 80161846, MSS(tagN widths) 67556587, best of three 66602235 (-16.92% vs heuristic, -954352 = -1.41% vs MSS), unshared 1069954757
vs heuristic: smaller 50406 equal 4933 larger 47; vs MSS: smaller 32236 equal 23145 larger 5; larger than unshared 0
best of three - heuristic (n=55386): min -74928 p1 -3566 p10 -383 p50 -51 p90 -1 p99 0 p99.9 0 max 7
best of three - MSS (n=55386): min -7794 p1 -150 p10 -41 p50 -3 p90 0 p99 0 p99.9 0 max 6
```

</details>

<details><summary>[X1] join output (<code>p4/wx_ml_tagN_join.txt</code>)</summary>

```text
rooted constants compared 663254 (incomplete 0, missing from study 0)
totals: MSS(tagN widths) 1130381317; K-based 1135611532 (+5230215 vs MSS); best of three 1121167486 (-9213831 vs MSS, -14444046 vs K-based); re-solve 1134824013 (+4442696 vs MSS, -787519 vs K-based)
fixed widths: all w=1 1122848598 (-7532719 vs MSS); all w=2 1135414511 (+5033194); all w=3 1151346211 (+20964894)
best-of-three width wins (rooted): w=1 505671, w=2 156170, w=3 1413
vs MSS per constant: K-based smaller 242375 equal 199829 larger 221050; best of three smaller 405832 equal 256519 larger 903; re-solve smaller 263473 equal 225637 larger 174144
best of three - MSS (n=663254): min -16508 p1 -118 p10 -30 p50 -3 p90 0 p99 0 p99.9 1 max 1485
K-based - MSS (n=663254): min -16508 p1 -98 p10 -20 p50 0 p90 40 p99 277 p99.9 752 max 10505
re-solve - MSS (n=663254): min -16508 p1 -100 p10 -21 p50 0 p90 40 p99 272 p99.9 690 max 10505
  loss +1485: "Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq" (K 2230, K-based w 3, best w 2, stored at best 1895, MSS 63779)
  loss +37: "equalizerCondition_yonedaPresheaf" (K 894, K-based w 2, best w 1, stored at best 769, MSS 14205)
  loss +32: "SheafOfModules.Presentation.mk.injEq" (K 553, K-based w 2, best w 1, stored at best 505, MSS 9442)
  loss +29: "SheafOfModules.relationsOfIsCokernelFree._proof_2" (K 822, K-based w 2, best w 1, stored at best 739, MSS 15365)
  loss +26: "Algebra.Extension.CotangentSpace.map_comp" (K 1457, K-based w 3, best w 1, stored at best 1429, MSS 32918)
  loss +25: "SheafOfModules.Presentation.mk.inj" (K 487, K-based w 2, best w 1, stored at best 448, MSS 8555)
  loss +23: "SheafOfModules.Presentation.noConfusionType" (K 351, K-based w 2, best w 1, stored at best 326, MSS 7734)
  loss +21: "AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty" (K 949, K-based w 2, best w 1, stored at best 882, MSS 17143)
  loss +20: "CategoryTheory.MonoidalCategory.externalProductFlip._proof_8" (K 340, K-based w 2, best w 1, stored at best 303, MSS 5626)
  loss +18: "Std.DTreeMap.Internal.Impl.link2.fun_cases" (K 241, K-based w 2, best w 1, stored at best 201, MSS 5711)
```

</details>

<details><summary>[X1] join output (<code>p4/wx_ml_tagN_best.txt</code>)</summary>

```text
all constants 679499 (no best 0): best of three 1121777032 vs stored 1468890902 (-23.63%)
rootless 16245 (changed 0)
rooted 663254: heuristic 1468281356, MSS(tagN widths) 1130381317, best of three 1121167486 (-23.64% vs heuristic, -9213831 = -0.82% vs MSS), unshared 214351801952039
vs heuristic: smaller 627129 equal 35622 larger 503; vs MSS: smaller 405832 equal 256519 larger 903; larger than unshared 0
best of three - heuristic (n=663254): min -270911 p1 -7015 p10 -1031 p50 -125 p90 -4 p99 0 p99.9 0 max 36
best of three - MSS (n=663254): min -16508 p1 -118 p10 -30 p50 -3 p90 0 p99 0 p99.9 1 max 1485
```

</details>

<details><summary>[X1] join output (<code>p4/wx_ml_tagN_slowest.txt</code>)</summary>

```text
163721 ms total | "CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite" | N 95110 | cand 81833 | K 21461 | K-based w 3 | best w 2 | stored w1/w2/w3 18653/18877/18440 | ms w1/w2/w3 74674/44791/44256
84389 ms total | "WeierstrassCurve.variableChange_Δ" | N 63501 | cand 18995 | K 9233 | K-based w 3 | best w 3 | stored w1/w2/w3 8259/8564/8525 | ms w1/w2/w3 21488/27008/35893
77150 ms total | "CategoryTheory.Bicategory.mateEquiv_vcomp" | N 50497 | cand 32338 | K 8940 | K-based w 3 | best w 2 | stored w1/w2/w3 6947/7533/7367 | ms w1/w2/w3 32773/23864/20512
68373 ms total | "Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux" | N 64047 | cand 41872 | K 8745 | K-based w 3 | best w 1 | stored w1/w2/w3 7165/7335/7006 | ms w1/w2/w3 13860/22620/31893
52355 ms total | "AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective" | N 66025 | cand 52066 | K 10555 | K-based w 3 | best w 3 | stored w1/w2/w3 8980/9284/8981 | ms w1/w2/w3 9839/22778/19738
49194 ms total | "Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual" | N 78913 | cand 59202 | K 13054 | K-based w 3 | best w 1 | stored w1/w2/w3 10696/11065/10482 | ms w1/w2/w3 15014/17136/17043
37653 ms total | "_private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.0.WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three" | N 50027 | cand 26233 | K 10413 | K-based w 3 | best w 3 | stored w1/w2/w3 8545/8943/8673 | ms w1/w2/w3 10723/14022/12908
37075 ms total | "_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1" | N 70414 | cand 61641 | K 11700 | K-based w 3 | best w 3 | stored w1/w2/w3 9464/10262/10024 | ms w1/w2/w3 11838/12668/12569
37029 ms total | "WeierstrassCurve.isHomogeneous_addSubMapCoeff" | N 60092 | cand 31902 | K 10150 | K-based w 3 | best w 2 | stored w1/w2/w3 7846/8152/8031 | ms w1/w2/w3 6283/13954/16792
33626 ms total | "WeierstrassCurve.Affine.addPolynomial_slope" | N 35899 | cand 20245 | K 5956 | K-based w 3 | best w 3 | stored w1/w2/w3 5150/5361/5253 | ms w1/w2/w3 8689/11987/12951
```

</details>

<details><summary>[X2] join output (<code>p4/wx_init_tag4_join.txt</code>)</summary>

```text
rooted constants compared 55386 (incomplete 0, missing from study 0)
totals: MSS(tag4 widths) 68547873; K-based 67701399 (-846474 vs MSS); best of three 67255886 (-1291987 vs MSS, -445513 vs K-based); re-solve 67592721 (-955152 vs MSS, -108678 vs K-based)
fixed widths: all w=1 67528222 (-1019651 vs MSS); all w=2 67694849 (-853024); all w=3 68358800 (-189073)
best-of-three width wins (rooted): w=1 43904, w=2 10981, w=3 501
vs MSS per constant: K-based smaller 23157 equal 22616 larger 9613; best of three smaller 32239 equal 23144 larger 3; re-solve smaller 27474 equal 23365 larger 4547
best of three - MSS (n=55386): min -6588 p1 -437 p10 -42 p50 -3 p90 0 p99 0 p99.9 0 max 6
K-based - MSS (n=55386): min -6588 p1 -337 p10 -35 p50 0 p90 5 p99 58 p99.9 339 max 1521
re-solve - MSS (n=55386): min -6588 p1 -360 p10 -36 p50 0 p90 0 p99 51 p99.9 313 max 1521
  loss +6: "_private.Init.Data.Iterators.Combinators.Monadic.FilterMap.0.Std.Iterators.Types.FilterMap.instFinitenessRelation._proof_2" (K 241, K-based w 2, best w 1, stored at best 212, MSS 6035)
  loss +4: "instLawfulMonadAttachStateTOfLawfulMonad" (K 178, K-based w 2, best w 1, stored at best 149, MSS 3843)
  loss +3: "_private.Init.Data.Iterators.Combinators.Monadic.ULift.0.Std.Iterators.Types.ULiftIterator.instFinitenessRelation._proof_2" (K 246, K-based w 2, best w 1, stored at best 230, MSS 5529)
  loss +0: "UInt16.zero_lt_one" (K 6, K-based w 1, best w 1, stored at best 4, MSS 477)
  loss +0: "EST.bind" (K 7, K-based w 1, best w 1, stored at best 4, MSS 267)
  loss +0: "Std.Iterators.PostconditionT.ctorIdx" (K 2, K-based w 1, best w 1, stored at best 2, MSS 136)
  loss +0: "Int32.toBitVec_div" (K 5, K-based w 1, best w 1, stored at best 5, MSS 496)
  loss +0: "Vector.find?_mk" (K 7, K-based w 1, best w 1, stored at best 7, MSS 412)
  loss +0: "Int16.toInt.eq_1" (K 3, K-based w 1, best w 1, stored at best 1, MSS 405)
  loss +0: "UInt64.toBitVec_ofNatTruncate_of_le" (K 7, K-based w 1, best w 1, stored at best 4, MSS 672)
```

</details>

<details><summary>[X2] join output (<code>p4/wx_init_tag4_best.txt</code>)</summary>

```text
all constants 56622 (no best 0): best of three 67302328 vs stored 80208288 (-16.09%)
rootless 1236 (changed 0)
rooted 55386: heuristic 80161846, MSS(tag4 widths) 68547873, best of three 67255886 (-16.10% vs heuristic, -1291987 = -1.88% vs MSS), unshared 1069954757
vs heuristic: smaller 50406 equal 4933 larger 47; vs MSS: smaller 32239 equal 23144 larger 3; larger than unshared 0
best of three - heuristic (n=55386): min -69549 p1 -3313 p10 -383 p50 -51 p90 -1 p99 0 p99.9 0 max 7
best of three - MSS (n=55386): min -6588 p1 -437 p10 -42 p50 -3 p90 0 p99 0 p99.9 0 max 6
```

</details>

<details><summary>[X2] join output (<code>p4/wx_ml_tag4_join.txt</code>)</summary>

```text
rooted constants compared 663254 (incomplete 0, missing from study 0)
totals: MSS(tag4 widths) 1148195956; K-based 1150611314 (+2415358 vs MSS); best of three 1135005370 (-13190586 vs MSS, -15605944 vs K-based); re-solve 1148702659 (+506703 vs MSS, -1908655 vs K-based)
fixed widths: all w=1 1138024409 (-10171547 vs MSS); all w=2 1148160385 (-35571); all w=3 1161814219 (+13618263)
best-of-three width wins (rooted): w=1 501851, w=2 157708, w=3 3695
vs MSS per constant: K-based smaller 244165 equal 199801 larger 219288; best of three smaller 405933 equal 256460 larger 861; re-solve smaller 267981 equal 225610 larger 169663
best of three - MSS (n=663254): min -22505 p1 -361 p10 -31 p50 -3 p90 0 p99 0 p99.9 1 max 266
K-based - MSS (n=663254): min -22505 p1 -176 p10 -21 p50 0 p90 39 p99 261 p99.9 648 max 9103
re-solve - MSS (n=663254): min -22505 p1 -228 p10 -22 p50 0 p90 37 p99 228 p99.9 630 max 9103
  loss +266: "Algebra.Extension.Cotangent.map_toInfinitesimal_bijective" (K 730, K-based w 3, best w 1, stored at best 691, MSS 16350)
  loss +156: "Module.isBaseChange_map_of_finite_free" (K 1186, K-based w 3, best w 1, stored at best 1148, MSS 31826)
  loss +135: "VectorField.DifferentiableWithinAt.pullbackWithin" (K 801, K-based w 3, best w 1, stored at best 785, MSS 21101)
  loss +129: "LinearEquiv.image_closure_of_convex'" (K 491, K-based w 3, best w 1, stored at best 463, MSS 12052)
  loss +125: "IsBaseChange.end" (K 446, K-based w 3, best w 1, stored at best 432, MSS 12782)
  loss +123: "_private.Mathlib.RingTheory.Kaehler.JacobiZariski.0.Algebra.Generators.H1Cotangent.auxMemKer" (K 583, K-based w 3, best w 1, stored at best 573, MSS 15469)
  loss +113: "TensorProduct.adjoint_map" (K 463, K-based w 3, best w 1, stored at best 452, MSS 11188)
  loss +109: "RingHom.Flat.tensorProductMap" (K 512, K-based w 3, best w 3, stored at best 338, MSS 12609)
  loss +100: "LinearMap.tensorEqLocusEquiv._proof_3" (K 390, K-based w 3, best w 1, stored at best 385, MSS 11107)
  loss +98: "instOrderIsoClassContinuousLinearMapIdOfNonUnitalAlgEquivClassOfStarHomClassOfContinuousMapClass" (K 520, K-based w 3, best w 1, stored at best 517, MSS 12475)
```

</details>

<details><summary>[X2] join output (<code>p4/wx_ml_tag4_best.txt</code>)</summary>

```text
all constants 679499 (no best 0): best of three 1135614916 vs stored 1468890902 (-22.69%)
rootless 16245 (changed 0)
rooted 663254: heuristic 1468281356, MSS(tag4 widths) 1148195956, best of three 1135005370 (-22.70% vs heuristic, -13190586 = -1.15% vs MSS), unshared 214351801952039
vs heuristic: smaller 627129 equal 35622 larger 503; vs MSS: smaller 405933 equal 256460 larger 861; larger than unshared 0
best of three - heuristic (n=663254): min -262502 p1 -6433 p10 -1031 p50 -125 p90 -4 p99 0 p99.9 0 max 36
best of three - MSS (n=663254): min -22505 p1 -361 p10 -31 p50 -3 p90 0 p99 0 p99.9 1 max 266
```

</details>

<details><summary>[X3] join output (<code>p4/wx_init_tagN_t1_slowest.txt</code>)</summary>

```text
8801 ms total | "_private.Init.Data.Vector.Extract.0.Vector.extract_append._proof_1" | N 26943 | cand 19283 | K 5136 | K-based w 3 | best w 2 | stored w1/w2/w3 4280/4474/4427 | ms w1/w2/w3 2847/2923/3031
8644 ms total | "_private.Init.Data.Array.Extract.0.Array.extract_append._proof_1_1" | N 26754 | cand 19091 | K 5146 | K-based w 3 | best w 2 | stored w1/w2/w3 4247/4454/4403 | ms w1/w2/w3 2901/2828/2915
8028 ms total | "_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList" | N 27628 | cand 22458 | K 4874 | K-based w 3 | best w 2 | stored w1/w2/w3 4076/4067/3785 | ms w1/w2/w3 2654/2806/2569
6252 ms total | "_private.Init.Data.Array.Extract.0.Array.extract_append_extract._proof_1_1" | N 24507 | cand 17140 | K 4678 | K-based w 3 | best w 3 | stored w1/w2/w3 3939/4107/4059 | ms w1/w2/w3 1980/2267/2005
5975 ms total | "Lean.Grind.Config.mk.injEq" | N 3512 | cand 551 | K 360 | K-based w 2 | best w 1 | stored w1/w2/w3 281/192/187 | ms w1/w2/w3 4450/873/652
5167 ms total | "_private.Init.Data.Vector.Extract.0.Vector.extract_append_extract._proof_1" | N 24658 | cand 17290 | K 4703 | K-based w 3 | best w 3 | stored w1/w2/w3 3981/4143/4097 | ms w1/w2/w3 1616/1719/1831
5165 ms total | "_private.Init.Data.Vector.Extract.0.Vector.extract_extract._proof_1" | N 26494 | cand 19017 | K 4919 | K-based w 3 | best w 3 | stored w1/w2/w3 4127/4303/4279 | ms w1/w2/w3 1375/1644/2146
4215 ms total | "_private.Init.Data.Array.Extract.0.Array.extract_extract._proof_1_1" | N 19523 | cand 11454 | K 3640 | K-based w 3 | best w 3 | stored w1/w2/w3 3108/3135/3121 | ms w1/w2/w3 1420/1363/1432
2631 ms total | "_private.Init.Data.Int.DivMod.Lemmas.0.Int.add_one_tdiv._proof_1_1" | N 18802 | cand 13281 | K 3236 | K-based w 3 | best w 3 | stored w1/w2/w3 2782/2793/2740 | ms w1/w2/w3 740/782/1109
2469 ms total | "_private.Init.Data.Vector.Extract.0.Vector.extract_add_left._proof_1" | N 14521 | cand 8259 | K 2854 | K-based w 3 | best w 3 | stored w1/w2/w3 2412/2494/2464 | ms w1/w2/w3 830/823/816
```

</details>

<details><summary>[X3] join output (<code>p4/wx_init_tagN_t1_ms.txt</code>)</summary>

```text
best-of-three ms per constant (sum of 3 widths, n=56622): p50 1 p90 10 p99 77 p99.9 570 max 8801
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_init_tagN_join.txt</code>)</summary>

```text
rooted constants compared 55386 (incomplete 0, missing from study 0)
totals: MSS(tagN widths) 67556587; K-based 66990376 (-566211 vs MSS); best of four 66602218 (-954369 vs MSS, -388158 vs K-based); re-solve 66913395 (-643192 vs MSS, -76981 vs K-based)
fixed widths: all w=1 66771574 (-785013 vs MSS); all w=2 67050223 (-506364); all w=3 67791486 (+234899)
best of four winner (rooted): w=1 44039, w=2 11156, w=3 184, all 7
vs MSS per constant: K-based smaller 23132 equal 22616 larger 9638; best of four smaller 32237 equal 23149 larger 0; re-solve smaller 27370 equal 23365 larger 4651
best of four - MSS (n=55386): min -7794 p1 -150 p10 -41 p50 -3 p90 0 p99 0 p99.9 0 max 0
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_init_tagN_best.txt</code>)</summary>

```text
all constants 56622 (no best 0): best of four 66648660 vs stored 80208288 (-16.91%)
rootless 1236 (changed 0)
rooted 55386: heuristic 80161846, MSS(tagN widths) 67556587, best of four 66602218 (-16.92% vs heuristic, -954369 = -1.41% vs MSS), unshared 1069954757
vs heuristic: smaller 50406 equal 4933 larger 47; vs MSS: smaller 32237 equal 23149 larger 0; larger than unshared 0
best of four - heuristic (n=55386): min -74928 p1 -3566 p10 -383 p50 -51 p90 -1 p99 0 p99.9 0 max 7
best of four - MSS (n=55386): min -7794 p1 -150 p10 -41 p50 -3 p90 0 p99 0 p99.9 0 max 0
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_ml_tagN_join.txt</code>)</summary>

```text
rooted constants compared 663254 (incomplete 0, missing from study 0)
totals: MSS(tagN widths) 1130381317; K-based 1135611532 (+5230215 vs MSS); best of four 1121164590 (-9216727 vs MSS, -14446942 vs K-based); re-solve 1134824013 (+4442696 vs MSS, -787519 vs K-based)
fixed widths: all w=1 1122848598 (-7532719 vs MSS); all w=2 1135414511 (+5033194); all w=3 1151346211 (+20964894)
best of four winner (rooted): w=1 504563, w=2 156147, w=3 1413, all 1131
vs MSS per constant: K-based smaller 242375 equal 199829 larger 221050; best of four smaller 405889 equal 257363 larger 2; re-solve smaller 263473 equal 225637 larger 174144
best of four - MSS (n=663254): min -16508 p1 -118 p10 -30 p50 -3 p90 0 p99 0 p99.9 0 max 1485
K-based - MSS (n=663254): min -16508 p1 -98 p10 -20 p50 0 p90 40 p99 277 p99.9 752 max 10505
re-solve - MSS (n=663254): min -16508 p1 -100 p10 -21 p50 0 p90 40 p99 272 p99.9 690 max 10505
  loss +1485: "Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq" (K 2230, K-based w 3, best w 2, stored at best 1895, MSS 63779)
  loss +26: "Algebra.Extension.CotangentSpace.map_comp" (K 1457, K-based w 3, best w 1, stored at best 1429, MSS 32918)
  loss +0: "UInt16.zero_lt_one" (K 6, K-based w 1, best w 1, stored at best 4, MSS 477)
  loss +0: "Std.DHashMap.Const.forInUncurried" (K 8, K-based w 1, best w 1, stored at best 8, MSS 416)
  loss +0: "Plausible.Configuration.maxSize" (K 1, K-based w 1, best w 1, stored at best 0, MSS 83)
  loss +0: "Std.ExtDHashMap.isSome_getKey?_iff_mem" (K 9, K-based w 2, best w 1, stored at best 9, MSS 648)
  loss +0: "Lean.Meta.LazyDiscrTree.Key.arrow.sizeOf_spec" (K 2, K-based w 1, best w 1, stored at best 2, MSS 363)
  loss +0: "Std.TreeSet.mem_of_mem_union_of_not_mem_left" (K 9, K-based w 2, best w 1, stored at best 9, MSS 502)
  loss +0: "IsRelPrime.mul_dvd" (K 12, K-based w 2, best w 1, stored at best 12, MSS 646)
  loss +0: "BialgHom.copy" (K 27, K-based w 2, best w 1, stored at best 27, MSS 1018)
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_ml_tagN_best.txt</code>)</summary>

```text
all constants 679499 (no best 0): best of four 1121774136 vs stored 1468890902 (-23.63%)
rootless 16245 (changed 0)
rooted 663254: heuristic 1468281356, MSS(tagN widths) 1130381317, best of four 1121164590 (-23.64% vs heuristic, -9216727 = -0.82% vs MSS), unshared 214351801952039
vs heuristic: smaller 627129 equal 35622 larger 503; vs MSS: smaller 405889 equal 257363 larger 2; larger than unshared 0
best of four - heuristic (n=663254): min -270911 p1 -7015 p10 -1031 p50 -125 p90 -4 p99 0 p99.9 0 max 36
best of four - MSS (n=663254): min -16508 p1 -118 p10 -30 p50 -3 p90 0 p99 0 p99.9 0 max 1485
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_init_tag4_join.txt</code>)</summary>

```text
rooted constants compared 55386 (incomplete 0, missing from study 0)
totals: MSS(tag4 widths) 68547873; K-based 67701399 (-846474 vs MSS); best of four 67255871 (-1292002 vs MSS, -445528 vs K-based); re-solve 67592721 (-955152 vs MSS, -108678 vs K-based)
fixed widths: all w=1 67528222 (-1019651 vs MSS); all w=2 67694849 (-853024); all w=3 68358800 (-189073)
best of four winner (rooted): w=1 43899, w=2 10981, w=3 501, all 5
vs MSS per constant: K-based smaller 23157 equal 22616 larger 9613; best of four smaller 32240 equal 23146 larger 0; re-solve smaller 27474 equal 23365 larger 4547
best of four - MSS (n=55386): min -6588 p1 -437 p10 -42 p50 -3 p90 0 p99 0 p99.9 0 max 0
K-based - MSS (n=55386): min -6588 p1 -337 p10 -35 p50 0 p90 5 p99 58 p99.9 339 max 1521
re-solve - MSS (n=55386): min -6588 p1 -360 p10 -36 p50 0 p90 0 p99 51 p99.9 313 max 1521
  loss +0: "UInt16.zero_lt_one" (K 6, K-based w 1, best w 1, stored at best 4, MSS 477)
  loss +0: "EST.bind" (K 7, K-based w 1, best w 1, stored at best 4, MSS 267)
  loss +0: "Std.Iterators.PostconditionT.ctorIdx" (K 2, K-based w 1, best w 1, stored at best 2, MSS 136)
  loss +0: "Int32.toBitVec_div" (K 5, K-based w 1, best w 1, stored at best 5, MSS 496)
  loss +0: "Vector.find?_mk" (K 7, K-based w 1, best w 1, stored at best 7, MSS 412)
  loss +0: "Int16.toInt.eq_1" (K 3, K-based w 1, best w 1, stored at best 1, MSS 405)
  loss +0: "UInt64.toBitVec_ofNatTruncate_of_le" (K 7, K-based w 1, best w 1, stored at best 4, MSS 672)
  loss +0: "Int64.toInt64_toUInt64" (K 2, K-based w 1, best w 1, stored at best 2, MSS 196)
  loss +0: "String.Legacy.Iterator.recOn" (K 3, K-based w 1, best w 1, stored at best 3, MSS 211)
  loss +0: "USize.lt_asymm" (K 3, K-based w 1, best w 1, stored at best 2, MSS 274)
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_init_tag4_best.txt</code>)</summary>

```text
all constants 56622 (no best 0): best of four 67302313 vs stored 80208288 (-16.09%)
rootless 1236 (changed 0)
rooted 55386: heuristic 80161846, MSS(tag4 widths) 68547873, best of four 67255871 (-16.10% vs heuristic, -1292002 = -1.88% vs MSS), unshared 1069954757
vs heuristic: smaller 50406 equal 4933 larger 47; vs MSS: smaller 32240 equal 23146 larger 0; larger than unshared 0
best of four - heuristic (n=55386): min -69549 p1 -3313 p10 -383 p50 -51 p90 -1 p99 0 p99.9 0 max 7
best of four - MSS (n=55386): min -6588 p1 -437 p10 -42 p50 -3 p90 0 p99 0 p99.9 0 max 0
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_ml_tag4_join.txt</code>)</summary>

```text
rooted constants compared 663254 (incomplete 0, missing from study 0)
totals: MSS(tag4 widths) 1148195956; K-based 1150611314 (+2415358 vs MSS); best of four 1135003221 (-13192735 vs MSS, -15608093 vs K-based); re-solve 1148702659 (+506703 vs MSS, -1908655 vs K-based)
fixed widths: all w=1 1138024409 (-10171547 vs MSS); all w=2 1148160385 (-35571); all w=3 1161814219 (+13618263)
best of four winner (rooted): w=1 500879, w=2 157688, w=3 3695, all 992
vs MSS per constant: K-based smaller 244165 equal 199801 larger 219288; best of four smaller 405989 equal 257170 larger 95; re-solve smaller 267981 equal 225610 larger 169663
best of four - MSS (n=663254): min -22505 p1 -361 p10 -31 p50 -3 p90 0 p99 0 p99.9 0 max 266
K-based - MSS (n=663254): min -22505 p1 -176 p10 -21 p50 0 p90 39 p99 261 p99.9 648 max 9103
re-solve - MSS (n=663254): min -22505 p1 -228 p10 -22 p50 0 p90 37 p99 228 p99.9 630 max 9103
  loss +266: "Algebra.Extension.Cotangent.map_toInfinitesimal_bijective" (K 730, K-based w 3, best w 1, stored at best 691, MSS 16350)
  loss +156: "Module.isBaseChange_map_of_finite_free" (K 1186, K-based w 3, best w 1, stored at best 1148, MSS 31826)
  loss +135: "VectorField.DifferentiableWithinAt.pullbackWithin" (K 801, K-based w 3, best w 1, stored at best 785, MSS 21101)
  loss +129: "LinearEquiv.image_closure_of_convex'" (K 491, K-based w 3, best w 1, stored at best 463, MSS 12052)
  loss +125: "IsBaseChange.end" (K 446, K-based w 3, best w 1, stored at best 432, MSS 12782)
  loss +123: "_private.Mathlib.RingTheory.Kaehler.JacobiZariski.0.Algebra.Generators.H1Cotangent.auxMemKer" (K 583, K-based w 3, best w 1, stored at best 573, MSS 15469)
  loss +113: "TensorProduct.adjoint_map" (K 463, K-based w 3, best w 1, stored at best 452, MSS 11188)
  loss +109: "RingHom.Flat.tensorProductMap" (K 512, K-based w 3, best w 3, stored at best 338, MSS 12609)
  loss +100: "LinearMap.tensorEqLocusEquiv._proof_3" (K 390, K-based w 3, best w 1, stored at best 385, MSS 11107)
  loss +98: "instOrderIsoClassContinuousLinearMapIdOfNonUnitalAlgEquivClassOfStarHomClassOfContinuousMapClass" (K 520, K-based w 3, best w 1, stored at best 517, MSS 12475)
```

</details>

<details><summary>[X4] join output (<code>p4/wx4_ml_tag4_best.txt</code>)</summary>

```text
all constants 679499 (no best 0): best of four 1135612767 vs stored 1468890902 (-22.69%)
rootless 16245 (changed 0)
rooted 663254: heuristic 1468281356, MSS(tag4 widths) 1148195956, best of four 1135003221 (-22.70% vs heuristic, -13192735 = -1.15% vs MSS), unshared 214351801952039
vs heuristic: smaller 627129 equal 35622 larger 503; vs MSS: smaller 405989 equal 257170 larger 95; larger than unshared 0
best of four - heuristic (n=663254): min -262502 p1 -6433 p10 -1031 p50 -125 p90 -4 p99 0 p99.9 0 max 36
best of four - MSS (n=663254): min -22505 p1 -361 p10 -31 p50 -3 p90 0 p99 0 p99.9 0 max 266
```

</details>

<details><summary>[X5] join output (<code>p6/cmp_id_report.md</code>)</summary>

```text
# MSS vs all candidates (TagN), 679499 constants (0 failed)
- TagN bytes: MSS 1130616480, all 1129388537 (-1227943)
- per constant: all larger 0, smaller 157438, equal 522061
- Shares: MSS 159110515, all 145331762; share bytes MSS 280097495, all 251311059; stored-term occurrences written inline by all: 13778893 in 239559 constants
- total wall 490.4 s
	Elapsed (wall clock) time (h:mm:ss or m:ss): 9:46.80
	Maximum resident set size (kbytes): 4930696
exit=0
```

</details>

<details><summary>[X5] join output (<code>p6/cmp_blake3_report.md</code>)</summary>

```text
# MSS vs all candidates (TagN), 679499 constants (0 failed)
- TagN bytes: MSS 1130990863, all 1129388537 (-1602326)
- per constant: all larger 206, smaller 166865, equal 512428
- Shares: MSS 159110515, all 145331762; share bytes MSS 280471878, all 251311059; stored-term occurrences written inline by all: 13778893 in 239559 constants
- total wall 374.6 s
	Elapsed (wall clock) time (h:mm:ss or m:ss): 6:15.35
	Maximum resident set size (kbytes): 4948468
exit=0
```

</details>

<details><summary>[X5] join output (<code>p6/outlier_diff2.md</code>)</summary>

```text
- MSS with StructuralId ties: TagN 67367 B, Tag4 72071 B
- MSS with Blake3 ties: TagN 63779 B, Tag4 72195 B
# Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq (048653e65a77d222)
- TagN bytes: MSS 67367, all 67367 (+0); table entries MSS 2230, all 2230; DAG nodes 19417
- entry bodies MSS 28683, all 28683; roots MSS 32421, all 32421
- Shares: MSS 18949 (TagN width 1/2/3/wider: [1101, 10111, 7737, 0]), all 16729 ([1101, 7891, 7737, 0]); stored-term occurrences written inline: MSS 0, all 2220
- all: phase-1 order kept false, first tier [18, 19, 20, 89, 100, 203, 215, 279], w 0
- entries with the same term-level form: 1456 of 2230; entries at a different index: 0
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 23: 108 (m9 a9 deg 108); 31: 104 (m10 a10 deg 104); 26: 94 (m11 a11 deg 94); 17: 83 (m13 a13 deg 83); 39: 82 (m14 a14 deg 82); 15: 79 (m15 a15 deg 79); 25: 75 (m16 a16 deg 75); 21: 72 (m17 a17 deg 72); 16: 62 (m18 a18 deg 62); 24: 60 (m19 a19 deg 60); 22: 57 (m23 a23 deg 57); 47: 55 (m24 a24 deg 55); 94: 47 (m26 a26 deg 47); 126: 42 (m27 a27 deg 42); 32: 38 (m28 a28 deg 38)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +0: term 12 m29 a29 refs 37/0 len 2/2
  - +0: term 13 m30 a30 refs 37/0 len 2/2
  - +0: term 14 m37 a37 refs 31/0 len 2/2
  - +0: term 15 m15 a15 refs 79/0 len 2/2
  - +0: term 16 m18 a18 refs 62/0 len 2/2
  - +0: term 17 m13 a13 refs 83/0 len 2/2
  - +0: term 18 m2 a2 refs 134/134 len 2/2
  - +0: term 19 m1 a1 refs 151/151 len 2/2
  - +0: term 20 m5 a5 refs 124/124 len 2/2
  - +0: term 21 m17 a17 refs 72/0 len 2/2
  - +0: term 22 m23 a23 refs 57/0 len 2/2
  - +0: term 23 m9 a9 refs 108/0 len 2/2
- body length differences: total +0 / 0
- Share bytes (refs x TagN width): MSS 44534, all 40094
- first entry (MSS order) with a different term-level form: term 736, MSS index 70, all index 70, deg 17, refs 17/17
  - first difference at position 4: MSS Some((true, 17)), all Some((false, 17))
  - MSS bytes: 72b824b1b805
  - all bytes: 72b824b1180d

```

</details>

<details><summary>[X5] join output (<code>p6/diff_up7_blake3.md</code>)</summary>

```text
- MSS with StructuralId ties: TagN 67367 B, Tag4 72071 B
- MSS with Blake3 ties: TagN 63779 B, Tag4 72195 B
# Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq (048653e65a77d222)
- TagN bytes: MSS 63779, all 67367 (+3588); table entries MSS 2230, all 2230; DAG nodes 19417
- entry bodies MSS 27958, all 28683; roots MSS 29558, all 32421
- Shares: MSS 18949 (TagN width 1/2/3/wider: [1101, 13699, 4149, 0]), all 16729 ([1101, 7891, 7737, 0]); stored-term occurrences written inline: MSS 0, all 2220
- all: phase-1 order kept false, first tier [18, 19, 20, 89, 100, 203, 215, 279], w 0
- entries with the same term-level form: 1456 of 2230; entries at a different index: 2175
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 23: 108 (m9 a9 deg 108); 31: 104 (m10 a10 deg 104); 26: 94 (m11 a11 deg 94); 17: 83 (m13 a13 deg 83); 39: 82 (m14 a14 deg 82); 15: 79 (m15 a15 deg 79); 25: 75 (m16 a16 deg 75); 21: 72 (m17 a17 deg 72); 16: 62 (m18 a18 deg 62); 24: 60 (m20 a19 deg 60); 22: 57 (m23 a23 deg 57); 47: 55 (m24 a24 deg 55); 94: 47 (m26 a26 deg 47); 126: 42 (m27 a27 deg 42); 32: 38 (m28 a28 deg 38)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +153: term 19100 m2032 a2228 refs 2/2 len 1426/1579
  - +151: term 19094 m2034 a2227 refs 2/2 len 1455/1606
  - +150: term 19088 m2033 a2226 refs 2/2 len 1458/1608
  - +147: term 19039 m2029 a2224 refs 2/2 len 1519/1666
  - +33: term 14001 m2022 a2093 refs 22/22 len 268/301
  - +30: term 14002 m1966 a2095 refs 22/22 len 315/345
  - +21: term 13999 m2020 a2089 refs 22/22 len 312/333
  - +19: term 14000 m925 a2091 refs 22/22 len 262/281
  - +7: term 10191 m825 a1756 refs 22/22 len 39/46
  - +6: term 10187 m902 a2125 refs 22/22 len 24/30
  - +6: term 11061 m2023 a1776 refs 22/22 len 36/42
  - +6: term 11663 m1982 a2076 refs 22/22 len 47/53
- body length differences: total +1397 / -672
- Share bytes (refs x TagN width): MSS 40946, all 40094
- first entry (MSS order) with a different term-level form: term 736, MSS index 70, all index 70, deg 17, refs 17/17
  - first difference at position 4: MSS Some((true, 17)), all Some((false, 17))
  - MSS bytes: 72b820b1b805
  - all bytes: 72b824b1180d

- MSS with StructuralId ties: TagN 162916 B, Tag4 168886 B
- MSS with Blake3 ties: TagN 160431 B, Tag4 167951 B
# sum_eight_sq_mul_sum_eight_sq (0bd4b1175ac1d995)
- TagN bytes: MSS 160431, all 162472 (+2041); table entries MSS 7281, all 7281; DAG nodes 49322
- entry bodies MSS 49920, all 50577; roots MSS 107233, all 108617
- Shares: MSS 55565 (TagN width 1/2/3/wider: [2359, 23866, 29340, 0]), all 53293 ([3089, 18093, 32111, 0]); stored-term occurrences written inline: MSS 0, all 2272
- all: phase-1 order kept false, first tier [10, 52, 142, 146, 300, 447, 468, 509], w 0
- entries with the same term-level form: 7125 of 7281; entries at a different index: 7278
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 11: 295 (m1 a8 deg 295); 12: 295 (m6 a9 deg 295); 13: 295 (m5 a10 deg 295); 14: 295 (m3 a11 deg 295); 15: 295 (m2 a12 deg 295); 16: 295 (m4 a13 deg 295); 17: 294 (m7 a14 deg 294); 19: 125 (m8 a15 deg 125); 147: 38 (m10 a16 deg 38); 20: 21 (m15 a21 deg 21); 18: 10 (m16 a23 deg 10); 145: 6 (m23 a31 deg 6); 26: 3 (m26 a40 deg 3); 122: 3 (m25 a42 deg 3); 92: 2 (m44 a92 deg 2)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +5: term 21183 m3836 a3314 refs 13/13 len 34/39
  - +5: term 21184 m3435 a3140 refs 7/7 len 37/42
  - +4: term 21212 m3433 a3191 refs 13/13 len 36/40
  - +4: term 26293 m6322 a3981 refs 9/9 len 59/63
  - +4: term 26294 m6260 a3984 refs 9/9 len 59/63
  - +4: term 26295 m7232 a3987 refs 9/9 len 59/63
  - +4: term 26296 m6211 a3990 refs 9/9 len 59/63
  - +4: term 26297 m6288 a3993 refs 9/9 len 59/63
  - +4: term 26298 m6044 a3996 refs 9/9 len 59/63
  - +4: term 26299 m6033 a3999 refs 9/9 len 59/63
  - +3: term 655 m154 a1341 refs 6/6 len 9/12
  - +3: term 805 m191 a1925 refs 7/7 len 9/12
- body length differences: total +2161 / -1504
- Share bytes (refs x TagN width): MSS 138111, all 135608
- first entry (MSS order) with a different term-level form: term 294, MSS index 17, all index 24, deg 28, refs 28/28
  - first difference at position 3: MSS Some((true, 19)), all Some((false, 19))
  - MSS bytes: 72211e03b800b808
  - all bytes: 72211e0318111810

- MSS with StructuralId ties: TagN 24055 B, Tag4 26675 B
- MSS with Blake3 ties: TagN 23547 B, Tag4 26729 B
# _private.Init.Data.List.ToArray.0.List.insertIdx_toArray._proof_1_8 (12f7c5d124fdd295)
- TagN bytes: MSS 23547, all 23791 (+244); table entries MSS 1486, all 1486; DAG nodes 6311
- entry bodies MSS 15584, all 15819; roots MSS 4365, all 4374
- Shares: MSS 7445 (TagN width 1/2/3/wider: [298, 5589, 1558, 0]), all 6881 ([562, 4253, 2066, 0]); stored-term occurrences written inline: MSS 0, all 564
- all: phase-1 order kept false, first tier [12, 89, 99, 101, 186, 195, 215, 305], w 0
- entries with the same term-level form: 1142 of 1486; entries at a different index: 1466
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 14: 31 (m4 a9 deg 31); 13: 30 (m5 a11 deg 30); 10: 28 (m6 a12 deg 28); 49: 25 (m7 a14 deg 25); 40: 24 (m8 a16 deg 24); 11: 22 (m9 a17 deg 22); 15: 17 (m18 a18 deg 17); 57: 16 (m23 a20 deg 16); 59: 16 (m22 a21 deg 16); 76: 16 (m20 a22 deg 16); 78: 16 (m21 a23 deg 16); 16: 14 (m25 a24 deg 14); 85: 14 (m24 a25 deg 14); 52: 13 (m26 a26 deg 13); 9: 11 (m31 a31 deg 11)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +31: term 5841 m1239 a1462 refs 2/2 len 186/217
  - +28: term 6036 m1412 a1438 refs 3/3 len 155/183
  - +28: term 6037 m1413 a1469 refs 2/2 len 155/183
  - +28: term 6073 m1472 a1482 refs 2/2 len 168/196
  - +23: term 6040 m1479 a1472 refs 2/2 len 163/186
  - +23: term 6061 m1475 a1475 refs 2/2 len 169/192
  - +22: term 5901 m1340 a1396 refs 3/3 len 157/179
  - +19: term 6135 m1476 a1483 refs 2/2 len 153/172
  - +18: term 5878 m1478 a1466 refs 2/2 len 138/156
  - +14: term 5873 m1329 a1464 refs 2/2 len 118/132
  - +13: term 6098 m1468 a1453 refs 4/4 len 156/169
  - +12: term 5870 m1303 a1417 refs 3/3 len 138/150
- body length differences: total +762 / -527
- Share bytes (refs x TagN width): MSS 16150, all 15266
- first entry (MSS order) with a different term-level form: term 415, MSS index 15, all index 10, deg 34, refs 34/34
  - first difference at position 2: MSS Some((true, 14)), all Some((false, 14))
  - MSS bytes: 71b805b4
  - all bytes: 71b6180d

- MSS with StructuralId ties: TagN 29926 B, Tag4 33101 B
- MSS with Blake3 ties: TagN 28862 B, Tag4 33682 B
# _private.Init.Data.Int.LemmasAux.0.Int.max_min_distrib_left._proof_1_1 (20646855d719ed79)
- TagN bytes: MSS 28862, all 29495 (+633); table entries MSS 1815, all 1815; DAG nodes 8427
- entry bodies MSS 14988, all 15230; roots MSS 11207, all 11598
- Shares: MSS 9731 (TagN width 1/2/3/wider: [433, 6942, 2356, 0]), all 9347 ([864, 5063, 3420, 0]); stored-term occurrences written inline: MSS 0, all 384
- all: phase-1 order kept false, first tier [8, 9, 14, 62, 69, 70, 106, 118], w 0
- entries with the same term-level form: 1538 of 1815; entries at a different index: 1789
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 29: 27 (m5 a8 deg 27); 59: 26 (m6 a9 deg 26); 42: 22 (m11 a11 deg 22); 11: 21 (m13 a13 deg 21); 39: 20 (m15 a14 deg 20); 78: 17 (m17 a16 deg 17); 54: 16 (m19 a18 deg 16); 55: 16 (m18 a19 deg 16); 20: 15 (m20 a20 deg 15); 53: 15 (m21 a21 deg 15); 27: 12 (m24 a24 deg 12); 18: 11 (m25 a25 deg 11); 37: 11 (m26 a26 deg 11); 84: 11 (m27 a27 deg 11); 31: 8 (m30 a28 deg 8)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +23: term 8190 m1799 a1764 refs 3/3 len 374/397
  - +23: term 8245 m1814 a1813 refs 2/2 len 377/400
  - +19: term 8119 m1771 a1809 refs 2/2 len 210/229
  - +19: term 8192 m1806 a1811 refs 2/2 len 378/397
  - +16: term 8123 m1801 a1810 refs 2/2 len 206/222
  - +6: term 8057 m1774 a1808 refs 2/2 len 79/85
  - +5: term 7236 m1600 a1790 refs 2/2 len 47/52
  - +4: term 7237 m1581 a1791 refs 2/2 len 48/52
  - +4: term 7474 m1717 a1792 refs 2/2 len 67/71
  - +4: term 7769 m1465 a1794 refs 2/2 len 75/79
  - +4: term 7874 m1716 a1805 refs 2/2 len 126/130
  - +3: term 7765 m1449 a1793 refs 2/2 len 76/79
- body length differences: total +662 / -420
- Share bytes (refs x TagN width): MSS 21385, all 21250
- first entry (MSS order) with a different term-level form: term 104, MSS index 33, all index 33, deg 7, refs 7/7
  - first difference at position 1: MSS Some((true, 29)), all Some((false, 29))
  - MSS bytes: 71b5b0
  - all bytes: 712018b0

- MSS with StructuralId ties: TagN 37641 B, Tag4 39855 B
- MSS with Blake3 ties: TagN 37065 B, Tag4 39847 B
# _private.Mathlib.CategoryTheory.Sites.Hypercover.One.0.CategoryTheory.PreOneHypercover.sieve₁_inter.match_1_3 (b544e59047529675)
- TagN bytes: MSS 37065, all 37641 (+576); table entries MSS 2271, all 2271; DAG nodes 12584
- entry bodies MSS 31380, all 31920; roots MSS 4384, all 4420
- Shares: MSS 13361 (TagN width 1/2/3/wider: [1019, 8987, 3355, 0]), all 9693 ([1019, 4743, 3931, 0]); stored-term occurrences written inline: MSS 0, all 3668
- all: phase-1 order kept false, first tier [25, 26, 27, 28, 29, 30, 33, 37], w 0
- entries with the same term-level form: 1078 of 2271; entries at a different index: 2213
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 39: 122 (m6 a8 deg 122); 17: 121 (m11 a9 deg 121); 20: 121 (m12 a10 deg 121); 24: 121 (m10 a11 deg 121); 35: 121 (m9 a12 deg 121); 19: 120 (m16 a13 deg 120); 21: 120 (m15 a14 deg 120); 31: 120 (m14 a15 deg 120); 34: 120 (m13 a16 deg 120); 32: 119 (m18 a17 deg 119); 38: 119 (m17 a18 deg 119); 18: 117 (m21 a19 deg 117); 23: 117 (m19 a20 deg 117); 36: 117 (m20 a21 deg 117); 22: 116 (m22 a22 deg 116)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +12: term 11638 m2070 a2231 refs 2/2 len 273/285
  - +12: term 11800 m2221 a2249 refs 2/2 len 105/117
  - +11: term 11789 m2225 a2247 refs 2/2 len 204/215
  - +11: term 11826 m1941 a2260 refs 2/2 len 112/123
  - +10: term 11284 m2191 a2218 refs 2/2 len 73/83
  - +9: term 11785 m2193 a2245 refs 2/2 len 110/119
  - +8: term 11428 m1918 a2224 refs 2/2 len 98/106
  - +8: term 11787 m2077 a2246 refs 2/2 len 112/120
  - +7: term 10930 m1939 a2147 refs 2/2 len 76/83
  - +7: term 11737 m2237 a2237 refs 2/2 len 353/360
  - +7: term 11772 m2218 a2239 refs 2/2 len 108/115
  - +7: term 11774 m2149 a2185 refs 3/3 len 107/114
- body length differences: total +919 / -379
- Share bytes (refs x TagN width): MSS 29058, all 22298
- first entry (MSS order) with a different term-level form: term 3480, MSS index 91, all index 111, deg 6, refs 6/6
  - first difference at position 7: MSS Some((true, 24)), all Some((false, 24))
  - MSS bytes: 74b824b2b4b802b80b
  - all bytes: 74b824b2b318161815

- MSS with StructuralId ties: TagN 27698 B, Tag4 30928 B
- MSS with Blake3 ties: TagN 26940 B, Tag4 31434 B
# _private.Init.Data.Int.LemmasAux.0.Int.min_max_distrib_left._proof_1_1 (ba424920055f512c)
- TagN bytes: MSS 26940, all 27314 (+374); table entries MSS 1716, all 1716; DAG nodes 7820
- entry bodies MSS 16436, all 16706; roots MSS 7837, all 7941
- Shares: MSS 9026 (TagN width 1/2/3/wider: [425, 6476, 2125, 0]), all 8676 ([809, 4984, 2883, 0]); stored-term occurrences written inline: MSS 0, all 350
- all: phase-1 order kept false, first tier [8, 9, 59, 62, 69, 70, 106, 118], w 0
- entries with the same term-level form: 1462 of 1716; entries at a different index: 1690
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 29: 25 (m6 a10 deg 25); 11: 21 (m12 a12 deg 21); 42: 21 (m13 a13 deg 21); 39: 19 (m15 a15 deg 19); 78: 19 (m16 a16 deg 19); 54: 16 (m17 a17 deg 16); 20: 15 (m19 a18 deg 15); 53: 13 (m24 a21 deg 13); 55: 13 (m21 a22 deg 13); 27: 12 (m25 a25 deg 12); 18: 11 (m26 a26 deg 11); 37: 11 (m27 a27 deg 11); 84: 11 (m28 a28 deg 11); 31: 8 (m32 a31 deg 8); 32: 8 (m34 a32 deg 8)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +31: term 7645 m1628 a1714 refs 2/2 len 382/413
  - +30: term 7509 m1686 a1706 refs 2/2 len 271/301
  - +26: term 7510 m1546 a1707 refs 2/2 len 303/329
  - +25: term 7669 m1582 a1715 refs 2/2 len 313/338
  - +23: term 7511 m1592 a1708 refs 2/2 len 284/307
  - +23: term 7528 m1574 a1711 refs 2/2 len 280/303
  - +21: term 7612 m1575 a1712 refs 2/2 len 298/319
  - +21: term 7636 m1581 a1713 refs 2/2 len 317/338
  - +18: term 7512 m1580 a1709 refs 2/2 len 209/227
  - +17: term 7513 m1560 a1710 refs 2/2 len 210/227
  - +16: term 7447 m1590 a1702 refs 2/2 len 137/153
  - +15: term 7271 m1494 a1692 refs 2/2 len 105/120
- body length differences: total +760 / -490
- Share bytes (refs x TagN width): MSS 19752, all 19426
- first entry (MSS order) with a different term-level form: term 104, MSS index 23, all index 23, deg 13, refs 13/13
  - first difference at position 1: MSS Some((true, 29)), all Some((false, 29))
  - MSS bytes: 71b6b0
  - all bytes: 712018b0

- MSS with StructuralId ties: TagN 27064 B, Tag4 30475 B
- MSS with Blake3 ties: TagN 26449 B, Tag4 30809 B
# _private.Init.Data.Int.LemmasAux.0.Int.min_max_distrib_right._proof_1_1 (bda7230c49640697)
- TagN bytes: MSS 26449, all 26954 (+505); table entries MSS 1687, all 1687; DAG nodes 7767
- entry bodies MSS 16756, all 17087; roots MSS 7026, all 7200
- Shares: MSS 8897 (TagN width 1/2/3/wider: [649, 6125, 2123, 0]), all 8540 ([759, 5043, 2738, 0]); stored-term occurrences written inline: MSS 0, all 357
- all: phase-1 order kept false, first tier [8, 9, 29, 62, 69, 70, 106, 117], w 0
- entries with the same term-level form: 1432 of 1687; entries at a different index: 1657
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 59: 26 (m5 a8 deg 26); 11: 21 (m12 a12 deg 21); 39: 20 (m14 a13 deg 20); 42: 20 (m15 a14 deg 20); 78: 19 (m16 a16 deg 19); 54: 16 (m18 a18 deg 16); 20: 15 (m19 a19 deg 15); 84: 15 (m20 a20 deg 15); 53: 14 (m21 a21 deg 14); 55: 13 (m22 a22 deg 13); 27: 12 (m25 a25 deg 12); 18: 8 (m29 a29 deg 8); 31: 8 (m31 a30 deg 8); 32: 8 (m34 a31 deg 8); 37: 8 (m32 a32 deg 8)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +35: term 7546 m1616 a1683 refs 2/2 len 292/327
  - +34: term 7440 m1611 a1675 refs 2/2 len 275/309
  - +32: term 7441 m1615 a1676 refs 2/2 len 300/332
  - +32: term 7459 m1620 a1681 refs 2/2 len 271/303
  - +29: term 7607 m1617 a1686 refs 2/2 len 298/327
  - +27: term 7377 m1296 a1671 refs 2/2 len 179/206
  - +24: term 7376 m1511 a1670 refs 2/2 len 182/206
  - +24: term 7386 m1681 a1672 refs 2/2 len 197/221
  - +21: term 7445 m1490 a1680 refs 2/2 len 205/226
  - +18: term 7476 m1685 a1682 refs 2/2 len 247/265
  - +12: term 7421 m1496 a1673 refs 2/2 len 163/175
  - +11: term 7134 m1393 a1657 refs 2/2 len 61/72
- body length differences: total +807 / -476
- Share bytes (refs x TagN width): MSS 19268, all 19059
- first entry (MSS order) with a different term-level form: term 109, MSS index 33, all index 33, deg 9, refs 9/9
  - first difference at position 1: MSS Some((true, 37)), all Some((false, 37))
  - MSS bytes: 71b81817
  - all bytes: 71202017

```

</details>

<details><summary>[X5] join output (<code>p6/diff_sample13_id.md</code>)</summary>

```text
- MSS with StructuralId ties: TagN 2819 B, Tag4 2819 B
- MSS with Blake3 ties: TagN 2819 B, Tag4 2819 B
# LinearMap.toMatrix₂ (150fea7b7bae8d61)
- TagN bytes: MSS 2819, all 2778 (-41); table entries MSS 75, all 75; DAG nodes 654
- entry bodies MSS 724, all 702; roots MSS 632, all 613
- Shares: MSS 492 (TagN width 1/2/3/wider: [198, 294, 0, 0]), all 403 ([239, 164, 0, 0]); stored-term occurrences written inline: MSS 0, all 89
- all: phase-1 order kept false, first tier [14, 15, 20, 23, 26, 72, 217, 232], w 0
- entries with the same term-level form: 48 of 75; entries at a different index: 9
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 21: 13 (m6 a8 deg 13); 16: 11 (m7 a9 deg 11); 17: 11 (m8 a10 deg 11); 19: 11 (m9 a11 deg 11); 22: 11 (m10 a12 deg 11); 18: 10 (m11 a13 deg 10); 24: 9 (m12 a14 deg 9); 25: 7 (m15 a15 deg 7); 27: 6 (m16 a16 deg 6)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +3: term 321 m42 a42 refs 4/4 len 16/19
  - +1: term 130 m28 a28 refs 2/2 len 5/6
  - +1: term 131 m29 a29 refs 2/2 len 5/6
  - +1: term 172 m18 a18 refs 4/4 len 5/6
  - +1: term 274 m54 a54 refs 2/2 len 10/11
  - +1: term 305 m60 a60 refs 2/2 len 11/12
  - +0: term 14 m2 a2 refs 21/21 len 2/2
  - +0: term 15 m3 a3 refs 21/21 len 2/2
  - +0: term 16 m7 a9 refs 11/0 len 2/2
  - +0: term 17 m8 a10 refs 11/0 len 2/2
  - +0: term 18 m11 a13 refs 10/0 len 2/2
  - +0: term 19 m9 a11 refs 11/0 len 2/2
- body length differences: total +8 / -30
- Share bytes (refs x TagN width): MSS 786, all 567
- first entry (MSS order) with a different term-level form: term 172, MSS index 18, all index 18, deg 4, refs 4/4
  - first difference at position 1: MSS Some((true, 21)), all Some((false, 21))
  - MSS bytes: 9117b6b808
  - all bytes: 9117180f1815

- MSS with StructuralId ties: TagN 775 B, Tag4 775 B
- MSS with Blake3 ties: TagN 775 B, Tag4 775 B
# Pi.seminormedRing._proof_5 (3fdd3d0435a6cd0f)
- TagN bytes: MSS 775, all 766 (-9); table entries MSS 13, all 13; DAG nodes 89
- entry bodies MSS 65, all 63; roots MSS 113, all 106
- Shares: MSS 39 (TagN width 1/2/3/wider: [20, 19, 0, 0]), all 39 ([29, 10, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [8, 10, 11, 12, 26, 27, 39, 40], w 0
- entries with the same term-level form: 13 of 13; entries at a different index: 4
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 57 m11 a11 refs 2/2 len 8/9
  - +0: term 8 m0 a0 refs 3/3 len 2/2
  - +0: term 10 m3 a3 refs 2/2 len 3/3
  - +0: term 11 m4 a4 refs 2/2 len 4/4
  - +0: term 12 m5 a5 refs 2/2 len 3/3
  - +0: term 13 m6 a8 refs 2/2 len 3/3
  - +0: term 25 m7 a9 refs 2/2 len 3/3
  - +0: term 26 m1 a1 refs 3/3 len 3/3
  - +0: term 27 m8 a6 refs 2/2 len 3/3
  - +0: term 32 m10 a10 refs 2/2 len 4/4
  - +0: term 39 m2 a2 refs 4/4 len 4/4
  - -1: term 40 m9 a7 refs 11/11 len 5/4
- body length differences: total +1 / -3
- Share bytes (refs x TagN width): MSS 58, all 49

- MSS with StructuralId ties: TagN 5285 B, Tag4 5285 B
- MSS with Blake3 ties: TagN 5285 B, Tag4 5285 B
# _private.Mathlib.NumberTheory.Bernoulli.0.Bernoulli.sum_pow_add_indicator_eq_zero (41a2b46683027c60)
- TagN bytes: MSS 5285, all 5176 (-109); table entries MSS 181, all 181; DAG nodes 775
- entry bodies MSS 1381, all 1299; roots MSS 566, all 539
- Shares: MSS 645 (TagN width 1/2/3/wider: [73, 572, 0, 0]), all 608 ([182, 426, 0, 0]); stored-term occurrences written inline: MSS 0, all 37
- all: phase-1 order kept false, first tier [24, 83, 103, 105, 155, 156, 157, 246], w 0
- entries with the same term-level form: 163 of 181; entries at a different index: 40
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 42: 5 (m2 a8 deg 5); 109: 5 (m4 a9 deg 5); 8: 3 (m11 a17 deg 3); 20: 3 (m16 a22 deg 3); 27: 3 (m19 a25 deg 3); 71: 3 (m27 a33 deg 3); 90: 3 (m31 a37 deg 3); 93: 3 (m33 a39 deg 3); 108: 3 (m43 a43 deg 3); 6: 2 (m58 a58 deg 2); 14: 2 (m59 a59 deg 2); 29: 2 (m63 a63 deg 2)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +3: term 335 m8 a13 refs 8/8 len 8/11
  - +1: term 269 m51 a51 refs 3/3 len 5/6
  - +1: term 361 m10 a15 refs 5/5 len 11/12
  - +1: term 561 m157 a157 refs 2/2 len 14/15
  - +1: term 619 m168 a168 refs 2/2 len 18/19
  - +1: term 688 m174 a174 refs 2/2 len 18/19
  - +0: term 6 m58 a58 refs 2/0 len 2/2
  - +0: term 8 m11 a17 refs 3/0 len 2/2
  - +0: term 9 m5 a10 refs 4/4 len 3/3
  - +0: term 11 m12 a18 refs 3/3 len 3/3
  - +0: term 12 m13 a19 refs 3/3 len 3/3
  - +0: term 13 m14 a20 refs 3/3 len 3/3
- body length differences: total +8 / -90
- Share bytes (refs x TagN width): MSS 1217, all 1034
- first entry (MSS order) with a different term-level form: term 335, MSS index 8, all index 13, deg 8, refs 8/8
  - first difference at position 5: MSS Some((true, 109)), all Some((false, 109))
  - MSS bytes: 73b7b0b4712054b4
  - all bytes: 73b804b0681d712054681d

- MSS with StructuralId ties: TagN 1443 B, Tag4 1443 B
- MSS with Blake3 ties: TagN 1443 B, Tag4 1443 B
# TensorProduct.comm_comp_comm (47a67d941d274480)
- TagN bytes: MSS 1443, all 1424 (-19); table entries MSS 28, all 28; DAG nodes 309
- entry bodies MSS 327, all 325; roots MSS 226, all 209
- Shares: MSS 146 (TagN width 1/2/3/wider: [74, 72, 0, 0]), all 146 ([93, 53, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [31, 89, 94, 113, 164, 169, 171, 201], w 0
- entries with the same term-level form: 28 of 28; entries at a different index: 9
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +6: term 261 m25 a25 refs 2/2 len 54/60
  - +0: term 26 m14 a14 refs 2/2 len 4/4
  - +0: term 31 m6 a3 refs 3/3 len 3/3
  - +0: term 65 m15 a15 refs 2/2 len 5/5
  - +0: term 66 m16 a16 refs 2/2 len 5/5
  - +0: term 69 m17 a17 refs 2/2 len 5/5
  - +0: term 89 m7 a4 refs 18/18 len 4/4
  - +0: term 94 m9 a6 refs 10/10 len 6/6
  - +0: term 113 m8 a5 refs 15/15 len 11/11
  - +0: term 114 m18 a18 refs 2/2 len 12/12
  - +0: term 115 m19 a19 refs 2/2 len 12/12
  - +0: term 164 m2 a2 refs 13/13 len 15/15
- body length differences: total +6 / -8
- Share bytes (refs x TagN width): MSS 218, all 199

- MSS with StructuralId ties: TagN 1498 B, Tag4 1498 B
- MSS with Blake3 ties: TagN 1498 B, Tag4 1498 B
# PartialEquiv.prod_symm (47be2a47baaa41c6)
- TagN bytes: MSS 1498, all 1483 (-15); table entries MSS 43, all 43; DAG nodes 308
- entry bodies MSS 372, all 359; roots MSS 256, all 254
- Shares: MSS 118 (TagN width 1/2/3/wider: [22, 96, 0, 0]), all 118 ([37, 81, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [12, 54, 55, 56, 134, 135, 136, 137], w 0
- entries with the same term-level form: 43 of 43; entries at a different index: 11
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 220 m18 a18 refs 3/3 len 18/19
  - +1: term 221 m30 a30 refs 3/3 len 10/11
  - +0: term 12 m1 a1 refs 3/3 len 2/2
  - +0: term 28 m4 a10 refs 2/2 len 6/6
  - +0: term 29 m5 a11 refs 2/2 len 6/6
  - +0: term 40 m6 a12 refs 2/2 len 4/4
  - +0: term 54 m0 a0 refs 5/5 len 2/2
  - +0: term 55 m7 a2 refs 2/2 len 4/4
  - +0: term 56 m10 a5 refs 2/2 len 4/4
  - +0: term 63 m13 a13 refs 2/2 len 4/4
  - +0: term 65 m16 a16 refs 2/2 len 4/4
  - +0: term 66 m17 a17 refs 2/2 len 4/4
- body length differences: total +2 / -15
- Share bytes (refs x TagN width): MSS 214, all 199

- MSS with StructuralId ties: TagN 594 B, Tag4 594 B
- MSS with Blake3 ties: TagN 588 B, Tag4 588 B
# Complex.exists (47c8de36ea6414a9)
- TagN bytes: MSS 594, all 585 (-9); table entries MSS 21, all 21; DAG nodes 114
- entry bodies MSS 94, all 92; roots MSS 171, all 164
- Shares: MSS 77 (TagN width 1/2/3/wider: [41, 36, 0, 0]), all 75 ([50, 25, 0, 0]); stored-term occurrences written inline: MSS 0, all 2
- all: phase-1 order kept false, first tier [10, 14, 16, 17, 33, 34, 37, 52], w 0
- entries with the same term-level form: 21 of 21; entries at a different index: 8
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 9: 2 (m4 a9 deg 2)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 27 m13 a13 refs 2/2 len 3/4
  - +1: term 32 m14 a14 refs 2/2 len 3/4
  - +0: term 9 m4 a9 refs 2/0 len 2/2
  - +0: term 10 m1 a1 refs 10/10 len 2/2
  - +0: term 13 m5 a10 refs 2/2 len 3/3
  - +0: term 14 m2 a2 refs 4/4 len 2/2
  - +0: term 15 m6 a11 refs 2/2 len 3/3
  - +0: term 16 m7 a4 refs 2/2 len 3/3
  - +0: term 17 m0 a0 refs 15/15 len 2/2
  - +0: term 19 m12 a12 refs 2/2 len 3/3
  - +0: term 33 m9 a6 refs 4/4 len 3/3
  - +0: term 34 m8 a5 refs 8/8 len 3/3
- body length differences: total +2 / -4
- Share bytes (refs x TagN width): MSS 113, all 100

- MSS with StructuralId ties: TagN 2776 B, Tag4 2776 B
- MSS with Blake3 ties: TagN 2776 B, Tag4 2776 B
# Std.Packages.PreorderOfLEArgs.decidableLT._autoParam (4a870ecdd4f7740a)
- TagN bytes: MSS 2776, all 2713 (-63); table entries MSS 34, all 34; DAG nodes 334
- entry bodies MSS 444, all 412; roots MSS 309, all 278
- Shares: MSS 243 (TagN width 1/2/3/wider: [69, 174, 0, 0]), all 229 ([132, 97, 0, 0]); stored-term occurrences written inline: MSS 0, all 14
- all: phase-1 order kept false, first tier [0, 1, 8, 9, 84, 85, 89, 95], w 0
- entries with the same term-level form: 30 of 34; entries at a different index: 21
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 11: 4 (m2 a12 deg 4); 5: 2 (m7 a17 deg 2); 19: 2 (m13 a18 deg 2); 26: 2 (m14 a19 deg 2); 51: 2 (m15 a20 deg 2); 54: 2 (m16 a21 deg 2)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 96 m23 a23 refs 2/2 len 6/7
  - +1: term 97 m28 a28 refs 2/2 len 5/6
  - +0: term 0 m0 a0 refs 16/16 len 2/2
  - +0: term 1 m1 a1 refs 5/5 len 2/2
  - +0: term 5 m7 a17 refs 2/0 len 2/2
  - +0: term 8 m8 a4 refs 2/2 len 2/2
  - +0: term 9 m4 a2 refs 3/3 len 2/2
  - +0: term 11 m2 a12 refs 4/0 len 2/2
  - +0: term 19 m13 a18 refs 2/0 len 2/2
  - +0: term 26 m14 a19 refs 2/0 len 2/2
  - +0: term 51 m15 a20 refs 2/0 len 2/2
  - +0: term 54 m16 a21 refs 2/0 len 2/2
- body length differences: total +2 / -34
- Share bytes (refs x TagN width): MSS 417, all 326
- first entry (MSS order) with a different term-level form: term 96, MSS index 23, all index 23, deg 2, refs 2/2
  - first difference at position 2: MSS Some((true, 5)), all Some((false, 5))
  - MSS bytes: 72b7582a583d
  - all bytes: 72200e582a583d

- MSS with StructuralId ties: TagN 2895 B, Tag4 2895 B
- MSS with Blake3 ties: TagN 2895 B, Tag4 2895 B
# CategoryTheory.Limits.biprod.braiding._proof_2 (6a9812db4d4daf40)
- TagN bytes: MSS 2895, all 2851 (-44); table entries MSS 151, all 151; DAG nodes 676
- entry bodies MSS 1049, all 997; roots MSS 614, all 622
- Shares: MSS 562 (TagN width 1/2/3/wider: [41, 521, 0, 0]), all 554 ([85, 469, 0, 0]); stored-term occurrences written inline: MSS 0, all 8
- all: phase-1 order kept false, first tier [114, 117, 121, 143, 186, 214, 216, 218], w 0
- entries with the same term-level form: 151 of 151; entries at a different index: 77
- roots with the same term-level form: false
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 40: 4 (m3 a17 deg 4); 44: 4 (m5 a19 deg 4)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 189 m27 a53 refs 3/3 len 4/5
  - +1: term 190 m28 a54 refs 3/3 len 4/5
  - +1: term 191 m29 a55 refs 3/3 len 4/5
  - +1: term 192 m30 a56 refs 3/3 len 4/5
  - +1: term 199 m31 a57 refs 3/3 len 4/5
  - +1: term 200 m32 a58 refs 3/3 len 4/5
  - +1: term 201 m33 a59 refs 3/3 len 4/5
  - +1: term 202 m34 a60 refs 3/3 len 4/5
  - +1: term 301 m104 a104 refs 2/2 len 4/5
  - +1: term 302 m105 a105 refs 2/2 len 4/5
  - +1: term 305 m106 a106 refs 2/2 len 4/5
  - +1: term 306 m107 a107 refs 2/2 len 4/5
- body length differences: total +12 / -64
- Share bytes (refs x TagN width): MSS 1083, all 1023

- MSS with StructuralId ties: TagN 2031 B, Tag4 2031 B
- MSS with Blake3 ties: TagN 2031 B, Tag4 2031 B
# Monoid.Coprod.map._proof_1 (75bca4f10bbf0073)
- TagN bytes: MSS 2031, all 2009 (-22); table entries MSS 63, all 63; DAG nodes 404
- entry bodies MSS 605, all 591; roots MSS 277, all 269
- Shares: MSS 229 (TagN width 1/2/3/wider: [53, 176, 0, 0]), all 226 ([75, 151, 0, 0]); stored-term occurrences written inline: MSS 0, all 3
- all: phase-1 order kept false, first tier [13, 14, 25, 40, 159, 164, 209, 257], w 0
- entries with the same term-level form: 60 of 63; entries at a different index: 10
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 86: 3 (m6 a10 deg 3)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +2: term 355 m59 a59 refs 2/2 len 35/37
  - +1: term 204 m40 a40 refs 2/2 len 14/15
  - +1: term 205 m21 a21 refs 3/3 len 8/9
  - +1: term 235 m45 a45 refs 2/2 len 13/14
  - +1: term 236 m46 a46 refs 2/2 len 13/14
  - +0: term 13 m1 a1 refs 11/11 len 2/2
  - +0: term 14 m0 a0 refs 14/14 len 2/2
  - +0: term 18 m7 a12 refs 2/2 len 4/4
  - +0: term 19 m8 a13 refs 2/2 len 4/4
  - +0: term 25 m9 a4 refs 2/2 len 4/4
  - +0: term 33 m12 a14 refs 2/2 len 5/5
  - +0: term 40 m13 a6 refs 2/2 len 3/3
- body length differences: total +6 / -20
- Share bytes (refs x TagN width): MSS 405, all 377
- first entry (MSS order) with a different term-level form: term 235, MSS index 45, all index 45, deg 2, refs 2/2
  - first difference at position 5: MSS Some((true, 86)), all Some((false, 86))
  - MSS bytes: 7321150e17b67221170e17b809
  - all bytes: 7321150e1768087221170e17b809

- MSS with StructuralId ties: TagN 2008 B, Tag4 2008 B
- MSS with Blake3 ties: TagN 2008 B, Tag4 2008 B
# Polynomial.cyclotomic_prime_mul_X_sub_one (75fb50ca854467f1)
- TagN bytes: MSS 2008, all 1969 (-39); table entries MSS 74, all 74; DAG nodes 277
- entry bodies MSS 518, all 484; roots MSS 198, all 193
- Shares: MSS 218 (TagN width 1/2/3/wider: [31, 187, 0, 0]), all 216 ([70, 146, 0, 0]); stored-term occurrences written inline: MSS 0, all 2
- all: phase-1 order kept false, first tier [7, 12, 17, 18, 74, 75, 83, 84], w 0
- entries with the same term-level form: 72 of 74; entries at a different index: 6
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 48: 2 (m32 a32 deg 2)
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 81 m37 a37 refs 2/2 len 4/5
  - +1: term 210 m69 a69 refs 2/2 len 21/22
  - +0: term 7 m4 a4 refs 2/2 len 3/3
  - +0: term 9 m5 a8 refs 2/2 len 3/3
  - +0: term 12 m0 a0 refs 9/9 len 2/2
  - +0: term 14 m6 a9 refs 2/2 len 3/3
  - +0: term 16 m7 a10 refs 2/2 len 3/3
  - +0: term 17 m1 a1 refs 4/4 len 3/3
  - +0: term 18 m8 a5 refs 2/2 len 3/3
  - +0: term 20 m11 a11 refs 2/2 len 3/3
  - +0: term 26 m12 a12 refs 2/2 len 3/3
  - +0: term 27 m13 a13 refs 2/2 len 3/3
- body length differences: total +2 / -36
- Share bytes (refs x TagN width): MSS 405, all 362
- first entry (MSS order) with a different term-level form: term 141, MSS index 52, all index 52, deg 2, refs 2/2
  - first difference at position 4: MSS Some((true, 48)), all Some((false, 48))
  - MSS bytes: 72b80bb801b818
  - all bytes: 72b80bb6680c

- MSS with StructuralId ties: TagN 1366 B, Tag4 1366 B
- MSS with Blake3 ties: TagN 1352 B, Tag4 1352 B
# CommGrpCat.toAddCommGrp._proof_1 (7610a624ae9ed671)
- TagN bytes: MSS 1366, all 1347 (-19); table entries MSS 32, all 32; DAG nodes 134
- entry bodies MSS 313, all 294; roots MSS 19, all 19
- Shares: MSS 95 (TagN width 1/2/3/wider: [20, 75, 0, 0]), all 95 ([39, 56, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [3, 5, 11, 17, 35, 36, 46, 47], w 0
- entries with the same term-level form: 32 of 32; entries at a different index: 9
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +0: term 3 m0 a0 refs 4/4 len 3/3
  - +0: term 5 m2 a2 refs 2/2 len 3/3
  - +0: term 6 m3 a8 refs 2/2 len 3/3
  - +0: term 7 m4 a9 refs 2/2 len 3/3
  - +0: term 11 m1 a1 refs 4/4 len 3/3
  - +0: term 15 m5 a10 refs 2/2 len 3/3
  - +0: term 16 m6 a11 refs 2/2 len 3/3
  - +0: term 17 m7 a3 refs 2/2 len 3/3
  - +0: term 20 m12 a12 refs 2/2 len 3/3
  - +0: term 22 m13 a13 refs 2/2 len 4/4
  - +0: term 25 m14 a14 refs 2/2 len 4/4
  - +0: term 26 m15 a15 refs 2/2 len 4/4
- body length differences: total +0 / -19
- Share bytes (refs x TagN width): MSS 170, all 151

- MSS with StructuralId ties: TagN 848 B, Tag4 848 B
- MSS with Blake3 ties: TagN 847 B, Tag4 847 B
# SkewMonoidAlgebra.instNonUnitalRing._proof_1 (84f5c3fc061d7f4a)
- TagN bytes: MSS 848, all 838 (-10); table entries MSS 18, all 18; DAG nodes 130
- entry bodies MSS 151, all 140; roots MSS 101, all 102
- Shares: MSS 56 (TagN width 1/2/3/wider: [25, 31, 0, 0]), all 56 ([35, 21, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [10, 12, 26, 27, 51, 54, 76, 79], w 0
- entries with the same term-level form: 18 of 18; entries at a different index: 8
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +0: term 10 m1 a1 refs 4/4 len 3/3
  - +0: term 12 m0 a0 refs 5/5 len 3/3
  - +0: term 15 m4 a8 refs 2/2 len 3/3
  - +0: term 22 m5 a9 refs 2/2 len 4/4
  - +0: term 26 m2 a2 refs 4/4 len 4/4
  - +0: term 27 m3 a3 refs 4/4 len 3/3
  - +0: term 38 m6 a10 refs 2/2 len 5/5
  - +0: term 41 m7 a11 refs 2/2 len 5/5
  - +0: term 51 m8 a4 refs 2/2 len 4/4
  - +0: term 54 m10 a6 refs 2/2 len 4/4
  - +0: term 73 m12 a12 refs 2/2 len 12/12
  - +0: term 94 m14 a14 refs 2/2 len 12/12
- body length differences: total +0 / -11
- Share bytes (refs x TagN width): MSS 87, all 77

- MSS with StructuralId ties: TagN 1294 B, Tag4 1294 B
- MSS with Blake3 ties: TagN 1294 B, Tag4 1294 B
# CategoryTheory.MonoidalOpposite.mopMopEquivalence_counitIso_inv_app (859c756372f27e7c)
- TagN bytes: MSS 1294, all 1271 (-23); table entries MSS 36, all 36; DAG nodes 210
- entry bodies MSS 292, all 277; roots MSS 187, all 179
- Shares: MSS 126 (TagN width 1/2/3/wider: [23, 103, 0, 0]), all 126 ([46, 80, 0, 0]); stored-term occurrences written inline: MSS 0, all 0
- all: phase-1 order kept false, first tier [17, 21, 22, 42, 53, 60, 62, 92], w 0
- entries with the same term-level form: 36 of 36; entries at a different index: 18
- roots with the same term-level form: true
- all: stored terms written inline (term: count, MSS index, all index, deg, unshared-size class), top 15: 
- entries with the largest (all - MSS) body length (term, MSS index, all index, refs MSS/all, length MSS/all):
  - +1: term 57 m21 a21 refs 2/2 len 4/5
  - +1: term 58 m22 a22 refs 2/2 len 4/5
  - +0: term 6 m1 a14 refs 2/2 len 6/6
  - +0: term 8 m2 a15 refs 2/2 len 8/8
  - +0: term 12 m3 a16 refs 2/2 len 4/4
  - +0: term 14 m4 a17 refs 2/2 len 4/4
  - +0: term 17 m5 a0 refs 2/2 len 4/4
  - +0: term 21 m7 a2 refs 2/2 len 3/3
  - +0: term 22 m11 a5 refs 2/2 len 4/4
  - +0: term 24 m18 a18 refs 2/2 len 4/4
  - +0: term 27 m19 a19 refs 2/2 len 6/6
  - +0: term 33 m20 a20 refs 2/2 len 6/6
- body length differences: total +2 / -17
- Share bytes (refs x TagN width): MSS 229, all 206

```

</details>

<details><summary>[X6] join output (<code>p5/outlier_kahn.txt</code>)</summary>

```text
idx,addr,name,kind,raw,k,wk,status1,status2,status3,stored1,stored2,stored3,bytes1,bytes2,bytes3,kbased,best,best_w,rewidth,rewidth_w,ms1,ms2,ms3,status_all,stored_all,bytes_all,best4,best4_w,ms_all,kept1,kept2,kept3,kept_all
0,048653e65a77d222b4f07c2bee4a1b01ae69f1d615ee776d997156626975b878,"Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq",defn,96389,2230,3,ok,ok,ok,1924,1895,1755,65444,65264,65247,65247,65247,3,65247,3,1034.347,1010.188,1015.793,ok,2230,67367,65247,3,1367.599,true,true,false,false
idx,addr,name,kind,raw,k,wk,status1,status2,status3,stored1,stored2,stored3,bytes1,bytes2,bytes3,kbased,best,best_w,rewidth,rewidth_w,ms1,ms2,ms3,status_all,stored_all,bytes_all,best4,best4_w,ms_all
0,048653e65a77d222b4f07c2bee4a1b01ae69f1d615ee776d997156626975b878,"Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq",defn,96389,2230,3,ok,ok,ok,1924,1895,1755,72405,70422,70623,70623,70422,2,70623,3,585.156,579.169,629.983,ok,2230,72065,70422,2,652.159
```

</details>


## Appendix B: differential tallies

For each differential log: the tally lines and the `DIAGNOSIS` lines, unedited. The per-constant `NOTE` lines are omitted.

<details><summary>[D0] Init, the 10 Lean-only constants, limit diagnosis (86df8874)</summary>

`diag_init.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 97 ms, Rust 6 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1533 ms, Rust 250 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 10 under [tiered-tagN, tiered-tag4]; loaded in 1027 ms]
      DIAGNOSIS _private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux (0691b3f1e8c36b6ba49eb789ca815ff0583eb48dc4c46886aadb190fe43be2f6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux (0691b3f1e8c36b6ba49eb789ca815ff0583eb48dc4c46886aadb190fe43be2f6) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb45a13a8fab2095b3f074dceb7bedb7a1a75f47f3ffe5c73b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb45a13a8fab2095b3f074dceb7bedb7a1a75f47f3ffe5c73b) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1 (5a362f9e99724cbf1e4dc40216ab8c45c0629e8394bc419dc3ce03a689ca4173) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1 (5a362f9e99724cbf1e4dc40216ab8c45c0629e8394bc419dc3ce03a689ca4173) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1 (89ed0e98891415751b5d901324eb6eece9183078959dd60430cb17bc64d44d79) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1 (89ed0e98891415751b5d901324eb6eece9183078959dd60430cb17bc64d44d79) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806af97e4b133d9d54fb55d3b46d23e0369d83fdd811284302e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806af97e4b133d9d54fb55d3b46d23e0369d83fdd811284302e6) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1 (b6be5c1a4db8c149c47bd94b0f4acb4231b46ecc62bc2a05cd4be985c5950a74) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1 (b6be5c1a4db8c149c47bd94b0f4acb4231b46ecc62bc2a05cd4be985c5950a74) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1 (d126ef57b21ab268daf3d9cb8faef5455e330eb505556ef14924e8d9cbec2fd9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1 (d126ef57b21ab268daf3d9cb8faef5455e330eb505556ef14924e8d9cbec2fd9) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514063f3b8c9158d9aea80ca6f8be60d1bdcb3c89b6e7a13333) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514063f3b8c9158d9aea80ca6f8be60d1bdcb3c89b6e7a13333) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1 (e852d49c2b3a2ea71d1036e9a19406c99f5db76288c568bceb90e40c939ebfec) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1 (e852d49c2b3a2ea71d1036e9a19406c99f5db76288c568bceb90e40c939ebfec) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1 (eed90987192d51608f220fd7d7ed664c9c87c132401a2e87a4912cc177e4e941) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1 (eed90987192d51608f220fd7d7ed664c9c87c132401a2e87a4912cc177e4e941) [tiered-tag4]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus tiered-tagN: 10 constants; 0 same bytes, 0 same error category, 10 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 63094 ms, Rust 9032 ms]
    [corpus tiered-tag4: 10 constants; 0 same bytes, 0 same error category, 10 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 40504 ms, Rust 8838 ms]
    [corpus: decode failures 0; total 570448 ms]
```

</details>

<details><summary>[D1] Init, all constants, old search, K-based (871eef12)</summary>

`corpus_full.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 169 ms, Rust 8 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1242 ms, Rust 207 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 56622 under [tiered-tagN, tiered-tag4, uniform-w2]; loaded in 647 ms]
    [corpus progress: 5000/56622]
    [corpus progress: 10000/56622]
    [corpus progress: 15000/56622]
    [corpus progress: 20000/56622]
    [corpus progress: 25000/56622]
    [corpus progress: 30000/56622]
    [corpus progress: 35000/56622]
    [corpus progress: 40000/56622]
    [corpus progress: 45000/56622]
    [corpus progress: 50000/56622]
    [corpus progress: 55000/56622]
    [corpus tiered-tagN: 56622 constants; 56587 same bytes, 25 same error category, 10 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1380260 ms, Rust 137091 ms]
    [corpus tiered-tag4: 56622 constants; 56583 same bytes, 29 same error category, 10 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1560208 ms, Rust 146501 ms]
    [corpus uniform-w2: 56622 constants; 56594 same bytes, 28 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1206994 ms, Rust 100361 ms]
    [corpus: decode failures 0; total 4536443 ms]
exit=0 wall=4543s
```

</details>

<details><summary>[D2] Init, all constants, new search, K-based (e4c0dead)</summary>

`init_bb_s0.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 43 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 477 ms, Rust 138 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 629 ms]
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1 (5a362f9e99724cbf1e4dc40216ab8c45c0629e8394bc419dc3ce03a689ca4173) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus progress: 5000/9437]
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1 (89ed0e98891415751b5d901324eb6eece9183078959dd60430cb17bc64d44d79) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806af97e4b133d9d54fb55d3b46d23e0369d83fdd811284302e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1 (eed90987192d51608f220fd7d7ed664c9c87c132401a2e87a4912cc177e4e941) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus tiered-tagN: 9437 constants; 9433 same bytes, 0 same error category, 4 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 91435 ms, Rust 14519 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 30748 ms, Rust 5302 ms]
    [corpus: decode failures 0; total 269562 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 4:31.73
	Maximum resident set size (kbytes): 834904
exit=0
```

`init_bb_s1.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 43 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 474 ms, Rust 137 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 631 ms]
    [corpus progress: 5000/9437]
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1 (d126ef57b21ab268daf3d9cb8faef5455e330eb505556ef14924e8d9cbec2fd9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514063f3b8c9158d9aea80ca6f8be60d1bdcb3c89b6e7a13333) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus tiered-tagN: 9437 constants; 9435 same bytes, 0 same error category, 2 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 76863 ms, Rust 13456 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 27102 ms, Rust 5230 ms]
    [corpus: decode failures 0; total 228840 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 3:51.04
	Maximum resident set size (kbytes): 835116
exit=0
```

`init_bb_s2.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 48 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 526 ms, Rust 141 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 496 ms]
    [corpus progress: 5000/9437]
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1 (b6be5c1a4db8c149c47bd94b0f4acb4231b46ecc62bc2a05cd4be985c5950a74) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus tiered-tagN: 9437 constants; 9436 same bytes, 0 same error category, 1 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 63983 ms, Rust 11723 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 22339 ms, Rust 5141 ms]
    [corpus: decode failures 0; total 144167 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:26.56
	Maximum resident set size (kbytes): 835248
exit=0
```

`init_bb_s3.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 46 ms, Rust 5 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 467 ms, Rust 136 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 496 ms]
    [corpus progress: 5000/9437]
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1 (e852d49c2b3a2ea71d1036e9a19406c99f5db76288c568bceb90e40c939ebfec) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus tiered-tagN: 9437 constants; 9436 same bytes, 0 same error category, 1 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 69022 ms, Rust 11963 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 23348 ms, Rust 4888 ms]
    [corpus: decode failures 0; total 161702 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:43.64
	Maximum resident set size (kbytes): 835172
exit=0
```

`init_bb_s4.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 43 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 391 ms, Rust 111 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 477 ms]
      DIAGNOSIS _private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux (0691b3f1e8c36b6ba49eb789ca815ff0583eb48dc4c46886aadb190fe43be2f6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb45a13a8fab2095b3f074dceb7bedb7a1a75f47f3ffe5c73b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9435 same bytes, 0 same error category, 2 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 67179 ms, Rust 11682 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 24042 ms, Rust 5102 ms]
    [corpus: decode failures 0; total 148137 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:30.23
	Maximum resident set size (kbytes): 834832
exit=0
```

`init_bb_s5.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 42 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 437 ms, Rust 124 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, uniform-w2]; loaded in 446 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 67185 ms, Rust 12046 ms]
    [corpus uniform-w2: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 23557 ms, Rust 5529 ms]
    [corpus: decode failures 0; total 109736 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:52.04
	Maximum resident set size (kbytes): 835176
exit=0
```

</details>

<details><summary>[D3] Mathlib sample, old search, K-based (86df8874)</summary>

`mathlib_diff_a.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 48 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 816 ms, Rust 147 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 10132 under [tiered-tagN, uniform-w2]; loaded in 9837 ms]
      DIAGNOSIS _private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux (0691b3f1e8c36b6ba49eb789ca815ff0583eb48dc4c46886aadb190fe43be2f6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negAddY_neg (14f75d2691415463319f5dfce1f3668d59f07ffde9b7aad7c8b0169f407f22ba) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1 (159e2b0d36d95a7feefe9a1f39b7e65da56802a29e83fe00e567d5b963506ede) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS Std.DTreeMap.Internal.Impl.balanceR!_eq_balance! (1601895625b67ecddc59ecf9425ca6eae4c66d6b7c8ea8ce5e4490c3ea338e86) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb45a13a8fab2095b3f074dceb7bedb7a1a75f47f3ffe5c73b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS TopCat.Sheaf.interUnionPullbackConeLift._proof_5 (1f150c14a61c243d759f462e339b7d824e712ee26eb41419aa9f55b98f0de407) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Localization.existsUnique_algebraMap_eq_of_span_eq_top (23ae320acce50ca3d566210d11ac48d17bf7607df1c356a1a709cdfd12f55d33) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (248b4aa033342acd791b861a9d0f8303a02c7f034e05a26eb8c5f4b087cc7e26) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS ModularForm.discriminant_T_invariant (28d6ee3847c930ae436f8ebc21fa67e03d783d95582be3871bccc5b249d01466) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion_aux (2dacebaef8b139ded3b4019b96c90d19d0e06a845cff61c2e55763b2a70ded07) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Scheme.IsLocallyDirected.glueData._proof_6 (338ca448f75e9c25258b64f2a325fac0899b8f347360454e8ecfe7bf7b72ccf7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_naturality (373b0d8e1af7fe3a1218e5b0f3e7df6c1aa2ad9d2f742ee6460b7f703e0e8e6c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS HomogeneousLocalization.Away.isLocalization_mul (3af1f33ae2a05488ff0ea5dcdd4892be7d1ece5b5190a45cb3f0380b63791e9f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.mateEquiv_hcomp (3cf47cf160e37479d1bdbab6b5706ee09570afc05cb16222ed5e00aac6e6711a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS mem_adjoin_map_integralClosure_of_isStandardEtale (3f383549903f2a37fed9f5d95b0324b680883ee6286b5cfeef222dcdeb91ecc2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk.«0».SzemerediRegularity.edgeDensity_star_not_uniform._proof_1_10 (40e45f2eae83609168fb72486797c8757cf07a130636951cc9b786bc23b56fdc) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.NatTrans.instIsClosedUnderLimitsOfShapeOverFunctorEquifiberedHomOfHasCoproductsOfShapeHom (4b3beb75cfb6da5466c4d9e4e1f23a364c4c16d56ae9be83aa14cbd19a472a47) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Std.Iter.atIdxSlow?_intermediateZip (55d247210280f56e60ab88a44a8cafb7977eb557fd8790c52fec53286049d547) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1 (5a362f9e99724cbf1e4dc40216ab8c45c0629e8394bc419dc3ce03a689ca4173) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.mono_pushoutSection_of_iSup_eq (5e122ca4869d76508a277442ec2a139158921d8628f607367032e3495bffacd5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.«0».WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three (67e377956e9a5e65fa8a97da8775eb1f9fe0ff8f7bc6aed75111cd4b17a34636) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq._unary (68f6e583c732c5f3c079ab3a315711d6b6cba09ffc8dd5b27bf618e251c3d4e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity.«0».ChevalleyThm.PolynomialC.induction_aux (6b75b2b24c2e310aa9ab5110fc9691b4b25818071fcff2019dbc13f2f5390377) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₇_det (6eb6aa5f6e5cc2b4d7606d8d544a3dc26d50e664bb81f852ef3225f88bddc7e4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus progress: 5000/10132]
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1 (89ed0e98891415751b5d901324eb6eece9183078959dd60430cb17bc64d44d79) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.exists_appTop_π_eq_of_isLimit (92454eb0dbd050541a59931f3e202130028143a7c217a88bd98601e4f56d3eb7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS SSet.StrictSegal.isPointwiseRightKanExtensionAt.fac_aux₂ (9fa5347780bca67caeaeb1f8a08ecc9257132be804ea62495a68113699479aba) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806af97e4b133d9d54fb55d3b46d23e0369d83fdd811284302e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (ae6266c2b1b35cb5d6b366f958c6ee2ec5d8e2fd577f6b401d82f59843d22004) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Bicategory.mateEquiv_hcomp (b201fe77a69f2111a0e3d3776b9ddda429506ebc08608e6307f867bcd69843cc) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.addPolynomial_slope (b6a5154a781629bb1beb70715e2f9792a918d9c54f5d5c3d4dfae9d5eeac67e9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback (bc547eefd4fd84f0992166f05140d4bc221cee0bbc84096c4d036a712e197361) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite (bd34cbe632ec9a56a33fd7bb51e23fef8fadb90d7ae3af8216921776ed84bff7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824, maxMaterialize=2147483648]; succeeded with [maxMaterialize=4294967296]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.isSheaf_type_propQCTopology_iff (c1a56567a54a70cbf0999232c590bb896c7544cd7678151801e236cd9ed6be37) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Lax.OplaxTrans.vComp_naturality_comp (c44c23e5d81a327b0388fb796eeb56d5b68a6d00d71ff74d8e3215088e23ab63) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul (c4641901bb3705423856ac01d337794b1d1096a11d0dc76975389aab6a5b1e99) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1 (d126ef57b21ab268daf3d9cb8faef5455e330eb505556ef14924e8d9cbec2fd9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS TopCat.subcanonical_grothendieckTopology (d216753fba4438d45cf79762178e94f4308da7809083d3392b6cdd369d177ea2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS MeasureTheory.VectorMeasure.variation_withDensity' (d5ea2d6fbb4ca2a2dd2a75ef68b1768bb780fbab0c85aab6a97254d2d6709738) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negAddY_eq' (d5ec80e0cce67eb9081abe1075d2940312017829abc9807ceebd32d4222b9b53) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (d86a5b2a6aef9f5659a894d980fde30a535ed86961a806202ad6bc342eeff25c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₆_det (d9660e5a43a0a0fb78097d2a4e562ac8897e887f60abed2bb3f1f3afc70b5f18) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Real.log_five_near_10 (da962aa5afcd9ef1d6f68919543b2a4f56ed97fb113cd9a101f964de681bacd6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Height.mulHeight_sym2_ge (dd9af4585ab3281fd2ae1e46887063a1fcf2d4103b57dff4a7134f89e2d9d159) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₈_det (df85f966e9848e272be9df5ad9e86542a31c5ffd53b2ed63ac8885b9a12ffd64) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq.match_1_1 (dfd42dc5d9b404a98882ab7c615ff22954c63fbbe353aa4ca8ad1d2a1bce1c77) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1 (e852d49c2b3a2ea71d1036e9a19406c99f5db76288c568bceb90e40c939ebfec) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.«0».PeriodPair.iteratedDeriv_six_relation_mul_id_pow_six (ee4f82100489a77cf78a4c542d89541d94630ea17ff1700f3cd242fea32ad3da) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1 (eed90987192d51608f220fd7d7ed664c9c87c132401a2e87a4912cc177e4e941) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus progress: 10000/10132]
      DIAGNOSIS StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv (fdf8644d47f8b068caf56ed87249a924df39afe7abe973d8b458c869639d3c38) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus tiered-tagN: 10132 constants; 10024 same bytes, 58 same error category, 50 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 4526636 ms, Rust 497523 ms]
    [corpus uniform-w2: 10132 constants; 10080 same bytes, 52 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 2634761 ms, Rust 225629 ms]
    [corpus: decode failures 0; total 11295228 ms]
uncaught exception: process 'lean' exited with code 255
	Elapsed (wall clock) time (h:mm:ss or m:ss): 3:08:16
	Maximum resident set size (kbytes): 4723896
exit=1
```

`mathlib_diff_b.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 53 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 839 ms, Rust 141 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 10131 under [tiered-tagN, uniform-w2]; loaded in 9278 ms]
      DIAGNOSIS WeierstrassCurve.variableChange_Δ (0473473f736e639b9211812b686cac21574deb66f2382c1f0cbf4166f7e542c7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (057bc467cdb7583185b00d13e915f514af7be0fb23afc5eb648a60c02bdf766c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS groupCohomology.H1InfRes_exact (076a4a5d72838673c8b1a235fff84767e47060fe8641e355be2c3c68fbf3fd7a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS sum_eight_sq_mul_sum_eight_sq (0bd4b1175ac1d995d92bf0bec451195592d9edf04afe3cee884da42b7b96c766) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go._unary (0f75bea9d5dd4591a6f321934e261404b9a8548358d528223bf692a33527d74b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Jacobian.negAddY_neg (16256043fdb806ecabbd3e043f8f0debf9826eaddc46e79aafb255f469655143) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField (1817bbc31c531206f258dd78757e193fe5357451872bb99278d6b46ff8ff6db3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS MeasureTheory.hasFDerivAt_convolution_right_with_param (221da52233e80ce3a00f6c08e88563b9f5bc6bd5ecf58711be10e25c6a529233) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual (2b0491741df2ce98fdf1d49103d1d62a34c935f682c5afe6ef8c4d84916ce51d) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq (2d33bfe7c13b87fd41641f9f2fa67e9324fdb71f8a8a3bac49eb3212bfead8e3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Proj.valuativeCriterion_existence_aux (36fd5f58fc5f01ac2095417c31694a35783c1c7f13730d9dfa05c2e004757429) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negDblY_eq' (37cd1c7638fa9899f80d12762241905e5858b0abbf3a9380e8efd93299d3edf5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq' (3d79d639858e7cc1e87be66760c72e5602102ed2ae099344d87ddc48d77d7494) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go._unary.eq_def (4382aa4d3e6b329f7c28bd5362cba003121730be4b8d8177db49a74abd26691d) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective (4ece542b15e7b7a1cfeccea61d88b4a5d5aa477eb8d8938135f7458d8e353e45) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal (665f70ff00b204b53d640e57a680266f14339615286866d299612ec5560b770f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Cubic.discr_eq_prod_three_roots (6a0f9ca821efc5daed4ea38e21ec37f894b62251fa54f0557700e7721ab6df02) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS groupHomology.H1CoresCoinf_exact (6cc20762d74eb85e981ae78103c561f0be13b11ae5cf5b02ca1bf76794455b3e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple.«0».RootPairing.GeckConstruction.instIsIrreducible_aux₀ (6d67600cf8c031b8c42fd108bf4361076ff70248e9a91a8bd1105d615ee73777) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus progress: 5000/10131]
      DIAGNOSIS _private.Mathlib.Topology.Order.WithTop.«0».TopologicalSpace.instSecondCountableTopologyWithTop._proof_3 (828b225acbe466836dca7bf72ce2c1125d3b502ccc7f80e80cbe8c0a40e81374) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux (83b417c6e46f08e27487d87f4529f9c7fdfe204a274e99549522d52940a4ea9b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Algebra.Group.Pi.Lemmas.«0».Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle._proof_1_2 (8466008af12aab87e42a21847e9d9e7d8d05f5baf1a65ec4c8e9cfb4e89e6717) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.ofJNe0Or1728_Δ (8a2cd7f10b14aee963dd9e952f040b418dd06fab0a3d6798332c2d8032bc01df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.AlgebraicGeometry.AffineTransitionLimit.«0».AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine (8db8dbcb6033f83c3e6e02db5f18b9efd78d24cfa41a6ad9ca3bb8c6192e6e19) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.instMulActionVariableChange._proof_1 (904073d4c5010184f89d49609e09059722b112294deed7930de71b63ee1fcdd3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Bicategory.mateEquiv_vcomp (9b20bc429f4cd0385f921ace7d460a81141d4121a5549e30aec57ed50d58713e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.addX_eq' (9cbee9afea050a41bf70cc127ecd5f108a3ba9a9eb83491ff815b26b5137fcd6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.IterM.stepAsHetT_filterMapWithPostcondition (a028902ef965f77b66367e310ad367299fa876d6f4d8ce3e15734713f39d16df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.PreOneHypercover.sieve₁_inter (a0c19571a4dbe5924fd473d3f07cc6039e9ec8ea132d3e96917b461db4818ea4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS retractionKerCotangentToTensorEquivSection._proof_20 (a4fb15377dc50d1f640fc355b336a6412f9b0426de9abf20a917a2a7bcad9097) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Lax.LaxTrans.vComp_naturality_comp (a73219dacca75c2ae3dcd1fad1ad17a03f5e43135428591c1faaa999e1afe2c8) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.variableChange_b₈ (a79576d568fe07158efe1f43e0c1c4824746bc891729104c0ff529452c7fefd0) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.Vandermonde.«0».Matrix.det_projVandermonde_of_field (a9268270fdbe2890e45ef573d3b75e238e4b77090bc38d785fe63a5795a7f0c5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS mpullback_mulInvariantVectorField (aff85dc73860760a7a7a1ba22c4fc276f01e30ad2c03a43534af4ab91eedff9a) [tiered-tagN]: Lean exhausted [maxCostEvals=1073741824, maxCostEvals=2147483648]; succeeded with [maxCostEvals=4294967296]; bytes equal to Rust
      DIAGNOSIS mpullback_mulInvariantVectorField (aff85dc73860760a7a7a1ba22c4fc276f01e30ad2c03a43534af4ab91eedff9a) [uniform-w2]: Lean exhausted [maxCostEvals=1073741824, maxCostEvals=2147483648]; succeeded with [maxCostEvals=4294967296]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.GrothendieckTopology.subcanonical_over (b247729636890a6027aa4a09607d23c9b0d13322b26dd823b9917bdb0563cfa4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS String.firstDiffPos_loop_eq._unary (b454ef896ad0240bf720542824f2db566840628d1fdf1ade4c4ed24f0838dea4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1 (b6be5c1a4db8c149c47bd94b0f4acb4231b46ecc62bc2a05cd4be985c5950a74) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.dblX_eq' (b9ee47912f596dbaf2375180a79623b227dc6c78a3b9281ad43b1f17bc30b00a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq._unary (bb5e8c0f8d4e379c065df6dccc7841f1f0cb7bd0094fb2d6e0a92de76a0f117e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Ideal.Quotient.stabilizerHom_surjective_of_profinite (c107a718cbecb1de3b4d28e890a0d00e4dd9966b925c5f0f87b5de29638c2f5c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Limits.colimitLimitToLimitColimit_surjective (c3222710fc60f83889987bc3d9397e478e1be4ed7eb404dae24ee6eb9ca022f9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt (c49eed57b9e8f7e0fa7145697db173f14d07e55aa16c130b61bba170f6a45bc5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare.«0».ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real (ce07522299bbd3b14d8dd4db01257925bb7c8c8c600262df528160fb225daf00) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Oplax.LaxTrans.vComp_naturality_comp (d67fa53ab81509443326e759ad6b054fd61c14f5e66c45eedf963f1388c125df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Mat_.hasFiniteBiproducts (dba35adb0f906c80bfe2f5056330ea0d30871907e8eaf7f3d54b86bd0241d359) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Iter.toList_intermediateZip_of_finite (dbeb56f1bbc5bd7e90258faa26f1632d8eadcf14de0153b8a47f40409242a6b9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514063f3b8c9158d9aea80ca6f8be60d1bdcb3c89b6e7a13333) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Function.Exact.splitInjectiveEquiv._proof_10 (e74bdfa22d2477ae37a67344d30f7301f74dfcc1c1bc01b15c3cff988e34ef55) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS TensorProduct.gradedMul_assoc (ecf0501ad22e32ceb7a4405a89e5a543f835528c1909c5abde71664d0084b3df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.«0».PeriodPair.analyticAt_relation_zero (efb98e985397cccd854391534530ad3c136bdd080e55ceeada910868093d1b8f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.StrictlyUnitaryLaxFunctor.ext (efdbdbe0618ebba20c0e864a40c2457349ce96db59f4d9bfd22c88324170b265) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS mpullback_addInvariantVectorField (f2bb780a290bf9d1d4f6231ba18eb6881b1cec5dc7e875cad8443d5982d94c5e) [tiered-tagN]: Lean exhausted [maxCostEvals=1073741824, maxCostEvals=2147483648]; succeeded with [maxCostEvals=4294967296]; bytes equal to Rust
      DIAGNOSIS mpullback_addInvariantVectorField (f2bb780a290bf9d1d4f6231ba18eb6881b1cec5dc7e875cad8443d5982d94c5e) [uniform-w2]: Lean exhausted [maxCostEvals=1073741824, maxCostEvals=2147483648]; succeeded with [maxCostEvals=4294967296]; bytes equal to Rust
      DIAGNOSIS retractionKerCotangentToTensorEquivSection._proof_19 (f35ae2d9f1e53d362abda6efe67df03aff946fa23efae7a1cb6102587d4cd658) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Algebra.Group.Pi.Lemmas.«0».Pi.single_add_single_eq_single_add_single._proof_1_2 (fa2efaa3a1a2a3ea5e6ae17642bc8127509db2bd2d750a35f3108daebc3106e2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.c_relation (fcc6866343ed8b0e1bd4a9dd85e90352bc9e172dc0366c339212ef2321779068) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
    [corpus progress: 10000/10131]
      DIAGNOSIS Matrix.sub_scalar_sq_eq_discr (fef37ae69f3001716f1c0673091eb70f05feca1386aa35f93f4855c1f85964fe) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus tiered-tagN: 10131 constants; 10032 same bytes, 43 same error category, 56 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 3594984 ms, Rust 427449 ms]
    [corpus uniform-w2: 10131 constants; 10082 same bytes, 47 same error category, 2 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 2244764 ms, Rust 174048 ms]
    [corpus: decode failures 0; total 12193240 ms]
uncaught exception: process 'lean' exited with code 255
	Elapsed (wall clock) time (h:mm:ss or m:ss): 3:23:14
	Maximum resident set size (kbytes): 4729316
exit=1
```

</details>

<details><summary>[D4] Mathlib sample, new search, K-based (e4c0dead)</summary>

`ml_bb_s0.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 42 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 414 ms, Rust 120 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 5065 under [tiered-tagN, uniform-w2]; loaded in 22880 ms]
      DIAGNOSIS WeierstrassCurve.variableChange_Δ (0473473f736e639b9211812b686cac21574deb66f2382c1f0cbf4166f7e542c7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap (057bc467cdb7583185b00d13e915f514af7be0fb23afc5eb648a60c02bdf766c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS sum_eight_sq_mul_sum_eight_sq (0bd4b1175ac1d995d92bf0bec451195592d9edf04afe3cee884da42b7b96c766) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Jacobian.negAddY_smul (0c1816c71ee7e564981d9ed82f49b1ab9d2abc7cd378c8b93782be6ed9628548) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Jacobian.negAddY_neg (16256043fdb806ecabbd3e043f8f0debf9826eaddc46e79aafb255f469655143) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS MeasureTheory.hasFDerivAt_convolution_right_with_param (221da52233e80ce3a00f6c08e88563b9f5bc6bd5ecf58711be10e25c6a529233) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.goCache_Inv_of_Inv._mutual (2b0491741df2ce98fdf1d49103d1d62a34c935f682c5afe6ef8c4d84916ce51d) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Proj.valuativeCriterion_existence_aux (36fd5f58fc5f01ac2095417c31694a35783c1c7f13730d9dfa05c2e004757429) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq' (3d79d639858e7cc1e87be66760c72e5602102ed2ae099344d87ddc48d77d7494) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastCpopLayer.go._unary.eq_def (4382aa4d3e6b329f7c28bd5362cba003121730be4b8d8177db49a74abd26691d) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS QuaternionAlgebra.instRing._proof_1 (55446000b79f451192f9c5f56b6623ed6ad6d17ab703ab2c1a1bc2b24a0cf670) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.GlueData.ofGlueData'._proof_7 (62166e0ed13f509cd8bf4fefa45f240f8a81ee11fadc1528d4a7f3dc5d142cd8) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal (665f70ff00b204b53d640e57a680266f14339615286866d299612ec5560b770f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Cubic.discr_eq_prod_three_roots (6a0f9ca821efc5daed4ea38e21ec37f894b62251fa54f0557700e7721ab6df02) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple.«0».RootPairing.GeckConstruction.instIsIrreducible_aux₀ (6d67600cf8c031b8c42fd108bf4361076ff70248e9a91a8bd1105d615ee73777) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Topology.Order.WithTop.«0».TopologicalSpace.instSecondCountableTopologyWithTop._proof_3 (828b225acbe466836dca7bf72ce2c1125d3b502ccc7f80e80cbe8c0a40e81374) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq_aux (83b417c6e46f08e27487d87f4529f9c7fdfe204a274e99549522d52940a4ea9b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.ofJNe0Or1728_Δ (8a2cd7f10b14aee963dd9e952f040b418dd06fab0a3d6798332c2d8032bc01df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Bicategory.mateEquiv_vcomp (9b20bc429f4cd0385f921ace7d460a81141d4121a5549e30aec57ed50d58713e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.addX_eq' (9cbee9afea050a41bf70cc127ecd5f108a3ba9a9eb83491ff815b26b5137fcd6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.IterM.stepAsHetT_filterMapWithPostcondition (a028902ef965f77b66367e310ad367299fa876d6f4d8ce3e15734713f39d16df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Lax.LaxTrans.vComp_naturality_comp (a73219dacca75c2ae3dcd1fad1ad17a03f5e43135428591c1faaa999e1afe2c8) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.GrothendieckTopology.subcanonical_over (b247729636890a6027aa4a09607d23c9b0d13322b26dd823b9917bdb0563cfa4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS String.firstDiffPos_loop_eq._unary (b454ef896ad0240bf720542824f2db566840628d1fdf1ade4c4ed24f0838dea4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_extract._proof_1_1 (b6be5c1a4db8c149c47bd94b0f4acb4231b46ecc62bc2a05cd4be985c5950a74) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.dblX_eq' (b9ee47912f596dbaf2375180a79623b227dc6c78a3b9281ad43b1f17bc30b00a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastAdd.go_denote_eq._unary (bb5e8c0f8d4e379c065df6dccc7841f1f0cb7bd0094fb2d6e0a92de76a0f117e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Ideal.Quotient.stabilizerHom_surjective_of_profinite (c107a718cbecb1de3b4d28e890a0d00e4dd9966b925c5f0f87b5de29638c2f5c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Limits.colimitLimitToLimitColimit_surjective (c3222710fc60f83889987bc3d9397e478e1be4ed7eb404dae24ee6eb9ca022f9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt (c49eed57b9e8f7e0fa7145697db173f14d07e55aa16c130b61bba170f6a45bc5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Oplax.LaxTrans.vComp_naturality_comp (d67fa53ab81509443326e759ad6b054fd61c14f5e66c45eedf963f1388c125df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Mat_.hasFiniteBiproducts (dba35adb0f906c80bfe2f5056330ea0d30871907e8eaf7f3d54b86bd0241d359) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Std.Iter.toList_intermediateZip_of_finite (dbeb56f1bbc5bd7e90258faa26f1632d8eadcf14de0153b8a47f40409242a6b9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append_extract._proof_1_1 (e07ec5807ddd2514063f3b8c9158d9aea80ca6f8be60d1bdcb3c89b6e7a13333) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Function.Exact.splitInjectiveEquiv._proof_10 (e74bdfa22d2477ae37a67344d30f7301f74dfcc1c1bc01b15c3cff988e34ef55) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.«0».PeriodPair.analyticAt_relation_zero (efb98e985397cccd854391534530ad3c136bdd080e55ceeada910868093d1b8f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.isHomogeneous_addSubMapCoeff (f2ce788af955876c5915f520ac59f72e473f57fbf3aec0857be7005701b17c22) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS retractionKerCotangentToTensorEquivSection._proof_19 (f35ae2d9f1e53d362abda6efe67df03aff946fa23efae7a1cb6102587d4cd658) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.c_relation (fcc6866343ed8b0e1bd4a9dd85e90352bc9e172dc0366c339212ef2321779068) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
    [corpus progress: 5000/5065]
      DIAGNOSIS Matrix.sub_scalar_sq_eq_discr (fef37ae69f3001716f1c0673091eb70f05feca1386aa35f93f4855c1f85964fe) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus tiered-tagN: 5065 constants; 5025 same bytes, 0 same error category, 40 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1363726 ms, Rust 196595 ms]
    [corpus uniform-w2: 5065 constants; 5065 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 379225 ms, Rust 22355 ms]
    [corpus: decode failures 0; total 5867027 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:37:49
	Maximum resident set size (kbytes): 4704176
exit=0
```

`ml_bb_s1.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 33 ms, Rust 2 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 344 ms, Rust 97 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 5066 under [tiered-tagN, uniform-w2]; loaded in 23804 ms]
      DIAGNOSIS Std.DTreeMap.Internal.Impl.balanceR!_eq_balance! (1601895625b67ecddc59ecf9425ca6eae4c66d6b7c8ea8ce5e4490c3ea338e86) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Int.DivMod.Lemmas.«0».Int.add_one_tdiv._proof_1_1 (194bacb9fee23ecb45a13a8fab2095b3f074dceb7bedb7a1a75f47f3ffe5c73b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS TopCat.Sheaf.interUnionPullbackConeLift._proof_5 (1f150c14a61c243d759f462e339b7d824e712ee26eb41419aa9f55b98f0de407) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Localization.existsUnique_algebraMap_eq_of_span_eq_top (23ae320acce50ca3d566210d11ac48d17bf7607df1c356a1a709cdfd12f55d33) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion_aux (2dacebaef8b139ded3b4019b96c90d19d0e06a845cff61c2e55763b2a70ded07) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS HomogeneousLocalization.Away.isLocalization_mul (3af1f33ae2a05488ff0ea5dcdd4892be7d1ece5b5190a45cb3f0380b63791e9f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.mateEquiv_hcomp (3cf47cf160e37479d1bdbab6b5706ee09570afc05cb16222ed5e00aac6e6711a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk.«0».SzemerediRegularity.edgeDensity_star_not_uniform._proof_1_10 (40e45f2eae83609168fb72486797c8757cf07a130636951cc9b786bc23b56fdc) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.Iter.atIdxSlow?_intermediateZip (55d247210280f56e60ab88a44a8cafb7977eb557fd8790c52fec53286049d547) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_add_left._proof_1 (5a362f9e99724cbf1e4dc40216ab8c45c0629e8394bc419dc3ce03a689ca4173) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ.«0».WeierstrassCurve.exists_variableChange_of_char_ne_two_or_three (67e377956e9a5e65fa8a97da8775eb1f9fe0ff8f7bc6aed75111cd4b17a34636) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity.«0».ChevalleyThm.PolynomialC.induction_aux (6b75b2b24c2e310aa9ab5110fc9691b4b25818071fcff2019dbc13f2f5390377) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negDblY_smul (7d2f95bea351a5d580a875a71037d19875cde0936727c2dd3f5f1b8d41c7a9e7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_extract._proof_1 (89ed0e98891415751b5d901324eb6eece9183078959dd60430cb17bc64d44d79) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Int.mul_mem_zero_one_two_three_four_iff (8c33c9187f0005395edd2569203d8cd530fa3792eb9fe66cf4fee100411c612a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.exists_appTop_π_eq_of_isLimit (92454eb0dbd050541a59931f3e202130028143a7c217a88bd98601e4f56d3eb7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Matrix.adjugate_fin_three (a55d6767308a54cc15ec6211709a0d1a53fc495cf399885ea6532c6788600efa) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.addPolynomial_slope (b6a5154a781629bb1beb70715e2f9792a918d9c54f5d5c3d4dfae9d5eeac67e9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback (bc547eefd4fd84f0992166f05140d4bc221cee0bbc84096c4d036a712e197361) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Functor.IsDenseSubsite.isIso_ranCounit_app_of_isDenseSubsite (bd34cbe632ec9a56a33fd7bb51e23fef8fadb90d7ae3af8216921776ed84bff7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824, maxMaterialize=2147483648]; succeeded with [maxMaterialize=4294967296]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.isSheaf_type_propQCTopology_iff (c1a56567a54a70cbf0999232c590bb896c7544cd7678151801e236cd9ed6be37) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append._proof_1 (d126ef57b21ab268daf3d9cb8faef5455e330eb505556ef14924e8d9cbec2fd9) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS TopCat.subcanonical_grothendieckTopology (d216753fba4438d45cf79762178e94f4308da7809083d3392b6cdd369d177ea2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS MeasureTheory.VectorMeasure.variation_withDensity' (d5ea2d6fbb4ca2a2dd2a75ef68b1768bb780fbab0c85aab6a97254d2d6709738) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Real.log_five_near_10 (da962aa5afcd9ef1d6f68919543b2a4f56ed97fb113cd9a101f964de681bacd6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₈_det (df85f966e9848e272be9df5ad9e86542a31c5ffd53b2ed63ac8885b9a12ffd64) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.«0».PeriodPair.iteratedDeriv_six_relation_mul_id_pow_six (ee4f82100489a77cf78a4c542d89541d94630ea17ff1700f3cd242fea32ad3da) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Vector.Extract.«0».Vector.extract_append_extract._proof_1 (eed90987192d51608f220fd7d7ed664c9c87c132401a2e87a4912cc177e4e941) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus progress: 5000/5066]
    [corpus tiered-tagN: 5066 constants; 5038 same bytes, 0 same error category, 28 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1267778 ms, Rust 173843 ms]
    [corpus uniform-w2: 5066 constants; 5066 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 333795 ms, Rust 22299 ms]
    [corpus: decode failures 0; total 4825471 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:20:27
	Maximum resident set size (kbytes): 4717480
exit=0
```

`ml_bb_s2.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 33 ms, Rust 2 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 335 ms, Rust 95 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 5066 under [tiered-tagN, uniform-w2]; loaded in 23498 ms]
      DIAGNOSIS WeierstrassCurve.addSubMapCoeff_condition (02ae6cb3f3ccb488fbfed20bf778afdf8f835339dc34fbad5538c6a266643fc4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS groupCohomology.H1InfRes_exact (076a4a5d72838673c8b1a235fff84767e47060fe8641e355be2c3c68fbf3fd7a) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Cpop.«0».Std.Tactic.BVDecide.BVExpr.bitblast.denote_blastCpopLayer.go._unary (0f75bea9d5dd4591a6f321934e261404b9a8548358d528223bf692a33527d74b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Algebra.WeaklyQuasiFiniteAt.of_quasiFiniteAt_residueField (1817bbc31c531206f258dd78757e193fe5357451872bb99278d6b46ff8ff6db3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq (2d33bfe7c13b87fd41641f9f2fa67e9324fdb71f8a8a3bac49eb3212bfead8e3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negDblY_eq' (37cd1c7638fa9899f80d12762241905e5858b0abbf3a9380e8efd93299d3edf5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912]; succeeded with [maxMaterialize=1073741824]; bytes equal to Rust
      DIAGNOSIS Std.DTreeMap.Internal.Impl.balance!_eq_balanceₘ (4838899f29ca9e49b6cba1126be0d7b721d4cae4f8876ed81d25620e9b0dacb5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Proj.lift_awayMapₐ_awayMapₐ_surjective (4ece542b15e7b7a1cfeccea61d88b4a5d5aa477eb8d8938135f7458d8e353e45) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS groupHomology.H1CoresCoinf_exact (6cc20762d74eb85e981ae78103c561f0be13b11ae5cf5b02ca1bf76794455b3e) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Algebra.Group.Pi.Lemmas.«0».Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle._proof_1_2 (8466008af12aab87e42a21847e9d9e7d8d05f5baf1a65ec4c8e9cfb4e89e6717) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.AlgebraicGeometry.AffineTransitionLimit.«0».AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine (8db8dbcb6033f83c3e6e02db5f18b9efd78d24cfa41a6ad9ca3bb8c6192e6e19) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.instMulActionVariableChange._proof_1 (904073d4c5010184f89d49609e09059722b112294deed7930de71b63ee1fcdd3) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.PreOneHypercover.sieve₁_inter (a0c19571a4dbe5924fd473d3f07cc6039e9ec8ea132d3e96917b461db4818ea4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS retractionKerCotangentToTensorEquivSection._proof_20 (a4fb15377dc50d1f640fc355b336a6412f9b0426de9abf20a917a2a7bcad9097) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.variableChange_b₈ (a79576d568fe07158efe1f43e0c1c4824746bc891729104c0ff529452c7fefd0) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.Vandermonde.«0».Matrix.det_projVandermonde_of_field (a9268270fdbe2890e45ef573d3b75e238e4b77090bc38d785fe63a5795a7f0c5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare.«0».ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real (ce07522299bbd3b14d8dd4db01257925bb7c8c8c600262df528160fb225daf00) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth (daa5d7f02cabe4d9d5ff0cf36901ffcc83fb5705605624c1c64c7b0e7a547d0b) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS TensorProduct.gradedMul_assoc (ecf0501ad22e32ceb7a4405a89e5a543f835528c1909c5abde71664d0084b3df) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.StrictlyUnitaryLaxFunctor.ext (efdbdbe0618ebba20c0e864a40c2457349ce96db59f4d9bfd22c88324170b265) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Polynomial.discr_of_degree_eq_three (f2e292bc76352c3382f2c4bbd6c0228cf74640f1c7966cd09480232d620748e1) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.Algebra.Group.Pi.Lemmas.«0».Pi.single_add_single_eq_single_add_single._proof_1_2 (fa2efaa3a1a2a3ea5e6ae17642bc8127509db2bd2d750a35f3108daebc3106e2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus progress: 5000/5066]
    [corpus tiered-tagN: 5066 constants; 5044 same bytes, 0 same error category, 22 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1191836 ms, Rust 165258 ms]
    [corpus uniform-w2: 5066 constants; 5066 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 320130 ms, Rust 21828 ms]
    [corpus: decode failures 0; total 3713030 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:01:54
	Maximum resident set size (kbytes): 4716612
exit=0
```

`ml_bb_s3.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 48 ms, Rust 3 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 517 ms, Rust 136 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 5066 under [tiered-tagN, uniform-w2]; loaded in 22773 ms]
      DIAGNOSIS _private.Init.Data.Nat.ToString.«0».Nat.digitChar_iff_aux (0691b3f1e8c36b6ba49eb789ca815ff0583eb48dc4c46886aadb190fe43be2f6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negAddY_neg (14f75d2691415463319f5dfce1f3668d59f07ffde9b7aad7c8b0169f407f22ba) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.«0».RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux._proof_1_1 (159e2b0d36d95a7feefe9a1f39b7e65da56802a29e83fe00e567d5b963506ede) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456, maxMaterialize=536870912, maxMaterialize=1073741824]; succeeded with [maxMaterialize=2147483648]; bytes equal to Rust
      DIAGNOSIS Module.reflection_mul_reflection_pow_apply (15b19b23c225d5d472221aea61b5cbe4166b359b0126b53a54669fa41cc8fbfc) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.goCache_decl_eq._mutual (1f13644c31ee2c19d333220bd3c0147bd65cb5ae77e4429b76ed3fa46de073e2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (248b4aa033342acd791b861a9d0f8303a02c7f034e05a26eb8c5f4b087cc7e26) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS ModularForm.discriminant_T_invariant (28d6ee3847c930ae436f8ebc21fa67e03d783d95582be3871bccc5b249d01466) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Scheme.IsLocallyDirected.glueData._proof_6 (338ca448f75e9c25258b64f2a325fac0899b8f347360454e8ecfe7bf7b72ccf7) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.associator_naturality (373b0d8e1af7fe3a1218e5b0f3e7df6c1aa2ad9d2f742ee6460b7f703e0e8e6c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS mem_adjoin_map_integralClosure_of_isStandardEtale (3f383549903f2a37fed9f5d95b0324b680883ee6286b5cfeef222dcdeb91ecc2) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.NatTrans.instIsClosedUnderLimitsOfShapeOverFunctorEquifiberedHomOfHasCoproductsOfShapeHom (4b3beb75cfb6da5466c4d9e4e1f23a364c4c16d56ae9be83aa14cbd19a472a47) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.dblX_smul (55c2d089702c5ef0842325387b5a2ebd34da6eadc46291b29ce198ccd89a791f) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.mono_pushoutSection_of_iSup_eq (5e122ca4869d76508a277442ec2a139158921d8628f607367032e3495bffacd5) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Std.Tactic.BVDecide.BVExpr.bitblast.blastMul.go_denote_eq._unary (68f6e583c732c5f3c079ab3a315711d6b6cba09ffc8dd5b27bf618e251c3d4e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₇_det (6eb6aa5f6e5cc2b4d7606d8d544a3dc26d50e664bb81f852ef3225f88bddc7e4) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS SSet.StrictSegal.isPointwiseRightKanExtensionAt.fac_aux₂ (9fa5347780bca67caeaeb1f8a08ecc9257132be804ea62495a68113699479aba) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList (a400ea3f99ba806af97e4b133d9d54fb55d3b46d23e0369d83fdd811284302e6) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (ae6266c2b1b35cb5d6b366f958c6ee2ec5d8e2fd577f6b401d82f59843d22004) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Bicategory.mateEquiv_hcomp (b201fe77a69f2111a0e3d3776b9ddda429506ebc08608e6307f867bcd69843cc) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728, maxMaterialize=268435456]; succeeded with [maxMaterialize=536870912]; bytes equal to Rust
      DIAGNOSIS Polynomial.discr_of_degree_eq_two (b2338e6157a26a6a907b37fac1a17cef48ec00184a8015af626661c32a33eafb) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CategoryTheory.Lax.OplaxTrans.vComp_naturality_comp (c44c23e5d81a327b0388fb796eeb56d5b68a6d00d71ff74d8e3215088e23ab63) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul (c4641901bb3705423856ac01d337794b1d1096a11d0dc76975389aab6a5b1e99) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Polynomial.Resultant.Basic.«0».Polynomial.sylvesterDeriv_of_natDegree_eq_three (cabce28d54f8e662e07494ef43a9f00d5bbc4dfefb7ac95b581dcc378a6771fe) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS WeierstrassCurve.Projective.negAddY_eq' (d5ec80e0cce67eb9081abe1075d2940312017829abc9807ceebd32d4222b9b53) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (d86a5b2a6aef9f5659a894d980fde30a535ed86961a806202ad6bc342eeff25c) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS CartanMatrix.E₆_det (d9660e5a43a0a0fb78097d2a4e562ac8897e887f60abed2bb3f1f3afc70b5f18) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS Height.mulHeight_sym2_ge (dd9af4585ab3281fd2ae1e46887063a1fcf2d4103b57dff4a7134f89e2d9d159) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
      DIAGNOSIS _private.Mathlib.RingTheory.Etale.QuasiFinite.«0».Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq.match_1_1 (dfd42dc5d9b404a98882ab7c615ff22954c63fbbe353aa4ca8ad1d2a1bce1c77) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
      DIAGNOSIS _private.Init.Data.Array.Extract.«0».Array.extract_append._proof_1_1 (e852d49c2b3a2ea71d1036e9a19406c99f5db76288c568bceb90e40c939ebfec) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864, maxMaterialize=134217728]; succeeded with [maxMaterialize=268435456]; bytes equal to Rust
    [corpus progress: 5000/5066]
      DIAGNOSIS StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv (fdf8644d47f8b068caf56ed87249a924df39afe7abe973d8b458c869639d3c38) [tiered-tagN]: Lean exhausted [maxMaterialize=67108864]; succeeded with [maxMaterialize=134217728]; bytes equal to Rust
    [corpus tiered-tagN: 5066 constants; 5036 same bytes, 0 same error category, 30 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1269207 ms, Rust 167713 ms]
    [corpus uniform-w2: 5066 constants; 5066 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 346656 ms, Rust 22847 ms]
    [corpus: decode failures 0; total 3796550 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:03:18
	Maximum resident set size (kbytes): 4705116
exit=0
```

</details>

<details><summary>[D5] Lean-only constants at 3ddda798, K-based</summary>

`lo_s0.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 69 ms, Rust 4 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 844 ms, Rust 201 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 30 under [tiered-tagN]; loaded in 20540 ms]
    [corpus tiered-tagN: 30 constants; 30 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 967287 ms, Rust 47357 ms]
    [corpus: decode failures 0; total 1036586 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 17:19.79
	Maximum resident set size (kbytes): 4732112
exit=0
```

`lo_s1.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 91 ms, Rust 4 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 709 ms, Rust 163 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 30 under [tiered-tagN]; loaded in 19930 ms]
    [corpus tiered-tagN: 30 constants; 30 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1198201 ms, Rust 58739 ms]
    [corpus: decode failures 0; total 1278450 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 21:21.33
	Maximum resident set size (kbytes): 4735896
exit=0
```

`lo_s2.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 113 ms, Rust 7 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 861 ms, Rust 246 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 30 under [tiered-tagN]; loaded in 20624 ms]
    [corpus tiered-tagN: 30 constants; 30 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1602130 ms, Rust 91515 ms]
    [corpus: decode failures 0; total 1715786 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 28:39.03
	Maximum resident set size (kbytes): 4733240
exit=0
```

`lo_s3.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 103 ms, Rust 6 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 990 ms, Rust 247 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../mathlib.ixe, 679499 constants, comparing 30 under [tiered-tagN]; loaded in 18584 ms]
    [corpus tiered-tagN: 30 constants; 30 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1361105 ms, Rust 60011 ms]
    [corpus: decode failures 0; total 1441288 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 24:04.55
	Maximum resident set size (kbytes): 4735536
exit=0
```

`lo_init.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 105 ms, Rust 6 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1095 ms, Rust 275 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/w2/../init.ixe, 56622 constants, comparing 10 under [tiered-tagN, tiered-tag4]; loaded in 1303 ms]
    [corpus tiered-tagN: 10 constants; 10 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 300271 ms, Rust 12945 ms]
    [corpus tiered-tag4: 10 constants; 10 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 244009 ms, Rust 14012 ms]
    [corpus: decode failures 0; total 572790 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 9:36.24
	Maximum resident set size (kbytes): 838408
exit=0
```

</details>

<details><summary>[D6] Mathlib, all constants, K-based: the 3 completed address shards, then the 3 empty logs (3ddda798)</summary>

`p4/lf_s0.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 183 ms, Rust 21 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 609 ms, Rust 172 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113249 under [tiered-tagN]; loaded in 9841 ms]
    [corpus progress: 5000/113249]
    [corpus progress: 10000/113249]
    [corpus progress: 15000/113249]
    [corpus progress: 20000/113249]
    [corpus progress: 25000/113249]
    [corpus progress: 30000/113249]
    [corpus progress: 35000/113249]
    [corpus progress: 40000/113249]
    [corpus progress: 45000/113249]
    [corpus progress: 50000/113249]
    [corpus progress: 55000/113249]
    [corpus progress: 60000/113249]
    [corpus progress: 65000/113249]
    [corpus progress: 70000/113249]
    [corpus progress: 75000/113249]
    [corpus progress: 80000/113249]
    [corpus progress: 85000/113249]
    [corpus progress: 90000/113249]
    [corpus progress: 95000/113249]
    [corpus progress: 100000/113249]
    [corpus progress: 105000/113249]
    [corpus progress: 110000/113249]
    [corpus tiered-tagN: 113249 constants; 113249 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 2894778 ms, Rust 366979 ms]
    [corpus: decode failures 0; total 3299727 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 55:02.90
	Maximum resident set size (kbytes): 4725640
exit=0
```

`p4/lf_s3.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 136 ms, Rust 8 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 710 ms, Rust 191 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113250 under [tiered-tagN]; loaded in 10888 ms]
    [corpus progress: 5000/113250]
    [corpus progress: 10000/113250]
    [corpus progress: 15000/113250]
    [corpus progress: 20000/113250]
    [corpus progress: 25000/113250]
    [corpus progress: 30000/113250]
    [corpus progress: 35000/113250]
    [corpus progress: 40000/113250]
    [corpus progress: 45000/113250]
    [corpus progress: 50000/113250]
    [corpus progress: 55000/113250]
    [corpus progress: 60000/113250]
    [corpus progress: 65000/113250]
    [corpus progress: 70000/113250]
    [corpus progress: 75000/113250]
    [corpus progress: 80000/113250]
    [corpus progress: 85000/113250]
    [corpus progress: 90000/113250]
    [corpus progress: 95000/113250]
    [corpus progress: 100000/113250]
    [corpus progress: 105000/113250]
    [corpus progress: 110000/113250]
    [corpus tiered-tagN: 113250 constants; 113250 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 2878724 ms, Rust 361923 ms]
    [corpus: decode failures 0; total 3276713 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 54:40.01
	Maximum resident set size (kbytes): 4724964
exit=0
```

`p4/lf_s4.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 166 ms, Rust 14 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 605 ms, Rust 163 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113250 under [tiered-tagN]; loaded in 11094 ms]
    [corpus progress: 5000/113250]
    [corpus progress: 10000/113250]
    [corpus progress: 15000/113250]
    [corpus progress: 20000/113250]
    [corpus progress: 25000/113250]
    [corpus progress: 30000/113250]
    [corpus progress: 35000/113250]
    [corpus progress: 40000/113250]
    [corpus progress: 45000/113250]
    [corpus progress: 50000/113250]
    [corpus progress: 55000/113250]
    [corpus progress: 60000/113250]
    [corpus progress: 65000/113250]
    [corpus progress: 70000/113250]
    [corpus progress: 75000/113250]
    [corpus progress: 80000/113250]
    [corpus progress: 85000/113250]
    [corpus progress: 90000/113250]
    [corpus progress: 95000/113250]
    [corpus progress: 100000/113250]
    [corpus progress: 105000/113250]
    [corpus progress: 110000/113250]
    [corpus tiered-tagN: 113250 constants; 113250 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 2789452 ms, Rust 362141 ms]
    [corpus: decode failures 0; total 3188208 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 53:11.58
	Maximum resident set size (kbytes): 4731392
exit=0
```

`p4/lf_s1.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 148 ms, Rust 8 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 599 ms, Rust 153 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113250 under [tiered-tagN]; loaded in 10395 ms]
    [corpus progress: 5000/113250]
    [corpus progress: 10000/113250]
    [corpus progress: 15000/113250]
    [corpus progress: 20000/113250]
    [corpus progress: 25000/113250]
    [corpus progress: 30000/113250]
    [corpus progress: 35000/113250]
    [corpus progress: 40000/113250]
    [corpus progress: 45000/113250]
    [corpus progress: 50000/113250]
    [corpus progress: 55000/113250]
    [corpus progress: 60000/113250]
    [corpus progress: 65000/113250]
    [corpus progress: 70000/113250]
    [corpus progress: 75000/113250]
    [corpus progress: 80000/113250]
    [corpus progress: 85000/113250]
    [corpus progress: 90000/113250]
    [corpus progress: 95000/113250]
    [corpus progress: 100000/113250]
    [corpus progress: 105000/113250]
    [corpus progress: 110000/113250]
    [corpus tiered-tagN: 113250 constants; 113250 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 3253186 ms, Rust 362555 ms]
    [corpus: decode failures 0; total 3652456 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:00:55
	Maximum resident set size (kbytes): 4726056
exit=0
```

`p4/lf_s2.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 138 ms, Rust 7 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 569 ms, Rust 163 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113250 under [tiered-tagN]; loaded in 10272 ms]
    [corpus progress: 5000/113250]
    [corpus progress: 10000/113250]
    [corpus progress: 15000/113250]
    [corpus progress: 20000/113250]
    [corpus progress: 25000/113250]
    [corpus progress: 30000/113250]
    [corpus progress: 35000/113250]
    [corpus progress: 40000/113250]
    [corpus progress: 45000/113250]
    [corpus progress: 50000/113250]
    [corpus progress: 55000/113250]
    [corpus progress: 60000/113250]
    [corpus progress: 65000/113250]
    [corpus progress: 70000/113250]
    [corpus progress: 75000/113250]
    [corpus progress: 80000/113250]
    [corpus progress: 85000/113250]
    [corpus progress: 90000/113250]
    [corpus progress: 95000/113250]
    [corpus progress: 100000/113250]
    [corpus progress: 105000/113250]
    [corpus progress: 110000/113250]
    [corpus tiered-tagN: 113250 constants; 113250 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 3822533 ms, Rust 385390 ms]
    [corpus: decode failures 0; total 4247937 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:10:52
	Maximum resident set size (kbytes): 4731444
exit=0
```

`p4/lf_s5.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 194 ms, Rust 10 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 640 ms, Rust 173 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/mathlib.ixe, 679499 constants, comparing 113250 under [tiered-tagN]; loaded in 10619 ms]
    [corpus progress: 5000/113250]
    [corpus progress: 10000/113250]
    [corpus progress: 15000/113250]
    [corpus progress: 20000/113250]
    [corpus progress: 25000/113250]
    [corpus progress: 30000/113250]
    [corpus progress: 35000/113250]
    [corpus progress: 40000/113250]
    [corpus progress: 45000/113250]
    [corpus progress: 50000/113250]
    [corpus progress: 55000/113250]
    [corpus progress: 60000/113250]
    [corpus progress: 65000/113250]
    [corpus progress: 70000/113250]
    [corpus progress: 75000/113250]
    [corpus progress: 80000/113250]
    [corpus progress: 85000/113250]
    [corpus progress: 90000/113250]
    [corpus progress: 95000/113250]
    [corpus progress: 100000/113250]
    [corpus progress: 105000/113250]
    [corpus progress: 110000/113250]
    [corpus tiered-tagN: 113250 constants; 113250 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 3089915 ms, Rust 375400 ms]
    [corpus: decode failures 0; total 3504034 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 58:28.78
	Maximum resident set size (kbytes): 4731024
exit=0
```

</details>

<details><summary>[D7] Init, all constants, best of three, tiered-TagN and tiered-Tag4 (a80c16cf)</summary>

`p4/b3_init_s0.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 58 ms, Rust 7 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 763 ms, Rust 273 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 821 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1154355 ms, Rust 64204 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1031664 ms, Rust 66100 ms]
    [corpus: decode failures 0; total 2318668 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 38:41.36
	Maximum resident set size (kbytes): 829404
exit=0
```

`p4/b3_init_s1.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 94 ms, Rust 8 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 874 ms, Rust 234 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 771 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 979395 ms, Rust 73444 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 943637 ms, Rust 77043 ms]
    [corpus: decode failures 0; total 2076188 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 34:39.14
	Maximum resident set size (kbytes): 829212
exit=0
```

`p4/b3_init_s2.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 70 ms, Rust 6 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 856 ms, Rust 228 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 744 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 828231 ms, Rust 59517 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 728887 ms, Rust 59856 ms]
    [corpus: decode failures 0; total 1679117 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 28:02.61
	Maximum resident set size (kbytes): 829400
exit=0
```

`p4/b3_init_s3.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 107 ms, Rust 9 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1445 ms, Rust 452 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 728 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 984823 ms, Rust 67224 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 753423 ms, Rust 61405 ms]
    [corpus: decode failures 0; total 1869504 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 31:13.17
	Maximum resident set size (kbytes): 829636
exit=0
```

`p4/b3_init_s4.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 98 ms, Rust 8 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 865 ms, Rust 233 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 681 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 810440 ms, Rust 62008 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 711211 ms, Rust 65741 ms]
    [corpus: decode failures 0; total 1652224 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 27:35.69
	Maximum resident set size (kbytes): 829624
exit=0
```

`p4/b3_init_s5.log`

```text
    §2 fixtures × [exact, uniform-w1, uniform-w2, uniform-w3, uniform-w5, tiered-tag4, tiered-tagN]: 89 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 88 ms, Rust 7 ms
    350 generated inputs (prefixes, 2-byte payloads, pairs, chains, heavy parents, general) × modes: 2398 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 1734 ms, Rust 562 ms
    [corpus: /tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe, 56622 constants, comparing 9437 under [tiered-tagN, tiered-tag4]; loaded in 2079 ms]
    [corpus progress: 5000/9437]
    [corpus tiered-tagN: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 657967 ms, Rust 55090 ms]
    [corpus tiered-tag4: 9437 constants; 9437 same bytes, 0 same error category, 0 Lean-only and 0 Rust-only resource exhaustion, 0 disagreements; Lean 588550 ms, Rust 54413 ms]
    [corpus: decode failures 0; total 1359924 ms]
	Elapsed (wall clock) time (h:mm:ss or m:ss): 22:45.38
	Maximum resident set size (kbytes): 824832
exit=0
```

</details>

<details><summary>[D8] Mathlib sample, best of three, tiered-TagN and tiered-Tag4 (a80c16cf), aborted</summary>

`p4/b3_ml_s0.log`

```text
Command terminated by signal 15
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:04:57
	Maximum resident set size (kbytes): 4731672
exit=143
```

`p4/b3_ml_s1.log`

```text
Command terminated by signal 15
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:04:55
	Maximum resident set size (kbytes): 4722932
exit=143
```

`p4/b3_ml_s2.log`

```text
Command terminated by signal 15
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:04:53
	Maximum resident set size (kbytes): 4730560
exit=143
```

`p4/b3_ml_s3.log`

```text
Command terminated by signal 15
	Elapsed (wall clock) time (h:mm:ss or m:ss): 2:04:51
	Maximum resident set size (kbytes): 4723700
exit=143
```

</details>

