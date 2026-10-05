# ExprMeta arena encoding (Ixon v4)

Question: can the ExprMeta arenas (43% of the Mathlib `.ixe`) be made substantially
smaller by a change small enough for the v4 PR?

**Status.** The implicit post-order encoding (§4) is part of format v4 in both
implementations; `docs/Ixon.md`, "ExprMeta Arena", is its normative description.
Hash-consing (§5) is not implemented; it is designed here for a stacked PR. §1–§5 were
measured on v3 files (header `0xE3`, `Tag0` integers, heuristic sharing tables); §6 and §7
on files with TagN integers everywhere but still the header `0xE3`, heuristic sharing and
no 4-byte TagN rung; §7 ends with the sizes of the final v4 files.

**Answer.** Yes, for the encoding; no, for deduplication.

- **This PR: implicit post-order children.** A serializer-only change in Lean and Rust.
  Arenas shrink by 13.2% of the Mathlib file and 12.9% of the Init file, measured against
  the v4 baseline (TagN, absolute indices).
  - Re-serialized with the production writer and compared with v3 files, the file shrinks
    by 19.95% on Mathlib (−667,051,250 bytes) and 19.11% on Init (−37,332,515).
  - Lean and Rust are byte-identical (§4).
- **Stacked PR: hash-consing.** It saves a further 10.6% (Mathlib) and 10.3% (Init). It
  changes the producers and both compilers. It is designed
  in §5 and kept separable.

All figures below are exact byte counts from the `arena_study` tool (§8). Its v3 pricing
equals the production writer on every node and every arena of both corpora.

## 1. Where the arena bytes are (v3 files)

| | Init (`init.ixe`) | Mathlib (`mathlib.ixe`) |
|---|---:|---:|
| file | 195,387,870 | 3,343,271,273 |
| arenas (of them in `original` metadata) | 67,995 (2,000) | 793,394 (22,265) |
| nodes | 16,335,501 | 272,299,746 |
| arena bytes, v3 (% of file) | 83,050,319 (42.51%) | 1,436,611,288 (42.97%) |
| App nodes, v3 bytes | 13,192,988, 66,872,939 | 221,528,194, 1,163,416,451 |
| structural child references (App, Binder, Let, Prj, Mdata) | 28,914,135 | 481,089,260 |
| call-site references | 0 | 14,763 |

A v3 App node is a tag byte plus two `Tag0` absolute indices, 5.26 bytes on average.
The corpus study (`sharing-minimum-measurements.md`, "ExprMeta arena structure follow-up") has
the delta histograms and the duplication counts; this note uses its figures where they
agree and adds the encodings below.

## 2. Distributions that decide the encoding

The compilers allocate an arena bottom-up in **post-order**:

- App spines: head, then per argument the argument's subtree and the App node;
- binders: type, body, node; let: type, value, body, node;
- prj and mdata: child, node.

The only exceptions are **expression-cache hits**: a repeated source subexpression gets
the earlier node's index and allocates nothing.

So, for most children, the child sits at the position a post-order reader would expect.
Δ below is `parent − child − 1`.

| slot (Mathlib) | children | Δ = 0 (immediately preceding) | at the post-order position ("fresh") | not backward |
|---|---:|---:|---:|---:|
| App function | 221,528,194 | 125,476,650 | 182,898,348 (82.6%) | 0 |
| App argument | 221,528,194 | 62,949,362 | 62,949,362 (28.4%) | 0 |
| Binder type | 18,460,184 | 307,946 | 7,153,864 (38.8%) | 0 |
| Binder body | 18,460,184 | 16,933,583 | 16,933,583 (91.7%) | 0 |
| Let type / value / body | 314,160 each | 315 / 8,016 / 299,268 | 127,318 / 227,123 / 299,268 | 0 |
| Prj / Mdata child | 56,054 / 113,970 | 27,687 / 101,758 | 27,687 / 101,758 | 0 |
| **all structural slots** | 481,089,260 | 206,104,585 | **270,718,311 (56.3%)** | **0** |

- **App argument.** Only 28% of App arguments are fresh. The rest are cache hits (bound
  variables, repeated arguments) and point further back.
- **Δ = 0 is too narrow.** A plain "Δ = 0 is implicit" rule catches 206M children. The
  post-order cursor (§3) also catches the App function after a fresh argument subtree:
  Δ = size of that subtree, and 57M more children.
- **Init** is the same shape: 16,200,603 of 28,914,135 children are fresh (56.0%).
- **No child points forward or to itself** in either corpus.

## 3. Encodings measured

Every row prices the whole arena: length prefix, tags, name indices, mdata and call-site
payloads, and child references.

- **abs:** TagN (`f = 0`) for every integer, absolute child indices. This is the v4
  baseline: what replacing `Tag0` by TagN gives with no arena change.
- **delta:** every child is TagN of `i − 1 − c` (candidate 1).
- **implicit:** this PR's encoding; it generalises candidate 2.
- **+ hash-consing:** dedup first, then encode (candidate 3; §5).

| encoding | Init bytes | Init vs abs (% of file) | Mathlib bytes | Mathlib vs abs (% of file) |
|---|---:|---:|---:|---:|
| v3 (Tag0, absolute) | 83,050,319 | +11,465,426 (+5.87%) | 1,436,611,288 | +203,696,265 (+6.09%) |
| abs (v4 baseline) | 71,584,893 | 0 | 1,232,915,023 | 0 |
| delta | 62,827,011 | −8,757,882 (−4.48%) | 1,066,692,419 | −166,222,604 (−4.97%) |
| **implicit (this PR)** | **46,429,855** | **−25,155,038 (−12.87%)** | **791,670,984** | **−441,244,039 (−13.20%)** |
| delta + hash-consing | 35,244,093 | −36,340,800 (−18.60%) | 576,239,799 | −656,675,224 (−19.64%) |
| implicit + hash-consing | 26,313,130 | −45,271,763 (−23.17%) | 435,756,696 | −797,158,327 (−23.84%) |

- **Against v3,** the implicit encoding with TagN removes 36,620,464 bytes on Init (18.74%
  of the file) and 644,940,304 on Mathlib (19.29%).
- **The two effects are not additive,** as the corpus study noted. Measured together,
  hash-consing adds −20,116,725 (Init) and −355,914,288 (Mathlib) on top of implicit.
- **Per-slot choice (suggested by the corpus study) is subsumed.** The one slot where plain deltas lose
  (Binder type) is handled by the implicit/explicit choice, which is made per child.

Implicit encoding by node kind (Mathlib):

| kind | nodes | abs bytes | implicit bytes | implicit B/node |
|---|---:|---:|---:|---:|
| app | 221,528,194 | 950,015,204 | 543,385,811 | 2.45 |
| binder | 18,460,184 | 135,167,096 | 101,936,299 | 5.52 |
| ref | 23,362,646 | 132,917,222 | 132,917,222 | 5.69 |
| leaf | 8,464,218 | 8,464,218 | 8,464,218 | 1.00 |
| letBinder, prj, mdata, callSite | 484,504 | 5,162,691 | 3,778,842 | |

**What remains after implicit** (Mathlib, 791.7 MB):

- explicit child references: 343.0 MB, mostly cache-hit App arguments;
- tag bytes: 272.3 MB;
- name indices: 174.0 MB.

## 4. The chosen encoding (implemented in v4)

`docs/Ixon.md`, "ExprMeta Arena", is the normative text. In short:

- **Arena.** `len`, then the nodes in index order.
- **Node tag.** Node `i` starts with the tag `kind << 3 | mask`:
  - kinds are the v3 tag numbers 0–11 (binder info stays packed in kinds 2–5);
  - `mask` has one bit per structural slot.
- **Implicit slot** (bit set). The slot is not written. A cursor `top` starts at `i` and
  visits the slots last to first. An implicit slot is node `top − 1`, and `top` then
  becomes `lo[top − 1]`. Afterwards `lo[i] = top`: the start of node `i`'s contiguous
  post-order block.
- **Explicit reference.** Structural slots with the bit clear, and every call-site
  reference, are TagN (`f = 0`) of `(i − 1 − c) mod 2^64`.
- **Bijective.** The writer sets a bit exactly when the child is `top − 1`. The reader
  rejects:
  - an explicit child equal to `top − 1`;
  - an implicit child with `top = 0`;
  - mask bits beyond the kind's slot count;
  - kinds above 11.

  Wrapping makes every `u64` index representable, including forward and self references
  (9 bytes). The encoder is therefore total (Lean's `PutM` cannot fail) and needs no new
  producer invariant. The property tests' generated arenas, which can self-reference at
  node 0, need no change.
- **Other integers** in the arena keep their helper encodings, which are TagN in v4 like
  every other integer: the length, name indices, mdata, call-site counts and scalars. Only
  the child deltas call `putTagN 0` / `TagN::put(0, …)` directly, so the arena encoding
  and the Tag0 → TagN replacement are independent changes.

### Constraints

- **Determinism and parity.** The bytes are a pure function of the in-memory arena, with
  the same algorithm in both languages.
- **Anonymous constant bytes and addresses** do not change.
- **The arena is unchanged.** It is still exactly what the compiler built: the encoding
  is a function of it and decodes back to it.

### Consumer impact

**None.** The decoded `ExprMetaArena` / `ExprMeta` (absolute `u64` indices) is identical,
so none of these change:

- the compilers (`Ix/CompileM.lean`, `crates/compile/src/compile.rs`);
- the decompilers (`Ix/DecompileM.lean`, `crates/compile/src/decompile.rs`);
- kernel meta ingress (`Ix/Tc/IngressMeta.lean`, `crates/kernel/src/ingress.rs`);
- the FFI marshalling (`crates/ffi/src/lean_ixon/meta.rs`);
- the proofs (none is about the serialized arena; the sharing proofs in `IxSharingVerify`
  do not touch metadata);
- IxVM, which does not read metadata.

**The one API change** is in the node-level (de)serializers: they now need the node's
position and the block starts.

- Lean: `putExprMetaDataIndexed` / `getExprMetaDataIndexed` become `putExprMetaNode` /
  `getExprMetaNode`.
- Rust: the public `ExprMetaData::put_with` / `get_with` become private
  `put_node` / `get_node`.
- Only one outside caller existed: `Benchmarks/SharingStudy.lean`. Its
  `getArenaBreak` now threads `lo` (4 lines).

### Diff size (this PR's share)

From `git diff --numstat` against the development branch before the arena change:

| file | added | removed | what |
|---|---:|---:|---|
| `crates/ixon/src/metadata.rs` | 515 | 153 | serializer; tests: 3 byte vectors, rejections, 2,000 pseudo-random arenas |
| `Ix/Ixon.lean` | 220 | 115 | serializer |
| `Tests/Ix/Ixon.lean` | 67 | 0 | the same byte vectors and rejections |
| `Benchmarks/SharingStudy.lean` | 5 | 3 | harness call site |
| `docs/Ixon.md` | 51 | 16 | the wire format |

- Separately: this note and the measurement example `crates/ixon/examples/arena_study.rs`
  (934 lines).
- No consumer, producer, proof or FFI file changes.

### Measured with the production writer (before TagN replaced Tag0)

The v3 files were read with a temporary, uncommitted legacy arena reader (the v3
`ExprMeta::get_with`, switched on only while the cursor parses the file). Each arena and
each §5 window was then re-serialized with the implicit encoding's production writer
(`ExprMeta::put_with`, `put_named_indexed`), and every arena was round-tripped through
the production reader.

Integers other than the child references were still `Tag0` in this measurement: the
Tag0 → TagN replacement had not landed.

| | Init | Mathlib |
|---|---:|---:|
| arenas re-serialized | 67,995 | 793,394 |
| size mismatches against the predicted pricing / round-trip mismatches | 0 / 0 | 0 / 0 |
| arena bytes, v3 → implicit | 83,050,319 → 45,731,058 | 1,436,611,288 → 769,664,251 |
| §5 windows + length prefixes, v3 | 84,921,487 + 161,358 | 1,469,007,694 + 2,063,780 |
| §5 windows + length prefixes, implicit | 47,602,226 + 148,104 | 802,060,657 + 1,959,567 |
| **file size change** | **−37,332,515 (−19.11%)** | **−667,051,250 (−19.95%)** |
| file size, v3 → implicit | 195,387,870 → 158,055,355 | 3,343,271,273 → 2,676,220,023 |

- **The v3 baseline is independently confirmed.** The v3 window and prefix totals equal
  the sum of the independent §5 breakdown in `sharing-minimum-measurements.md`, category
  by category, on both files.
- **Larger than the §3 implicit row.** These savings exceed the "implicit" row because
  name indices are still `Tag0` here. With TagN integers the arenas cost the §3
  "implicit" figures (46,429,855 and 791,670,984), and the name-index growth of §6
  applies.

### Lean/Rust parity

- **Lean `ixon` suite: 374 passed, 0 failed.** It includes:
  - the byte vectors;
  - "Surgery metadata env bytes Lean==Rust";
  - the generator-driven "Env serde roundtrips", "Env serialization Lean==Rust" and
    "Env bytes Lean==Rust" over generated environments with full metadata (call sites,
    extension tables, `original`).
- **The ignored `ixon-corpus` gate passed** (331 s). The Rust compiler writes the IxTests
  binary's whole environment, a superset of Init, in the new format. Then:
  - pure Lean `deEnv` parses it;
  - `serEnv` reproduces the bytes exactly;
  - the FFI parse agrees.
- **Rust:** `cargo test -p ixon`: 412 passed, 0 failed.
- **Related Lean suites:** `ffi meta-env catalog import-ixe decompile-unit tc-unit` (run
  under `lake env`): 692 passed, exit 0.
- **Before TagN replaced Tag0.** The results above are from before that change.

**After TagN became the only integer code** (on the development branch, once TagN became the only code):

- **Lean `ixon` suite: 331 passed, 0 failed.** The share-codec tests were removed with the
  TagN change.
- **The `ixon-corpus` gate passed** (242 s).
- **Rust:** `cargo test --release -p ixon --lib --tests`: 387 passed, 4 failed. The four
  failures also occur on a clean checkout of that state (382 passed, the same 4 failed), so
  they are not caused by the merge:
  - `proof::tests::catalog_claim_wire_bytes_pinned`;
  - `proof::tests::v3_claim_fixtures_and_strict_scope`;
  - `resource::addressed::tests::canonical_cross_language_fixtures`;
  - `sharing_exact::tests::parallel_tiered_matches_sequential`.
- **Lint:** clippy (`--lib --tests --example arena_study`, `-D warnings`) is clean.
- **Known breaks in that state itself** (both fixed later on `ix-sharing`):
  - The `sharing_corpus` example did not compile: it imported the removed
    `put_expr_with`.
  - The `sharing-study` harness did not compile: it had 35 uses of `Ixon.getTag0` and
    `getTag4`, including its own arena-length read.

  The arena change touches only the harness's node-reader call.

## 5. Stacked PR: within-arena hash-consing

**Measured effect.** Dedup first, then the implicit encoding: −355.9 MB on Mathlib
(10.65% of the file) and −20.1 MB on Init (10.30%), beyond §4.

- **Surviving nodes.** 140,419,081 of 272,299,746 (51.6%); on Init, 8,991,706 of
  16,335,501.
- **Why this differs from the corpus study's count.** That study found 133,235,031
  duplicates on Mathlib. Here
  nodes carrying a level-spelling patch are never merged (see the audit), so 1,354,366
  fewer nodes merge.
- **Redirection cost.** Roots and patch keys outside the arena get *cheaper*, because
  indices shrink:
  - Mathlib: 2,522,841 type/value/rule roots and patch keys; 2,588 point to a merged node
    and are redirected; their TagN bytes go 3,681,438 → 3,391,478.
  - Init: 139,483 indices, 177 redirected, 167,482 → 159,564 bytes.
  - Call-site references redirected inside the arena: 2,253 on Mathlib, 0 on Init. They
    are priced in the arena rows.

**Consumer audit (tree assumptions).**

- **No code mutates an arena node after allocation**, in Lean or Rust. The only
  post-allocation read is `finishEtaCallSite`, which only reads.
- **Every expression-conversion cache is keyed by (expression, arena index)**, so a
  shared node is safe:
  - Rust decompile: `(Arc ptr, idx)`;
  - Rust kernel ingress: `(expr ptr, arena_idx)`;
  - Lean `DecompileM`: `(e, arenaIdx)`;
  - Lean `IngressMeta`: `(shareIdx, arenaIdx)`.
- **No consumer does index arithmetic** on arena indices. The decompiler's `u64::MAX`
  "no metadata" sentinel is in-memory only.
- **The one per-node side table is `univPatches`.** Level-spelling patches are keyed by
  arena index, and all four consumers read them per node. Two occurrences with different
  original spellings must not share a node, so patched nodes are never merged; the
  measurement above already obeys this. The compiler also clones the head's patch onto
  `callSite`/`etaCallSite` roots by index lookup during compilation, which is before any
  post-pass, so it is unaffected.

**Design.**

- **A post-pass, not a change to `allocArenaNode`.** `ExprMetaArena.hashCons` runs where a
  constant's metadata is finalized. It keeps the first occurrence of every class, keyed by
  (node with renumbered children, patched?). It renumbers:
  - children and call-site references;
  - type/value/rule roots;
  - `UnivPatch.arenaIdx`.
- **Order and acyclicity.** First-occurrence order keeps every reference backward and the
  output deterministic. The result is the same as allocation-time dedup.
- **Proofs.** No theorem covers the compiler's metadata or its arenas: the proofs of the
  arena allocation and the metadata finalizer were part of the compiler-correctness proof
  tree, which is retired ([kernel](kernel.md), "Removal ledger"). The post-pass needs no
  lemma.

**Size estimate.**

- the pass in Lean and Rust, about 120 lines each, plus Lean/Rust parity tests;
- one call at each metadata finalization site: Lean `takeArena` users in
  `Ix/CompileM.lean` (defn, axio, quot, recr, ctor, inductive and mutual paths) and
  `Ix/AuxGen/CompileAux.lean`, and the Rust equivalents in `compile.rs`, `mutual.rs` and
  `kernel_egress.rs`;
- fixture regeneration, which v4 needs anyway.

That is too large for "serializer only", hence a stacked PR. It needs no format change:
the §4 encoding already handles DAG arenas.

## 6. TagN and integers in [82,048, 2^24): census and the 4-byte rung

Measured on the v4 files of §7 with `arena_study --int-census`.

**The gap.** For values in [82,048, 2^24), TagN (`f = 0`) takes 5 bytes where `Tag0`
took 4. The census walks every `f = 0` integer outside constant bodies:

- §1–§4 counts and lengths;
- §3 hints;
- every §5 integer: name keys, constant ranks, fused hints, window lengths, all
  `ConstantMeta` fields, arena integers and table counts.

It prices each integer three ways: `Tag0`, TagN as specified, and TagN with one more
rung.

**Self-check.** For every §5 window (66,621 Init, 778,344 Mathlib; 0 mismatches), the
TagN-priced census integers plus the non-integer bytes equal the production writer's
window.

**Constant bodies** cannot reach the gap for `f = 0`. The largest refs/univs tables are
1,350/129 entries (Mathlib) and 441/22 (Init), and indices are bounded by them.

**Integers in [82,048, 2^24), each one byte longer than in `Tag0`:**

| field class | Init | Mathlib |
|---|---:|---:|
| arena node name indices (binder, let, ref, prj, call-site, mdata keys, `OfName`) | 1,379,100 | 29,774,488 |
| `ConstantMetaInfo` name indices (name, levels, all, ctx, ctors, rules, induct) | 222,383 | 3,349,298 |
| §5 name keys | 59,222 | 773,149 |
| §5 constant ranks | 0 | 683,556 |
| arena explicit child deltas | 0 | 242,432 |
| everything else (lengths, counts, roots) | 24 | 366 |
| **total = bytes a 4-byte rung would save** | **1,660,729 (1.06% of the file)** | **34,823,289 (1.31%)** |

- **Name-class growth over `Tag0`, net of the values that got shorter:**
  - Mathlib: arena names +22,243,839, `ConstantMetaInfo` names +3,052,196, §5 keys
    +771,058, §5 ranks +645,449.
  - Init: arena names +712,195, `ConstantMetaInfo` names +209,601, §5 keys +56,370.
- **A 4-byte rung is free in code space for every flag width.** In the five-rung TagN
  measured here, the last selector `c = 3` was invalid. Codes `c = 0, 1, 2, 3` can select
  2, 3, 4 and 8 following bytes (widths 1, 2, 3, 4, 5, 9).
  - For `f = 0` the rung covers [82,048, 16,859,264).
  - TagN is then never longer than `Tag0` below 2^32.
  - The rung also covers `f = 4` Share indices in [66,568, …). The Mathlib compile
    measured here (heuristic sharing) has one sharing table of 81,464 entries, so some
    Share references there pay the same extra byte. Constant bodies are outside this
    census, so they are not counted.
  - The rung was adopted (`docs/sharing-minimum.md` §12.16) and is part of TagN in v4
    (`docs/Ixon.md`, "Integer Encoding (TagN)"). The figures above are its exact savings.
- **A per-arena local name table is no fix.** On the v3 files it saves 2.9 MB on Mathlib
  and costs 0.4 MB on Init: there are 28.8M distinct names per arena out of 42.2M
  references.

## 7. File sizes with TagN-only integers and the implicit arenas

Init and Mathlib were recompiled once TagN was the only integer code and the implicit
arena encoding was in place (`ix compile`, same inputs as the v3 corpora; heuristic
sharing, five-rung TagN, header `0xE3`):

| | v3 file | v4 file | change |
|---|---:|---:|---:|
| Init (`Benchmarks/CompileInit.lean`) | 195,387,870 | 156,922,814 | −38,465,056 (−19.69%) |
| Mathlib (`Benchmarks/Compile/CompileMathlib.lean`, 771,129 constants requested) | 3,343,271,273 | 2,654,926,848 | −688,344,425 (−20.59%) |

- **Writer check on the v4 files** (`--check-writer --other-tagn`): every arena equals its
  predicted implicit TagN size, and every arena round-trips through the production
  reader. 0 / 0 mismatches over 67,995 (Init) and 793,394 (Mathlib) arenas.
  - Arena bytes: 46,429,863 (29.59% of the v4 Init file) and 791,674,724 (29.82% of
    Mathlib).
  - Priced with absolute TagN indices instead, the arenas would be 25,155,038 and
    441,243,705 bytes larger. That is this PR's share of the v4 reduction.
- **The rest of the file barely moves.** Outside the arenas it shrinks by 1.8 MB (Init) and
  43.4 MB (Mathlib).
- **Same metadata, fresh compile.** The arenas are the same as in the v3 corpora apart
  from a fresh compile: Init 16,335,501 nodes in both; Mathlib 272,299,589 v4 vs
  272,299,746 v3.
- **Not yet the final v4 file.** These files still have the header byte `0xE3`,
  heuristic sharing tables and no 4-byte rung. With the rung (still `0xE3` and heuristic
  sharing, before the route switch) the same compiles write 155,259,078 and 2,620,063,965 bytes.

The final format adds version 4 (header `0xE4`), canonical sharing and the rung of §6.
Compiled with it (`lake exe ix compile`, same inputs, at this PR's head; the same bytes were
written before and after the Rust optimizations):

| | v3 file | final v4 file | change |
|---|---:|---:|---:|
| Init | 195,387,870 | 143,680,738 | −51,707,132 (−26.46%) |
| Mathlib | 3,343,271,273 | 2,318,833,546 | −1,024,437,727 (−30.64%) |

- **Canonical sharing's share.** Against the heuristic-sharing files above (the same
  environments), the final files are 11,578,340 bytes (−7.46%, Init) and
  301,230,419 bytes (−11.50%, Mathlib) smaller.
- **Identity.** sha256 `317d63bb…873363` (Init) and `a893a449…917bfc` (Mathlib). Every
  canonical-route compile of these inputs that was measured, before and after the Rust
  construction's optimizations, wrote the same bytes.

## 8. Reproduction

`$S` is any directory holding the corpora, and `arena_study` is
`target/release/examples/arena_study`. `init.ixe` and `mathlib.ixe` are compiled with
`lake exe ix compile Benchmarks/CompileInit.lean --out $S/init.ixe` and
`lake exe ix compile Benchmarks/Compile/CompileMathlib.lean --out $S/mathlib.ixe` (the
Mathlib setup is in `sharing-minimum-measurements-mathlib.md`, "Reproduction"). A reader
accepts only its own format version, so the v3 rows need v3 files and a v3 checkout
(the development branch before the arena change), and the §6–§7 rows need files written by the same checkout
that reads them.

```text
nix develop --command bash -c 'cargo build --release -p ixon --example arena_study'
# Pricing of all encodings + v3 writer check: build against the v3 metadata.rs
# (the development branch before the arena change), then
arena_study $S/init.ixe --check-writer --writer v3
#   -> 0 size / 0 roundtrip / 0 node mismatches (67,995 arenas, 83,050,319 bytes)
arena_study $S/mathlib.ixe --check-writer --writer v3
#   -> 0 / 0 / 0 (793,394 arenas, 1,436,611,288 bytes); 127-398 s with machine load
# Production-writer measurement: this branch + the temporary legacy reader
# (pub static LEGACY_V3_ARENA, consulted at the top of ExprMeta::get_with;
# set by the tool around NamedMetaCursor parsing), then
arena_study $S/init.ixe --check-writer --writer implicit      # 28 s
arena_study $S/mathlib.ixe --check-writer --writer implicit   # 394 s
# Parity
nix develop --command bash -c 'cargo test --release -p ixon'
nix develop --command bash -c 'lake build IxTests sharing-study'
nix develop --command bash -c '.lake/build/bin/IxTests ixon'
nix develop --command bash -c 'lake env .lake/build/bin/IxTests --ignored ixon-corpus'
```

With TagN-only integers (§6, §7):

```text
nix develop --command bash -c 'lake build ix'
lake exe ix compile Benchmarks/CompileInit.lean --out $S/init_v4.ixe              # 27 s
lake exe ix compile Benchmarks/Compile/CompileMathlib.lean --out $S/mathlib_v4.ixe # 261 s
#   (Benchmarks/Compile/.lake copied from a checkout with the Mathlib build)
arena_study $S/init_v4.ixe --check-writer --other-tagn      # 0 / 0 mismatches
arena_study $S/mathlib_v4.ixe --check-writer --other-tagn   # 0 / 0 mismatches, 231 s
arena_study $S/init_v4.ixe --int-census                      # 66,621 / 66,621 windows
arena_study $S/mathlib_v4.ixe --int-census                   # 778,344 / 778,344 windows
```
