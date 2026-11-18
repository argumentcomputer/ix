# Fewer commitments for Aiur compression

> **Historical (2026-11-15).** This document is a design exploration. The chosen design is described in [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status: design exploration for review. Nothing here is implemented. Figures
are cited measurements unless marked as estimates.

## Summary

The terminal PLONK circuit is too large because each BN254 KZG proof it
verifies carries thousands of commitments, one per AIR column. The fresh
Init BN proof has 6,325 variable G1 points. Each commitment costs the next
verifier a non-native scalar multiplication. Three families of change reduce
that count:

1. **Pack columns at the PCS level** (§4). Interleave many columns into one
   KZG polynomial and open all of them with one SHPLONK-style batched opening.
   - **Measured on the matched verifier execution:** 8,978 → 60 variable G1
     points.
   - **Shape-only estimates:** about 69 points at a `2^26` coefficient cap
     for the saved grouped Init BN profile, plus fixed-key commitments. The
     terminal-profile geometry gives 81–84. Mixed-height lifting (22–27
     points) adds evaluation and structure-check costs that have not been
     counted.
   - **For comparison:** the hand-written path has 12 variable and 16 fixed
     points.
   - **What changes:** the application programs, their compiled constraints
     and the compiler proofs stay unchanged. The recursive Aiur verifier's
     PCS implementation, proof parsing and transcript must change, as must
     the Rust prover.
   - An earlier packed experiment opened the same packing with binary folds,
     which produced hundreds of fold and witness points. This opening needs
     none of them.
2. **Narrow the layout** (§5). Compile Aiur verifiers into a few columns, as
   the hand-written stages do: either fully inlined straight-line circuits, or
   per-function gate templates with dynamic calls. Both need new compiler
   proofs.
3. **Make each commitment cheaper** (§6). Use windowed or GLV MSMs, fixed
   bases for key commitments, and a constant key in the terminal. This is
   incremental, roughly 2–8×.

Option 1 is the largest single lever, but it's a protocol change, and the
handoff records a preference for keeping the current protocols. The
protocol-preserving levers in §7 come first:

- source factoring of cold wide functions;
- less restrictive grouping;
- selective narrowing of cold circuits.

Each should be measured on all commitment classes, padded cells, quotient
work and cost to the next verifier. Whole-program flattening (§5, 2a) and
packed openings stay candidates until those measurements show the
incremental routes can't reach the target.

## 1. Cost model

The verifier of a multi-stark KZG proof pays for three things:

| Quantity | Paid per | In-circuit cost | Today, actual Init |
|---|---|---|---|
| G1 points | commitment and opening witness | non-native scalar multiplication plus point decoding | about 4,400 points; G1/Fq/MSM work is about 60% of 734,887,425 terminal cells |
| Field evaluations | column and opening point | native Fr arithmetic; BLAKE3 if hashed as bytes | about 9,000 values; hashing is a large share of BLAKE3's 22% |
| Constraint DAG | circuit | native Fr arithmetic over each circuit's constraint graph | small: about 12,000 static operations across 161 function circuits |

Fixed costs per stage are the key digest, transcript, pairing accumulator and
claims. Proving a stage costs cells, separately from all of this.

Only the first row is expensive in a non-native verifier. So the goal is
fewer *G1 points*, not fewer columns as such. Columns matter today only
because per-column KZG gives each one its own point.

The hand-written path keeps both small. Its final gnark circuit has
14,689,424 constraints (`2^24`), proves in 11.2 s, and costs 292,004 gas per
external verification with 2 public inputs and 1 commitment
(`docs/measurements/aiur-compression-incremental.json`).

## 2. How SP1 and ZisK do it

Sources: `~/repos/clones/zkvm/sp1` at `749b0c6` and
`~/repos/clones/zkvm/zisk` at `8fb64a9`, plus pil2-proofman
`pre-develop-1.4.0-alpha`, all read without building.

| | SP1 (Hypercube 6.1) | ZisK (pil2-proofman 1.4) | Ix hand-written | Ix Aiur today |
|---|---|---|---|---|
| Recursion PCS | multilinear BaseFold, jagged PCS, LogUp-GKR | FRI over Goldilocks | per-column KZG over BN254 | per-column KZG over BN254 |
| Cost of a column to the next verifier | almost none: all chips under 2 digests | Merkle leaf width only | non-native MSM term | non-native MSM term |
| Verifier authoring | Rust DSL compiled to a straight-line program | circom generated from stark info, then R1CS | hand-written Rust gadgets | Aiur source |
| Recursion layout | 8–9 fixed chips; program in preprocessed columns | `plonk2pil`: one fixed PIL template per hash family (18–46 wires, custom gates) | multi-stark `plonkish`: 3 advice columns | one AIR per function |
| Hand-written constraint code | about 3.7k lines of chips, written once | about 200–300 lines of PIL per family, written once | per-gadget Rust (`recursive/native_*.rs`, 2,766 lines) | none |
| Final wrapper | gnark PLONK or Groth16; 5 public inputs; 1 BSB22 commitment | pilfflonk over BN254; 1 public input | gnark PLONK; 2 public inputs | gnark PLONK from gate files; 2 public inputs |
| On-chain gas | not in repo; about 270–300k (Groth16) / 300k+ (PLONK) from memory, unverified | 332,661 (`verifyProof`) to 353,287 (call) on a comparable wrap; stock PLONK on the same circuit 263,175 | 292,004 | 285,614 (289,883 through the shared `IxPlonkVerifier` adapter) |

Both projects also make column count nearly irrelevant at the commitment
layer: SP1 stacks every chip under one jagged commitment, and ZisK commits
Merkle trees. §4 is the KZG analogue of that choice.

**Gas.** For a fixed proof system, verification gas depends on the number of
public inputs and commitments, not on circuit size or the inner PCS. The Aiur
terminal keeps the hand-written shape: 2 public fields and 1 commitment. Measured on the EVM
(forge 1.9.0, solc 0.8.37, `via_ir`) it costs 285,614 gas, or 289,883 through
the same adapter as the hand-written path (292,004), under the 320k target. Final proof size is constant: 584
bytes native, 864 in Solidity form.

## 3. Why the final hop can't be hash-based

Wide recursion is already hash-based: the Goldilocks root, aggregation and
`CompressWrap` use FRI with BLAKE3. The hop into BN254 can't be, because
Poseidon2 is excluded.

A FRI verifier's cost is mostly Merkle-path hashing, independent of column
count. With 100 queries, 4 trees of about 24 levels each and about 300 FRI
fold-path nodes, that is roughly 40,000 BLAKE3 compressions. The Aiur
BLAKE3 library lowers to about 1,468 gates plus 224 byte lookups per round,
in eight round rows per compression: about 11.7k gates per compression
(§9). That is roughly 470M constraints before leaf hashing, far over
`2^24` even with more aggressive FRI parameters.

SP1 makes this hop with Poseidon2 over BN254. ZisK's BLAKE3 family needs
custom BLAKE3 gates in pilfflonk, which stock gnark lacks, and produces a
6,752-byte proof. A KZG proof has no Merkle paths, so KZG remains the right
last hop. What has to change is how many points it carries.

## 4. Option 1: packed KZG openings

### Construction

Group the columns of one commitment round (main, lookup or quotient) into
packs. A pack of `W` columns `f_0 … f_{W-1}`, each of degree below `n`, commits
one polynomial:

```text
P(X) = Σ_j X^j · f_j(X^W)          deg P < W·n ≤ SRS size
```

The commitment is the existing MSM over interleaved monomial coefficients:
the coefficient of `X^{j + W·k}` is coefficient `k` of `f_j`. The prover
already transforms each column to coefficients, so commitment work is
unchanged.

The opening uses this identity:

```text
P(X) mod (X^W − ζ)  =  Σ_j f_j(ζ) · X^j
```

The remainder's coefficients are exactly the column evaluations at `ζ`. For
the next-row point, the point set becomes `{X^W = ζ} ∪ {X^W = ζω}`, with
vanishing polynomial `(X^W − ζ)(X^W − ζω)`. The remainder is determined by the
claimed values at both points.

All packs, with their different point sets, are proved by one SHPLONK batch
(Boneh–Drake–Fisch–Gabizon):

1. The prover commits `W₁ = Σ_i γ^i (P_i − r_i) / Z_i`.
2. After a random `z`, the prover commits the linearization witness `W₂`.
3. The verifier checks
   `e(F + z·W₂, [1]₂) = e(W₂, [τ]₂)`, where
   `F = Σ_i γ^i Z_{T∖S_i}(z)(C_i − r_i(z)·[1]₁) − Z_T(z)·W₁`.

This needs only `[1]₂` and `[τ]₂`, so it works with Ignition. The verifier
evaluates `Z_i(z) = (z^W − ζ)(z^W − ζω)` and `r_i(z)` natively, in O(W).
Opening witnesses: 2 in total, not per point or per pack.

**Evaluations must be hashed.** Claimed evaluations enter the transcript
before the first SHPLONK challenge, as in halo2 and pilfflonk. An earlier
draft proposed binding them only through a committed vector `E` opened at a
random point. That is unsound. Every check on the values is linear in them,
and the values are chosen after the challenges, so a prover can change several
of them consistently. The prototype's test
`committed_evaluations_without_hashing_are_forgeable` demonstrates the
forgery; the hashed mode rejects it. In-circuit hashing cost therefore still
grows with the number of evaluations. A cheaper sound alternative would be an
algebraic hash over native Fr, not a linear form.

**Prototype measurement** (2026-11-13; `target/packed-shplonk/summary.json`).
Matched verifier execution (`kzg-source.ixa`, `KzgVerifier::verify_deferred`),
development SRS cap `2^20`, CPU only, equal-height packs, hashed evaluations,
one challenge `γ` across packs as in fflonk:

| | Per-column KZG (production config) | Packed SHPLONK |
|---|---:|---:|
| Variable G1 points | 8,978 (7,058 main + 1,659 lookup + 243 quotient + 18 openings) | 60 (21 + 19 + 18 packs, plus `W₁`, `W₂`) |
| Proof bytes | 646,044 (compact codec) | 491,406 (bincode) |
| Opened values | 11,029 | 11,029 + 3,964 extra |
| Prove / verify time | 11.74 s / 0.087 s | 8.06 s / 0.009 s |
| Peak RSS | 1.66 GB | 2.01 GB |

**Tests passing:**
- the closed forms agree with polynomial division and with root-based
  interpolation;
- forgery rejections: altered evaluations, commitments and witnesses; moved
  or dropped points; swapped or missing packs;
- a two-circuit multi-stark system round-trips through serialization;
- an Aiur program (`bn254-trace.ixa`) proves and verifies, and a changed
  output is rejected.

**Known gaps:**
- The extra evaluations (26% of the proof) come from current-row-only columns
  sharing packs with next-row columns. Planning packs by height and next-row
  use would remove most of them.
- No CUDA measurement.
- The Aiur verifier source, key-digest binding and mixed-height lifting are
  not yet done.

### Counts on the actual Init profile

Estimates, using the terminal profile's real circuit heights and widths
(`target/terminal-gadget/actual-init/profile-checked/profile.json`): 8,658
main, 1,396 lookup (group 2) and 372 quotient columns over 25 heights.

| Packing | SRS cap | Packs (main + lookup + quotient) | Variable G1 points (packs, plus 3 fixed overhead points; the 3 assumed a committed `E` (§4, unsound) as well as `W₁` and `W₂`) |
|---|---:|---|---:|
| equal heights only | 100.8M | 29 + 25 + 25 = 79 | 82 |
| equal heights only | `2^26` | 82 | 85 |
| mixed heights (lifted) | 100.8M | 11 + 5 + 3 = 19 | 22 |
| mixed heights (lifted) | `2^26` | 15 + 5 + 4 = 24 | 27 |
| per-column KZG (today) | — | — | 6,325 (fresh Init BN proof); 11,700 columns in this terminal profile |

**Mixed-height lifting.** A column of height `h` placed in a pack whose
height is `n` uses `g(X) = f(X^{n/h})`. Then `g(ζ_n) = f(ζ_n^{n/h})` and
`g(ζ_n·ω_n) = f(ζ_n^{n/h}·ω_h)`. With `ζ_n = ζ^{N/n}`, every height-`h`
column opens at the same points it uses today, whatever pack it lands in.

**Lifting needs an extra soundness check.** An arbitrary committed `g` of
degree below `n` represents `n/h` independent height-`h` traces, tiled. Each
tile restarts its LogUp accumulator. A circuit with `k` tiles contributes its
declared total `k` times, so the global balance check could pass while the
actual messages don't balance. Lifted packs must also prove the structure
`g(x·ω_{n/h}) = g(x)`, by one more opening point set per lift factor (native
check). Equal-height packs don't need this.

A pack is opened at the union of its members' point sets. Structure-check
points therefore add evaluations for every column in a lifted pack. That
raises evaluation payload, native arithmetic and evaluation hashing, which
the 22–27 point count does not include.

### Expected effect (estimates)

- **Recursive verification.** A proof drops from thousands of points to
  roughly 60–85 with equal-height packs. The non-native MSM share of the
  terminal (about 60% of 735M cells) shrinks accordingly. Evaluation
  hashing remains, and in-circuit BLAKE3 over every evaluation is a large
  cost; native evaluation arithmetic and constraint DAGs remain as well.
- **Measured Aiur verification of a packed proof** (2026-11-13;
  `target/packed-shplonk/aiur/summary.json`). The Aiur packed verifier
  (`KzgPackedVerifier::verify_deferred`) checks the native packed proof of
  the matched execution. Its deferred pairing pair matches the native
  verifier, and forged openings, packs and witnesses are rejected.

  | Unpadded main cells | Per-column (8,978 points) | Packed (60 points) |
  |---|---:|---:|
  | Total | 581,368,823 | 146,620,018 (÷4.0) |
  | G1/MSM | 349.4M | 2.8M |
  | BLAKE3/transcript | 145.3M | 98.0M |
  | Byte reading + memory | 75.1M | 41.0M |

  After packing, cost follows the *number of evaluations and key bytes*, not
  points. The packed verifier hashes about 480 KB of evaluations (11,029
  requested plus 3,964 extra) and a 369 KB key, at roughly 100 cells per
  hashed byte. So column count still matters, through evaluation hashing.

  Next levers:
  - Fewer columns, from §7 grouping (6,304 → 2,510 points measured on Init)
    and source factoring. This shrinks evaluations proportionally.
  - Pack planning by next-row use, removing most extra evaluations (about 10%).
  - A constant predecessor key in the terminal, removing key hashing.
  - Cheaper BLAKE3 per byte in Aiur, for example several bytes per row as in
    PR 665.
- **Actual Init, grouped and packed** (2026-11-13;
  `target/packed-shplonk/init/summary.json`).
  - **Configuration:** best grouping policy
    (`p-sep16-splitB-coldA-in-reuse`), lookup quotient budget 4, and packed
    SHPLONK under a development SRS of `2^23`, on CPU.
  - **Proof:** the Init CompressBN proof has 159 variable G1 points (100
    main, 35 lookup, 22 quotient, 2 opening). That compares with 2,510
    per-column under the same grouping and 6,325 for the fresh baseline. It
    is 114,705 bytes, with 3,266 requested plus 47 extra evaluations.
  - **Prover:** 650 s and about 120 GiB peak (commitments 391 s), against
    79 s on GPU for the per-column prover. The packed PCS has no GPU path
    yet.
  - **Aiur verification:** 90.4M unpadded (147.5M padded) main cells,
    maximum height `2^21`. That compares with roughly 615M for today's BN
    stage on per-column proofs. The verifying key's hashing and parsing take
    about 53M cells, evaluation absorption about 12M, and the MSM over 159
    points 6.1M.
  - **Remaining levers:**
    - a constant predecessor key in the terminal;
    - fewer columns, hence fewer evaluations;
    - the terminal's PLONK lowering efficiency (about 8 constraints per
      cell through today's translator).
- **Packed prover on GPU** (`target/packed-shplonk/gpu/summary.json`).
  The Init packed proof takes 54.0 s to prove, against 79 s for the per-column
  GPU baseline. Commitments take 16.5 s and the opening 21.8 s. Peak RSS is
  45 GiB, set by witness generation. The proof is byte-identical to the CPU
  proof, and streaming lookups and quotients are opt-in for the packed config.
- **Generic packed-verifier PLONK sizing**
  (`target/packed-shplonk/terminal/summary.json`). This is not a complete
  terminal. The generic packed verifier checks the grouped and packed Init
  proof under the generic schema, with accumulator words public.
  - **Counts:** exact gnark compiles per circuit, scaled linearly per row,
    with the unused-maps reduction applied.
  - **Excluded:** the constrained pairing gadget (about 1.8M constraints in
    its smallest fixture), accumulator decompression to affine words, and the
    policy, statement and stage checks.

  | Variant | Aiur cells unpadded / padded | PLONK constraints | Domain |
  |---|---|---:|---:|
  | Key as data | 90.4M / 147.5M | 1,084,011,970 | `2^31` |
  | Key digest skipped (measured) | 49.1M / 84.7M | 610,575,097 | `2^30` |
  | Constant key (heuristic estimate) | 33.5M / 53.6M | 383,080,204 | `2^29` |

  Translation costs about 7.3 constraints per padded cell. `Blake3::compress`
  costs 3,686 constraints per round row, about 29k per compression across
  eight rows. The straight-line model (§9) gives 1,468 gates per round row,
  about 11.7k per compression plus byte lookups, so roughly 2.5× fewer, not
  15×. The MSM over 159 points costs about 45M.

  **Conclusion.** Packing makes the recursive stages cheap: 159 points, 115
  KB, 54 s to prove and 90M cells to verify. The terminal still needs three
  things:
  1. a last stage whose proof has tens of points and evaluations, meaning a
     narrow layout for that one stage (§5);
  2. a straight-line lowering of the terminal, not the per-row translation;
  3. a constant predecessor key.

  Packing keeps every earlier stage cheap, so option 2 is needed only for the
  last stage.
- **Terminal PLONK circuit:** see above; the remaining gap is about 26×. An earlier estimate here
  (4–5M cells, 32–40M constraints) omitted evaluation hashing, through the
  unsound committed-vector shortcut, and is withdrawn. The Aiur packed
  verifier's measured cells decide this; that measurement is in progress.
  Per-point MSM work (§6), cheaper evaluation hashing and a better terminal
  lowering (§5) all compose with packing.
- **Prover.** Commitment MSMs cover the same coefficients, plus zeros for
  lifted columns, which a sparse-aware MSM skips. Each opening adds two MSMs
  of up to SRS size (`W₁`, `W₂`) and linear-time divisions. The prover loads
  up to the full Ignition prefix (100.8M G1 powers, about 6.5 GB affine).
- **Proof size.** Dominated by evaluations, about 300 KB. Thousands of points
  go away. Final PLONK size is unchanged.

### Why the earlier packed experiment didn't show this

`aiur-compression-packed-experiment` (`kzg/packed.rs`) used the same
interleaved packing, but opened it with *binary coefficient folds*
(Gemini-style). That costs `log W` fold commitments per group plus per-group
witnesses: 346 folds and 309 witnesses in its actual proof. It also ran with
a `2^20` development coefficient cap, which allowed only small packs (67
trace commitments). Its 722 points therefore reflect that opening method and
cap, not packing itself.

### What it changes and what has to be proved

- **Rust:** a new opening path in `kzg/pcs.rs` and in multi-stark's PCS
  interface (commit packs, SHPLONK witnesses), plus the native verifier.
- **Aiur:** the KZG verifier source (`MultiStark/MultiStark/BN/KzgPcs.lean`
  and its transcript). This is Aiur source, so its correctness is proved like
  the rest of the verifier.
- **No change** to the Aiur compiler, its proofs, or program layouts.
  CompressGL and CompressBN keep their wide layouts; width now costs only
  cells.
- **Soundness argument:** standard KZG and SHPLONK (algebraic group model,
  q-SDH), plus:
  - uniqueness of interleaving;
  - degree bounds of `SRS/W` per column, tighter than today's;
  - Fiat–Shamir order: `[E]` and the commitments are absorbed before `γ` and
    `z`;
  - for lifted packs, the structure check above.

  This is a written argument, not new cryptography, but it needs independent
  review before adoption.

## 5. Option 2: narrow layouts

These keep per-column KZG and reduce the column count instead.

**2a. Static straight-line circuits.** Specialize a fixed-shape verifier into
one straight-line program, then lay it out in multi-stark's generic
`plonkish` relation: 3 advice columns, copy constraints as LogUp cycles over
fixed labels, and fixed tables. The hand-written stages use that layout; only
their gadgets are hand-written.

The verifiable route extends the existing pipeline:

1. **Certified source transformations.** Extend `Aiur/Aiur/Inlining` to unfold
   recursion bounded by configured lengths, to select match arms on constants
   and constructors, to propagate constants, and to forward stores to loads.
   Today's inliner rejects recursive cycles. Shape values are pinned by added
   source assertions.
2. **The existing verified compiler and certified optimization passes**
   (propagation, constraint elimination, degree reduction, allocation).
3. **A narrow layout adapter.** Place the compiled polynomial constraints and
   fixed-table lookups into the three-wire layout, with a proof that it
   preserves the compiled relation. Inlining alone yields fewer but wider
   logical circuits; this adapter is what turns wires into rows.

Witnesses still come from the existing runtime. Steps 1 and 3 need new proofs
(recursion unfolding, memory resolution, layout), which is months of Lean
work. Execution bytecode (`Aiur/Aiur/Execution`) has no theorems relating it
to source, so circuits must not be derived from bytecode. A bytecode partial
evaluator is acceptable only as a measurement tool.

Measured estimate for the matched KZG verifier: 8,704,685 gates and 1,500,951
table lookups (§9), versus 5,335,559 gates and 1,891,808 lookups hand-written.

The audit (§8) found that the KZG verifier needs small source changes and the
FRI verifier needs redesign before this applies.

**2b. Per-function gate templates with dynamic calls.** This is a hybrid not
covered by the census. Each function's verified one-row circuit is flattened
into a fixed gate template spanning several narrow rows, with copy
constraints inside the template. All templates live in one shared narrow
trace, each function in a region of configured capacity. Calls, memory and
fixed maps stay LogUp messages with today's verified semantics.

- **Kept:** dynamic call counts within capacities, memoization, recursion and
  memory semantics.
- **Avoided:** inlining, unrolling and memory resolution, so step 1 above
  disappears.
- **New:** the per-template flattening proof, region placement, and messages
  wider than a narrow row. Arities go up to 260; arity 3 dominates the census
  at 144M of 236M packets. Wide messages need invocation-ID chunking with
  uniqueness obligations, or a medium width of 8–16 advice columns.
- **Commitments:** tens, plus fixed columns.
- **Cells:** about the inlined gate count plus message rows plus capacity
  slack.

**2c. A narrow VM.** Rejected by the census: a dynamically scheduled scalar
instruction VM extrapolates to 110B cells for the terminal.

## 6. Option 3: cheaper commitments

Each of these is independent of options 1 and 2:

- **MSM algorithm.** Windowed Straus with per-point tables, GLV decomposition
  (BN254 has an efficient endomorphism), and merged add/double. G1 add's
  guarded `double` arm currently doubles its residualized cost. Roughly 2–4×
  per point.
- **Short batching scalars.** Independent 128-bit batching challenges instead
  of powers of one challenge halve per-point additions. This is a transcript
  change with a standard soundness bound.
- **Fixed bases.** Key commitments are fixed points when the key is constant,
  as in the terminal specialized to its predecessor key. Precomputed tables
  remove doublings.
- **Terminal key as constants.** This removes in-circuit key hashing and key
  graph interpretation. The terminal is not verified recursively, so it may
  embed its predecessor key.

Applied to today's 4,400 points, these alone are not enough. Applied to a packed proof's 25–85 points, they are what bring
the terminal toward `2^24`.

## 7. Protocol-preserving layout levers

These keep per-column KZG and the existing compiler. An earlier draft
dismissed them as "5–10× at most". That was not established: it looked at
hot functions, but most commitments sit in rarely executed wide circuits.

**Commitments are concentrated in cold circuits.** Saved grouped Init BN
profile (`target/prefix-init-grouping/init-grouped/report.json`): 74
circuits, 6,304 points (4,740 main), 552.8M main cells.

| Circuits kept as is | Their points | Points left if every other circuit merges into one circuit at today's widths |
|---|---:|---:|
| height > `2^16` | 1,173 (main 934) | about 2,223 |
| height > `2^18` | 441 (main 347) | about 1,491 |
| height > `2^20` | 98 (main 59) | about 1,148 |

Circuits of height `2^16` or less hold 80% of main commitments but only 5.7%
of main cells. One group with eight padded rows contributes 623 main, 425
lookup and 2 quotient commitments. The merged figures are dominated by the
widest cold circuit. Shrinking cold widths moves the floor toward the hot set:
441–1,173 points, or 5–14× fewer than today, before any narrowing of hot
circuits. These are layout counts, not measured proofs.

Candidates, which can be combined:

- **Source factoring and inlining policy.**
  - Cold functions with large inline expansions should call small reusable
    helpers instead. For example, `CompressBN::fold` builds its transcript
    with inline byte serialization: 621 columns for one row.
  - Extraction can be certified by checking that inlining the helpers
    recovers the original program (`Prepared.entry_iff`,
    `Aiur/Aiur/Inlining/Program.lean`).
  - Trades a few more rows for far fewer distinct columns. Helpers must be
    reused and deduplicated, or extraction just adds circuits.
- **Less restrictive grouping.** Function grouping keeps some columns private
  to avoid raising constraint degree, and lookup grouping
  (`aiur_backend/kzg/circuits.rs`) never raises a circuit's quotient degree.
  Both are performance policies, not requirements.

  Count-only, on the terminal graphs, lookup-plus-quotient columns are:

  | Quotient-degree policy | Lookup + quotient columns |
  |---|---:|
  | preserve each circuit's degree | 2,602 |
  | allow up to 2 | 1,959 |
  | allow up to 4 | 1,374 |

  Main columns are unchanged. Larger quotient domains and grouped constraint
  evaluation cost time, which must be measured.
- **Fixed-capacity stacking.** Rarely executed function traces occupy
  predefined regions of shared columns. Costs capacity padding and fixed
  columns.
- **Selective narrowing or tiling.** Distribute a wide, rarely executed
  compiled circuit over several rows of moderate width, reconstructing its
  logical row through constrained wiring. This is §5's 2b, applied only where
  it pays. Frequent compact functions keep today's layout, and memoization
  and dynamic calls are preserved.
  - The obligation is "a valid physical trace reconstructs valid rows of the
    existing circuit", after which the existing compiler theorem applies.
  - Boundary calls, results and ROM payloads must be counted.
  - Three columns isn't necessarily optimal; a moderate width may balance
    commitments, rows and routing better.
- **Local specialization of structural parameters.** Remove key
  interpretation and statically known control flow in the functions where it
  costs columns, without flattening the whole verifier.

What these routes can reach for the terminal is unknown. 441–1,173 points is
far below today's ~4,400–6,300, but well above the hand-written ~28. Reaching
`2^24` would then also need cheaper per-point arithmetic (§6), narrowing of
hot circuits, or the packed openings of §4.

## 7a. Other levers considered
- **Pipeline order.** Keep wide layouts under Goldilocks FRI. With option 1,
  wide KZG stages become affordable; without it, every BN254 KZG stage must be
  narrow (option 2).
- **Out of scope:**
  - multilinear/sumcheck backends (HyperKZG, jagged PCS, LogUp-GKR), a
    larger protocol change;
  - Poseidon2 wrappers (excluded);
  - custom-gate final provers (not stock gnark);
  - a hand-written narrow tail (not Aiur source).

## 8. Residualization audit (applies to option 2a)

This is a read-only audit of the KZG verifier and terminal
(`MultiStark/MultiStark/BN`, `CompressFinal.lean`) and of the Goldilocks FRI
verifier.

**KZG verifier and terminal: feasible with small source changes.**

- **Structural lengths are unconstrained hints.**
  - `kzg.io.length` (`KzgIO.lean:23`).
  - Counts, active flags, per-circuit `logs` and dimensions, read through
    `KzgIO::u32` and `KzgIO::tag`.

  These must be pinned by configuration.
- **Key graph interpretation must be constant.** `KzgDeserialize::node` and
  `eval_at` dispatch on node structure. Commitment points, `Const` values,
  anchors and digests stay data.
- **Witness-length MSM list.** `KzgMsm.lean:54` conses only nonzero digits; it
  should select from a fixed table.
- **Stage selection.** The terminal's `kzg.final.stage` needs separate entries
  or pinning.
- **Pointers.** No ROM pointer is hashed, compared or used in arithmetic.

**FRI verifier: needs redesign before option 2a.**

- **Merkle multi-opening.** `Modules/Mmcs.lean` deduplicates query indices, so
  its shape depends on Fiat–Shamir collisions.
- **Rejection sampling.** `ch_sample_field` is unbounded.
- **Wrapper output.** `CompressWrap` doesn't pad to configured heights. The
  hand-written path fixes the root layout in Rust (`pipeline/root.rs`).

## 9. Measurements

**Matched KZG verifier, straight-line gate model** (2026-11-13; count-only, no
proving).

- **Input:** `aiur_verifier_comparison` on the current `kzg-source.ixa`
  fixture. Both verifiers check one natively verified development proof
  (62 + 3 MSM bases).
- **Model:** the compiled constraint graphs were dumped. The census's
  demand-driven affine model (`target/narrow-layout-census/fused.py`) was
  applied per function instance, with exact dynamic call counts from
  re-execution: 258,075 calls for 235,543 unique invocations. Fixed-map calls
  count as table lookups; function calls and ROM accesses count as wiring.

| Verifier | Gates | Lookups |
|---|---:|---:|
| Hand-written | 5,335,559 | 1,891,808 |
| Straight-line Aiur (model) | 8,704,685 | 1,500,951 |
| … with G1 add's `double` arm always emitted | 10,687,234 | — |

The ratio is 1.63–2.0×. BLAKE3 accounts for about 2.3M of these gates: 1,468
gates and 224 byte lookups per round row, and eight rows per compression.

**Packed Init verifier, straight-line gate model**
(`target/packed-shplonk/terminal/straightline.json`). Same model, applied to
verifying the grouped and packed Init CompressBN proof.

| Variant | Gates | Map lookups |
|---|---:|---:|
| Key as data (measured) | 206,064,797 | 16.7M |
| Key digest skipped (measured) | 109,016,276 | 6.9M |
| Constant key (estimate) | 77,303,759 | 6.0M |

With a constant key, two items dominate:
- `Blake3::compress`: 27.5M gates, about 2,345 compressions of transcript
  absorption. The generic packed verifier hashes the key and claims, not the
  proof blob, so there is no duplicate proof hash to remove.
- `KzgAlgebra::eval_at`: 23.1M gates, interpreting the key's constraint
  graph node by node.

A true constant-key specialization compiles that graph into about 12,000
direct field operations. Within this model that leaves roughly 54M gates
before the excluded pairing, accumulator and policy checks: about `2^26`,
at Ignition's limit, and about 3× over `2^24`. G1 add's guarded `double`
arm adds about 4.6M more.

These are heuristic estimates, not bounds. Subtracting standalone
key-parsing rows can remove memoized invocations that proof verification
also needs. The recorded call counts don't include descendants duplicated
once memoization disappears. Only counting an actual specialized program
settles the figure.

**Hand-written FRI stage on Init:** 43,758,979 gates, 14,713,168 lookups and
119,894 BLAKE3 compressions (`aiur-compression-goldilocks.json`).

**Packed counts:** see §4. Scripts are in the session scratchpad and can be
re-created from the profile JSON.

## 9a. Trace size: Aiur versus the hand-written verifier

Matched per-component comparison, same development proof (2026-11-13;
`target/overhead-research/summary.json`, `matched_table.json`). [M]
measured, [E] estimate.

| | Hand-written | Aiur | Aiur / hand-written |
|---|---:|---:|---:|
| Main cells, unpadded [M] | 22.7M | 4.97M | 0.22 |
| Main cells, padded [M] | 27.3M | 7.38M | 0.27 |
| Committed cells (main + lookup + quotient) [M] | 81.8M | 11.9M | 0.15 |
| Commitments [M] | 12 | 9,277 | ~770× |

Aiur's arithmetic is already more compact than the hand-written circuit:

- **Per operation:** G1 add is 385 cells against 2,016; an MSM base is about
  39K cells against 228K.
- **BLAKE3:** a compression is 4,016 cells against 12,470 rows of 4-bit
  pieces.
- **Why the hand-written circuit is large:** it puts every gate and copy wire
  in a full 3-column row and pays lookup and quotient cells per row.
- **Distance from a bespoke design:** an estimated 1.5–2× for G1 add [E];
  BLAKE3 is at about bespoke level.

The losses are representational:

1. **Commitment count:** 9,277 against 12. Packed openings (§4) address it.
2. **Key as data:** hashing and parsing the key, and interpreting its
   constraint graph. On the packed Init verifier this is 42.7M unpadded
   cells, 47%: 7,125 of 9,458 compressions plus most of the 16.6M
   byte-reading cells. The hand-written verifier compiles the key in.
3. **Byte-at-a-time streams:** about 58 cells per byte of list and memory
   plumbing, against 63 per byte of compression. About 33M cells on packed
   Init.
4. **Power-of-two padding per circuit:** 1.48× matched, 1.63× packed Init,
   about 1.6× terminal. `range80` alone wastes 44M cells in the terminal.

Smaller inefficiencies, where Aiur still wins overall:

- **Fq range and canonicity checks:** 27% of main cells and about 49% of
  lookup cells.
- **Arguments materialized in both caller and callee:** 32% of function
  cells. In G1 add, 115 of 141 columns feed lookups.
- **Lookups with only constant arguments:** about 554K padded lookup cells
  in G1 add and double.

**Ranked general changes** (estimates; they overlap and are not additive):

| Change | Packed Init effect [E] | Cost | Formal impact |
|---|---|---|---|
| Bind the predecessor key without hashing or parsing it in circuit: a preprocessed key table fixed by the verifying key, or certified specialization (§10) | −55M unpadded (−61%) | medium–high | one verifier identity per predecessor key; specialization needs its refinement proof |
| Shard large circuits into 2–3 power-of-two pieces (cheap once commitments are packed) | −50M padded | low–medium | backend lookup-balance argument |
| Word- or block-level byte streams instead of per-byte list rows | −28M | medium | stream-encoding lemmas |
| Inline Fq leaf range and relation helpers; bounded non-canonical intermediates | −2M (terminal about −95M) | low–medium | inlining preserves meaning; new bound lemmas |
| Fold constant-argument lookups at compile time | about −1M lookup cells (terminal −63M) | low | trivial |
| Split rarely taken branches out of wide rows | about −3M | low–medium | preserves meaning |

Not recommended:
- **A `2^20` range table:** its fixed cost exceeds the savings at these sizes.
- **Raising the quotient-degree budget alone:** it doesn't remove argument
  columns.

A field-native hash for the transcript was suggested and is excluded
(Poseidon2 is out of scope). Rough combined effect on packed Init [E]: about
30M padded cells, against 147.5M today.

## 10. Normalization point and specialized tail

Variable shapes enter at the front of the pipeline. A Mathlib root and an
Init root have different trace heights, so the Goldilocks stages and the
first BN stage verifying the Goldilocks proof differ too. They should not
need to vary after that. But the shape also won't settle by itself:

- Each BN stage's trace heights depend on the shape of the proof it verifies
  (active circuits, heights, and so packs and evaluations). Once every stage
  verifies a small packed proof, those differences should shrink to the same
  power-of-two heights. The pipeline design deliberately doesn't assume this
  (`aiur-compression.md` §3.2), and it hasn't been measured.
- Even for one predecessor shape, execution counts vary slightly with proof
  values. Examples are zero MSM digits, infinity branches in G1 arithmetic and
  memoization hits, which can cross a power-of-two boundary.

So the pipeline gets one explicit **normalization point**, as the hand-written
path normalizes its root layout (`pipeline/root.rs`). That point is the **last
BN stage**:

1. **Fixed shape.** The backend configuration fixes that stage's circuit set
   (all active) and each circuit's capacity, with headroom. Capacities are
   versioned configuration, never read from an observed proof.
2. **Admission.** The prover pads every circuit to its capacity. An execution
   that exceeds a capacity is rejected as an admission error; the shape is
   never adjusted to fit.
3. **Specialized verifier.** The stage's key, and therefore the shape of its
   proof, is constant. The terminal is compiled against that constant key and
   shape.

Placing it last keeps padding cheap: by then every input is a small packed
proof, so Init and Mathlib should need nearly the same capacities. Everything
before it stays size-agnostic, which is where Aiur's dynamic layout earns its
place: IxVM, aggregation, Goldilocks stages and earlier BN stages.

**What becomes possible after it.** Stages after the normalization point see
one fixed predecessor shape and key. They can therefore be specialized for
performance without hand-written circuit code:

- **Terminal (required).** Certified specialization (§5, 2a) of the packed
  KZG verifier against the constant key and shape, lowered to straight-line
  gnark gates. Specialization folds constraint-graph interpretation (23.1M
  gates in the constant-key estimate) into about 12,000 field operations.
  - Heuristic estimate: roughly 54M gates before the pairing, accumulator
    and policy checks (§9), about `2^26`. Reaching `2^24` therefore needs
    the optional last-mile stage below, or fewer evaluations and cheaper
    transcript hashing.
- **A specialized last-mile stage (optional).** If the terminal must reach
  `2^24`, one more stage after the normalization point could be specialized
  the same way and laid out narrowly (multi-stark `plonkish`). Its proof
  would have tens of points and evaluations, as the hand-written recursive
  stage's does. Both specialized stages use the same certified
  specialization; only the backend differs.
- **No change to soundness assumptions.** Specialization only removes
  dynamic flexibility the configured shape doesn't use. Pinning a shape value
  adds an assertion, and correctness rests on the certified transformation
  and the existing compiler proofs.

**Measurements needed first:**
- the shape of successive packed BN stages on Init: whether heights stop
  changing after one or two stages;
- the same on a second, larger workload (Mathlib, or a large saved root),
  to size capacities and headroom;
- the padding cost of the configured capacities against unpadded execution.

## 11. Status and plan

Done (2026-11-13), all count-only or development-setup measurements:

- Grouping, including shared BLAKE3 rounds and commitment-aware cold groups,
  and lookup quotient budget 4: the actual Init BN proof goes from 6,304 to
  2,510 points with an identical accumulator.
- Packed SHPLONK KZG:
  - native prototype, GPU prover (Init 54 s, 45 GiB) and Aiur verifier;
  - the grouped Init BN proof has 159 points and 115 KB, and costs 90.4M
    cells to verify, against about 615M.
- Packed BN stages on actual Init under Ignition (`2^26`), five
  consecutive stages, GPU (`docs/measurements/aiur-packed-bn-stages.json`):
  - stage one and later stages are separate programs and keys
    (`CompressBNPacked::first_v1` with the per-column verifier,
    `compress_v1` with the packed verifier only), both pinned by a packed
    policy (`IXAUKP01`);
  - word-level streams merged, transcript and digest bytes unchanged;
    grouping policies updated for the new word and packed-verifier
    functions;
  - function-circuit sharding with copy counts fixed in the key;
  - steady-state verification 263.7M → 161.8M padded main cells
    (129.6M unpadded), 115–124 KB proofs, 60 points, 10–14 s to prove;
    stage one 636M → 607M padded. Shapes stop changing at stage 3 or 4.
- Packed CompressGL, so the first BN stage is the steady program
  (`docs/measurements/aiur-packed-bn-stages.json`, run `g1_packed_gl_chain`):
  - CompressGL on the actual Init root proven with packed SHPLONK (lookup
    budget 4, `2^26`, two-copy sharding): 87 points and 207 KB against the
    per-column 376 KB; 55 s to prove against 47 s, peak RSS 110 GB against
    107 GB;
  - one BN program, `CompressBNPacked::chain_v1`, under a two-key policy
    (`IXAUKG01`: packed GL key at stage one, its own key afterwards), so
    `first_v1` and its key disappear. Stage one verifies the packed GL proof
    in 256M committed main cells against 607M, with 4 s execution against
    42 s and 13 s proving against 35 s;
  - stages 2–4: 168–170M committed, 121 KB proofs, 60–63 points, 10 s.
    Shapes still change between stages 3 and 4 (one circuit at a
    power-of-two boundary), so the normalization point remains necessary.
- Terminal sizing:
  - per-row translator: 383M–1,084M constraints;
  - straight-line model with a constant key: 77.3M gates, roughly 54M after
    specialization of graph interpretation (§9). These are heuristic
    estimates, excluding the pairing, accumulator and policy checks.
- Terminal reductions on the steady packed BN proof (`i3-shard2` stage 3;
  exact gnark counts, `target/terminal-reduction/summary.json`, pairing
  check excluded). The generic verifier costs 781M constraints
  (`2^30` domain).
  - Exact per-circuit capacities in the PLONK exporter and translator:
    476M (`2^29`). Fixed tables keep their power-of-two height, and rows
    past the execution are zero rows.
  - Fixed-key terminal (`KzgPackedTerminal::verify`): 252M (`2^28`). The
    key bytes are a fixed table of the terminal's own circuit and are still
    parsed in circuit, but no longer hashed.
  - Inlining the Fq range leaves: −3.2M on the terminal, −0.8% padded cells
    in the verifier as used by a BN stage. Recorded as a patch, not applied.
  - Folding constant-argument lookups: at most −0.6M on this input, so
    skipped. It needs a compiler change that also keeps the execution's
    fixed-map counts consistent.
  - About 70M of the remaining cost is spent parsing the key, which a
    structured key table or specialization would remove. BLAKE3 transcript
    work is 73M.
- Terminal reductions, second round (same input and method;
  `target/terminal-reduction/summary2.json`):
  - Affine gate lowering in the PLONK translator (`aiur_plonk_lower.go`):
    each row's nodes become affine forms with fixed cells and selectors
    folded, a product of two affine operands is one gate, an asserted form
    with n atoms takes max(1, n-2) gates, a sole-use product fuses with its
    assertion, and lookup constants move into the shared fingerprint base.
    The fingerprint exponents are rotated so the first non-tag argument has
    exponent zero. 252M → 201M.
  - Structured key tables: the export parses the key's circuits section with
    the in-circuit grammar's checks and stores nodes, roots, lookups and
    shapes as fixed tables; the terminal rebuilds the circuit list from them
    and evaluates the constraint graph straight from the node table (a
    terminal copy of the graph-evaluation functions). 201M → 130M (`2^27`).
  - Inlined Fq range leaves applied, fixtures regenerated: 128.1M. The BN
    stage verifier's padded cells drop 0.8%.
  - Remaining: BLAKE3 transcript absorption 66M (2,480 compressions of
    proof bytes, at about 3,330 gates per round row, of which 2,180 are
    lookup gates), graph evaluation 16M, G1/MSM 13M. Ignition's `2^26`
    needs fewer absorbed bytes or cheaper byte lookups, which are protocol
    or backend-gate changes rather than lowering.

Next, in order. Steps 1–3 can run in parallel; step 4 starts when step 1
lands.

1. **Productionize packed BN stages.** Wire the packed PCS into CompressBN
   (Aiur source verifier in place of the per-column one). Done in the
   development tree: split first/steady programs, packed policy, word
   streams, sharding; pins not yet updated.
   - Key-digest binding and policy pins.
   - Ignition loading for the packed config.
   - Pack planning by next-row use.
   - The written soundness argument, reviewed independently.
   - Fixture and verifying-key pin updates, with human review of the pins.
2. **Source factoring and grouping adoption** (in progress). Fewer columns
   mean fewer evaluations to hash at every packed stage.
3. **Certified specialization in Lean.** Extend `Aiur/Aiur/Inlining` with
   bounded unrolling, constant arm selection, constant propagation,
   store-to-load forwarding and pin assertions. Add the flattening to gates
   with its proof. Start on the terminal's verifier modules; this depends
   only on the fixed-shape interface, not on final capacities.
4. **Normalization point.** Measure stage-shape convergence on Init and a
   larger workload. Then implement configured capacities, all-active
   padding and admission rejection for the last BN stage, and pin its key.
   Start once step 1 provides real packed BN stages, since capacities depend
   on the packed verifier program.
5. **Specialized terminal.** Compile the terminal against the normalized key
   and shape (step 3's specialization, gnark backend). Measure constraints,
   then add the optional specialized last-mile stage if `2^24` requires it.
6. **Init E2E, then Mathlib, through `ix bench run`**, against hand-written
   parity:
   - final PLONK `2^24`–`2^25`, with proving time near the hand-written
     11 s;
   - compression wall time comparable to the hand-written 403–1,317 s
     (warm/cold);
   - ≤ 320k gas, measured on the EVM.
