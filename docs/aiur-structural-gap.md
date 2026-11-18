# The structural gap between Aiur and hand-written compression

> **Historical (2026-11-15).** This document is an analysis that led to the narrow backend and the stage ladder. The current pipeline is described in [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status: analysis for review. Measurements are cited; everything else is
marked as reasoning or estimate. Companion to
[aiur-narrow-recursion.md](aiur-narrow-recursion.md).

## 1. Summary

The recorded hand-written pipeline ends in a 1,909-byte recursive KZG packet
and a complete 14,689,424-constraint (`2^24`) gnark PLONK circuit. The packed
Aiur chain produces roughly 121–124 KB KZG proofs. The complete packed
terminal relation (`CompressFinalPacked::verify_accumulator_v1` with the
gnark pairing contract) measures 130,069,850 constraints (`2^27`) on the Init
packed-GL chain at exact execution capacities with no headroom, after the
accumulator fold weight moved to the verifier transcript (193,301,681 and
`2^28` with the earlier proof-digest fold). It is not a
completed Aiur PLONK endpoint: no key setup or proof was run at that size.
Sources and scopes are separated in §2.

The structural gap has two parts: **the proof interface passed to the next
stage**, and **the execution work that the next circuit must prove**. The
cell comparisons suggest Aiur represents local arithmetic compactly, but
they do not establish that arithmetic or lookup cost is already optimal.

- **Wide versus narrow.** Aiur's current backend gives each function or
  certified group its own columns, with one row per distinct invocation.
  Not every local expression becomes a column: arithmetic expressions and
  certified elimination already avoid many of them. The hand-written
  recursive stage uses a three-advice-column computation trace and one
  merged table. Its program coefficients and wiring live in preprocessed
  columns, so the next verifier checks a small generic gate relation rather
  than a separate relation for every helper function. Proof cost depends on
  commitments, evaluations, circuit descriptions and opening domains; total
  predecessor cells alone do not determine it.
- **Dynamic and generic versus fixed and specialized.** Aiur's general
  recursive stages read keys as data and accept dynamic shapes. Its fixed-key
  tail removes some of that work but still interprets the key graph. The
  hand-written pipeline normalizes the root's layout first, then runs a short
  ladder of distinct circuits, each compiled against its predecessor's fixed
  shape.

The terminal adds another distinction. The hand-written gnark circuit
directly expresses verification arithmetic. The Aiur-to-PLONK frontend
checks an Aiur execution trace, including calls, memory, activation and
lookup multiplicities. Better polynomial lowering reduces the cost of those
checks without removing the underlying execution obligations.

## 2. Measured comparison

The matched development-proof comparison measures the two verifiers on the
same input proof. It is separate from the full-pipeline measurements below.

| Matched development proof | Hand-written | Aiur | Source |
|---|---|---|---|
| Main cells, matched verifier | 22.7M (27.3M padded) | 4.97M (7.38M padded) | overhead research, §9a of the companion doc |
| Committed cells, matched | 81.8M | 11.9M | same |
| Main + lookup + quotient columns | 3+1, 4+1, 2+1; 12 total | 9,277 per-column | same; excludes fixed-key commitments and opening witnesses |

The full-pipeline records establish endpoint size and the remaining gap;
they are not a matched timing comparison of verifier implementations.

| | Hand-written endpoint | Packed Aiur example |
|---|---|---|
| KZG packet | 1,909 bytes | 123,529 bytes on the `i3-shard2` steady-state fixture; about 121 KB on the newer packed-GL chain |
| Scalar evaluations | Dozens | 3,674 requested, zero extras on `i3-shard2` |
| Variable G1 points | Column commitments plus opening witnesses | 60 on `i3-shard2`, despite 3,042 main/lookup/quotient columns |
| Predecessor key handling | Fixed verification arithmetic and preprocessing commitments | Generic stages hash and parse the key; the fixed-key tail uses structured tables but still interprets the graph |
| PLONK constraints | 14,689,424, complete, domain `2^24` | 130,069,850, complete terminal relation, domain `2^27` (exact capacities; 206,074,931 and `2^28` at power-of-two capacities) |

Sources:

- [hand-written endpoint measurement](measurements/aiur-compression-incremental.json);
- [packed BN stages](measurements/aiur-packed-bn-stages.json), run `i3_sharding_k2`, stage 3;
- [fixed-key verifier sizing](../target/terminal-reduction2/r2-keygraph/summary.json),
  artifact `ac99be9d9931fe088a2d2c260ca6f50253c473a4d4d3ed88eb48c47d9f09e1c0`;
- [complete terminal sizing](../target/fold-transcript/summary.json),
  artifact `d715d0cefe46b2f6f7cc91fd56a30c618f9e5619383ebe46a4b3a1e6f58c4ba3`
  (transcript fold); the proof-digest fold's sizing is
  [target/terminal-complete/summary.json](../target/terminal-complete/summary.json),
  artifact `cf48db62e26ef75eeefb49d4e7f21959c368106417aa153a491dd7259f132e29`;
- [matched trace and component accounting](../target/overhead-research/summary.json).

The component accounting reports:

- G1 add: 385 cells against 2,016.
- An MSM base: about 39K cells against 228K.
- BLAKE3 compression: 4,016 cells against 12,470 rows.

The complete terminal adds, to the fixed-key verifier, the original
statement and `IXAUKG01` policy/stage binding, the carried-accumulator fold
and the 18 private affine outputs bound to gnark's `PairingCheck` with the
fixed Ignition anchors. On the same input (`gl-chain/run-k2`, stage-4
proof) the verifier alone is 126,667,514 (`2^27`, measured before the
verifier returned its transcript), so the integration costs 3,402,336:

| Increment over the fixed-key verifier | Transcript fold | Proof-digest fold |
|---|---:|---:|
| BLAKE3 | 79,933 | 62,364,700 |
| Pairing contract: `PairingCheck`, canonical-limb, infinity and curve checks, output binding | 1,796,045 | 1,796,045 |
| Fold MSMs, point encoding and other G1 work | 1,393,606 | 1,404,093 |
| Remainder: statement, policy, stage and claim checks, new fixed tables, small-capacity effects | 132,752 | 1,069,329 |
| Total | 3,402,336 | 66,634,167 |

The proof-digest fold hashed the 121 KB predecessor proof a second time for
`BLAKE3(proof)`. Every stage that verifies a packed proof now squeezes the
weight from the verifier's final transcript, which has already absorbed the
whole proof, after absorbing a domain tag, policy, statement, stage, key
digest and the four points; the soundness argument is
[aiur-packed-kzg-soundness.md §4a](aiur-packed-kzg-soundness.md). The same
change on a steady `chain_v1` stage (GPU run, Init root, three BN stages,
same sharding profile) reduced the stage's predecessor verification from
175.7–177.4M to 160.4M padded main cells (168.2–169.9M to 158.7M sharded),
from about 350M to 282M executed instructions and from about 94,300 to 74,500
`Blake3::compress` rows; the regrouped program's proof grew from about 121.2
to 122.6 KB (341 lookup columns instead of 310).

These figures compare trace representations, not PLONK constraint counts or
proving time. In particular, the BLAKE3 figures use different units. Calls,
copy constraints, lookup work and fixed columns must be included in a full
comparison before deriving a per-operation efficiency ratio.

## 3. Why width compounds

Let a stage's program have `C` committed columns. Its proof carries about `C`
evaluations per opening point. Without packing it also carries `C` points;
with packing, a few dozen points.

More precisely, scalar payload is the sum of `width × requested points`
over matrices and rounds, including fixed openings, plus extra pack
evaluations. Packing reduces curve commitments; it does not remove the
individual evaluations needed by the AIR checks. Next-row-aware packing
helps by avoiding extra values, rather than hiding the requested ones.

The next stage pays for each evaluation (hashed into the transcript and used
in constraint checks) and for each point (a non-native scalar
multiplication). When that next stage is the same program, as in Aiur's
self-recursive BN stage, its own trace includes that verification. So `C`
influences both the proof's width and the cost of the program's own trace,
and repeating the same wide verifier has a cost floor associated with its
own circuit family. Heights, activation, packing and proof values still
affect the result; convergence to one shape is not guaranteed.

The hand-written recursive stage keeps the main/lookup/quotient interface
near 12 columns by using a long, narrow trace. The computation need not be
small to produce a small proof interface. Current Aiur improvements affect
different parts of the cost:

- packed openings removed the per-column points;
- word streams reduce execution work;
- grouping reduces columns as well as changing cell and quotient costs;
- sharding reduces padding but can add columns and evaluations.

The `i3-shard2` runs retain 3,674 evaluations and a 123,529-byte proof from
stage 2 through stage 5. Repeating that stage does not yield the hand-written
packet size. In the latest fixed-key census, BLAKE3 round rows alone account
for about 66M constraints, graph evaluation about 16M, and G1/MSM about 15M.
The first figure is already above the entire `2^24` target; it is a measured
cost of the current implementation, not a lower bound for every BLAKE3
implementation. [Census](../target/terminal-reduction2/census-keygraph.txt).

Normalization fixes an admitted shape and makes specialization possible.
It does not, by itself, reduce the number of columns or evaluations. Final
PLONK proof size is a separate matter: with the same proof format and public
interface it remains succinct as circuit size grows. The obstacle is fitting
the complete verifier within the supported domain and proving-time budget.

## 4. What is and isn't fundamental

- **Width** comes from the backend representation (one row per distinct
  invocation), not from Aiur's semantics. It determines much of the next
  stage's proof interface.
- **Generic verification** (keys as data) comes from designing for universal
  self-recursion. The hand-written pipeline avoids it by normalizing the root
  and using a fixed ladder of stages.
- **Byte-level data handling** is a verifier-program choice, already partly
  replaced by word streams.
- **Execution-trace checking in PLONK** preserves general calls and memory.
  Static wiring and specialized arithmetic can remove some of that work,
  but the existing gate optimizations alone do not establish such a change.

## 5. Direction: the existing compiler emits a narrow representation

Candidate direction: extend the existing compilation pipeline with a
**narrow physical layout pass** over its verified per-function circuits. A
function's logical row becomes a fixed template: a sequence of narrow rows
over a small shared width `W`. The reference circuit compiler and its
source-correctness theorems remain the logical interface; this does not
require a replacement frontend or language semantics.

- **Template wiring:** fixed by the compiler, enforced as copy constraints
  with fixed labels, as multi-stark's `plonkish` lowering does.
- **Calls, memory and memoization:** remain lookup messages with today's
  semantics. Dynamic execution, memoization and keys as data survive.
- **Correctness:** the obligation is "a valid physical template trace
  reconstructs a valid row of today's per-function circuit". The existing
  theorems then connect it to source semantics. The physical-layout
  refinement is a new proof obligation even if the pass lives inside the
  existing compiler. Correctness does not follow merely from reusing its
  input representation.

This is a candidate to compare with targeted source factoring, selective
narrowing and specialization of known verifier components. The measurements
in §7 should precede choosing a general template backend.

Supporting changes:

- choose an explicit normalization point with measured capacity and padding
  costs; the earliest possible point is not necessarily the cheapest;
- use constant keys wherever a stage verifies a fixed predecessor (the
  fixed-key terminal already does this);
- use typed proof inputs where possible, while reconstructing and checking
  every canonical encoding that the transcript, accumulator fold or statement
  binds.

The target stage ladder that combines this direction with normalization and
verifier plans is in §5b.

## 5a. Preprocessed verifier plans for fixed stages

Preprocessing removes some generic verification work within the existing
architecture. It is important to distinguish three levels:

1. **Fixed key bytes:** eliminate hashing an untrusted key, but still parse
   its bytes in circuit.
2. **Structured fixed tables:** eliminate most parsing; graph operations
   and their operands are still fetched and evaluated by an Aiur program.
3. **Compiled verifier arithmetic:** emit the known graph's arithmetic and
   wiring at artifact construction, so no graph interpreter is proved at
   run time.

The latest implementation reaches level 2. A table-driven verifier plan is
useful, but does not automatically provide level 3.

The hand-written pipeline compiles a `Plan` from its predecessor's trusted
verifying key, claim schema and shape
(`recursive/native_verifier/plan.rs`). Everything that depends only on the
key becomes circuit constants, and the circuit does only proof-dependent
work.

Aiur can preprocess any stage whose predecessor key and shape are fixed by
configuration: the terminal, and any stage after the normalization point.
The stage's program reads a **verifier plan** from fixed tables computed when
the artifact is built. This removes key-byte hashing and parsing. A flat
operation table can reduce traversal overhead, but reading an opcode and
dispatching on it is still interpretation.

**Plan contents:**

- the predecessor key in parsed form: circuit list, shapes, lookup
  structure, pack layout;
- each predecessor circuit's constraint graph as a flat operation table,
  with authenticated operand indices and ordering;
- the transcript state that depends only on the key: seed, and anything
  absorbed before the first proof-dependent value;
- domain constants per trace height;
- precomputed multiples of the predecessor's fixed commitments, making those
  MSM terms fixed-base table lookups.

**What can be reused:** the verifier's transcript, AIR algebra, opening
reduction and curve libraries. The program must still be adapted to consume
the plan. The current `KzgPackedTerminal` has a table-based graph evaluator;
its equivalence to the generic evaluator is a separate obligation from
correct compilation of either program.

A focused alternative for level 3 is to generate ordinary Aiur arithmetic
from the trusted constraint graph: an `Add(a,b)` node becomes the addition
of the already-generated operand expressions. A generic graph-evaluation
equivalence theorem could certify this transformation, followed by the
existing Aiur compiler. This is narrower than a general whole-program
residualizer. It removes graph interpretation, not proof-dependent hashing
or all dynamic calls and memory operations.

**Binding and soundness.** The plan is part of the stage's own verifying key,
since fixed tables are committed in the key, so it can't be swapped. Two
ways to establish that the plan corresponds to the pinned predecessor key:

1. **A Lean plan function (preferred).** Compute the tables with a Lean
   function `plan(K)` while building the artifact, and prove that if the
   stage's tables equal `plan(K)`, its verifier computes the same deferred
   pairing obligation as verification under `K`. Acceptance equivalence
   also includes discharging that obligation. This requires verification of
   the Lean plan function and the program that reads its output.
2. **An in-circuit relation to the authenticated key.** Constrain the plan
   to be the checked projection of the key whose digest is verified, or
   check a canonical plan encoding that reconstructs that same key.
   Hashing the original key alone does not bind a separately supplied plan
   to its semantics. This route must count the parsing or encoding checks
   it retains and may give up much of the saving.

**Measured progress and remaining opportunities:**

- fixed key bytes plus improved PLONK lowering: about 201M constraints;
- structured key and graph tables: about 130M, a further reduction of
  about 71M on the same input and sizing method;
- graph evaluation still costs about 16M. Compiling the graph into
  arithmetic could remove much of that interpreter cost, but the generated
  arithmetic and its wiring are not free;
- precomputing fixed-base MSM data is another opportunity, not a measured
  saving in these figures.

The fixed-key verifier (`KzgPackedTerminal::verify`) currently checks a proof
under its embedded key and returns the outer deferred pairing operands.
The complete terminal must additionally bind the original statement and
policy/stage, handle the predecessor's accumulated pairing obligation, and
discharge the required pairings. `CompressFinalPacked` (§2) now does all
three; the integration costs 66.6M constraints on the same input, mostly for
hashing the predecessor proof into the fold.

**What plans don't address:** proof width. The terminal still absorbs
thousands of claimed evaluations because those are proof data. The latest
census attributes about 66M constraints to BLAKE3 round rows alone. The
hand-written endpoint benefits from both preprocessing and a narrow
predecessor proof; neither a fixed key nor a table-driven plan supplies
both properties.

**Open questions:**

- **Ownership:** whether the plan function belongs with the Aiur library or
  the compression programs, and who maintains its proof.
- **Recomputation:** plans are recomputed whenever the predecessor key
  changes, so tie their artifacts to the key digest in the fixture checks.
- **Self-recursion:** naively embedding the complete own key creates a
  circular key derivation. The present construction does not solve that
  problem. Use these plans at a boundary with an independently fixed
  predecessor, such as a short ladder of distinct stages after normalization.

## 5b. Target architecture: the hand-written stage ladder, generated from Aiur

The measurements keep converging on the hand-written pipeline's stage
structure. Each of its stages exists for a reason the Aiur pipeline has now
rediscovered, and each reason can be met with Aiur source and the existing
backends, plus the narrow template backend (§5). The target is that
ladder. Hand-written circuit code is not part of it.

**Hand-written Init reference** (`docs/measurements/aiur-compression-incremental.json`;
cold/warm per-stage times from that run's logs under
`ix.ci-merge-tests/target/aiur-compression-stages-run/wrapper-{init,alt}`):

| Hand-written stage | Purpose | Cold | Warm |
|---|---|---:|---:|
| Wrap (`CompressWrap`, Goldilocks), layout normalized | Fixes shapes first, where padding is cheapest | 25 s | 25 s |
| FRI stage: narrow Goldilocks circuit verifying the wrap | Narrow output, so the first KZG stage's per-query leaf hashing is cheap | ~94 s | ~94 s |
| First KZG stage: narrow, 2^26 rows | Moves to BN254 cheaply because its input is narrow | 366 s | 48 s |
| Recursive KZG stage: narrow, fixed | Gives the terminal a tiny, fixed-shape proof (1,909-byte packet) | 290 s | 50 s |
| PLONK, `2^24` | On-chain endpoint (864-byte proof, about 292k gas) | ~36 s | ~36 s |
| **Total** | | ~1,317 s | ~403 s |

The cold times are dominated by committing the narrow stages' large fixed
columns. That depends only on the circuit and is cached across runs.

**Target Aiur ladder:**

| # | Stage | Layout | Status |
|---|---|---|---|
| 1 | Root (IxVM aggregation) | dynamic Aiur, Goldilocks FRI | exists |
| 2 | `CompressWrap`, normalized output | dynamic Aiur, Goldilocks FRI; pads to configured capacities, fixed shard count, all circuits active | candidate layout v2 (grouping `m16384w64`) proven on Init and verified by packed CompressGL; release pins not yet updated (status below) |
| 3 | Narrow Goldilocks FRI stage | narrow template layout, Goldilocks | **conditional**: needed only if a narrower wrap plus packed CompressGL can't make step 4 cheap enough |
| 4 | First KZG stage (CompressGL) | packed openings; narrow templates if its output feeds the terminal directly | exists, wide and packed |
| 5 | Narrow KZG stage | narrow template layout (fixed-capacity regions, `W` ≤ 16) | Rust prototype v2 proven on the normalized-wrap Init chain under a fixed 2-shard configuration with admission (110 evaluations, 56 s GPU prove, 4.6 KB proof); verified Lean tiling pending |
| 6 | Terminal | Aiur PLONK terminal, fixed predecessor key via a verifier plan, gnark `PairingCheck` boundary | `CompressFinalNarrow`: complete contract, **23.37M constraints, `2^25`**; real Ignition PLONK proof verified (CPU, 131 s prove) |

**Step 2 status (2026-11-14, `target/wrap-normalized/summary.json`).**
FRI parameters are unchanged (`log_blowup` 2, 100 queries, 20 query PoW
bits). The candidate is `crates/stark-verifier/compress-wrap/m16384w64-v2.layout.json`,
stored with its grouping policy and per-circuit row bounds. It pins the
wrapper artifact and key and fixes 33 circuits in one shard, all active.
`Wrapper::admit` runs on the wrap execution and rejects a root that exceeds
any capacity before proving. Packed CompressGL takes the wrap proof as its
predecessor through `compress_gl::WrapPolicy`. The policy pins the wrapper
artifact, key, layout digest and claim prefix, and maps a root statement to
CompressGL's statement.

The grouping compiler gives a many-member group a wide union of columns. A
single cold group of every function with at most 65,536 Init rows is 805
columns wide. Restricted to members under 64 columns, it is still 496 wide.
Grouping by rows works better. `m16384w64` gives the 22 functions with
16k–65k Init rows their own group, 255 columns at `2^20`. It splits the rest
by width into a narrow group (453 columns, `2^18`) and a wide one (497
columns, `2^16`). Pure row thresholds cut wrap cells further but open 600–900
more columns per query, which costs CompressGL more than the wrap saves.
Candidates were counted with `wrappolicy` exports and `wrap-plan` before
proving (`target/wrap-normalized/policies/`).

Capacities come from what can vary between roots that pass root admission
(pinned aggregate key, one shard):
- **No headroom:** rows fixed by the key and the claim, such as key
  deserialization and the key/claim byte stream.
- **+5%:** proof-driven rows. Openings are fixed when all circuits are
  active. Merkle paths and FRI rounds grow about 3% per extra log2 of root
  height.
- **+15%:** per-distinct-height work. Init's root has 20 distinct heights;
  at most 22 fit under `2^21`, and 23 under `2^22`.
- **+5%:** ROM.

Only five narrow circuits move up a power of two.

Both chains below were run back to back on an idle machine with the same
binary and BN artifact.

| Init | Raw root → CompressGL | Normalized wrap → CompressGL |
|---|---:|---:|
| GL input proof | 5.44 MB, 5,598 opened elements/query | 3.40 MB, 3,262 opened elements/query |
| Wrap stage | — | 6.5 s exec + 3.5 s GPU prove, 11.7 GB RSS, 1.65B committed cells |
| CompressGL main cells, padded / with copies | 1,471M / 1,209M | 1,109M / 709M |
| CompressGL stage time, peak RSS | 126.7 s, 110 GB | 83.7 s, 85 GB |
| BN stages 1–3 | 43.0 s | 44.3 s |
| To third BN proof | 173.3 s (180.5 s in the earlier e2e run) | 141.8 s |

The first iteration used a single cold group of every function with at most
65,536 Init rows (`t65536`), with +1 on every circuit Init filled above 90%.
Its wrap committed 3.19B cells and took 40.7 s at 111 GB RSS, which
cancelled the CompressGL saving.

No current-format Mathlib root exists, and the bounds are analytic.
Admission rejects any of these:
- a root with two shards;
- a root whose max height is `2^23` or more;
- a root whose key-driven rows differ.

Such a root needs a v3 layout. The tightest circuits are the narrow cold
group, whose bound fills 97.8% of `2^18`, and `Blake3::compress_chunks`,
at 92%.

**Steps 5–6 status (2026-11-14, `target/narrow-terminal/summary.json`).**

**Chain.** wrap → GL → BN1 → BN2 (`target/wrap-normalized/pair-wrap`) →
narrow BN3 → `CompressFinalNarrow` → gnark PLONK, all on Init with the
Ignition setup.

**Shared fixed slots.** The Aiur packed verifier now reads shared fixed
slots:

- Key tag 2 lists each circuit's slot.
- The transcript absorbs the slot list after the shapes, as the fork's
  `observe_shape` does.
- Each slot is opened once, at its owner.

It agrees with the native verifier byte for byte, measured by the fold
weight squeezed from the final transcript. Forged shared openings and slot
lists are rejected (`tests/aiur_kzg_packed_shared_fixed.rs`).

**Shard count: 2.** The stage's capacities, shard height and count are fixed
by a configuration file, and each execution is admitted against it.

| Narrow BN3 | 2 shards, +8% headroom | 3 shards, +25% |
|---|---:|---:|
| evaluations / packs | 110 / 41 | 132 / 49 |
| GPU prove / peak RSS | 56 s / 113 GB | 75 s / 121 GB |
| terminal, exact (gnark) | **23.37M** | 26.08M |
| terminal, power-of-two capacities | 29.36M | 29.95M |

- **Headroom.** +8.2% is the most that fits two `2^25` shards. Stage-3
  executions from two other Init predecessors were admitted, with
  `BN254G1::add` at most 94.5% full.
- **Risk.** A root whose stage 3 exceeds +8% anywhere is rejected and needs
  the 3-shard configuration, which has its own key and terminal (26.1M, also
  `2^25`).

**Terminal.** `MultiStark/CompressFinalNarrow.lean` does the following:

- embeds the narrow key, with its digest fixed at export;
- authenticates the policy and binds the anchors;
- checks the keyed claim chunks against the configured policy, stage 3 and
  the public statement;
- verifies the narrow proof;
- folds with the transcript weight;
- returns 18 words to gnark's `PairingCheck`.

Its 23.37M constraints break down as:

| Part | Constraints |
|---|---:|
| G1 | 10.2M |
| BLAKE3 | 6.3M |
| terminal contract | 1.8M |

**Final PLONK proof (CPU; the CUDA PLONK backend stops at `2^24`):**

| | Aiur narrow terminal | Hand-written |
|---|---:|---:|
| constraints | 23.37M | 14.69M |
| domain | `2^25` | `2^24` |
| prove | 131 s | 11.2 s |
| load | 47 s | 24.7 s |
| setup | 88 s, plus a one-time 975 s Lagrange basis | |
| peak RSS | 55 GB | |
| Solidity proof | 864 B | 864 B |

Gas was not measured, because this host has no Foundry. Fitting `2^24`
would need about 6.6M fewer constraints, mostly G1 MSM work.

**Principles carried over from the hand-written design:**
- **Normalize first,** at the wrap, on the Goldilocks side.
- **A fixed ladder of distinct stages,** each verifying one fixed predecessor
  key and shape. There is no self-recursive BN chain, so verifier plans
  (§5a) apply at every boundary without circular keys.
- **Narrow wherever a stage's proof is verified by an expensive verifier,**
  meaning every BN254 stage whose output is verified in BN254.

**Kept from Aiur:**
- the dynamic per-function layout where width is cheap (IxVM, aggregation,
  the wrap's input side), because it uses fewer cells there;
- packed openings, so any stage that stays wide is cheap to verify;
- one template backend for both fields, so the narrow Goldilocks stage and the
  narrow KZG stage use the same compiler feature and proof.

**Decision gate for stage 3.** The root-width analysis (`target/root-width/`)
decides it. If grouping, FRI parameters at unchanged security and wrap
normalization make CompressGL's leaf hashing small enough, drop stage 3.
Otherwise add it, generated from the Aiur FRI verifier source with templates.

**Targets:**
- warm end-to-end compression comparable to the hand-written 403 s;
- a terminal at `2^25` or below;
- unchanged gas and final proof size.

Cold first-run cost includes the narrow stages' fixed preprocessing, as the
hand-written pipeline's did, and should be reported separately.

## 6. Unknowns

### 6.1 How functions share physical columns

The evaluation count is the total committed columns across all circuits. If
each of about 150 functions keeps its own circuit, even at `W = 8` that is
about 1,200 columns: better, but not hand-written. Reaching tens of columns
needs functions to share physical columns. Options:

1. **Templates inside existing groups.** The certified grouping pass already
   merges functions into a shared circuit with per-member selectors. Apply
   templates per group: columns ≈ groups × (`W` + selectors). Small, but
   group count and selector overhead decide it.
2. **Fixed-capacity regions.** All functions share one narrow trace, each in
   a region whose size is fixed in the key, with gate coefficients and wiring
   labels in preprocessed columns. Each invocation needs its own wiring
   namespace within that region. This reuses the hand-written layout idea,
   but dynamically selected calls between invocations still need binding.
   Configured capacities fit after normalization; dynamic stages need
   headroom, which means padding.
3. **Template fetched from a fixed table.** Each row looks up its gate
   coefficients and wiring labels by `(function, step)` from a fixed template
   table. This avoids reserved per-function regions, but still needs total
   trace capacities, padding and admission limits. A template lookup binds
   local code, not which invocation executes it: invocation identity,
   activation, step coverage and value consistency must also be enforced.
   Every row pays a fetch/routing cost. The rejected scalar-VM prototype is
   one expensive realization of this idea, not a lower bound for every
   fetched-template design.

**To decide:** which option, and at what `W`. Count total columns and
evaluations, cells, fixed columns and their openings, padding, quotient
degree, and constraint-evaluation work. Sharing columns can increase degree
or cause many more constraints to be evaluated over a larger quotient
domain. Main-column count alone is not the objective.

### 6.2 Wiring inside a template

multi-stark constraints can reference only the current and next row. A
template spanning `k` rows needs values to travel further. Options:

- **Copy constraints by lookup over fixed labels,** as the hand-written
  layout does: about two lookups per wired cell. The hand-written trace pays
  grouped lookup accumulator columns for these and its other messages;
  their count depends on grouping and degree. Labels must distinguish
  different invocations as well as local slots.
- **Carry registers:** values pass row to row in extra columns. That raises
  `W`, and makes scheduling a register-allocation problem.
- **Schedule for adjacency:** every gate reads only the current or previous
  row. That limits which programs fit at a given `W`.

**To decide:** copy-cycle lookups are the proven route; their cost per wired
value has to be counted.

### 6.3 Messages wider than a row

Call and memory tuples have arity 3–260 (arity 3 is 144M of 236M packets in
the census). A narrow row can't carry a wide tuple. Options:

- **Invocation-ID chunking:** `(call id, index, value)` messages. These need
  uniqueness and completeness obligations, listed in the census.
- **Random linear compression in stage 2:** needs custom phase-two columns,
  which multi-stark's API doesn't support today.
- **Keep wide boundary circuits** for selected calls, or reduce interfaces
  through source factoring and selective inlining. These reuse more of the
  current machinery but retain columns; count those columns in the result.
- **Keep the tuple across a few template rows** under one invocation ID.
  This still requires a reconstruction/transport argument; the current
  single-row tuple lookup does not check it automatically.

**To decide:** which messages genuinely need a new transport representation.
Do not serialize narrow fixed-map and ROM messages merely because some calls
are wide. Chunking is a candidate for the unresolved wide interfaces, not a
free or already-verified consequence of tiling arithmetic.

### 6.4 Cell cost

Rows ≈ gates per invocation × invocations, plus wiring and message rows.
The preliminary straight-line model counts 8.7M gates for the matched
verifier, against 4.97M Aiur cells and about 7.2M hand-written rows. Those
numbers do not establish a template layout's cell count or an upper bound.

For dynamic templates that preserve memoization, count one template per
distinct invocation and preserve incoming call multiplicities separately.
For static inlining, count the expanded symbolic call graph, including all
guarded arms and sharing that the generated program actually retains.
Runtime multiplicities alone omit descendants skipped by memoized calls.

**Unknown:** whether the complete physical layout is close to hand-written
cell counts after adding routing, fixed tables, auxiliary/quotient columns
and capacity slack. Only a concrete planner can settle that tradeoff.

### 6.5 Fixed (preprocessed) columns

Templates put gate coefficients and wiring labels in fixed columns:
15+4 in the matched hand-written fixture (the table width can vary). These
are committed in the key, but the next verifier still opens them, so they
count toward evaluations and the key's size.

**To decide:** how many fixed columns, and whether a constant-key verifier
treats them as fixed-base terms.

### 6.5a Normalize early, at the wrap's output

Init measurements (`target/e2e-packed/summary.json`) show packed BN stages
never settle into one shape. They alternate in a two-stage cycle: a
63-point predecessor yields a 60-point proof and vice versa, and
`KzgGroup_packed_small` flips between 4,096 and 8,192 rows. Normalizing only
the last BN stage leaves CompressGL and BN stage 1 following the root's
size, and keeps repeated BN stages just to let shapes settle.

The hand-written pipeline normalizes the root layout first
(`pipeline/root.rs`), on the Goldilocks side, where padding is cheapest. The
Aiur equivalent:

1. **Fixed wrap output.** `CompressWrap` pads its output proof to a
   configured layout: fixed per-circuit capacities, a fixed shard count and
   every circuit active, sized for the largest supported root. Admission
   rejects larger roots. Init and Mathlib then yield identically shaped wrap
   proofs.
2. **Configured capacities downstream.** Every later stage pads to configured
   capacities with headroom for data-dependent variation. Its input shape is
   fixed, so every proof shape is fixed.
3. **No repeated BN stages.** The chain becomes root → wrap (normalized) →
   CompressGL → BN → terminal. Each boundary has a distinct, fixed
   predecessor key, so preprocessed verifier plans (§5a) apply without the
   self-recursion problem.

**Costs to measure:**
- Init pays for a wrap sized for the largest root, in Goldilocks cells.
- The wrap and Goldilocks prover need padding to configured capacities.
- Capacity headroom at each stage.

Sizing needs a Mathlib root in the current format.

### 6.6 Dynamic shapes and padding

Regions (option 2 in §6.1) need per-region capacities; fetched templates
(option 3) still need an overall capacity and padding policy. Some Init runs
stabilized at stages 3–5, while the newer packed-GL chain crossed a
power-of-two boundary between stages 3 and 4. Neither observation establishes
a shape guarantee. Configured normalization can fix the tail's interface;
earlier stages can remain dynamic within their admitted bounds. Capacity
selection needs another workload and headroom for proof-value-dependent
execution, not just the observed Init counts.

### 6.7 Proof work

The tiling refinement has to be proved once:

- that a template satisfies the original row relation;
- that the copy cycles are sound;
- message chunking, if used.

The existing per-function correctness proofs are reused. Chunking adds the
census's uniqueness and completeness obligations.

The key-plan exporter and PLONK gate lowerer also need their own
correspondence arguments or checked transformations. Type-checking their
Lean inputs, and passing execution tests, do not extend the existing
compiler theorem to those transformations automatically.

**To decide:** the size of these proofs relative to the existing ~7,300
lines of compiler proofs.

### 6.8 Interaction with packing

Narrow proofs make packing less important for points but still useful.
Packing stays compatible, and early stages that remain wide keep benefiting
from it.

## 7. Measurement before building

First isolate the proof-interface cost from the verifier-implementation
cost. The existing endpoints differ in both:

| Proof being checked | Direct arithmetic verifier | Aiur execution-trace verifier |
|---|---|---|
| Actual narrow hand-written final KZG proof | Existing reference | Measure with the existing Aiur column-KZG verifier |
| Current packed Aiur proof | Count a direct verifier using the same packed-opening equations | Existing packed-verifier measurement |

**Measured (2026-11-13, `target/two-by-two/summary.json`).** The Aiur
column-KZG verifier was run on the *actual* hand-written final recursive KZG
proof: the 1,909-byte packet with a 1,669-byte compact proof, natively
verified, with the Aiur accumulator passing the pairing check.

| Proof being checked | Direct arithmetic verifier | Aiur execution-trace verifier |
|---|---:|---:|
| Hand-written final KZG proof | 14,689,424 (complete terminal) | 21,119,377 at exact capacities (`2^25`); 27,455,308 at power-of-two capacities |
| Packed Aiur proof (`i3-shard2`) | not measured | 130,210,243 (`2^27`); 128,122,520 with inlined Fq helpers; 126,667,514 on the packed-GL chain, 130,069,850 (`2^27`) as the complete terminal with the transcript fold (193,301,681 with the proof-digest fold) |

- **Breakdown on the narrow proof:** G1/MSM 9.11M; BLAKE3 and transcript
  7.47M (1,816 compressions); fixed tables and unattributed 3.22M; memory and
  I/O about 1M.
- **Key handling:** a fixed-key variant (heuristic) gives 20.8M; the narrow
  key is tiny.
- **Scope:** the narrow-proof and verifier-only packed counts exclude the
  final pairing and the statement/accumulator binding; the complete packed
  terminal count includes them.

**Reading.** On a narrow predecessor proof, the Aiur execution-trace
verifier costs about 1.4× the complete hand-written terminal, a lower bound
on the true ratio given the excluded checks. On the packed proof the same
verifier costs about 6.2× more than on the narrow one. The dominant gap is
therefore the **last KZG stage's output interface**, not the Aiur terminal
or its PLONK lowering. Reducing the last stage's columns and evaluations is
the priority; a hand-written replacement terminal is not needed to reach the
`2^25`–`2^26` range.

Use the same trusted key, transcript, expected statement and pairing
obligations within each row. Separate PCS-verifier costs from complete
terminal costs so the missing checks in today's Aiur diagnostic do not
distort the comparison. A direct packed verifier used for this experiment is
a reference/counting tool, not a decision to replace the Aiur implementation.

- If Aiur can cheaply check the narrow proof, prioritize reducing the last
  KZG stage's output interface.
- If a direct circuit can cheaply check the packed proof, specialize or
  optimize Aiur's terminal execution before assuming another narrow stage
  is necessary.
- If both remain too large, both interface reduction and cheaper verifier
  execution are needed. These measurements still do not prove optimality.

Then compare concrete template candidates. Existing compiled graphs and
execution records support an initial count-only screen:

1. Per function: gates per invocation (`fused.py` model), wired values
   inside templates, message arities, invocation counts on the Init BN and
   CompressGL executions. Distinguish unique invocations from requests and
   identify inactive guarded calls.
2. For layouts (groups with templates, fixed-capacity regions, fetched
   templates), including selective narrowing of cold functions, at several
   widths such as `W` ∈ {3, 8, 16, 32}: total columns and actual requested
   evaluations, cells including wiring and message rows, fixed columns,
   padding, quotient degree and constraint-evaluation work.
3. The resulting next-verifier cost per stage. Measured cost per evaluation
   and point is a screening model, not an exact extrapolation: hash-block
   boundaries, memoization, active circuits and padding can change it.
   Validate a promising layout with a small real proof and execution of its
   next verifier before an Init-sized run.

The exact counts require a concrete physical plan with all routing and
activation constraints included. An arithmetic-only census cannot supply
those counts for a layout that has not been specified.

An initial engineering target is low hundreds of evaluations or fewer,
with complete stage cell costs within roughly 2× the hand-written reference.
That budget is a decision aid, not a feasibility theorem. The final decision
must use the complete terminal's constraint count, configured capacity and
proving cost, with `2^24` as the performance target and Ignition's `2^26`
PLONK-domain limit as a separate hard bound. Packing, source improvements,
preprocessing and narrow layouts may all contribute; these comparisons do
not establish that one particular compiler redesign is necessary.

### 7.1 Template layout screen (planner counts, 2026-11-14)

**Measured planner counts**, not proofs. Tool and data are in
`target/template-screen/` (`run.sh`, `dump.rs`, `planner.py`,
`summary.json`). Inputs are the ungrouped export of the same
`CompressBNPacked::chain_v1` program, the production grouping (artifact
`85b20c2b…`, whose raw rows match `column-min/base` exactly), and one Init
execution (stage 3 of `gl-chain/run-k2`). The record has 1,266,290 unique
invocations, 1,412,937 call requests, 18.35M fixed-map requests, and 440K
ROM objects with 1.27M requests. The planner reproduces the baseline's
3,516 unsharded evaluations.

The planned layout uses a row of `W` cells. At `W = 3` the row has one PLONK
lane. At larger widths it has `W/4` four-cell lanes plus a `join` selector,
which turns the row into one long linear relation. Message rows hold the
multiplicity and payload, with optional four-cell sub-slots (`M`). Each cell
is one copy LogUp slot with a fixed label and a fixed multiplicity. Messages
wider than `W − 1` use keyed chunks (T1): the key is the callee's invocation
id, the ROM address or the table row. Narrow traces are split into
`2^26/quotient`-row shards, and each shard is counted as its own circuit.
Gate lowering follows `fused.py` (3-wide: 224M weighted gate rows, against
238M planned), but this lowering is not optimized.

| `W=8`, 25% headroom | Evaluations | Committed cells | Fixed cells | Terminal estimate |
|---|---:|---:|---:|---:|
| Production grouping | 3,516 | 0.21B | 1M | 78–123M |
| L2 regions, T1, wide ROM/tables kept | 1,101 | 2.08B | 3.46B | 39–52M |
| L2 regions, T1, narrow ROM + stacked table | **423** | 2.09B | 3.47B | **27.5–32.5M** |
| L1 (regions per certified group), narrow ROM | 1,326 | 2.46B | 4.08B | 42–59M |
| L3 fetched templates, narrow ROM | 843 | 6.24B | 7M | 34–45M |
| L2, T2 (keep wide groups) | 3,390 | 0.45B | 0.42B | 77–120M |

The terminal estimate is the measured 21.1M on the hand-written proof plus
16.5K (BLAKE3 only) to 29.4K (all width terms) constraints for each
evaluation beyond its 36.

Other widths for L2/T1 with narrow ROM: `W = 3` gives 252 evaluations at
exact capacity and 315 with 25% headroom. That is 448M rows in 14 shards,
with a 25.7–29.3M terminal estimate. `W = 16` gives 499 evaluations and
`W = 32` gives 587–642.

**Reading.** The ≤ ~500-evaluation target is met only by fixed-capacity
regions (L2) with keyed chunking, ROM and fixed tables narrowed as well, at
`W` ≤ 16. The estimated terminal is then about 25–35M, near `2^25` but not
`2^24`. **No layout meets the cell criterion.** L2 at `W = 8` has 0.82–1.12B
main cells and 1.5–2.1B committed cells (101–138M rows, 7–9 shards). That
compares with 203M main cells for the hand-written final stage (3 × `2^26`)
and 177M for today's stage: about 4–5.5× and 4.6–6.3× respectively in main cells,
without counting fixed cells.

Dominant remaining costs:

- **`Blake3::compress`:** 94K invocations at 653 template rows each, against
  502 wide columns. That is 56% of rows at `W = 8`.
- **Copy wiring:** 447M copy constraints, about 4 per row. Every operand and
  message argument occupies its own wired cell.
- **Message rows:** 26–35M, including inactive guarded slots. Map slots are
  23.5M against 18.35M requests.
- **Per-shard fixed columns:** 225 of 423 evaluations.

Layouts that lose:

- **Retaining wide ROM and table circuits** adds about 700 evaluations.
- **T2** keeps 17 of 25 function groups wide at `W = 8`, because wide
  messages are pervasive.
- **L1** repeats the fixed, lookup and quotient columns per group.
- **L3** moves template fields into main columns that are opened at two
  points.

Templates therefore buy interface width at roughly 5× cell cost. The next
lever is cell cost (BLAKE3 template, operand fusion and in-place message
arguments), not width.

### 7.2 Optimized template lowering (planner counts, 2026-11-14)

**Measured planner counts**, not proofs. Tool: `target/template-screen/planner2.py`;
output: `summary2.json`. Same inputs, L2/T1 layout, narrow ROM and stacked
table, and the same terminal estimator as §7.1. Each stage keeps the previous
stage's changes. All figures are for `W = 8` with 25% headroom.

| Stage | Template rows | Evaluations | Main cells | Committed cells | Fixed cells | Terminal estimate |
|---|---:|---:|---:|---:|---:|---:|
| §7.1 lowering | 110.4M | 423 | 1.12B | 2.09B | 3.47B | 27.5–32.5M |
| S1a fusion, CSE, multi-product spans | 97.6M | 396 | 1.02B | 1.90B | 3.40B | 27.1–31.7M |
| S1b + unrolled `Blake3::compress` | 79.1M | 306 | 0.82B | 1.52B | 2.72B | 25.6–29.0M |
| S2 + lane-slot / in-place messages | 68.2M | 342 | 0.70B | 1.30B | 2.84B | 26.2–30.1M |
| S3 + adjacent-row reads (estimate) | 63.1M | 371 | 0.68B | 1.27B | 3.45B | 26.6–31.0M |
| S4a S2 + periodic shards | 68.2M | 177 | 0.82B | 1.52B | 0.56B | 23.4–25.3M |
| S4b S4a + degree-3 gates | 70.5M | **135** | 0.82B | 1.63B | 1.11B | **22.8–24.0M** |

Other counters, §7.1 → S2: copy constraints fell from 447M to 326M. Cells
used fell from 604M to 424M. Message rows fell from 34.9M to 5.5M, with 19.2M
small messages moved into lanes of gate rows. Map slots fell from 23.5M to
18.3M, against 18.35M requests. The inactive slots were all in
`Blake3::compress`.

**What each stage models, and what soundness needs:**

- **S1a.** A product `(a·x+b)(c·y+d)` becomes one product gate on the cells
  `x` and `y`, with its linear corrections in the same lane. A product with
  at most two linear uses and no use as a cell is folded into those
  relations. Products and linear values are deduplicated within one
  template. A relation spans up to `L` lanes using fixed span flags
  (`L(L+1)/2` columns), with carries only beyond one row. Soundness: the
  transformations are exact algebra over coefficients fixed in the key, and
  sharing never crosses invocations. The lowerer still needs the
  correspondence proof from §6.7.
- **S1b.** One region per compression holds 7 rounds and the finalization.
  Each round is specialized to its match arm and stage constant. Round state
  is wired instead of carried by 162-wide self-calls. A compression costs
  2,987 rows, against 8 × 653 before. Soundness: the region's receive fixes
  `stage = 0`, and every caller enters through `compress_init`. The
  recursion depth is static (94,336 = 8 × 11,792). Requests equal
  invocations, so memoization loses nothing. The constant-stage arm
  conditions still hold as constraints.
- **S2.**
  - Messages with payload ≤ `k` and a fixed multiplicity, or ≤ `k − 1` and a
    multiplicity cell, use a lane slot. Each lane slot has a fixed tag,
    multiplicity constant and multiplicity coefficient: 3 fixed columns per
    lane and one lookup per lane.
  - Constant multiplicities need no cell. A padding slot must hold a valid
    witness, such as a copy of a real invocation; the table's multiplicity
    absorbs its lookups.
  - Identical lookups are merged, which LogUp additivity allows.
  - A message is read in place only when one gate lane's cells are exactly
    its payload. This almost never happens at `W = 8`.
  - The callee's chunk key is its fixed invocation ID.
  - Evaluations rise because each shard gains 6 fixed columns and one
    lookup column.
- **S3.** Linear uses whose previous occurrence is in the previous row read
  it through next-row coefficients. That costs `W` fixed columns and opens
  main at `ζω`. Cell use falls 7%, but evaluations rise. This is an
  optimistic estimate: freed cells are assumed to repack.
- **S4a.** Each shard holds `⌈cap_f/S⌉` slots of every region, so all shards
  have one height and one fixed matrix. multi-stark uses one global `ζ`
  (`verifier.rs`), so that matrix's openings can be shared. Soundness:
  - Labels and invocation IDs get a per-shard constant offset in the lookup
    expressions, so copy cycles and call keys never alias across shards.
  - No invocation straddles a shard.
  - multi-stark must let circuits share a preprocessed slot and open it
    once. It does not do this today.
  - Equal heights add padding: 0.82B main cells, against 0.70B for S2.
- **S4b.** Products only in a span's first lane, so `C_l = qm·a·b +
  st_l·lin_l + Σ m_{l,l'}·lin_{l'}` has degree 3. Lookups are grouped in
  pairs, the quotient degree is 2 and shard capacity is `2^25`: 3 shards
  instead of 6. This costs 3% more rows.
- **What must stay fixed per row:**
  - per-lane gate coefficients;
  - span flags;
  - per-cell copy labels;
  - message slot tags and multiplicity coefficients;
  - the invocation ID.

  A step-indexed coefficient table would move these into main columns plus
  a lookup, opened per shard, which is the L3 result in §7.1. Periodic
  shards remove the per-shard cost instead. Caveat inherited from §7.1: one
  copy lookup per cell with a fixed label omits per-cell copy multiplicities
  (`W` more fixed columns, or a second lookup per cell). With periodic
  shards, that adds about `W` evaluations.

**Width sweep (S4b, 25% headroom; S4d adds S3 to S4b):**

| `W` | Rows | Evaluations | Main cells | Committed cells | Terminal estimate |
|---:|---:|---:|---:|---:|---:|
| 6 | 85.4M | 131 | 0.82B | 1.77B | 22.7–23.9M |
| 6, S4d | 77.7M | 137 | 0.62B | 1.33B | 22.8–24.1M |
| 8 | 70.5M | 135 | 0.82B | 1.63B | 22.8–24.0M |
| 12 | 47.7M | 155 | 0.82B | 1.50B | 23.1–24.6M |
| 16 | 37.3M | 200 | 1.09B | 1.97B | 23.8–25.9M |

**Reading.**

- **Evaluations.** Periodic shards and the degree-3 gate bring the stage to
  about 130–140 evaluations at `W` ≤ 8. That is a terminal estimate of about
  23–24M, inside `2^25`. Under this estimator `2^24` is out of reach at any
  evaluation count, because the floor is 21.1M at 36 evaluations.
- **Cells.** The gap narrows but does not close. The best balance is `W = 6`
  S4d: 0.62B main cells, about 3.0× the hand-written 203M, and 1.33B
  committed cells. It depends on the optimistic adjacency estimate. Without
  adjacency the result is 0.82B main cells, about 4.0×, mostly power-of-two
  shard padding: unpadded it is 0.65–0.71B.
- **Remaining cost.** `Blake3::compress` is still about 36–40% of rows.
  Each round is about 290 rows at `W = 8`: 32-bit add-with-carry relations
  over 16 bytes plus byte-lookup lanes. Next come `KzgBlake3::realign`,
  `KzgDeserialize::node` and `KzgAlgebra::eval_at`.
- **Caveat.** Rows and evaluations are counted at selected shard
  boundaries. Fitting the rows into fewer power-of-two shards can move the
  totals more than a single optimization.

**Measured with the v2 template backend (2026-11-14,
`target/template-backend/v2/summary.json`;
`docs/aiur-template-backend.md` "v2 layout").** The S4b layout is
implemented in `template/v2.rs`:

- periodic `2^25` shards sharing one fixed slot, through a multi-stark fork
  with `System::new_shared`;
- degree-3 spans;
- lane-slot messages;
- unrolled `Blake3::compress`.

The last stage uses the ungrouped export of the steady chain artifact.
Grouped artifacts are not supported.

| Init stage 3, `W = 8` | planner2 S4b (gl-chain, h25) | v2 gl-chain h0 | v2 fold-transcript chain h0 / h25 |
|---|---:|---:|---:|
| template rows | 70.5M | 73.5M | 62.0M / 77.5M |
| `2^25` shards | 3 | 3 | 2 / 3 |
| evaluations | 135 | 132 | 110 / 132 |
| main / committed cells | 0.82B / 1.62B | 0.81B / 1.62B | 0.54B / 1.08B, 0.81B / 1.62B |
| fixed cells | 1.11B | 1.41B | 1.41B |

The planner's row and evaluation counts hold to within 4%.

**Proof.** The fold-transcript chain was proven at h25 on the GPU with the
Ignition SRS (stage 3, verifying the stage-2 packed proof):

- per-column KZG:
  - witness: 14.7 s;
  - fixed matrix: built in 88 s on the CPU, committed once in 11 s;
  - prove: 43 s;
  - proof: 6.4 KB, 63 G1 points, 132 evaluations;
- packed SHPLONK (packing capacity `2^26`):
  - fixed matrix: built in 7.7 s, committed in 14 s;
  - prove: 76 s;
  - peak RSS: 121 GB;
  - proof: 5.7 KB, 49 packed commitments.

Both verify natively and reject a changed output.

**Terminal: at about `2^25`, and the estimate holds only with packed
openings.** Counts are gnark counts at exact capacities. The verifier
reads the key as data.

- **Per-column KZG verifier:** 66.2M on the unshared 3-shard proof. It
  pays about 190K constraints per committed column (G1 38.7M), so the
  §7.1/§7.2 per-evaluation model, which holds the MSM fixed, does not apply
  to it.
- **Packed verifier** (`KzgPackedVerifier::verify_deferred`), on proofs
  with Init's circuits and packing ratio:
  - unshared, 3 shards: 37.0M measured;
  - unshared, 2 shards: 28.5M measured;
  - the 3-shard stage with its shared fixed slot (53 packs, 132
    evaluations): **27.3–29.4M**, derived from the measured marginal costs;
  - without the key digest, as in the fixed-key terminal: 24.4–26.6M.

  The current key grammar cannot name a shared slot. The derivation is in
  `docs/aiur-template-backend.md` M7.
- **Against planner2 (22.8–24.0M):** about 1.5–2.6M above, mostly G1. The
  proof has 49 packs at a packing ratio of 2.

**Remaining:**
- the complete-terminal contract, not counted here;
- a verified fixed-key relation that reads a shared slot. This needs the
  Lean packed verifier and key grammar to carry per-circuit slots.

Within `2^25` at exact capacities, with about 4–9M of margin before the
contract; not `2^24`.
