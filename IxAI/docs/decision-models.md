# Decision models inside Ix's toolchain: a screening

**Scope.** This screens decisions made by Ix's own compiler, prover and the proofs written for
it. It does not cover the main use of a decision model: a judgment inside a program written in
Lean or Ix, where the model answers a narrow typed question and the program's code acts on the
answer (routing, triage, approval, escalation, and the decision points of an agent harness such
as Lane). That use is the subject of `decision-library.md`. A negative result here says nothing
about it.

Where a small learned decision model would help inside the toolchain, screened against four
tests. Written 2026-11-20 against `~/repos/ix.ci-merge-tests` (`de5970000`), the upstream ref
`origin/pr-678-latest` (`826c389b2`) and this project's combined certificate work.

**Result: no candidate passes all four tests.** Most fail test 3: Ix already has an exact cost
model and a fast search, a profiler, or a canonical rule that forbids choice. Two candidates leave
tests 3 and 4 open: the shape of generated refinement proofs (ranked first) and tactic choice in
the hand-written refinement proofs (second). For the first, the likely outcome of the experiment
below is a better generator rule rather than a model. The experiment is still worth running,
because it settles the question for every Aiur program whose refinement proofs are generated.

## The four tests

1. **Checked independently.** A kernel, a certified checker or a proof verifies the output, so
   soundness never depends on the model.
2. **Exact, cheap labels.** Decision quality is measurable exactly and cheaply enough to build a
   training set.
3. **No formula or profiler already answers it.** If a direct computation gives the answer at
   acceptable cost, use it.
4. **Measured headroom over the simple rule**, by a margin that matters.

Three earlier candidates failed and are not repeated here except in the last section:
reducibility hints (`kernel-hints.md`, Measurements: at most 1% total change, no claim better by
1%), the `prop-xhard` classifier (`plan.md`, "Timing, learned contribution and scorer hotspots":
the same answer as the outer-form rule on all 768 items, at half the throughput), and predicting
IxVM execution cost (a profiler gives the exact number).

## Measurements made for this screening

All of these are single-threaded or read-only. Outputs are in `.truthmines/decision-models/`.

| What | Command or source | Result |
|---|---|---|
| Time of Aiur's grouping search on a real program: the KZG/BN verifier, 147 functions, two workload profiles | `grouping_search` from `~/repos/ix.aiur-compression-active/Aiur/.lake/build/bin` with the `reproduce` arguments of `docs/measurements/aiur-fused-bn-grouping.json` (`--max-members 16 --sweeps 8`) | **0.78 s wall, 69 MB peak.** Converges after 4 sweeps (149, 35, 11, 0 moves). The policy is identical, as JSON, to the committed `aiur-fused-bn-grouping-policy.json`. |
| Sensitivity of that search to its one structural parameter | same, `--max-members` 4, 8, 32, 64 | 4: 3,286 columns, 52 circuits. 8: 2,948 columns, 44 circuits. 16, 32 and 64: 2,948 columns, 44 circuits, identical cells and FFT cost. The search saturates at a group size of 16. |
| Where the cells of the project's `Fixed::step` circuit go | `ix/aiur/step0.report.json` (the proved step 0) | 563,164 stage-one cells. The byte pair table (`UInt8::pair_inputs`, 65,536 rows × 7) is **458,752 (81.5%)**. All 12 function circuits together are 102,876 (18.3%). Proving takes 46 ms. |
| Cost of the generated `.obs` path-lemma chunks, net of their closure | `.truthmines/combined/sweep/full-survey.obs-standalone.tsv` (existing survey), less the smallest standalone cost, 163.3 million queries; `obs-chunk-costs.txt` | Chunks made by cutting every 120 tactic lines differ by more than 10x. `delta.obs` chunks 3 to 9: 4, 14, 59, 90, 115, 143, 161 million queries. `deltas.obs` chunks 3 to 9: 4, 11, 21, 33, 115, 214, 283 million. 15 of 45 chunk constants ran out of memory when checked standalone. |

On the last row: a standalone check is transitive, so if the nested `as_aux_lemma` chunks depend
on one another, these numbers are cumulative and the increments are what each chunk adds
(`delta.obs`: 4 to 45 million per chunk). That is still uneven by about 10x across chunks of
equal length. I did not determine which reading is correct (inferred, not measured).

## Candidates

### 1. Shape of generated refinement proofs (`ObsGen`, `obs_rewrite.py`)

- **Decision.** How a generated `.obs` path-lemma proof is written: where it is cut into
  `as_aux_lemma` blocks, which hypotheses are cleared and when, and in what order the list
  equations are substituted. Today a fixed post-processing pass (`ix/combined/obs_rewrite.py
  --chunk 120`) applies three rules and cuts every 120 tactic lines.
- **Typed input.** The generator's tactic script for one function of an Aiur program (for
  `Fixed::delta`, a straight-line sequence of `obtain ⟨…⟩ := h.letValue_inv`-style inversions),
  with the goal and context size at each line, all Lean syntax.
- **Output space.** A cut set over line positions (`2^L` for `L` lines; the rewritten
  `Fixed::deltas` proof is 2,818 lines, 1,358 before the rewrite, in
  `IxAIRefine/Fixed/Obs/Fixed1.lean`). A practical restriction: one chunk length `K` per lemma
  from a small set, or a binary "cut here" per line.
- **User.** Anyone who writes an Aiur program and proves it refines a Lean specification with the
  generated path lemmas, then certifies the result with IxVM.
- **Check.** The Lean kernel, and IxVM, check whatever proof comes out; every cut placement proves
  the same statement. A placement that fails to elaborate falls back to the default.
- **Labels.** Two exact costs. Term nodes per constant come from elaboration: the whole generated
  source builds in 9 minutes at 8 GB (`plan.md`, In progress). IxVM queries per constant come from
  an execution, minutes per leaf (the survey: 70 to 250 million queries per leaf of one to five
  constants). One IxVM label costs about a minute of a large machine; one node-count label is a
  fraction of an elaboration.
- **Simple rule.** Cut every 120 lines, after the three rewrite rules.
- **Headroom evidence.** The three rewrite rules took the terms from 126 million to 9.7 million
  nodes (13x; 31x on `transpose20x16`), and the build from 30 min at 37 GB to 9 min at 8 GB. After
  them, equal-length chunks still differ by more than 10x in IxVM cost (table above), and the leaves
  holding the path lemmas dominate the certificate: leaves 0 and 1 are 5.2 of 7.2 billion queries
  and 76 of 99 proving minutes (`plan.md`). That shows the cost is uneven. It does not show that a
  different cut placement would lower the total.
- **Tests.** 1 passes. 2 passes for node counts. IxVM labels are exact but cost minutes each. 3 is
  open: chunk cost may follow a formula in context size times lines, in which case a dynamic
  program over cut positions with that formula is the tool, not a model. 4 is open.

### 2. Tactic choice in the hand-written refinement proofs (`IxAIRefine/Fixed`)

- **Decision.** Which closing tactic, or which short sequence, to try at a goal inside a `*_spec`
  lemma, `Soundness` or `Deployed`.
- **Typed input.** The Lean goal and local context.
- **Output space.** A fixed menu. The current proofs use, by site count over `IxAIRefine/Fixed/*.lean`:
  `by simp` 515, `simp` 132, `by decide` 110, `rw` 89 and `by rw` 27, `exact` 83, `by omega` 46
  and `omega` 10, `by norm_num` 39 and `norm_num` 5, `rfl` 27 (plus 1,616 `obtain` inversions, which
  are mechanical). About 10 classes. The files hold 220 theorems.
- **User.** Whoever writes or updates a refinement proof when the program or specification
  changes. Each change of `Fixed` so far has meant re-proving spec lemmas by hand.
- **Check.** The Lean kernel, then Ix's `check-lean`.
- **Labels.** Exact: does the tactic close the goal (and how big a term does it produce). Each
  label is one elaboration of one goal: milliseconds to seconds, with outliers under
  `maxHeartbeats 40000000` in `StepSpecs.lean`.
- **Simple rule.** A fixed cascade (`rfl`, `decide`, `omega`, `simp`, `norm_num`, `simp_all`,
  `grind`), first success wins.
- **Headroom evidence.** None in the repository. The project's own premise-selection result
  (README, "Premise selection": a bilinear scorer beats IDF baselines but stays well below Opus 5.5)
  suggests a small model on statements is weak on proof-search questions.
- **Tests.** 1 passes. 2 passes. 3 passes, since no algorithm decides which tactic works. 4 is open,
  and the dataset of one program's proofs is small.

### 3. Aiur circuit idioms for a Lean specification function

- **Decision.** Choosing, per operation, among circuit idioms that each have a proved refinement:
  for example the width of the range check in `shr8` and `sign_split` (six or seven bytes through
  `UInt8::from_fields`, against a 16-bit table), or how a length-`n` dot product is split into the
  `dot8`/`dot11`/`dot16`/`dot20` functions.
- **Typed input.** The specification function (`IxAICore` Lean) and the call sites in the Aiur
  program; the output is an idiom per site from a menu of 2 to 4.
- **Check.** The refinement proof of each idiom (`FixedSoundness.lean`: `shr8_sound`,
  `sign_offset_sound`, `zero_test_sound`) plus Aiur's certified compile.
- **Labels.** Exact and cheap: widths, heights, padded cells and FFT cost follow a closed formula
  that matches the backend for every circuit (`formal-aiur-grouping-tuning.md`, "Predicted widths
  ... match the actual backend for every function circuit on all four workloads").
- **Simple rule and headroom.** In `Fixed::step` the byte pair table is 81.5% of stage-one cells and
  is shared by every range check, so the decision is global (which tables the library uses), not
  per call site. Function circuits are 18.3%, the upper bound for any per-site choice, of a 46 ms
  proof.
- **Tests.** 1 and 2 pass. 3 fails: with a handful of sites and an exact cost formula, enumerating
  the idioms is cheap. 4 fails for `Fixed`: the per-site bound is 18% of a 46 ms proof.

### 4. Aiur function grouping (`Grouping.Plan`, `grouping_search`, `grouping_tune`)

- **Decision.** A membership policy: which functions share a physical circuit.
- **Input and output.** Per function: private, lifted and shared columns, lookups, constraint
  degree, rows per workload (`GroupingSearch.Chip`). Output: a partition of the functions into
  groups of at most 16 (147 functions in the KZG verifier; 214 function circuits in IxVM).
- **Check.** `grouping_tune --policy` compiles and certifies every layout (`Checked.localRule_iff`,
  `packet_sound`, `Plan.derives_iff`). The search is untrusted.
- **Labels.** Exact and closed-form: `fftCost`, `padded`, `lookupDegree` in `GroupingSearch.lean`.
- **Direct answer.** A local search with that exact objective takes **0.78 s** on 147 functions and
  converges in four sweeps (measured above). Raising the group-size limit past 16 changes nothing.
  It is run once per program version, and its result is committed.
- **Headroom.** Against the ungrouped default the search removes 56% of columns (6,657 to 2,948)
  and 70% of circuits (147 to 44), at 0.4% fewer cells. The gap between this local optimum and the
  global optimum is not measured. If it mattered, restarts or a solver would close it faster than
  a model could be trained.
- **Tests.** 1 and 2 pass. 3 fails. 4 does not apply: the search already captures the headroom.

### 5. Depth-pass slot classification (`Depth.Config`, `Depth/Classify.lean`)

- **Decision.** For each call slot inside a recursive strongly connected component, `exact`
  (demand `d − 1`, no column) or `gap` (demand `d − 1 − gap`, with range-checked limbs; 2 columns
  with the default limbs `[16, 8]`).
- **Check.** `Depth.Certified` re-checks everything soundness needs. A wrong `exact` only makes
  honest proving fail.
- **Direct answer.** A static rule (the slot is the chip's only intra-component slot, or its calls
  lie in exclusive control-flow scopes) is conservative. Whether `exact` holds for a workload is
  answered by executing it and checking the depth words, which is a profiler.
- **Headroom.** At most 2 columns per `gap` slot. I did not count `gap` slots in IxVM (not
  measured).
- **Tests.** 1 passes. 2 is weak: whether `exact` is correct depends on the inputs, so a label
  holds only for the workloads seen. 3 fails. 4 is small by construction.

### 6. Sharing order in the certified compile (`Ix/Sharing/Family.lean`)

- **Decision.** The order in which a component's shared subterms enter the sharing table, for
  components of more than 16 members (`greedyOrderAux`).
- **Why it fails.** The order is not free. Sharing is part of a constant's address
  (`ix_canonicity.md`: "The representation of sharing is therefore part of the address"), and the
  rule `sharing-k16-greedy-v1` fixes the family (`sharing-minimum.md` §14.1: "An implementation
  may use a different search algorithm only if it produces the same retained rows"). A learned
  order would change addresses, so it would have to become part of the canonical rule itself.
- **Headroom.** Small in bytes. K16 against the earlier exact rule changed 112 of 689,469 Mathlib
  constants, net +223 bytes (§14.4). A per-constant choice of tie rule would gain 0.011% (§12.15).
- **The real problem** is speed: the greedy chain re-scores every candidate at each pick (77% of
  the compile profile; constants of 1.5 million nodes do not finish in 15 minutes, `plan.md`).
  That is an incremental-evaluation problem with a fixed answer, not a decision.
- **Tests.** 1 passes in the narrow sense (the decompiler checks validity), but canonicity forbids
  any deviation. 3 fails: the rule is the answer. 4 fails.

### 7. Which constants share an execution (`ix shard`, `crates/ixon/src/shard.rs`)

- **Decision.** The partition of an environment's constants into claims (shards).
- **Direct answer already in Ix.** A recorded kernel profile (`.ixprof`: heartbeats, substitution,
  whnf, def-eq and intern counts per block, and the delta graph), a linear cost model with
  calibrated constants (`COST_PER_SUBST` and the like), and a multilevel hypergraph partitioner
  (coarsening, FM refinement, 4 restarts) minimizing cross-shard ingress in bytes, which is the
  loading cost that `kernel-hints.md` measured as 25.6% of rows.
- **What is weak.** The size model, not the partition choice: the prover's record model
  under-predicted the combined certificate's leaves by 2.2x to 6.5x (`plan.md`), and the prover
  split a leaf by itself. That is calibration of four constants against executions, a regression
  on profile counters, and the owner's earlier ruling on cost prediction applies.
- **Headroom.** The 20% figure in `kernel-hints.md` is for 80 independent claims each loading its
  own closure; how much of it the partitioner already removes on Mathlib is not measured. The
  measurement that settles it: execute the same 80 claims as independent claims and as the
  partitioner's shards, and compare loading rows (execution only, about 10 to 15 minutes gated).
- **Tests.** 1 passes. 2 passes (execution). 3 fails. 4 open but bounded by 25.6%.

### 8. Trace-shard layout, retention and lookup grouping in the prover

- **Decisions.** Trace-shard budgets (`plan_shards(record, budget)`), retention (`Retain` against
  `Regenerate`), and the lookup group size.
- **Direct answers.** The shard plan is a deterministic function of the record and the budget
  (`aiur-trace-sharding.md` §3). Retention has two policies, and the measurement chose
  `Regenerate` for K > 1 (§7.3: 0.9 s rebuild against 4.5 s clone per shard, held witnesses at 10x
  the record). Lookup group sizes 1 to 8 are already searched exhaustively for minimum auxiliary
  width (`aiur-prefix-init-grouping.json`, `lookup_selection`). The remaining advice in
  `aiur-single-gpu-performance.md` is to compare a few planned layouts on one retained record.
- **Tests.** 1 passes. 2 passes. 3 fails: the options are few and each is measured directly.

## Ranking

| Rank | Candidate | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| 1 | Shape of generated refinement proofs | pass | pass (nodes); IxVM labels cost minutes | open | open; costs uneven by 10x |
| 2 | Tactic choice in refinement proofs | pass | pass | pass | open; small dataset |
| 3 | Aiur circuit idioms | pass | pass | fail at current sizes | fail for `Fixed` |
| 4 | Partitioning claims | pass | pass | fail | open, bounded |
| 5 | Aiur grouping | pass | pass | fail (0.78 s search) | captured by search |
| 6 | Depth slots | pass | weak | fail | small |
| 7 | Trace-shard layout and retention | pass | pass | fail | measured |
| 8 | Sharing order | forbidden by canonicity | pass | fail | 0.011% |

### First: the generated proof-shape experiment

The question is whether a placement of cuts and clears that depends on the lemma beats the fixed
120-line rule by a margin worth a model, and whether a formula already finds it.

1. **Dataset.** The 51 generated `.obs` lemmas of `Fixed` (originals in
   `.truthmines/combined/obs-generated`). For each lemma, variants from `obs_rewrite.py` with
   `--chunk` 30, 60, 120, 240 and none, plus one formula rule: cut when the accumulated context
   size (hypotheses times their type sizes, read from the elaborated goal) passes a threshold.
2. **Cheap stage (labels: term nodes).** Elaborate each variant and count the nodes of every
   resulting constant. That is five elaborations of the generated files at about 9 minutes and
   8 GB each, one gated job per variant (about 45 minutes in all). This needs only the generated
   files rebuilt, not Ix.
3. **Expensive stage (labels: IxVM queries).** For the best two variants and the default, execute
   the leaves that hold the path lemmas with the program source's closure taken as given (or
   subtract the 163 million-query floor). This takes 30 to 40 minutes per variant on shards 0 and
   1 as they stand, so it has to be split into leaves of under 10 minutes each.
4. **Metric.** Total IxVM queries of the path lemmas (and peak memory) under each variant, and,
   per lemma, the gap between the best variant and the 120-line rule. Also how well a fitted
   formula (nodes, or context size times lines) ranks the variants (Spearman correlation against
   queries).
5. **Decision rule.** If one fixed `K` or the context-size rule comes within 10% of the per-lemma
   best, ship it in `obs_rewrite.py` and stop: no model. A model is justified only if the
   per-lemma best beats every fixed rule by more than 20% of the path lemmas' queries, and the
   formula ranks variants poorly.

If a model is justified, a first model in the style of the certified pipeline:

- **Input encoding.** Per tactic line: the inversion lemma's name (one of about 10:
  `letValue_inv`, `call_inv`, `var_inv`, …, a one-hot), the number of hypotheses in context, the
  total node count of their types, the node count of the goal, and the distance since the last cut.
  These are counts read from the elaborated goal, so they are deterministic and exact.
- **Output head.** Binary "cut after this line" per line, or a class over `K ∈ {30, 60, 120, 240}`
  per lemma.
- **Training signal.** Squared error against one-hot targets from the per-lemma best variant, as
  for `IxAICore`'s questions. Labels come from node counts (cheap). IxVM queries are used for
  evaluation only.
- **Gate.** The placement is advice. Elaboration or IxVM rejects nothing it should accept, and a
  failed placement falls back to the default.

The honest expectation is that step 5 ends the experiment with a rule. The `eq_def` episode points
the same way: the largest proof-form effect seen so far (two lemmas from killed at 40 GB to 2
million queries) was an IxVM bug, `try_nat_dispatch_prewhnf`, and the fix belonged in the kernel,
not in a model that learned to avoid it.

### Second: tactic choice

1. **Dataset.** Every closing-tactic site in `IxAIRefine/Fixed/*.lean` (1,137 lines start with or
   use `simp`, `decide`, `omega`, `norm_num`, `rfl`, `exact`, `rw` or `simpa`, by a regex count),
   with the goal at that site.
2. **Baseline.** Replace each site's tactic with the fixed cascade. Count how many sites the
   cascade closes, and the time and term size against the hand-written tactic.
3. **Metric.** The share of sites the cascade fails to close, and the extra elaboration time where
   it succeeds. That share is the headroom a model could address.
4. **Cost.** One instrumented elaboration of the `Fixed` proofs per cascade step, about 7 runs.
   `StepSpecs.lean` is the slow file. My estimate is 10 to 30 minutes per run (not measured).
5. **Decision rule.** If the cascade closes more than 95% of sites, the remainder is for a
   general proof agent, not a small model.

## Not worth a model

- **Aiur function grouping.** The search has an exact closed-form objective, runs in 0.78 s on 147
  functions, converges, and is certified downstream. Its result is committed once per program.
- **Sharing order.** Part of the canonical address. The rule fixes the answer, and the byte
  headroom is 0.011%. The open problem is the greedy chain's speed.
- **Depth-pass slots.** A conservative static rule plus execution answers it, at 2 columns per slot.
- **Lookup group size, trace-shard budgets, retention.** Few options, each searched or measured
  directly.
- **Partitioning claims into executions.** A profile, a calibrated cost model and a hypergraph
  partitioner already exist. What remains is refitting the record-size model, which is
  calibration, not a decision.
- **Per-call-site Aiur idioms in small programs.** Exact cost formula and a handful of sites, so
  enumerate. In `Fixed` the shared byte table, 81.5% of cells, makes the choice global.
- **Reducibility hints, lazy-delta and argument-order advice.** At most 1% (`kernel-hints.md`).
  Substitution and loading dominate.
- **IxVM execution cost per constant.** A profiler gives the exact number.
- **`prop-xhard`-style classifiers on solver residue.** The same answers as the outer-form rule.

## What this screening did not determine

- Whether the `_proof_1_k` chunk costs are cumulative or independent (the reading of the survey).
- The gap between the grouping search's local optimum and a global optimum.
- How much of the 20% loading saving `ix shard`'s partitioner already captures on Mathlib.
- The number of `gap` slots in IxVM's depth configuration.
- Any headroom figure for tactic choice. No elaboration was run here, by the task's limits.
