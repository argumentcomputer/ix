# Plan

The master planning doc: goal, current status, decisions with their reasons, experiment results,
and what comes next. Pointers to code and sources live in `references.md`; detailed designs in
`aiur-composition.md` and `rl.md`; the wider strategy in `~/repos/notes/ix-ai-strategy.md`.

## Goal

An Ix-based harness and training framework for verifiably safe, specified AI:
- models are small, typed, Jev-style decision models whose answers are Lean types;
- training is a pure, deterministic Lean function `train spec config`, so the same training gives
  the same output, and an Ix certificate proves a model is exactly that output;
- safety properties are theorems that hold for every weight setting, so no training run or reward
  can break them;
- rewards are spec-level Lean functions with content addresses, so a certificate names the reward
  a policy was trained against;
- BLAKE3 everywhere; the Ix store as a local Truth Mines sketch.

## Current goal: one certificate in under 30 minutes (set 2026-11-20)

Work is planned against one measurable goal at a time. Anything that does not move the current
goal's number is parked (list below), not started.

**Goal.** For the deployed triage decision model, one PLONK certificate that covers the training
run, the final weights, the model's card and gate decisions, and the typechecked environment of
the refinement and safety theorems, produced end to end in under 30 minutes on this machine's
one GPU, and accepted by `ixai-verify combined`.

**What the clock covers.** Everything a prover does, with nothing reused from an earlier run:
environment leaf proofs, environment aggregation, the training block proofs and their
aggregation, the join, and compression to PLONK. Reported beside it, not inside it: the Lean
build, the certified compile (79 s today), the one-time circuit exports, and verification (7.7 s).
The run that counts is made with no other job on the machine.

**Budget.**

| Stage | Certified run (M1) | Best measured so far | Needed |
|---|---|---|---|
| Environment leaf proofs | 99:00 | shard 0 proved: 30:26 → 16:27 (`kernel-subst`), 5:42 (experiment); all 5 shards executed under `kernel-subst`: 4.07 billion queries for 7.2 | about 13:00 |
| Environment aggregation | 8:56 | leaves and aggregation in one prover run under `kernel-subst`: **32:52** (was 107:56); with the path lemmas in the fused shape: **15:33** | |
| Training: 30 block proofs | 0:23 | | |
| Training: aggregation | 4:18 | | |
| Join | 0:22 | | |
| Compression to PLONK | 3:18 | | |
| **Total** | **116:17** | **23:54** on paper: 15:33 measured for the environment (`kernel-subst`, fused lemmas, one run), the other stages as in M1; not yet one timed run, and without the card | **under 30:00** |

`kernel-subst` on the five shards, executed (accepted, 2026-11-20): queries 1.10, 1.76, 0.70,
0.23, 0.27 billion (certified: 2.18, 3.03, 1.23, 0.37, 0.42); FFT cost 1.04e13, 1.68e13,
6.14e12, 1.95e12, 2.32e12; execution 9:17, 14:45, 5:35, 2:09, 2:24, which is 34:10 if run one
after another. M1's 99 minutes were five separate prover runs, each executing and then proving
with the GPU idle during execution. One prover run over all claims overlaps executions with
proving (three executions per GPU beside the proof in hand), so the wall time should approach
the proving time alone (about 25 minutes at shard 0's rate of 40 s per 1e12 of FFT cost). That
run, leaves and aggregation together from an empty store, is queued as G1's exit measurement
(`cert/fullv5`).

**Prover settings (checked against the fork's `docs/aiur-gpu-proving.md`, 2026-11-20).** The
M1 run and the shard proofs so far were not set up as that guide prescribes:
- Trace population ran on the CPU. Our builds use `IX_CUDA=1` only, and with `AIUR_GPU_TRACE`
  unset such a build populates every circuit's main trace on the host. The logs show the cost:
  for shard 0 under `kernel-subst`, of the 6:52 after execution, the GPU proved for 2:20 and
  stalled 3:58 waiting for the host; in M1's shard 0, proving 3:05 and stall 12:21.
  `AIUR_GPU_TRACE=generated` populates on the device with the same build; a build with
  `IX_FORMAL_COMPILED_TRACE=1` adds compiled writers. Proof bytes are the same in every mode.
- One prover run per shard, where the guide's unit is one `prove --aggregate` run over the
  whole manifest (overlapping executions; no cutting of an over-budget shard into parts).
- `--max-ram 170` in a 180 GiB scope, a limit chosen to leave room for other jobs; the prover's
  own default is MemTotal less 20% (199 GiB).
- A from-scratch run is `--fresh`, which keeps proving keys and fixed preprocessing; an empty
  store would put key generation inside the clock.
Native executors were in use throughout (`native-ixvm`, `native-aggregation`).
Device population measured on shard 0 under `kernel-subst` (2026-11-20): with
`AIUR_GPU_TRACE=generated`, 248 of 254 function circuits populate on the device ("no compiled
bundle"; 6 stay on the host for unsupported hints), and almost nothing changes: 16:21 against
16:27, trace 358 s against 377 s, GPU proving 136 s, stall 222 s against 238 s, device peak 95
GiB against 70. So the stall is not removed by moving those circuits; the claim is 61 trace
shards, populated at about 6 s each while the GPU proves one in about 2 s. Untested causes:
the six circuits left on the host, regeneration of each shard for the second round
(`--retention`, decided by the RAM budget), and the absence of compiled writers
(`IX_FORMAL_COMPILED_TRACE=1` at build). What does shrink both proving and stall is a smaller
trace (G2, G3). In hand: the whole environment in one run with `--fresh`,
`AIUR_GPU_TRACE=generated`, `--max-ram 200` (`cert/fullv5`). Upstream's reference for scale: Init, 56,312
constants in four claims, proved in 591 s on one GPU in one such run.

**G1's exit measurement (2026-11-20, `cert/fullv5`).** The M1 environment under `kernel-subst`
in one `prove --aggregate --fresh` run, `--max-ram 200`, `AIUR_GPU_TRACE=generated`: root
`1f672106…` verified in 32:52 wall (1,913 s inside the prover), 198 GiB peak. The six claims
were proved by 26:04 and the five joins and root took the rest, partly overlapped. Executions
overlapped as intended (the two small claims ran side by side in two minutes). The two heavy
claims still stall the GPU: 61 and 76 trace shards, proving 136 s and 118 s, stall 220 s and
253 s, about 8 minutes of the run. The partition is M1's refined one (shard 1 cut in two for
the old kernel's record size), which this kernel no longer needs.

**G2's exit measurement (2026-11-20, `cert/fuse`).** The environment regenerated with the fused
path lemmas (36,840 constants requested, 175 MB for 245 MB, root `403b1b69…`) under
`kernel-subst`, in one `prove --aggregate --fresh` run with the same settings: the sharder
cuts it into 3 claims where it cut 5; root `97665cf7…` verified in 15:33 wall (912 s inside the
prover), 125 GiB peak. Claims proved by 13:00. The largest claim: 483 s of execution, 50 trace
shards, proving 137 s, stall 121 s.

The stages after the leaves sum to 17:17 today, which leaves about 12:40 for the leaves unless
aggregation also shrinks (it should, with fewer and lighter leaves; not measured). M1 did not
include the card and decisions; their kernel cost in the environment is not measured yet.

**Milestones.** Each ends with a measured number, on the full environment, not an estimate.

| | Milestone | Exit criterion | State |
|---|---|---|---|
| G1 | Committed kernel validated and adopted | all 5 shards accepted; Ix's kernel tests pass apart from pinned costs; leaf-proof total measured | all 5 shards accepted (4.07 billion queries for 7.2); Ix's test tier: 14 of 17 suites pass, including the exploit suite (bad declarations still rejected), circuit verdicts and claim safety; the three failures are 149 pinned FFT costs (lower now) in `ixvm-eval` and `ixvm-kernel-checks`, and two generated mirror files that need regenerating (`ixvm-source`); **met**: environment proved in one run in 32:52 |
| G2 | Generated lemmas in the cheaper shape | IxVM queries of the three worst lemmas measured against today's; environment regenerated with statements unchanged; leaf-proof total measured | measured under `kernel-subst` (own cost = closure minus statement-only floor): `transpose20x16` 528.6 → 107.6 million queries (4.9×), `deltas` 592.3 → 123.7 million (4.8×), `step` 34.9 → 22.1 million (1.6×); the string-lookup risk does not show; statements identical by text (103 declarations) and by elaborated type (307 constants); estimate for the environment about −45%; **met**: the regenerated environment builds (8:06), compiles (70 s) and is proved in one run in 15:33 for 32:52; the rewritten files and `Core/Fused.lean` are in the source tree and on the branch |
| G3 | Rebase cost removed without losing what it was added for | the variant passes a workload of the shape the rebase was added for, the 80 Mathlib claims and all 5 shards; leaf-proof total measured | no rebase in inference (`exp-noinferrebase`): all 5 shards accepted, 2.57 billion queries (0.52, 0.54, 0.69, 0.41, 0.41; the two library shards are 50 to 75% worse than `kernel-subst`), Mathlib +5.4%. Bounded search (`infer-rebase-shallow`): shard 0 at 386 million queries and FFT 3.33e12 (better than no rebase), Mathlib 882.5 million (+0.8%), all 80 accepted; shards 1 to 4 not run. Upstream's constant `Simps.addProjections._unsafe_rec` is not in our Mathlib snapshot, so it tests nothing here; another witness is needed |
| G4 | Card and decisions in the environment | their leaf cost measured; `aiur_join_check` confirms the model constant is the run's final model | cost measured under `kernel-subst` (`measure_deployed.sh`): the environment with `IxAICombined.Deployed` compiles (36,835 constants, 79 s); own cost of the card 183 million queries (1:23 on its own), of one gate decision 3 million, of the model's range lemma 1.7 million: about 0.2 billion in all, a few percent of the environment. The checker's comparison of the model constant with the run's output is not written yet |
| G5 | The timed run | one quiet end-to-end run under 30:00, `ixai-verify combined` reports `PROVED`, certificate and timings recorded | |

If G1 to G3 together leave the total above 30 minutes, the next levers, in order: fewer and
larger training blocks (aggregation 4:18), then the aggregation tree's shape. Not: more hardware.

**Queued for when this goal is met (2026-11-20, at the owner's request).** Run the kernel's row
profiler on Mathlib, under the kernel the goal ends with. The profiler is on `ix-ai`
(`8bfad0c8a`: `IX_KERNEL_ROWS_PROFILE` writes, per selected function and argument, how many
distinct values its rows had; `IX_KERNEL_HINTS_TRACE` writes rows per function per claim). Plan:
a profiler build of the final kernel (one kernel build); a pilot on the 80-claim sample and a
few whole shards of `.truthmines/store/mathlib-d13f23b/env.ixe` to measure rows per second and
state what the whole library would cost before starting it; then execution only, shard by
shard and resumable, with rows per kernel function, the functions and arguments where rows
concentrate, and the constants that cost most. Deliverable: where Mathlib's rows are, ranked,
with the same breakdown that found the substitution and rebase costs here.

**Parked until this goal is met.** The decision library's training objective (a core change);
Lane changes and the Lane gate prototype; the kernel redesign with free variables by level; a
size-generic training program; a second use case; the external review's performance items
(their agents finish what is queued in idle gaps of the machine, and start nothing new).

## Status (2026-11-18)

Done:
- Tiny and small triage models certified end to end: one 584-byte PLONK certificate each, covering
  training, evaluation card, decisions and safety theorems.
- Full model (600 steps, 16 hidden units): training proved by 600 Aiur step proofs, chain-
  checked to `train spec config`; IxVM certificates for its card, decisions and theorems.
  2026-11-19, on the circuit with `bound` (ix `de59700`): GPU packages 600/600 byte-identical to
  the host's (export 167 s), proved in 44 s of proving (283 s wall, 9.3 MB each), all verify, chain
  to `train` (weights BLAKE3 `45ea4f5f…`, `.truthmines/aiur/full-bound`); all 600 also verified by a
  separate verifier (key recompiled from the package, claims built from the spec chain; 98 s). One `Fixed::train`
  execution of the full config (the claim `train_sound` is about) also proved as a single Aiur
  STARK: 1.7 s prove (CPU; the GPU quotient kernel runs out of memory on the 238k-column entry
  row), 220 MB proof `fb0a1af2…`, verified independently (1.2 s) against verifier-supplied inputs
  and weights, tampered output rejected (`.truthmines/aiur/train`). Export compiles the circuit in
  17 min (`ixai_step train-export`).
- Determinism across Lean, Python and IxVM, in fx, bf16 and f32 (`shell/golden.sh`).
- Verifier-gated rewards (`ixai reward`) and refused forged claims.
- Verifiable RL spec (`IxAICore/Reinforce.lean`, `TriagePolicy.lean`), builds; `ixai rl` runs.
- Numeric format experiment (below).
- `Fixed` circuit restructured into small functions plus `Fixed::train`; builds.
- `train_refines` proved (standard axioms only): any accepted `Fixed::train` run equals
  `IxAICore.train` on the full config, with no hypotheses. The circuit range-checks every updated
  parameter (`bound`: -4096 <= raw < 4320), which carries a per-step magnitude invariant
  (`Magnitudes.lean`); the real run stays within -390..545. Costs 331 byte-pair lookups per step.
- `train_sound` / `step_sound` (`IxAIRefine/Fixed/Soundness.lean`, standard axioms): memo-checker
  acceptance of a `Fixed::train` claim over a certified compilation of `Fixed.source`, with the
  full config's inputs, implies the output represents `encModel (train Triage.spec fullConfig)`;
  `train_sound_eq` / `step_sound_eq` give equality of the decoded output (encodings are
  pointer-free); `train_of_steps` chains 600 step claims to `train` in Lean. `bound` is covered at
  the circuit level by `Specs.bound_spec` and as a gadget by `bound_sound` (`ix/aiur/FixedSoundness.lean`).
  Remaining links: STARK -> memo acceptance (trusted backend, Rust lowering, claim encoding);
  compilation = `Fixed.source` is an `#eval` parity check (`IxAIRefine.Check`), not a theorem.
  Deployed step packages (`IxAIRefine/Fixed/Deployed.lean`, standard axioms): `step_sound_deployed`
  states `step_sound_eq` over the shipped `ModulesArtifact` of `Modules.prepare` with
  `["Fixed::step"]`, and `train_of_deployed_steps` turns 600 accepted claims of that circuit,
  chained by public IO (claim i's decoded output = claim i+1's model input), into
  `ms 600 = train Triage.spec fullConfig`. Their one extra hypothesis, `StepOnlyParity` (the
  step-only preparation's source is `Fixed.source`; `Modules.prepare` keeps whole modules, so
  `train` stays in it), is `#eval`-checked like `IxAIRefine.Check`. A generic world-extension
  lemma (`ObsFn.extend`, `step_sound_of_extends`) covers a smaller step-only source should one
  be shipped. Outside Lean: STARK -> memo acceptance for each package and reading the chained IO
  from the 600 proofs.
- GPU trainer: Lean host plus CUDA kernels, bit-exact with the spec, writes witness packages
  byte-identical to the host's; `gpuStep_eq`, `train_eq_gpuTrain`,
  `gpuStepHintKeys_eq_stepHintKeys` proved. Exact 128-bit guard refuses only on real int64
  overflow (0/300 random shapes refused, was 105); int8 `mma.sync` tensor-core GEMM with limb
  planes, ~11x device speedup at 1024^3, bit-identical; `gpuStepM_eq`, `tileReduceM_dotRaw`,
  `blockReduceM_flag` proved with standard axioms only.
- Tier 1 premise-selection pipeline (extract, curate, commit, train, evaluate) on a Mathlib slice;
  `split_disjoint` proved. Round 2 (fx16 bilinear scorer): time-split R@10 47.0% / MRR 0.327,
  above IDF (46.6% / 0.291) and frequency; module split still below IDF (30.3% vs 38.1%).

- M2b generator of kernel-decided typed questions (`IxAICore/Typed.lean`): simply typed λ-calculus
  typing and propositional status, labels decided by `infer` and `status` with soundness proved
  (`infer_iff`, `status_*_iff`), fresh evaluation sets (`fresh_disjoint`), two decision models
  trained by `train`, `ixai bench typed` and new baseline batch kinds (results below).
- Certified DPLL labeller (`IxAICore/Dpll.lean`, `dpll_iff`, `solve_iff`, `satN_iff`;
  `fastStatus_eq` in `Typed.lean`) and a hard propositional family `prop-hard` (40 atoms, 170
  clauses), exported with every earlier batch to `baseline-v2`.

- Verification boundary (2026-11-19, after an external review; contract in `verification.md`).
  Six findings fixed, each with a regression test (`IxAITest`, `IxAIVerifyTest`,
  `ix/verify-tests.sh`): step-proof chains are verified by `verify_claim` against claims built from
  the spec and the committed program, and an incomplete chain is `INCOMPLETE`, never accepted
  (reports are diagnostics only, `ixai aiur-diagnose`); Merkle roots bind the leaf count and paths
  check index range and shape (`merkleRootV2`, `verifyPath_sound` and length binding proved, standard
  axioms; the dataset roots changed, version 1 kept as `rootsV1`); curation refuses items with
  unaddressed names (`unresolvedName`, `curate_spec`; counts unchanged on `order-basic` and
  `mathlib-full`); `ixai check` checks against the consumer's job, not the file's header; reward
  submissions must be one term, are elaborated only under bubblewrap, and are checked against the
  harness's target address; benchmark values are no longer program initializers (`ixai` start
  104.6 s → 0.03 s; `bench-typed.tsv`, `bench-typed-xhard.tsv` byte-identical). New
  `ixai-verify` (spec + verification layer only) checks a model package (commitment, model,
  receipt) of the full run: `PROVED` in 142 s, through the 600 step proofs (89 s) and the one
  `Fixed::train` proof (2 s), with the aiurExec root `attested` (its PLONK is not re-verifiable
  here) and 8 IxVM claim proofs; every remaining hypothesis is printed with the outcome.

- Reward harness and gate domain (2026-11-20, second review pass). The reward worker no longer sees
  the host filesystem or inherits the caller's environment: it mounts only the toolchain closure,
  `ix`, the bundle's `IxAICore` and one fresh job directory per submission, so concurrent submissions
  are isolated. Submissions are parsed by the toolchain that compiles them (Lean 4.34.1), and the
  goal's statement is checked in the compiled Ixon by address (`IxAIVerify.Ixe.checkGoalType`), so
  the parser is not in the trusted base. The triage gate has an explicit domain: `Formula.inScope`
  (atoms below 3), `valid_iff_forall_eval` (validity is truth under every assignment), and proofs
  that the generator stays in it (`Triage.data_scoped`, `test_scoped`); `Triage.admit` refuses
  out-of-domain formulas such as `P3 → P0`, which `valid` calls true. No formula enters from outside
  yet, so nothing calls `admit`. `probabilitiesNonneg` and `chunkPos` correct two edge cases for new
  specs and leave the certified `probabilities` and `chunk` unchanged. Hex digests accept either
  case and must be exactly 32 bytes; `ixai reward` takes `--out`. Standard axioms only; certified
  addresses unchanged; `ix/reward-tests.sh` 16/16. The bundle's Lean 4.34.1 build of `IxAICore`
  (`ix/bundle/.lake`) predates the two new modules and needs a rebuild before the next certified
  compile.
- Verification boundary (2026-11-20, second review pass). A job (`ixai-job-commitment-v2`) is issued
  before training from the spec and config alone. It holds the claim policy (Ix `Check`, pinned spec
  and role binding, no axioms or assumptions), the canonical model encoding, and claim templates
  compiled by the consumer (`ixai-verify template`, `commit`). The verifier reads the trained `.ixe`
  itself, every record authenticated by its hash; requires each proof's claim to be exactly the
  policy's claim about a theorem that instantiates its template; then runs `ix verify` and checks
  its exit status and claim digest. The model is read from the claims' common `trainedOutput`
  constant, so one model serves training, card and gate. Model words are canonical and in
  `[-4096, 4320)` on every model. A verifier that started on the evidence and failed rejects its
  route; one that could not start leaves it incomplete. Trajectories parse strictly; step 1000 is
  `step-1000`. `verify_claim --batch` (fork `ix-aiurexec`, `b32313569`) checks the 600 step proofs
  with one key: 88.6 s → 1.9 s. The full package is `PROVED` in 15.0 s (was 142 s);
  `ix/verify-tests.sh` passes 28/28, the 13 earlier cases with unchanged expectations. Not checked:
  the card's value is matched by type only, not compared with a natively computed card.
  `IxAIVerify/Ixe.lean` and `IxAIVerify/Ixon.lean` overlap and should be merged.
- Compressed training result verified by the consumer (2026-11-20, review §5.3). `ixai-verify`
  checks the terminal gnark PLONK certificate of the compression pipeline itself
  (`aiur_plonk_verify`, fork `ix-aiurexec` `330bd06`, Ix's own `gnark::verify`). The key is pinned
  by BLAKE3 in the job (`compression`: verifying key `736588d0…`, wrapper key `1bc0cd05…`), and
  its KZG anchors must be Ix's release Ignition parameters (SRS SHA-256 `06db33d8…`; no
  development SRS was used). The public statement
  `S = BLAKE3(compress-wrap/v1 ‖ wrapper key ‖ H(claim [1,0] ‖ 0⁸ ‖ S_root))`, with `S_root` over
  the recompiled root key and the root claim, is recomputed by the consumer from the spec, the
  submitted model and keys recompiled from the approved packages (`IxAIVerify.Compression`, with
  `#guard`s reproducing the pipeline's recorded statements). All three certificates verify (600
  steps `d8551c47…`, 30 blocks `20d80b11…`, one `train_tree` `26eb66b9…`, whose Merkle root is
  rebuilt), each in 1.4–2.1 s (the PLONK check is 20–40 ms). An `aiur-exec` route alone now gives
  `PROVED` (11.9 s). Changed bytes, model words, intermediate models and keys are rejected; a
  missing verifier leaves the route incomplete (`ix/verify-tests.sh`, 39/39). Taken as given: the
  wrapper key digest (pinned, not recompiled), the statement format, and the Ignition ceremony
  (anchors checked, not replayed). Not done: block and tree roots verify only through
  `ixai-verify compressed`, not as package routes, and `ixai package-assemble` does not yet write
  `plonkKey`, so the documented full-package command still reports `aiur-exec` as attested.
- Timing, learned contribution and scorer hotspots (2026-11-20, review §4.3, §4.5, §4.6).
  - Timing: timed decisions now return only the answer, its confidence and the certified flag
    (`answerOf`, `certAnswerOf`); reference labels are joined afterwards. The earlier figures
    included the DPLL labeller. Per decision: `prop-xhard` model 1.72 → 0.50 ms and certified
    3.86 → 2.60 ms; `prop-hard` 4.81 → 2.57 ms and certified 8.85 → 6.51 ms; `prop` 0.16 →
    0.10 ms; stlc 37 → 34 µs.
  - Learned contribution: negative. `ixai bench typed-xhard` also writes
    `bench-typed-xhard-unresolved.tsv` (BLAKE3 `437333be5969…`). On the 768 items without a
    certificate at 16 nodes, the model and the outer-form rule (CNF → contradiction, DNF →
    tautology) give the same answer on all 768: 89.1% [86.8, 91.4], 0/83 traps, paired gap +0.0.
    The 95 items the model answers above τ are all ones the rule also gets right. At the same
    solver budget, single thread: solver alone 180 checked decisions/s; solver + rule 179 checked
    and 709 correct/s; solver + model 89 checked and 353 correct/s. Neither adds a checked
    decision, and the model's features repeat the solver's work, so on `prop-xhard` the model is
    pure cost over the rule.
  - Scorer: `Pool.of`/`inModules` use binary search on sorted `own`/`excl` and on `decl`;
    `PreparedLib.indices` and `Refs.of` no longer copy or append quadratically; `parMap` clamps
    its chunks. `mathlib-full-rerank-theorem.tsv`, `bench-small.tsv`, `bench-typed.tsv` and
    `bench-typed-xhard.tsv` are byte-identical. Wall time is unchanged within noise (538.7 s
    before, 552.4 s after): Mathlib's modules average about 25 theorems, so the quadratic terms
    were small. `bench mathlib-full module` and `time` (17 and 32 min) were not rerun.
- A library for certified decisions in Lean programs (2026-11-20, `IxAIDecide`,
  `decision-library.md`). A program declares an option type (`finiteOf`), an input encoding
  derived from field types (`Encode`, `Encode.via`, which also states what the model may see)
  and a seeded labelled generator (`Task`); training is the core's `train` on `Task.spec`,
  unchanged. A `Gate` has a floor and a per-option confidence threshold, with theorems for every
  weight setting: an option is returned only at its threshold, `defer` below the floor, never an
  option other than the model's own, a stricter gate only adds deferrals, a cascade keeps each
  stage's guarantee, and confidence is at most 256, so a threshold of 257 rules an option out
  (`run_never`). Use case: pay, hold or reject an invoice (18 features, a hidden fraud
  interaction, 1/16 label noise); `handle` applies exact rules first, and `handle_paid` proves
  for every model that a paid invoice has an approved vendor, is within its purchase order and
  was judged `pay` at the gate's threshold or more.
  Training follows a protocol fixed before its runs (`Protocol.lean`): fan-in-scaled
  initialization, a validation stream, selection among 48 checkpoints per seed on validation
  only, seeds fixed in advance, the held-out set scored once. Three threshold rules were each
  fixed before their runs, on fresh seeds each time; none makes the gated model both safer
  than the written policy and useful. Results on 1,024 held-out invoices per seed:
  - Accuracy of the model's top answer, which no rule changes: 902.3, 905.1 and 903.6 on the
    three seed sets, against the written policy's 889.1, 885.5 and 890.6 and the 914.1, 916.0
    and 917.3 of the best rule on the visible fields.
  - Rule v1 (90% precision averaged over all `pay` answers; seeds 101 to 108): the gate pays
    wrongly 10.4% of the time against the policy's 8.9%.
  - Rule v2 (the policy's validation precision plus one point in every confidence bin; seeds
    201 to 208): safer (7.5% against 9.1%) but decides 500 of 1,024 on average and pays nothing
    on 3 seeds.
  - Rule v3 (an exact one-sided 95% binomial test on cumulative answers against the policy's
    precision, in integer arithmetic in `Protocol.lean`; 4,096 validation examples; seeds 301
    to 308): pays on 2 of 8 seeds, and those payments are 9.3% wrong against the policy's 9.0%.
    It fails safety, usefulness and the requirement to pay on at least 7 seeds.
  - Where the limit is: an oracle gate that pays exactly the safest visible profiles passes
    v3's test on 7 of 8 seeds and pays 514 invoices per seed with 7.6% wrong, safer than the
    policy on all 8. So the rule and the label noise leave room (1.5 to 2 points); the trained
    models do not use it. Their most confident `pay` answers are no more precise than the
    policy's, and the deployed model is more confident paying a new vendor that changed bank
    details through the portal (247/256) than a routine invoice (246/256): it learned "pay
    unless a hold condition applies" and does not rank payable invoices by fraud risk. The
    training objective (squared error on one-hot labels, no cost on a wrong payment, 512
    examples, at most 16 hidden units) is the binding limit, and it lives in the core.
  - `reject` never qualifies under any rule, which is right under the generator;
    `never_rejects` proves it for every weight setting.
  The deployed model is seed 301's under rule v3 (179 parameters, 2,560 steps): its gate never
  pays and never rejects (`never_pays`, `never_rejects`), so it holds or sends to a person; its
  card (901 correct against the policy's 881; 337 decided, all `hold`, 302 right) and four
  decisions are proved by `decide +kernel`, and its training is re-run bit for bit at every
  test build (`#guard`, evaluation, not a kernel proof). `Fast.lean` gives `@[csimp]` array
  versions of the core's shuffle and schedule, proved equal. No further threshold rounds: the
  next step is the objective (a cost on wrong payments, or probability targets, with more
  data), which is a change to the certified core and its circuit.
  Not general enough in the core: `card` and `Model.ask` clamp probabilities, the triage gate
  has one threshold; the Aiur circuit, refinement proofs and code generators are tied to
  `Triage.spec`, so this model's training is not certified by either route yet.
- A guardrail gate for the Lane harness (2026-11-20, `IxAIDecide/LaneGate.lean`,
  `decision-library.md` "Decisions inside an agent harness: Lane"). The first decision around
  Lane is whether a finished change may merge without review. A typed `ChangeSummary` mirrors
  what Lane's change record holds (edit counts per class, added axioms, unchecked files,
  conflicts, obligations) plus three values only the main agent can supply (who classified the
  edits, merge conflicts from `merge --check-only`, sorries). Exact rules send to review any
  change whose edits were not classified by the main agent, or that has a statement, removed,
  modifier or definition-body edit, an added axiom, text changed outside declarations, an
  unchecked file, a conflict, an open obligation, a sorry or an IxC rejection; only an empty
  change is discarded; a gated model may only choose between `mergeNow` and `review`. Proved
  for every model and gate: `mergeNow` implies no exact rule applies, main-agent classification
  and a `clean` judgment at the gate's threshold (`handle_mergeNow`,
  `mergeNow_no_statement`, `…_added_axiom`, `…_unchecked_file`, `…_conflict`, `…_sorry`,
  `mergeNow_classified_by_main`), and the model never causes a discard (`handle_discard_iff`).
  No model is trained: there is no data. Reading Lane's code (fork `a97befb`) corrected the
  earlier document-only mapping: the change record's edit classes are reported by whoever ran
  `finish` (the worker, for a delegated lane) and the server checks only their shape; a file's
  `unchecked: false` is whatever tag the writer sent; `finish` does not check for sorries;
  `submit --require` recomputes the edits in the main agent's process but stores no outcome,
  and nothing links a submission to a change address; heartbeat use is printed and recorded
  against nothing. So no labels exist yet. Proposed in `lane.md` as changes 11 (outcome records
  for merge, submit and discard, keyed by change address, written only on the main agent's
  requests) and 12 (`lane classify`: main-agent reclassification, about 60 lines, not written).
  Change 11 is drafted on the fork's local branch `outcome-records` (`f9a048d`, 105 lines and a
  test); it has not been built or tested. The gate module and its checks are a prototype kept in the
  working directory: the library does not import them and they are not on the branch, which
  carries the Lane design documents only.
- Combined certificate verified by the consumer (2026-11-20, M1). `ixai-verify combined`
  (`IxAIVerify.Combined`) checks the 584-byte certificate `7a2a00c5…` against a job that pins
  the compression pipeline: `PROVED` in 7.7 s (checker 4.3 s, PLONK 25 ms, 4.1 GB peak).
  `aiur_join_check` (fork `ix-cert` `84f9ec3b3`, which now prints the addresses of the constants
  the theorem's statement references) recompiles the IxVM and `ix_aggr` keys from artifacts
  pinned by digest in the verifier (`0cbcb681…`, `80d584ab…`) and rebuilds the environment's
  `CheckEnv` claim. It checks the run against arguments and an expected model that the verifier
  writes from the specification and the submitted model; the trainer's spec files are not read.
  The verifier binds the theorem's `IxAICore.train` and `Triage.spec` to the job's addresses and
  `IxAIAiur.fullConfig` to the config in the consumer's compiled templates, compares `out.bin`
  with the output claim it computes natively, and verifies the PLONK proof under the pinned key
  against `S = 3b9edda7…`, computed from the root key and the root claim that the checker read
  in the same bytes. A changed proof byte, a changed model word, another root, and a checker
  that panics are rejected; a missing or failing-at-setup checker and a job without the pin are
  incomplete. `ix/verify-tests.sh` 48/48; a `#guard` reproduces the statement. It is a command,
  not a receipt route: job format v2 names neither the circuits nor the block program (the
  recommendation is an optional `combined` object in the job naming the two circuit digests, the
  run aggregator and program digests, the theorem, the binding and the block size). Taken as
  given: the run aggregator and program digests (command line), the artifact pins, and the
  theorem's statement beyond the three constants it references.
- One certificate for training and its environment (2026-11-20, M1). A 584-byte PLONK
  certificate (`7a2a00c5…`, `.truthmines/combined/cert/full/plonk/plonk/proof.bin`) covers one
  `AiurRun` claim that joins two proofs:
  - the IxVM `CheckEnv` aggregate of the full environment of the refinement theorem (36,760
    constants compiled, 30,989 in Lean's logic, 6 leaves, claim `456de28a…`, subject root
    `946dd8ed…`), which holds `IxAICombined.train_of_deployed_blocks_enc` (`2512dc43…`), the
    binding `IxAICombined.blockRun` (`16a3eaac…`), the generated path lemmas and the Aiur
    compiler's correctness proofs, with no user axiom;
  - the training run: the aggregate over 30 `Fixed::train_block` executions under the program
    key `d46caf1e…`, from the initial model to the model with BLAKE3 `062ecbcd…`.
  The join is `ix_aggr` shape 18 (`ChildKind.aiur`): it verifies both proofs and opens the
  theorem and the binding in the environment's subject root by Merkle paths. Built with
  `ix/combined/certify.sh full STAGE` on the toolchain of `~/repos/forks/ix-cert`
  (`IX_PROFILE=cert`), one GPU:

  | Stage | Time | Note |
  |---|---|---|
  | leaf proofs | 99 min | 5 shards, 6 claims; 7.2 billion queries |
  | aggregation | 8:56 | root `7d710a49…`, 118 GB peak |
  | join with the training root | 0:22 | 18.2 million rows, one trace shard, 6.0 MB proof; root key `79894717…` |
  | independent check | seconds | `aiur_join_check`: `PROVED`, every item recomputed (below) |
  | compression | 3:18 | 584 bytes; all 8 pipeline checks pass; 143 GB peak |

  Checked independently of the prover:
  - `aiur_join_check` recompiles the aggregator's and IxVM's keys from the pinned artifacts,
    rebuilds the environment's `CheckEnv` claim from the environment and its partition, takes the
    theorem's and binding's addresses from the environment, recompiles the run aggregator's and
    the program's keys from their packages, and rebuilds the run's endpoints and data root from
    the specification's arguments and expected output. Verdict `PROVED`, 0 user axioms.
  - The certificate's terminal statement, recomputed from the joined root's key and claim
    (`S = 3b9edda7…`, the same derivation as `IxAIVerify.Compression.terminalStatement`), equals
    the pipeline's, and the standalone verifier (`aiur_plonk_verify`) accepts the certificate
    under the pinned verifying key `736588d0…` (Ignition SRS) and rejects a changed statement.
  What it rests on: STARK and FRI soundness and Ix's audit boundary; soundness of `ix_aggr`
  with the two new shapes and of the `AiurExec` run aggregator (both unproved prototypes);
  IxVM's soundness, with one kernel function changed from the version PR 678 proves
  (`try_nat_dispatch_prewhnf`); `BlockOnlyParity`, checked by `#eval`; the claim encoding, checked
  in Rust and not in Lean; the compression pipeline's layers; BLAKE3; the Ignition ceremony.
  Not yet: the trained model's card and decisions in the same environment
  (`IxAICombined/Deployed.lean` is generated, not yet compiled in); a route in `ixai-verify` for
  this certificate (the two checks above were run by hand); the Ix protocol decision on
  `ChildKind.aiur`.
- Structure and hygiene (2026-11-20, review §2). Shared primitives are a new library
  `IxAICommon` (`Hash`, `Merkle`, `Literal`, `Paths`), and the toy logic's `Stmt` moved out of the
  mock kernel into `IxAI/Stmt.lean`: `IxAIVerify`, `ixai-verify` and `ixai` import no mock-up
  module, names and namespaces are unchanged, and every generated claim and certificate source is
  byte-identical, so no certified address changed. The two Ixon readers are one
  (`IxAIVerify.Ixon`; `checkGoalType` keeps both readers' checks and now also authenticates every
  record). `Ixai.lean` is dispatch only, its commands in `IxAICli` (one module per concern), the
  helpers shared with `ixai-verify` in `IxAIVerify.Cli`. Paths come from the executable's
  location or `IXAI_PROJECT`; `IXAI_AIUREXEC`, `IX_CI_CHECKOUT` and `IX_COMPRESS_CHECKOUT` default
  to today's values; scripts under `ix/` locate the project themselves.
  `ixai package-assemble --plonk-key FILE [--out DIR]` writes the `plonkKey` that lets a pinning
  job verify the `aiur-exec` certificate. `lake build` of the default targets (which had been
  failing for want of an `IxAIBench.lean` root), `ix/verify-tests.sh` 40/40,
  `ix/reward-tests.sh` 16/16, `bench-small.tsv` byte-identical. Open: block and tree
  certificates as package routes need a job-format decision (where the block size is committed;
  whether an unproved `train_tree_sound` may yield `PROVED`); generated files still sit in
  `ix/bundle` and `ix/aiur`, which receipts and the index name by path. (Version control since 2026-11-20: the sub-project `IxAI/` on branch `ix-ai` of the Ix fork.)
- GPU trainer review fixes (2026-11-19). `add_wide` uses an early-clobber output; CUDA errors are
  recorded per call, so a failure reports its real cause (`gpu/error-test.sh`); the shim's lazy
  setup runs under `pthread_once`; the tensor GEMM grid is flat (it failed to launch past 65535 row
  tiles). The model and the keys each cross to the host in one copy: in the full run, keys plus
  model take 23 µs per step instead of 108 µs. Tensor GEMMs reuse the previous step's limb counts,
  which the kernel checks on the device, falling back to CUDA cores in the block when an operand
  does not fit, so a step makes 4 blocking calls instead of 24: at 1024^3, 0.42 ms device time
  instead of 0.60 ms and 1.40 ms wall instead of 1.57 ms (the rest is pageable copies). Verified:
  GPU packages 600/600 BLAKE3-identical to `full-bound`, 300/300 random cases equal to `Model.step`
  with 0 refused on every path, and weights and keys of all five triage configs equal to the spec.

In progress:
- One certificate for training and its environment (`ChildKind.aiur`, `offload.md`): finished
  2026-11-20 (Done, above). What follows is the record of what stood in the way and how each
  obstacle was removed. The protocol change is in `~/repos/forks/ix-childkind-aiur` (branch
  `childkind-aiur`, `ad283ad81`) and, with the kernel fixes, in `~/repos/forks/ix-cert` (branch
  `cert`). The environment child compiles: the closure of
  `train_of_deployed_blocks_enc` and `blockRun` (36,760 constants, 234 MB of Ixon,
  `.truthmines/combined/env/consts.ixe`) takes 79 s at 12.6 GB, where it did not finish in 45 min at
  190 GB (all of Mathlib, 783,115 constants, compiles here in 404 s). Two causes, both in the 51
  generated `.obs` path lemmas (`IxAIRefine/ObsGen.lean`), whose terms held 126 million nodes
  (`Fixed::transpose20x16` alone 29.6 million):
  - The proofs are straight-line inversion scripts, and each substitution rebuilt every type that
    mentions the substituted variable: the growing call and value lists in the goal, and above all
    the types of hypotheses already used, each with its own copy of the environment, whenever a
    step renamed the heap. Deferring the list equations, flattening the environment once per
    `let`, and clearing each hypothesis after its inversion give 9.7 million nodes (13x; 31x on
    the largest), and the sources build in 9 min at 8 GB instead of 30 min at 37 GB.
  - Ix's certified compile orders a constant's shared subterms greedily, re-scoring every
    candidate at each pick (`Ix.Sharing.Family.greedyOrderAux`, 77% of the profile). A proof of a
    million nodes costs about two minutes; those of 1.5 and 2.2 million did not finish in 15.
    Cutting each proof every 120 tactic lines into nested `as_aux_lemma` blocks keeps every
    constant under about 300,000 nodes.
  Both rewrites are a post-processing pass over the generator's output (`ix/combined/obs_rewrite.py
  --chunk 120`), applied to the working copy `.truthmines/combined/src`; the generator itself is
  unchanged, and the originals are in `.truthmines/combined/obs-generated`.
  IxVM cannot check this environment as it stands (2026-11-20, execution only, no proving):
  - The static partition gives 4 shards. Shard 0 (1,405 constants) is accepted in 11:48 at 83 GB:
    1.56 billion queries, FFT cost 1.0e13, planned as 73 trace shards. Shards 1 and 3 were killed
    at the 180 GB limit after 26 and 15 minutes (ix was planning against its default budget,
    `MemTotal` less 20%, which is above the limit; `exec_shards.sh` now passes `--max-ram 170`).
    Shard 2 is rejected by IxVM's kernel.
  - Three standalone checks fail with "inferred type is not def-eq to the expected type":
    `Aiur.Generic.SourceSemantics.Represented.builtin`, `Aiur.Represents.project` and
    `Aiur.Circuit.System.ProvenanceModel.heap_sound_cells` (IxVM artifact `5111b234…`,
    `ix/combined/check_consts.py`). A standalone check is transitive (`run_check_transitive`): it
    checks the constant and everything it depends on. The failures trace back to inductive
    types those theorems depend on (below). Lean's kernel accepts all of them.
  - Standalone costs are closure costs, so they cannot be added up. The whole closure of the
    refinement theorem's statement checks in one claim of 191 million queries (65 s, 17 GB).
    `«Fixed::dot20».obs` with its closure is 205 million, of which at least 122 million is the
    closure of the program source `Fixed.source`; the path lemma's own share is at most 85
    million and not measured. An earlier reading here, that the generated path lemmas are each as
    expensive as the costliest Mathlib theorem, came from adding closure costs and is withdrawn.
  A smaller environment used to find the causes (`IxAICombined/Assumed.lean`): the same binding
  with the refinement theorem as a named axiom, which an Ix claim lists in its context
  (`ClaimContext.axioms`). It is a measurement device only: the certificate is to cover the full
  environment, with IxVM fixed where it is slow or incomplete (decided 2026-11-20). Compiled, it
  is 30,489 constants and 57 MB (11 s): 17,594 in the statement's closure by a Lean-side count,
  and about 13,500 auxiliaries (equation lemmas, match splitters, `noConfusion`, `sizeOf` and
  the like) that the certified compile adds for every declaration it reaches
  (`ClosureOptions.selected.units`, `Ix/EnvScope.lean`). Executed without proving:
  - First attempt: as 2 shards, shard 0 was killed at 180 GB after 14 minutes; as 16 leaves, 14
    were accepted and two exceeded 44 GB. Checking those two leaves' constants one at a time
    found one constant in each that alone needs more than 34 GB: `IxAICore.Formula.gen.eq_def`
    and `IxAICore.shuffleAux.eq_def`, the unfolding lemmas Lean generates for two structurally
    recursive spec functions. Nothing references them; they are auxiliaries, and they existed
    only because three proofs in `IxAIRefine/Fixed/TrainSpec.lean` unfolded those functions with
    `simp only [f]` and `rw [f]`. Their sibling equations `eq_1` and `eq_2` cost about 10,000
    queries each, so it is the `eq_def` proofs IxVM's kernel finds hard, not the functions.
  - Fix: `TrainSpec.lean` states the unfoldings it needs by `rfl` (`shuffleAux_succ`, `gen_zero`,
    `gen_succ`) and uses those. A Lean experiment confirms that `simp only [f]`, `rw [f]`,
    `simp only [f.eq_1]` and `unfold f` all create `f.eq_def`, and a `rfl` lemma does not. The
    source in `~/repos/ix.ixai-aiur` carries the same change.
  - After the fix (30,471 constants, root `05ba3755…`): the default 2 shards execute in 74 and
    71 s at 16 GB, 188 and 184 million queries, FFT cost 1.31e12 and 1.29e12, planned as 13 and
    12 trace shards that fit the device. All 16 leaves of the finer partition are accepted too
    (27 to 191 million queries each), but that partition costs seven times as much in total,
    because every claim repeats the axiom's closure. Nothing was proved for it.
  - In an environment with a user axiom every claim checks the axiom's closure
    (`validate_user_axioms` loads the axiom through the transitive check), so a trivial claim
    costs 191 million queries there against 1 million without the axiom.
  The full environment after the `TrainSpec.lean` fix (36,747 constants, 245 MB, root
  `539c35fb…`, 6 shards at a 170 GiB budget): the first shard was still growing past 69 GiB after
  9 minutes, so other expensive constants remain. The rejection is narrowed to inductive types:
  standalone checks of `Aiur.Represents` (a predicate nested through `List.Forall₂`),
  `Aiur.RepresentsArgs` and `Aiur.Generic.SourceSemantics.Represented` fail, and with them
  everything that depends on them. In hand (2026-11-20), each in its own fork of ix: the
  `eq_def` blow-up as an IxVM performance fix (`~/repos/forks/ix-kernel-hints`), the nested
  inductive rejection (`~/repos/forks/ix-kernel-inductive`), both reading the kernel of ix PR 678
  for what it already changes; and a survey of this environment for every other rejected or
  expensive constant (`.truthmines/combined/sweep/full-survey.tsv`).
  - The rejection is resolved (2026-11-20, fork `~/repos/forks/ix-kernel-inductive`, branch
    `kernel-inductive-index-lift`, `23d6ed579`). IxVM's circuit was right to reject: the fault was
    in the model advice, the auxiliary declarations the prover generates for a nested inductive
    block and hands to IxVM to check. Its generator (`genNested`,
    `IxC/Kernel/Frontend/InModel/Nested.lean`) lifted index arguments only past a constructor's
    own fields, so a parameter mentioned in an index pointed at the wrong binder wherever other
    binders intervene; the file's header recorded it as a known gap. A nested block is rejected
    exactly when an index argument mentions a block parameter (minimal case:
    `inductive NB (α : Type) : List α → Type | mk : List (NB α []) → NB α []`);
    `Aiur.Represents` hits it through its implicit `F`. Ix PR 678 makes the same correction
    (`fieldIdxAt`, `ctorIdxAt`), and the fix is that correction ported. The circuit and its
    artifact are unchanged (`5111b234…`): advice is untrusted and checked in full, so the set of
    environments IxVM can be made to accept is the same; only the honest prover now produces
    advice that type-checks. With the fixed `ix` and the pinned artifact all 17 rejected
    constants are accepted, and ix's IxVM test tier passes 17/17 before and after, its
    must-reject suites with unchanged verdicts. Not run: `lake -d IxC build --wfail`, the axiom
    audit, and the whole environment with the fixed binary. To use it:
    `. ix/combined/inductive_env.sh`.
  - The `eq_def` blow-up is fixed in IxVM (2026-11-20, fork `~/repos/forks/ix-kernel-hints`,
    branch `kernel-hints`, `29d988849`; details in `.truthmines/kernel-eqdef`). Cause: before
    dispatching a `Nat` binary operation, IxVM's full `whnf` head-normalized every argument
    (`KernelWhnf::try_nat_dispatch_prewhnf`), even when the operation cannot fire. On an open
    term such as `x * 2685821657736338717` the multiplication unfolds to an addition whose first
    argument is the multiplication again, to a depth of the literal. An `eq_def` proof exposes
    such terms because it needs iota on the function's matcher, which reduces the scrutinee
    `r.below n` to a pair; `eq_1`, `eq_2` and lemmas whose draw is stuck earlier never do.
    Lean's kernel never reduces a `Nat` operation's arguments on open terms. Fix, one function:
    head-normalize the second argument first and make no move if it is not a literal. Every
    success path of the dispatch needs that literal, so the function returns what it returned
    before wherever it terminated. Both lemmas go from killed at 40 GB to 2.16 and 2.08 million
    queries with their closures; the 80 Mathlib sample claims are all still accepted, 0.02%
    fewer rows in total and none more expensive. The IxVM artifact changes (`0cbcb681…`). The
    literal-size experiment that isolates it: `x * 2685821657736338717 % 2^64 % n` never
    finishes, `x * 3 % 16 % n` costs 1 million. Formal proofs to redo in PR 678's terms:
    `try_nat_dispatch_prewhnf_step` (`IxVMRefinement/Whnf/Prim.lean`) and its extraction.
    `KernelInfer::dec_nat` reduces both arguments before checking for literals in the same way;
    not changed.
  - With both fixes the full environment executes (2026-11-20). One build of ix carries the
    tracing commit, the two kernel fixes and the Aiur-child aggregator (fork
    `~/repos/forks/ix-cert`, branch `cert`; `ix/combined/build_cert.sh`; `IX_PROFILE=cert` in
    `ix/ixw`; IxVM artifact `0cbcb681…`, aggregation artifact `80d584ab…`). The three
    `TrainSpec.lean` proofs are back to their original form, so the environment holds the two
    `eq_def` lemmas again, and compiles to the root it had at the start (`30b4a837…`, 36,760
    constants, 245 MB). Its default partition for a 170 GiB budget is 5 shards, all accepted by
    IxVM in execution:

    | Shard | Constants | Time | Peak memory | Queries | FFT cost | Trace shards |
    |---|---|---|---|---|---|---|
    | 0 | 1,540 | 14:19 | 124 GB | 2.18 billion | 1.43e13 | 105 |
    | 1 | 1,368 | 19:53 | 152 GB | 3.03 billion | 1.98e13 | 140 |
    | 2 | 3,512 | 7:52 | 76 GB | 1.23 billion | 7.95e12 | |
    | 3 | 4,579 | 2:40 | 27 GB | 0.37 billion | 2.35e12 | |
    | 4 | 19,990 | 3:00 | 34 GB | 0.42 billion | 2.79e12 | |

    7.2 billion queries in all. Shards 0 and 1 hold the generated path lemmas and are dominated
    by substitution (`KernelSubst::expr_glb` alone is 628 million rows in shard 0); their proofs
    are planned within the budget (proving peak 130 and 159 GiB).
  - The leaf proofs are done (2026-11-20, `ix/combined/certify.sh full leaves`, one GPU; each
    time is execution plus proving, each proof verified): leaf 0 in 30:26, leaf 1 in 45:50,
    leaf 2 in 14:32, leaf 3 in 3:38, leaf 4 in 4:13, 99 minutes in all. Leaf 1's execution
    record passed the prover's 128 GiB ceiling after 17 minutes and the prover cut it into two
    claims by itself (records of 64.7 and 83.3 GiB), so the proved partition has six leaves. The
    prover's record model under-predicts these claims by 2.2x to 6.5x (it predicted 12.7 to
    31.5 GiB). Aggregation first failed on the fork's key pins (`tools/formal-aiur.keys` embeds
    the verifying keys; regenerated and committed for the two changed circuits,
    `ix/combined/update_pins.sh`), then took 9 minutes. The certificate is under Done.
  - Survey of the environment constant by constant (`.truthmines/combined/sweep/full-survey.tsv`
    and the files beside it; 224 of 256 leaves executed alone, 9.5 billion queries, largest 257
    million and 16 GiB): under the fixed builds nothing is rejected and nothing is pathological
    in the way the two `eq_def` lemmas were. The cost is spread: the generated path-lemma chunks
    (`«Fixed::deltas».obs._proof_1_k`, `transpose20x16`, `train_block`, `hidden`: 70 to 250
    million queries per leaf of one to five constants), the spec lemma `transpose20x16_spec`
    (257 million), and the Aiur compiler's `lower_complete._mutual`, `lower_inactive._mutual`
    and `lower_sound._mutual` (241, 209 and 112 million; the first is the largest term in the
    environment at 873,000 nodes). Of the three types that failed standalone, only the nested
    `Aiur.Represents` was rejected itself; the other two are definitions that mention it. 103
    named constants depended on it, the seed theorem among them.
  - PR 678's kernel on the same cases (`.truthmines/kernel-678/RESULT.md`): it has the same
    `eq_def` blow-up (both lemmas ran to a 170 GB limit), so that fix has to be ours; its verdict
    on the inductive types was not obtained by running it (stopped: its first-use setup held
    the job queue for an hour), only by reading its sources as above.
- Learned kernel hints (`kernel-hints.md`): measured, negative. A tracing build of ix (fork branch
  `kernel-hints`, `35e69a3ba`) records every lazy-delta step and per-function rows of an IxVM
  execution. On 80 Mathlib claims (25 costliest, 55 random; 1.09 billion rows) five other hint sets,
  including the inverted order, change total rows by 1.0% at most and improve no claim by 1%.
  Rows go to substitution (38.7%) and loading constants (25.6%); definitional equality is 3.5%.
  The claims load definitions 41,929 times but only 6,283 distinct ones, so grouping claims into
  executions is worth up to about 20% of rows, far more than unfolding order.

- Decision models, where they belong (2026-11-20). Inside Ix's toolchain nothing passes the
  screening (`decision-models.md`: eight candidates against four tests; most fail because Ix
  already has an exact cost formula with a fast search, a profiler, or a canonical rule; a cost
  predictor for partitioning was dropped in favour of profiling out of circuit). The use that
  matters is a judgment inside a Lean or Ix program, after Jev's use-case map: the model answers
  a narrow typed question, the program's code acts, and here the combining rules are proved and
  the model is certified as its specification. A first library for this exists (`IxAIDecide`,
  entry below under Done), with a mapping of the map's agent-harness items onto Lane's decision
  points (delegation and escalation, review triage at merge, budgets, what to surface to a
  worker), where labels are Lane's own kernel-checked records. Limit: these models take typed input and cannot judge free
  text; for text an untrusted encoder would supply committed features and only the head and the
  gate would be certified.
- IxVM substitution performance (2026-11-20, fork `~/repos/forks/ix-kernel-subst`, branch
  `kernel-subst` at `a1a76573e`, on top of `cert`; write-up and per-claim numbers in
  `.truthmines/kernel-subst/NOTES.md`). Seven commits to the kernel circuit, each argued to
  return what it returned before:

  | Workload | `cert` | `kernel-subst` |
  |---|---|---|
  | 80 Mathlib claims, rows | 1,086,113,864 | 875,384,658 (−19.4%; every claim cheaper, all accepted) |
  | of which `KernelSubst` | 420.3 million | 246.8 million (−41.3%) |
  | `«Fixed::dot20».obs`, rows | 209.0 million | 159.9 million (−23.5%) |
  | shard 0 of the full environment, queries | 2.18 billion | 1.10 billion (−49.4%) |
  | shard 0, FFT cost | 1.43e13 | 1.04e13 (−27.5%) |
  | shard 0, peak memory, time | 118 GB, 14:19 | 69 GB, 9:17 |

  Where the rows were: every substitution walk cost two memoized rows per node (a closedness
  test, then a walk with the same arguments); the loose-variable searches walked closed
  subterms (86% of their rows answered 0); spine collection appended with `snoc`, quadratic in
  the spine; and, dominating the generated proofs, the rebase: `k_infer` and `k_is_def_eq`
  lower each open term past its unused innermost binders, which needs a search (`expr_glb`)
  that depends on the cutoff, so a subterm is walked again from every enclosing binder (1.29 of
  shard 0's 2.18 billion queries). The commits inline the walks, prune the searches with the
  cached loose-variable range, collect spines with an accumulator, reorder one search, and make
  `dec_nat`/`dec_int` reduce their second argument only when the first is a literal. Variants
  that had fewer rows but wider circuits were measured and not kept (rows are not cost: one
  reached 1.05 billion queries on shard 0 at FFT 2.03e13).
  Not on the branch: removing the rebase. Without it at all, shard 0 is 515 million queries, FFT
  4.90e12, 41 GB, 3:43 (`exp-norebase`), but `«Fixed::dot20».obs` is 0.6% worse and the rebase
  was added because a Mathlib constant
  (`Algebra.kerTensorProductMapIdToAlgHomEquiv._proof_1`) did not finish without it. Dropping it
  is sound by PR 678's own specifications of the two functions; what is at risk is termination
  and cost elsewhere. `exp-noinferrebase` (`711fdc14f`, nine lines: `k_infer_rebase` always takes the
  unrebased branch) drops only the inference rebase: shard 0 at 520 million queries, FFT
  3.95e12, 40 GB, 3:44, against v5's 1.10 billion, 1.04e13, 69 GB, 9:17. Both branches of
  `k_infer_rebase` meet the same specification, so the change is sound; what it may lose is
  what the rebase was added for (upstream #560: open inference workloads that did not converge
  in practical time, with a fixture). In hand: that fixture, the Mathlib sample and shards 1 to
  4 under it, and a cheaper middle design if it is not clean. The design that removes the cost altogether is Lean's: open binders with free
  variables named by de Bruijn level, so that instantiation walks only the paths to the
  variable replaced and no rebase is needed; that touches every kernel module that walks
  binders. Changed functions and the PR 678 proofs they affect are listed in the notes.
- Where the environment's proving cost is, and what is being done about it (2026-11-20). The 99
  minutes of leaf proving are not spread over the 36,760 constants. A 224-leaf execution of the
  environment (`.truthmines/combined/sweep/full-survey.leaves256.*`, 9.54 billion queries on the
  survey build) puts about 71% of the queries in leaves made of this project's own generated
  path lemmas (`IxAIStep.Fixed.Obs.«Fixed::f».obs` and their `_proof_1_N` pieces: 1,648 of
  23,447 constants), 16 to 21% in the Aiur compiler's proofs and a few percent in Lean's
  library; the 50 most expensive leaves hold 179 constants and 63% of the cost. In the
  certified partition, shards 0 and 1 (3,562 constants: those lemmas and Aiur's proofs) are 5.2
  of 7.2 billion queries and 76 of the 99 minutes; the 29,750 constants of shards 3 and 4 take
  8 minutes. In hand, in this order of expected effect: the shape of the generated proofs
  (their inversion scripts were tuned for compile cost, never for checking cost); the kernel's
  substitution cost (`kernel-subst`, merged into `cert` with regenerated pins, `9a54ac3a5`,
  IxVM artifact `1b348b95…`); the rebase experiments. Shard 0 proved on the one GPU with the
  standalone binaries (`kernel-subst/bin/prove0.sh`, 2026-11-20; light jobs ran beside it):

  | Kernel | Shard 0 proved in | of which execution | Peak memory |
  |---|---|---|---|
  | certified (`0cbcb681…`) | 30:26 | about 14:19 | 123 GiB |
  | `kernel-subst` (committed) | 16:27 | 9:35 | 74 GiB |
  | `exp-noinferrebase` (experiment) | 5:42 | 3:16 | 46 GiB |

  The same experiment on the 80 Mathlib claims: all 80 accepted, 923 million queries against
  `kernel-subst`'s 875 million (+5.4%; per claim −5.1% to +38.8%, median +2.7%, 4 claims worse
  by more than 10%) and the certified kernel's 1,086 million. So the inference rebase pays a
  little on ordinary Mathlib declarations and costs a great deal on the generated refinement
  proofs; the bounded-search variant (`infer-rebase-shallow`) is meant to keep both.
 The cost
  is paid once per program and toolchain, not per training run: a run is joined to an existing
  environment root in 22 seconds.
- Generated path lemmas, proof shape (2026-11-20, lab in `.truthmines/combined/src/Aiur/ShapeLab/`).
  `ix/combined/obs_rewrite.py --fuse --chunk 40` (opt-in; the default mode still reproduces the
  certified files byte for byte) rewrites the generator's inversion scripts in continuation
  form: one lemma application per construct from a new library `IxAIRefine/Core/Fused.lean` (61
  theorems), whole inversion of variable and `x[i]` arguments, plain calls and `let`s with flat
  patterns, lookups by `rfl`, consumed hypotheses cleared, a cut every 40 lines. Statements are
  unchanged and all 51 lemmas elaborate (about 2 minutes against 9). Measured on term size
  only: distinct (subterm, binder depth) pairs fall 3.9 times and summed binder depth 8.9
  times over all lemmas (`transpose20x16` 6.4 and 17.6, `deltas` 6.7 and 22, `step` 3.9 and
  11). Chunk size alone changes nothing; the gain is fusing plus clearing. Weighted by the
  survey's per-lemma cost, the path lemmas would fall to about a fifth, roughly half of the
  environment's 7.2 billion queries, if IxVM cost follows those measures. Not yet measured in
  IxVM at all: `ShapeLab/measure.sh run1` (baselines, statement-only floors and variants for
  three functions) has been queued since 15:22 behind the kernel jobs; results will be in
  `/opt/dlami/nvme/ix-ai/shapelab/run1/summary.tsv`. Open risk: `rfl` lookups make the kernel
  compare strings about 2,000 times, which the size measures do not see. Regenerating the
  canonical tree waits on the measurement.
- A second combined certificate with the deployed model's card and gate decisions in the
  environment (`IxAICombined/Deployed.lean`, `envc.sh deployed`): deferred until the generated
  lemmas and the kernel are settled, so that the environment is re-proved once. Its soundness
  benefit is modest: it replaces a comparison across two certificates by one inside a single
  environment, and the checker must still confirm that the model constant encodes to the run's
  final commitment (done by script today: 331 of 331 words equal).
- Second external review, premise selection (2026-11-20; parked behind the current goal, code
  in the working directory, builds, not yet measured at Mathlib scale). Baseline on the code
  as it was (all digests as recorded): module split 918 s (prepare 26.9 s, training 178 to 202 s
  per epoch, ranking 421 s, 6.14 GB peak); time split 1,959 s (ranking 437 s, 6.48 GB). The
  main cost was not on the review's list: `modelScore` bound the library embeddings in a `let`
  above a lambda, and Lean compiles such a definition to take the lambda's arguments, so all
  270,304 premises were re-embedded for every ranked theorem (confirmed in the generated C);
  `ScoreFn` now computes them once, in parallel. `Digest`'s hash and equality copied the bytes
  into an array on every lookup; they now read in place (`hash_digest` proves the hash values
  unchanged). Also: reachability as a bitset (about 14 MB for about 0.9 GB), streamed
  `decls.tsv`, list-free `ofHex?` and `normName` (both proved equal), softmax gradients summed
  over a theorem's gold premises before one outer product (old `step` kept as the
  specification and compared on the first 1,000 steps of each run), shared IDF overlaps
  (proved), `top30` from the IDF top 500, allocation-free `ofOrder` (proved), `splitOf` in one
  pass (proved), `TypedXhard` returning its timed results. Not done, with reasons: sparse
  gradient rows (the premise gradient touches most rows, so the review's 98% figure is wrong
  for it), `Int64` (no bound is proved in advance), candidates from import ranges (small once
  equality is a memory compare). `bench small` is byte-identical (`dea98701…`), and ran in
  16.1 s against 27.4 s on a light run. The Mathlib-scale run after the changes
  (`review2-premises/job.sh after1`, about an hour) is held until the goal's jobs are done.
  Tested but not proved: the bitset against the list reachability, `topBy` prefixes, the
  marked pool union, the new `step` against the old.
- Second external review, the rest (2026-11-20): in hand, split by subsystem. Premise
  selection at Mathlib scale and the typed benchmarks (`IxAIData`, `IxAIBench`); the GPU
  trainer (`gpu/cuda/step.cu`); the verification pipeline and reward path (`IxAIVerify`,
  `IxAICli/Reward.lean`); the decision library's test and training time. Done directly: one
  shared `/proc` sampler in `ix/combined/check_consts.py` in place of a scan per worker;
  `certify.sh`'s machine paths gathered into overridable settings; the project is
  under version control as the sub-project `IxAI/` on branch `ix-ai` of the Ix fork
  (`~/repos/forks/ix-ai`), beside the Aiur program and refinement proofs (`Aiur/IxAIRefine`,
  `Aiur/IxAIStep.lean`, `Aiur/IxAICombined*`) and the prover changes it depends on; sources only:
  toolchain copies, artifacts and the store are ignored. The working directory is still
  `~/repos/ix-ai-pipeline`, whose scripts assume that location.

Blocked on a decision:
- One certificate for the full model needs the `aiurExec` aggregation change in Ix (below). The
  `Fixed::train` proof cannot enter the compression pipeline or aggregation as is: its entry circuit is 238,264
  columns wide and Ix's verifying-key format (`stark-key`) stores widths in u16 (keygen panics);
  `train_block` (14,554) and `step` (3,101) fit. So `aiurExec` would carry 600 step (or 30
  `train_block`) children chained by IO, matching `train_of_deployed_steps`. Wrapping step claims
  directly as the compression pipeline's root (key and claims as data, no protocol change) does not work either: the
  batch format and the wrap verifier take many claims, but Aiur's prover emits one claim per proof,
  and even one `Fixed::step` batch root overflows the pinned wrap layout (`G_cold0` 1.52x its 2^18
  rows; 1.34x with blowup 4 / 50 queries, 4.9 MB proof), so it needs a new wrap layout and with it
  new GL, narrow and PLONK keys.
  Prototype done 2026-11-19 (fork `~/repos/forks/ix-aiurexec`, branch `aiurexec-prototype`,
  `docs/aiur-composition.md` there): a separate `AiurExec::aiur_exec` aggregator (key as data,
  IxVM and `ix_aggr` unchanged) aggregated the 600 step proofs into one root, and the compression pipeline
  compressed it to a 584-byte PLONK certificate (`d8551c47…`, every pipeline check passing; root key
  `6638d08d…`, output claim `df9df4eb…`: 600 executions, m0 to the expected weights); an
  independent `aiur_exec_check` (keys recompiled, chain rebuilt from the spec) accepts the root
  (`.truthmines/aiur/aiurexec`). Joins proved like `ix prove --aggregate` (resident GPU prover,
  record-pool admission, dependency-driven joins, streamed trace shards; `aiur_exec_tree`): 597
  joins in 38:43 at 145 GB peak, 3.6 s per join on the device (CPU: 48 s, 97 GB per join), then
  two normalized wraps to fit the pinned wrap layout and the compression pipeline (202 s). With 30
  `Fixed::train_block` executions (20 steps each) instead, and an `AiurExecBlock` aggregator for
  their claim shape, the whole run goes from block proofs to a 584-byte PLONK certificate in 509 s
  on the one GPU (`.truthmines/aiur/aiurexec-block`): block proofs 23 s, 59-node tree 258 s, wraps
  29 s, compression pipeline 199 s; root key `4c900afc…`, certificate `20d80b11…`, `aiur_exec_check` accepts (30
  executions, m0 to the expected weights). Packages and aggregator are exported once per circuit
  (136 s and 87 s). The double-wrapped block root uses 0.99 of the wrap layout's `G_cold0`, so a
  further wrap may be needed for other roots. The Lean side covers step claims
  (`train_of_deployed_steps`); block claims need the same for a deployed `train_block` package.
  One execution instead (2026-11-19, fork branch `single-proof`, `docs/aiur-composition.md`
  there; `.truthmines/aiur/single`): `FixedTree::train_tree` (`Aiur/IxAITree.lean` in the
  ix.ixai-aiur worktree) runs all 600 steps in one execution with a narrow 697-word claim
  `m0 ‖ lr → root ‖ m600`. Batches come from hint channels as range-checked bytes, each step is
  `Fixed::step` unchanged, and `root` is a BLAKE3 Merkle tree whose leaf i hashes the model after
  step i and batch i, so it commits to the data and to all 600 intermediate models (any step can
  be opened). `Fixed` and the step/block keys are unchanged. The proof is one trace shard (4.0M
  rows, 276M cells) proved on the GPU in 4.6 s (0.83 s proving, 16 MB); one `AiurExecTrain` leaf
  (20 s) and one normalized wrap (13.5 s) fit the pinned wrap layout at `G_cold0` 0.96 (the leaf
  alone is 1.55x); the compression pipeline makes the 584-byte certificate (`26eb66b9…`, 197 s,
  every check passing; root key `8ee3db8d…`, output claim `32ec9bea…`, Merkle root `2df512a2…`).
  251 s end to end (315 s in a repeat run whose compression pipeline took 259 s) against the
  block route's 509 s, with three recursive proofs instead of 61;
  `aiur_exec_check --tree` accepts (keys recompiled, Merkle root rebuilt with the `blake3` crate
  from the spec's batches and models) and rejects a changed model, batch word or output. Lean:
  needs `train_tree_sound` (statement and plan in the fork doc), not yet proved; the extra
  assumption over `train_of_deployed_steps` is BLAKE3 collision resistance plus a refinement of
  the Aiur BLAKE3 library to BLAKE3.
  What needs sign-off:
  adopting this as Ix's `aiurExec` claim and `ChildKind.aiur` (the certificate binds the
  aggregator's key, not an Ix claim), and composing it with the IxVM environment root.
- Baselines: Opus 5.5 via sub-agents (Baseline protocol); no Jev runs.

## Milestones

| | Milestone | Done when | Depends on |
|---|---|---|---|
| M1 | Full triage model, one certificate | One PLONK certificate covers training (Aiur circuit, `train_refines` without a bounds hypothesis), evaluation card and safety theorems | `aiurExec` sign-off (re-prove and one-`Fixed::train` STARK done 2026-11-19) |
| M2 | Certified learning that helps proving | Measured on held-out Mathlib theorems: the learned premise selector (or policy) improves proof-search throughput (theorems closed per CPU-hour), solver cost (nodes or time per closed goal) or the rate of premise-guided proofs, against solver-only and heuristic (IDF, frequency, name-overlap) baselines with comparable tool access and budget; one certificate covers data root, training and evaluation | a proof-search harness with a fixed solver and budget; fx16 spec path; the curated `mathlib-full` dataset |
| M2b | Kernel-decided typed questions (Jev-style) | Typed answers with calibration comparable to a Jev or frontier baseline on kernel-labelled propositions (labels certifiable as Eval claims), ≥100× cheaper and faster | generator done (`IxAICore/Typed.lean`); instances hard for Opus 5.5 (98–100% on `baseline-v1`; 40-atom `prop-hard`: Opus 40% = majority, ours 79%, 100% with certificates); a model that learns beyond surface form (current: majority or form-only) |
| M3 | Certified RL | A policy trained by `rlTrain` on M2 or M2b, beating fixed policies, certified like training, with the gamed-reward check | M2 or M2b; RL target circuit |
| — | Deferred: tactic router, elaboration-level rewards | — | Ix's provable elaborator |

Accuracy is held to near-parity on narrow tasks with checkable answers; the order-of-magnitude
targets are cost and latency, and verification is what baselines cannot offer. M2's measure
changed on 2026-11-19 (external review): recall against a frontier ranker says how well a model
imitates a ranking, not whether learning makes proving cheaper. The question is now whether the
certified model improves what a solver achieves under the same tools and budget; recall@k stays as
a diagnostic.

## Baseline protocol

Comparable to the Jev vs Claude Opus 5 Banking77 study (`references.md`), adapted to tasks with
certified labels:
- Baseline: Claude Opus 5.5, run as sub-agents of this session answering fixed batches zero-shot
  with a strict typed answer per item; no Jev runs. Recorded: answers, tokens (total and per item),
  wall time per batch.
- Metrics: accuracy (or recall@k / MRR for ranking) with bootstrap CIs and a paired-bootstrap gap;
  macro-F1 and balanced accuracy where labels are imbalanced; invalid responses; ECE after a
  per-question calibration fit on held-out labels; cost and latency per 1,000 decisions; a
  confidence cascade (small model first, Opus on low confidence).
- Reference points: decision models trail the best LLM by a median 11.6 macro-F1 points at ~44×
  lower cost; Jev is 3.4 points under Opus 5 on Banking77 at 22× lower cost and 13× lower p50
  latency. M2 premise selection compares against ReProver (R@10 38.4%) and LeanPremise (R@16 61.1%).
- Integrity: evaluation sets are fresh (generated from a seed committed after training, for M2b) or
  held-out modules (M2); every score is a certified card.

## Decisions

| Date | Decision | Why |
|---|---|---|
| 2026-11-18 | Prove training with a dedicated Aiur circuit plus a one-time refinement proof, not by kernel evaluation in IxVM. | Kernel `decide` of 600 steps took ~6 GPU-hours over 400 shards; the circuit proves them in 32 s. The gap is interpretation overhead and grows with the model. |
| 2026-11-18 | Compose the training proof with IxVM proofs by aggregation, with a key-as-data `ChildKind.aiur` and an `aiurExec` claim. Awaiting sign-off. | One protocol change, after which new circuits and models never touch IxVM or `ix_aggr`, so typechecking proofs and compression keys stay valid. Lookup circuits inside IxVM would change its key with every circuit. (`aiur-composition.md`) |
| 2026-11-18 | A fixed set of numeric primitives may go into Ix's own pipeline once. | Generic, stable primitives change IxVM once, not per model; per-model circuits use the aggregation route. |
| 2026-11-18 | Default numeric format: fixed point with 16 fractional bits; keep block floating point for larger models and FloatLib f32 for IEEE semantics. | Best and tightest held-out accuracy in the sweep, cheapest to prove (field arithmetic), exactly associative so GPU-deterministic. |
| 2026-11-18 | RL: contextual bandit with the exact expected advantage over a typed action set, regressed by the existing training step. | No sampling variance or importance weights; reuses the step circuit and its refinement proof; deterministic schedule. (`rl.md`) |
| 2026-11-18 | The proof-search loop is an IxAI agent over deterministic Ix tactics; its interface speaks Ixon, not JSON. | Content-addressed goals and results are cacheable, replayable facts; no REPL or external prover is needed. A JSON shim for external provers is optional and outside the core. |
| 2026-11-18 | GPU training via a small Rust/CUDA crate with exact integer GEMM on int8 tensor cores (16-bit operands split into 8-bit limbs, int32 accumulation). | Integer accumulation is exactly associative, so results reproduce the Lean spec on any GPU; outputs are checked by the Aiur step proofs. |
| 2026-11-18 | Trust model for GPU training: certified results, not certified compilation. The GPU trainer is untrusted; correctness comes from certificates of `train spec config = W`. Its main job is witness generation: emitting each step's hint values (rounding quotients, sign bytes, inverses) in the Aiur prover's format, so the circuit only checks. Lean theorems relating the GPU algorithm to the spec are design-level assurance. | Training's output is what must be correct, and certificates prove it regardless of who computed it. A GPU backend for IxCC would need verified tiling, memory layout and a PTX semantics, and is unlikely to match hand-tuned kernels; a narrow library of proved coarse primitives is the fallback if per-run certificates ever bottleneck. |
| 2026-11-18 | Version control and cluster on Ixon (`ixvc.md`): Unison's model (names as metadata, immutable namespaces, hash-keyed classified edits, conflicts as data) plus a Unison Cloud-style control and data plane, with certificates replacing trust in workers. Source comes back via `ix decompile` extended with metadata recorded by Ix's elaborator (tactic scripts, comments, layout), not a separate source layer. | Shared store instead of worktrees, semantic diffs and merges, proof-aware propagation, results checkable by anyone, and agents exchanging addresses instead of transcripts. |
| 2026-11-18 | Start the cluster in local mode: one server owning the GPU and store, running train → witnesses → prove → aggregate → PLONK → record, with verification kept. | No untrusted parties locally, so no control-plane/worker split is needed; one GPU owner removes contention; the same job and result formats extend to distributed mode. |
| 2026-11-18 | GPU trainer host in Lean, kernels in CUDA C behind a thin C shim called via `@[extern]`; no Rust crate. Port once the first (Rust-hosted) version reports. | Performance is in the kernels, not the host; the witness format is defined in Lean (`IxAIStep` `hintTable`/`exportAll`) and is reused rather than reimplemented; Lean's C FFI already serves BLAKE3; Rust is being phased out as IxCC matures. |
| 2026-11-18 | Bounded arithmetic in the spec: value and accumulator bounds are part of the config, and leaving them is a defined training error. Runtime implementations are fixed-width (Int64 operands with Int64 or 128-bit accumulators on CPU and on GPU, where CUDA builds `__int128` from 64-bit add-with-carry and `mul.hi`/`mul.lo`; int8 limbs with int32 accumulation on tensor cores; range-checked field elements in Aiur), each with a theorem that within the bounds it equals exact integer arithmetic. Lean `Int` appears only in proofs; no unbounded fallback path. | Unbounded integers switch to bignum arithmetic above 2^63 and would be slow exactly when needed; one bound shared by every implementation and the circuit (2^55) keeps all of them exact and agreeing. |
| 2026-11-18 | Grading and RL rewards run entirely on the pure side: model-written source goes through Ix's own provably contained elaborator (no `IO`, fuel-bounded user macros and tactics) and then the kernel; "this source elaborates to this term" is itself a claim. Real sandboxes are needed only for environments that deliberately touch the outside world. | Lean's own elaboration runs arbitrary `IO` (`#eval`, `run_cmd`, tactics), so REPL-graded RL needs sandboxes; a pure elaborator removes code execution from the grading path and makes rewards certifiable at the source level. The OpenAI–Hugging Face incident (July 2026) was an escape from an impure eval environment in pursuit of an answer key; pure environments, spec-defined checkers instead of stored answers (reference data only as commitments), and fresh evaluation instances generated from a seed committed after training remove the target. Address matching is exact deduplication only (bound-variable and global renaming); it catches accidental duplicates and contamination but not an adversary, who can reorder arguments, eta-expand, unfold or choose another proof. |
| 2026-11-18 | Environments in three tiers: (1) pure, evaluated in the spec; (2) certified, real x86 binaries compiled by IxCC with effect bounds proved on their Ix source (grader, task server, package proxy, agent tools); (3) uncertified third-party software, conventionally sandboxed and marked as trusted base. | IxCC carries source-level properties to the binary, so containment for most infrastructure is a proof rather than a container; what remains trusted is the CPU, OS interface and loader, plus explicitly uncertified targets (e.g. real buggy software in cyber evals). |
| 2026-11-18 | Labels and rewards use spec-defined fuel, never wall-clock time; environments are named by hash. | Timeouts make labels depend on machine load; loose version pinning makes them irreproducible. |
| 2026-11-18 | Tier 1 data: premise selection on `Mathlib.Order.Basic`, `Mathlib.Logic.Relation`, `Mathlib.Logic.Function.Iterate` and their imports. Declarations come from a Lean 4.34.1 script over the Mathlib build Ix compiles (`ix/premises/Extract.lean`), addresses from `ix compile --consts-file` plus `ix diff` against a name-stripped env; items are keyed by Ixon address and curated by pure rules in `IxAIData/Rules.lean`; test = whole modules with a proved dependency-respecting split. (`data.md`) | Ix as a library needs Lean 4.34.1 and its Rust archives, so it cannot link into this 4.34.0 project; the pipeline's own Mathlib is 4.34.0, so its declarations would not be the ones Ix addresses. The CLI route uses only the existing `ix` binary and gives every named constant's address in one pass. |
| 2026-11-18 | Tier 1 premise selection: a bilinear two-tower scorer in Fx16 (`IxAIData/Scorer.lean`) trained by a pairwise hinge loss with hard negatives, evaluated on a module split and a time-ordered split, against frequency and IDF baselines with MRR. Fx16 is a new definition beside `IxAICore.Fx`, which certified artifacts depend on. | The fx8 relevance MLP died at batch > 1 and ranked below frequency; a decision MLP is the wrong shape for ranking. The module split hides the same-module lemmas that are most gold premises, so the time split is the meaningful one; IDF overlap is the baseline to beat. |
| 2026-11-19 | Premise scorer v2: hashed declaration-name tokens in both towers and name-overlap pair features (`nameToks`, `nameContext`); a leave-one-out training prior (`pairContext … selfUse`); a listwise softmax loss beside the hinge loss; an optional residual over a frozen IDF weight; the negative mix, loss, residual, name tower, learning rate and epochs chosen per split by validation MRR (`scorerGrid`, 192 configs). A larger Mathlib slice is not extracted. | Names are Ix metadata beside the content addresses, so they change no address, and they are what Opus reads. The training prior counted each theorem's own proof, so `prior > 0` marked every gold premise in training and none of the held-out-module ones; removing that leak moved the module split from 7.8 points below IDF to level with it. Validation could not separate residual from free IDF weight, nor bigram and reverse-coverage name features (tried, removed), so the simpler forms stay. Extracting a larger slice is cheap (the current one: 3 s extract, 16 s compile) but `extract.sh` writes `PremiseScope.lean` into `~/repos/ix.ixai-aiur`, which this round did not touch. |
| 2026-11-19 | Premise scorer v3: learning rate decayed linearly to 0 over the run (`decay`); neighbour votes (the premises of the 8 training theorems most similar by IDF-weighted constant and name Jaccard) and co-usage as pair features, from training statistics that leave out what a held-out theorem could not see (`LeaveOut`: own proof, whole module, or later theorems of the module); head-argument and hypothesis cross features; seed ensembles. The selection grid is decay-only (`scorerGrid`, 48 configs per split). | Without decay, validation MRR swung from epoch to epoch (module split, epochs 5–10: 0.33, 0.07, 0.33, 0.13, 0.31, 0.33) while weight magnitudes grew smoothly, so v2's pinned configs were picked at a lucky phase; rounding to nearest changed nothing, decay removed the swings. Votes, co-usage, cross features and ensembles stayed within validation noise (±0.02 MRR on 103–126 theorems); votes help only with leave-module-out statistics (time split, leave-self: −0.06 MRR). Statistics use inverted indices, so their cost grows with postings, not with training-set pairs. |
| 2026-11-18 | IxBench v0 (`ixai bench`): one report over triage, RL, premise selection, shift, integrity and cost, in integer arithmetic with fixed bootstrap seeds and a BLAKE3 over the results file; wall clock kept outside the digest. Premise scorers use the configs validation selects, pinned; `full` re-runs the selection and checks it. LLM baselines run on exported 25-item text batches and are scored on the same items by `ixai bench score`. | A single deterministic digest makes regressions visible and the report itself checkable; pinning keeps `small` at 13 s; plain-text batches let sub-agents answer without tools or JSON. |
| 2026-11-19 | M2b questions: STLC typing (de Bruijn, 5 context variables, terms of size 80–160, half mutated to a type error; "typechecks?" and "which of 4 candidate types?") and propositional status of random 3-CNF at the satisfiability threshold (12 atoms, 52 clauses) or its De Morgan dual. Labels by `infer` and full enumeration; evaluation from seed 20261119, which no training config uses, with exact duplicates removed. A separate results file `bench-typed.tsv`, run by `ixai bench typed` and after `ixai bench full`. | Labels are pure, total and proved against a relational or semantic spec, so each is a kernel-checkable fact. Random formulas of depth 5–8 (with or without forbidding constant subformulas) gave tautologies and contradictions with one shallow reason, which a careful solver spots; threshold 3-CNF is the standard hard distribution. A separate file keeps the v0 digests unchanged and `small` at 13 s. |
| 2026-11-19 | Harder M2b propositional instances: threshold 3-CNF over 40 atoms with 170 clauses (ratio 4.25) or its De Morgan dual, as a new family `prop-hard` beside the 12-atom one; labels by a DPLL procedure (unit propagation and splitting on a shortest clause, fuel = total clause length + 1) proved sound and complete against the semantics (`fastStatus_eq : fastStatus n f = status n f`), which also labels the 12-atom family. Model features add failed-literal counts, propagation length, polarity imbalance and how early a DPLL capped at `4n` nodes finds a model. | Opus 5.5 was at 100% on 12 atoms, which unit propagation and a few case splits settle by hand; at 40 atoms DPLL needs 340–1,350 nodes (median 680, 39 draws) to refute an unsatisfiable draw, against 257 at 30 atoms, far past a careful hand derivation. 40 atoms keeps the whole typed bench at about 3 minutes (labels ~2 ms each). The same theorem makes the old labels identical (old rows of `bench-typed.tsv` unchanged), so v0 and v1 digests and batches stand. The capped search is a one-sided certificate, cheap (≤ `4n` nodes), and the only added feature that moved validation accuracy. |
| 2026-11-19 | `prop-hard` certificates: a refutation search `Dpll.lookahead` (unit propagation and failed-literal probing with learned units at each node, then splitting on the literal of greatest binary/ternary weight product; depth 6, at most 16 nodes, one closure pass per node), proved sound (`lookahead_sound`, `refuteCore_sound`: `refuted → ¬ Sat`), and `certify` (`certify_sound : certify n c f = some s → status n f = s`), which answers by theorem when the core is refuted or the `4n`-node DPLL finds a model (and a clause is falsifiable); otherwise the model answers, trained with the refutation result as feature 27, and may defer below a confidence threshold chosen on validation (seed 31337) for 95% accuracy on answered items. A new section `prop-hard-cert` beside the unchanged `prop-hard` rows; `IxAICore.lean` no longer imports `Typed`/`Dpll` (only `ixai` uses them), so edits there do not rebuild `ix.ixai-aiur`. | Failed-literal closure is what plain DPLL lacks here: on 600 validation draws it refutes every unsatisfiable core within 16 nodes (mean 4–5; with three closure passes per node 15 at the root, 182 within 3 nodes, 314 within 6, 367 within 8, 381 within 12; one pass, as used, also 382 of 382 and cheaper), against DPLL's median 680, at ~5 ms per core; the lookahead branching rule (product of propagation drops) refuted no more and cost ~30% more. So the certificates decide 80% of fresh items and every uncertified one is satisfiable; budgets 3–6 leave 41–66% to the model, where the defer option is what keeps answered accuracy at 96–97%. The typed section takes 210 s (was 114 s), most of it the second `prop-hard` training. Exported batches, keys and every earlier row of `bench-typed.tsv` are unchanged. |
| 2026-11-19 | Local Truth Mines store of Lean libraries compiled by Ix (`ix.ci-merge-tests` `de597000`, Lean 4.34.1) under `.truthmines/store/` (`index.tsv`; BLAKE3 of every `.ixe`): all of Mathlib `d13f23b7` with Lean core and its dependencies as one whole-environment compile (783,115 constants, 689,237 addresses, 2.35 GB, env root `83584d17…`, 6 min 50 s, 66 GB peak RSS), plus Lean core, FLT, CSLib and PhysLean on the same Mathlib. A full-Mathlib premise dataset (`datasets/mathlib-full`: 267,064 items, 270,304 library theorems) comes from the existing extraction route. (`data.md`) | The Mathlib build Ix compiles was already complete, so the whole store costs minutes. Names map to the same addresses in every compile (whole env, closure compile and `order-basic`), so datasets can join on addresses across scopes. IxC checks the whole environment natively in 32 min with 0 rejections; only unsafe meta code in core and Aesop is declined. An IxVM proof of Mathlib is about 2 GPU-hours (Ix's Nov 17 run) and was not run. Before full-Mathlib training, `curate` needs hash-set forms of `dedup` and the split, which are quadratic in lists (an estimated 5.6 h interpreted). |
| 2026-11-19 | Premise selection on all of Mathlib (`mathlib-full` in `scopes`): curation through hash-set forms of `dedup`, `split`/`splitBy`, `disjoint` and `premiseRule`, each proved equal to its list specification (`dedupFast_eq`, `splitFast_eq`, `splitByFast_eq`, `disjointFast_eq`, `premiseRuleSet_eq`, `curate_spec`); module split by FNV-1a of the module name (1 in 50 test, 1 in 50 validation); training through candidate pools (`Pool`) and an array Fisher–Yates (`shuffleArr_eq`); `ixai bench mathlib-full module\|time\|rerank` with its own digests. Configs from a 5-config validation grid around the pinned one: 2 epochs, rounding to nearest (time: lr 1024). (`data.md`) | Curation of 267k items takes 28 s instead of ~5.6 h, and reproduces `order-basic` exactly. The pinned 12 epochs are ~46,000 steps per epoch here (160 on `order-basic`); on the module split they leave the score bound, on the time split they stay in bounds but are 0.036 MRR below 2 epochs; 1–4 epochs are within 0.01 validation MRR. More data did not close the top-of-list gap to Opus on the `order-basic` rerank items (MRR 0.381 v. v3's 0.385). |
| 2026-11-19 | M2b family past failed-literal reasoning: `prop-xhard`, Tseitin parity formulas on uniform connected 3-regular graphs with 16 vertices (24 atoms), unsatisfiable (odd charge), satisfiable traps (odd charge, the clause the planted assignment falsifies removed) and even instances, 0–3 planted noise clauses, CNF or dual; generator claims checked by `XInst.check` with `XInst.check_sound` (claim = `status`), labels still `fastStatus`; separate command `ixai bench typed-xhard` and results file, export to a new `baseline-v3` holding only `prop-xhard-01..04`; training seeds chosen on validation. | Tseitin clauses never become unit after one assignment, so the 16-node failed-literal refuter that solves `prop-hard` refutes 0 of 397 unsatisfiable validation cores (3 at 256 nodes), while ground truth is known by construction (parity argument, proved) and DPLL still labels in ~1 ms (median 3,331 nodes). 16 vertices keeps labels cheap; traps make "satisfiable" not cheaply certifiable (the capped DPLL misses 31% of them). A separate command keeps every `bench-typed.tsv` row and the v0–v2 exports byte-identical. The existing training is seed-fragile (2 of 5 seeds end at majority), hence validation-chosen seeds. |
| 2026-11-20 | The combined certificate covers the full environment of the refinement theorem, not a reduced one. Where IxVM or Aiur is slow or incomplete on it, fix IxVM or Aiur (in forks of ix, preserving semantics and soundness) rather than work around it in the Lean sources. Ix PR 678 is a source of ideas; no rebase onto it for now. | IxVM should scale to millions of lines of Lean theorems; a workaround in one project's proofs leaves the cost for every other user. |

## Results

Premise selection, `order-basic` (`ixai premises run order-basic --split both`, bilinear scorer
dim 16, Fx16, config chosen by validation MRR; every accessible library theorem is a candidate).
v2 (2026-11-19) adds name features, the leave-one-out prior and the listwise loss; v1 is the
address-only scorer:

| Split | Ranker | R@1 | R@5 | R@10 | MRR |
|---|---|---|---|---|---|
| module (208 test, 1,377 candidates each) | bilinear model v3 (softmax, 0 IDF + 12 module + 8 random, lr 4096 decayed, 12 epochs, no votes) | 8.7% | 28.8% | 36.7% | 0.276 |
| | bilinear model v2 (softmax, 0 IDF + 12 module + 8 random negatives, lr 4096, 4 epochs) | 6.9% | 27.1% | 38.1% | 0.260 |
| | bilinear model v1 | 3.4% | 19.2% | 30.3% | 0.183 |
| | frequency | 0.0% | 2.3% | 3.2% | 0.029 |
| | IDF | 6.9% | 25.0% | 38.1% | 0.254 |
| | name-IDF (`nameRankScore`) | 5.8% | 20.4% | 30.6% | 0.209 |
| | earlier fx8 relevance MLP | 0% | 0.5% | 2.6% | n/a |
| time (157 test, 719 candidates each) | bilinear model v3 (softmax, residual, 0 IDF + 4 module + 16 random, lr 4096 decayed, 12 epochs, 8-neighbour votes, leave-module statistics) | 16.0% | 42.3% | 60.3% | 0.420 |
| | bilinear model v2 (softmax, residual, 0 IDF + 4 module + 16 random, lr 4096, 8 epochs) | 16.0% | 41.5% | 58.4% | 0.407 |
| | bilinear model v1 | 11.3% | 34.9% | 47.0% | 0.327 |
| | frequency | 4.3% | 11.7% | 17.6% | 0.126 |
| | IDF | 9.4% | 30.1% | 46.6% | 0.291 |
| | name-IDF | 13.7% | 29.4% | 40.7% | 0.332 |

v3 (2026-11-19, configs chosen by validation before the test numbers were read): level with v2
within the paired interval on both splits (time +1.9 R@10, +0.012 MRR; module −1.4 R@10, +0.016
MRR; table in IxBench below), so the top-of-list gap to Opus is unchanged. What helped: decay, for
stability only (every decayed config within 0.02 validation MRR of the best; no collapses). What
did not, on validation: neighbour votes (≤ +0.02 MRR time, nothing module; the vote ranking alone
is 0.349 test MRR on the time split, between IDF and the model), co-usage with the IDF top 5–20,
head-argument and hypothesis cross features, 4-seed ensembles, rounding to nearest, IDF-mined
negatives tailored to reranking (16–30 per theorem: worse and unstable), `later` statistics. The
remaining gap looks like knowledge the statement shapes and names do not carry, not training.
`ixai premises run` (48 configs per split) takes 8 minutes for both splits.

v2: on the time split the model leads IDF by 11.7 points R@10 and 0.115 MRR, both outside the
paired bootstrap interval (IxBench below); on the module split it is level with IDF (+0.0 R@10,
+0.005 MRR), where v1 was 7.8 points below. What helped, by validation and test: the
leave-one-out prior (the largest single change on the module split: before it, v2 features gave
22.1% R@10 there); name features (time split 47.0% → 53.3% R@10 before the prior fix); random and
same-module negatives rather than IDF-mined ones on both splits (mean validation MRR over the
grid 0.264/0.275 module and 0.439/0.439 time, against 0.236 and 0.379 with 8 IDF negatives). What did not: the frozen-IDF residual and the
learned IDF weight are within 0.005 validation MRR of each other (the time split picks residual
by a hair); initialising the `nameScore` weight at 1; bigram and reverse-coverage name features;
removing the name tower from `φ`/`ψ` (mean validation MRR −0.011 module, +0.004 time; the name
pair features carry the signal). Softmax at lr 16384 leaves its bounds
(score above 2^27), so softmax uses lr 1024/4096. Training is not monotone in epochs on the
module split: 8 epochs is worse than 4 and 12 for nearly every config (mean validation MRR 0.15
against 0.28 and 0.30), so validation choices there are noisy. The 192-config selection takes
16 minutes for both splits (was 12 configs); the pinned run is unchanged in cost.

Time split: last fifth of every module's theorems by declaration order; 576 training theorems,
118 dropped for using a test theorem as a premise; disjointness checked (`splitBy_disjoint`).
The model beats both baselines on the time split; on the module split it beats frequency but not
IDF. Starting the IDF pair weight at 1 and validating the negative mix mattered most: with 8
IDF-mined negatives per theorem, training drives the IDF weight towards 0 and ends below the IDF
baseline (time split MRR 0.248); the time split chose random and same-module negatives instead.
Longer training (12–24 epochs) overfits; 2–4 epochs win on validation.

Numeric formats (`ixai formats`, 8 seeds, `.truthmines/formats-seeds.log`); held-out accuracy,
majority baseline 68%:

| Format | lr 1/256 mean (range) | lr 2/256 mean | Native time per 600-step run |
|---|---|---|---|
| fx8 | 86.6% (72–92) | 85.8% | 0.21 s |
| fx12 | 89.6% (73–94) | 73.0% | 0.22 s |
| fx16 | 91.2% (88–94) | 74.9% | 0.28 s |
| fx24 | 90.2% (74–94) | 72.4% | 0.64 s |
| bfp8 | 76.0% (68–83) | 72.4% | 0.63 s |
| bfp12 | 87.2% (73–94) | 71.2% | 0.70 s |
| bfp16 | 86.1% (74–94) | 71.4% | 0.75 s |
| bf16 (FloatLib) | 88.5% (77–94) | 73.0% | 2.1 s |
| f32 (FloatLib) | 87.9% (77–94) | 75.0% | 2.1 s |

Above 12 bits the formats are within seed noise; 8-bit formats are worse; learning rate matters
more than format. FloatLib timings measure software emulation, not hardware floats. Proving cost
per format is not measured yet.

RL (`ixai rl small`, 200 held-out formulas, oracle reward 14848): always attempt −12416, always
defer −3712, RL on the specified reward −2752, RL on the gamed reward −12416; false publications
under the gamed policy: 0.

### IxBench v0

`ixai bench [tiny|small|full]` (`IxAIBench/`): one report per model size, Markdown tables on stdout
and a TSV results file under `.truthmines/bench/` whose BLAKE3 is printed. Everything except the
wall-clock block is integer arithmetic over fixed seeds and is bit-identical across runs (two `small`
runs gave the same file). Digests: `small` `63810c70eedd…`, `full` `f192ffb48100…`. Run time 13 s
(`small`), 58 s (`full`, which also re-runs the premise scorer's validation selection). Triage is
scored on 1,000 held-out formulas whose first `testSize` are the certified card's test set (checked
against `card`); ECE uses 10 bins over the predicted answer's probability; bootstrap intervals are
percentile, 1,000 resamples, seed 20261118.

Triage, `small` (64 formulas, 2 epochs, hidden 8) and `full` (400 formulas, 30 epochs, hidden 16):

| size | question | accuracy [95% CI] | macro-F1 | balanced acc. | majority | ECE |
|---|---|---|---|---|---|---|
| small | valid | 69.5% [66.6, 72.3] | 41.0% | 50.0% | 69.5% | 0.201 |
| | head | 47.4% [44.3, 50.3] | 12.8% | 20.0% | 47.4% | 0.222 |
| | coverage | 54.8% [51.6, 57.8] | 23.6% | 33.3% | 54.8% | 0.025 |
| full | valid | 75.1% [72.1, 77.7] | 57.9% | 59.1% | 69.5% | 0.047 |
| | head | 57.9% [54.8, 60.8] | 42.5% | 41.6% | 47.4% | 0.116 |
| | coverage | 62.8% [59.6, 65.6] | 50.7% | 50.3% | 54.8% | 0.071 |

The `small` model is a majority-class predictor on every question. Risk-coverage for `full`
(accuracy on the most confident 100/90/80/50%): valid 75.1/79.1/82.3/88.4%, head
57.9/62.2/68.2/81.4%, coverage 62.8/64.0/64.5/63.2%.

Policy / RL (200 held-out formulas; reward in 1/256 under `Triage.reward`; regret = oracle − policy):

| policy | small reward | small regret | full reward | full regret | false published |
|---|---|---|---|---|---|
| oracle | 14848 | 0 | 14848 | 0 | 0 |
| RL, specified reward | −2752 | 17600 | 7360 | 7488 | 0 |
| RL, gamed reward (`hackedReward`) | −12416 | 27264 | −12416 | 27264 | 0 |
| always attempt | −12416 | 27264 | −12416 | 27264 | 0 |
| always defer | −3712 | 18560 | −3712 | 18560 | 0 |
| supervised triage model, attempt if P(valid) > 3/8 | −3712 | 18560 | 3776 | 11072 | 0 |

The gamed policy attempts all 200 formulas (142 refuted) and scores 51,200 under its own reward;
`Triage.outcome` publishes 0 false formulas for it (`outcome_publish_sound`).

Premise selection (same at every size; pinned scorer configs, which `full` confirms validation
still selects):

| split | ranker | R@1 [95% CI] | R@5 [95% CI] | R@10 [95% CI] | MRR [95% CI] |
|---|---|---|---|---|---|
| module (208) | bilinear model v2 | 6.9% [4.3, 9.8] | 27.1% [22.5, 32.1] | 38.1% [32.7, 43.7] | 0.260 [0.219, 0.303] |
| | IDF | 6.9% [4.3, 10.0] | 25.0% [20.2, 30.0] | 38.1% [33.1, 43.7] | 0.254 [0.212, 0.297] |
| | frequency | 0.0% [0.0, 0.0] | 2.3% [0.8, 3.9] | 3.2% [1.4, 4.9] | 0.029 [0.017, 0.043] |
| | model − IDF (paired) | +0.0 [−3.3, +3.4] | +2.0 [−2.6, +7.2] | +0.0 [−4.4, +4.9] | +0.005 [−0.043, +0.054] |
| | v1 model − IDF (paired) | −3.5 [−6.9, −0.2] | −5.8 [−10.6, −0.5] | −7.8 [−13.1, −2.9] | −0.070 [−0.119, −0.019] |
| module, v3 | bilinear model v3 | 8.7% [6.0, 11.9] | 28.8% [24.4, 34.3] | 36.7% [31.7, 42.2] | 0.276 [0.235, 0.324] |
| | v3 − IDF (paired) | +1.7 [−2.1, +5.7] | +3.7 [−1.7, +9.7] | −1.4 [−6.3, +3.5] | +0.022 [−0.032, +0.078] |
| | v3 − v2 (paired) | +1.7 [−0.5, +4.0] | +1.7 [−1.7, +5.5] | −1.4 [−5.0, +1.9] | +0.016 [−0.011, +0.043] |
| time (157) | bilinear model v2 | 16.0% [12.0, 20.3] | 41.5% [36.1, 46.7] | 58.4% [51.8, 64.7] | 0.407 [0.348, 0.466] |
| | IDF | 9.4% [5.9, 13.1] | 30.1% [24.8, 35.0] | 46.6% [40.2, 52.8] | 0.291 [0.241, 0.338] |
| | frequency | 4.3% [2.0, 6.9] | 11.7% [8.0, 16.3] | 17.6% [13.0, 22.9] | 0.126 [0.087, 0.171] |
| | model − IDF (paired) | +6.6 [+1.7, +11.3] | +11.3 [+5.3, +17.4] | +11.7 [+4.9, +18.5] | +0.115 [+0.051, +0.180] |
| | v1 model − IDF (paired) | +1.9 [−2.9, +6.2] | +4.7 [−1.5, +11.5] | +0.3 [−7.1, +8.3] | +0.035 [−0.023, +0.097] |
| time, v3 | bilinear model v3 | 16.0% [11.8, 20.4] | 42.3% [37.0, 47.8] | 60.3% [54.0, 66.5] | 0.420 [0.362, 0.479] |
| | v3 − IDF (paired) | +6.6 [+2.0, +11.2] | +12.1 [+6.0, +17.7] | +13.7 [+6.6, +21.1] | +0.128 [+0.071, +0.190] |
| | v3 − v2 (paired) | +0.0 [−3.2, +3.1] | +0.7 [−3.8, +4.9] | +1.9 [−1.7, +5.4] | +0.012 [−0.020, +0.045] |

v3 rows (2026-11-19, `small` digest `dea987012024…`; the pinned configs are those `ixai premises
run` selected; the report now carries v2 beside v3 with the paired gap): v3 scorer 38,595
parameters, training 4.0 s (module) and 4.2 s (time), 12.3 s per 1,000 full-candidate queries;
`full`'s re-selection is 48 configs per split (about 7 minutes, was 16).

v2 (2026-11-19, `small` digest `cfcc4718e3a1…`, which also covers sections added since): the
time-split lead over IDF is outside the bootstrap interval at every cutoff; the module split is
level with IDF. v1's time-split lead was within the interval and its module-split deficit was not.
v2 premise scorer: 38,585 parameters; training 1.4 s (module) and 2.3 s (time); 11.5 s per 1,000
queries over all ~719 candidates. `full`'s re-selection now trains 192 configs (about 16 minutes);
`ixai premises run` with the same grid picked exactly the pinned configs (same model digests
`bdc057fc4c09…`, `aa72e9d41e0b…`).

Distribution shift (`full`; trained on depth-3 formulas; 1,000 formulas each; majority in
parentheses):

| test distribution | valid acc. | head acc. | coverage acc. | ECE (valid) |
|---|---|---|---|---|
| depth 3, card seed | 75.1% (69.5) | 57.9% (47.4) | 62.8% (54.8) | 0.047 |
| depth 3, fresh seed | 75.9% (71.7) | 61.2% (51.4) | 63.3% (55.3) | 0.044 |
| depth 4 | 67.1% (65.6) | 49.5% (57.6) | 54.5% (49.3) | 0.035 |
| depth 5 | 70.6% (68.9) | 39.7% (65.3) | 53.2% (49.8) | 0.046 |

Deeper formulas erase most of the lead over majority, and `head` falls below it.

Integrity, all pass: card counts reproduced; module and time splits train/test and fit/validation
disjoint; premise rule agrees with the host filter; the three forged claims of `writeForged`
(inflated card, relabeled model, overtrained model) differ from the specification, so their Eval
claims cannot hold (refusal by Ix itself is on record for `tiny`: 3 forged Eval claims FAILED in
`.truthmines/index.tsv`; other sizes require a certificate run); a training trajectory tampered at
step 300 of 600 is refused by `verifyRun`; recorded reward harness refuses 9 of 9 shortcut proofs.
Information: 221 of the 1,000 `full` test formulas also occur in its training set (small formula
space).

Cost (`full`): triage model 331 parameters (662 bytes int16, 432 bytes canonical encoding);
routing policy 178; premise scorer 30,385 (int32). Single thread: 3.1 ms per 1,000 gated triage
decisions, 1.9 ms per 1,000 routing decisions, 8.4 s per 1,000 premise queries over all ~719
candidates; training 0.16 s (triage `full`), 0.22 s (RL `full`), 0.75 s per premise split.

LLM baseline: `ixai bench export .truthmines/bench/baseline-v0` writes 19 batches of at most 25
items (12 triage: 100 formulas × the three questions; 7 premise reranking: the 157 time-split test
theorems × the IDF top 30, 166 of 255 gold premises among them), answer keys apart, and a
manifest; `ixai bench score DIR` scores `DIR/answers/*.txt` against our model and IDF on the same
items. Statements are given as names plus extracted shape and constants, since no pretty-printed
statements are extracted. Opus 5.5 run pending.

### Claude Opus 5.5 baseline (IxBench v0 export, 2026-11-18)

Ten Opus 5.5 sub-agents, zero-shot, reasoning only (no code), on `.truthmines/bench/baseline-v0`;
scored by `ixai bench score`. 0 invalid lines; 1 premise name not among the candidates.

| task | Opus 5.5 | ours | IDF | Opus tokens / item | Opus wall / batch of 25 | ours per item |
|---|---|---|---|---|---|---|
| triage valid (100) | 100% (ECE 0.013) | 76.0% (0.068) | | ~410 | 6–8 s | ~3 µs |
| triage head (100) | 100% (0.013) | 54.0% (0.099) | | ~410 | 6–8 s | ~3 µs |
| triage coverage (100) | 100% (0.021) | 66.0% (0.083) | | ~420 | 6–8 s | ~3 µs |
| premise rerank R@10 (157, ceiling 65%) | 61.1% [54.7, 67.8] | v2 54.5% [48.6, 60.7] (v1 44.7%) | 45.4% | ~5,400 | 42–81 s | ~ms |
| premise rerank MRR@10 | 0.627 [0.553, 0.692] | v2 0.368 [0.312, 0.427] (v1 0.315) | 0.283 | | | |
| premise rerank R@5 | 58.4% | v2 38.4% (v1 35.2%) | 29.8% | | | |
| premise rerank R@1 | 33.7% | v2 14.1% (v1 11.3%) | 9.4% | | | |

Premise reranking, paired gaps (`ixai bench score`, v2 model; same 157 items and Opus answers):

| gap | R@1 | R@5 | R@10 | MRR@10 |
|---|---|---|---|---|
| Opus − v3 model | +18.8 [+13.4, +24.3] | +20.7 [+14.0, +27.2] | +7.4 [+2.3, +12.7] | +0.241 [+0.175, +0.304] |
| v3 − v2 model | +0.7 [−1.8, +3.3] | −0.7 [−4.8, +2.5] | −0.7 [−3.8, +2.2] | +0.017 [−0.011, +0.045] |
| Opus − v2 model | +19.6 [+13.8, +25.4] | +20.0 [+14.0, +26.2] | +6.6 [+1.8, +12.1] | +0.259 [+0.193, +0.321] |
| Opus − v1 model | +22.3 [+16.1, +28.9] | +23.1 [+16.0, +29.5] | +16.4 [+9.9, +23.1] | +0.311 [+0.235, +0.379] |
| Opus − IDF | +24.3 [+18.6, +29.9] | +28.6 [+22.5, +35.0] | +15.6 [+10.2, +21.2] | +0.344 [+0.273, +0.413] |

v3 on these items: R@1 14.9%, R@5 37.6%, R@10 53.7%, MRR@10 0.385 [0.327, 0.444]. v2 v. IDF on these items: +4.7 R@1, +8.6 R@5, +9.1 R@10, +0.085 MRR@10 (point estimates). Name
features closed 60% of the R@10 gap to Opus, but little of the top-of-list gap: Opus puts a gold
premise first a third of the time, the model a seventh.

Readings:
- Triage is saturated for a frontier model: 3-atom, depth-3 formulas are decidable by enumerating
  8 assignments in context. It cannot show a Jev-style trade-off; M2b needs questions with
  headroom (more atoms, depth, first-order or type-checking questions decided by the kernel).
- Premise reranking has headroom on both sides: Opus was 16 points above our v1 model at R@10
  (6.6 for v2) and is near the 65% candidate ceiling. Opus sees declaration names, which carry much of the signal and
  which it has likely seen with their proofs during pretraining (Mathlib is public), so this is an
  upper-bound-ish baseline. Our model sees only addresses and shapes.
- Cost: Opus used ~844k tokens for 157 premise queries and ~124k for 300 triage items.

### Premise selection on all of Mathlib (2026-11-19)

`ixai bench mathlib-full module|time` (`IxAIBench/Large.lean`): train on the `mathlib-full` split,
rank test theorems over every accessible library theorem (47,819 on average). The model scores a
prefilter pool, the union of the IDF and name-IDF top 500 (~840 candidates; 54% of module-split
and 61% of time-split gold premises), the rest follow in IDF order; IDF and name-IDF rank
everything. Time split: 3,604 of the 36,033 test theorems (every 10th). Statistics ignore postings
over 256. Bootstrap as in IxBench (1,000 resamples, paired).

| split | ranker | R@1 | R@5 | R@10 | MRR [95% CI] |
|---|---|---|---|---|---|
| module (184,881 train, 3,445 test) | model (pinned, 2 epochs, nearest) | 5.5% | 15.4% | 21.2% | 0.382 [0.370, 0.396] |
| | IDF | 3.1% | 6.7% | 9.3% | 0.235 [0.223, 0.247] |
| | name-IDF | 3.7% | 10.0% | 14.2% | 0.275 [0.262, 0.288] |
| | model − IDF (paired) | +2.3 [+2.0, +2.7] | +8.7 [+8.0, +9.4] | +11.8 [+10.9, +12.7] | +0.147 [+0.133, +0.163] |
| time (95,627 train, 3,604 test) | model (pinned, 2 epochs, lr 1024, nearest) | 6.6% | 19.0% | 25.9% | 0.466 [0.453, 0.480] |
| | pinned v3 (12 epochs) | 5.5% | 16.8% | 23.1% | 0.430 [0.418, 0.442] |
| | IDF | 3.5% | 9.0% | 12.2% | 0.290 [0.278, 0.303] |
| | name-IDF | 3.5% | 10.1% | 14.2% | 0.279 [0.267, 0.292] |
| | model − IDF (paired) | +3.1 [+2.7, +3.5] | +9.9 [+9.2, +10.6] | +13.7 [+12.8, +14.5] | +0.176 [+0.161, +0.191] |
| | model − name-IDF (paired) | +3.1 [+2.7, +3.5] | +8.8 [+8.2, +9.5] | +11.6 [+10.9, +12.3] | +0.186 [+0.173, +0.199] |

IDF top 30 reranked (MRR over the top 10): module model 0.259 v. IDF 0.222 (+0.037 [+0.025,
+0.049]); time 0.342 v. 0.276 (+0.065 [+0.052, +0.078]). Digests: `mathlib-full-module.tsv`
`2f12a6bb…`, `mathlib-full-time.tsv` `811efe04…`. Cost: load and curate 28 s, prepared library
27 s, statistics 19 s, negatives 6–11 s, training 176–199 s per epoch (module, 184,881 theorems) and 65–75 s (time, 95,627),
ranking 7 min (24 threads); 6.5 GB peak RSS; runs 17 min (module) and 34 min (time, with the pinned 12-epoch model).

`order-basic` rerank items on a full-Mathlib model (`ixai bench mathlib-full rerank theorem`,
`mathlib-full-rerank-theorem.tsv` `2141455e…`): trained on the 88,822 Mathlib items that are not
one of the 157 rerank theorems and whose proofs use none of them, directly or through other
items' proofs (106,837 excluded; dependencies through definitions are not followed). The module
rule, no module that is or imports a rerank theorem's module, leaves 5 of 195,659 items. Same 30
candidates and keys as `baseline-v0` (unchanged):

| ranker | R@1 | R@5 | R@10 | MRR@10 [95% CI] |
|---|---|---|---|---|
| Opus 5.5 | 33.7% | 58.4% | 61.1% | 0.627 [0.553, 0.692] |
| full-Mathlib model | 17.2% | 35.6% | 50.5% | 0.381 [0.319, 0.445] |
| v3 (`order-basic`) | 14.9% | 37.6% | 53.7% | 0.385 [0.327, 0.444] |
| IDF | 9.4% | 29.8% | 45.4% | 0.283 [0.230, 0.332] |
| Opus − full model (paired) | +16.4 [+11.2, +21.8] | +22.7 [+16.2, +28.6] | +10.5 [+5.8, +15.5] | +0.245 [+0.178, +0.306] |
| full model − v3 (paired) | +2.3 [−1.5, +6.4] | −1.9 [−6.8, +2.9] | −3.1 [−7.7, +1.4] | −0.003 [−0.049, +0.042] |

190× more training theorems moved nothing outside the interval: the gap to Opus is unchanged. On
full Mathlib the model leads both baselines by wide, tight margins (its full-ranking lead comes
mostly from candidates outside the IDF top 30), but the reranking task stays where it was.

### M2b typed questions

`ixai bench typed` (`IxAICore/Typed.lean`, `IxAIBench/Typed.lean`): two families of questions whose
labels are computed by pure, total Lean procedures, so every label is a closed `decide`/Eval fact.

- STLC typing: context of 5 variables over `N`, `B` and arrows; a type-directed random de Bruijn term
  (generation depth 7, size 80–160 on most draws; evaluation set 1–161, mean 101, depth mean 10),
  then with probability 1/2 up to 6 local mutations until it has no type (variable re-pointed, λ
  annotation changed, subterm replaced by a term of another type). Questions: `typechecks` (Bool)
  and `type` (A–D among the true type and three nearby types, or `none`). Proved: `infer_iff`
  (`infer Γ t = some T ↔ HasType Γ t T`), `HasType.unique`, `TypeItem.wellTyped_iff`,
  `TypeItem.pick_sound`, `TypeItem.pick_none_iff`.
- Propositional status: a random 3-CNF over 12 atoms with 52 clauses, kept when unsatisfiable
  (contradiction) or satisfiable (contingent), and its De Morgan dual for tautologies and half the
  contingent items, so the outer form does not decide the label. Proved: `mem_assignments`,
  `valid_iff`, `sat_iff`, `status_tautology_iff`, `status_contradiction_iff`,
  `status_contingent_iff`, `PForm.eval_dual`.
- Fresh instances: evaluation sets are drawn from seed 20261119, not derived from any training seed,
  and filtered by `fresh` (`fresh_disjoint`); 0 exact duplicates were drawn in either family.
- Models: the existing `train` and MLP; features are bag-of-node-kinds, depth, size, context and
  candidate shapes, one-level checks with context types (`shallowErrors`, `quickType`) for STLC;
  connective counts, per-atom polarity summaries and 8 fixed probe assignments for prop. All
  features lie in 0…3: `Fx` inputs are unnormalized and larger inputs switched every hidden unit off.
  Config by validation accuracy on seed 31337 (`ixai bench typed-sweep`): batch 50, lr 1/256,
  10 epochs, hidden 16, 2,000 training instances. More steps make it worse: updates round toward
  −∞, so long runs drift weights down until the ReLUs die.

1,000 fresh instances each (digest `f305d4595805…`):

| question | accuracy [95% CI] | macro-F1 (majority) | balanced acc. | majority | ECE |
|---|---|---|---|---|---|
| stlc typechecks | 59.6% [56.5, 62.5] | 57.6% (31.7%) | 58.4% | 46.6% | 0.071 |
| stlc type (5-way) | 53.4% [50.3, 56.4] | 13.9% (13.9%) | 20.0% | 53.4% | 0.083 |
| prop status (3-way) | 65.7% [62.9, 68.6] | 53.0% (17.0%) | 66.7% | 34.4% | 0.137 |

Readings: `type` is a majority-class predictor (`none`). `status` at balanced accuracy 66.7% is the
form-only rule (CNF → contradiction, DNF → tautology, never contingent): the features do not
capture satisfiability near the threshold. `typechecks` is 13 points over majority on the
one-level checks. Cost: 711 / 403 parameters; 37 µs (STLC) and 1.4 ms (prop, eight probe
evaluations of a ~390-node formula) per decision, single thread.

Headroom check (one reader, by reasoning only, before the Opus run): 10 items at each of three
difficulty levels, all answered correctly: STLC sizes 25–60, 45–100 and 80–160; prop random
formulas (8 atoms, depth 6), nontrivial random formulas (9 atoms, depth 7), and threshold 3-CNF
(9 then 12 atoms). The final items took full derivations (STLC) or unit propagation with up to
three levels of case splits (prop), several thousand reasoning tokens each. So a frontier model
that reasons per item is not shown to be below 85% at this difficulty; the batch protocol (25 items
per answer) may still leave headroom, and the Opus run measures it. Harder prop instances need a
labeller faster than full enumeration (2^12 assignments × 52 clauses already dominates training
time at 45 s).

LLM batches: `ixai bench export .truthmines/bench/baseline-v1` writes the 19 v0 batches and 12 new
ones (`stlc-typechecks-01..04`, `stlc-type-01..04`, `prop-status-01..04`, 25 items each, the first
100 fresh instances per question), keys in `keys/typed.tsv`; `ixai bench score DIR` scores both,
each part reading only its own answer files.

Claude Opus 5.5 on the 300 typed items (one sub-agent per batch, reasoning only, no tools beyond
reading the batch; `ixai bench score .truthmines/bench/baseline-v1`, 2026-11-19):

| question | LLM accuracy [95% CI] | our model | gap [95% CI] | macro-F1 LLM / ours | ECE LLM / ours |
|---|---|---|---|---|---|
| stlc typechecks | 98.0% [95.0, 100.0] | 54.0% | +44.0 [+33.0, +54.0] | 97.9% / 53.3% | 0.175 / 0.116 |
| stlc type | 99.0% [96.0, 100.0] | 47.0% | +52.0 [+42.0, +61.0] | 97.9% / 12.7% | 0.194 / 0.136 |
| prop status | 100.0% [100.0, 100.0] | 73.0% | +27.0 [+19.0, +36.0] | 100.0% / 55.9% | 0.080 / 0.202 |

About 1.0M tokens in all (~70–77k per STLC batch, ~100–112k per prop batch; ~3.4k per item),
3–6 minutes per batch. Readings: the families are saturated for a frontier model even 25 items
per answer, as the headroom check suggested; Opus's ECE is underconfidence (confidence ~80% at
98–100% accuracy). A Jev-style trade-off needs instances past what a careful reader resolves:
threshold 3-CNF with 30+ atoms (a certified DPLL labeller), or STLC with System F or
dependent types where inference is not local.

Hard propositional family `prop-hard` (2026-11-19): threshold 3-CNF over 40 atoms with 170
clauses, or its De Morgan dual, drawn and balanced as before; evaluation from seed 20261119 through
`fresh`. Labels by `fastStatus` (`IxAICore/Dpll.lean`): DPLL with unit propagation and splitting on
a shortest clause, fuel = total clause length + 1, so it is structurally recursive and each label
remains a closed term the kernel evaluates. Proved, with only `propext` and `Quot.sound`:
`Dpll.dpll_iff` (enough fuel → result ↔ satisfiable), `Dpll.solve_iff`, `Dpll.satN_iff` (over
length-`n` assignments), `fastSat_eq : fastSat n f = sat n f`, `valid_eq_not_sat_dual`,
`fastStatus_eq : fastStatus n f = status n f`, so `status_*_iff` describe it. It also labels the
12-atom family: the old rows of `bench-typed.tsv` are unchanged and `prop` training fell from 45 s
to 2.7 s. Cost at 40 atoms: 2.1 ms per label; the typed bench runs in 3 minutes, 30 s of it
training `prop-hard`. Refuting an unsatisfiable draw takes DPLL 340–1,350 nodes (median 680).

Features: the 21 of `prop-status` plus five on the formula's CNF core (`coreFeatures`): failed
literals under unit propagation, an atom failing both ways, total propagation, how early DPLL capped
at `4n` nodes finds a model, and polarity imbalance. Validation (seed 31337, 600 items, the
`prop-status` config): 76.1% with all, 64.0% without the capped search, 63.6% with the 21 only, so
the capped search, a one-sided certificate found for about half the satisfiable cores, carries all
of the gain. 1,000 fresh instances (digest `15c0935f06ab…`):

| question | accuracy [95% CI] | macro-F1 (majority) | balanced acc. | majority | ECE |
|---|---|---|---|---|---|
| prop-hard status (3-way) | 79.0% [76.6, 81.6] | 76.3% (17.1%) | 79.8% | 34.7% | 0.096 |

Batches: `ixai bench export .truthmines/bench/baseline-v2` writes every v0 and v1 batch (byte-identical
to `baseline-v1`) plus `prop-hard-01..04` (ids `PH001`–`PH100`; atoms `x1`…`x40`; ~120 KB per
batch), keys appended to `keys/typed.tsv`; on these 100 items our model scores 79.0% [71, 86]
(majority 40%). `answers/` holds the `baseline-v1` answers, so `ixai bench score` reproduces the
earlier rows.

Claude Opus 5.5 on `prop-hard-01..04` (four sub-agents, reasoning only, 2026-11-19):

| question | Opus 5.5 [95% CI] | our model | gap Opus − ours [95% CI] | macro-F1 Opus / ours | ECE Opus / ours | majority |
|---|---|---|---|---|---|---|
| prop-hard | 40.0% [30, 50] | 79.0% [71, 86] | −39.0 [−54, −23] | 19.0% / 77.7% | 0.123 / 0.104 | 40.0% |

Every sub-agent judged the items undecidable by hand and answered `contingent` for all 25 at
confidence 50–55 (~150k tokens and 30–40 s per batch, almost all of it reading the batch), so Opus
scores exactly the majority rate and is calibrated only in the trivial sense. Each did note the
form-only exclusion (a CNF is never a tautology, a DNF never a contradiction) but did not use it to
split labels. Our small model, whose one informative feature is a capped search
(≤ `4n` DPLL nodes) producing a one-sided certificate of satisfiability, is 39 points ahead. This is the first M2b family where the small decision model beats the frontier
baseline; a tool-using baseline (a SAT solver call) would score 100%, so the comparison measures
the decision under a fixed compute budget, as in Jev.

Certificates for `prop-hard` (2026-11-19). Two cheap one-sided procedures on the CNF core (the
formula, or the dual of a DNF): the capped DPLL already in the features (≤ `4n` = 160 nodes) can
only find a model, and `Dpll.lookahead` can only refute: at each node unit propagation and
failed-literal probing to a fixpoint (a literal whose propagation reaches an empty clause is false
in every model, so its complement is asserted), then a split on the literal of greatest weight
product, every leaf refuted within depth 6 and 16 nodes. Proved with `propext`, `Quot.sound` and
(through `status_contingent_iff`) `Classical.choice`, no `sorry` or `native_decide`:
`Dpll.propagate_sat`, `probe_sat`, `closure_sat`, `lookahead_sound` (`refuted → ¬ Sat F`, for any
probe order and branching rule), `boundedDpll_sat` (model found → `Sat F`), `sat_restrict_iff`,
`falsifiable_sound`, `modelFound_sound`, and `certify_sound : certify n c f = some s → status n f = s`
(refuted CNF → contradiction, refuted DNF dual → tautology, model and falsifiable clause →
contingent). `ixai bench typed-refute` measures the refuter on the 600 validation draws: 382 of 382
unsatisfiable cores refuted within 16 nodes (mean 5 nodes, 4.9 ms per core with one closure pass;
with three passes, by budget: 1 node 15, 3 nodes 182, 6 nodes 314, 8 nodes 367, 12 nodes 381); no
satisfiable core is refuted (as the theorem requires); the capped DPLL finds a model for 81 of 218
satisfiable cores.

The `prop-hard-cert` section answers by certificate where one fires and by a model with the
refutation result as feature 27 (0 not refuted, 1 within the budget, 2 within a quarter, 3 at the
root) elsewhere; same 1,000 fresh instances (digest `dd799cf8f3fb…`; the earlier rows are unchanged):

| question | accuracy [95% CI] | macro-F1 (majority) | balanced acc. | majority | ECE |
|---|---|---|---|---|---|
| prop-hard status, certified + model | 100.0% [100.0, 100.0] | 100.0% (17.1%) | 100.0% | 34.7% | 0.056 |

| part | items | accuracy | labels |
|---|---|---|---|
| certified (by theorem) | 802 (80.2%) | 100% | contradiction 331/331 refuted, tautology 322/322 dual refuted, contingent 149/347 model found |
| model-decided | 198 (19.8%) | 100.0% [100.0, 100.0] | contingent 198 |

At this budget every unsatisfiable draw is refuted, so an uncertified item is contingent and the
model only has to learn "not refuted → contingent"; the defer threshold chosen on validation is 0
(nothing deferred) and accuracy is 100% at every coverage. Smaller budgets show the defer option at
work (`ixai bench typed-cert`, not in the digest; τ chosen on validation for 95% on answered items):

| refutation budget | certified | accuracy (all) [95% CI] | model-decided accuracy | defer τ | answered [95% CI] | accuracy answered [95% CI] | accuracy at 90% / 70% / 50% coverage |
|---|---|---|---|---|---|---|---|
| 3 nodes (= 4) | 34.3% | 80.5% [78.0, 82.9] | 70.3% | 161/256 | 39.1% [35.9, 42.2] | 97.4% [95.6, 98.9] | 82.6% / 86.5% / 94.0% |
| 6 nodes | 59.4% | 81.5% [79.2, 83.9] | 54.4% | 168/256 | 64.7% [61.7, 67.8] | 95.8% [94.1, 97.3] | 84.7% / 92.5% / 100% |
| 16 nodes (used) | 80.2% | 100.0% | 100.0% | 0 | 100% | 100% | 100% / 100% / 100% |

On the 100 exported `PH` items (`ixai bench score .truthmines/bench/baseline-v2`, batches and keys
unchanged): Opus 5.5 40.0% [30, 50] against 100.0% [100, 100] for certificate + model, gap −60.0
[−70, −50], macro-F1 19.0% / 100.0%, ECE 0.123 / 0.046 (the `prop-hard` row, 79.0%, is unchanged).
Cost: 8.7 ms per decision (refutation alone 4.9 ms; the plain `prop-hard` decision 4.7 ms, the DPLL
label 2.2 ms); training 40 s. The typed section now takes 210 s (114 s before), 313 s for the
process. The refuter makes `prop-hard` easy for a 16-node search, so it no longer measures a
decision under a tight budget; a harder family (more atoms, or instances built to defeat
failed-literal reasoning) is needed for that.

Tseitin parity family `prop-xhard` (2026-11-19; `ixai bench typed-xhard`, `IxAICore/Xhard.lean`,
`IxAIBench/TypedXhard.lean`). A uniform simple connected 3-regular graph on 16 vertices (a random
pairing redrawn until simple and connected), edge i = atom x(i+1) (24 atoms), and per vertex the
constraint "the parity of its three edges is its charge" as the four 3-clauses of the wrong parity.
From a drawn assignment σ* with charges equal to σ*'s parities: unsatisfiable = one charge flipped
(odd total); satisfiable trap = the same flip with the one clause σ* falsifies removed (every model
agrees with σ* at that vertex); satisfiable even = no flip. Plus 0–3 random 3-clauses true under σ*
(one more for traps, so the clause count does not give the class), clauses and literals shuffled,
CNF or De Morgan dual as before; 64–67 clauses, formula size 477–506. Label guarantee: the sampler
records what it built (`XInst`), `XInst.check` verifies it by evaluation, and
`XInst.check_sound : x.check n = true → status n x.form = x.claim`, from `Tseitin.not_sat` (odd
total charge → no model of any CNF subsuming the Tseitin clauses; `Tseitin.vertex_parity`,
`parity_incFrom`: summing vertex parities counts each edge twice) and `subsumes_eval`; axioms
`propext`, `Classical.choice`, `Quot.sound` only. Training and scoring still label by `fastStatus`
(`fastStatus_eq`); on all 1,600 validation and evaluation draws `check` passes and the claim equals
`fastStatus` (a `#guard` in `Xhard.lean` checks 12 draws on 8 vertices at build time).

DPLL refutes an unsatisfiable core in 2,033–4,535 nodes (median 3,331; traps median 53, even 25).
The refutation search (`refuteCore`, one closure pass) on the 397 unsatisfiable validation cores:

| budget (nodes) | depth | refuted | satisfiable refuted | time per unsat core |
|---|---|---|---|---|
| 16 (as `prop-hard`) | 6 | 0/397 (0.0%) | 0 | 1.2 ms |
| 64 | 8 | 0/397 (0.0%) | 0 | 1.4 ms |
| 256 | 10 | 3/397 (0.7%) | 0 | 11.7 ms |

No vertex constraint becomes unit after one assignment, so failed-literal probing learns nothing;
the capped `4n`-node DPLL finds a model for 111/160 traps and 43/43 even cores. 1,000 fresh
instances (seed 20261119, 0 duplicates of training; `bench-typed-xhard.tsv` digest `481c29de17b5…`;
`bench-typed.tsv` byte-identical after the change):

| question | accuracy [95% CI] | macro-F1 (majority) | balanced acc. | majority | ECE |
|---|---|---|---|---|---|
| prop-xhard, model only (26 features) | 90.1% [88.3, 91.8] | 89.2% (17.1%) | 89.5% | 34.7% | 0.087 |
| prop-xhard, certified + model (16 nodes) | 91.7% [90.0, 93.3] | 91.1% (16.8%) | 91.2% | 33.8% | 0.154 |

| part | items | accuracy [95% CI] | labels |
|---|---|---|---|
| certified (by theorem) | 232 (23.2%) | 100% | contingent 232/315 by model found; 0/338 contradictions and 0/347 tautologies refuted |
| model-decided | 768 (76.8%) | 89.1% [86.8, 91.4] | contradiction 338, tautology 347, contingent 83 (traps) |

Defer (τ = 182/256, chosen on validation seed 31337 for 95% on answered items; validation 33.3%
answered at 100%): 32.7% [29.9, 35.5] answered at 100.0% [100, 100], 673 deferred. Accuracy at
coverage 100 / 95 / 90 / 80 / 70 / 50%: 91.7 / 91.6 [90.2, 93.4] / 91.8 [90.4, 93.7] / 93.0
[91.1, 94.6] / 93.8 [91.8, 95.4] / 94.2% [92.6, 96.6] (bootstrap 1,000, seed 20261118). Reading:
the refuter certifies nothing, so every contradiction and tautology is model-decided, and the model's
89.1% there is the rate of answering by the outer form alone (685 of 768 are unsatisfiable cores);
it does not separate the 83 uncertified traps from unsatisfiable cores, which is the decision left
open at this budget. Training is seed-fragile: of seeds 2614–2618 (`ixai bench typed-xhard-sweep`,
validation) two end near 33% for the plain model and two near 58% for the certified one, so each
model's seed is chosen on validation (plain 2614: 89.5%; certified 2615: 91.8%, tied with 2617 and
2618).

Batches for a later Opus run: `ixai bench export-xhard .truthmines/bench/baseline-v3` writes only
`prop-xhard-01..04` (ids `PX001`–`PX100`, the first 100 fresh instances; atoms `x1`…`x24`, ~47 KB
per batch; contradiction 30, contingent 39, tautology 31), key `keys/xhard.tsv` (BLAKE3
`bb234de39707…`), manifest `ce5330015379…` (batches `63cc8ea56222…`, `9374bb2d2589…`,
`2af6101b96ea…`, `b7fef1fb53cc…`); re-export is byte-identical; `ixai bench score-xhard DIR` scores
`answers/prop-xhard-*.txt`. baseline-v0/v1/v2 are untouched. Cost: label 1.2 ms, decision 1.7 ms,
certified decision 3.8 ms; training 13 s; `typed-xhard` 177 s (section 72 s), export 132 s, peak
RSS 286 MB. These timings were taken when every `ixai` start spent about 100 s initialising closed
constants of the typed bench (`TypedBench.items` and closed subterms of `run`); start-up is now
0.03 s (Verification boundary, in Status), so they overstate each command by that much.

## Next

0. The full-environment certificate (decision of 2026-11-20). In order:
   - IxVM accepts every constant of the environment: the nested inductive types
     (`Aiur.Represents` and the like), fixed in IxVM or by taking the kernel of ix PR 678 if it
     accepts them (a standalone build of PR 678 is in `~/repos/ix.ixai-pr678`, run through
     `ix/hints/ix678`; `ix/hints/test678.sh` runs it on the problem cases).
   - IxVM checks it within memory: the `eq_def` blow-up, and whatever the survey of the
     environment finds. Then restore the three `TrainSpec.lean` proofs that were changed to avoid
     generating those lemmas, so that the fix is exercised on the real case.
   - One ix build carrying those fixes and the Aiur-child aggregator (`ChildKind.aiur`, fork
     `ix-childkind-aiur`): leaf proofs, aggregation, the join with the 30-block training root,
     the independent check and compression (`ix/combined/certify.sh`). A build of ix
     regenerates its IxVM artifact and native executor from its own sources
     (`formal_generated` in ix's lakefile), so a fork with a changed kernel is a consistent
     toolchain by itself.
   - Then the trained model's card and decisions in the same environment
     (`ix/combined/gen_deployed.py`), so one claim ties the run, the card and the gate to one
     model constant.
   - Not IxVM but in the way of scaling: ix's certified compile does not finish on constants of
     1.5 million nodes or more (`Ix.Sharing.Family.greedyOrderAux`); the generated proofs are cut
     into smaller lemmas to avoid it (`obs_rewrite.py --chunk`).
1. M1: with sign-off, the `aiurExec` aggregation change over the 600 step proofs (chained IO as in
   `train_of_deployed_steps`; one `Fixed::train` proof exceeds the u16 key format), then one
   certificate for the full model. The prototype already certifies training alone (one PLONK
   certificate over the aiurExec root, above; 8.5 min end to end over 30 `train_block` proofs,
   4.2 min over one `FixedTree::train_tree` proof); what remains is the Ix claim and protocol
   change, `train_tree_sound` (or a deployed-`train_block` chain theorem for the block route), and
   joining that root with the environment's.
2. M2: top-of-list precision (rerank R@1 15% v. Opus 34%). v3 (decay, neighbour votes, co-usage,
   cross features, ensembles) closed none of it on this slice, and neither did data: trained on
   all of Mathlib without the rerank theorems' dependents, rerank MRR is 0.381 (v3 0.385, Opus
   0.627). The next lever is what the model sees: richer extracted statements (hypothesis heads,
   pretty-printed types; only hypothesis counts are extracted now) and a model that reads them;
   one certificate over data, training and evaluation.
3. M2b: `prop-xhard` (Tseitin parity, 24 atoms) defeats the failed-literal refuter (0/397 at 16
   and 64 nodes, 3/397 at 256); certified + model 91.7% [90.0, 93.3], defer answers 32.7% at 100%,
   but the model does not separate uncertified traps from contradictions (it answers by outer form).
   Next: the Opus 5.5 baseline on `baseline-v3` (`prop-xhard-01..04`, reasoning only; a reader who
   groups clauses by atom triple can find the parity structure, so this tests that, not search);
   features that see the structure (complete four-clause parity groups, a missing clause); typing
   families beyond one-level checks (System F); certify a `fastStatus` or `certify` label as an Ix
   Eval claim.
4. GPU: precise bound check, tensor cores; RL on fx16, then its target circuit (M3).
5. `ixvc` local mode (`ixvc.md` first steps).
