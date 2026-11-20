# ix-ai-pipeline

A Lean framework for **specified learning** with Ix: AI models whose training data, labels,
objective, training run, evaluation and deployment rules are all Lean definitions, certified by
Ix zero-knowledge proofs and recorded in a local Truth Mines store. It implements the pipeline
described in `~/repos/notes/ix-ai-strategy.md`.

## Overview

| Part | State | Details |
|---|---|---|
| **Certified, deterministic training** | The fixed-point decision model trains as a pure Lean function: BLAKE3 everywhere, bit-identical across compiled Lean, Python and IxVM. All 600 SGD steps are proven in Aiur and independently re-verified. A Lean refinement chain (`train_refines` → `train_sound_eq`, and `step_sound_deployed` for the per-step program) shows the proved program computes the Lean `train`, using only `propext`, `Classical.choice` and `Quot.sound`. Folding the 600 step proofs into one PLONK certificate goes through an `aiurExec` aggregator prototyped in a fork of Ix; adopting it is an Ix protocol decision. | below; `docs/plan.md` (Status); `docs/offload.md` |
| **Safety by construction** | The deployed system acts only through a gate, and its safety theorems hold for every weight setting, so training cannot change what the system may do, only how much work the model saves. | below |
| **Typed decision questions (M2b)** | STLC typing and propositional status families with labellers proved sound and complete. On 40-atom `prop-hard`, a sound capped refuter (`certify_sound`) certifies most answers and the model answers the rest: 100%, against Opus 5.5 at 40% without tools. A harder family, `prop-xhard`, aims beyond that refuter. | `docs/plan.md` (M2b results) |
| **Premise selection** | A bilinear Fx16 scorer over all of Mathlib (262k theorems; curation proved equal to its specification, splits proved disjoint) beats IDF baselines on full ranking, but stays well below Opus 5.5 on rerank-30. | `docs/data.md`; `docs/plan.md` |
| **Verifiable model package** | `ixai-verify` checks a commitment, a model and a receipt without prover logs or re-running SGD: the 600 step proofs and the one-proof `Fixed::train` route against claims built from the spec, the claims of card, decisions and safety theorems, and prints `PROVED`, `PREDICTED`, `INCOMPLETE` or `REJECTED` with every hypothesis it rests on. | `docs/verification.md` |
| **IxBench** | Deterministic benchmark with BLAKE3 digests, bootstrap CIs and calibration error; batches exported for Opus sub-agent baselines and scored with `ixai bench score`. | `docs/plan.md` |
| **Local Truth Mines store** | Ix stores, compiled and typechecked, for Lean core, Mathlib, FLT, cslib and PhysLean, with every certified claim indexed in `.truthmines/index.tsv`. | `.truthmines/` |
| **Agent workbench** | Lane, extended in a fork with BLAKE3-addressed lanes, change and verify records, main-agent re-checks at submit, deterministic fuel, merges per declaration, conflicts as data, and admission through Ixon/IxC. How it combines with Ixon-native version control and the IxAI models into one system. | `docs/lane.md`; `docs/integration.md` |
| **Provable decisions** | Strategy: a System One for Ix, typed decisions over Lean/Ix syntax only, each with a receipt binding the model, its certified training, a gate theorem and its calibration against kernel labels; first demo, definition equivalence. | `docs/provable-decisions.md` |
| **Learned kernel hints** | Measured on 80 Mathlib claims: IxVM's untrusted reducibility hints move the cost of a kernel check by about 1%, so they are not worth a model. Substitution (39%) and loading constants (26%) dominate; grouping claims so shared constants load once is worth up to about 20%. | `docs/kernel-hints.md` |
| **Next** | One PLONK certificate for the full training run; a reinforcement-learning loop on the fixed-point model (`docs/rl.md`); sandboxed proof agents; a premise model that reads statements; Ixon-native version control (`docs/ixvc.md`). | `docs/plan.md` (Next) |

## Specified learning, certified with Ix

`IxAICore` is a Lean library that imports only `Init` and is written so that a kernel can
evaluate it. Ix's IxVM evaluates it inside its proofs.

**The model** (`IxAICore/Decision.lean`) is a typed decision model in the style of Jev and the
Decisions APIs, but every answer has a Lean type:

| Question | Answer type | Decided by |
|---|---|---|
| `valid` | `Bool` | truth table |
| `head` | `Head` (inductive: `p0`, `p1`, `p2`, `top`, `none`) | the formula's implication spine |
| `coverage` | `Coverage` (inductive: `never`, `rarely`, `mostly`, `always`) | counting satisfying assignments |

Its other properties:
- **Labels are computed, not annotated.** The specification supplies a decision procedure for each question.
- **Squared error against one-hot targets.** This is the Brier score, a proper scoring rule, so outputs estimate probabilities.
- **Training is a pure function, `train spec config`.**
  - Data generation, labels, initialization, batch schedule and SGD are all specified.
  - Every gradient entry is an exact sum, rounded once, so no implementation or summation order can change a bit.

**The deployed system** (`IxAICore/Triage.lean`) acts only through a gate:
- the model routes a formula to the decision procedure when it is confident;
- the system publishes the formula only if the procedure confirms it.

`act_publish_sound`, `act_publish_confident` and `act_defer_iff` hold **for every possible
weight setting**. Training changes how much work the model saves, never what the system may do.

### What is certified on this machine

All claims below were proved with the real `ix` (from `~/repos/ix.ci-merge-tests`) on an RTX PRO
6000 GPU, verified with `ix verify`, and recorded in `.truthmines/index.tsv`. Seconds are prove
time, and every uncompressed STARK proof is 14–24 MB.

| Claim | Kind | Seconds |
|---|---|---|
| Tiny model: `train spec config` = the trained weights (91 parameters, 16 examples, 2 SGD steps) | Eval | 14.6 |
| Its evaluation card: accuracy, Brier score and calibration error per question | Eval | 11.7 |
| Four gate decisions of the deployed model (decision receipts) | Eval | 5.7–5.9 each |
| `deployedPublishSound`, `deployedPublishConfident`, `deployedDeferIff`, stated for the deployed weights | Check | 5.2–5.6 each |
| Small model, whole run (171 parameters, 64 examples, 8 steps) | Eval | 100.5 |
| Small model as a chain: examples, schedule and initial weights, then 8 per-step claims and the chain theorem | Eval ×12, Check ×1 | 4–15 each |
| The whole certified environment (training, card, decisions and safety theorems as `decide +kernel` theorems): one aggregate CheckEnv proof over 2,065 constants | Aggregate | about 30–70 |
| The same environment compressed to a 584-byte PLONK certificate (compression pipeline, Ignition SRS) | Compress | 157 |
| Full model training (600 SGD steps): one Aiur proof per step, chain-checked to `train spec config` | Aiur ×600 | 32 total |
| Full model card, four gate decisions and three deployed-model safety theorems | Check ×8 | 131, then about 6 each |
| Two agent proofs accepted by the reward harness | Check | 4.5 each |

**Determinism.** The same specification yields the same weights in compiled Lean, in an
independent Python implementation (`shell/triage.py`, also with every reduction reversed), and in
IxVM inside the proof, for every size including the full 600-step run in Python. The chain's
final weights and the one-claim run's weights have the same Ixon address (`27ddf0fc…`), so the
two certification routes agree on one content-addressed model.

**No reward hacking, no false reports.** `ixai forge` writes the claims a dishonest trainer might
make. IxVM refuses each one inside the prover (`Eval: result does not match output`):
- an evaluation card with accuracy raised by 5 points;
- a model trained on inverted labels, claimed as the specified training result;
- a model trained one epoch longer than its configuration says.

There is no learned reward to game: the objective is a fixed Lean function of decided labels, and
the certificate covers the data generation, the labels and every update.

**Truth Mines.** `ix/ixw` runs `ix` with `HOME=.truthmines`, so `.truthmines/.ix/store` is a local
content-addressed store of constants, claims and proofs, and `.truthmines/index.tsv` records every
certification. `ixai mines .truthmines/index.tsv` summarizes it. Content addressing makes reuse
automatic: re-certifying an identical definition under another name returned the existing proof.

**Succinct certificates.** The whole certified environment compresses to **one 584-byte PLONK
proof** (864 bytes as a Solidity payload), proved with the BN254 Ignition SRS. The environment
contains training, card, decisions and deployed-model safety theorems, all as `decide +kernel`
theorems (`Certified_tiny.lean`).

How it was produced:
- **Aggregate.** Its CheckEnv claim over 2,065 constants is aggregated into the root `193c85bd…`.
- **Export.** The root is exported with the pinned root key `55f0b8b0…`.
- **Compress.** The root goes through the compression pipeline of `~/repos/ix.aiur-compression-active` (wrap, GL chain, narrow stage, PLONK terminal over a 2^25 domain) via `ix/ladder.sh`, under that worktree's heavy-job lock.

The run took 2 min 37 s end to end, with a 136 GB peak; the PLONK stage proved in 23 s and verifies in about 4 ms. Every pipeline check passed, including that a wrong statement is refused by the prover and rejected by the verifier.

The certificate is at `.truthmines/compression/ladder_tiny_run1/plonk/proof.bin`. The
`ix.ci-merge-tests` binary cannot compress on its own, because its release keys (0.3) predate its
aggregation backend.

**Rewards an agent cannot game.** `ixai reward ix/bundle` checks agents' proofs with Ix's strict
checker:
- **The harness writes each theorem statement**, and an agent supplies only the proof text.
- **Each candidate is compiled with `ix compile`** and checked with `ix check-lean`, which declines any axiom other than `propext`, `Classical.choice` and `Quot.sound`.
- **Only honest proofs of true statements are accepted:**
  - `sorry` is declined (`sorryAx`);
  - `native_decide` is declined (`Lean.ofReduceBool`);
  - an axiom smuggled into the proof text does not elaborate;
  - an invalid statement admits no accepted proof at all.
- **Accepted proofs are promoted** to Check certificates in the store, about 4.5 s each.

Verdicts are written to `.truthmines/rewards.tsv`.

### Full-size run

The full model (16 hidden units, 331 parameters, 400 examples, 30 epochs: 600 SGD steps) is
certified the same way, in chunks (`ixai certified ix/bundle full 20` writes `Certified_full.lean`):

- **30 chunk theorems**, each saying that 20 steps from one checkpoint reach the next.
- **Data theorems** for the examples, the schedule and the initial weights.
- **`trainingCertified : train spec config = w30`**, proved by rewriting with the chunk theorems.
- **The card, the decisions and the deployed-model theorems.**

Costs measured so far:

| Step | Cost |
|---|---|
| Lean's kernel checking the whole file (inside `ix compile`) | 21.7 min, 73 GB peak |
| One chunk theorem as an Ix Check claim | 659 s, 50 MB proof |
| The whole environment | 36 shards |

`ix/certify-full.sh` proves the shards one at a time, aggregates them, exports the root and runs
the compression pipeline. Results are logged in `.truthmines/compression/full.log` and the index.

The step function computes each transpose once per step, so all indexing is linear. It produces
weights identical to the earlier version and to Python at every size.

### Aiur: the training step as a circuit

`ix/aiur/FixedStep.lean` writes one SGD step of the full model (16 hidden units, 331 parameters,
batches of 20) as a formal Aiur program.

**How the arithmetic is encoded:**
- **`shr8`** is fixed-point rounding. A hint supplies the quotient and remainder, and the circuit
  checks them: a range-checked remainder byte, a quotient range-checked in six bytes, and
  `256q + r = s`. That admits only the integer floor for `|s| < 2^55`.
- **ReLU and its derivative** use a byte-decomposed sign and a hinted zero test.
- **Everything else is exact field arithmetic.**

**How it is checked:**
- **Agreement with the Lean spec.** Lean's reference evaluator shows the Aiur `step` equals
  `IxAICore`'s `Model.step` on real batches, and the forward pass equals `Model.outputs` on 24
  held-out examples.
- **Dishonest hints are rejected:** a shifted quotient, a wrapped quotient (only the range check
  catches it), a flipped sign and a forged zero test.

**How it is proved.** The step compiles to a 12-chip circuit. `ixai_step all DIR 600` exports every
step of the full run as an execution package (weights, batch, learning rate and hint table), and
Aiur's GPU prover proves each one (`ix/aiur/prove-run.sh`). The prover is built in our own ix
worktree, `~/repos/ix.ixai-aiur`, at the same commit.

| | IxVM evaluation | Aiur circuit |
|---|---|---|
| One SGD step (full model) | minutes per 20-step chunk; 659 s to prove one chunk | **46 ms** to prove, 2 ms to execute, 21 ms to verify |
| The full 600-step run | projected about 6 h; shards exceeded the 30-minute cap | **32 s of proving**, 410 s end to end including a one-time 110 s circuit compile |
| Proof size | 50 MB per chunk | 4.3 MB per step |

`ixai aiur-chain .truthmines/aiur/full` checks the 600 proofs as a chain:
- every proof verified;
- step 0 was proved on `config.init`, the scheduled batch of the specified examples, and the configured rate;
- every proven output is `Model.step` of its input, and is the next step's input;
- the final proven weights equal `train spec config`.

The final weights are the Ixon constant `IxAICertified.full.trainedOutput`, `1393027d…` (weights
BLAKE3 `45ea4f5f…`). Changing one proven output by one unit, or an unverified proof, is rejected.

**Soundness of the hinted gadgets** (`ix/aiur/FixedSoundness.lean`, proved over the Goldilocks
field, standard axioms only):
- `shr8_sound`: for `|s| < 2^55`, the circuit's check `256q + r = s` in the field, with a
  range-checked remainder byte and a quotient within the six range-checked bytes, forces
  `q = ⌊s/256⌋`. A prover cannot shift the rounding.
- `sign_offset_sound`: the seven range-checked bytes reconstruct exactly `v + 2^55`, so bit 55 is
  `v ≥ 0`.
- `zero_test_sound`: with `nz = v·inv` and `v·(1 − nz) = 0`, `nz` is `1` exactly when `v ≠ 0`,
  whatever inverse is supplied.

**Status of the Aiur step's correctness.** Proved in Aiur's formal semantics, with standard axioms
only: `step_sound_deployed` and `train_of_deployed_steps` (`IxAIRefine/Fixed/Deployed.lean` in the
ix.ixai-aiur worktree) show that accepted `Fixed::step` claims, chained by their public inputs and
outputs, give `train Triage.spec fullConfig`. A verifier therefore checks only the proofs and the
chain links, without re-running `Model.step` (`ixai-verify`, `docs/verification.md`). Two links
remain outside Lean: an accepted STARK implies that the modelled checker accepts, and the shipped
circuit is the compilation of `Fixed.source` by an evaluation-checked parity, not a theorem.
The training proofs and the environment that holds this refinement theorem are folded into one
certificate: a 584-byte PLONK proof of an `AiurRun` claim that joins the IxVM check of the
environment (36,760 constants) with the 30-block training run, built on a fork of Ix that adds
the join to its aggregator and fixes two kernel issues the environment exposed
(`docs/offload.md`; identifiers, timings and what is checked independently in `docs/plan.md`).

### Working on a shared machine

- **Gate:** every heavy command (proving, compression, large compiles, project builds) goes
  through `ix/heavy.sh`.
  - It waits until no other `lake`, `lean`, `cargo`, `rustc`, `nvcc` or `ix prove`/`compress`
    process is running and load is low, then takes the heavy-job lock other sessions use.
  - It re-checks under the lock and logs every decision to `.truthmines/heavy.log`.
  - It refuses to run inside the command sandbox, where `ps` cannot see the machine.
- **Light lane:** a build of a few of this project's own Lean modules runs at once through
  `ix/light.sh`, beside a heavy job: one light job at a time, in a 24 GiB scope, 15 minutes at
  most. Everything else stays behind the gate.
- **Pinned toolchains:** the project keeps its own pinned copies of the Ix builds it uses, so
  rebuilds of other checkouts cannot change its results.
  - `ix/toolchain-ci`: the ci build, used for proving and aggregation.
  - `ix/toolchain`: the compression build, with the compression pipeline's artifacts, the Ignition SRS and a
    pipeline manifest whose base and cache are inside the project, pinned by BLAKE3 in
    `ix/toolchain/l3.json.blake3`.
  - Large files are hard links, so they take no extra space and keep their pinned bytes even if
    the original files are replaced.
  - IxVM and aggregation artifacts are in `ix/artifacts`, pinned by digest.
- **Reproduced from the pinned toolchain:** the tiny certificate, with the same public statement
  (`ladder_tiny_pinned`). The scripted end-to-end run (`tiny-e2e`) reproduced the same aggregate
  root, `193c85bd…`.

### Running it

```sh
lake build                                   # Lean 4.34.0 (.toolchain), FloatLib, Blake3
.lake/build/bin/ixai claims ix/bundle tiny   # Claims_tiny.lean: Eval inputs beside normal-form outputs
.lake/build/bin/ixai chain ix/bundle small   # Chain_small.lean: one Eval claim per training step
.lake/build/bin/ixai certified ix/bundle tiny  # Certified_tiny.lean: everything as kernel-checked theorems
.lake/build/bin/ixai forge ix/bundle tiny    # Forged_tiny.lean: claims Ix must refuse
.lake/build/bin/ixai reward ix/bundle        # agents' proofs checked by `ix check-lean`
.lake/build/bin/ixai mines .truthmines/index.tsv  # summarize the local Truth Mines index
cd ix/bundle && lake build IxAICore          # same sources on Ix's toolchain, Lean 4.34.1
../ixw compile Claims_tiny.lean --local --no-build --out claims.ixe
../certify.sh claims.ixe eval IxAIClaims.tiny.trainedInput IxAIClaims.tiny.trainedOutput
../certify.sh claims.ixe check IxAIClaims.tiny.deployedPublishSound
```

`ix/certify.sh` builds the claim in the local store, proves it on the GPU, verifies it and appends
a line to the index. Proving needs the GPU, which the command sandbox hides, so run it outside the
sandbox.

### Trusted base

What the certificates rest on:
- IxVM's soundness (`IxVM.consistent`, whose obligations are still open on PR #678);
- STARK and FRI soundness;
- BLAKE3;
- the pinned IxVM artifact (`ix/artifacts`, by digest);
- Lean's elaboration of the bundle's source into Ixon. `ix compile` is the certified compiler, but proved Ix elaboration is still work in progress.

Compressed certificates also rest on the BN254 SRS; this sketch used the development SRS for one
attempt and the Ignition SRS for the compression pipeline.

## Earlier mock-up

Modules under `IxAI/` model the wider pipeline with a toy kernel: orchestration, rewards, stores
and light clients (`Kernel`, `Store`, `Cert`, `Task`, `Orchestrate`, `Training`, `Decision`,
`Examples`). Next to them, the native milestone-1 pipeline (`Stmt`, `Num`, `Model`, `Data`,
`TrainClaim`, and the fixed-point, bfloat16 and binary32 formats in `Float` and `Formats`) is what
`ixai check` and the verifier's trajectory check use. Both are described below.

## Building

Lean 4.34.0 through `.toolchain`, with FloatLib, Mathlib and Blake3 as dependencies. On the shared
machine every build goes through the gate (`ix/heavy.sh lake build`):

```sh
lake build          # builds the libraries, runs the #guard tests, builds the executables
.lake/build/bin/demo
shell/golden.sh     # end-to-end determinism test with the untrusted Python trainer
ix/heavy.sh ix/verify-tests.sh  # the verification boundary on the built binaries (runs ix/reward-tests.sh too)
```

The tests in `IxAITest.lean`, `IxAICoreTest.lean` and `IxAIVerifyTest.lean` are `#guard`
commands, so they run during `lake build`, and any failure fails the build.

**Libraries** (all default targets), and what each one imports:

| Library | Contents | Imports |
|---|---|---|
| `IxAICore` | The kernel-evaluable specification | `Init` only |
| `IxAICommon` | Shared primitives: BLAKE3 and canonical encodings (`Hash`), Merkle roots and paths (`Merkle`), kernel normal-form literals (`Literal`), the project's location (`Paths`). Declarations in the `IxAI` namespace. | `IxAICore`, Blake3 |
| `IxAI` | The native milestone-1 pipeline and the toy-kernel mock-up (above) | `IxAICommon`, FloatLib |
| `IxAIVerify` | The consumer's verification layer (`docs/verification.md`), with the command-line helpers both executables share (`Cli`) | `IxAICore`, `IxAICommon`, the native pipeline of `IxAI`; no mock-up module |
| `IxAIData`, `IxAIBench` | Premise-selection datasets, IxBench | `IxAICore`, `IxAICommon`; `IxAIBench` also `IxAIData` |
| `IxAICli` | The commands of `ixai`, one module per concern: `Trajectory` (data, train), `Formats`, `RL`, `Codegen` (claims, chain, certified, forge, weights), `Mines`, `Reward`, `Package` (aiur-chain, aiur-diagnose, package-assemble), `Bench` | all of the above but the mock-up |
| `IxAITest`, `IxAICoreTest`, `IxAIVerifyTest` | Build-time tests | what they test |

Executables: `ixai-verify` (`IxaiVerify.lean`, linking `IxAIVerify` and what it imports only),
`ixai` (`Ixai.lean`, dispatch over `IxAICli`), `demo` (`Main.lean`, the mock-up's walkthrough).
`IxAIGpu` and `ixai-gpu-export` are built on request.

**Paths.** Nothing outside the project is fixed in the sources but as a default of a setting:

| Setting | Default | Read by |
|---|---|---|
| `IXAI_PROJECT` | the checkout whose `.lake/build/bin` holds the running executable | `IxAICommon/Paths.lean` (`projectDir`): `.truthmines` (index, rewards, package, datasets, bench results), `ix/ixw`, `ix/artifacts` |
| `IXAI_AIUREXEC` | `/home/sam/repos/forks/ix-aiurexec` | `IxAIVerify/Tools.lean` (the fork's release examples), `ix/verify-tests.sh` (their CUDA libraries) |
| `IXAI_VERIFY_CLAIM`, `IXAI_AIUR_EXEC_CHECK`, `IXAI_PLONK_VERIFY`, `IXAI_IXW`, `IXAI_IX_STORE` | those examples of the fork; the project's `ix/ixw` and `.truthmines/.ix/store` | `IxAIVerify/Tools.lean` |
| `IX_CI_CHECKOUT` | `/home/sam/repos/ix.ci-merge-tests` | `ix/ixw` (profile `ci`), the reward harness's `ix` binary (`IxAICli/Reward.lean`) |
| `IX_COMPRESS_CHECKOUT` | `/home/sam/repos/ix.aiur-compression-active` | `ix/ixw` (profile `compress`) |
| `IX_BIN`, `IX_LEAN` | the profile's binary; `/nix/store/xnh27vas…-lean-4.34.1` | `ix/ixw`, the reward harness, `ix/verify-tests.sh`, `ix/rebuild-full.sh` |
| `HEAVY_LOCK` | `/home/sam/repos/ix.aiur-compression-active/target/heavy.lock`, shared with the other sessions | `ix/heavy.sh` |
| `IXAI_VERIFY_WORK` | `/tmp` | scratch directories of the verifiers and the tests |
| `ixai reward BUNDLE --out FILE` | the project's `.truthmines/rewards.tsv` | `IxAICli/Reward.lean` |
| `ixai package-assemble --out DIR` | the project's `.truthmines/package/full` | `IxAICli/Package.lean` |

The scripts under `ix/` find the project from their own location.

## Certified training of a tiny model (milestone 1)

A 16-unit MLP learns to predict whether a formula of the toy logic is classically valid.

- **Labels are decided, not annotated.** `Data.lean` generates formulas from a seed and labels
  them by truth table. The dataset is committed by a Merkle root, and its claim says every item is
  what the specification computes from its formula.
- **Training is a specification.** `Model.lean` defines forward pass, hand-written
  backpropagation and SGD once, against the `Arith` numeric interface in `Num.lean`. The run is a
  pure function of the config and the dataset (`TrainConfig.spec`): the seed fixes the initial
  weights and the batch schedule.
- **Determinism by construction.** Products round; sums of products are accumulated exactly and
  rounded once. The result does not depend on the order of a reduction, so a parallel
  implementation can reproduce it bit for bit.
- **Untrusted trainer, trusted checker.** `shell/train.py` trains in Python. `ixai check`
  recomputes each step against the Lean specification. `verifyRun_sound` shows that an accepted
  trajectory ends at exactly the specified weights, satisfies the per-step invariant, and used the
  committed dataset.

```sh
ixai data data.txt                      # config, dataset root and items, for the trainer
python3 -I shell/train.py data.txt py.txt
ixai check py.txt                       # against the consumer's job (`--job default`), not the file's header
```

`shell/golden.sh` checks that the Python run is bit-identical to `ixai train`, also with every
reduction summed in reverse order, and that a run with one weight changed by one unit at one
step is rejected, naming that step.

**Formats.** The model is written once against `Arith` (`Num.lean`) and runs in three formats:
fixed point (`fx`), and FloatLib's IEEE `bf16` and `f32` (`Float.lean`, FloatLib commit
`21865090` on Lean 4.34.0 and Mathlib v4.34.0). Every batch gradient entry is an exact sum over
the batch, rounded once, so neither the order of terms in a dot product nor the order of examples
in a batch affects any bit. `ixai --format bf16 train FILE` and `ixai check FILE` work per
format. `shell/train.py` implements IEEE rounding independently (exact rationals, round to
nearest, ties to even, FloatLib's signed-zero rules) and reproduces the Lean runs bit for bit.

| Format | Held-out accuracy | Lean train + check | Python trainer |
|---|---|---|---|
| `fx` | 92% | 0.2 s | 0.4 s |
| `bf16` | 82% | 1.4 s | 2.7 s |
| `f32` | 82% | about 1.5 s | 3.3 s |

The toolchain is pinned through `.toolchain`, a Nix GC root for Lean 4.34.0
(`nix build -o .toolchain` with lean4-nix's `fromToolchainFile`). Mathlib's cache lives in
`.cache` (`XDG_CACHE_HOME=$PWD/.cache lake exe cache get`).

**Checked natively, not by a kernel.** These modules are run and checked as compiled Lean
(`ixai check`). The specification that Ix certifies is `IxAICore` (above), written for kernel
evaluation; commitments in both use BLAKE3 (`IxAICommon/Hash.lean`).

## Map

| Module | Models | Strategy doc |
|---|---|---|
| `IxAI/Stmt.lean` | The toy logic's statements and their canonical encoding | §4.1 |
| `IxAI/Kernel.lean` | Content-addressed statements and proofs. A checker that reads only an interface (statements and axiom footprints, never proof bodies). Axioms identified by name *and* statement. | §4.1, §8.3 |
| `IxAICommon/Merkle.lean` | Membership paths, so a light client can use one constant of a large store without holding the rest | §5.1, §8.4 |
| `IxAI/Store.lean` | Truth Mines: append-only checked store with a root, full recheck, dependency closure | §5 |
| `IxAI/Cert.lean` | `Claim`, `Holds`, `ProofSystem` with a soundness predicate, a non-succinct mock, light clients | §4.2, §4.3, §8.2 |
| `IxAI/Task.lean` | Tasks with fixed targets, the rewarder, task environments carved from a store | §7.2, §8.3 |
| `IxAI/Orchestrate.lean` | Interface-first projects: spec statements, delegated submissions, deduplication, progress, promotion | §8.5 |
| `IxAI/Training.lean` | RL episodes with in-loop kernel rewards and promotion of accepted results; dataset claims | §7.5, §8.3 |
| `IxAI/Decision.lean` | Typed decision answers and gates whose safety holds for every model output | §9.2 |
| `IxAI/Examples.lean` | A three-statement library standing in for FLT; honest and reward-hacking agents | §8 |
| `IxAI/Num.lean` | The `Arith` numeric interface and the fixed-point instance, with exact accumulation | §9.3 |
| `IxAI/Model.lean` | Tiny MLP: forward pass, backpropagation, SGD step, training fold | §9.3 |
| `IxAI/Data.lean` | Specified PRNG, formula generator, decided labels, committed dataset | §7.1 |
| `IxAI/TrainClaim.lean` | Training configs, schedules, step chains, `verifyRun` and its soundness theorem | §7.4, §8.3 |
| `Ixai.lean`, `IxAICli/Trajectory.lean` | The `ixai` executable: export data, write the reference run, check any run | §7.5 |
| `shell/train.py`, `shell/golden.sh` | Untrusted Python trainer and the determinism test | §7.5 |

## What is proved

All proofs use only Lean's standard axioms.

- `reward_accepted`: an `accepted` verdict means the candidate proves exactly the task's fixed target statement, with no holes, by a proof the kernel accepts against the task interface, using only allowed axioms. A model cannot earn reward by weakening or restating the target.
- `mkTask_excludes_target`: a task environment never offers the target, or a renamed copy of it, as a citable lemma.
- `mock_sound`: the mock proof system is sound for `Holds`.
- `lightClient_sound`: for any sound proof system, a light client that knows only the statement and the root learns `Holds` for that statement's address.
- `chain_eq_fold`: for any step function, a chain of steps in which each link starts where the last ended and applies the step correctly ends at the fold of the step over the inputs. It uses no axioms.
- `chainCheck_spec`: the executable chain check implies that, and that the invariant holds at the end.
- `verifyRun_sound`: an accepted training trajectory ends at exactly `TrainConfig.spec` of the committed dataset, the final weights satisfy the invariant, and the dataset passes its claim.
- `Fx.exactSum_reverse`: exact accumulation is independent of summation order.
- `Gate.approve_sound` and `Gate.approve_monotone`: approval happens only at or above the threshold, whatever the model outputs.

## What the tests exercise

- Orchestration: a proof citing an unaccepted lemma fails, then succeeds once the lemma is accepted. A weakened statement, a proof hole and an unlisted axiom are each rejected for the right reason. A renamed duplicate becomes reuse. Progress reaches 3/3.
- Training: honest reference proofs pass every task, and every hack fails every task, including reusing an allowed axiom name to assert a different statement.
- Certificates: a certificate verifies for its statement, not for another statement. No certificate is produced for an unproved statement. Membership paths verify for each entry and fail for the wrong leaf.
- Decisions: gate outcomes and confidence at the extremes.

## What is mocked, and what Ix would supply

| Mock | Ix |
|---|---|
| Propositional natural deduction, `infer` | Ixon terms checked by IxCK, proved in IxVM |
| BLAKE3 addresses over the mock's own term encoding | BLAKE3 over canonical, alpha-invariant Ixon |
| `Stmt` given directly | Statements from proved Ix elaboration |
| `mock` proof system: the certificate carries the whole store and is rechecked | `check`/`checkEnv` claims, aggregated and compressed to a fixed-size PLONK certificate; soundness from `IxVM.consistent` plus cryptographic assumptions |
| A list-based store and a simple Merkle tree | The Truth Mines root and its update relation, still to be specified (§5.1) |

The rest of the pipeline only depends on `ProofSystem.Sound`, so replacing `mock` with an Ix-backed system changes costs, not the guarantees above.

## Next steps

The mock-up's own plan was to back `ProofSystem` with Ix, replace the toy kernel with Ixon
constants and add evaluation-backed checks. The certified pipeline above does those for training,
evaluation and the gate (real `check`/`checkEnv` claims, Ixon addresses, compressed
certificates); the mock-up remains as the model of orchestration, rewards and stores. Still
open from that plan: the store-update relation and the root's membership proofs, task interfaces
carved from a real environment, and timeouts and budgets in the episode runner. Current work is
tracked in `docs/plan.md`.
