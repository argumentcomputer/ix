# Design: one certificate for a trained decision model

This is the design of the system as it stands on branch `ix-ai` after the 30-minute goal was
met (2026-11-21): what the certificate says, how it is produced, why each part is shaped the
way it is, and what it rests on. Remaining work is in `todo.md`. The history of measurements
and decisions is in `plan.md`; the join is designed in detail in `aiur-composition.md` and the
consumer's acceptance contract in `verification.md`.

## What the certificate says

One 584-byte PLONK proof (`certificates/m2/proof.bin`) covers one `AiurRun` claim that joins
two proofs:

- **The environment.** An IxVM `CheckEnv` aggregate: Ix's kernel, running inside the proof,
  typechecked a Lean environment of 36,915 constants with no user axiom. That environment
  holds:
  - the specification of training, `IxAICore.train`, and of the triage task;
  - the refinement theorem `IxAICombined.train_of_deployed_blocks_enc`, which says that 30
    executions of the Aiur program `Fixed::train_block`, started from the specification's
    initial model, end at the encoding of `train spec config`;
  - the binding `IxAICombined.blockRun`, which names that program by its key;
  - the safety theorems of the gate, which hold for every weight setting;
  - the trained model as a constant (`IxAICombined.Deployed.trainedOutput`), its evaluation
    card on 200 held-out formulas (`cardCertified`) and four gate decisions.
- **The training run.** An aggregate over 30 executions of `Fixed::train_block` (20 SGD steps
  each, 600 in all), chained from the initial model to the final one.

The join verifies both proofs and opens the theorem and the binding in the environment's
subject root by Merkle paths. Together with the theorem, the claim gives

    IxAICore.train IxAICore.Triage.spec (config full) = the submitted model

and the independent check confirms that the model constant in the environment is that same
model, so the card and the decisions are statements about the trained weights.

A consumer checks it in 7 seconds (`ixai-verify combined`) without re-running training and
without the prover's logs.

## The pieces

| Piece | What it is | Where |
|---|---|---|
| Specification | The model, `train`, the data and label generators, the gate and its theorems. Imports only `Init`; written so a kernel can evaluate it. | `IxAI/IxAICore` |
| Training program | The same training step written for Aiur, Ix's circuit language: `Fixed::step`, `Fixed::train_block`. Written out per model shape (8×16×11, batch 20, 20 steps a block). | `Aiur/IxAIStep.lean`, `Aiur/IxAIRefine/Fixed` |
| Refinement proofs | Generated path lemmas, one family per function of the program, and the hand-written theorems that compose them into the refinement theorem. | `Aiur/IxAIRefine`, `Aiur/IxAICombined.lean` |
| Deployed model module | Generated from a run's output: the model literal, its range lemma, the card and the decisions. | `Aiur/IxAICombined/Deployed.lean`, `IxAI/ix/combined/gen_deployed.py` |
| Kernel | Ix's kernel as an Aiur program (IxVM), with this branch's cost reductions. | `Ix/IxVM` |
| Run aggregator | Proves a chain of executions of one program and folds them into a tree. | `aiur_exec`, `aiur_exec_tree` (prover examples) |
| Join | `ix_aggr` with a join shape whose second child is an Aiur run. | `crates/ix-prover/src/aggregate.rs` |
| Independent checker | Recomputes the joined claim from the files and checks the root proof; confirms named constants are in the environment and that one of them is the run's final model. | `aiur_join_check` |
| Compression | The joined root wrapped and compressed to PLONK over BN254. | the compression pipeline, pinned under `IxAI/ix/toolchain` |
| Consumer verifier | A Lean program that checks a job commitment, the certificate and the files, and prints the hypotheses the verdict rests on. | `IxAI/IxAIVerify`, `IxAI/IxaiVerify.lean` |
| GPU trainer | Lean host and CUDA kernels that produce the same bits as the specification, and the witness packages the prover consumes. Untrusted. | `IxAI/IxAIGpu`, `IxAI/gpu/cuda` |
| Decision library | Typed options, encodings, tasks and gates with theorems for every weight setting; an invoice use case. | `IxAI/IxAIDecide`, `decision-library.md` |
| Premise selection | The dataset over all of Mathlib, the scorer and the benchmarks. Not part of the certificate. | `IxAI/IxAIData`, `IxAI/IxAIBench`, `data.md` |
| Scripts | The stages below, the job gate and the measurement tools. | `IxAI/ix`, `IxAI/ix/combined` |
| Certificates | The records of M1 (116:46) and M2 (22:51). | `IxAI/certificates` |

## The pipeline

`ix/combined/timed_run.sh NAME` runs every stage as one job under one clock, reusing no proof.
Times are from the run recorded in `certificates/m2`.

| Stage | What happens | Time |
|---|---|---|
| train | 30 block proofs (23 s), their aggregation tree (4:26), two wraps of the tree's top (23 s) | 5:12 |
| env | the environment's three claims executed and proved, and their joins, in one prover run | 13:52 |
| export | the environment root laid out as files | 0:02 |
| join | environment root and training root joined into one `AiurRun` claim | 0:23 |
| check | `aiur_join_check` on the joined root; nothing is compressed before it passes | 0:04 |
| compress | the joined root compressed to the 584-byte certificate | 3:19 |
| **total** | | **22:51** |

Outside the clock: the Lean build of the environment (8 minutes), its certified compile (about
80 s), the one-time circuit exports and keys, and verification.

The machine has one 96 GB GPU. Heavy jobs run one at a time through `ix/heavy.sh`, a FIFO gate
with priorities; short builds use `ix/light.sh`, a capped lane that stands aside for timed runs.

## Design decisions

**Integer parameters.** A weight is a fixed-point number `raw / 256` with `raw : Int`. Sums are
exact and a product rounds once, so no implementation, summation order or device can change a
bit. This is what makes "the same training gives the same output" a theorem and not a hope, and
it makes the encoding of a model into field elements one-to-one, which the checker relies on
when it compares the model constant with the run's output.

**Certified results, not certified training code.** The GPU trainer and the Lean host are
untrusted. They only have to produce the bits; the certificate says the bits are
`train spec config`. A wrong trainer cannot produce an accepted certificate.

**Training is proved in Aiur, the theorems in IxVM.** Evaluating training inside the kernel
does not scale: the small model's 8 steps took 100 s as a kernel evaluation. Aiur executes the
steps directly (23 s for all 30 block proofs). The price is a refinement theorem connecting the
Aiur program to the Lean specification, which the kernel checks once. The join puts both under
one statement.

**Blocks of 20 steps.** The run is proved as 30 executions of a 20-step block, folded into a
tree, where the earlier route needed one proof for each of the 600 steps.

**The program is written out per shape.** `train_block` has its 20 steps and its matrix
routines unrolled for 8×16×11 and batch 20. The refinement proof therefore depends on the model
shape, not on the data or the run. The top theorem is stated for the deployed configuration.

**Generated lemmas in continuation form.** The refinement proof has about 1,650 generated
lemmas, one per path through each function. In their first form they were 71% of the kernel's
work on the environment. `obs_rewrite.py --fuse` rewrites them so that a path's steps are
chained through 61 shared lemmas (`Core/Fused.lean`) instead of nested, which cut the two
worst lemmas' kernel cost almost five times with identical statements.

**The kernel's substitution and search.** Two rounds of changes to the IxVM kernel, each
leaving every verdict unchanged:
- substitution walks are merged with the closedness test, skip closed subterms, and build
  spines with an accumulator; searches stop early; number decoding is lazy;
- the search that finds how far a term can be lowered past unused binders, used to share memo
  keys in inference and definitional equality, is one memoized search bounded at 64 binders.
  Past the bound it answers 0, the answer for a term that is not lowered, which is valid for
  every term, so nothing that was rejected can be accepted.

Together: 7.2 billion kernel queries on the first environment, 1.86 billion after; on a sample
of 80 Mathlib claims, 19% fewer rows than before the first round and no more than the first
round alone.

**One prover run for the environment.** The prover executes claims while the GPU proves
others. M1 proved shard by shard in separate runs, which left the GPU idle during every
execution; the environment is now one `prove --aggregate --fresh` run over the whole manifest,
leaf proofs and aggregation together.

**Prover settings for the environment stage.** `AIUR_GPU_TRACE=cpu` with
`AIUR_TRACE_SHARD_MAX_CELLS=2100000000`: on these claims the device record of all circuits does
not fit the card beside the trace shards, so the planner fills nearly everything on the host
whatever the mode, and without a device record the card holds larger shards. `--max-ram 200`
on a machine the run has to itself.

**A prepared record is validated once.** The prover re-checked the whole execution record
before every shard it supplied to the GPU, serially, which starved the GPU on large claims.
The branch carries the validate-once part of upstream's fix. It changes no circuit and no key;
proofs are byte-identical.

**The model constant is checked, not trusted.** The environment says "this constant has this
card". The run says "training ended at this output". `aiur_join_check --model-constant` decodes
the constant by structure and compares it word by word with the run's output, so the two are
about the same model.

**The consumer approves circuits by digest.** `ixai-verify combined` takes the BLAKE3 of the
IxVM artifact and of the join aggregator on the command line, recompiles them to keys through
the checker, and lists that approval among the hypotheses it prints. A certificate made under a
changed kernel is checked the same way as the first.

**Safety by construction.** The deployed system acts only through a gate, and the gate's
theorems (`act_publish_sound`, `act_publish_confident`, `act_defer_iff`) hold for every weight
setting. Training, and any reward that drives it, changes how much work the model saves, never
what the system may do.

**BLAKE3 everywhere.** Constants, artifacts, jobs, certificates and store entries are named by
BLAKE3, as in Ix.

## What it rests on

Listed in full by the verifier's output and in `verification.md`. In short:

- soundness of STARK, FRI and PLONK and Ix's audit boundary; BLAKE3; the Ignition ceremony;
- soundness of IxVM's kernel, where this branch changed functions whose upstream refinement
  proofs are not redone: `try_nat_dispatch_prewhnf`, the substitution walks and searches, and
  the bounded rebase search;
- soundness of `ix_aggr` with the join shapes for an Aiur child, and of the `AiurExec` run
  aggregator: both unproved prototypes;
- `BlockOnlyParity`, checked by evaluation; the claim encoding, checked in Rust;
- the compression pipeline's layers.

The kernel changes are tested, not proved: Ix's IxVM test tier passes 14 of 17 suites on the
adopted kernel, including the exploit suite, circuit verdicts and claim safety; the three
failures are 149 pinned costs that are now lower and two generated files that need regenerating.

## How the time came down

| Step | Environment | End to end |
|---|---|---|
| M1: five prover runs, first kernel changes | 107:56 | 116:46 |
| Substitution walks and searches; one prover run | 32:52 | |
| Generated lemmas in continuation form | 15:33 | 24:23 on paper |
| Bounded rebase search; shard-size setting; card and decisions added | 13:52 | **22:51** measured |

Validating a record once is on the branch but not in that run: on the largest claim alone it
measured 491 s to 453 s.

## Reproducing the timed run

With the environment built, compiled and cut (`.truthmines/combined/env/g5.ixe`, `g5.ixes`;
`ix/combined/envc.sh` compiles a variant, `gen_deployed.py` writes the model module) and the
30 training packages in place:

```sh
CHECK_FLAGS="--model-constant IxAICombined.Deployed.trainedOutput --contains IxAICombined.Deployed.cardCertified" \
  HEAVY_PRIORITY=1 ix/heavy.sh ix/combined/timed_run.sh g5
```

It writes `cert/g5/timeline.tsv`, the certificate and every stage's log. The consumer's check
is the command in `certificates/m2/README.md`.
