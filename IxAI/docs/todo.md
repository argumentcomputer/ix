# Remaining work

State on 2026-11-21, after the 30-minute goal was met (22:51, `certificates/m2`). The design
of what exists is in `design.md`. Each item says what is there, what is missing, and the first
step. Estimates are marked as such; everything else is measured.

No job is queued or running. The owner stopped the remaining measurement runs on 2026-11-21:
they are listed in section 1 and none of them blocks anything else.

## 1. Implemented, not yet measured

### 1.1 The stall fix in a whole run

- **There:** the prover validates a prepared record once (on `ix-ai`; fork branch
  `cert-validate-once`). Keys unchanged, proof of the smallest claim byte-identical, the prover
  crate's tests pass. On the largest claim alone: trace 149.4 s to 80.4 s, GPU stall 58.2 s to
  12.1 s, end to end 491 s to 453 s. On the smallest: stall 18.4 s to 5.6 s, 3:57 to 3:48.
- **Missing:** the environment in one run, and a timed end-to-end run. The toolchain the
  scripts use (`ix/toolchain-cert`, built from fork branch `cert`) does not contain the fix.
- **First step:** merge `cert-validate-once` into `cert`, run `ix/combined/build_cert.sh`
  (about 4 minutes when the build tree is warm; pins must not change), then
  `ix/combined/timed_run.sh g5`.
- **Estimate:** half a minute to a minute and a half off the 13:52 environment stage. The gain
  is smaller than the stall it removes, because on the largest claim execution (292 s) and GPU
  proving (about 140 s) are untouched.

### 1.2 Premise selection at Mathlib scale

- **There:** the changes are on `ix-ai`. The small benchmark is byte-identical and ran in
  16.1 s for 27.4 s.
- **Missing:** the Mathlib-scale run. Baseline: module split 918 s (ranking 421 s, training 178
  to 202 s per epoch, 6.14 GB peak); time split 1,959 s (ranking 437 s, 6.48 GB).
- **First step:** `review2-premises/job.sh after1` on the scratch disk, about an hour. Every
  digest must equal the recorded one.
- **Estimate:** ranking several times faster (it re-embedded 270,304 premises per theorem);
  training less; about 0.9 GB lower peak.

### 1.3 GPU trainer variants

Five changes to `step.cu`, built and never run, kept as patches with their harness and the
acceptance list in `gpu/variants/README.md`. The trainer in `gpu/cuda` is unchanged.

### 1.4 The timed run, repeated

22:51 is one run. Two more runs of `timed_run.sh` on an idle machine would give the spread.

## 2. Verifier follow-ups

- **Pass the model check through.** `aiur_join_check` has `--model-constant` and `--contains`;
  `ixai-verify combined` does not pass them, so the consumer's verdict does not yet include
  "the card is about the trained model". Add the options to `IxAIVerify/Combined.lean`, list
  them among the checks, and add a rejecting test (a model constant that differs in one word).
- **Default circuit digests.** Without `--ixvm-blake3` and `--join-aggregator-blake3` the
  verifier approves M1's circuits. Either require the options or read the digests from the
  job commitment, so that the job, not a constant in the verifier, names the kernel.
- **Reward submission** takes 18.2 s, about 7 s of it three `ixw addr-of` calls. Combining them
  needs a change to the pinned toolchain.

## 3. Owed for soundness and for upstream

- **Refinement proofs of the changed kernel functions.** Upstream proves IxVM's kernel refines
  its specification. This branch changed `try_nat_dispatch_prewhnf`, the substitution walks and
  searches (merged closedness test, skipped closed subterms, accumulator spines, early exit,
  lazy number decoding) and the rebase search (`expr_glb_shallow`, shared by `k_infer_rebase`
  and `k_def_eq_rebase`). Their proofs are not redone. Until they are, the kernel changes rest
  on tests: the exploit suite, circuit verdicts, claim safety, and equal verdicts on every
  shard and on 80 Mathlib claims.
- **Pinned costs and generated files.** Ix's IxVM test tier fails three suites for bookkeeping
  reasons: 149 pinned FFT costs are now lower (`ixvm-eval`, `ixvm-kernel-checks`), and
  `IxVM/IxVM/Lookup.lean` and `Ix/IxVM/Refinement/Mirrors/KernelLevels.lean` are stale
  (`lake exe ixvm/ixvm-proof-gen`). Repin and regenerate, then the tier should pass in full.
- **Unproved prototypes.** `ix_aggr`'s join shapes for an Aiur child and the `AiurExec` run
  aggregator have no soundness proof. `BlockOnlyParity` is checked by evaluation. The claim
  encoding is checked in Rust, not in Lean.
- **A witness for the def-eq rebase.** Upstream added it for a constant
  (`Simps.addProjections._unsafe_rec`) that is not in our Mathlib snapshot. The bounded search
  leaves our stand-in unchanged (98.8 million queries), but the original case is untested here.
- **A fixed cost on small claims.** 69 of the 80 Mathlib claims cost 16 to 45 rows more under
  the bounded search (at most +0.003%); the total is 0.01% lower.
- **Upstreaming.** The branch is one line of history. For review upstream it splits into: the
  substitution changes; the bounded rebase search; validate-once (upstream has it; drop ours on
  rebase); the Aiur-child join shapes with `aiur_exec`; `aiur_join_check`; the sub-project.

## 4. Next performance steps

Where the 22:51 is: environment 13:52, training side 5:12 (tree 4:26), compression 3:19, join
and check 0:28.

### 4.1 Prove the environment once per model shape

- **Today:** every certificate re-proves the whole environment, 13:52, although nearly all of
  it (the specification, the compiler's proofs, the path lemmas) depends only on the model's
  shape. Per run, only the top theorem's configuration and the module with the trained model,
  its card and decisions change.
- **Design:** state the top theorem for any configuration of the shape (seed, data, number of
  blocks as arguments), so one environment proof serves every run of that shape. Keep the
  run's module in a shard of its own and fix the partition, so the prover reuses the stored
  proofs of the unchanged shards (it does this already when `--fresh` is not given) and proves
  one small shard and the joins.
- **Estimate:** training side, join, check and compression are 9 minutes. The run's own shard
  costs about 0.2 billion kernel queries (the card is 183 million, 1:23 on its own) and the
  environment's joins took 2:20 in the timed run, so about 13 minutes per further run, less if
  the card is certified beside the certificate instead of inside it.
- **First step:** find what in `train_of_deployed_blocks_enc` and `blockRun` is specific to the
  deployed configuration, and whether the sharder keeps a partition stable when one module
  changes.

### 4.2 The training side's tree

4:26 of the 5:12 is the aggregation tree over 30 block proofs. At most 20 to 25 seconds are
recoverable by scheduling alone. Larger steps: fewer and larger blocks (each block proof is
under a second today), or a wider tree. Both change the program's key and the binding, so they
cost one re-proof of the environment; do them together with 4.1.

### 4.3 The rest of the GPU stall

After validate-once the host still fills nearly every trace cell: the device record of all 240
eligible circuits is 151 GB against a 96 GB card, so 6 are admitted, and each shard is supplied
twice because multi-shard batches with device lookups always regenerate. Both are prover design
questions for upstream, not settings. What shrinks the cost from our side is a smaller trace,
which is 4.4.

### 4.4 The kernel on machine-generated proofs

The largest claim's execution, 292 s, starts the critical path. Two directions:

- **Free variables by level** (parked redesign). The kernel moves terms under and out of
  binders by shifting indices, and the rebase search exists to recover memo sharing that the
  shifting destroys. Opening a binder with a free variable numbered by its depth removes the
  shifting, the search and most of substitution's index work. The variables are numbers, not
  names, so content addresses stay anonymous. It is a rewrite of inference and definitional
  equality and of their refinement proofs; nothing is measured.
- **The row profiler on Mathlib** (asked for by the owner, to run once the goal is met). The
  profiler is on the branch (`IX_KERNEL_ROWS_PROFILE`, `IX_KERNEL_HINTS_TRACE`). Plan: a
  profiler build of the current kernel; a pilot on the 80-claim sample and a few shards of the
  Mathlib store to state what the whole library costs before starting it; then execution only,
  shard by shard and resumable. Deliverable: where Mathlib's rows are, by kernel function.

### 4.5 Compression

3:19, fixed per certificate, not examined.

## 5. Parked product work

- **The decision library's training objective.** Three pre-registered threshold rules failed to
  make the gate both safer than the policy and useful; an oracle threshold shows the limit is
  the training objective, which is a change to the core specification (`decision-library.md`).
- **Lane.** Design docs are on the branch (`lane.md`, `integration.md`). The fork
  (`~/repos/forks/lane`, branch `outcome-records`) is untested and the gate prototype
  (`IxAIDecide/LaneGate.lean` in the working directory) is deliberately not on the branch.
- **A training program generic in size.** The Aiur program is written out for 8×16×11. A
  generic one would make the refinement proof independent of shape; it needs loops over
  runtime sizes in the program and in the path lemmas.
- **A second use case** beside triage, and the reinforcement-learning loop (`rl.md`).

## 6. Housekeeping

- **Working directory.** Work happens in `~/repos/ix-ai-pipeline`; the branch's copy is
  `IxAI/` in `~/repos/forks/ix-ai`, and files are copied across at each commit. The scripts
  assume the first location. Move the working directory into the worktree and make the scripts
  relative. The standalone git repository in the working directory (one commit) is redundant.
- **Toolchain and branch.** `ix-ai` is ahead of fork branch `cert` by the validate-once merge;
  `cert` is what `build_cert.sh` builds (see 1.1).
- **Scratch disk.** `/opt/dlami/nvme` is wiped when the instance stops. Only there: the built
  toolchain trees (`cert`, `combined/target`), the kernel variants' binaries and run data
  (`kernel-subst`), the stall and validate-once runs and pinned binaries (`timed`), the built
  environment tree with the fused lemmas (`combined/src-fuse`), the GPU variants' builds and
  the 2026-11-19 baseline results (`review2-gpu`), the premise baseline (`review2-premises`).
  The `cert-validate-once` worktree is there too: after a stop, `git worktree prune` in the
  fork. Sources and results that matter are on the branch or in `.truthmines`.
- **Stale build tree.** `.truthmines/combined/src/Aiur` has the fused sources and old build
  outputs; rebuild it before using it.
- **Root disk** is 94% full (31 GB free).
- **Fork branches that can go:** `exp-noinferrebase`, `exp-norebase`, `infer-rebase-shallow`,
  `shallow32`, `rebase-shared32`, all superseded by `rebase-shared64`, which is merged.
- **Nothing is pushed.** The fork's push URL is disabled. To publish:
  `git -C ~/repos/forks/ix-ai push -u origin ix-ai` and
  `git -C ~/repos/forks/ix-ai push origin ixai-m1 ixai-m2`.
