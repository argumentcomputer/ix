# References and context

Pointers only: local code, Ix internals, machine rules, CLI notes, external papers and products.
Decisions, status and results are in `plan.md`. Facts here were checked against the code on the
date noted, so re-verify paths before relying on them.

Last checked: 2026-11-18.

## Machine rules (shared box)

- Other agents build Ix and run Mathlib here. Before any build, test or proof, check the box is
  free, and run every heavy command through the gate:
  `ix/heavy.sh timeout 1800 <cmd>`. It waits for other lake/lean/cargo/rustc/nvcc/ix jobs and a
  low load, takes FIFO tickets (`.truthmines/heavy.queue`), holds
  `~/repos/ix.aiur-compression-active/target/heavy.lock`, and logs to `.truthmines/heavy.log`.
- A build of a few of this project's own Lean modules need not wait in that queue:
  `ix/light.sh <cmd>` runs it at once, beside a heavy job, one light job at a time, in a 24 GiB
  scope with a 15-minute limit, and logs `light-start`/`light-end` to the same log. Not for
  proving, IxVM execution, builds of ix or Rust crates, test suites that run a prover or
  checker, or anything whose timing is reported. A timing measured while a light job ran shows
  as an overlap in the log and should be reported as such.
- While a job is queued or running, keep working: review, write the documentation, plan the
  next step. Do not end a turn to wait for a job.
- The gate refuses to run inside the Bash sandbox (`ps` sees too little); run it unsandboxed.
  Outside the sandbox `$TMPDIR` is unset.
- No single execution may run longer than 30 minutes (`timeout 1800`); split work instead.
- Never edit `~/repos/ix.ci-merge-tests` (owned by another agent) or `~/repos/clones/*`
  (read-only research clones). Never push; never write a repo-local `.claude/`.
- One GPU (RTX PRO 6000, 98 GB). `ix prove --gpu-device 0` uses it; heavy shards are dominated by
  CPU-side execution before the STARK starts.

## This project: `~/repos/ix-ai-pipeline`

Lean 4.34.0 (`.toolchain`, a Nix GC root), FloatLib `21865090`, Mathlib v4.34.0, Blake3
`3f8b8056`. Not a git repository.

| Path | What |
|---|---|
| `IxAICore/` | The kernel-evaluable spec (Init only, structural recursion): `Fx` fixed point, `Rng` xorshift64*, `Formula`, `Decision` (typed Jev-style decision model, `train`, `card`), `Triage` (gate + safety theorems), `Chain` (per-step certification), `Reinforce` (verifiable RL), `TriagePolicy` (RL routing policy). |
| `IxAICommon/` | Shared primitives: `Hash.lean` (BLAKE3 `digestOf`, canonical `Enc`), `Merkle.lean`, `Literal.lean` (kernel normal-form rendering for Eval claims), `Paths.lean` (the project's location, `IXAI_PROJECT`). |
| `IxAI/` | Host side: the MLP pipeline in fx/bf16/f32, and the toy-kernel mock-up. |
| `Ixai.lean`, `IxAICli/` | The `ixai` CLI (dispatch in `Ixai.lean`, one `IxAICli` module per concern): `claims`, `chain`, `certified DIR SIZE [K]`, `forge`, `mines`, `reward`, `rl`, `aiur-chain`, `package-assemble`, `blake3`, … |
| `shell/train.py`, `shell/triage.py` | Python mirrors; bit-identical to Lean (determinism check). |
| `ix/ixw` | Runs `ix` with `HOME=.truthmines`; `IX_PROFILE` = `ci` (`IX_CI_CHECKOUT`, default ix.ci-merge-tests, IxVM `5111b234`), `ci-pinned` (`ix/toolchain-ci`, hard-linked binary), `compress`, `pinned` (`ix/toolchain`: compression binary, compression pipeline artifacts, Ignition SRS, `l3.json` pinned by `l3.json.blake3`). |
| `ix/certify.sh` | One Eval/Check claim: binding, prove, verify, index line. |
| `ix/certify-full.sh` | Resumable whole-environment run: per-shard gated prove, aggregate (`stark-export-7d687ca0` artifact), `export_root`, `ladder.sh` to PLONK, index record. |
| `ix/rebuild-full.sh`, `ix/full-run.sh` | Regenerate + compile `Certified_full`, then shard and certify. |
| `ix/bundle/` | Lean 4.34.1 project of generated claim files (`Certified_*`, `Claims_*`, `Forged_*`, `Reward_*`) and their `.ixe`/`.ixes`. |
| `gpu/` | GPU trainer: `cuda/step.cu` (kernels, each commented with the `IxAIGpu.Step` function it implements), `cuda/ixai_gpu.c` (C shim giving them Lean's object ABI), `cuda/error_test.cu` with `error-test.sh` (failed calls report their real CUDA error), `test.sh` (differential tests; results in `.truthmines/gpu/test-lean`). The host is `IxAIGpuHost` in the worktree's Aiur package (`lean_exe ixai_gpu`: `train`, `keys`, `check`, `package`). |
| `IxAIGpu/` | Theorems about the kernels: `Reduce` (warp reductions are exact sums), `Step` (`gpuStep = Model.step`), `Keys` (`gpuStepHintKeys_eq`), `HostKeys` (`stepHintKeys` restated over `IxAICore`). |
| `ix/aiur/` | `FixedStep.lean` (the `Fixed` Aiur program, mirror of the worktree copy), `FixedSoundness.lean` (gadget soundness over Goldilocks), `prove-run.sh`. |
| `.truthmines/` | Local Truth Mines: Ix store (`.ix/store`), `index.tsv` (every certified claim), `rewards.tsv`, `heavy.log`, `compression/` (runs, ladders, PLONK proofs), `aiur/full` (600 step proofs), `store/` (Ix compiles of Mathlib, Lean core, FLT, CSLib, PhysLean; `store/index.tsv`), `datasets/` (premise extractions). |
| `docs/aiur-composition.md` | Chosen design for one certificate: dedicated Aiur circuit + refinement proof + key-as-data `aiurExec` aggregation child. |
| `docs/rl.md` | Verifiable RL design and related work. |
| `docs/plan.md` | Goal, status, decisions, results, next steps. |
| `~/repos/notes/ix-ai-strategy.md` | Strategy doc (zkPCC, Truth Mines, specified learning; §15 the prototype). |

## Own Ix worktree: `~/repos/ix.ixai-aiur`

Worktree of Ix at `4f14ec1ca`; `.lake/packages` and `Aiur/.lake/build` hard-linked from
ix.ci-merge-tests. Local additions in `Aiur/` (uncommitted):

- `IxAIStep.lean`: the `Fixed` program (`aiur_library%`), split into ~25 small functions, plus
  `Fixed::train`; host-side hints, checks and `exportWith` (packages from any source of hint
  keys). `lean_exe ixai_step` (root `IxAIStepMain.lean`).
- `IxAIGpuHost/`: the GPU trainer's host. `FFI` (`@[extern]` context over `cuda/ixai_gpu.c`),
  `Host` (gather, training loop, hint keys from the kernels' buffers, packages via `exportWith`),
  `KeysEq` (`gpuStepHintKeys_eq_stepHintKeys`, against the real `IxAIAiur.stepHintKeys`).
  `IxAIGpuMain.lean` is `lean_exe ixai_gpu`. `IxAIGpuHost/cuda` and `IxAIGpu` are symlinks into
  the pipeline; the lakefile compiles `step.cu` with nvcc (arch and toolkit as
  `crates/aiur/build.rs`) and links `libcudart_static.a` from the toolkit.
- `IxAIRefine/`: `#ixai_fixed_program` (emits named defs), `Static`, `Source`, `Check` (parity
  with `Modules.prepare`), `Core/*` (generic inversion lemmas copied from IxVMRefinement),
  `ProofGen`/`ObsGen` (generator parameterised by a `Target`), `GenFixed` (target and caps),
  `Fixed/` (generated path lemmas), `Fixed/Specs.lean` (leaf specs).
- `Tools/IxAIRefineGen.lean`: generator driver.
- Prover: `target/release/examples/prove` with
  `LD_LIBRARY_PATH=target/release/build/multi-stark-becb7b956815cc03/out`.
- Lean 4.34.1: `/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1/bin`.

## Ix internals (in `~/repos/ix.ci-merge-tests`, read-only)

Semantics and soundness:
- `Aiur/Aiur/Generic/SourceSemantics.lean`, `Observe.lean`: relational semantics `EvalFn`,
  observed `ObsFn world name args heap result heap' calls`. A `hint` evaluates to any typed
  constant, so soundness must come from the program's checks.
- `Aiur/Aiur/Audit.lean:1732`: `Optimized.Physical.Prepared.native_heap_sound_observed`: STARK
  acceptance implies `ObsFn` of the source, generic over program and entry.
- `Aiur/Aiur/Modules/Link.lean` (`Modules.prepare` gives a `Generic.Source`),
  `Modules/Correctness.lean` (execution to semantics), `Modules/Emit.lean` (`emitProgram`).
- `Aiur/Aiur/Library/*/Correctness.lean`: hand-written field models, not tied to the source.

Refinement precedent:
- `IxVM/IxVM/Elab.lean` (`#ixvm_program`), `ObsGen.lean` and `ProofGen.lean` (path-lemma
  generator, hard-coded to IxVM), `IxVMRefinement/Obs/*` (generated), `IxVMRefinement/Core/`
  (generic lemmas, per-function specs), `Ix/IxVM/Refinement/Statement.lean` (the IxVM↔IxC
  refinement statement).

Aggregation and claims:
- `Ix/Aggr/Protocol.lean:17-38` and `crates/aggregate-controller/src/protocol.rs`: `ChildKind` is
  `ixvm | aggr`; `allowedBlob` hashes exactly the IxVM and self verifying keys.
- `Ix/Claim.lean:215-232`: claim kinds `eval | check | checkEnv | reveal | contains | catalog |
  resource | binding`. `docs/eval-claims.md`.
- `crates/stark-verifier/src/lib.rs:131`: verification over an arbitrary key.
- `crates/proof-compression` (root stage keyed by an Aiur vk), `Ix/Shard/Manifest.lean` (`.ixes`
  format: magic 8 B, u128, u32 count, per shard id/heartbeats/own/ingress, optional assumption
  root, blocks, foreign blocks, then tree, peaks, records).
- Kernel roles: `IxC/Kernel/Key.lean:68` (`Role`, closed), `IxVM/IxVM/Source/KernelNatPrim.lean`.

## Ix CLI notes

- `ix compile F.lean --local --no-build --out F.ixe`; `addr-of --ixe F.ixe Name`.
- Eval claims need `--binding` from `prove-binding`, and outputs in kernel normal form
  (`nat_lit`, `Int.ofNat`/`Int.negSucc`, explicit `@List.cons T`).
- `ix check` runs IxVM out of circuit and checks the whole dependency closure (so timings of a
  composite theorem include its parts).
- `ix shard F.ixe --shards N` partitions by static heartbeat estimates, which miss kernel
  `decide` cost: heavy evaluation theorems cluster. Decode `.ixes` and map addresses with
  `addr-of` to see what landed where.
- `ix prove --ixes … --shard k`, `--aggregate --aggr-artifact …`, `--exec-only` (audit splits
  without proving), `--report`, `--out-ixes`.
- Compression: `export_root expected|extract`, then `ladder.sh` (the compression pipeline) gives a 584-byte
  PLONK proof (864 B Solidity). The wrapper fits roots up to ~5.46 MB.

## External references

Proof-carrying code and verifiable compute:
- Necula, *Proof-Carrying Code* (POPL 1997).
- EigenAI, arXiv 2602.00182 (deterministic verifiable inference).
- TypeSafe Jev, Tinfoil, Anthropic FlashProve, Attestable, OpenAI and Gemini decision APIs, the
  NEA neolab article: product landscape, summarised in the strategy doc.

Reinforcement learning:
- Reward hacking in RLVR: arXiv 2604.15149 (LLMs gaming verifiers), arXiv 2602.01103,
  emergentmind.com/topics/reward-hacking-in-reinforcement-learning-with-verifiable-rewards-rlvr,
  budgeted strong-verifier audits in GRPO (deeplearn.org/arxiv/857340).
- GRPO and group-relative REINFORCE as off-policy: arXiv 2509.24203.
- Baselines for contextual bandits: arXiv 2405.05736.
- Reproducible RL: verl.readthedocs.io/en/latest/advance/determinism.html, vLLM/vime
  reproducibility docs, Thinking Machines on batch-invariant kernels, arXiv 2511.17826
  (deterministic inference across tensor-parallel sizes).

Lean AI-proving tooling (surveyed 2026-11-18; read-only clones of lean-beam, Pantograph and
kimina-lean-server in `~/repos/clones/lean-ai/`):
- leanprover-community/repl: JSON `{cmd, env}` → sorries with `proofState`; `{tactic,
  proofState}` → goals; `allTactics` traces. The protocol behind Kimina, DeepSeek, Goedel and
  Numina RL stacks.
- Pantograph (github.com/lenianiva/Pantograph, `doc/repl.md`): `goal.start/tactic/continue`,
  `draft` (sorries to goals), `goal.subsume` (transposition), `goal.save` without the environment,
  `frontend.process` for traces; cooperative ms timeouts.
- lean-beam (github.com/leanprover/lean-beam): FRO agent interface; LSP plugin + broker, CLI and
  MCP; `runAt` speculative tactics with handles, `todo`, `sync`, `save`; explicitly not a proof
  confirmation, which is Ix's gap to fill.
- Kimina Lean Server (github.com/project-numina/kimina-lean-server): FastAPI over the REPL;
  `/verify`; Kimina RL = GRPO on verl, binary verified reward plus format gates, failed rollouts as
  error-fix samples (huggingface.co/blog/AI-MO/kimina-prover-rl). NuminaMath-LEAN (Apache-2.0).
- AXLE (axle.axiommath.ai/v1/docs, github.com/AxiomMath/axiom-lean-engine, MIT client):
  `verify_proof`, `extract_proof_states`, `theorem2sorry`, `have2lemma`, `normalize`, …;
  environments named by Lean version only; `unfolded_type_hash`. Data: AxiomMath/Putnam2025,
  IMO2026 (MIT).
- Math Inc: LeanParanoia (github.com/math-inc/LeanParanoia): exploit classes (sorry, axioms,
  `extern`, `implemented_by`, `csimp`, `native_decide`, constructor/recursor integrity,
  lean4checker replay); a test suite for IxVM's acceptance policy. `strongpnt` has no licence.
- Harmonic Aristotle: closed paid API; nothing to adopt.
- `lake comparator` / `lake check` (core since Lean 4.35.0): the FRO trusted-judge design.
- Lane (github.com/argumentcomputer/lane, Argument, Lean 4.34.1; clone
  `~/repos/clones/lean-ai/lane`): parallel agent proving workbench. One server per repo, logical
  lanes over one checkout and build, delegated per-lane worker tokens, in-process `prove`,
  `prove-session`, `verify --affected`, declaration-aware merge, journaled `submit`. No Ix,
  addresses or sandbox. Fit with `ixvc` and the agent plan: `lane.md`.
- Goedel-Prover-V2 (self-correction from compiler errors, expert iteration), DeepSeek-Prover-V2
  (GRPO), LeanDojo-v2 / ReProver (premise retrieval with hard negatives).

Lean libraries:
- Zhang, *Towards Formalizing Reinforcement Learning Theory*, arXiv 2511.03618;
  github.com/ShangtongZhang/rl-theory-in-lean (Q-learning and linear TD convergence, Mathlib).
- MDPLib: reservoir.lean-lang.org/@formalproofs/mdplib (tabular, robust, risk-averse MDPs).
- FloatLib (IEEE floats in Lean), Mathlib, Blake3 (Lean bindings; `Blake3.C.hash`,
  `Blake3.Pure.digest`).

## GPU training (surveyed 2026-11-18)

- TorchLean (lean-dojo.github.io/TorchLean, MIT, arXiv 2602.22631): specify, run and verify neural
  networks in Lean 4; opt-in CUDA via FFI, explicitly not a trusted proof boundary.
- lean4-mlir (github.com/brettkoonce/lean4-mlir): Lean → StableHLO MLIR → IREE (CUDA HAL).
- Hesper (reservoir.lean-lang.org/@Verilean/Hesper): verified GPU programming over WebGPU.
- NVIDIA CCCL/CUB determinism (nvidia.github.io/cccl/unstable/cccl/determinism.html): integer
  addition is exactly associative, so integer reductions reproduce across runs and GPU
  architectures; float `gpu_to_gpu` mode costs ~20–30%.
- RepDL (arXiv 2510.09180, microsoft/RepDL): bitwise-reproducible float training.
- Transformer Engine MXFP8 (docs.nvidia.com/deeplearning/transformer-engine-releases): 32-element
  blocks, E8M0 scales; documented for SM 10.0/10.3.
- llm.c (github.com/karpathy/llm.c): minimal C/CUDA training template.
- Ix CUDA already present: `crates/aiur/cuda/population.cu` (trace population),
  `crates/aiur-tracegen/src/cuda.rs` (circuits compiled to CUDA row writers),
  `crates/proof-compression/cuda/` (KZG, PLONK). Execution itself runs on the host.
- `ixai formats` (`IxAI/Formats.lean`, `Arith.block`): the numeric format comparison harness.

## Content-addressed version control

- Unison (unison-lang.org): definitions addressed by 512-bit SHA3 of the name-free syntax tree
  (`docs/language-reference/hashes`: cycles `#x.n`, constructors `#x#c`, builtins `##n`); codebase
  in SQLite, text is a view; namespaces as immutable `Name → Hash` maps; causal history nodes hashed
  with parents; edits keyed by hash, classified Same/Subtype/Different
  (github.com/unisonweb/unison/blob/trunk/docs/codebase-editor-design.markdown); type-preserving
  updates propagate, others go to a scratch file and `todo` frontier (`blog/new-update-process`);
  projects/branches/three-way merge, conflicts only on same-definition edits
  (`docs/usage-topics/workflow-how-tos/resolve-conflicts-projects`); `lib` namespace for
  dependencies; Unison Cloud ships computations by hash (`forkAt`); 1.0 (Nov 2025) adds an MCP
  server for agents (`unison-1-0`).
- Anthropic Scion (anthropic.com/research/redesigning-source-control): server-centric, changesets
  in a WAL with content-addressed blobs, server-side merges, ref CAS on one Spanner row, metadata
  APIs separate from lazy content fetch.
- OpenAI Pando (openai.com/index/scaling-git-at-openai): Git protocol kept, backend rebuilt for
  agent-scale load.
- Jujutsu: conflicts as first-class committed data.
- Ix pieces: `Ix/Claim.lean` (`checkEnv`, `catalog` aggregating `checkEnv` under a Merkle root,
  `contains`, `reveal`), `~/.ix/store`, `~/.ix/cache` (shard proofs reused by address).
- Unison Cloud (open source, MIT, 2026-10; unison-lang.org/blog/unison-cloud-open-source). Read-only
  clones in `~/repos/clones/unison/` (`cloud-api` Haskell control plane, `unison-cloud-ui` Elm,
  `byoc` Nix/EC2/EKS template). Nimbus worker and client are Unison code on Share
  (`@unison/nimbus`, `@unison/cloud`), readable via `api.unison-lang.org/users/unison/projects/
  nimbus/branches/main/{readme,browse,definitions/by-name/<name>,find?query=}`.
  - cloud-api: Postgres state, S3 service blobs keyed by SHA-256 of serialized bytes
    (`src/Cloud/Deployment/Impl.hs`), Consul discovery, synchronous acknowledged cache
    invalidation to nimbus over per-node websockets (`src/Cloud/Web/Cluster/Impl.hs`).
  - nimbus: `remote.run` handles the `Remote` ability; `thread.detachRemote` →
    `sendForkRequestTcp` with `Thunk.create = serialize_v4 (Value.value t)` (code travels inside
    the serialized value; `Value.deserializeAndLoad` on receipt); shuffle-sharded peers from a
    consul-template config; remote results are trusted.

## Decision-model and task benchmarks (surveyed 2026-11-18)

- Jev 1.13 vs Claude Opus 5 on Banking77 (openrouter.ai/blog/insights/jev-vs-claude-opus-5-classification):
  3,080 utterances, 77 intents, one-line criteria per label written from label names; Opus zero-shot,
  temperature 0, strict JSON enum, cached system prompt; 8 concurrent requests. Metrics: accuracy with
  bootstrap CIs and a paired-bootstrap gap, macro-F1, invalid responses, p50/p95/p99 latency, cost per
  1,000, confidence-routing cascade. Jev 81.0% vs Opus 84.4% (gap 2.3–4.4 points), p50 175 ms vs 2,266 ms,
  $0.11 vs $2.42 per 1,000.
- Decision models vs LLMs buyer's guide (beri.net): decision models trail the best LLM by a median 11.6
  macro-F1 points at ~44× lower cost; Jev ECE 0.157 vs best frontier 0.066, recalibration 3.3× better;
  per-question calibration fits on a few hundred held-out labels; cascades match the LLM at 1/4–1/2 cost.
- Cost-aware model selection for text classification (arXiv 2602.06370): fine-tuned encoders match or
  beat prompted LLMs at 1–2 orders of magnitude lower cost and latency.
- Calibrated routing (arXiv 2605.18796): isotonic calibration of confidence for cascades.
- Premise selection: LeanDojo/ReProver (arXiv 2306.15626) random split R@1 13.5%, R@10 38.4% (BM25 6.7%,
  17.2%); novel_premises R@1 9.1% (BM25 5.9%). LeanHammer/LeanPremise (arXiv 2506.07477, ICLR 2026)
  recall@16 61.1%, @32 71.9% on Mathlib (random forest 22.1% @16). Text+structure selector arXiv
  2510.23637. No published GPT/Claude premise-ranking baselines found.
- Propositional logic: LogicPrpBank (truth-value classification, macro-F1; small fine-tuned models beat
  large ones), SATBench (arXiv 2505.14615; o4-mini 65% on hard UNSAT vs 50% chance), LogicSkills (arXiv
  2602.06533; ~92% on FO2 validity), 2-SAT robustness under reordering/renaming (arXiv 2602.12665).
  Label imbalance makes accuracy misleading; report balanced metrics and trivial baselines.
