# Project Review (2026-11-19)

The project now verifies real training proofs against consumer-specified inputs. The most important open question is whether a package marked `PROVED` connects the same model across the training proof, evaluation card and deployment theorems.

### Verification evidence

- The consumer supplies the expected trajectory job. The step-chain verifier requires every scheduled proof, checks its public inputs and outputs, and reports missing steps as `INCOMPLETE`. Prover reports have a separate diagnostic command. Merkle v2 binds the leaf count and checks path shape and index. Curation rejects items with unresolved proof dependencies or axiom names. The reward harness parses a single term before isolated elaboration. [Verification contract](verification.md)
- Independent review checks passed for `IxAITest`, `IxAICoreTest` and `IxAIVerifyTest`. The saved default 600-step trajectory verified. The saved 219,790,547-byte `Fixed::train` STARK (`fb0a1af2…`) also verified against the saved 228,332 input words and all 331 packaged output weights. The startup probes for `ixai` and `ixai-verify` each took about 40 ms. [Saved STARK evidence](../.truthmines/aiur/train/README)
- The project's separate full-package run reports `PROVED` in 142 s, including the 600 step proofs and eight IxVM claims. The consumer classifies its supported compressed `aiur-exec` route as `attested`. It checks the root claim and proof-file digest, while PLONK verification occurred during production. The 142 s and the compression timings below are recorded project measurements. [Full-package run](verification.md#the-full-run-2026-11-19)

## 1. Overall Direction

### Strengths

- **Clear, defensible thesis:** "Specified learning" — pure, kernel-evaluable training functions (`train spec config`), safety gates proved for *all* weight settings (`act_publish_sound`, `outcome_publish_sound`), and separating kernel proofs (specs, theorems, cheap cards) from purpose-built Aiur circuits (hot numerics) bridged by refinement theorems (`docs/offload.md`).
- **Real end-to-end engineering:** Tiny/small models are compressed to 584-byte PLONK proofs, the 600-step model has verified Aiur proofs, a bit-exact CUDA + int8 tensor-core trainer exists, full-Mathlib (262k theorems) premise curation runs in ~28 s with proved hash-set equivalences, and a dedicated consumer verifier (`ixai-verify`) checks the training evidence. Section 3 covers the remaining model and theorem bindings.
- **Honest empirical discipline:** Baselines and negative results are reported transparently (`order-basic` rerank-30 gap vs Opus, `prop-xhard` form-only collapse, deeper-formula shift), and every trusted assumption is printed with verifier outcomes.

### Job identity before training

`ixai-verify commit` currently resolves the card and deployment theorem addresses from an environment that already contains the trained weights and results. That commitment supports later audits of a known run. For outsourced training, the consumer must be able to issue a job **before the output exists**. Commit to the specification, dataset, configuration, assumption policy, approved programs and claim templates. Have the receipt supply the canonical model commitment and proofs instantiating those templates for that model. An acceptance test should create the job before training, then verify the returned training, evaluation and deployment claims using that original job. [Commitment builder](../IxaiVerify.lean) · [Result declarations](../Ixai.lean)

### Strategic Risks & Scope Creep

1. **Sprawling roadmap relative to M1/M2 proof-of-value.** Within one repo (17.2k LOC) and `docs/`, there are ~7 parallel tracks: M1 (`aiurExec` / `ChildKind.aiur` / `FixedTree`), M2 (Mathlib premise selection), M2b (STLC / `prop-hard` / `prop-xhard`), M3 (certified RL), CUDA tensor cores, plus design docs for `ixvc`, `lane` integration, learned kernel hints, definition-equivalence demos, and typed program synthesis. Before starting new tracks (`ixvc`, kernel hints, def-eq), two core questions need closure:
   - **M1:** Land the Ix protocol decision (`ChildKind.aiur` / `aiurExec`) or standardize the single-proof tree route (`FixedTree::train_tree` + `train_tree_sound`) so full training + environment is one certificate.
   - **M2:** As `docs/plan.md` notes, the key milestone is *whether a certified model improves actual proof-search throughput* — and the current bag-of-constants/names bilinear scorer has plateaued (0.381 vs 0.385 MRR even with 190× more Mathlib data). Pushing M2 requires extracting real statement structure (or an Ixon encoder) and building the fixed-budget proof-search harness rather than tuning more pair heuristics.
2. **Toy-model arithmetic debt (`Fx` floor bias) is distorting ML conclusions.** `IxAICore.Fx` uses floor division (`>>> 8`, rounding toward $-\infty$) on every dot product and weight update. As noted in `docs/plan.md` (lines 516–517, 706–709), this biases pre-activations downward, kills ReLUs on longer runs, and causes severe seed fragility (2/5 seeds collapsing to majority on `prop-xhard`). Before attributing weak accuracy to model capacity on M2b/M3, newer specs should use round-to-nearest (as `Scorer.lean` already adopted via `nearest := true`) and `Fx16`.

---

## 2. Project Structure & Hygiene

1. **No version control (`git`) on a 17k-LOC, 65 GB workspace.**
   The directory has a `.gitignore` but is not a git repository (`fatal: not a git repository`). With multiple forks/worktrees (`ix.ixai-aiur`, `ix.ci-merge-tests`, `forks/ix-aiurexec`) and fast iteration, having no commit history or diffable state for the pipeline itself is a major operational risk.
2. **Disk & generated-artifact sprawl (65 GB total).**
   - `.truthmines` (47 GB), `.lake` (8.9 GB), `ix/` (8.8 GB), `.cache` (449 MB).
   - Generated `.lean`, `.ixe`, `.ixes`, `.log`, `.proof`, `.ixa`, and `reward-work/` files sit directly inside `ix/bundle/` (47+ files) and `ix/aiur/`, and `shell/__pycache__/` is present. Moving generated outputs under a dedicated build/output dir (e.g., `.truthmines/gen/` or `build/`) would keep source directories clean.
3. **Coexistence of legacy mock layer (`IxAI/`) and real core (`IxAICore/`).**
   - `IxAI/` still carries the early toy-kernel mock (`Kernel.lean`, `Store.lean`, `Cert.lean`, `Task.lean`, `Orchestrate.lean`, `Training.lean`, `Decision.lean`, `Examples.lean`) alongside shared utilities (`Hash.lean`, `Merkle.lean`, `Literal.lean`, `TrainClaim.lean`) that `IxAIVerify` actually depends on.
   - Splitting shared crypto/encoding primitives (`Hash`, `Merkle`, `Literal`) out of the toy mock-up into a small `IxAICommon` (or moving `IxAI` mock modules into `IxAIMock/`) would clarify the real dependency graph.
4. **Hardcoded user/machine paths.**
   Absolute `/home/sam/repos/...` and `/nix/store/...` paths are hardcoded in `IxAIVerify/Tools.lean:20-31`, `Ixai.lean:352,454`, `ix/ixw:14-34`, and `ix/heavy.sh:13`. Notably, `ixai reward` writes to hardcoded `/home/sam/repos/ix-ai-pipeline/.truthmines/rewards.tsv` regardless of the `bundle` argument.
5. **Monolithic CLI (`Ixai.lean`, 820 LOC) and duplicated helpers.**
   `Ixai.lean` mixes code generation (`writeClaims`, `writeChain`, `writeCertifiedChunked`), reward sandboxing, package assembly, diagnostics, RL, format sweeps, and benchmark dispatch; `flag`/`flagValue` and `cmdTrajectory`/`check` are duplicated between `Ixai.lean:71-88` and `IxaiVerify.lean:25-97`.
6. **Documentation drift inside `README.md` and `docs/`.**
   - `README.md:12` reports `train_refines`/`train_sound_eq`/`step_sound_deployed` as proved, while `README.md:194-199` says refinement is still "not a general proof ... next steps", and `README.md:254-383` still appends the full early mock-up README ("Not yet evaluable by a kernel", "Next steps: 1. Back ProofSystem with Ix").
   - `docs/rl.md:43` still says "Written, not yet elaborated" despite full RL results in `docs/plan.md:325-335`.
   - `docs/plan.md:718-720` still cites the 100 s `ixai` startup delay that `docs/plan.md:90-91` reports as fixed (`104.6 s → 0.03 s`).

---

## 3. Correctness, Soundness & Security Findings

The formal proofs themselves are clean — zero `sorry`, zero custom `axiom`, zero `native_decide` across all Lean libraries (the only `unsafe`/`@[implemented_by]` is `submissionEnv` in `IxAIVerify/Submission.lean:50-57` to enable parser initializers for `Init`). The issues are at the **imperative, FFI, and verification boundaries**:

### High / Security & Soundness Boundary

1. **Bind the card and gate theorems to the authenticated model (P1).** The verifier authenticates the compiled `.ixe`, then looks for the weights and config in a separate Lean source file chosen by the receipt. A substring check cannot establish the value of `trainedOutput` in the compiled environment. The verifier prints source-to-environment correspondence as a hypothesis. Read the canonical model commitment from the authenticated Ixon declaration, or verify an `Eval` claim connecting that declaration to the submitted weights. Use the same commitment for training, the card and the gate. [Package verifier](../IxAIVerify/Package.lean)
2. **Verify the exact Ix claim (P1).** `ixVerify` searches a human-readable `ok:` line for the proof and declaration addresses. It does not check the process exit status or compare the kind, subject, context and assumptions of the claim. Those fields distinguish an unconditional check of the expected theorem from a check under different assumptions. Construct the expected `Check` claim under the consumer's policy and require both successful verification and equality of its canonical digest or decoded fields. [Ix adapter](../IxAIVerify/Package.lean)
3. **Use one canonical signed encoding for weights (P1).** The package hashes signed integers after a parameter-count check. The Rust `verify_claim` adapter reads those integers modulo the Goldilocks prime, so distinct integer encodings can have different model digests and identical proof inputs. The circuit's range checks constrain the field value. The consumer must also validate the signed range required by the refinement theorem on every intermediate and final model before hashing or encoding the words. [Model digest](../IxAIVerify/Spec.lean) · [Training routes](../IxAIVerify/Aiur.lean)
4. **Inline PTX assembly missing early-clobber in `add_wide`** (`gpu/cuda/step.cu:70-77`):
   ```cpp
   asm("add.cc.u64 %0, %2, %4;\n\taddc.u64 %1, %3, %5;"
       : "=l"(s.lo), "=l"(s.hi)
       : "l"(a.lo), "l"(a.hi), "l"(b.lo), "l"(b.hi));
   ```
   Output `"=l"(s.lo)` lacks the early-clobber modifier `"=&l"`. Because `%0` is written before `%3` (`a.hi`) and `%5` (`b.hi`) are read by `addc.u64`, NVCC is allowed to alias `s.lo` with `a.hi`/`b.hi` whenever `a.hi`/`b.hi` are not live past the `asm` (currently only masked because line 75 reads `a.hi`/`b.hi` for overflow checking). Change to `"=&l"(s.lo)`.
5. **Rust panic treated as `.unavailable` (`INCOMPLETE`) instead of `.refused` (`REJECTED`)** (`IxAIVerify/Aiur.lean:90-93`):
   `notRun` checks for `"panicked at"` in stderr. If a crafted/corrupted proof causes `verify_claim` to panic during deserialization or verification, the route becomes `INCOMPLETE` rather than `REJECTED` (and if another route in the receipt is valid, `verifyPackage` returns `PROVED` without rejecting the corrupted route).
6. **Sandbox read-exposes the entire host filesystem** (`IxAIVerify/Sandbox.lean:37-43`):
   `--ro-bind / /` mounts everything read-only (home directory, SSH keys, benchmark answer keys outside `.truthmines`, sibling repos), hiding only `.truthmines`. Although `--unshare-all` cuts network access, an elaborating submission can read any host file and exfiltrate it into compiler diagnostics/stdout or files in `writable`. Mount only the minimal required paths (`/nix`, `/usr`, `/lib*`, `/bin`, `bundle`, `work`) instead of `/`.
   The process also inherits the caller's environment. Give each worker a minimal environment and mount only its toolchain, declared inputs and a fresh job directory. `rewardSubmit` uses the same `Reward_{task}_submission` directory for concurrent submissions to one task, so their compile and check stages can observe different artifacts. Allocate a unique directory per submission and check that submission's immutable output. [Sandbox arguments](../IxAIVerify/Sandbox.lean) · [Reward submission](../Ixai.lean)
7. **Reward harness does not verify `IxAIReward.goal`'s compiled type in `.ixe` and has a toolchain parser mismatch** (`Ixai.lean:359-414`):
   `checkSubmission` parses `proof` in Lean 4.34.0 `Init`, whereas `ixw compile` compiles `candidateSource` under Lean 4.34.1 with `import IxAICore`. After compiling, `rewardOne` checks `addr-of IxAIReward.target` and runs `check-lean --consts IxAIReward.goal`, without directly checking in `.ixe` that `IxAIReward.goal`'s type is `IxAIReward.target`. Checking the goal's type directly in `.ixe` removes parser consistency from the TCB.

### Medium / Functional Bugs

8. **The triage validity theorem needs an explicit input domain (P2).** `Formula.atom` accepts any `Nat`, while `Formula.valid` checks the eight assignments to atoms 0–2. Lean returned `true` for `valid (P3 → P0)`, but evaluating that formula with only P3 true returned `false`. The training generator stays within three atoms. The theorem `act_publish_sound` correctly proves `f.valid = true`; extending that conclusion to truth under every admissible assignment requires a domain guarantee at the public gate. Use `Fin 3` or check the bound at ingress, then prove the semantic statement for accepted inputs. [Formula domain](../IxAICore/Formula.lean) · [Gate theorem](../IxAICore/Triage.lean)
9. **Vacuous `all` bug turns `PREDICTED` into `INCOMPLETE` on unknown route kinds** (`IxAIVerify/Package.lean:277-290`):
   Line 277 states unimplemented route kinds are ignored, and line 281 filters them out of `implemented`. When `routes` is non-empty but contains *only* unknown kinds, `implemented` is `#[]`, so `implemented.all (·.status == .incomplete)` on line 289 evaluates vacuously to `true` and sets `r.incomplete := true`, changing the outcome from `PREDICTED` to `INCOMPLETE`. Guard with `!implemented.isEmpty && implemented.all ...`.
10. **`stepName` silently collides at step ≥ 1000** (`IxAIVerify/Aiur.lean:55`):
   `s!"step-{(toString (1000 + i)).drop 1}"` maps `i = 1000` to `"step-000"`, colliding with step 0. Use explicit zero-padding for widths ≥ 3 without dropping digits.
11. **`cudaGetLastError()` clears the CUDA error before `ixai_gpu_error()` reads it** (`gpu/cuda/step.cu:496,624`):
   Line 624 calls `cudaGetLastError() != cudaSuccess`, which resets CUDA's error state to `cudaSuccess`, so when `gpu/cuda/ixai_gpu.c:63` calls `ixai_gpu_error()`, it reports `"no error"`. Use `cudaPeekAtLastError()` on line 624 (or store the last `cudaError_t` in `IxaiGpu`).
12. **Silent `Int.toNat` truncation and loose parsing in trajectory verification** (`IxAIVerify/Trajectory.lean:41,98-100,133-143`):
   Negative ints in headers (`seed`, `hidden`, `epochs`, `batch`), batch indices, or IEEE wire bits silently turn into `0` via `Int.toNat`; `parseLinks` doesn't enforce alternating `"step "` / `"w "` prefixes or exact parameter counts before `MLP.ofList`.
13. **Panics and error-handling gaps:**
    - `String.fromUTF8! cBytes` in `IxAIVerify/Package.lean:216` panics on non-UTF8 commitment files (use `String.fromUTF8?`).
    - `k.toNat!`, `String.toNat!`, `s.toInt!` in `Ixai.lean:803-813` crash on invalid CLI args.
    - `ix/heavy.sh` runs under `set -e` (`ix/heavy.sh:9`), so if `"$@"` fails on line 71, the script exits immediately and never writes the `end ($status)` log line on line 73.
14. **Minor spec/math edge cases:**
    - `probabilities` in `IxAICore/Decision.lean:91-95` clamps logits to `[0, 1]` before normalizing, discarding margin above `1.0` (e.g., `[256, 512]` becomes `[128, 128]`, so `argmax` and `confidence` disagree).
    - `chunk 0` in `IxAICore/Decision.lean:121-123` yields `fuel` empty lists instead of guarding `max k 1` (as `Scorer.lean` does).
    - `Digest.ofHex?` in `IxAI/Hash.lean:43-58` rejects uppercase hex `A-F`, and `Digest` doesn't enforce 32-byte length in its type while `Enc Digest` omits a length prefix.
    - Unsynchronized `static` lazy initialization in `gpu/cuda/ixai_gpu.c:50-53,83-92` (use `pthread_once` if ever called from concurrent Lean tasks).

---

## 4. Performance & Scalability

1. **Repeated key setup in `verifyStepRoute`** (`IxAIVerify/Aiur.lean:96-148`):
   - Currently spawns `verify_claim` **600 separate times**, recompiling the verifying key from `approved-*.exec.ixa` on every invocation (~89 s wall across 24 cores, vs ~21 ms per proof = ~12.6 s single-threaded, <1 s parallel). Adding a `--batch` mode to `verify_claim` that compiles the key once and verifies a manifest of `(proof, args, out)` tuples could amortize key setup. The proposed 1–2 s wall time is an estimate. Benchmark all 600 proofs with the same storage and hardware to establish the gain.
   - `runPool` (`IxAIVerify/Tools.lean:53-64`) executes in lockstep waves of 24 dedicated OS threads (waiting for the slowest task in each wave before launching the next wave, creating 600 threads total) and leaves scratch `.args`/`.out` files behind in `/tmp/ixai-verify-*`.
2. **CUDA GPU trainer stalls and launch overhead** (`gpu/cuda/step.cu:445-639`):
   - `limb_top` (`gpu/cuda/step.cu:445-454`) runs `cudaMemcpy(..., DeviceToHost)` **synchronously twice per tensor-core GEMM** (up to 10 host-device sync stalls per SGD step). Using pinned host buffers + async streams or bounding limb count from the spec's known weight/input bounds (e.g., `|w| < 4320` already fits 2 limbs without scanning) would eliminate most stalls.
   - `ixai_gpu_step` launches **17+ kernels per step** (5 standalone `transpose_kernel`s + 5 GEMMs + 5 epilogues + 2 bias updates). Fusing epilogues/transposes or capturing a CUDA Graph for fixed shapes would cut launch overhead significantly for small/medium models.
   - `ixai_gpu_keys` (`gpu/cuda/step.cu:630-639`) issues **10 separate synchronous `cudaMemcpy` calls** per step. Allocating the 10 key buffers as slices of one contiguous device buffer turns this into a single bulk transfer (and allows `cudaMemcpyAsync` overlapped with host witness packing).
3. **Full-Mathlib premise scorer hotspots** (`IxAIData/Scorer.lean`):
   - `Pool.of` (`IxAIData/Scorer.lean:802-808`) scans every theorem in `it.thm.module` to build `own`, and then does linear `own.contains j` inside `excl`; `Pool.inModules` (`IxAIData/Scorer.lean:813-818`) does linear `!p.excl.contains j`. On 184k theorems, binary-searching `decl` (when sorted within a module) and using binary search on sorted `own`/`excl` removes the per-module quadratic component.
   - `PreparedLib.of` (`IxAIData/Scorer.lean:728`) pushes onto arrays inside a `HashMap` (`m.insert p.addr ((m.getD p.addr #[]).push i)`), copying on shared references — the exact pattern avoided on line 277 with lists.
   - `Refs.of` (`IxAIData/Scorer.lean:299`) uses $O(k^2)$ `acc ++ [x]` in `dedupNat'`.
   - `parMap` (`IxAIData/Scorer.lean:821-825`) always spawns 96 tasks regardless of `xs.size` (clamp chunks to `min chunks xs.size`).
4. **Proving bottleneck for M1:**
   The single-execution `FixedTree::train_tree` route produced a 584-byte training certificate in 251 s and 315 s on a repeat. The 30-block route took 509 s and the 600-step tree took over 40 min. Finishing the tree route requires `train_tree_sound`, the BLAKE3 refinement and consumer verification of the terminal PLONK proof against a pinned key and exact public statement. The combined training-and-environment prototype also faces a separate bottleneck. Compiling the 36,557-constant environment closure timed out at 45 min. Track that cost independently of compression. [Project measurements](plan.md) · [Verification routes](verification.md#training-routes)
5. **Separate prediction timing from reference labelling (P2).** The timed paths call `predOf` and `certPredOf`, which construct records containing the result of `targetOf`. The generated code calls the reference labeller inside prediction, even though the timer consumes only confidence. Time a function returning the model answer, confidence and certification status. Join precomputed reference labels afterward. Rerun the timing comparison before using the published 1.7 ms model and 3.8 ms hybrid figures as deployment costs. [Prediction helpers](../IxAIBench/Typed.lean) · [Timing loop](../IxAIBench/TypedXhard.lean)
6. **Measure the learned contribution on unresolved cases.** On 1,000 `prop-xhard` instances the hybrid reached 91.7% accuracy. The solver certified 232 answers. On the remaining 768 the model's 89.1% accuracy matches a rule using the formula's outer form alone (685/768). Report that rule alongside the model and measure additional checked decisions or completed proofs per second at the same solver budget. [Benchmark results](plan.md)

---

## 5. Top Prioritized Next Actions

1. **Close the package acceptance contract.** Bind canonical weights and config through authenticated Ixon, require exact Ix claims under the consumer's policy, and support a job commitment issued before training. Use one returned model identity across training, evaluation and deployment.
2. **Harden the gate, reward workers and adapters.** Enforce the formula's atom domain. Restrict worker reads and environment, isolate concurrent submissions and check the goal's compiled type. Address CUDA error reporting and register constraints, route classification, step numbering and strict input parsing as detailed in §3.
3. **Finish independent verification of the compressed training and environment result (M1).** Bind a standalone terminal PLONK check to the pinned key and expected statement. Complete the tree refinement or the refinement theorem for the deployed `train_block` chain, and resolve compilation of the environment child.
4. **Benchmark verification and learning separately.** Reuse one verifying key per batch of step proofs and measure the wall time. Remove reference labelling from prediction timings. For M2/M2b, measure completed proofs or checked decisions per fixed budget against solver-only and heuristic baselines before expanding the roadmap.
5. **Make the review and builds reproducible.** Establish version control for pipeline sources, separate generated artifacts and mock code from shared libraries, replace hardcoded paths, and reconcile the stale README and planning sections identified in §2.
