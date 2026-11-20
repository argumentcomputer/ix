# Verification: the acceptance contract

What a consumer of a trained model checks, with what, and what it still assumes. The verifier is
`ixai-verify` (`IxaiVerify.lean`), a small executable that links the specification (`IxAICore`)
and the verification layer (`IxAIVerify`) only: no benchmarks, datasets, GPU code or provers.

## Layers

| Layer | Modules | Role |
|---|---|---|
| Specification | `IxAICore` | Pure, kernel-evaluable definitions: models, `train`, `card`, the gate, safety theorems. |
| Verification | `IxAIVerify`, the shared primitives of `IxAICommon` (`Hash`, `Merkle`, `Literal`, `Paths`) and the native training claims of `IxAI` (`TrainClaim`, `Float`; never the toy-kernel mock-up) | Encodings, expected claims, job commitments, proof checking, composition. Depends on the specification only. |
| Proving | `IxAIGpu`, `GpuExport.lean`, `ix/` scripts, the `ixai` commands that write packages, certificates and receipts | GPU training, witnesses, adapters to Aiur and Ix. |
| Experiments | `IxAIData`, `IxAIBench`, the rest of `ixai` (`IxAICli`) | Datasets, benchmarks, reports. |

`ixai` is the experiments CLI and still links everything; benchmark values are computed only when
a benchmark command runs (`TypedBench.items ()`, `trajectoryCheck ()`, and
`compiler.extract_closed false` in the modules whose closed terms would otherwise become program
initializers).

## The package

A consumer receives three things.

1. **The job** (`job.json`, format `ixai-job-commitment-v2`), issued before training from the
   specification and a config alone, and identified by its BLAKE3, which the consumer holds
   independently of the trainer. It names:
   - the specification: `IxAICore.Triage.spec` and `IxAICore.train`, by Ixon address;
   - the config, field by field and by `configDigest` (`H("job/config", fields)`);
   - the dataset: its example count and root, `merkleRootV2` over `H("job/example", inputs,
     targets)` of `(config.data Triage.spec).map Triage.spec.example`, in order;
   - the approved programs, as BLAKE3 digests of Aiur program packages: `Fixed::step`,
     `Fixed::train`, `AiurExec::aiur_exec`;
   - the claim encoding, by the digest of its text (`IxAIVerify.stepClaimEncoding`): word layout of
     models and batches, the argument order of each program, canonical signed words;
   - the claim policy: every evaluation and deployment claim is an Ix `Check` claim under one
     context (specification digest, role binding), over the standard axioms only, with no
     assumptions, validating its binding;
   - the model encoding: the Ixon addresses of `IxAICore.Model.mk`, `List.cons`, `List.nil`,
     `IxAICore.Fx.mk`, `Int.ofNat`, `Int.negSucc`, and of the gate's three actions;
   - the claim templates: the evaluation card (`cardCertified`), the gate decisions
     (`decision0..3`) and the safety theorems at the deployed model (`deployedPublishSound`,
     `deployedPublishConfident`, `deployedDeferIff`), each a statement with holes for the model
     (`trainedOutput`) and its outputs (`cardOutput`, `decisionOutput`), as the Ixon term of a
     `Prop`-valued definition in the consumer's compilation of `IxAIVerify.templateSource`;
   - optionally, the compression pipeline (`compression`): the BLAKE3 of the terminal PLONK
     verifying key (`plonkVerifyingKeyBlake3`) and of the wrapper key its statement names
     (`wrapKeyBlake3`). See [The compressed certificate](#the-compressed-certificate).
2. **The model**: one line of 331 raw fixed-point words, `w1 ‖ b1 ‖ w2 ‖ b2` row by row, each a
   canonical decimal integer (`0`, or no leading zero, no `+`, never `-0`) in `[-4096, 4320)`.
3. **The receipt** (`receipt.json`, format `ixai-receipt-v1`): where the evidence is. A list of
   training routes, each tagged by `kind`, the compiled environment (`.ixe`), and one Ix proof
   (store address) per claim template (`claim`: the template's id).

Issuing a job, before any training:

```
ixai-verify template --config full --out Template_full.lean
(cd ix/bundle && ../ixw compile Template_full.lean --local --no-build --out template_full.ixe)
ixai-verify commit --config full --template-source Template_full.lean --template-env template_full.ixe \
  --program Fixed::step=program-step.ixp --program Fixed::train=program-train.ixp \
  --program AiurExec::aiur_exec=aggregator.ixa \
  --plonk-key ix/toolchain/base/target/e2e-l3/plonk-prepared/prepared/verifying-key.bin \
  --wrap-layout ix/toolchain/base/crates/stark-verifier/compress-wrap/m16384w64-v3.layout.json \
  --out job.json
```

`commit` checks that the source is `templateSource` for the config, reads the role binding from
the template environment's header and the addresses with `ixw addr-of`, and reads each template's
term from its Ixon record. The specification digest of the policy is the pinned ix build's
(`--ix-spec` names another). `ixai package-assemble [--out DIR] [--plonk-key FILE]` writes the
trainer's side for the full run into `.truthmines/package/full` (or `DIR`); with `--plonk-key` its
`aiur-exec` route names that terminal verifying key (`plonkKey`), so a job that pins the compression
pipeline verifies the certificate instead of reporting the route attested.

### Training routes

| `kind` | Evidence | Checked here | Route status when it passes |
|---|---|---|---|
| `aiur-steps` | one `Fixed::step` STARK proof per scheduled step, and the prover's 600 intermediate models | every scheduled step present; every model canonical and in the weight range; all proofs verified by one `verify_claim --batch` process (one key, all cores) against `m_i ‖ batch_i ‖ lr → m_{i+1}`, with `m_0 = config.init`, `m_600` = the submitted model, batches from the schedule | verified |
| `aiur-train` | one `Fixed::train` STARK proof of all 600 steps | verified by `verify_claim` against `m_0 ‖ lr ‖ xs ‖ ts → model` | verified |
| `aiur-exec` | `aiurExec` root (`root-vk.bin`, `root-claims.bin`, `allowed.bin`, `out.bin`), the compression pipeline's PLONK proof and its verifying key (`plonkKey`) | `aiur_exec_check`: the root claim names the approved programs' keys and chains 600 executions from `m_0` over the scheduled batches to the submitted model; the PLONK proof's BLAKE3; then `aiur_plonk_verify`: the proof verifies under the job's pinned key against the statement computed here from the recompiled keys and the specification | verified when the job pins the compression pipeline; attested (claim checked, certificate not re-verified) when it does not |

Programs are never taken from a prover's package. The verifier wraps the approved program package
(checked by BLAKE3) in an execution package of its own with no arguments or hints
(`IxAIVerify.Ixon.wrapPackage`), so `verify_claim` recompiles the key from the approved program.
Claims are built from the specification (`IxAIVerify.Spec`): examples, schedule and initial weights.
No SGD step is computed; the intermediate models are the prover's and the proofs chain them.

Every model word, intermediate or final, is checked before it is hashed, encoded or compared: a
canonical decimal integer (`IxAIVerify.canonicalInt?`) in `[-4096, 4320)` (`checkModelWords`), the
range `Fixed`'s `bound` admits (`ix/aiur/FixedSoundness.lean`) and the refinement theorems read. Words
are read modulo the Goldilocks prime by the circuit, so without the range two integers congruent
modulo the prime would have one proof and two model digests. `verify_claim` refuses non-canonical
words and words outside `(-p, p)` as well.

A verifier that cannot start (binary missing, shared library not loadable), or that stops before it
reads any proof (`verify_claim --batch` prints `key ready` once its key is built; `aiur_exec_check`
prints `ok:` for each check of the evidence; `aiur_plonk_verify` prints `key ready` once the pinned
key and the Ignition anchors are loaded), leaves its route `incomplete`: that says nothing about
the evidence. Once it has started on the evidence, any failure, a panic included, rejects the route,
and a rejected route rejects the package whatever the other routes show.

Other kinds are reported as not implemented and ignored, so new evidence plugs in as a new kind:
one proof of all 600 steps on another circuit (a tree or block aggregate). Such a route needs a
program digest in the commitment's `programs` and its own claim builder in `IxAIVerify.Aiur`; the
outcome rules below do not change. The combined IxVM+Aiur certificate, whose single claim covers
environment and training, is checked by its own command (see
[One certificate for training and its environment](#one-certificate-for-training-and-its-environment)).

### Claims

The verifier reads the receipt's environment itself (`IxAIVerify.Ixon`): every blob and constant
must hash to its address, so the file needs no digest of its own. For each claim template:

- the receipt's proof is read from the Ix store and must hash to its address;
- its claim must be exactly the policy's `Check(context, T, none)` for some constant `T`: kind,
  specification digest, binding, axioms, assumptions and validator are compared byte for byte
  (`Ix.Claim.ser`), and each difference is reported;
- `T` must be a theorem of the environment whose type is the template's statement with each hole
  replaced by a closed term (`Ixon.matchTemplate`);
- `ix verify PROOF` must exit 0 and print `ok: proof PROOF verifies claim D` with `D` the BLAKE3 of
  the expected claim.

The `trainedOutput` hole must be the same constant in every claim. Its Ixon record, a safe
definition, possibly through other definitions, is read as a model literal through the committed
constructors, and must equal the submitted model: the model that training proves is the one the
card evaluates and the gate deploys. Each decision's output must be the action the native gate
computes on the submitted model. No Lean source file is read, and a record's `verified` column in
`.truthmines/index.tsv` is never read.

### Outcomes

| Outcome | Exit | When |
|---|---|---|
| `PROVED` | 0 | a training route was verified here in full, and every committed claim's proof verifies and is bound to the model |
| `PREDICTED` | 3 | every claim verifies, but no training route was verified in full (none given, or only attested): the model is checked by its evaluation only |
| `INCOMPLETE` | 4 | committed evidence is missing: a step proof, a claim proof, the environment, or a verifier that could not start (missing binary or library) or stopped before reading any proof |
| `REJECTED` | 1 | evidence contradicts the job: a proof that does not verify, a verifier that panicked or failed on the evidence, a program with another digest, a claim other than the policy's, a theorem that does not state its template, a model outside the weight range or not canonically written, a model that is not the chain's end or the claims' model; a rejected route rejects the package even when another route verified |

A missing step is never a pass: `ixai aiur-chain DIR` and `ixai-verify chain` return
`INCOMPLETE` for an empty directory or a directory of reports without proofs.

### Visible conditions

The verifier prints every hypothesis its outcome rests on. For `PROVED` through `aiur-steps`:

- the job commitment is the consumer's own;
- the approved program digests name the compilation of the Aiur programs the consumer approved;
- STARK soundness of `verify_claim` (its BLAKE3 and path are printed);
- `Fixed::step` computes `Model.step` on these words: `step_sound_deployed`, whose hypothesis
  `StepOnlyParity` is `#eval`-checked, not proved;
- compilation of `Fixed.source` to circuits is an `#eval` parity check (`IxAIRefine.Check`);
- the claim encoding is read the same way by the circuit (checker code, not a Lean definition the
  claim names);
- native evaluation of the specification (examples, schedule, `config.init`) agrees with kernel
  evaluation;
- IxVM STARK soundness for the claims; that the claim templates mean what the consumer intends
  (the consumer compiled them); that this verifier reads Ixon as Ix writes it.

`aiur-exec` adds: the `aiurExec` aggregator is an unproven prototype (fork `ix-aiurexec`), and
either (no compression pin in the job) the root STARK is bound only by a PLONK certificate verified
at proving time, with STARK/PLONK soundness, or (with the pin) the assumptions of the terminal
check listed below.

## The compressed certificate

Ix's compression pipeline turns the `aiurExec` root (STARK proof, key, claim) into one 584-byte
gnark PLONK proof over BN254: root → `CompressWrap` (Goldilocks FRI) → `CompressGL` (FRI verifier
over BN254, packed-SHPLONK KZG) → `CompressNarrowFixed` (KZG) → `CompressFinalNarrow` (terminal
relation) → PLONK. Its only public inputs are the two little-endian 128-bit halves of a 32-byte
statement `S`. The verifier computes `S` itself (`IxAIVerify.Compression`) and never reads it, or
anything it is built from, from the certificate or from the trainer's files:

| Part | Value | Source |
|---|---|---|
| root key digest `K` | `BLAKE3` of the aggregator's batch key | recompiled from the approved aggregator package (`aiur_exec_check`, which prints `key: aggregator BLAKE3 entry N` before it reads the root directory, or `--keys` alone) |
| identity (80 bytes) | `BLAKE3(program key) ‖ u64 entry ‖ K ‖ u64 entry` | program key recompiled from the approved program package, the same way |
| output (104 bytes) | `u64 count ‖ BLAKE3(enc m₀) ‖ BLAKE3(enc m_n) ‖ data root` | computed here: `m₀ = config.init`, `m_n` the submitted model, the count and data root from the schedule's batches and `lr` (`ExecShape`; for one `train_tree` execution, the BLAKE3 Merkle tree over the intermediate models and batches) |
| root claim | `[1, entry] ‖ words(BLAKE3 identity) ‖ words(BLAKE3 output)` (18 Goldilocks words) | computed here |
| root statement | `S_root = BLAKE3("ix/compress-wrap/v1\0" ‖ K ‖ BLAKE3(claims_bytes([root claim])))` | computed here (`compress_wrap::Statement`) |
| wrapper claim | `[1, 0] ‖ 0⁸ ‖ words(S_root)` | computed here; the prefix `[1, 0]` (call tag, entry of `CompressWrap::verify_root`) is Ix's `WrapPolicy::claim_prefix`, taken as given |
| terminal statement | `S = BLAKE3("ix/compress-wrap/v1\0" ‖ W ‖ BLAKE3(claims_bytes([wrapper claim])))` | computed here (`WrapPolicy::statement_for`); `W`, the wrapper key's BLAKE3 (`1bc0cd05…`, the `m16384w64-v3` layout's `key_blake3`), is the job's pin, not recompiled |
| public inputs | `u128_le(S[0..16])`, `u128_le(S[16..32])` | computed here and by the verifier tool (`final_program::statement_arguments`), and compared |

`words` is a digest as eight little-endian `u32`, `enc` each word modulo the Goldilocks prime as a
little-endian `u64`, `claims_bytes` the claim count, then each claim's length and words, as `u64`.
`IxAIVerifyTest` reproduces the statements and public inputs that the pipeline recorded for all
three certificates in `.truthmines/aiur`, and the BLAKE3 of the root and wrapper claim files.

What is pinned, by BLAKE3, in the job (`compression`): the terminal PLONK verifying key
(`verifying-key.bin` of the prepared terminal, `736588d0…`, SHA-256 `30dd3ee8…`), which fixes the
terminal circuit (the Lean-exported constraint system `54a12ad1…` with its pairing configuration
`eec66e8a…`), the narrow key and policy it embeds, and the KZG points the verification equation
uses; and the wrapper key `W`. The receipt names the key file (`plonkKey`, written by
`ixai package-assemble --plonk-key FILE`); its BLAKE3 must be the pinned one (otherwise `REJECTED`),
and the verifier reads a copy of the checked bytes.

The check is `aiur_plonk_verify KEY KEY_BLAKE3 PROOF S` (fork `ix-aiurexec`,
`crates/proof-compression/examples/aiur_plonk_verify.rs`, built with `--features plonk,cuda`). It
calls Ix's own verifier (`gnark::verify` → `tools/gnark` `verifyAiurProof`, the call the pipeline
makes after proving), with the key's SHA-256 as the trusted digest and, as the setup anchors,
`[1]G1`, `[1]G2`, `[τ]G2` of the Ignition parameters bundled in the build (Ix's release recursive
key, pinned by BLAKE3 in Ix's source). gnark refuses a key whose anchors differ, so a key set up on
a development SRS (`--dev-kzg-srs`, `--dev-final-srs`, known trapdoor) is rejected. The SRS file the
three certificates were proved with is Ix's release Ignition SRS (SHA-256 `06db33d8…`, the pin in
`pipeline/prepare.rs`; `plonk-srs.json` records `setupClass: ignition`).

`ixai-verify compressed` runs this check alone, for any of the three kinds of root:

```
ixai-verify compressed --config full --shape steps|blocks:20|tree --aggregator AX --aggregator-blake3 HEX \
  --program P --program-blake3 HEX --plonk proof.bin --plonk-key verifying-key.bin --plonk-key-blake3 HEX \
  --wrap-key-blake3 HEX --model model.txt [--models models.txt]
```

It recompiles the keys (`aiur_exec_check --keys`), computes `S` and verifies the proof; no other
file of the prover is read (`--models`: the intermediate models a `train_tree` root hashed, each
checked to be in the weight range, the last the submitted model).

Measured 2026-11-20: all three certificates verify against the pinned key and the statements
computed here (600 `Fixed::step` executions `d8551c47…`, statement `1c67d287…`; 30
`Fixed::train_block` executions `20d80b11…`, `8b28f4f9…`; one `train_tree` execution `26eb66b9…`,
`2771ff48…`), each in 1.4–2.1 s wall for the whole command (key recompilation about 0.5 s, the
PLONK verification itself 20–40 ms). A package whose only training route is `aiur-exec` is
`PROVED` in 11.9 s, the claims' `ix verify` runs included. `ix/verify-tests.sh` §8 covers a
certificate with one byte changed, a model word changed, another root's certificate, a changed
intermediate model of the tree, a key other than the pinned one, and a PLONK verifier that cannot
start or stops before reading the proof.

Assumptions printed with a verified route, beyond those of the root claim:

- `aiur_plonk_verify` (BLAKE3 printed) runs gnark's verifier as the pipeline does;
- PLONK knowledge soundness (gnark, BN254 KZG) for the pinned key;
- the Ignition ceremony (MAIN IGNITION, final contributions 196 and 197): the PLONK and the narrow
  stage's KZG are sound only if its `τ` is unknown, i.e. at least one contributor destroyed its
  secret. The verifier checks that the key's anchors are the release's; it does not replay the
  ceremony;
- each recursion layer is sound and verifies what its predecessor claims (terminal → narrow →
  CompressGL → wrapper → root STARK). Those verifier programs are Aiur written in Lean but not
  proved to implement their verifiers; the Rust circuit lowering, key writers, statements and
  policies are trusted (Ix `docs/aiur-compression-architecture.md` §3);
- STARK soundness of the root, the wrapper and CompressGL (multi-stark, Goldilocks FRI, BLAKE3) and
  packed-SHPLONK soundness (Ix `docs/aiur-packed-kzg-soundness.md`);
- the statement format and wrapper claim prefix are Ix's, and `W` is the job's pin;
- BLAKE3 collision resistance;
- the step semantics of the route (`step_sound_deployed` and the other `aiur-steps` hypotheses but
  STARK soundness of `verify_claim`).

### The full run (2026-11-20)

`.truthmines/package/full`: job `commitment.json` `742359c1…` (format v2, issued from the spec and
the `full` config: config digest `32744b61…`, dataset root `2733c972…`, programs `Fixed::step`
`5a471d31…`, `Fixed::train` `40503d02…`, `AiurExec::aiur_exec` `a5c45df9…`; claim policy: spec
`7e6bc58c…`, role binding `32284836…`; templates compiled from `Template_full.lean` into
`template_full.ixe`), model weights `45ea4f5f…`. The 2026-11-19 commitment, which named the trained
environment and claim addresses, is kept as `commitment-v1.json`.

```
ixai-verify package --commitment .truthmines/package/full/commitment.json \
  --commitment-blake3 742359c1b762c73a0123396565eb34a325b992438a4cb8446222ed3b7d89285b \
  --receipt .truthmines/package/full/receipt.json
```

`PROVED` in 15.0 s (previously 142 s): `aiur-steps` verified (600 proofs in one `verify_claim --batch` process, 1.9 s
wall, against 88.6 s for 600 processes before), `aiur-train` verified, `aiur-exec` attested (claim
checked), all 8 claims verified (template, exact claim, model read from constant `1393027d…`;
`ix verify` four at a time, about 10 s). The fork's verifier builds may link
`libmulti_stark_cuda.so`, so they need `LD_LIBRARY_PATH` pointing at it and, for
`aiur_exec_check`, `LD_PRELOAD` of the system `libcuda.so.1` (as `ix/ladder.sh` does). Scratch files
go to `IXAI_VERIFY_WORK` (default `/tmp`) and are removed afterwards.

The template's role binding must be the trainer's: Ix records in an environment's header the role
table of the kernel roles its closure uses, and a `Check` claim names that table's hash. The
template names `String.decEq`, `String.toByteArray` and `Int.decEq` (`roleAnchors`) so that its
closure binds the same 86 roles as an environment that runs the specification; a trainer whose
environment binds another table produces claims the policy refuses.

## One certificate for training and its environment

`.truthmines/combined/cert/full` is one 584-byte PLONK certificate (`7a2a00c5…`) of the same
compression pipeline over the root of an `ix_aggr` join (shape 18, `ChildKind.aiur`): one
`AiurRun` claim that joins IxVM's `CheckEnv` claim of the environment holding the refinement
theorem `IxAICombined.train_of_deployed_blocks_enc` and its binding `IxAICombined.blockRun` with
the `aiurExec` root of the training run, 30 `Fixed::train_block` executions of 20 steps.
`ixai-verify combined` (`IxAIVerify.Combined`) checks it:

```
ixai-verify combined --commitment job.json --commitment-blake3 HEX --template-env template_full.ixe \
  --root .truthmines/combined/cert/full/root --plonk .truthmines/combined/cert/full/plonk/plonk/proof.bin \
  --plonk-key verifying-key.bin --env .truthmines/combined/env/full.ixe \
  --partition .truthmines/combined/cert/full/proven.ixes --run-root .truthmines/combined/run-root \
  --aggregator .truthmines/aiur/aiurexec-block/aiur-exec.ixa --aggregator-blake3 001431282dc3… \
  --program .truthmines/aiur/aiurexec-block/packages/block-000.ixa --program-blake3 5a8070af53a9… \
  --model model.txt [--theorem NAME] [--binding NAME] [--block-steps 20]
```

It is a command and not a receipt route because the job (format v2) names none of what the joined
root is checked against: the IxVM and `ix_aggr` artifacts, the run aggregator and the
`Fixed::train_block` program (the job's `AiurExec::aiur_exec` is the step aggregator), and the
theorem; a route would need the job-format decision that block and tree routes also wait for. The
command takes from the job what it does fix (config, the addresses of `IxAICore.train` and
`IxAICore.Triage.spec`, the template environment, the compression pin), and the approved packages
by BLAKE3 on the command line, as `compressed` does. It needs a job that pins the compression
pipeline (otherwise `INCOMPLETE`).

In order, with every file of the trainer copied into the work directory first, so that every check
and the statement read the same bytes:

1. `aiur_join_check` (fork `ix-cert`, `crates/ix-prover/examples/aiur_join_check.rs`;
   `IXAI_AIUR_JOIN_CHECK`, default `ix/toolchain-cert/bin/aiur_join_check`) on the joined root. Its
   `SPEC_ARGS` and `EXPECTED_OUTPUT` files are written by the verifier: `m₀ ‖ lr ‖ xs ‖ ts` from
   the job's config, and the submitted model. `.truthmines/combined/spec` is never read. Its exit
   status must be 0, with a `PROVED` line naming the theorem, the binding and the BLAKE3 of the
   submitted model's encoding (computed here), and a `hypotheses:` line.
2. The addresses it prints of the constants the theorem's statement references must be the
   consumer's: `IxAICore.train` and `IxAICore.Triage.spec` the job's (`spec.trainAddress`,
   `spec.address`), and `IxAIAiur.fullConfig` the address of `IxAITemplate.<config>.config` in the
   consumer's template environment (`--template-env`, whose BLAKE3 must be the job's), read with
   `ixw addr-of`. An `assumed:` line (the theorem is an axiom of the environment) leaves the
   outcome `INCOMPLETE`: the run is checked, the theorem is not.
3. The run's output claim `out.bin` must equal the one computed here (`Combined.expectedOutput`,
   `Compression.execOutput` for blocks of 20).
4. `aiur_plonk_verify` under the job's pinned key, against
   `S = Compression.terminalStatement W (BLAKE3 root-vk.bin) rootClaim`, `rootClaim` the one
   18-word claim of `root-claims.bin` (`Compression.decodeClaims`: the bytes must be exactly the
   `claims_bytes` encoding of canonical words), exactly as for the `aiur-exec` route.

| Value | Where it comes from |
|---|---|
| `m₀`, `lr`, the 600 scheduled batches, their 30 blocks | computed here from the job's config (`IxAICore` evaluated natively) |
| the final model | the submitted model, checked canonical and in `[-4096, 4320)` |
| the run's output claim (count, `BLAKE3(enc m₀)`, `BLAKE3(enc m₃₀)`, data root) | computed here and compared with `out.bin`; `aiur_join_check` recomputes it too, from the files written here |
| IxVM key, `ix_aggr` key (the root key) | recompiled by `aiur_join_check` from the artifacts pinned by BLAKE3 in `IxAIVerify.Combined` (`0cbcb681…`, `80d584ab…`; files `ix/artifacts/ixvm-PIN.ixa` and `aggregate-PIN.ixa`, or `IXAI_IXVM_ARTIFACT`, `IXAI_JOIN_AGGREGATOR`; never the `cert` profile's current digests) |
| the run aggregator's and program's keys, the run's identity | recompiled by `aiur_join_check` from the approved packages (BLAKE3 given by the consumer) |
| the environment's `CheckEnv` claim and subject root | rebuilt by `aiur_join_check` from the trainer's environment and partition |
| theorem and binding addresses | read by `aiur_join_check` from the environment, by the names the consumer gives |
| `IxAICore.train`, `IxAICore.Triage.spec`, `IxAIAiur.fullConfig` | compared here with the job and the consumer's template environment |
| root key digest `K` | BLAKE3 of the copy of `root-vk.bin` that `aiur_join_check` found equal to the recompiled key (`79894717…`) |
| root claim | the copy of `root-claims.bin` that `aiur_join_check` checked word by word against the recompiled keys and `ix-claim.bin` |
| statement `S` (`3b9edda7…`) | computed here |
| `W`, PLONK verifying key | the job's pin |

Taken as given: the job (its BLAKE3), the digests of the approved run aggregator and program
(command line, not in the job), the pinned artifacts' digests (in the verifier's source), the
theorem's and binding's names, and the theorem's statement beyond the three constants it is checked
to reference.

Hypotheses printed with `PROVED`: those of the job and the approved packages; `aiur_join_check`
(BLAKE3 printed) reads claims and environment records as Ix and the circuits do and does not verify
the root's proof; the theorem states the refinement its name says (its statement is not compared
with an expected term); IxVM's soundness for the `CheckEnv` claim, with the pinned kernel differing
from the one Ix PR 678 proves in `try_nat_dispatch_prewhnf`; the hypotheses `aiur_join_check`
prints (STARK acceptance implies memo-checker acceptance; `BlockOnlyParity`, checked by `#eval`;
soundness of `ix_aggr` with shapes 17 and 18 and of `AiurExec`; the claim encoding, checked in Rust
and not in Lean); all the terminal hypotheses of the compressed certificate (above); and that the
claim encoding is read the same way by the circuit and native evaluation of the specification
agrees with the kernel's.

Outcomes follow the routes' rules: a tool that cannot start (`aiur_join_check`, `ixw`,
`aiur_plonk_verify`), a missing pinned artifact or template environment, or `aiur_join_check`
stopping before its first `ok:` line leaves it `INCOMPLETE`; a `REJECT` line, or a failure after
the checker started on the evidence, `REJECTED`; a missing file of the trainer with a failure
other than a `REJECT` is missing evidence, `INCOMPLETE`.

Measured 2026-11-20: `PROVED` in 7.7 s wall for the whole command (4.1 GB peak, 225% CPU):
`aiur_join_check` 4.3 s (31 checks, environment claim `456de28a…`, 0 user axioms), the PLONK
verification 25 ms, the rest the job, `ixw addr-of` on the template environment and copying. `ix/verify-tests.sh` §9 covers the certificate accepted, one byte
of the proof changed, one model word changed, the run's own root (`aiurexec-block/top/root`) in
place of the joined root, a missing `aiur_join_check`, one that panics after its first check, one
that fails in its setup, and a job without the compression pin. `IxAIVerifyTest` reproduces
`3b9edda7…` and its public inputs from the key digest and the bytes of `root-claims.bin`.

## The other verification boundaries

- **Trajectories** (`ixai check`, `ixai-verify trajectory`): the consumer names the job
  (`--job NAME` or `--job-digest HEX`, default `default`); a header naming another job is rejected
  before any step is read, the steps are checked against the consumer's job, so the number of
  steps is the job's schedule, and `--weights HEX` binds the returned weights to the verified
  result.
- **Dataset and store roots** (`IxAICommon/Merkle.lean`): `merkleRootV2` hashes the leaf count into the
  root; paths carry count and index and are rejected out of range or with the wrong number of
  siblings. Proved for any hash: `rootOf_ne_of_length_ne`, `collision_of_rootOf_eq`,
  `verifyPath_index`, `verifyPath_sound`. `merkleRootV1` is kept only to recompute roots recorded
  before version 2 (`rootsV1` in the dataset manifests).
- **Curation** (`IxAIData/Rules.lean`): an item with any constant or axiom name the extraction
  cannot address is refused (`Refusal.unresolvedName`); `curate_spec` states that every accepted
  item has `unresolved = 0` and only allowed axioms.
- **Proof submissions** (`ixai reward BUNDLE [--out FILE]`, `ixai reward-submit`): every submission gets a fresh job directory of its own, removed after the verdict. Every step that reads it runs in bubblewrap, and the harness refuses to run without `bwrap`. The worker sees only the system's `/usr` and `/lib*`, the Nix closure of the compiling toolchain, the `ix` binary, `ixw`, the bundle's built `IxAICore`, and its own job directory (writable only while compiling). Its environment is `PATH`, `IX_BIN` and `IX_LEAN`, and nothing is inherited. The text must parse as exactly one term without escape hatches, checked by `IxAIVerify.checkSubmission` running as a script under the toolchain that compiles it (`ixw`'s `IX_LEAN`). After compiling, the harness reads the `.ixe` once and checks from its bytes that `IxAIReward.goal` is a safe theorem whose type is the constant at the target address the harness computed from its own file (`IxAIVerify.Ixon.checkGoalType`, which authenticates every record of the environment by its address), so parsing is not trusted. It then runs `ix check-lean` with the job directory read-only and requires the `.ixe` to be unchanged. Kernel checking does not contain elaboration, so the isolation is required, not optional. Tests: `ix/reward-tests.sh`.

## Regression tests

`IxAITest` and `IxAIVerifyTest` (`#guard`s, run by `lake build`) and `ix/verify-tests.sh`
(through `ix/heavy.sh`; it runs `ix/reward-tests.sh` as a section) cover each boundary above with
the failing input that motivated it.
