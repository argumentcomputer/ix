# M1: one certificate for training and its environment

`proof.bin` is a 584-byte PLONK certificate. It covers one `AiurRun` claim that joins two proofs:

- **The environment.** The IxVM `CheckEnv` aggregate of the Lean environment of the refinement
  theorem `IxAICombined.train_of_deployed_blocks_enc`: 36,760 constants compiled, 30,989 in
  Lean's logic, no user axiom. It holds the theorem, the binding `IxAICombined.blockRun` that
  names the training program's key, the generated path lemmas and the Aiur compiler's
  correctness proofs.
- **The training run.** The aggregate over 30 executions of `Fixed::train_block` (20 SGD steps
  each, 600 steps) from the specification's initial model to the model in `model.txt`.

The join (`ix_aggr` shape 18) verifies both proofs and opens the theorem and the binding in the
environment's subject root by Merkle paths. With the theorem, the claim gives
`IxAICore.train IxAICore.Triage.spec (config full) = ` the submitted model.

| Identifier | Value |
|---|---|
| certificate, BLAKE3 | `7a2a00c51524146aadc86b72750ced8f4d56f5cdc874e8562e090b99790b3b22` |
| terminal statement `S` | `3b9edda783a3ec5ccf1a4f5b0d807d9653386ddb8c6e99cca49de4f69b954def` |
| PLONK verifying key, BLAKE3 | `736588d00f08bb56626b83f8fea79af0bb516a6e6f99e6bde301afdf7c4a3b3e` (Ignition SRS) |
| joined root key, BLAKE3 | `798947179cf837f378820476df87c3149d67b5bf4e229e89c264e2c061620635` |
| environment claim | `456de28ade2e2601560041fe690a4f8ca74c5f43fcd72e8ece7051147dd493a9` |
| environment subject root | `946dd8ed55744b00fa85a517f93ec62482c88782bab7e3d0d719a08d511d7637` |
| environment root (compile) | `30b4a837fe92a42443c41f7557f105507dde3cbd75d44fbf9d5d4aecee2e699c` |
| environment aggregate root | `7d710a49d426cad8ad0c4e3673611ef6bd12226c87cf96f7715a0e6e8496cec7` |
| theorem address | `2512dc4398223ef0bf19ac50b4d3e8c111520ba4e656fccd3e85bc7f0d848d59` |
| training program key | `d46caf1e358f9e28744a1163b2d25b2ea4de331870fcc78e1625119edfa1da58` |
| IxVM artifact, verifying key | `0cbcb6812057cbb047da1a290a6ff6c72b1582e56596cab337c927a39f24fcd7`, `bfdd87cb08817fa6e0496fd4f3c20592b73a1c6e437db5f7b1234c4f28b22622` |
| `ix_aggr` artifact | `80d584ab24439dd23ad642a57009210ba3d407f4c20a4755c600d043fcaefa2e` |

## Files

| File | What it is |
|---|---|
| `proof.bin` | the certificate |
| `plonk-verifying-key.bin` | the terminal verifying key the certificate is checked under |
| `checks.json` | the compression pipeline's own eight checks, all true |
| `root/` | the joined root as exported, without its proof: the verifying key (`root-vk.bin`), the claim (`root-claims.bin`), the claim's preimage (`ix-claim.bin`) and `backend-allowed.bin`. The terminal statement is computed from the key and the claim. |
| `run-root/` | the training run aggregate's root as exported, without its proof: `root-vk.bin`, `root-claims.bin`, `out.bin` (the run's output claim) and `allowed.bin` |
| `aggregate.root` | the environment aggregate's root |
| `model.txt` | the submitted model |
| `check.txt` | the output of the independent check `aiur_join_check` on the joined root: 31 `ok:` lines and `PROVED` |
| `MANIFEST.tsv` | BLAKE3 and size of every input, including those too large for the repository |

Kept outside the repository, by digest in `MANIFEST.tsv`: the 245 MB compiled environment, the
proved partition, the two root proofs, the IxVM and `ix_aggr` artifacts, the run aggregator and
the block program package.

## What it was made from

- **Environment sources:** `Aiur/IxAIRefine`, `Aiur/IxAIStep.lean`, `Aiur/IxAICombined.lean`,
  `Aiur/IxAICombined/` and `IxAI/IxAICore`, compiled against the Aiur library as of Ix commit
  `4f14ec1ca`. The Aiur library on this branch is newer, so the environment root above is
  reproduced from that commit's library, not from this tree.
- **Prover and aggregator:** commit `2a7952660` (the two kernel changes, the Aiur-child join
  shapes and the pins of the changed circuits).
- **Independent checker:** `aiur_join_check` as of `84f9ec3b3`.
- **Training-run proofs and the standalone PLONK verifier:** commit `330bd0677`.
- **Compression:** the pinned pipeline under `IxAI/ix/toolchain` (not in the repository), with a
  manifest naming the joined root's key.

## Checking it

With the inputs of `MANIFEST.tsv` in place and a job commitment that pins the compression
pipeline (`ixai-verify commit … --plonk-key … --wrap-layout …`, as `ix/verify-tests.sh` §8
builds it):

```sh
ixai-verify combined --commitment JOB.json --commitment-blake3 HEX --template-env template_full.ixe \
  --root certificates/m1/root --plonk certificates/m1/proof.bin \
  --plonk-key certificates/m1/plonk-verifying-key.bin \
  --env full.ixe --partition proven.ixes --run-root certificates/m1/run-root \
  --aggregator aiur-exec.ixa --aggregator-blake3 001431282dc34b09e890944f9396bfe1ac2187914d30744a02209a130057e0bc \
  --program block-000.ixa --program-blake3 5a8070af53a98fd010ec7fb4af17818183f6388b1a336548213716d38d5827c0 \
  --model certificates/m1/model.txt
```

It reports `OUTCOME: PROVED` with the hypotheses it rests on; `ix/verify-tests.sh` §9 runs it and
seven rejecting or incomplete variants against the working store's copies of these files.

## What it rests on

Listed in full by the check and in `docs/verification.md`. In short: STARK, FRI and PLONK
soundness and Ix's audit boundary; soundness of `ix_aggr` with the two join shapes and of the
`AiurExec` run aggregator, both unproved prototypes; IxVM's soundness, with one kernel function
(`try_nat_dispatch_prewhnf`) changed from the version whose refinement is proved;
`BlockOnlyParity`, checked by evaluation; the claim encoding, checked in Rust; the compression
pipeline's layers; BLAKE3; the Ignition ceremony.
