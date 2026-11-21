# M2: the certificate with the model's card, end to end in 22:51

`proof.bin` is a 584-byte PLONK certificate made on 2026-11-21 by one timed run
(`ix/combined/timed_run.sh g5`) that reused no proof and had the machine to itself. It covers
one `AiurRun` claim that joins:

- **The environment** (36,915 constants, no user axiom): the refinement theorem
  `IxAICombined.train_of_deployed_blocks_enc`, the binding `IxAICombined.blockRun`, the
  safety theorems, and, new against M1, the deployed model as a constant
  (`IxAICombined.Deployed.trainedOutput`) with its evaluation card
  (`IxAICombined.Deployed.cardCertified`) and four gate decisions (`decision0` to `decision3`).
- **The training run**: 30 executions of `Fixed::train_block`, from the specification's initial
  model to the model in `model.txt`.

The independent check also confirms that the model constant in the environment is the model
the run ended at (331 words), so the card and the decisions are about the trained model.

## Timeline

| Stage | Seconds |
|---|---|
| train: 30 block proofs, their tree, two wraps | 311.6 |
| env: 3 claims and their joins in one prover run | 831.9 |
| export | 1.9 |
| join | 22.7 |
| check (`aiur_join_check`, `PROVED`) | 3.7 |
| compress to PLONK | 199.5 |
| **total** | **1,371.4 (22:51)** |

M1 took 116:46. `timeline.tsv` and `timed.txt` are the run's own records.

## Identifiers

| | |
|---|---|
| certificate, BLAKE3 | `82cf6fbebeb5d9f30271ea3595591b816fed4fc7a2e708a3e9c38b45a4d87ac5` |
| terminal statement `S` | `4f473d40857c2df8d64ca21851d48553907dbddb9105f45c21dd9ce81d4bde46` |
| PLONK verifying key, BLAKE3 | `736588d00f08bb56626b83f8fea79af0bb516a6e6f99e6bde301afdf7c4a3b3e` (as M1; the file is `../m1/plonk-verifying-key.bin`) |
| environment claim | `8e99a8edf7f20c2da381a729bcc60de1b43cc2fc559583bd78f17a71b153b461` |
| environment subject root | `e837df3f9ef6ac3d4d11b2be89ae2d39d8c23bee875d9bb57dac6eb376797f39` |
| environment root (compile) | `ff52b081d173d5def42fd66bd536d8a7b5e18bc0d4679aefbf57eeb3fee033b0` |
| model constant | `a2523a1d7cefc0881b5966b2dd97a7c6ac8f5a99c97c23fc9e6b0f2f63cae9a4` |
| card theorem | `2ba03dbd58e3c70daae183198ce92dbca18d79d070c841d55dba85320bd4d0f9` |
| training program key | `d46caf1e358f9e28744a1163b2d25b2ea4de331870fcc78e1625119edfa1da58` |
| IxVM artifact | `6c9353f8392d9d5fae944a8ac0ff7cfb276189e7f6a369364ba9c5ccfac13407` |
| `ix_aggr` artifact | `80d584ab24439dd23ad642a57009210ba3d407f4c20a4755c600d043fcaefa2e` (as M1) |

## Files

`proof.bin`, `checks.json` (the compression pipeline's own checks, all true), `root/` and
`run-root/` (the joined root and the training root as exported, without their proofs),
`aggregate.root`, `model.txt`, `job.json` (the job commitment the consumer check used),
`check.txt` (the independent checker's output: `PROVED`, with the model-constant and
containment lines), `consumer-check.txt` (`ixai-verify combined`: `OUTCOME: PROVED`),
`timeline.tsv`, `timed.txt`, and `MANIFEST.tsv` with the BLAKE3 and size of every input,
including those kept outside the repository.

## What it was made from

This branch at the merge of the bounded rebase search (the kernel and its pins), with the path
lemmas in the fused shape. The settings of the environment's prover run are in `timed.txt`.

## Checking it

As for M1, with this certificate's circuits approved by digest:

```sh
ixai-verify combined --commitment certificates/m2/job.json --commitment-blake3 2b8b2eadc928b93cf86f88364a26f5408d8cbed301b94a53b697b0a74f1af791 \
  --template-env template_full.ixe --root certificates/m2/root --plonk certificates/m2/proof.bin \
  --plonk-key certificates/m1/plonk-verifying-key.bin --env g5.ixe --partition proven.ixes \
  --run-root certificates/m2/run-root \
  --aggregator aiur-exec.ixa --aggregator-blake3 001431282dc34b09e890944f9396bfe1ac2187914d30744a02209a130057e0bc \
  --program block-000.ixa --program-blake3 5a8070af53a98fd010ec7fb4af17818183f6388b1a336548213716d38d5827c0 \
  --model certificates/m2/model.txt \
  --ixvm-blake3 6c9353f8392d9d5fae944a8ac0ff7cfb276189e7f6a369364ba9c5ccfac13407 \
  --join-aggregator-blake3 80d584ab24439dd23ad642a57009210ba3d407f4c20a4755c600d043fcaefa2e
```

The model-constant and containment checks are options of `aiur_join_check`
(`--model-constant`, `--contains`); `ixai-verify combined` does not pass them yet.

## What it rests on

As M1 (`../m1/README.md`), with these differences: the kernel has further changed functions
whose refinement is not redone (the substitution walks and searches, and the bounded rebase
search); it is one run, not repeated.
