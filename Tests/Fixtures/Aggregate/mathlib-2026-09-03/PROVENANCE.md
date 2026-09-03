# Mathlib Stage 2 aggregate proof — 2026-09-03

This directory contains a real production Aiur-FRI Stage 2 root proof for a
complete Mathlib environment. The dated directory is intentional: a future
protocol, verifying-key, parameter, or Mathlib-environment update should add a
new dated fixture rather than silently replacing this record.

## Artifact identity

- File:
  `c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f.ixon-proof`
- Format: serialized `Ixon.Proof` containing a `CheckEnv` claim and compact
  Aiur proof bytes
- Ixon content address (BLAKE3):
  `c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f`
- SHA-256:
  `1a3cc584d5ab8cfba51fb5457aca13b643020b3684281d49472f9d0a21df1df1`
- Size: 9,813,583 bytes (9.36 MiB)
- Root claim:
  `CheckEnv(3211abb340539c10220990fb095f8763cb3a364e111ebe57fb518992d42d7382, none)`

## Inputs and producer

- Environment: `mathlib.ixe`, 3,326,434,731 bytes, SHA-256
  `1044785de558aa99f93bca19d1e03b239289485d54cc458168b86851f4734609`
- Final manifest: `mathlib-233r-proved.ixes`, 52,548,538 bytes, SHA-256
  `c889f696272a865fed43ba1690c0795ac7c3d4d58c7ff386149cfbaff5778ee4`
- Environment constants: 679,499
- Retained shards: 239
- Stage 1 recovery revision:
  `54da708f12a7d1e07d19716e9000cb78cb5df553`
- Stage 2 producer revision:
  `77d132d80c65efd9d7d65136a7f4e3466e36ab9a`
- Prover: 64-vCPU CPU box with approximately 495 GiB usable RAM
- Recursion policy: production defaults (q=100), wrap-first,
  `--structural-above 4096`, `--jobs 2`, `--max-ram 450`

The production command started at `2026-09-02T19:01:35Z`:

```console
xargs -a proof-addresses-r.txt -n 239 -x ix aggregate \
  --ixe mathlib.ixe \
  --ixes mathlib-233r-proved.ixes \
  --jobs 2 \
  --max-ram 450
```

It completed all 477 slots (239 wraps and 238 joins) in 14:46:26 with exit
status 0. Peak process RSS was 515,028,732 KiB (491.2 GiB), with zero swaps.

## Full validation

The root was subsequently validated against both original inputs with the
manifest-bound production verifier:

```console
ix verify --aggregate \
  --ixe mathlib.ixe \
  --ixes mathlib-233r-proved.ixes \
  c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f
```

At revision `e92a44f518addd31e77a68b06ec8f9841c553b83`, validation established:

- the wrapper reproduces its content address;
- the Aiur proof verifies under the production `ix_aggr` system;
- the proof claim equals the exact manifest-relative root claim;
- all 679,499 environment constants occur exactly once;
- there are no missing, duplicate, or foreign constants; and
- the root has zero undischarged assumptions.

The parallel native audit took 2.939 seconds, backend setup 174 milliseconds,
and proof verification 51 milliseconds (3.23 seconds total wall time).

The repository test deliberately does not commit the 3.33 GB environment or
52.5 MB manifest. It pins the wrapper size, content address, decoded claim,
absence of assumptions, and native verification under the current production
backend. Repeating the full constant-coverage audit requires input artifacts
matching the SHA-256 values above.

## Updating this fixture

1. Produce a new complete Stage 2 root and run the manifest-bound validation
   command above against the exact source environment and manifest.
2. Create a new `mathlib-YYYY-MM-DD` directory and copy the root object from
   its fanout path under `~/.ix/store` without transforming it.
3. Record the producer and validator revisions, input hashes, proof address,
   claim, parameters, slot count, timings, and peak RSS in the new provenance
   file.
4. Update the fixture constants in `Tests/AggrSemantics.lean` and run
   `lake exe IxTests ix-aggr` plus the standard formatting, Clippy, and test
   gates.
