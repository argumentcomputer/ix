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
- Inner Aiur proof: 9,813,545 bytes, SHA-256
  `8810a775f8f5dee1aee109e86f0507d4fa79f025d26dbbff8c83c187f2ad3deb`

The compatibility guest's exact verifier inputs are committed alongside the
wrapper:

| File | Size | SHA-256 |
| --- | ---: | --- |
| `aiur-vk.bin` | 193,473 bytes | `c3f5aeb6e984b71513158f3c006a5d53b44a0930a0837aa3bc670f6e3d86f336` |
| `outer-claim.bin` | 144 bytes | `45423c0d1e587c0a201d3220aa26065ac41bb5c8dfd8c1801af368c92c248dbe` |
| `fri-parameters.bin` | 40 bytes | `6e632ea87df3ca2f0bfa9cf7cdeba3006c8acc81038f6566cc0e964d9567c5df` |

The recursion verifying-key BLAKE3 digest is
`be6f790a7a978336ab513cb77c9e208a606df72f9167e4a264778da641749768`.
The five little-endian FRI words are `(0, 1, 100, 0, 20)`.

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

## Protocol status

This proof was produced with `multi-stark` revision `2892243e` and remains a
record of the fully validated run above. Current Ix uses `multi-stark`
revision `a8aab731`, whose native pruned-multiproof protocol and verifying key
are intentionally incompatible. The current backend rejects this historical
wrapper with `InvalidProofShape`; accepting it through that verifier would be
a protocol-separation failure.

Ix therefore exposes a separate, artifact-specific SP1 compatibility path:

```console
ix compress-root \
  c2fdce660eb66899efa303b41d4ca1611a62a688ef20684fdc327739d38bd67f \
  --protocol mathlib-2026-09-03 --mode execute
```

The compatibility guest pins the producer-compatible Ix connector revision
`8846eed2a79e062c41b47131272dff41536d5cdb` and Multi-STARK revision
`2892243e674f9a0b3aca9004a8d00c79a23beec1`. Revision `8846eed2` retains the
protocol independently validated at `e92a44f518addd31e77a68b06ec8f9841c553b83`
while making host-only tracing optional for the zkVM target. Its host accepts
only the exact wrapper address, closed claim, proof length and proof SHA-256
above, then gives the committed key, claim, FRI parameters and proof to that
guest. It is never tried as a fallback from the current protocol.

The three verifier inputs were reconstructed at the producer-compatible
revision `d7f5ee0e541ce211df150b7bd393589692174416` from the deterministic
`ix_aggr` backend and the committed wrapper. Their sizes and both the key's
BLAKE3 identity and every file's SHA-256 were checked before import.

The repository test deliberately does not commit the 3.33 GB environment or
52.5 MB manifest. It pins the wrapper size, content address, decoded claim and
absence of assumptions. While `a8aab731` is current, it also pins rejection by
the current verifier at the known protocol boundary. Repeating the full
constant-coverage audit—or obtaining a proof that verifies under the current
backend—requires input artifacts matching the SHA-256 values above and a new
Stage 1 + Stage 2 run.

## Updating this fixture

1. Produce a new complete Stage 2 root and run the manifest-bound validation
   command above against the exact source environment and manifest.
2. Create a new `mathlib-YYYY-MM-DD` directory and copy the root object from
   its fanout path under `~/.ix/store` without transforming it.
3. Export the exact recursion verifying key, outer claim bytes, and FRI
   parameter bytes from a producer-compatible build.
4. Record the producer and validator revisions, input hashes, proof address,
   claim, parameters, slot count, timings, and peak RSS in the new provenance
   file.
5. Add a separately named compatibility guest; do not repoint an existing
   historical protocol or make it an automatic fallback.
6. Update the fixture constants in `Tests/AggrSemantics.lean` and run
   `lake exe IxTests ix-aggr` plus the standard formatting, Clippy, and test
   gates.
