# Aiur GL-to-BN CLI

`--aiur-chain` selects a configuration for `CompressGL` and one or more
`CompressBN` stages. Required `--aiur-chain-blake3` independently authenticates
its exact bytes before parsing. The resulting KZG envelope is verified
against the expected aggregate statement, both pinned programs and keys, and
the accumulated pairing equation. Terminal Aiur-to-PLONK integration is a
separate stage.

Prepare the keys from a JSON template containing the trusted compiler artifact
digests, fixed public capacities and host resource limits:

```json
{
  "format": "ix-aiur-chain-v1",
  "gl": {
    "artifact": "compress-gl.ixa",
    "artifact_blake3": "<64 hex digits>",
    "max_log_height": 24,
    "quotient_degree": 2
  },
  "bn": {
    "artifact": "compress-bn.ixa",
    "artifact_blake3": "<64 hex digits>",
    "max_log_height": 24,
    "quotient_degree": 8
  },
  "bn_stages": 1,
  "admission": {
    "gl": {
      "max_record_bytes": 68719476736,
      "max_trace_bytes": 103079215104,
      "max_total_rows": 4294967296
    },
    "bn": {
      "max_record_bytes": 68719476736,
      "max_trace_bytes": 34359738368,
      "max_total_rows": 4294967296
    }
  }
}
```

Paths resolve relative to the JSON file. Record limits bound interpreter
storage; trace limits cover main, fixed and lookup matrices. Prover workspaces
and allocator overhead require additional memory. Public capacities belong to
the verifier keys and remain fixed when a smaller proving-power prefix is
loaded.

```sh
ix compress aiur-chain-key template.json --out prepared-chain
ix compress aiur-check --aiur-chain prepared-chain/manifest.json \
  --aiur-chain-blake3 MANIFEST_BLAKE3
ix compress ROOT --aiur-chain prepared-chain/manifest.json \
  --aiur-chain-blake3 MANIFEST_BLAKE3 --fresh --out run
ix verify --aggregate --ixe env.ixe --ixes proven.ixes \
  --aiur-chain prepared-chain/manifest.json \
  --aiur-chain-blake3 MANIFEST_BLAKE3 COMPRESSED
```

Key preparation requires a new output directory. It copies the authenticated
artifact bytes to `gl-program.ixa` and `bn-program.ixa`, writes `gl-key.bin` and
`bn-key.bin`, and writes `manifest.json` last. All bundle paths are relative,
so identical inputs and setup produce identical manifests in different directories.
The printed digest identifies the candidate manifest for review. The manifest
digest must be supplied independently of the proof and bundle; the proof
envelope contains no verifier pins. `aiur-check` reproduces both keys from their
artifacts and setup before an expensive run. Ordinary verification needs the trusted artifacts and
portable keys, but no proving powers.

Production uses the installed Ignition SRS or `IX_KZG_SRS`. Development key
preparation and preflight require `--dev-srs`, compression requires
`--dev-kzg-srs`, and verification requires `--dev-srs`. Development verification
prints `development-only` and is not admitted as production verification.

The benchmark mode uses the same fresh proof, manifest verification, compression
and final verification commands as the other whole-environment modes:

```sh
ix bench run --backend ixvm --env Init --constants none \
  --env-mode compress --env-compression aiur-bn \
  --aiur-chain prepared-chain/manifest.json \
  --aiur-chain-blake3 MANIFEST_BLAKE3 --out results.json
```

`--env-dev-srs` explicitly selects development parameters for that benchmark.
The output retains the existing `compress-time`, `compress-proof-size`,
`compress-verify-time` and end-to-end metrics. Compression also writes
`aiur-bn-report.json` with per-stage row counts, trace bytes and phase timings,
plus the intermediate GL proof and final chain envelope.

For `--fresh`, the known Aiur stage proof/report files are removed before
validation or proving. A failed run therefore leaves no stale BN proof at its
output path; unrelated files are preserved.
