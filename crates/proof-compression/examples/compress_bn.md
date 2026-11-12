# Running an Aiur BN compression stage

Build `cargo build --release -p ix-proof-compression --example compress_bn`.
The executable accepts `key`, `plan`, or `prove`, followed by a trusted JSON
configuration and a new output directory. Paths are relative to the working
directory. Existing output directories are refused.

`key` derives the BN verifier from a pinned compiler artifact and the selected
setup. The public capacity is independent of the loaded SRS prefix. Production
uses the released Ignition parameters selected by `IX_KZG_SRS` or `IX_PARAMS_DIR`.
Setting `development` to `true` selects known-trapdoor parameters for testing.

```json
{
  "artifact": "compress-bn.ixa",
  "artifact_blake3": "<independently expected artifact digest>",
  "max_log_height": 24,
  "quotient_degree": 8,
  "development": false,
  "gl_predecessor": {
    "artifact": "compress-gl.ixa",
    "artifact_blake3": "<independently expected GL artifact digest>",
    "key": "gl-key.bin",
    "key_blake3": "<independently expected portable GL key digest>",
    "proof": "gl-proof.bin",
    "root_key_blake3": "<authorized aggregate root key digest>",
    "root_claims_blake3": "<expected serialized root claims digest>",
    "max_record_bytes": 68719476736,
    "max_trace_bytes": 103079215104
  }
}
```

The optional `gl_predecessor` verifies the native GL proof against the supplied
root statement, constructs a policy authorizing both source-wire keys and their
physical entry IDs, and emits `input.json` with the source advice files. Omitting
it prepares only the candidate BN key and its source projection. A portable-key
digest and a source-key digest identify different encodings and are not
interchangeable.

```sh
target/release/examples/compress_bn key trusted.json prepared
target/release/examples/compress_bn plan prepared/input.json counted
target/release/examples/compress_bn prove prepared/input.json proven
```

`plan` executes the Aiur verifier with a bounded interpreter record and reports
exact padded trace dimensions without allocating proving traces. `prove` checks
the configured trace limits, available proving powers and trusted BN key before
allocating witnesses. The trace-byte allowance covers main, fixed and lookup
matrices; polynomial transforms, commitments and allocator overhead need
additional memory. The report distinguishes these counts from proof timings.

For a subsequent stage, use an `input` object instead of `gl_predecessor`. It
contains `policy`, `policy_blake3`, `statement_blake3`, `stage`, `key`, `claims`,
`proof`, `max_record_bytes`, and `max_trace_bytes`. Key, claims and proof paths
refer to the preceding stage's `source-key.bin`, `source-claims.bin` and
`source-proof.bin`. Increment the stage while retaining the independently
authorized policy and statement digests.

The stage proof authenticates a deferred pairing accumulator. Successful native
verification of this proof does not discharge that accumulator; terminal
`CompressFinal` verification is required to accept the complete chain.
