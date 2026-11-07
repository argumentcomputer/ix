# STARK parameters and security

Every Aiur proof (IxVM claims, the recursive verifier and aggregation) is a
multi-stark proof over Goldilocks, with challenges in its degree-2 extension,
BLAKE3 Merkle commitments and FRI. This page gives the FRI parameters, the
security they buy, the floor every key must meet, and how to change them.

## Parameters

| Parameter | Value | Where |
| --- | --- | --- |
| `log_blowup` | 2 (rate 1/4) | varies |
| `num_queries` | 100 | varies |
| `query_proof_of_work_bits` | 20 | varies |
| `commit_proof_of_work_bits` | 0 | varies |
| `max_log_arity` | 1 (binary folding) | fixed by the adapter and the recursive verifier |
| `log_final_poly_len` | 0 (constant final polynomial) | fixed |
| `cap_height` | 0 (Merkle roots) | fixed |

These are the parameters main shipped before formal Aiur. The source is
`aiur::trace::stark::Parameters::DEFAULT` (`crates/aiur/src/trace/stark.rs`),
which every prover and verifier uses: `ixvm-proof`, `stark-verifier`,
`ix-prover` and the compression FFI. Lean mirrors it in
`Ix/Aiur/Parameters.lean` (`Aiur.defaultCommitmentParameters`,
`Aiur.defaultFriParameters`), and the Rust test `lean_mirror_matches` checks
that the two agree.

All seven values are in the verifying key's header (`crates/stark-key`), so
they are covered by the key's BLAKE3 digest, and multi-stark seeds the
Fiat-Shamir transcript with them. A proof made under any other parameters,
weaker or stronger, fails against a key built with these. The recursive
verifier reads the parameters from the inner key it is given, so it verifies
inner proofs under whatever parameters that key carries; the aggregation
program pins the IxVM and aggregation key digests, which binds them.

## Security

The usual summary is the ethSTARK conjecture's query-phase bits,
`log_blowup · num_queries + query_proof_of_work_bits` (plonky3's
`conjectured_soundness_bits`): 2 · 100 + 20 = 220. That is the FRI query
phase only. The whole protocol has other terms that do not depend on the
query count, and the extension field bounds them: challenges are drawn from
a field of about 2^128 elements, so the constraint batching (ALI), the
out-of-domain sample (DEEP), the logUp lookup argument and FRI's commit phase
each lose `log2` of the instance's size from 128 bits. For a trace of 2^n
rows these are roughly `128 - n - log2(degree)` (DEEP),
`128 - log2(constraints)` (ALI) and `128 - log2((W + 2) · lookup rows)`
(lookups, `W` the widest message). No choice of queries or proof of work moves
them; only a larger extension field would.

`lake exe fri-security` computes every term for a real instance, in three
regimes: unique decoding and the Johnson (list-decoding) bound, which are
proven, and the conjectured regime of eprint 2025/2010. Its input is the
statistics of a key and a proof:

```sh
target/release/stark-verifier statistics key.bin proof.bin > stats.json
lake exe fri-security stats.json
lake exe fri-security stats.json --table \
  --parameters 2,100,0,20 --parameters 1,200,0,20   # LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW
```

It also reads the compression stage's FRI key
(`fri_sizing --statistics outer-vk.bin`, see
[compression stage boundaries](compression-stage-collapse.md)), and
`--instance` takes an instance's facts directly.

## The floor

`stark_key::security::check` rejects parameters below the floor:

- `log_blowup` between 1 and 4, and at least one query;
- at most 32 proof-of-work bits in either phase, so grinding cannot stand in
  for queries;
- `log_blowup · num_queries + query_proof_of_work_bits` of at least 220, the
  default's level.

Building a backend (`Backend::new`, `for_batch`, `for_batch_verification`,
`for_batch_on_device`) checks it, and so do both key decoders
(`stark_key::from_bytes` and `aiur::trace::stark::VerifyingKey::from_bytes`),
including the compression pipeline's root key. The floor makes "never weaker
than main" a property of the code: a key at #678's original setting (blowup 2,
64 queries, no proof of work: 64 bits) is rejected.

Tests whose toy keys keep recursive circuits small use
`from_bytes_below_floor` and `Backend::for_batch_below_floor`. They are hidden
from the documentation and must never decode or build a key a verifier trusts.

## Changing the parameters

1. Change `Parameters::DEFAULT` and its Lean mirror in
   `Ix/Aiur/Parameters.lean` together. If the floor changes, change
   `stark_key::security::MIN_CONJECTURED_BITS` and
   `Aiur.minConjecturedSecurityBits` together too.
2. Run the estimator on a representative proof under the new parameters, and
   keep every regime at least as strong as before.
3. Every verifying key changes: the IxVM key, the recursion and aggregation
   keys, and the aggregation root key the compression release keys pin
   (`crates/proof-compression/verifying-keys`). Regenerate them, and the
   cached proofs keyed by them.
4. Run `bash tools/ixvm/check-formal.sh`, which proves and verifies IxVM,
   recursion and aggregation under the new parameters.

For measurements, `compare` (`crates/stark-verifier/examples/compare.rs`)
takes `--parameters LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW`, and
`--below-floor` for weaker settings.
