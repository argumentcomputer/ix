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
`--instance` takes an instance's facts directly. It covers FRI only; the BN254
KZG stages after it are not FRI.

Under the default parameters, the weakest term of each regime is (bits, and
the limiting term):

| Instance | Unique decoding | Johnson, BCHKS25 | Johnson, DKT26 | Conjectured |
| --- | --- | --- | --- | --- |
| IxVM `Nat.add_comm` (2^16 rows, 158 circuits, 1.5M lookup rows) | 87.8 (query) | 85.2 (batching) | 87.9 (batching) | 100.1 (lookup) |
| Its recursive verifier (2^22 rows, 68 circuits, 367M lookup rows) | 87.8 (query) | 80.3 (batching) | 82.9 (batching) | 92.2 (lookup) |

So the provable security of a recursive proof is about 80 bits and its
conjectured security about 92; the extension field, not the FRI parameters,
sets both. Larger instances lose more.

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
than main" a property of the code: a key at #678's original setting
(`log_blowup` 1, 64 queries, no proof of work: 64 bits) is rejected.

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
   cached proofs keyed by them; the compression keys become a new version
   ([Deriving the verifying keys](../crates/proof-compression/README.md#deriving-the-verifying-keys)).
4. Run `bash tools/ixvm/check-formal.sh`, which proves and verifies IxVM,
   recursion and aggregation under the new parameters.

For measurements, `compare` (`crates/stark-verifier/examples/compare.rs`)
takes `--parameters LOG_BLOWUP,QUERIES,COMMIT_POW,QUERY_POW`, and
`--below-floor` for weaker settings.

## Choosing the parameters

Candidate sets with at least the default's 220 conjectured bits, measured on
2026-11-07 at `b919c570` on a 64-core Xeon 6975P-C, CPU only, with the box to
itself (`compare --parameters`). Each row proves IxVM's `Nat.add_comm` claim,
then runs the recursive verifier on that proof and proves it, both under the
row's parameters. Security is each regime's weakest term on the recursive
verifier's instance. #678's original setting is the first row, for reference.

| log_blowup, queries, commit PoW, query PoW | Conjectured query bits | IxVM prove (s) | IxVM proof (MB) | Recursion cells (M) | Recursion FFT cost (G) | Recursion prove (s) | Recursion peak RSS (GB) | Recursion proof (MB) | Unique decoding | Johnson (BCHKS25 / DKT26) | Conjectured |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1, 64, 0, 0 | 64 | 0.49 | 6.00 | 930 | 142 | 20.7 | 45.8 | 3.17 | 26.6 | 31.9 / 31.9 | 62.3 |
| **2, 100, 0, 20 (default)** | 220 | 0.69 | 9.20 | 1,037 | 160 | 29.4 | 71.1 | 4.88 | 87.8 | 80.3 / 82.9 | 92.2 |
| 1, 200, 0, 20 | 220 | 0.56 | 17.90 | 1,839 | 292 | 39.9 | 82.9 | 9.36 | 92.2 | 81.0 / 83.8 | 92.2 |
| 3, 67, 0, 20 | 221 | 0.92 | 6.32 | 944 | 144 | 40.1 | 111.7 | 3.39 | 75.6 | 77.8 / 80.9 | 92.2 |
| 4, 50, 0, 20 | 220 | 1.36 | 4.84 | 929 | 141 | | | | 65.6 | 75.3 / 78.9 | 92.2 |
| 2, 96, 0, 28 | 220 | 6.59 | 8.85 | 1,032 | 159 | | | | 91.8 | 80.3 / 82.9 | 92.2 |
| 2, 100, 16, 20 | 220 | 0.75 | 9.20 | 1,037 | 160 | | | | 87.8 | 80.3 / 82.9 | 92.2 |

- The conjectured regime is the same for every set: the lookup term, which the
  field sets, limits it.
- A larger blowup (`log_blowup` 3 or 4) shrinks IxVM proofs by up to 47 % and
  the recursive verifier by up to 10 %. It costs the inner prover time and
  memory, and the recursive proof under blowup 8 took 36 % longer and 57 %
  more memory. It also loses 2.5 to 22 provable bits, because the Johnson
  batching term and the unique-decoding query term both weaken as the rate
  falls.
- `log_blowup` 1 with 200 queries is provably slightly stronger. It doubles the
  recursive verifier's queries: 77 % more cells, a 36 % slower recursive
  proof and proofs twice as large.
- Moving 4 queries into 8 more bits of query proof of work gains 4 provable
  bits under unique decoding and saves under 1 % of the recursive verifier,
  but grinding 2^28 adds about 6 s to every proof.
- Commit-phase proof of work only strengthens the commit term, which limits no
  regime here.

No candidate is clearly better at equal or better security, so the default
stays at main's parameters. `Nat.add_comm` is small; on large claims the
inner prover's LDE, and so its time and memory, grows with `2^log_blowup`,
which weighs further against a larger blowup.
