# Proof compression

`fri` builds a constrained multi-stark FRI verifier. `foreign` translates its
Goldilocks circuit into scalar-field constraints. `kzg` implements the commitment
backend; `recursive` builds the next KZG verifier with public pairing operands.
All circuits use the multi-stark Plonkish API.

From the workspace root:

```sh
cargo test --release -p ix-proof-compression
cargo run --release -p ix-proof-compression --bin init_fri -- ROOT_EXPORT OUTER_FRI --prove-outer
cargo run --release -p ix-proof-compression --bin init_fri_kzg -- stage OUTER_FRI FIRST_KZG 25
cargo run --release -p ix-proof-compression --bin init_fri_kzg -- prove FIRST_KZG --resident
cargo run --release -p ix-proof-compression --bin init_kzg_wrap -- stage FIRST_KZG FINAL_KZG
cargo run --release -p ix-proof-compression --bin init_kzg_wrap -- prove FINAL_KZG --resident
cargo run --release -p ix-proof-compression --bin init_kzg_wrap -- verify FINAL_KZG
```

`ROOT_EXPORT` contains `root-vk.bin`, `root-proof.bin`, and `root-claims.bin`.
The Init commands require the fixed 18-word Init statement. `init_fri` also accepts
`--native-only` and `--check-only`. The first KZG stage accepts log heights 24–28;
25 is the measured six-partition configuration. The final stage currently accepts
first-stage profiles 24 and 25. Omit `--resident` to use disk
checkpoints. Staging invokes `zstd`; full proving needs hundreds of GiB of RAM.

The measured final packet is 2,757 bytes, including the public claim and pairing
operands. Verification must check both the outer proof and the external pairings.
Verifier keys and expected statements must come from the verifier, not the proof.

The commands use a **known-trapdoor development SRS**. Their proofs are not
production-secure; a validated trusted SRS and a security review remain necessary.
The saved FRI fixture exercises the unchanged Init public statement in CI.
