# Compression stage boundaries

The supported pipeline is an aggregate root proof, a Goldilocks/Blake3 FRI
proof, a BN254 KZG proof, recursive BN254 KZG, and an optional PLONK or Groth16
final proof. The final systems share the same inner KZG verifier relation.

The recursive KZG stage reduces the first stage's many commitments and openings
before translating its verifier into gnark constraints. Keep that boundary until
an actual first-stage packet has been exported, compiled directly for the chosen
final backend, and measured within the required security and memory limits.
Measurements of the recursive Init wrapper do not establish the cost of wrapping
the first stage directly.

## Execution and trust boundaries

`pipeline::compress` runs the stages in-process with explicit inputs and
configuration. Stage directories retain checked checkpoints for resumption.
Final features link one gnark C archive into `ix`; a loaded prover retains
its circuit, keys and optional device allocations across calls.

KZG and PLONK share a BN254 CUDA library built against sppark. Groth16 uses
installed ICICLE libraries. Cargo reports each runtime artifact to Lake for
packaging alongside the executable.

PLONK uses admitted Ignition parameters. Groth16 needs its own circuit-specific
setup. Both final proof types require independently authorized verifier keys;
a generated candidate catalog does not grant that authorization. Explicit KZG
verification requires a pinned key and expected statement.

## Parameter research

Inspect keys through the Rust decoder before calculating candidate security
bounds:

```sh
cargo run --release -p ix-proof-compression --no-default-features \
  --features parallel --example fri_sizing -- --statistics outer-vk.bin | \
  python3 tools/compression/fri_security_estimate.py -
```

The `fri_sizing` example estimates candidate frontend layouts. Materializing the
full lowering with `FRI_SIZING_LOWER=1` can require tens of GiB. Candidate query
counts and trace layouts are research inputs; performance comparisons must retain
the same security requirement. The calculator reports individual terms and the
assumptions of each regime.

[Operational setup and commands](../crates/proof-compression/README.md),
[final backends](../tools/plonk-wrapper/README.md), and
[revision-labelled measurements](proof-benchmark-comparison.md) are maintained
separately. Detailed stage-collapse experiments are preserved in Git history at
`7b9a7f21`.
