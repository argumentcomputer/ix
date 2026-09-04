# SP1 aggregate-root compressor

This directory contains the terminal connector for the aggregate-first
pipeline. It verifies one persisted `ix_aggr` recursion proof inside SP1 and
then uses SP1's stock recursion tail to produce a final Groth16 or Plonk SNARK.
It does not re-run the Lean kernel and it does not batch shard proofs: stage 2
has already reduced the complete computation to one root.

The guest accepts exactly one Aiur verifying key, the canonical recursion FRI
parameters, one 18-word `ix_aggr` outer claim, and one compact Multi-STARK
proof. Its public values are fixed at 224 bytes:

```text
"IXROOT01" || blake3(aiur_recursion_vk) || fri_parameters || outer_claim
```

Both the host and guest decode and verify the proof. The host check fails fast;
the repeated guest check is what the SP1 proof attests to.

## Integrated command

The repository's `sp1` Nix shell supplies `protoc` and the Succinct Rust
toolchain used by `sp1-build`. Run the CLI with the optional connector on an
aggregate proof address from the Ix store. Keep `IX_SP1=1` (or
`IX_SP1_CUDA=1`) on every `lake` invocation: Lake rebuilds the Rust archive as
part of `lake exe`.

```console
nix develop .#sp1 --command env IX_SP1=1 lake build ix

# Small box-independent guest/wire smoke (synthetic 18-word Aiur claim).
nix develop .#sp1 --command cargo run --release \
  --manifest-path sp1-compress/Cargo.toml --example execute_smoke

# CPU emulation: validates the complete guest/wire path and prints cycles.
nix develop .#sp1 --command env IX_SP1=1 \
  lake exe ix compress-root ROOT_ADDRESS --mode execute

# Final Groth16 proof. The SDK artifact retains public values and can be
# re-verified by SP1; the raw file is the onchain proof encoding.
nix develop .#sp1 --command env IX_SP1_CUDA=1 \
  WITHOUT_VK_VERIFICATION=1 SP1_PROVER=cuda \
  lake exe ix compress-root ROOT_ADDRESS --mode groth16 \
    --output root.sp1 --onchain-output root.groth16
```

`WITHOUT_VK_VERIFICATION=1` is currently required for proof generation because
the repository's SP1 fork adds Blake3 recursion shapes not yet present in its
distributed vk map. Execute mode does not need the bypass. The command always
natively verifies the aggregate root before starting SP1, verifies the final
SP1 proof after proving, and checks the guest public values against an
independent host reconstruction.

The synthetic smoke above passed on 2026-08-30 at 4,272,596 instructions
(3,987,232 gas), including 891 `blake3_compress` precompile calls. Those
numbers validate the connector only; they are not an estimate for the much
larger production `ix_aggr` verifier key and proof.

The `sp1-compress/guest` and root Cargo dependencies deliberately pin the same
`multi-stark` revision, and the SP1 crates are pinned to fork commit
`7a1cefe5ff8aba1c9dc5a69d3687a57aa5991e0a` (SP1 v6.6 plus the Blake3
precompile). The guest's SP1-aware Blake3 is
likewise pinned at `d36366f7badbff9be8e2522868dddd14561638f3`. Proof and
verifying-key encodings are revision-sensitive; do not update one without the
others.
