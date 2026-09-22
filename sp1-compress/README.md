# SP1 aggregate-root compressor

This directory contains the terminal connector for the aggregate-first
pipeline. It verifies one persisted `ix_aggr` recursion proof inside SP1 and
then uses SP1's stock recursion tail to produce a final Groth16 or Plonk SNARK.
It does not re-run the Lean kernel and it does not batch shard proofs: stage 2
has already reduced the complete computation to one root.

The guest accepts exactly one Aiur verifying key, the canonical recursion FRI
parameters, one 18-word `ix_aggr` outer claim, and the root's batch proof: a
vector of trace-shard Multi-STARK proofs under one preamble (`K = 1` when the
root was proven unsharded). The guest verifies the batch as the native
verifier does — shard headers, Aiur's batch policy and the residual sum with
the `memseg` boundary terms — so a root proven on GPUs with `ix prove
--trace-shards` compresses unchanged. Its public values are fixed at 224
bytes:

```text
"IXROOT01" || blake3(aiur_recursion_vk) || fri_parameters || outer_claim
```

Both the host and guest decode and verify the proof. The host check fails fast;
the repeated guest check is what the SP1 proof attests to.

## Integrated command

The repository's `sp1` Nix shell supplies `protoc` and the Succinct Rust
toolchain used by `sp1-build`. The host links gnark natively
(`sp1-sdk/native-gnark`), which needs Go 1.24+ and libclang at build time and
no Docker at run time. Do not switch the host back to SP1's Docker backend for
Plonk: in SP1 v6.x its Plonk verify wrapper forwards `proof_nonce` and
`vk_root` in swapped order (`crates/recursion/gnark-ffi/src/ffi/docker.rs`,
`verify_plonk_bn254`), so a correct Plonk proof is rejected right after it is
produced; the Groth16 wrapper and the native backend are correct, and
upstream CI exercises Plonk only natively. Run the CLI with the optional connector on an
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

# Final Plonk proof. The SDK artifact retains public values and can be
# re-verified by SP1; the raw file is the onchain proof encoding.
nix develop .#sp1 --command env IX_SP1_CUDA=1 SP1_PROVER=cuda \
  lake exe ix compress-root ROOT_ADDRESS --mode plonk \
    --output root.sp1 --onchain-output root.plonk
```

The connector uses upstream SP1: the guest hashes with Blake3 in software, so
the stock recursion key map and Succinct's published Plonk and Groth16
circuits apply and nothing custom is trusted. Plonk is the production
target: its circuit is built on the universal Aztec Ignition SRS, whereas
Groth16's per-circuit setup is only as trustworthy as Succinct's ceremony.
The command always natively verifies the aggregate root before starting SP1,
verifies the final SP1 proof after proving, and checks the guest public
values against an independent host reconstruction.

The synthetic smoke above passed on 2026-08-30 at 4,272,596 instructions
(3,987,232 gas), including 891 `blake3_compress` precompile calls. Those
numbers validate the connector only; they are not an estimate for the much
larger production `ix_aggr` verifier key and proof.

The `sp1-compress/guest` and root Cargo dependencies deliberately pin the same
`multi-stark` revision, and the SP1 crates are pinned to upstream tag
`v6.6.0`. The guest links only under the Succinct toolchain of that SP1
release (`sp1up --version v6.6.0`, rustc 1.94.0-dev); the toolchain shipped
with SP1 v6.8 fails the link with undefined `__atomic_*` builtins. Proof and
verifying-key encodings are revision-sensitive; do not update one without the
others.

The Blake3 precompile of the `argumentcomputer/sp1` fork saves 19% of the
guest's cycles (580 M against 691 M for a production root, measured
2026-09-18) but changes every recursion program: its key map must be
regenerated (191,670 shapes, about 50 hours on 64 cores) and its Plonk and
Groth16 circuits rebuilt for the resulting wrap key before any proof it makes
is sound. The `guest-mathlib-2026-09-03` compatibility guest keeps its fork
pin.
