# sp1-compress

Compresses Aiur multi-STARK proofs by verifying them inside an [SP1](https://github.com/succinctlabs/sp1)
zkVM guest and recursively proving that verification. The multi-STARK proofs the
Ix pipeline produces are megabytes; SP1's `compressed` mode yields a
constant-size proof, and `groth16`/`plonk` yield onchain-sized ones.

This is distinct from `../sp1`, which runs the Ix kernel typechecker itself
inside the guest. Here the guest runs the `multi-stark` *verifier* over a
proof produced outside the zkVM.

## Layout

- `guest/` — SP1 program: decodes the Aiur verifying key
  (`aiur::vk_codec` format), the FRI parameters, the claim, and the proof from
  prover input; runs `multi-stark` verification; commits
  `blake3(vk) || fri_params || claim` as public values. Built by `sp1-build`
  for `riscv64im-succinct-zkvm-elf` (needs the succinct toolchain via `sp1up`).
- `host/` — CLI driving the SP1 SDK.

## Usage

```bash
# End-to-end demo: hand-built Aiur program → multi-STARK proof → SP1 proof.
cargo run --release -- demo --mode compressed

# Emulate only (cycle counts, no proving):
cargo run --release -- demo --mode execute

# Compress artifacts produced by the real pipeline:
cargo run --release -- compress --vk vk.bin --claim claim.bin --proof proof.bin
```

Artifact formats: `--vk` is `aiur::vk_codec::aiur_system_to_bytes` output;
`--claim` is one canonical little-endian `u64` per Goldilocks element
(`[function_channel, fun_idx, inputs.., outputs..]`); `--proof` is
`multi_stark::prover::Proof::to_bytes` output. `demo --save-artifacts DIR`
writes examples of all three.

FRI parameter flags default to the canonical `ix prove` values
(`Ix/Cli/ProveCmd.lean`) and must match the proving side.

The final SP1 proof's public values bind the vk digest, FRI parameters, and
claim; a consumer must check those against known-good values, plus the SP1
verifying key of this guest.

`groth16`/`plonk` modes additionally need Docker (or an SDK built with
`native-gnark`) for the gnark wrapper.
