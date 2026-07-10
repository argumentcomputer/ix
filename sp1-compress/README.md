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

## `ix compress` (integrated CLI)

The `ix` CLI drives the same guest through FFI when built with the `sp1`
feature (`IX_SP1=1 lake build`):

```bash
ix prove Nat.add_comm            # → proof address in ~/.ix/store
ix compress <proof-hex> --mode compressed --output nat.sp1
```

## Cargo features (host crate / ix-ffi / lake env)

| host feature | ix-ffi feature | lake env         | effect |
|--------------|----------------|------------------|--------|
| —            | `sp1`          | `IX_SP1=1`       | SP1 compression compiled in (CPU prover) |
| `cuda`       | `sp1-cuda`     | `IX_SP1_CUDA=1`  | GPU prover available; select at runtime with `SP1_PROVER=cuda`. Auto-downloads `sp1-gpu-server` to `~/.sp1/bin` on first prove (needs NVIDIA driver, no Docker). |
| `portable`   | `sp1-portable` | `IX_SP1_PORTABLE=1` | Portable executor + cycle tracker, for sandboxes whose `/dev/shm` is too small for the native JIT executor (SIGBUS). Slower; don't use on real machines. |

## Setup on a fresh machine

```bash
# 1. SP1 guest toolchain + protoc
curl -L https://sp1up.succinct.xyz | bash && ~/.sp1/bin/sp1up
sudo apt-get install -y protobuf-compiler
export PATH="$HOME/.sp1/bin:$PATH"

# 2. Build ix with SP1 + CUDA support
IX_SP1_CUDA=1 lake build ix

# 3. Prove and compress on GPU
lake exe ix prove Nat.add_comm
SP1_PROVER=cuda lake exe ix compress <proof-hex> --mode compressed --output nat.sp1
```

Memory-constrained CPU proving can be throttled with
`SP1_WORKER_NUM_CORE_WORKERS=1 SP1_WORKER_CORE_BUFFER_SIZE=1
SP1_WORKER_NUM_DEFERRED_WORKERS=1` (defaults 4/4/4).

## Measured (July 2026)

- Demo (2-function Aiur program): inner proof 817 KB → guest 60.5M cycles
  (Keccak precompile; 215M without) → SP1 compressed proof 1.27 MB, ~20 min
  on a memory-throttled 16-core CPU.
- Real `ix prove Nat.add_comm` kernel proof: inner proof 33.6 MB, vk 8.3 MB
  (728-circuit system) → guest verifies in 3.56B cycles (`--mode execute`).
  CPU-proving that is impractical (~day); use CUDA or the prover network.
- Guest cycles are dominated by Goldilocks/extension-field arithmetic
  (constraint evaluation across all circuits + FRI folding at
  `num_queries = 100, log_blowup = 1`), not hashing. A recursion-friendly
  inner FRI config (higher blowup, fewer queries) is the main lever.
