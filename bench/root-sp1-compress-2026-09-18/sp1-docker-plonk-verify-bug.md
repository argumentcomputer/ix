# SP1: Docker backend rejects every Plonk proof it produces

Upstream defect found on 2026-09-18 while compressing Ix roots; present in
SP1 v6.6.0 and on `main` at the time of writing.

## Symptom

`ProverClient` with `SP1_PROVER=cpu` (or any prover that wraps through the
Docker gnark backend) in `.plonk()` mode fails after the wrap stage with

```text
task failed with fatal error: Failed to verify plonk wrap proof: failed to verify proof: algebraic relation does not hold
Controller: task failed: Fatal(artifact not found)
```

The second line is what the SDK surfaces; the first is visible only with a
tracing subscriber installed. Groth16 mode through the same backend works.

## Cause

`crates/recursion/gnark-ffi/src/ffi/docker.rs`:

```rust
pub fn verify_plonk_bn254(
    data_dir: &str, proof: &str, vkey_hash: &str, committed_values_digest: &str,
    exit_code: &str, vk_root: &str, proof_nonce: &str,
) -> Result<()> {
    verify(ProofSystem::Plonk, data_dir, proof, vkey_hash, committed_values_digest,
        exit_code,
        proof_nonce,   // <- `verify` expects `vk_root` here
        vk_root,       // <- and `proof_nonce` here
    )
}
```

`verify_groth16_bn254` in the same file passes `vk_root, proof_nonce` in the
right order, as does `ffi/native.rs` for both systems. The captured command
line of the failing verify shows the swap directly:

```text
verify --system plonk ... --exit-code 0 --proof-nonce 8396014634849681418319559... --vk-root 0
```

where the witness the proof was made from has `vk_root = 8396…` and
`proof_nonce = 0`. CI does not catch it because `.github/workflows/gnark.yml`
runs `test_e2e_plonk` with `--features native-gnark`, and the Docker workflow
tests only `test_e2e_node_groth16`.

## Reproduction without the SDK

With the stock v6.1.0 Plonk artifacts in `~/.sp1/circuits/plonk/v6.1.0` and
any witness `w.json` written by `build_constraints_and_witness`:

```console
docker run --rm -v ~/.sp1/circuits/plonk/v6.1.0:/circuit -v $PWD/w.json:/witness \
  -v $PWD/out.bin:/output ghcr.io/succinctlabs/sp1-gnark:v6.1.0 \
  prove --system plonk /circuit /witness /output
# extract raw_proof from the bincode ProofBn254::Plonk in out.bin, then:
docker run --rm ... verify --system plonk --data-dir /circuit --proof-path /proof \
  --vkey-hash $VKEY --committed-values-digest $CVD --exit-code $EC \
  --proof-nonce $PROOF_NONCE --vk-root $VK_ROOT --output-path /output   # OK
docker run --rm ... verify ... --proof-nonce $VK_ROOT --vk-root $PROOF_NONCE ...   # algebraic relation does not hold
```

## Fix

Swap the two arguments in `verify_plonk_bn254` of `ffi/docker.rs`. Until
then, build with `sp1-sdk/native-gnark`, which this repository does.
