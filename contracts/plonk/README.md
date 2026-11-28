# ix PLONK Solidity adapter

`IxPlonkVerifier` binds a caller-supplied expected claim digest to two
little-endian 128-bit public inputs and calls a fixed PLONK verifier address
pinned by its `codehash`. `IxL3PlonkVerifier` additionally computes the
aggregate claim digest from `(claim_bytes, proof_key_digest)` in-contract via
BLAKE3 before delegating to the pinned PLONK verifier. BLS12-381 uses Pectra
EIP-2537 precompiles (`0x0c`, `0x0f`); BN254 uses Ethereum's EIP-196/197 BN254
precompiles (`0x06`, `0x07`, `0x08`).

## Archival status of `src/PlonkVerifier.sol` (Release 0.5)

`src/PlonkVerifier.sol` is the **archived Release 0.5** BN254 PLONK verifier
targeting `crates/proof-compression/verifying-keys/0.5/plonk-verifying-key.bin`
(`vk_version = 7`, pre-key-bound KZG). It is retained for historical regression
testing against `testdata/nat-add-comm.json` and as the BN254 EIP-196/197 body
template embedded by the native Rust PLONK exporter; **it rejects all Release
0.6 proofs and must not be deployed for Release 0.6 keys**.

## Exporting verifiers with the native Rust PLONK exporter

Go/gnark tooling (`tools/gnark`) has been removed. Generate fresh BN254
(EIP-196/197) or BLS12-381 (Pectra EIP-2537) PLONK verifiers directly in pure
Rust via `crates/proof-compression/src/aiur_backend/plonk/native/solidity.rs`:

- Library API: `ix_proof_compression::aiur_backend::plonk::native::prepare_to_dir`
  (writes `verifying-key.bin`, `proving-key.bin`, `inputs.json`, `manifest.json`,
  and the exported Solidity verifier) or `export_solidity(&vk)` paired with
  `solidity_filename_for_vk(&vk)`.
- Standalone CLI example (for self-contained `outputs == 0` `.ixscs` circuits):

```sh
cargo run --release -p ix-proof-compression --example native_plonk_prove -- \
  path/to/circuit.ixscs --curve bn254 --out out-dir
```

Pass `--curve bls12-381` for Pectra EIP-2537 `Bls12381PlonkVerifier.sol`.
Development trapdoor SRS setups always emit a renamed contract
(`PlonkVerifier_DEV_INSECURE_DO_NOT_DEPLOY`) to `PlonkVerifier.DEV_INSECURE.sol`
/ `Bls12381PlonkVerifier.DEV_INSECURE.sol` and must never be deployed. Native
PLONK-SCS requires self-contained `outputs == 0` circuits (deferred `scs.outputs`
are rejected fail-closed).

## Deployment & verification

Deploy the generated verifier and pass its address and `codehash` to the adapter
constructor (`IxPlonkVerifier` or `IxL3PlonkVerifier`). Applications must select
the intended adapter and derive the expected digest independently of the proof.
Proofs use the gnark-compatible `MarshalSolidity` encoding (`proof.solidity.bin`);
native (`IXNPPR01`) and envelope encodings are rejected. A successful `verify`
call returns `true`.

## Foundry tests

The BN254 tests use the archived Release 0.5 fixture in
`testdata/nat-add-comm.json`, whose `verifyingKeySHA256` must match
`crates/proof-compression/verifying-keys/0.5/plonk-verifying-key.bin`. The
BLS12-381 tests use `testdata/bls12-381/Bls12381PlonkVerifier.sol` and
`testdata/bls12-381/proof.json`. The test suites cover acceptance, changed
digests, malformed proofs, raw-verifier negative controls (unreduced inputs
`input + R_MOD`, all-zero proofs, and BLS12-381 non-subgroup torsion points),
gas griefing, and deployment-size limits:

```sh
forge test --root contracts/plonk -vv
```

The pinned test configuration uses solc 0.8.37, via-IR, 200 optimizer runs,
Prague bytecode and Osaka execution rules. Keep deployment, external-call gas
and total transaction gas separate in benchmark results.
