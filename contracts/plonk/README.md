# ix PLONK Solidity adapter

`IxPlonkVerifier` binds a caller-supplied expected claim digest to two
little-endian 128-bit public inputs and calls a fixed gnark verifier address.
The gnark key fixes the complete wrapper circuit, including both inner pairing
obligations. BN254 uses Ethereum's BN254 precompiles.

`src/PlonkVerifier.sol` is gnark's own Solidity export of the bundled release
key, `crates/proof-compression/verifying-keys/0.1/plonk-verifying-key.bin`.
Regenerate it from the repository root whenever that key changes:

```sh
go -C tools/gnark run ./cmd/solidity -system plonk \
  -key ../../crates/proof-compression/verifying-keys/0.1/plonk-verifying-key.bin \
  -out ../../contracts/plonk/src/PlonkVerifier.sol
```

Deploy the generated verifier and pass its address to the adapter
constructor. Applications must select the intended adapter and derive the
expected digest independently of the proof. Proofs use gnark's
`MarshalSolidity` encoding; the native and envelope encodings are rejected. A
successful call must return `true`.

The tests use the proof in `testdata/init.json`, whose `verifyingKeySHA256`
must match the release key. They cover acceptance, changed digests, malformed
proofs and deployment-size limits:

```sh
forge test --root contracts/plonk -vv
```

The pinned test configuration uses solc 0.8.37, via-IR, 200 optimizer runs,
Prague bytecode and Osaka execution rules. Keep deployment, external-call gas
and total transaction gas separate in benchmark results.
