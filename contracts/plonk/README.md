# ix PLONK Solidity adapter

`IxPlonkVerifier` binds a caller-supplied expected claim digest to two
little-endian 128-bit public inputs and calls a fixed gnark verifier address.
The gnark key fixes the complete BLS12-381 wrapper circuit, including both
inner pairing obligations. The contract requires EIP-2537 support.

Use `PlonkVerifier.sol` and `proof.solidity.bin` emitted by the helper for the
reviewed wrapper key. Deploy the generated verifier and pass its address to
the adapter constructor. Applications must select the intended adapter and
derive the expected digest independently of the proof. A successful call must
return `true`.

The conformance tests use a tiny Filecoin-backed PLONK circuit to test the
backend, public-input packing and precompiles. They do not prove an ix claim.
Generate those fixtures explicitly, then run Foundry:

```sh
cd tools/bls-plonk-wrapper
IX_PLONK_TEST_OUTPUT=../../contracts/plonk/generated \
  go test -run TestFilecoinBackendAndProofCodec -count=1
cd ../..
forge test --root contracts/plonk -vv
```

The pinned test configuration uses solc 0.8.37, via-IR, 200 optimizer runs,
Prague bytecode and Osaka execution rules. Keep deployment, external-call gas
and total transaction gas separate in benchmark results. The target for a full
wrapper transaction is at most 500k gas and at least 25% below the validated
optimized direct verifier.
