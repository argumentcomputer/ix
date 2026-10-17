# ix PLONK Solidity adapter

`IxPlonkVerifier` binds a caller-supplied expected claim digest to two
little-endian 128-bit public inputs and calls a fixed gnark verifier address.
The gnark key fixes the complete wrapper circuit, including both inner pairing
obligations. BLS12-381 uses EIP-2537; BN254 uses Ethereum's BN254 precompiles.

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

## Actual BN254 Init proof on Anvil

The actual `2^24` BN254 Init proof passes the adapted SP1 v6.1.0 PLONK verifier
and the ix claim-digest adapter on local Anvil. This uses the 14,689,440-constraint
classic-GLV circuit with both inner pairing checks, not the tiny backend fixture.

The untouched SP1 verifier rejects the proof. Its fixed circuit key uses five
public inputs and domain `2^25`; ix uses two inputs and domain `2^24`. The test
also supplies five inputs to the stock low-level verifier and correctly framed
SP1 selector/exit-code/vk-root/nonce bytes to its high-level facade. Those paths
reject cryptographically; the facade returns `InvalidProof()`.

Only **23 `VK_*` constants** differ between the adapted contract and SP1's
low-level contract: public-input count, domain/inverse/root, circuit commitments
and the commitment-API index. The verification algorithm, SRS anchors, proof
layout and transcript logic are unchanged. With the pragma normalized, the
adapted source equals the verifier emitted by our pinned gnark helper byte for
byte. The existing ix adapter supplies the two little-endian 128-bit limbs of
the independently expected claim digest, instead of SP1's five-field public
statement mapping. The proof itself is unchanged.

Source: [SP1 v6.1.0 verifier](https://github.com/succinctlabs/sp1-contracts/blob/d3629729c3216eb51bd4859d027a8eb729399fa4/contracts/src/v6.1.0/PlonkVerifier.sol).
The original sources, licenses and hashes are retained under `bn254/upstream`;
`bn254/provenance.json` records every changed constant and the authenticated ix
key/proof identities. `bn254/src/PlonkVerifier.sol` is specific to this
benchmark circuit, not an interchangeable SP1 verification key.

### Receipt measurements

Measured on 2026-10-17 with Foundry/Anvil 1.8.5, solc 0.8.37, via-IR, optimizer
200 runs, Prague bytecode and Osaka execution rules. Deployment-size limits
were enabled. These are mined transactions on a fresh local chain:

| Path | Execution gas | Intrinsic/calldata gas | Total receipt gas | ABI calldata |
| --- | ---: | ---: | ---: | ---: |
| Adapted SP1 `Verify(bytes,uint256[])` | 279,915 | 36,088 | **316,003** | 1,060 bytes |
| ix `verify(bytes,bytes32)` adapter | 284,435 | 35,668 | **320,103** | 964 bytes |

The Solidity proof is **864 bytes**. The native 584-byte encoding and 624-byte
ix envelope are storage/interchange formats and are rejected by this Solidity
interface. Both successful calls return `true`; transaction traces confirm the
return value as well as the receipt status. The totals exceed the EIP-7623
calldata floor, so the execution/intrinsic split above applies.

The adapted verifier has **7,531 bytes** of runtime code and **7,557 bytes** of
initcode; deployment used **1,681,283 gas**. The adapter has **913 runtime bytes**
and **1,159 initcode bytes including its constructor argument**; deployment used
**255,356 gas**. All fit ordinary EIP-170/EIP-3860 limits. These deployment costs
are excluded from verification gas.

The valid trace calls SHA-256 nine times, MODEXP six times, BN254 scalar
multiplication 21 times, BN254 addition 21 times and the two-pair BN254 pairing
precompile once. Their combined precompile gas is 257,366. Both inner pairing
obligations are already constrained by the PLONK circuit; no extra application
pairing calls are required.

All **47 acceptance/rejection checks passed**: stock-key incompatibility,
positive raw/adapter verification, both digest halves, swapped/missing/extra or
noncanonical public inputs, empty/truncated/trailing proofs, wrong proof formats,
mutations of all 27 proof words, and noncanonical point/scalar encodings. Every
call uses the same 2M gas bound, including the positive controls. The test uses
only an isolated local Anvil chain and shuts down its own node after completion.

### Reproduce

Use the hash-pinned Foundry and Solidity binaries documented in
[`../kzg/README.md`](../kzg/README.md#run-local-checks). No prover, proving key,
SRS download or new proof generation is needed:

```sh
python3 contracts/plonk/bn254/bench.py \
  --tools target/toolchains/solidity \
  --out target/plonk-evm/replay
```

The output directory must be new. Compilation input/output, deployment and
verification receipts, call traces, negative-call results and the Anvil log are
saved there. The completed run is `target/plonk-evm/run-final/report.json`.
This validates the exported circuit key and fixture; production applications
still select their intended key and obtain the expected digest independently.
