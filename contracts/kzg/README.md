# Solidity KZG verifier prototype

This package verifies ix's two-circuit v5 KZG packets for caller-selected Lean
library statements, with a Keccak transcript and Ethereum's BLS12-381
precompiles. It checks the scalar constraint and
LogUp identities, the outer KZG opening equation, and the separate pairing
equation deferred from the inner proof.

**The checked-in `GeneratedVerifier.sol` is a small conformance-test circuit,
not a Lean library verifier.** Its traces have 32 and 16 rows and prove a lookup,
`private * private = 49`, and binding of the public values. It uses authentic
Filecoin parameters and the same 2,181-byte packet layout, but it does not
prove a Lean library computation. A library verifier must be generated from
the trusted portable profile for its proof circuit. Library values are public
inputs, not embedded constants: one verifier accepts different statements
that its pinned circuit/profile permits. Different proof geometries or
circuits can require different authenticated verification keys.

The implementation is a prototype. It has local native/EVM conformance tests;
it has not been independently audited or deployed on a public chain.

## Interface and encoding

```solidity
function verify(
    bytes calldata packet,
    bytes calldata yHints,
    uint64[18] calldata expectedClaim
) external view returns (bool);
```

`packet` is the native `kzg/packet.bin`, without the `IXCMP` storage envelope.
It contains the profile ID, 18 little-endian public words, two compressed
deferred pairing operands, and the `KQP4` proof. The generated contract pins
the profile, fixed commitments and setup anchors. `expectedClaim` is the
application's independently expected 18-word library statement. The contract
requires an exact match with the packet and binds those values into proof
verification. Applications must use the intended verifier address and obtain
`expectedClaim` from trusted application state, not copy it from an untrusted
proof. No library-specific public words are hardcoded in the contract.

`yHints` supplies a 48-byte big-endian y coordinate for each variable G1 point:
deferred A, deferred B, then the proof's main, LogUp, quotient and opening
points. The contract checks canonical coordinates, compression flags,
lexicographic sign and infinity, and passes every point through a subgroup
checking precompile. Infinity has a zero hint. Hints do not change the
transcript: it absorbs the original canonical compressed bytes.

The fixture requires 816 hint bytes, for 2,997 payload bytes or 3,748 bytes
including the Solidity ABI, function selector and expected statement.
Noncanonical scalars and encodings, wrong profiles/claims, and failed scalar identities revert. A
well-formed failing pairing returns `false`; acceptance requires `true`.

## Generate native fixtures

Run from the ix repository root:

```sh
cargo run --release --locked -p ix-proof-compression \
  --features solidity --example solidity_export -- \
  fixture contracts/kzg/testdata contracts/kzg/src/GeneratedVerifier.sol
forge fmt --root contracts/kzg
```

This uses the checked-in 256-power Filecoin cache and its pinned import
receipt. It generates three tiny proofs. The two positive fixtures use
different synthetic library statements under the same verification key.
`fixture-other-statement.json` exercises the second statement; exchanging
the expected claims between these proofs must fail.
`fixture-bad-pairing.json` has a valid outer proof under the same circuit/profile but fails the deferred pairing.
Each JSON file includes native transcript challenges and folded opening
points. The generated source and JSON explicitly identify the test-only scope.

The exporter is behind `solidity`; normal prover builds do not include
its fixture generation or Solidity code generation.

## Export an existing library profile

```sh
cargo run --release --locked -p ix-proof-compression \
  --features solidity --example solidity_export -- \
  export /path/to/final-kzg/verifier.bin \
    /path/to/final-kzg/kzg/packet.bin TRUSTED_VERIFIER_BLAKE3 \
    /path/to/output /path/to/output/GeneratedVerifier.sol
```

The verifier digest must come from a trusted source. The exporter checks it,
decodes a v5 profile, and verifies the complete packet for its carried
statement before writing contract constants and test vectors. The exported
contract accepts an independently expected statement at each verification
call; the packet's values do not become contract constants. It supplies all
verifier data from the portable key; proving powers and checkpoint traces are not needed. Place the
generated contract beside `KzgVerifier.sol` and its libraries in a separate
Foundry project to evaluate that profile without replacing these test fixtures.

The repository includes a real aggregate Filecoin profile and proof. Export
them without downloading proving parameters or running the prover:

```sh
cargo run --release --locked -p ix-proof-compression \
  --features solidity --example solidity_export -- \
  export crates/proof-compression/profiles/aggregate-filecoin-v5.bin \
    crates/proof-compression/tests/fixtures/aggregate-kzg/filecoin-v5-packet.bin \
    8779b34ad026a9e7075c253f036f50e553348b9d3f5c7baab21ddf487301d7cb \
    /path/to/output /path/to/output/GeneratedVerifier.sol
```

The digest is pinned in the native verifier catalog and the adjacent profile
JSON records the proof's provenance. For this profile, derive `expectedClaim`
from its authenticated ten-word aggregation-program prefix followed by the
BLAKE3 digest of the serialized application claim, packed as eight
little-endian `uint32` words. The checked-in serialized claim is
`crates/proof-compression/tests/fixtures/aggregate-kzg/filecoin-claim.bin`.
The export's `expectedClaim` field describes the packet; it does not replace
independent statement derivation by the application.

## Run local checks

The tested toolchain is Foundry 1.8.5 and solc 0.8.37. `foundry.toml` targets
Prague bytecode and executes tests under Osaka gas rules. It enables the
optimizer with 200 runs and via-IR compilation, and uses no external Solidity
libraries. The EVM must implement EIP-2537 and EIP-7883 pricing is included.

```sh
forge test --root contracts/kzg --gas-report -vv

cargo test --release --locked -p ix-proof-compression \
  --features solidity --lib pipeline::wrap::outer::solidity::
```

The local prebuilt tools are under `/tmp/ix-solidity-tools/bin`; on this host,
the offline Solidity command is:

```sh
/tmp/ix-solidity-tools/bin/forge test --root contracts/kzg \
  --use /tmp/ix-solidity-tools/bin/solc --offline --gas-report -vv
```

The [official Foundry release](https://github.com/foundry-rs/foundry/releases/tag/v1.8.5)
Linux amd64 archive has SHA-256
`6c66ffcc55fa4249197721baa3098bc208014ea1d8aa04b2ed50ac6bccffb226`.
The [official Solidity release](https://github.com/argotorg/solidity/releases/tag/v0.8.37)
`solc-static-linux` has SHA-256
`5de843c2c93563cc66425c99a4fb13fdbf32b4c4ae07469480faaf126e14404a`.

## Current results

On the checked-in small Filecoin fixture, with the toolchain above:

| Check | Result |
| --- | --- |
| Solidity tests | 47 passed, including three 256-case differential fuzz tests |
| Focused native exporter and code-generation tests, including the bundled aggregate proof | 9 passed |
| Transcript and opening operands | All six challenges and both folded G1 points match Rust |
| Statement binding | One verifier accepts two statements; crossed or changed expected claims are rejected |
| Pairing obligations | Outer-valid/inner-invalid and outer-invalid/inner-valid cases are rejected |
| Valid verification call | 757,950 gas, measured around the external call in the test harness |
| Runtime bytecode | 23,136 bytes, below EIP-170's 24,576-byte limit |
| Deployment bytecode | 23,162 bytes |

The call measurement excludes transaction intrinsic/calldata gas and contract
deployment. The gas-report average includes malformed inputs and is not the
cost of a valid proof. The harness bounds each verifier call to 10M gas; a
positive test with the same limit prevents out-of-gas from masquerading as a
successful rejection. Precompile wrappers separately bound gas forwarded for
malformed points. These are local measurements of this fixture, not a full
Lean library proof or an Ethereum transaction receipt.

The Rust exporter generates direct graph arithmetic, matrix layouts and opening
coefficients from the authenticated profile. Opening groups preserve native
first-occurrence order and merge equal domain roots. Both pairing checks remain
separate, and all variable points retain subgroup validation even when their
MSM coefficients are zero. The fixture's curve precompile charges are 497,148
gas; the remaining 260,802 gas covers decoding, transcript and scalar work,
precompile preparation and external-call overhead.

Verification reuses transcript and MSM buffers, batches all scalar inversions
into one bounded MODEXP call, and decodes scalar spans with one bounds check.
Together these reduce the original fixture measurement from 4,812,808 to
757,950 gas. Regenerating the contract through the exporter preserves these
optimizations. The native fixture test also checks generated-source consistency
while allowing formatter whitespace changes.

The bundled aggregate Filecoin proof also passes five focused EVM checks:
valid verification, EIP-170 size, native/EVM challenges and folded points,
every mutated expected claim word, and a changed packet claim even when the
caller supplies the same changed value. Its trace heights are `2^27` and
`2^17`; its generated verifier has 23,700 runtime bytes and 23,726 deployment
bytes. Verification uses 761,311 gas around the external call, excluding
transaction intrinsic/calldata gas. The packet, hints and ABI sizes match
the small fixture. These are local Osaka measurements, not public-chain
transaction receipts.

Next work is broader real-proof differential coverage and CI integration.
The native exporter regression covers the bundled aggregate Filecoin profile
and packet. The `ix compress` driver derives statements from the aggregation
backend and supports aggregate `CheckEnv` claims; accepted profiles pin the
aggregation program and proof geometry, while the application supplies the
expected claim.
