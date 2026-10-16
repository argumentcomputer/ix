# BLS12-381 PLONK wrapper

This CPU helper proves verification of an ix BLAKE3 KZG packet, including its
outer opening equation and its deferred pairing equation. Its only public
inputs are the expected claim digest, packed as two little-endian 128-bit
limbs. The trusted circuit fixes the inner profile and aggregation-program
prefix.

The implementation is experimental. The checked-in outer packets are small
conformance circuits, not aggregate Lean proofs. Production verification keys
need review of the complete circuit and its measurements before authorization.

## Build and use through ix

Go 1.26.8 or newer is required for source builds. `lake build ix` builds the
native helper beside ix and its compression worker; `lake run install` installs
all three. `nix build .#ix` packages them, and `nix build .#plonk-wrapper` builds
and tests only this helper. Runtime proving and verification do not need Go or
Cargo installed.

```sh
export IX_KZG_FILECOIN_CACHE=/path/to/filecoin-prefix-2p27.bin
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

The existing ix setup configuration owns Filecoin selection and authentication.
`IX_KZG_FILECOIN_MANIFEST` selects an explicitly pinned cache receipt when using
a cache other than the standard `2^27` cache. Terminal PLONK rejects `--dev-srs`.
Key generation and Lagrange conversion are deterministic operations on these
public powers; they do not require a circuit-specific trusted ceremony.

The output's `plonk` directory contains the native proof, Solidity proof bytes,
generated verifier, public key and a candidate verifier catalog. `ix compress`
preserves the claim and stores a new proof address. Override the helper location
with `IX_PLONK_HELPER` if it is not beside the CLI/worker.

## Authorize verification keys independently

Set `IX_PLONK_VERIFIER_CATALOG` to an independently trusted JSON catalog before
verifying a PLONK proof with `ix verify`. Generating a proof does not activate
its candidate catalog. Approving a key approves the circuit and fixed program
prefix represented by that key.

The generated `verifier-catalog.candidate.json` has the catalog schema and uses
a path relative to its directory for `verifying-key.bin`. It records the key's
SHA-256, inner profile, program prefix, circuit hash and helper hash. Review and
install accepted entries as trusted application configuration. Proof envelopes
carry only a key identifier and proof bytes; they cannot supply a trusted key.

Verification checks the selected key's digest and Filecoin G1/G2 anchors and
derives the expected public digest from the independently supplied ix claim.
It requires no proving SRS or GPU.

## Standalone operations

`ix-compression-worker plonk export` authenticates a portable BLAKE3 profile,
verifies its packet against an independently expected statement, and exports
the fixed scalar program and canonical witness:

```sh
ix-compression-worker plonk export \
  verifier.bin packet.bin TRUSTED_VERIFIER_BLAKE3 expected-statement.json input
ix-bls-plonk-wrapper compile input/profile.json artifacts
ix-bls-plonk-wrapper check-witness artifacts input/witness.json
```

`check-witness` is an assignment diagnostic, not a proof. It uses diagnostic
commitment challenges. Production `prove` uses gnark's real KZG commitment
computation and verifies the resulting PLONK proof before publishing it.

Read the padded `Domain` from `artifacts/manifest.json`, then export the required
parameters through ix:

```sh
ix-compression-worker plonk srs DOMAIN parameters.bin
ix-bls-plonk-wrapper prepare artifacts parameters.bin TRUSTED_EXPORT_BLAKE3
ix-bls-plonk-wrapper prove artifacts input/witness.json proof-output
ix-bls-plonk-wrapper verify \
  artifacts/verifying-key.bin TRUSTED_KEY_SHA256 \
  proof-output/proof.bin EXPECTED_CLAIM_DIGEST
```

The parameter export receipt is written beside `parameters.bin` as
`parameters.json`. Obtain `TRUSTED_EXPORT_BLAKE3` from that authenticated Rust
operation, independently of an untrusted parameter file. Gnark requires `N+3`
monomial powers and `N` Lagrange points; the adapter requests the next power of
two from ix and retains the ceremony's full public degree. Its current maximum
PLONK domain is `2^26` with the provisioned `2^27` cache.

Circuit and key artifacts bind the profile, executable and parameter receipt.
The helper checks hashes before reuse. Lagrange points are cached separately
by setup, domain, receipt and helper identity; `IX_PLONK_LAGRANGE_CACHE` can
select the shared directory. A changed executable needs a new artifact
directory. Corrupt artifacts fail closed.

## Tests and sizing

```sh
cd tools/bls-plonk-wrapper
go test ./...
IX_PLONK_SIZE=1 go test -run TestComponentSizing -v
```

The ordinary tests cover BLAKE3 block/chunk/XOF boundaries, canonical curve
encodings, subgroup rejection, complete verifier witnesses, cached-parameter
integrity, basis conversion and small PLONK proofs using real Filecoin powers.
The small PLONK backend proof tests exercise `N=8`, separately from the full
verifier circuit.

The measured full conformance verifier has 20,665,582 constraints, a `2^25`
domain and one extra committed polynomial. Point validation and public binding
account for about 3.21 million constraints, BLAKE3 adds 6.29 million, scalar
identities add 441, opening MSMs add 7.77 million, and the pairing checks add
about 1.70 million each. These are cumulative-compilation differences; shared
range checks can affect component accounting.

Both pairing checks remain separate. Even eliminating the second check for
free would leave more than `2^24` constraints, so pairing batching cannot
reduce the current padded domain. The standard gnark MSM path is retained:
the tested alternative increased the full count to 25,429,821.

The backend is native CPU gnark at `262cf453c107d147a228b6b7418c5cf791c3b79b`.
Upstream experimental WebGPU/WASM PLONK acceleration exists, but this helper
does not activate it. The packaged native ICICLE/CUDA integration is for
Groth16.
