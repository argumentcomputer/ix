# BLS PLONK wrapper implementation handoff

Updated 2026-10-16. The experimental wrapper, ix integration and packaging are
implemented, but a complete ix wrapper PLONK proof has not been produced.
Parameter preparation was killed by a confirmed system OOM before indexing or
proving. Work stopped at the user's request; no builds or prover jobs remain
running. This checkpoint records the state before the initial local commit.

Worktree: `/home/sam/repos/ix.bls-plonk-wrapper`, branch
`sb/bls-plonk-wrapper`, based on ix
`faba9bdd4445295f08dfbcf773ada80afe3f0c35`. The implementation plan is
[bls-plonk-wrapper-plan.md](bls-plonk-wrapper-plan.md). This handoff records the
current implementation and supersedes the earlier October 15 checkpoint.

## Implemented behavior

`ix compress ROOT_PROOF_ADDRESS --plonk --out OUTPUT` selects a terminal
BLS12-381 PLONK stage after the existing compression pipeline. It preserves
the ix claim and produces a new proof envelope. The circuit verifies the final
KZG packet, including both its opening pairing and its deferred pairing.
Its public inputs are the expected BLAKE3 claim digest packed into two
little-endian 128-bit limbs; the trusted circuit fixes the aggregation prefix.

The final ix KZG transcript is BLAKE3. This is separate from gnark's outer
PLONK transcript, which uses matching native/Solidity settings. The wrapper
uses Filecoin universal powers through ix's existing authenticated loader;
there is no circuit-specific trusted ceremony. Development SRS selection is
rejected for the terminal PLONK stage.

Verification requires an independently authorized catalog selected by
`IX_PLONK_VERIFIER_CATALOG`. A generated candidate catalog is never activated
automatically. The envelope identifies a key by SHA-256; verification checks
that key and its Filecoin anchors and derives the expected digest from the
caller's claim. Verification does not require the proving SRS.

| Area | Files and behavior |
| --- | --- |
| BLAKE3 profiles | `crates/proof-compression/src/pipeline/{stages/wrap.rs,wrap/outer.rs,verifier.rs}` and `profiles/aggregate-*-v6.*`. New proving selects version 6/BLAKE3. Historical v5 decoding and direct Solidity fixtures remain. Production v6 profile metadata was regenerated; production v6 proof packets were not. |
| Shared verifier export | `pipeline/wrap/outer/solidity/plonk.rs` and `plonk/ir.rs` reuse the validated graph/opening layout. The scalar program is generated through multi-stark's graph sweep and `logup_constraint_values`, rather than another handwritten scalar verifier. |
| Circuit | `tools/bls-plonk-wrapper/{blake3,profile,circuit}.go`. BLAKE3 block/tree/XOF behavior, canonical point encodings, curve/subgroup checks, native-to-emulated scalar binding, complete MSM arithmetic and two separate pairing checks. Identity maps to `(0,0)`. Trusted fixed-base relations are checked before folding coefficients. |
| Parameters and artifacts | `pipeline/plonk.rs` and Go `{parameters,artifacts,backend}.go`. Rust authenticates Filecoin and exports canonical coordinates with a BLAKE3 receipt. Go derives/caches Lagrange points, prepares keys, proves, verifies and exports Solidity. Cache identities bind the setup, domain, receipt, profile and relevant executable. |
| Native integration | `pipeline/mod.rs`, worker dispatch, `crates/ffi`, `Ix/Cli/{Compression,CompressCmd}.lean`. Adds the `--plonk` flag, proof-envelope dispatch and independently trusted key catalog. Helper output goes to stderr so CLI proof-address output remains usable. |
| Solidity | `contracts/plonk/`. An immutable generated-verifier address and digest-to-limb adapter, with positive, changed-digest, malformed-proof and deployment-size tests. Requires EIP-2537. |
| Build and CI | `lakefile.lean`, `flake.nix`, `.github/workflows/{ci,bench-main,bench-pr}.yml`. Builds/installs the Go helper beside ix and the worker, exposes a standalone Nix package/check, and provisions Go for CI. The new CI job uses the existing Ubuntu 26 RunsOn image. |

Go helper commands are `compile`, `check-witness`, `prepare`, `prove` and
`verify`. Worker PLONK commands are `fixture`, `export`, `srs`,
`profile-blake3` and `wrap`. See the helper and contract READMEs for their
arguments. `check-witness` explicitly reports that it creates no proof; its
diagnostic commitment hint is not used by production `plonk.Prove`.

The Go module pins gnark `v0.16.5-0.20261015185324-262cf453c107`, gnark-crypto
`v0.22.1-0.20261009142911-8911ee45d22b` and Go 1.26.8. The upstream tip was
checked on October 16; v0.16.4 was the latest tagged gnark release then. This
helper uses the native CPU backend. Experimental WebGPU/WASM PLONK support
exists upstream but is not enabled here. The inspected native ICICLE/CUDA
integration is for Groth16. SP1's inspected final PLONK path also runs on CPU,
using an older gnark fork and BN254; the plan has the pinned source comparison.

## Verified results

These results cover the source before the final parameter-memory scheduling
change described below, except where explicitly stated. No tests or builds
were started after the request to stop builds and prepare this handoff.

| Check | Result and boundary |
| --- | --- |
| BLAKE3 differential tests | Passed lengths 0, 1, 63, 64, 65, 1023, 1024, 1025, 2048 and 3073, including 96-byte XOF output and mutations. |
| Compiled one-block BLAKE3 | Valid witness passed and changed input failed; 261,201 constraints including lookup overhead. |
| G1 encoding/subgroups | Identity, generator and negative generator passed; wrong sign, wrong subgroup and a noncanonical `X = p` alias were rejected. |
| Complete verifier witnesses | Two distinct Filecoin conformance statements passed; changed digest and an outer-valid packet with an invalid deferred pairing failed. |
| Full compiled circuit | 20,665,582 constraints, domain `2^25`, two public inputs and one extra commitment. Compilation took 15.23 seconds; serialized constraints occupy 495,020,281 bytes. |
| Compiled witness diagnostic | Valid full witness passed in 2.24 seconds. A subgroup-valid invalid deferred pairing failed in the compiled circuit, bypassing host pre-verification. This is not a PLONK proof. |
| Actual PLONK proofs | Tiny Filecoin-backed `N=8` circuits proved and verified for `m=0` and `m=1`. Native proofs are 664/744 bytes and Solidity encodings are 1,056/1,184 bytes. These circuits do not verify an ix packet. |
| Lagrange and artifact checks | Basis-conversion equality, cache reuse, corruption rejection and backend-identity separation passed on small parameters. Rust parameter export/cache and catalog rejection tests passed. |
| Solidity conformance | Four tests passed on the earlier run. The tiny `m=1` proof used 371,471 gas around the external adapter call, with 1,284 bytes of ABI calldata. This excludes transaction intrinsic/calldata gas and is not a full-wrapper measurement. The October 16 Foundry rerun was not completed because the downloaded binaries need NixOS runtime-loader setup. |
| Rust pipeline tests | The broad filtered run passed 41 tests and found two historical Solidity-version guard failures. Those guards were fixed; the focused five-test Solidity rerun passed. The entire filtered suite was not repeated afterward. |
| Rust Clippy and FFI | Focused Clippy with all targets and `-D warnings` passed. Release `cargo check -p ix-ffi --features parallel` passed. |
| Lean/Lake | `lake -R check-build` and typechecking the two changed CLI modules passed using compatible existing dependency artifacts. A complete `lake build ix` was not run. |
| Nix helper package | Standalone helper build and its checks passed before the final memory change: `/nix/store/n87wh5a7wv2c7y492manm7fvjbpiyr5x-ix-bls-plonk-wrapper-0.1.0`. Full ix packaging was not built. |
| Final memory-change build | `go build -buildvcs=false -trimpath` succeeded. Its new binary has not run parameter preparation or tests. |

The attempted `go vet ./...` session lost its result during the interruption;
it is not counted as a pass. The pre-existing long identity-column proof test
remains ignored. Git whitespace checks pass; no claim is made that the whole
repository test suite or CI has passed.

### Circuit cost breakdown

| Cumulative phase | Constraints | Added constraints |
| --- | ---: | ---: |
| Point validation and public binding | 3,211,317 | 3,211,317 |
| BLAKE3 transcript | 9,496,602 | 6,285,285 |
| Scalar relation | 9,497,043 | 441 |
| Opening MSMs | 17,265,132 | 7,768,089 |
| Outer pairing | 18,965,730 | 1,700,598 |
| Deferred pairing | 20,665,582 | 1,699,852 |

These are compilation differences; shared range checks affect attribution.
Fixed-point folding reduced the initial 23,358,575 constraints to 20,665,582.
The alternative gnark MSM setting increased the count to 25,429,821 and was
reverted. The current implementation retains the default classic GLV path.
Even deleting the entire second pairing for free leaves more than `2^24`
constraints, so pairing batching alone cannot reduce the padded domain.
Randomized pairing batching was not implemented.

## OOM and the final unexercised change

At 10:35:01 America/New_York on October 16, the kernel reported a global OOM
and killed PID 386714, `ix-bls-plonk-wr`, during Lagrange preparation. Its RSS
was approximately 22.1 GiB. Other assistant processes accounted for roughly
22.6 GiB; the VM has about 47 GiB visible RAM and no swap. The existing monitor
only enforced a process RSS threshold, so it did not detect aggregate memory
pressure before the OOM. This does not establish the isolated memory required
by the complete wrapper prover.

The authenticated monomial export completed and survives. No Lagrange cache
was published, `KeysReady` remains false, and neither full indexing nor proving
has completed. There is no full-wrapper proving time, peak-memory result or
total verification transaction-gas result.

The final edit in `tools/bls-plonk-wrapper/backend.go` delays loading the
constraint system until after Lagrange conversion, releases FFT temporary
memory before deserialization, releases setup temporaries before key writing,
and reports the preparation stage. The new helper compiled successfully, but
the memory reduction and runtime behavior have not been tested. No system
available-memory guard or persistent hard-limit runner was implemented.

The last resume check found roughly 36 GiB available and no other large
compute job. The user authorized the full machine and does not want an
artificially small memory cap. At the next authorized run, check actual host
headroom, retain default CPU parallelism, and account for whole-system memory
rather than relying solely on RSS or Go's soft `GOMEMLIMIT`.

## Preserved local artifacts

Everything below is ignored build/research data, not part of the proposed
commit. Paths are relative to this worktree unless absolute.

| Artifact | Location or identity |
| --- | --- |
| Go toolchain | `target/plonk-tools/go/bin/go` (1.26.8). Downloaded from go.dev and checked against official SHA-256 metadata. |
| Go caches | `GOPATH=$PWD/target/plonk-go`, `GOCACHE=$PWD/target/plonk-go-build`. |
| Rust cache and worker | `/home/sam/repos/ix.sb-solidity-verifier/target`; worker under `release/ix-compression-worker`. This cached executable predates some final source edits. |
| Compiled circuit | `target/plonk-artifacts/`; manifest records `KeysReady: false`. |
| Original matching helper | `target/plonk-tools/ix-bls-plonk-wrapper`; SHA-256 `f5fd0c6addfa9792d136be29ee3f2a6cf82ad12c4dd4c099555b5a780ed18c4d`. |
| New helper with deferred circuit loading | `target/plonk-tools/ix-bls-plonk-wrapper-v2`; SHA-256 `eabb30f677f9aa17adb2a9d27611a79e52abb6669c78e8b7913058f77cf4b0e6`. |
| Component measurements | `target/plonk-components.json` and `target/plonk-components-alternative.json`. |
| Filecoin cache used by Rust | `target/plonk-data/filecoin-through-2p26.bin`; sparse file with the authenticated header, required prefix and complete chunk index. Unrequested later powers are holes. |
| Canonical monomial export | `target/plonk-data/wrapper-srs.bin` and `wrapper-srs.json`; 33,554,435 points for `N=2^25`, 3,221,226,040 bytes. |
| Export resource report | `target/plonk-data/export-resources.json`: 53 seconds, peak RSS 9,602,716 KiB, exit 0. |
| Solidity tooling/fixtures | `target/plonk-tools/foundry/` and `contracts/plonk/generated/`. Foundry runtime setup on this NixOS host remains incomplete. |
| Lean typecheck overlay | `target/lean-check/`; compatible prebuilt dependencies came from `/home/sam/repos/ix`. |

The old compiled artifact binds the original helper hash. The new helper must
compile into a new artifact directory; do not edit the manifest to bypass
identity checks. The underlying conformance profile SHA-256 is
`195b35b3f9dc926aa9fe7a01719adc6cb9e6913e0c6443228ae3105d2466830b`, and the
existing compiled circuit SHA-256 is
`e6b895608883f29d03a5db1183e0083d0ceb75bf2fc3bf5c5b38f7f13ca677b4`.

The existing Rust loader authenticated the requested prefix of the sparse
Filecoin cache, not its unpopulated tail. The source was the existing
[prepared Filecoin prefix cache](https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/filecoin-prefix-2p27.bin).
The independently obtained receipts are:

- Filecoin manifest BLAKE3: `1442386005c4e4a2ebc23c109694eb9bb16fe54bc5708f0380658ac99a37f10a`.
- Setup ID: `48b74609da5ec9a9d59efb1d4c9d91d81815a304a8baab8ba35af4fe0145239f`.
- Export BLAKE3: `26d517c2c6c54adfba55635f01d942a3be3394a97f14a4ea22db8d3c13e44c20`.
- Public maximum degree: `268435454` (`2^28 - 2`).

## Remaining work after handoff

1. Exercise the final preparation-order change on a small circuit, including
   prepare/reuse/corruption cases. Add host-memory monitoring before another
   large run. Do not reuse the old RSS-only runner as an OOM safeguard.
2. Complete Lagrange conversion, full indexing and a complete conformance
   wrapper proof, recording time and memory for each stage. The `2^25` domain
   may still exceed the practical prover budget even if conversion succeeds.
3. Give the BLAKE3 conformance fixtures known claim bytes. Their current digest
   words are synthetic `1000+i`-style test values, so they cannot exercise
   `pipeline::verify` against a known claim preimage. Regenerate those witnesses
   with `statement::with_claim`, preserve the fixed aggregation prefix, and
   check profile identity before reusing keys. This change is not implemented.
4. Exercise the complete Rust proof-envelope/catalog path, including wrong
   claim, wrong key and setup anchors, without a proving SRS available to the
   verifier. Expand native intermediate-value differential checks as needed.
5. Generate and prove an actual aggregate v6/BLAKE3 packet. The new production
   profiles are public metadata conversions, not new proof packets; the small
   conformance circuit does not establish production resource requirements.
6. Run real local verification transactions with the full wrapper proof and
   compare the same gas boundary against the optimized direct verifier. The
   acceptance target remains at most 500k total transaction gas and at least
   25% savings; neither has been established for the full wrapper.
7. Complete the deferred integration checks: focused tests of the final Go
   edit, `go vet`, full CLI packaging and CI. Treat catalog authorization and
   production circuit review as separate from generating a key.

## Commit scope

Suggested title: `feat(compression): add experimental BLS12-381 PLONK wrapper`.
The commit description should state that it adds the BLAKE3 relation, Filecoin
parameter adapter, native/CLI integration, independent key authorization,
Solidity adapter and packaging, with small-backend proof coverage. It must
also state that complete wrapper proving stopped at parameter preparation and
that the final memory-ordering change is only build-checked.

The initial commit includes the wrapper implementation, plan, handoff and
[`compression-architecture-options.md`](compression-architecture-options.md).
The architecture-options document is included unchanged for follow-up review;
its alternative pipeline proposals have not been implemented or measured.
The current wrapper measurements are recorded above. Ignored `target/`
artifacts and generated contract fixtures are excluded.

For a split review, the natural groups are: BLAKE3 profiles and shared Rust
export; Go circuit/backend and fixtures; ix CLI/catalog/build integration; and
Solidity plus documentation. Some files cross those boundaries, so splitting
requires hunk staging and independent validation of the resulting commits.
The initial commit does not split those groups.
