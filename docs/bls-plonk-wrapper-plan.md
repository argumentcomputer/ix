# BLS12-381 PLONK wrapper plan

Implementation state and measured results as of 2026-10-16 are recorded in the
[implementation handoff](bls-plonk-wrapper-status.md). The wrapper is
experimental; full parameter preparation and proving remain incomplete after
an OOM. The sequence below describes the intended validation and acceptance
criteria, not completed milestones.

Add a terminal KZG-PLONK proof over the BLS12-381 scalar field around ix's
existing final KZG packet. The wrapper must enforce the complete inner
verification relation, including both pairing obligations. Its recipient checks
only the PLONK proof and the independently expected claim digest.

The priority is cheap verification, including Solidity verification. Reuse the
existing Filecoin Powers of Tau and accept the additional prover work needed to
put the inner pairing checks inside the circuit. No circuit-specific trusted
ceremony is acceptable. PLONK circuit compilation and deterministic key
generation from public parameters are acceptable.

Switch the final ix KZG transcript from Keccak back to BLAKE3 and add the
terminal PLONK stage. Reuse ix's existing BLAKE3 transcript definition and
recursive-verifier vectors. Regenerate the final profile, packet fixtures and
wrapper keys together; an existing Keccak packet cannot be converted by changing
its identifier. Backward compatibility with the Keccak profile is not required.
The earlier compression stages and Filecoin parameter ownership remain intact.

Implementation baseline: ix `sb/solidity-verifier` at
`faba9bdd4445295f08dfbcf773ada80afe3f0c35`, the exporter commit immediately after
`sb/proof-compression` at `eb50b1b2e08e6f4d5926617fd0773d2a7c8eeb8d`.
It retains multi-stark `8b6c3fbdd8575bfeb818a32acf06509bac81ff3b` and the existing
Filecoin setup implementation. Source links pin this baseline. Refresh the
exported profile and fixtures together if the inner protocol changes.

## Existing ix components to reuse

Filecoin provisioning and setup policy are already implemented. This work needs
a PLONK representation adapter, not another downloader, ceremony importer, or
independent Filecoin authentication implementation.

| Existing component | Role in the wrapper |
| --- | --- |
| [SetupConfig and SetupSource][ix-setup] | Reuse environment selection, explicit development policy, authenticated SRS loading, and verifier parameters. |
| [Filecoin loader][ix-filecoin] | Reuse receipt and chunk authentication, pinned anchors, validated point decoding, and the provisioned prefix cache. |
| [Srs and PublicSetup][ix-srs] | Preserve the ceremony identity and complete public degree independently of the loaded prefix. |
| [Bundled verifier catalog][ix-catalog] | Select and authenticate the inner profile and its aggregation-program prefix. |
| [Recursive packet verifier][ix-verification] | Use as the native acceptance oracle, including the separate deferred pairing equation. |
| [Statement encoding][ix-statement] and [compact proof codec][ix-codec] | Derive canonical packet shape and claim binding from the trusted profile. |
| [Solidity exporter][ix-exporter] and [opening code generator][ix-opening-export] | Share validated graph instructions, matrix layout, opening formulas and differential vectors with the gnark circuit. |
| [Recursive verifier gadgets][ix-recursive] | Reuse constraint descriptions, test vectors, and scalar/MSM verification logic where applicable. |
| [Fixed preprocessing cache][ix-cache] and [storage helpers][ix-storage] | Reuse cache identity principles, checksums, and durable publication helpers. |

The existing recursive gadget accepts BLAKE3 and exposes pairing operands for
external verification. It supplies a tested specification for the wrapper's
transcript, scalar checks and MSMs. The gnark circuit must additionally enforce
the resulting pairing equation and the separate deferred pairing equation.

## Proof relation and public inputs

Pin the inner verifier profile, its constraints and fixed commitments, Filecoin
anchors, domain sizes, transcript parameters, and aggregation-program prefix in
the wrapper circuit. A proof cannot supply its own trusted verification key or
constraint graph.

The private witness is the existing final packet, or an equivalent decoded
representation whose canonical encodings are constrained. The current fixture
is 2,181 bytes and contains 15 outer-proof G1 points, 37 scalar values, two
deferred G1 pairing operands, the statement, and the profile identifier. Derive
dimensions from the trusted codec when exporting a profile rather than treating
these fixture counts as a general protocol rule.

Expose the existing 32-byte claim digest as two public 128-bit limbs. For digest
bytes `d[0..32]`, define each limb by little-endian packing of its consecutive
16-byte half. Constrain the limbs to 128 bits and reconstruct the eight
little-endian 32-bit words in statement positions 10 through 17. Statement
positions 0 through 9 are constants from the authenticated profile.

This preserves ix's existing BLAKE3 claim digest without adding a new hash of the
statement. Native callers compute the expected digest through the existing ix
claim encoding. A Solidity caller supplies an independently expected digest,
which the application binds to its own statement or state. The contract derives
the two public limbs from that digest; it does not trust a digest embedded in
the proof.

The circuit must enforce all of the following:

1. Exact profile and shape, canonical scalar and point encodings, and the public
   statement binding.
2. The existing BLAKE3 transcript, including parameter seeding, observation
   order, lengths, canonical encodings, challenge reduction and opening
   omissions. Each squeeze hashes the old 32-byte state followed by the
   observations, uses the first 64 XOF bytes as a little-endian integer reduced
   modulo Fr, and takes the next 32 bytes as the new state.
3. Public-message balance, lookup relations, quotient reconstruction, and the
   out-of-domain constraint identities, including invalid-challenge rejection.
4. The KZG opening MSMs and their resulting pairing equation.
5. The deferred pairing equation carried by the recursive packet, with its
   operands bound to the same inner proof's public values.

Keep two separate pairing equations as the reference implementation and size
randomized batching in step 2. With matching Filecoin anchors, the equations
`e(L,H)e(-R,tauH)=1` and `e(A,H)e(B,tauH)=1` can be folded into
`e(L+rho*A,H)e(-R+rho*B,tauH)=1`. Derive the nonzero field challenge `rho` inside
the circuit using a separately domain-separated transcript that binds the
trusted profile, expected claim, full canonical packet and all four operands
after they are fixed. Specify its hash, encoding and zero-challenge rule.

Under the random-oracle model, a uniform challenge contributes approximately
`Q/(r-1)` batching error for `Q` grinding attempts, in addition to the underlying
proof-system assumptions. Account for the actual challenge distribution and
hash security in the argument. Adopt batching only after review and cancellation
tests; multiplying equations without a fresh challenge is unsound.

Every untrusted G1 point must receive the required canonical, curve, and subgroup
checks. Constrain ix's infinity flag and canonical compressed identity encoding
to map to gnark's affine `(0,0)`, and require finite points to satisfy their
curve equation. In gnark v0.16.4, `ScalarMul` and `MultiScalarMul` use complete
arithmetic by default; preserve that default and use `AddUnified` for explicit
additions. Do not enable `WithIncompleteArithmetic` on these proof paths.
Exercise zero scalars, infinity, equal/opposite points and identity sums.
Trusted SRS anchors must remain nonidentity. Precomputed G2
line coefficients can be circuit constants derived from the pinned anchors;
prover-supplied unconstrained line coefficients are not acceptable.

Host parsing and native verification provide diagnostics and differential
oracles. They cannot substitute for constraints: negative tests must construct
adversarial circuit witnesses that bypass the normal host preparation path.

## Backend and integration

Use a separately versioned Go helper based on current upstream gnark. As of
2026-10-15, the latest release is [v0.16.4][gnark-release] and the inspected
default-branch tip is `262cf453c107d147a228b6b7418c5cf791c3b79b`. Pin that tip
as the implementation candidate, including its dependency graph and Go 1.26.8
toolchain requirement. Its post-release changes include a SHA3 `Sum` state fix,
an SCS zero-coefficient fix and lookup-argument improvements. Recompile and size
against that exact revision. The BLS12-381 PLONK backend and curve gadgets used
for the cost table are unchanged from v0.16.4.

Place the Go module under `tools/bls-plonk-wrapper/` and add a narrow Rust adapter
under `crates/proof-compression/src/plonk/`. Rust owns profile selection,
Filecoin parameter loading, packet decoding, and integration with the existing
worker. The helper owns circuit compilation, PLONK indexing, proving, native
wrapper verification, and Solidity export.

Use a versioned canonical interchange format for the trusted profile, witness,
and SRS adapter output. Specify lengths, endianness, field bounds, infinity
encoding, and artifact digests. Never exchange an arkworks or gnark in-memory
Montgomery representation as the transport format.

Scalar identities of the existing proof are native over BLS12-381 Fr, but the
generic curve API takes scalars as `emulated.Element[Fr]`. Build those limbs from
a constrained canonical bit decomposition of each native scalar, enforce the
integer bound below Fr, and reuse the decomposition. Equality modulo the native
field alone does not establish a unique encoding. Count this conversion and
its range checks separately. G1 and pairing arithmetic use the larger Fq field
and remain emulated.

Use `PairingCheck`, which constrains a non-residue witness instead of computing
a full final exponentiation. It does not establish the G1 input subgroup
obligations. Supply trusted constant G2 lines and validate all variable inputs.
Pass the 19 pinned commitments and generator as compile-time constants so
gnark's fixed-base comb tables apply; ordinary variable-base MSM estimates
overstate this portion of the circuit.

Distinguish the final ix KZG transcript, which is replayed inside the circuit,
from the outer PLONK transcript, which native and Solidity verifiers replay.
Use gnark's matching native/Solidity configuration for the latter. Freeze both
choices in the wrapper profile and test their encodings independently.

### SP1 comparison and GPU support

The architecture matches SP1's terminal PLONK path: Rust prepares a recursive
verifier circuit and witness, Go/gnark compiles an SCS, deterministic PLONK
indexing uses a universal monomial/Lagrange SRS, and the resulting key exports a
Solidity verifier. At SP1 `02fa30185ecd658174b211d56128b14867ab8e81`, that path
uses BN254 and Aztec Ignition parameters. Its [Go dependency][sp1-go-mod] is a
gnark v0.14-era fork at `p4u/gnark` commit `cd7874155e26`, not current upstream.
Its [build][sp1-build] and [prove][sp1-prove] code are integration references,
not a source for this wrapper's circuit costs: SP1 wraps its recursive STARK
verifier, whereas ix also needs emulated BLS KZG MSMs and pairing checks.

GPU support has three distinct scopes:

| Path | Current support and consequence |
| --- | --- |
| Native gnark PLONK helper | CPU by default when no accelerator is attached. Use this for initial measurements. |
| [gnark WebGPU backend][gnark-webgpu] | Experimental BLS12-381 PLONK acceleration exists. It offloads MSMs, FFT work and the quotient numerator, and builds only for `GOOS=js GOARCH=wasm` with a JavaScript/WebGPU runtime. It is not enabled by the proposed native Go helper. |
| [gnark ICICLE/CUDA integration][gnark-icicle] | The packaged integration supports Groth16, not PLONK. SP1's [CUDA feature][sp1-cuda] selects that Groth16 path; its inspected final PLONK prover calls the CPU backend. Earlier SP1 proving stages can use GPUs independently. |

Thus GPU acceleration is available experimentally, but there is no packaged
native CUDA PLONK path in the inspected upstream tree or SP1 wrapper. A native
accelerator can implement gnark's `MultiExp`, `ToCanonical` and
`ComputeNumerator` hooks; ix's existing CUDA prover does not automatically
implement them. Evaluate WebGPU runtime and memory limits, or a native adapter,
as a separate work item after circuit sizing. The documented WebGPU benchmark
fixtures use `2^15` and `2^18`; they do not establish feasibility at this
wrapper's eventual domain size.

## Filecoin parameters and derived keys

Start parameter acquisition through the existing `SetupConfig::from_env` and
`SetupSource` flow. Reuse `IX_KZG_FILECOIN_CACHE` and
`IX_KZG_FILECOIN_MANIFEST`, including the built-in receipt for the provisioned
`2^27` cache. Production wrapper keys must be classified as Filecoin using the
existing identity, public-degree, and anchor checks. Development fixtures remain
explicitly selected and isolated from production keys and caches.

For a compiled PLONK domain of size `N`, gnark requires at least `N + 3` monomial
G1 powers and exactly `N` Lagrange G1 points. Derive the Lagrange points
deterministically from authenticated monomial powers and cache them by ceremony
identity, `N`, encoding version, and backend version. This is public
preprocessing, not a new trusted setup.

The first adapter can request
`next_power_of_two(N + 3)` through `SetupSource::srs(..., false)` and export the
required `N + 3` points. Preserve `Srs.public_setup` and the G2 anchors when
trimming. The existing cache suffices through `N = 2^26` with this approach.
At `N = 2^27`, PLONK needs more than the cached `2^27` powers. Report that
requirement explicitly; do not weaken validation or silently generate powers.
If that case becomes necessary, extend the existing authenticated Filecoin
prefix workflow. The complete ceremony publishes powers through exponent
`2^28 - 2`, but those additional points are not in the provisioned prefix cache.

Do not implement a second Filecoin reader in Go. Export parameters already
authenticated by ix. If adapter memory becomes material, add a bounded export
operation to the existing loader while preserving its manifest, chunk, anchor,
and point validation.

Separate reusable Lagrange SRS preparation from circuit-specific deterministic
PLONK indexing. Put derived artifacts in a distinct wrapper cache namespace,
using the existing storage/checksum helpers. Bind cache entries to the Filecoin
identity and receipt, inner profile, circuit digest, domain size, backend and
compiler versions, outer transcript, and public-input schema. Include the
relevant executable identity for operational cache invalidation.

Authenticate portable wrapper verification keys through the application catalog
or deployed contract. A cache digest or a key shipped alongside a proof is not
independent verifier authorization. Verification needs only the trusted wrapper
key and expected claim digest; it must not require a proving SRS file.

## Implementation sequence

### 1 Share the exporter and switch the final transcript

Change final-stage proving and verifier construction to BLAKE3 together. Bind
the transcript choice to the profile and invalidate stale keys and caches.
Generate small positive and outer-valid/deferred-invalid Filecoin fixtures with
the new transcript before regenerating a production aggregate packet.

Factor the exporter's validated `GraphProgram` and `OpeningLayout` into a shared
representation usable by the gnark adapter. Extend it to describe scalar and
opening formulas, fixed points, transcript parameters and statement binding.
Drive Go circuit generation or evaluation from that trusted representation,
with the graph fixed at compilation. Preserve the existing graph/window and
opening-order differential tests. Avoid maintaining another independent
handwritten copy of the multi-stark verifier relation.

Generate native intermediate vectors for BLAKE3 challenges, scalar identities,
opening MSM results and both pairing equations. Include block/chunk/XOF
boundaries from ix's transcript tests.

Deliverable: authenticated profiles and reproducible small fixtures with native
verification and exporter/circuit agreement.

### 2 Size components before the complete circuit

Implement and measure the components over BLS12-381 Fr separately:

| Component | Required accounting |
| --- | --- |
| BLAKE3 transcript | Actual compression calls, constant-prefix precomputation, tree and XOF handling, canonical byte packing and 512-bit reduction. |
| Native scalar relation | Graph, lookup identities, quotient reconstruction, public binding and inversions. |
| Scalar conversion | Canonical native-to-emulated Fr decomposition and reused bits/limbs. |
| G1 arithmetic | Variable bases separately from the 19 fixed commitments and G; verify fixed-base comb selection and complete additions. |
| Point validation | Canonical encoding, curve checks and subgroup checks for all 17 variable packet points; valid infinity cases. |
| Pairings | Two fixed-G2 two-pair checks versus one randomized two-pair check, including the batching transcript and extra scalar multiplications. |

Count fixed-commitment relations only after validating them for the exported
profile. Keep all variable-point validation even when a coefficient is zero.
Use the optimized `PairingCheck` gadget in both variants. Choose batching only
if its reviewed soundness argument and measured cost justify it.

Then compile the whole circuit and record constraints, wires, public inputs,
extra committed polynomials, padded domain, witness-generation time and peak
memory. Component counts may not add exactly because range checks and
commitments can be shared. Complete sizing before large SRS conversion or
full-profile proving. BLAKE3 is the required transcript; a Poseidon2 redesign
is outside this implementation.

Deliverable: valid witnesses satisfy the circuit, adversarial witnesses fail,
and measured size determines the domain, parameters and resource requirements.

### 3 Adapt authenticated parameters and index the circuit

Implement the canonical Rust-to-gnark SRS adapter, deterministic Lagrange
conversion, and cached PLONK proving/verifying keys. Check the first powers and
both G2 anchors against ix, and verify that commitments to small known
polynomials agree between implementations.

Use the existing 256-power Filecoin fixture for encoding, identity, and tiny
PLONK backend tests. It cannot support a full pairing-verifier circuit. Full
wrapper proving needs the larger prefix selected from the compiled domain.

Deliverable: preparation and cache reuse preserve the same authenticated setup,
and corrupted or mismatched derived artifacts are rejected.

### 4 Prove and verify the wrapper natively

Produce a full wrapper proof for the regenerated BLAKE3 Filecoin packet and verify it
against its independently expected claim digest. Repeat with another valid
statement under the same profile. Use the same wrapper key for both.

Test each inner obligation independently. In particular, include a packet with
a valid outer KZG proof and an invalid deferred pairing equation. Exercise
modified claims, transcript challenges, opening values, proof points, profile
metadata, and canonical-encoding boundaries. Check that corrupted outer PLONK
proofs fail in the native wrapper verifier. Cover both coordinates/flags of
infinity, zero scalars, cancelling MSM terms and mismatched native/emulated
scalar representations. If batching is selected, mutate every challenge input
and test deliberately cancelling invalid pairing equations.

Deliverable: the wrapper's acceptance matches the native ix oracle on the
positive and adversarial corpus, including witnesses prepared without a native
pre-verification shortcut.

### 5 Integrate Solidity verification

Export the BLS12-381 PLONK verifier and put a small application adapter in front
of it. The adapter accepts proof bytes and the independently expected claim
digest, performs the specified limb packing, and invokes the pinned wrapper key.
Use EIP-2537 for the outer PLONK verification. There must be no extra application
calls to check the original proof's pairing operands.

Run the same corpus through native and Solidity verification. Check malformed
lengths, public-input bounds, changed digest halves, wrong verification keys,
invalid curve points, identity cases, and failed precompile calls. Record runtime
and deployment bytecode size and enforce the deployment limits.

Deliverable: native/EVM acceptance parity and measured transaction gas meeting
the acceptance target below.

### 6 Package the terminal stage

Integrate the helper with `ix-compression-worker`, then expose an optional
terminal PLONK mode through `ix compress`. Preserve the original claim address
and assign a new proof address. Give the wrapper its own versioned proof format
and verification dispatch; do not reinterpret an existing KZG packet as PLONK.

Package the helper beside the worker through Lake and Nix. Track Go sources,
`go.mod`, `go.sum`, profiles, fixtures, and backend versions in build inputs and
cache keys. Proving must not require Go or Cargo on the deployment host.
Add focused CPU CI coverage and explicit resource-heavy benchmark targets.

Deliverable: an installed ix can produce and verify the new proof format, and
native/Solidity verification works without access to the proving cache.

## Performance measurements and targets

Measure the added wrapper separately from the existing compression pipeline.
Use a fixed statement, trusted profile, backend revision, compiler, machine,
and thread configuration. Use all available CPUs. The authorized development
machine has no CUDA GPU and 48 GB usable RAM; start with small examples and
component tests and admit larger runs only when sizing fits that memory budget.
Report any additional KZG work caused by the transcript change separately from
the new PLONK stage.

| Measurement | Boundary and required output |
| --- | --- |
| Circuit construction | Compilation time, constraints, wires, commitment count, padded `N`, peak RSS. |
| Parameter preparation | Existing Filecoin authentication/export, Lagrange conversion, and indexing reported separately. |
| Cold wrapper proof | Key/cache load, witness generation, proof generation, verification, serialization, and publication. |
| Warm wrapper proof | The same scope with prepared keys cached; distinguish a warm process from a fresh process reading cached files. |
| Native verification | Trusted key loaded; decode, validate, and verify the full wrapper. Report key loading separately. |
| Solidity verification | A successful verify-only transaction with an independently expected digest; report execution, intrinsic/calldata costs and total gas, with deployment separate. Record fork/compiler and byte counts. |
| Resources | Peak RSS, VRAM when applicable, persistent key sizes, temporary disk peak, and proof/calldata sizes. |

Set time and memory estimates from measured component sizes and the compiled
domain. The original `2^27` recursive trace does not determine that domain.
For scale, at `N = 2^24` one Fr vector is 0.5 GiB, one `4N` vector is 2 GiB,
and the two affine G1 SRS arrays total about 3 GiB; at `2^25` these double.
The prover needs many vectors plus constraints, witnesses, keys and scratch
space. These figures are individual allocations, not a total-memory estimate
or evidence that a full proof fits 48 GB. There is no committed minutes/tens-of-
GiB proving allowance before sizing.

For reference, gnark v0.16.4's stock BLS12-381 Solidity template has the following
calculated curve-operation costs. `m` is its number of additional committed
polynomials; it is not the number of inner pairing checks.

| `m` | G1 MSM sizes | Pairing check | Curve subtotal | Solidity proof bytes |
| --- | --- | --- | ---: | ---: |
| 0 | 10, 6, 5, 2 | Two pairs | 310,956 gas | 1,056 |
| 1 | 11, 7, 5, 2 | Two pairs | 326,568 gas | 1,184 |
| 2 | 12, 8, 5, 2 | Two pairs | 341,916 gas | 1,312 |
| 4 | 14, 10, 5, 2 | Two pairs | 372,372 gas | 1,568 |

Use total transaction gas for both sides of the comparison. The plan's
acceptance target is `G_wrapper <= min(500,000, 0.75 * G_direct_optimized)`:
at most 500k and at least 25% below the best validated direct verifier for the
same application statement and security obligations. A 600k wrapper fails this
target. Compile the actual circuit to determine `m` and measure its generated
contract; the curve subtotals alone are not transaction estimates.

The [pinned direct-verifier record][ix-direct-baseline] reports 761,311 gas around
an external call for the aggregate Filecoin profile, excluding transaction
intrinsic/calldata costs, with 3,748 ABI bytes. Reproduce it as a real verify-only
transaction under the same fork/compiler as the wrapper. Use adapters that both
accept the independently expected digest, and separately record adapter costs;
the old 18-word expected-statement ABI otherwise distorts the comparison. Keep
the original Keccak implementation in that historical benchmark checkout; it
is not a compatibility requirement for the new BLAKE3 pipeline.

Measure the direct verifier's outstanding fixed-commitment simplification,
witness-MSM split and reviewed randomized pairing batching. The existing
design calculations suggest roughly 47k, 7k and 89k curve-gas savings
respectively, but they are not measured cumulative savings for the aggregate
profile. Recompute the combined MSM sizes and overhead rather than subtracting
the three estimates. Execution near 620k is a scenario to beat, not an observed
baseline. The acceptance comparison must use the combined measured result.

SP1's published approximately 300,000-gas BN254 PLONK figure is an external
reference. Its curve, recursive verifier and dependency revision differ; its
additional proving time does not predict this wrapper's proving time.

## Completion criteria

- The production wrapper uses BLS12-381 PLONK and ix's authenticated Filecoin
  parameters, with no new trusted ceremony or production trapdoor generation.
- Both inner pairing obligations are constrained, and the final verifier needs
  only the wrapper proof, trusted key, and independently expected digest.
- Setup policy, Filecoin authentication, public degree, and anchor ownership
  remain in the existing ix implementations.
- Canonical encoding, point validity, subgroup membership, transcript replay,
  scalar identities, and statement binding have differential and adversarial
  coverage, including BLAKE3 chunk/XOF boundaries, scalar conversion and valid
  identity cases. Shared exporter formulas drive the circuit.
- Native and Solidity verification agree; neither needs the proving SRS.
- The prepared parameters and keys can be reused safely across statements of
  the fixed profile, and artifact corruption or identity mismatch is rejected.
- Proving time, memory, native verification time, successful Solidity gas,
  calldata, and deployment costs are measured with the stated boundaries.
- The wrapper meets the 500k/25% transaction-gas target and the measured proving
  resource budget. Experimental GPU support is not assumed in CPU measurements.
- Curve/gadget integration and the complete verifier relation receive focused
  review before the new verification key becomes an accepted production key.

## References

- [gnark BLS12-381 PLONK setup requirements][gnark-setup]
- [gnark BLS12-381 PLONK prover and accelerator interfaces][gnark-prove]
- [gnark BLS12-381 Solidity verifier template][gnark-solidity]
- [gnark emulated BLS12-381 pairing checks][gnark-pairing]
- [gnark emulated curve arithmetic and fixed-base dispatch][gnark-curves]
- [gnark v0.16.4 release and gadget fixes][gnark-release]
- [gnark changes since v0.16.4][gnark-current]
- [gnark experimental WebGPU backend][gnark-webgpu]
- [SP1 PLONK build and SRS selection][sp1-build]
- [EIP-2537 curve operations and gas schedule][eip2537]
- [SP1 proof types and published cost comparison][sp1]

[ix-setup]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/setup.rs
[ix-filecoin]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/kzg/srs/filecoin.rs
[ix-srs]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/kzg/srs.rs
[ix-catalog]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/verifier.rs
[ix-verification]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/stages/verification.rs
[ix-statement]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/statement.rs
[ix-codec]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/kzg/compact.rs
[ix-recursive]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/recursive/native_verifier.rs
[ix-cache]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/fixed_cache.rs
[ix-storage]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/storage.rs
[ix-exporter]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/wrap/outer/solidity.rs
[ix-opening-export]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/crates/proof-compression/src/pipeline/wrap/outer/solidity/codegen.rs
[ix-direct-baseline]: https://github.com/argumentcomputer/ix/blob/faba9bdd4445295f08dfbcf773ada80afe3f0c35/contracts/kzg/README.md#current-results
[gnark-setup]: https://github.com/Consensys-Incorporated/gnark/blob/v0.16.4/backend/plonk/bls12-381/setup.go
[gnark-prove]: https://github.com/Consensys-Incorporated/gnark/blob/v0.16.4/backend/plonk/bls12-381/prove.go
[gnark-solidity]: https://github.com/Consensys-Incorporated/gnark/blob/v0.16.4/backend/plonk/bls12-381/solidity.go
[gnark-pairing]: https://github.com/Consensys-Incorporated/gnark/blob/v0.16.4/std/algebra/emulated/sw_bls12381/pairing.go
[gnark-curves]: https://github.com/Consensys-Incorporated/gnark/blob/v0.16.4/std/algebra/emulated/sw_emulated/point.go
[gnark-release]: https://github.com/Consensys-Incorporated/gnark/releases/tag/v0.16.4
[gnark-current]: https://github.com/Consensys-Incorporated/gnark/compare/v0.16.4...262cf453c107d147a228b6b7418c5cf791c3b79b
[gnark-webgpu]: https://github.com/Consensys-Incorporated/gnark/blob/262cf453c107d147a228b6b7418c5cf791c3b79b/backend/accelerated/webgpu/README.md
[gnark-icicle]: https://github.com/Consensys-Incorporated/gnark/blob/262cf453c107d147a228b6b7418c5cf791c3b79b/backend/accelerated/icicle/doc.go
[sp1-go-mod]: https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/go.mod
[sp1-build]: https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/sp1/build.go
[sp1-prove]: https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/sp1/prove_plonk.go
[sp1-cuda]: https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/sp1/prove_groth16_icicle.go
[eip2537]: https://eips.ethereum.org/EIPS/eip-2537#gas-schedule
[sp1]: https://docs.succinct.xyz/docs/sp1/generating-proofs/proof-types#plonk
