# Compression as Aiur programs

Proof compression turns an Ix aggregate root (a Goldilocks/BLAKE3 STARK) into
a small BN254 proof. Today every stage after the root is a hand-written
circuit (`crates/proof-compression`). This document sketches the same pipeline
written as Aiur programs, proven by multi-stark over Goldilocks and over BN254
with the existing KZG backend, then by PLONK through a new Aiur compiler
backend. The endpoint is a BN254 PLONK proof using Ignition and gnark's
established Solidity verifier implementation. This document states what that
would gain, what it would cost, and what stays trusted.

## 1. Today

| Stage | Proves | System | Written as |
|---|---|---|---|
| Root | the environment checks | multi-stark, Goldilocks/BLAKE3 | Aiur (`ix_aggr`), normalized to the release layout |
| FRI | the root verifies | multi-stark, Goldilocks/BLAKE3 | hand-written `plonkish` circuit (`src/fri/*`), fixed by the layout |
| First KZG | the same verifier, over BN254 | multi-stark + `KzgConfig`, BN254 Fr | the FRI circuit translated gate by gate (`src/foreign.rs`) |
| Recursive KZG | the first KZG proof verifies | multi-stark + `KzgConfig` | hand-written Fq-in-Fr, curve, MSM, transcript gadgets (`src/recursive/*`) |
| Final (optional) | the recursive relation | gnark PLONK / Groth16 | hand-written Go (`tools/gnark/circuit.go`) |

The FRI circuit hard-codes every circuit of the aggregation key: its
constraints, widths, heights, FRI rounds (`root/fixed.rs`). The root layout
and normalization (`crates/proof-compression/README.md`, "Proving and
verification") exist to give it one shape. Changes to that key or layout
propagate through the FRI plan, fixed preprocessing, recursive key and final
verifier. The final circuit also specializes the statement prefix, which
contains the allowed IxVM/aggregation identity digest. An IxVM-only change
can therefore require new final keys even when the aggregation key and
layout stay unchanged. The release workflow re-derives and checks the keys,
Solidity verifier and fixtures when these inputs change (`verifying_keys.rs`,
README "Deriving the verifying keys").

None of these circuits is covered by the Aiur formalization; their soundness
rests on review and tests.

## 2. The property to keep: keys as data

Aiur's recursive verifier already does what the hand-written circuits cannot.
`MultiStark::verify_multi_stark_proof`
(`MultiStark/MultiStark/Modules/Recursion.lean`) reads the verified system's
key as input bytes, checks their BLAKE3 digest against a public input, and
then runs the STARK verifier over whatever shape that key and proof describe:

```
fn verify_multi_stark_proof(system_digest: [Field; 8], claims_digest: [Field; 8]) {
  let sbytes = StarkIO::read_byte_stream(1, …);
  assert_eq!(Blake3::pack_digest(Blake3::hash(sbytes)), system_digest);
  let (sys, _) = SystemDeserialize::read_system(sbytes);
  …
  assert_eq!(StarkVerifier::verify_batch_at(sys, idx, len, claims), 1);
}
```

Its circuit is fixed by the verifier *program*; the verified circuit is
data. For fixed backend parameters and sufficient final execution capacity,
compression keys depend on the compression programs and their compilation,
not on IxVM or `ix_aggr`. Changing the IxVM program changes an authenticated
digest in the statement. The final PLONK key also depends on the exporter's
execution capacity (§3.3); exceeding it requires a larger circuit and key.

## 3. Proposed pipeline

| Stage | Program | Field / PCS | Verifies |
|---|---|---|---|
| Root | `ix_aggr` (unchanged) | Goldilocks / FRI | — |
| **G→B** | `CompressGL` | **BN254 Fr / KZG** | the root, a Goldilocks STARK, with Goldilocks arithmetic emulated in Fr |
| **B→B** | `CompressBN` | BN254 Fr / KZG | a G→B proof or another B→B proof, carrying its accumulated pairing |
| Final (required) | `CompressFinal` (Aiur) | BN254 PLONK (gnark) | the last B→B proof and its accumulated pairing |

Ignition supplies reusable BN254 KZG setup parameters. Both KZG stages and
the final PLONK stage already use Ignition by default today
(`pipeline/setup.rs`, `tools/gnark/cmd/ignition/main.go`). PLONK uses KZG
internally, but a multi-stark proof using `KzgConfig` is not a PLONK proof.
Retaining PLONK preserves the established on-chain verifier implementation
and compact proof format. Within the SRS degree bound, a new final circuit
needs a new key and Solidity export derived from the same production ceremony.

### 3.1 `CompressGL`: a Goldilocks STARK verifier running over BN254

The existing `StarkVerifier`, `Pcs`, `Mmcs`, `Transcript` and `StarkHash`
modules, instantiated over an *emulated* Goldilocks instead of the native
field. Their arithmetic goes through a small interface:

```
-- the field the verified STARK lives in, as an Aiur library
module GL {
  fn add(a: GL, b: GL) -> GL      -- native: field add; emulated: add, reduce
  fn mul(a: GL, b: GL) -> GL      -- emulated: a·b = q·p + r, r < p, q < 2^64
  fn eq(a: GL, b: GL) -> Bool
  fn from_le_bytes(b: [U8; 8]) -> GL   -- canonical-byte check (gl_lt_p)
}
module GLExt { … }                -- the quadratic extension, over GL
```

Over BN254 a Goldilocks element fits in one Fr element (p < 2^64 ≪ r), so
emulation is a range check plus one bounded-quotient relation per
multiplication: the same relation `foreign.rs` encodes by hand today, but as
an Aiur library function with a Lean correctness theorem, like the existing
U32/U64 libraries (`Aiur/Aiur/Library/U32.lean`). BLAKE3 needs no change: the
library is byte-oriented and specialized to a field with `toField F`
(`Aiur/Aiur/Library/Blake3/Goldilocks.lean`).

The verifier modules are parameterized over `GL` instead of using `Field`
directly (`type Goldilocks = Field` today, `Aiur/Aiur/Library/Field/Goldilocks.lean`).
Over Goldilocks the interface is the identity, so `ix_aggr` is unchanged;
over BN254 it is the emulation.

The native interface is `GoldilocksSignature`
(`Aiur/Aiur/Library/Field/Goldilocks/Signature.lean`). Its transparent
one-field representation checks operation types; each provider must establish
canonical residues and arithmetic semantics. `gl_val` reduces any eight-byte
word, while `gl_from_bytes` rejects encodings at or above the modulus. The
existing verifier uses both reducing conversions and canonical output
encodings; changing one into the other is a protocol change. A BN254 host
must also replace the ambient-field `goldilocks.inverse` advice with explicit
Goldilocks inversion.

Native inline helpers preserve the default aggregation and recursion backend
key bytes in the export comparison, but change bytecode and population-plan
metadata in the `.ixa` artifacts. Artifact/source caches and generated native
executors therefore need regeneration. Backend-key identity and full artifact
identity are separate validation gates.

`CompressGL` takes the aggregation key as data (§2), so it replaces the FRI
stage, the first KZG stage, the layout and normalization at once. Its BN254
proof's shape depends on the root's size, which is why a second stage
follows.

### 3.2 `CompressBN`: a KZG multi-stark verifier running over BN254

Verifies a `KzgConfig` multi-stark proof: the same `StarkVerifier`
structure (constraints, LogUp lookups, DEEP/quotient checks) with KZG
openings instead of FRI. New libraries:

```
module Fq   { … }   -- BN254 base field, emulated in Fr (limbs, bounded quotients)
module G1   { add, double, scalar_mul, msm }   -- over Fq
module Kzg  { fn verify_opening(…) -> PairingCheck }  -- defers the pairing
```

#### Deferred pairings across layers

A KZG opening check reduces to one pairing equation. `CompressBN` defers
the verified proof's opening equation as public values, as today's recursive
stage does. Once `CompressBN` verifies another `CompressBN` proof,
two obligations exist: the child's carried equation and the new one from the
child's own openings. Authenticating the child's public values does not
establish the child's equation, so neither may be dropped. Today's verifier
checks both (`pipeline/wrap/recursive.rs`, `verify`); a chain of layers
folds them instead.

Every KZG proof in the chain uses the same SRS, so each pending equation has
the form `e(P, [1]₂) = e(Q, [τ]₂)` with the same G2 elements. Each
`CompressBN` statement carries one accumulator `(P, Q) ∈ G1²`:

1. Verify the child proof up to its opening check, reducing the opening to
   a pending pair `(P_new, Q_new)` without computing a pairing.
2. Read the child's accumulator `(P_c, Q_c)` from the child's statement,
   bound to the child proof checked in step 1. The first `CompressBN` layer,
   verifying `CompressGL`, starts from the identity.
3. Derive `ρ` from the transcript after absorbing the child proof, its
   accumulator and `(P_new, Q_new)`.
4. Output `(P_new + ρ·P_c, Q_new + ρ·Q_c)` as this proof's accumulator.

For fixed pairs and an independent uniform `ρ`, if either equation fails
the folded one holds with probability at most `1/|Fr|`. The Fiat–Shamir
soundness analysis must also account for transcript queries and challenge
sampling. One pairing check on the final folded accumulator discharges the
chain. Each nontrivial fold costs two emulated G1 scalar multiplications and
two additions; the scalar decomposition can be shared.

#### Dynamic intermediate shapes

Aiur verifier programs read proof dimensions as data. `CompressGL` and
`CompressBN` can therefore compose with varying trace heights and circuit
activation, within the backend's admitted bounds. Neither their interfaces
nor `CompressFinal` require a normalized terminal `CompressBN` layout.

Repeated verification does not by itself guarantee convergence to one
shape. Additional `CompressBN` layers are useful only if they reduce the
work needed by the final verifier enough to justify their proving cost.
Measure whether an input can be brought within `CompressFinal`'s execution
capacity and how many layers that takes; do not assume a fixed point or a
bounded layer count.

### 3.3 The final PLONK proof

The final stage proves, in PLONK over BN254, that one `CompressBN`
proof verifies and that its accumulator's pairing equation holds. Its
relation is written as an Aiur program too, `CompressFinal`, instead of the
hand-written gnark circuit (`tools/gnark/circuit.go`):

```
fn compress_final(statement: Statement) {
  let (proof, acc) = read_compress_bn_proof();
  let pending = CompressBN::verify_to_opening(proof, statement, acc);
  Pairing::check(fold(pending, acc));   -- emulated BN254 pairing over Fq
}
```

As with the FRI and KZG verifier programs, Aiur expresses the relation and
native proving software proves its execution. The new component is a
generic Aiur-to-PLONK compiler backend; writing a PLONK verifier in Aiur
would not itself make Aiur executions produce PLONK proofs.

```text
CompressFinal (Aiur source)
  → compiled Aiur constraints and execution witness
  → generic PLONK constraint and witness lowering
  → stock gnark prover with Ignition
  → PLONK proof and gnark-exported Solidity verifier
```

The exporter must preserve arithmetic constraints, function-call and memory
channels, lookup multiplicities, activation, fixed tables, depth checks and
public claim binding. Gnark's log-derivative machinery supplies useful
primitives; mapping Aiur's execution rules to them is new backend work, not
an automatic consequence of using lookups in both systems.

For one deployed PLONK key, the exporter chooses a bounded capacity for
`CompressFinal`'s own execution, generates padding and activation constraints,
and rejects executions that exceed it. Input-proof dimensions remain data.
Even fixed input dimensions do not fix the actual execution row counts,
because memoization, memory interning and branches can depend on values.
Capacity belongs to the generated final circuit, not to a hard-coded layout
between Aiur stages. Its key depends on `CompressFinal`, the compiler and
exporter, capacity, authenticated constants and setup parameters.

That capacity has a concrete upper bound. The admitted Ignition ceremony
has 100,800,000 G1 powers, but the current importer retains at most `2^26`.
Gnark chooses `N = next_power_of_two(constraints + public_inputs)` and needs
`N + 3` powers. The Rust exporter currently rounds that request up again to
a power-of-two prefix. Its largest usable domain is therefore `2^25`, or
33,554,430 constraints with the existing two public inputs. One additional
constraint requires `N = 2^26` and a `2^27`-power loaded prefix, exceeding
both the retained file and the full ceremony. A loader that retained and
served `2^26 + 3` powers could support the larger domain without a new
ceremony; that is a separate parameter-format/loader change. The pure
`pipeline::plonk_limits` helper checks these bounds before allocation.

`CompressFinal` reuses `CompressBN`'s KZG verification logic and accumulator
fold, then checks the folded pairing. A fully Aiur implementation needs a
constrained BN254 pairing library, including extension-field arithmetic and
a Miller loop with a final-exponentiation check or a sound equivalent.
Arkworks can compute hints; it does not supply the Aiur constraints that
validate them. This is additional work beyond the Fq/G1 operations used by
`CompressBN`.

The target discharges the pairing inside the final relation, so on-chain
verification consumes only a PLONK proof. Exposing the final folded
accumulator for an extra on-chain pairing is a separate tradeoff: it adds
public inputs, calldata and verifier work, and must be measured separately.

#### Proof size and verification cost

The [recorded Init measurements](proof-benchmark-comparison.md#matched-init-final-measurements)
give 584 bytes for the native PLONK proof, 624 bytes for its Ix envelope and
864 bytes for the Solidity proof payload. The last number excludes public
inputs and ABI overhead. The current compression README describes the
recursive KZG endpoint as roughly 2.1 KB; compare the same serialization and
workload when assessing bandwidth savings. Fewer proof bytes reduce payload
bandwidth, but do not establish a proportional reduction in verification
time or gas.

In pinned gnark revision `262cf453c107`, `Proof.MarshalSolidity`
(`backend/plonk/bn254/solidity.go`) emits `768 + 96·m` bytes, where `m` is
the auxiliary commitment count. One shared auxiliary commitment preserves
the 864-byte target. Gnark's `multicommit` combines requests into one
commitment, but the exporter must verify that its challenge dependencies
permit that construction. Measure commitment count, public input size and
verification gas alongside constraints, proving time and peak memory.

The Aiur compiler theorems apply to the source-to-circuit part. The new
PLONK lowering and the correctness of the verifier and pairing programs
remain separate obligations (§5). Retire the hand-written final circuit
only after correctness checks and a matched PLONK performance comparison;
the existing Groth16 R1CS count is not a PLONK cost estimate.

### 3.4 Incremental Goldilocks wrapper

The first implementation path retains the existing hand-written FRI, KZG
and PLONK stages and inserts a small Goldilocks Aiur program, `CompressWrap`,
before them. It calls the existing generic
`MultiStark::verify_multi_stark_proof` on the root key and expected claim rows
as data. A selected fixed layout normalizes this wrapper, so the hand-written
FRI circuit depends on the wrapper program and its layout rather than on
IxVM or `ix_aggr`. This fixed boundary belongs to the incremental path;
the full Aiur pipeline in §§3.1–3.3 keeps its intermediate shapes dynamic.

Using the generic recursion entry unchanged would leave the root key digest
in its public prefix, which today's final circuit embeds in its key. The
dedicated `CompressWrap::verify_root` entry therefore exposes eight reserved
zero words followed by the digest of this 84-byte preimage:

```text
"ix/compress-wrap/v1\0" || BLAKE3(root_key_bytes) || BLAKE3(root_claim_rows_bytes)
          20 bytes              32 bytes                    32 bytes
```

It computes both digests from the advice streams, checks the public statement
digest, and invokes the generic verifier. Its 18-word Aiur claim has a fixed
call channel, entry index and zero prefix; only the final eight words vary.
The host independently pins the root key and supplies the expected original
claim rows before executing or proving the wrapper. Verification derives the
same expected digest from those trusted inputs.

This changes the public statement API: the final PLONK digest authenticates
the root key and serialized root claims, not only the original Ix claim
bytes. Existing release keys and `ix verify` do not implicitly authorize
this statement. The research bridge uses separately derived keys and
explicit expected inputs; production adoption needs a versioned statement
policy and verifier deployment. The PLONK protocol and Ignition ceremony
remain unchanged.

The wrapper can reduce key churn without implementing BN254 execution in
Aiur or a generic Aiur-to-PLONK exporter. It adds a Goldilocks execution and
proof; its cost must be measured on the same root as the hand-written FRI
comparison. A fixed wrapper layout also has a supported input bound and may
need a new release if future inputs exceed it. Neither its runtime nor the
cost of the full BN254 design follows from unrelated aggregation-wrap runs.

## 4. What changes

| | Today | Aiur compression |
|---|---|---|
| IxVM or `ix_aggr` change | release re-derivation; key/layout changes propagate through fixed stages, and prefix changes specialize the final verifier | new authenticated digest in the statement; no key changes while backend bounds and final capacity suffice |
| Root layout and normalization | required | removed: `CompressGL` reads any root shape |
| Aiur compiler coverage | none of the compression circuits | `CompressGL`, `CompressBN`, `CompressFinal` and their Aiur libraries; backend lowering and source correctness remain separate (§5) |
| Keys | per release, pinned in `verifying_keys.rs` | per compiled compression program and backend parameters; final PLONK key also depends on exporter, capacity and authenticated constants |

## 5. Trust after the change

The Aiur audit (`Aiur/Aiur/Audit.lean`) proves compiler and derivation
soundness over an arbitrary field, with field-size side conditions stated as
lower bounds on the characteristic (`characteristic` in
`Optimized/Depth/EndToEnd.lean`; LogUp multiplicity sums below p). BN254 Fr
satisfies them; each `_goldilocks` corollary needs a `_bn254` counterpart.

Still trusted, as today for the root:

- the Rust lowering of compiled circuits to multi-stark;
- multi-stark's AIR/LogUp soundness, now also with `KzgConfig` (the KZG PCS
  in `proof-compression/src/kzg`) and the BN254 transcript;
- the admitted Ignition SRS and its ceremony assumptions, shared by the KZG
  and PLONK backends; reusing it does not make their proof protocols identical;
- gnark's PLONK prover, its exported Solidity verifier, and the export of
  Aiur execution constraints, lookups and public claims to a gnark constraint
  system, including padding and capacity enforcement;
- that the verifier *programs* implement the verifiers: the library
  theorems cover Lean models of the libraries, not the verifier modules
  (`Audit.lean` notes this for IxVM and MultiStark). Program-level
  correctness of `StarkVerifier`, `Kzg`, the accumulator fold and `Pairing`
  is new proof work about Aiur source. Compiler soundness alone does not
  establish that these programs implement the intended protocols.

The gain is that the verifier logic, today the largest unverified surface,
moves inside the formalized compiler's scope.

## 6. Work required

**Rust (`crates/aiur`).** Current field and serialization boundaries are 64-bit:

- `FieldBackend` (`modulus() -> u64`, `from_u64`), `NativeField<F: PrimeField64>`
  (`field.rs`) and `bytecode::Program.modulus: u64`: generalize to a
  multi-limb field, or add a BN254 backend beside the Goldilocks one.
  Separate checked conversions for bounded counters/indices from full field
  serialization. Truncating to the low limb is not a valid implementation
  of `to_u64` for arbitrary Fr values.
- The trace adapter fixes `System<GoldilocksBlake3Config>` and rejects other
  moduli (`trace/stark.rs`); `WitnessField::words()` assumes a transparent
  `u64`. A `System<KzgConfig>` adapter proves the same `CircuitInputs`
  (constraints and lookups) that `KzgConfig` already accepts in
  `proof-compression`.
- Artifact version 2 is limited to 64-bit moduli and constants on both sides.
  The Lean `modulus: Nat` signature does not make the encoding wide:
  `Execution/Encode.lean` rejects moduli at or above `2^64`, and `Ixon.lean`
  rejects such naturals before writing its UInt64 TagN. Trace constants have
  the same bound. A versioned encoding must add wide field values while
  keeping counts and indices bounded; the Rust reader and generated native
  executors (`formal-generated`) also need the corresponding support.

**Lean.** Parameterize the verifier modules over a `GL` interface (§3.1); write
`GL`, `Fq`, `G1`, `Kzg` and `Pairing` libraries, including the pairing's
extension fields, with correctness theorems; instantiate the audit corollaries
at BN254.

**PLONK backend.** Lower the exported Aiur circuits and execution witness to
gnark sparse constraints. Arithmetic lowering is only part of this work:
calls, memory, lookups, activation, multiplicities and depth must preserve the
existing execution semantics. Generate final capacity and padding rules,
retain gnark's proof format and Solidity export, and derive the new circuit
keys from Ignition. The first milestone is a small Aiur program with calls,
memory and lookups, verified in Solidity. Check that changing its claim or
corrupting its execution witness is rejected, and record constraints,
commitments, payload size and gas before scaling to `CompressFinal`.

**Libraries.** Native arithmetic is available; constrained Aiur libraries
still need implementation:

- BN254 Fr in multi-stark's field traits already exists as
  `proof-compression`'s `kzg::field::Scalar` (`ark_bn254::Fr` behind
  multi-stark's `Field`/`TwoAdicField`), the type `KzgConfig` proves with.
  It is not an implementation of the `p3::PrimeField64` bound used by today's
  `NativeField`. Its canonical limbs and checked `canonical_u64` conversion
  are useful boundary APIs. It moves to a shared crate for `crates/aiur`.
  BN254 arithmetic comes from
  arkworks only: Plonky3's `p3-bn254`, a wrapper of the same arkworks type,
  is deprecated from Plonky3 0.9.0, and the pinned Plonky3 is not bumped for
  this work. Later Plonky3 releases serve as a guide to where its field and
  PCS traits are heading, so the shared crate tracks their shape without
  depending on them.
- Fq, G1/G2, pairings, MSM and FFTs over Fr come from `ark-bn254`, `ark-ec`
  and `ark-poly`, with `sppark` for the GPU MSM; all are dependencies today.
  They compute the hints the emulation libraries check.
- What libraries cannot remove is `crates/aiur`'s assumption of 64-bit
  fields. The first BN254 path supports the interpreter and host trace
  population only; native executors and CUDA population stay
  Goldilocks-only until measurements call for them. Measure execution and
  proving separately before choosing further acceleration; verifying one
  proof can still involve substantial work.

**Hashing.** Root Merkle trees and the inner FRI/KZG transcripts retain
BLAKE3; replacing them with Poseidon2 or another arithmetization-oriented
hash is outside this design. A FRI proof over BN254 with BLAKE3 Merkle trees
would make the final verifier hash bytes for every query path, so the BN254
stages use KZG commitments. The final PLONK protocol retains pinned gnark's
Solidity-compatible transcript.

`CompressBN` must reproduce the KZG transcript's canonical 32-byte Fr
encoding and BLAKE3 XOF behavior (`kzg/transcript.rs`): 64 output bytes
reduced into Fr, followed by 32 bytes for the next state. Aiur's existing
32-byte hash entry point alone does not implement that transcript; add and
cross-check the XOF and wide-field encoding paths as part of the libraries.

Lookup challenge expansion inside the PLONK exporter is a separate decision:
pinned gnark's multicolumn `logderivarg` helper uses MiMC internally.
Reusing that helper unchanged would introduce MiMC into the backend. Resolve
whether to admit that backend primitive or implement BLAKE3-based expansion
before choosing the lookup lowering; a blanket BLAKE3-only claim would not
describe stock gnark's helper.

**Proof system.** `KzgConfig` already uses BN254 Fr as its own challenge
field (extension degree one). Generalizing the Aiur Rust lowering must
preserve that configuration and remove assumptions specific to Goldilocks'
quadratic extension and FRI blowup. This lowering is unverified.

## 7. Costs and open questions

- **Size.** Hand-written gadgets are tuned per gate; Aiur programs pay for
  general memory and channel lookups. The overhead must be measured before
  committing: measure the verifier over *Goldilocks* first, with the field
  interface instantiated natively. `CompressWrap` supplies this baseline
  against the hand-written FRI verifier of the same root.
  Compare the same key, proof, public claims and FRI parameters. Stage-one
  advice plus fixed-table cells are comparable across the two paths; frontend
  gate/value counts and total committed cells measure different things.
  Report stage-two and quotient arrays separately. Scaling Goldilocks cells
  from 8-byte to 32-byte elements is a lower-level storage estimate, not a
  measured BN254 peak or evidence that the full pipeline fits memory. KZG
  also removes the FRI blowup and uses extension degree one; its coefficient
  arrays and quotient strategy differ. These effects and emulated-GL rows
  must be measured together before projecting a BN254 memory budget.
- **BN254 proving speed.** Fr uses wider elements and a different commitment
  backend, with FFT/MSM costs that depend on shape and implementation. The
  existing first KZG stage supplies a measured baseline; both emulated-GL
  cell counts and actual BN254 proving time are needed for comparison.
- **Recursion depth.** How many `CompressBN` layers make final verification
  fit the PLONK execution capacity, whether further layers reduce work, and
  whether the count is bounded for supported inputs. Intermediate shapes
  remain dynamic; no convergence to a terminal layout is assumed (§3.2).
- **Emulated-field cost of `G1` over Fq in Fr.** Today's recursive gadgets
  (`native_field.rs`, `native_msm.rs`) set the baseline to beat or match.
- **Final pairing and PLONK cost.** Measure the Aiur pairing library and the
  generic lookup/memory lowering against the existing final PLONK circuit.
  Check the 864-byte payload target independently of constraint count and
  verification gas. A correct but much larger circuit may make proving
  memory or time the limiting factor.
- **Implementation scope.** After BN254 and `CompressBN` exist, the final
  program mostly reuses their verifier logic. The generic PLONK exporter
  and constrained pairing library are substantial additions. Size the work
  from the small-program prototype; formal correctness is a separate effort.

## 8. Steps

The Goldilocks wrapper and matched measurements are the first decision point.
The full BN254 and PLONK-exporter track proceeds only after those results
support its expected cost; formal verification has its own work budget.

1. **`GL` interface over Goldilocks.** Refactor the verifier modules onto it,
   with the native instance; compare the default aggregation and recursion
   backend keys byte-for-byte. Record artifact-byte changes separately and
   regenerate affected execution caches. No new field.
2. **`CompressWrap` and matched measurements.** Implement the stable-prefix
   statement and normalize the generic Goldilocks verifier (§3.4). Compare
   its execution with the hand-written FRI verifier of the same root: cells,
   prove time and memory. Use Init before extrapolating to full BN254 work;
   small fixtures validate the tooling and statement binding only.
3. **BN254 backend in `crates/aiur`.** Multi-limb field, bytecode modulus,
   `System<KzgConfig>` adapter; prove a small Aiur program end to end over
   BN254 with KZG. First round-trip wide moduli/constants in the versioned
   artifact format and execute arithmetic that forces wide values, such as
   `x + 1` at `x = r - 1` and inversion of two, before adding the prover.
4. **`CompressGL` over BN254.** Emulated `GL`; replaces FRI and first KZG.
5. **`CompressBN`** with the accumulator fold and dynamic proof shapes.
6. **Generic PLONK exporter prototype.** After step 3, prove a small Aiur
   execution with calls, memory and lookups using gnark and Ignition, and
   verify it with gnark's Solidity export. Establish capacity enforcement,
   negative witness checks, commitment count, proof size and gas.
7. **`Pairing` and `CompressFinal`.** Extend the prototype to the final
   verifier, with generated execution capacity and padding. Measure extra
   `CompressBN` layers by their effect on final verification cost.
8. **Matched validation.** Compare against the existing PLONK endpoint on
   the same workloads, including proving time, memory, payload and gas;
   retire the hand-written final circuit after the comparison succeeds.
9. **Formal coverage.** BN254 audit corollaries; library theorems for `GL`,
   `Fq`, `G1`, `Kzg`, the pairing extension fields and `Pairing`; source-level
   verifier and accumulation correctness; correctness of the PLONK lowering.

## 9. Goldilocks research entry points

The wrapper commands operate on explicit files and independently supplied
root-key pins and expected claim rows. They do not replace the production
`ix compress` release catalog. Export the wrapper and build the tools:

```sh
lake build multiStark/stark-export
lake env MultiStark/.lake/build/bin/stark-export export-trace compress-wrap.ixa --compress-wrap
cargo build --release --locked -p stark-verifier --features parallel
cargo build --release --locked -p ix-proof-compression --examples
```

Given a natively verified `root/` with `root-vk.bin`, `root-claims.bin` and
`root-proof.bin`, `ROOT_KEY_BLAKE3` must be the independently authorized key
digest. A plan samples the required heights; release selection must cover
the supported workload instead of choosing a new layout for every proof.

```sh
target/release/stark-verifier wrap-plan compress-wrap.ixa \
  root/root-vk.bin root/root-claims.bin root/root-proof.bin \
  "$ROOT_KEY_BLAKE3" wrap-plan 0
target/release/stark-verifier wrap-prove compress-wrap.ixa \
  root/root-vk.bin root/root-claims.bin root/root-proof.bin \
  "$ROOT_KEY_BLAKE3" wrap-plan/layout.json wrap-proof
target/release/stark-verifier wrap-verify compress-wrap.ixa \
  "$ROOT_KEY_BLAKE3" root/root-claims.bin wrap-proof/proof.bin wrap-plan/layout.json
```

The `ix-prover` example `export_root` derives expected Ix claim bytes from an
environment and manifest, or extracts an existing `IXAGGR2` proof after
checking those bytes and independently pinned artifacts. It preserves the
raw root proof without adding a normalization wrap.

Sizing has explicit allocation levels. `--count-root` walks the exact
verifier builder with a counting backend and retains no circuit or witness.
`--check-root` materializes them and can require substantial memory; it still
does not allocate the proving traces. Only the latter produces physical
layout metrics for the matched comparison.

```sh
target/release/examples/fri_sizing --count-root root
target/release/examples/fri_sizing --check-root root handwritten-cost
target/release/examples/compression_costs compare \
  wrap-plan/report.json handwritten-cost/circuit-cost.json
target/release/examples/compression_costs plonk 33554430 2 67108864 100799999
```

The `compress_wrap` example bridges a proven wrapper to the existing
pipeline. Its `prepare` mode validates the wrapper artifact/key pin, original
root pin and claims, composite statement and exact normalized proof geometry
before writing the compression input. Its `compress` mode runs the existing
FRI/KZG stages and optionally PLONK (`--plonk`, built with the `plonk` feature).
Ignition is the default; `--dev-srs` explicitly selects development parameters.
The resulting `claim.bin` contains the 84-byte composite statement preimage.
Locally derived candidate keys require independent authorization before use
by another verifier; the example's self-check does not grant that authority.

## 10. Matched Goldilocks sizing

[Recorded input and artifact identities](measurements/aiur-compression-goldilocks.json)
identify the exact roots, FRI parameters, wrapper artifact and construction
choices for these measurements. Each row compares verification of the same
root key, claim rows and proof bytes. Both use the production FRI parameters
(blowup four, 100 queries, 20 query proof-of-work bits).

| Input | Aiur stage-one advice | Aiur fixed | Hand-written stage-one advice | Hand-written fixed | Aiur / hand-written, combined |
|---|---:|---:|---:|---:|---:|
| Tiny square fixture | 1,456,390 | 989,184 | 22,414,368 | 25,037,920 | 0.05154 |
| Init aggregate root | 868,054,410 | 989,184 | 1,439,499,296 | 1,699,155,040 | 0.27688 |

These are padded Goldilocks cells. The tiny height-one input has unusually
strong memoization sharing and is not representative of a large root. The
Init root certifies 56,312 logical constants, with 599 unsafe or partial
constants excluded by the same subject policy as the shard prover and Lean
acceptance path. Its hand-written comparison uses the generic batch verifier
with compact BLAKE3; the Aiur layout is normalized with zero extra headroom.

For Init, Aiur's combined stage-one and fixed arrays contain 869,043,594 cells
(6,952,348,752 bytes), versus 3,138,654,336 cells (25,109,234,688 bytes) for the
hand-written circuit. Aiur additionally has 372,751,008 stage-two base-field
cells and 47,456,668 quotient cells, recorded separately. The combined ratio
therefore measures those two array classes, not total prover memory or speed.
It does not support an inference that Aiur is larger from comparing its
committed cells to the hand-written frontend's gate/value counts. The BN254
emulation and proposed Aiur-to-PLONK exporter's costs remain unmeasured.

[Three fresh-process GPU pairs](measurements/aiur-compression-matched-gpu.json)
also measured both paths on that original Init root, sequentially with no
overlapping proof jobs or thread overrides. The machine had 32 logical CPUs
and one 96 GB RTX PRO 6000 Blackwell GPU. Median complete-command results:

| Path | Elapsed | Peak host RSS | Output proof |
|---|---:|---:|---:|
| Aiur `CompressWrap`, normalized | 9.51 s | 7.88 GiB | 5,427,662 bytes |
| Hand-written generic compact FRI verifier | 93.66 s | 148.80 GiB | 1,367,315 bytes |

Elapsed time includes validation, setup, execution or circuit construction,
proving, verification and serialization, with up to 0.5 seconds of completion
sampling granularity. Host RSS excludes VRAM. The hand-written path used the
backend's supported GPU/host split and admission fallbacks. Aiur produces a
larger intermediate proof, so the result measures one layer of verification
and proving work, not an end-to-end compression speedup or a BN254 projection.

## 11. Incremental pipeline validation

The [incremental validation record](measurements/aiur-compression-incremental.json)
records an Init root passing through `CompressWrap`, the existing FRI and KZG
stages, and the existing gnark PLONK backend under Ignition. This exercises
the Goldilocks wrapper path in §3.4; the BN254 Aiur programs and generic
Aiur-to-PLONK exporter remain later work.

| Final artifact or check | Result |
|---|---:|
| PLONK constraints | 14,689,424 |
| PLONK domain | `2^24` |
| Native proof | 584 bytes |
| Ix envelope | 624 bytes |
| Solidity proof payload | 864 bytes |
| Adapter ABI calldata | 964 bytes |
| Local EVM verifier call, excluding transaction intrinsic gas | 292,004 gas |

The local EVM tests use solc 0.8.37 with Prague compilation and Osaka execution.
The expected composite digest was independently derived from the authorized
root key and original claim rows before consuming the PLONK proof. Altered
proofs and both altered digest halves are rejected.

A second, distinct square-relation root key was proved and compressed under
the same Init wrapper layout. Both runs produced byte-identical wrapper,
FRI, recursive KZG and PLONK keys and identical exported Solidity source.
One verifier instance accepts both proofs with their independently expected
digests and rejects both cross-swapped proof/digest pairs. The two workloads
are different, so their cold/warm run times are not a speedup comparison.

A checkpoint test substituted the alternate root's final PLONK proof into
a copy of the Init run. Resumption verified and reused the earlier three
stages, rejected the mismatched PLONK proof, and regenerated only that stage.
The repaired proof passed local EVM verification under the independently
expected Init digest; the original outputs and all fixed keys were unchanged.

The output keys remain separately derived candidates. The production release
catalog and deployed contracts are unchanged; adoption requires the
versioned statement policy described in §3.4 and independent authorization
of the new key. Existing default aggregation and recursion verification keys
remain byte-identical after the native GL interface refactor. Their changed
artifact identities and the acceptance-path fingerprint have separate review
candidates, as the repository's pin gates require.
