# Compression architecture options

Two alternative restructurings of the proof-compression pipeline, written so
that each can be evaluated against the same baseline and measurements:

- **Plan A: BN254 with sharding and a final PLONK proof.** Port the KZG stages
  from BLS12-381 to BN254, shard the recursive stage across GPUs, and wrap the
  result in a standard BN254 PLONK proof.
- **Plan B: five stages with a retuned FRI compression.** Retune stage 3 so
  that the KZG stage verifying it fits in one circuit, drop the recursive KZG
  stage, and keep the PLONK wrapper as an optional gas optimization.

Neither plan has been implemented or measured. The plans are not mutually
exclusive, but Plan B's first experiment is cheaper and its outcome changes
what Plan A would be optimizing, so it should run first.

Source references pin ix `faba9bdd4445295f08dfbcf773ada80afe3f0c35` and its
working-tree wrapper status in
[`plonk-wrapper-status.md`](plonk-wrapper-status.md), multi-stark
`sb/kzg-core`, and ZisK pil2-proofman PR 610 at
`971579d5ea1b5ec3f7b1233aac3342d90686b844`.

## Baseline pipeline

| Stage | Output | Prover | Measured cost |
| --- | --- | --- | --- |
| 1. FRI shard proving | 25+ MB | Goldilocks, BLAKE3 | Not part of compression |
| 2. FRI recursive aggregation | about 5 MB | Goldilocks, BLAKE3 | Not part of compression |
| 3. FRI compression | about 1.5 MB | Goldilocks GPU | 61–62 s, 213 GiB host peak |
| 4. First KZG stage | tens of KB | BLS12-381 GPU, 11+ partitions of `2^24` or `2^25` rows | 165–178 s warm |
| 5. Recursive KZG stage | 2,181 bytes | BLS12-381 GPU, one `2^27` computation trace | 107–121 s warm |
| 6. gnark PLONK wrapper | 624-byte BN254 / 784-byte BLS envelope | BN254 or BLS12-381, CPU | Actual Init: 53.79 s / 127.17 s core proving; BN254 `N = 2^24`, BLS `N = 2^25` |

KZG stage timings are the one-GPU warm runs recorded in multi-stark
`docs/kzg-merge-plan.md`. PLONK timings are the separate native CPU measurements
in the [wrapper status](plonk-wrapper-status.md). The partition rule is
[`MIN_PARTITIONS = 11`](../crates/proof-compression/src/pipeline/first.rs)
with heights checked in
[`wrap/saved.rs`](../crates/proof-compression/src/pipeline/wrap/saved.rs).
The wrapper figures come from the status document.

On-chain verification today:

| Verifier | Gas | Boundary |
| --- | ---: | --- |
| Direct Solidity verifier of the stage-5 packet | 757,950 | Execution only; about 3.7 KB ABI calldata extra |
| Same, after its known compatible optimizations | about 620,000 | Design estimate: pairing folding, fixed-commitment relations, witness MSM split |
| gnark BLS12-381 PLONK, tiny `m = 1` backend proof | 371,471 | Execution around the adapter call; 1,284 bytes ABI calldata extra |

All-in comparisons must add the 21,000-gas intrinsic cost and calldata to both
sides. On that basis the wrapper saves roughly 250,000–300,000 gas per
verification against the optimized direct verifier.

Three facts constrain both plans:

- **BLAKE3 is required** throughout. Poseidon2 and Keccak transcripts are out
  of scope.
- **Curve recursion is the dominant structural cost.** Stages 5 and 6 each
  verify a BLS12-381 KZG proof inside a circuit over the same curve's scalar
  field. That needs emulated base-field arithmetic for every untrusted G1 point
  and every pairing. Each stage's cost scales with the number of commitments
  and the transcript bytes of the proof it verifies.
- **Stage 3 is not tuned for stage 4.** [`pipeline/root.rs`](../crates/proof-compression/src/pipeline/root.rs)
  proves it with the root key's own parameters, `GoldilocksBlake3Config::new(cp, fp)`.
  Those are the Aiur defaults in
  [`Ix/Aiur/Protocol.lean`](../Ix/Aiur/Protocol.lean): blowup 4, 100 queries,
  binary folding (`maxLogArity = 1`), Merkle cap height 0, and 20 query
  proof-of-work bits.

## Plan A: BN254, sharding and a final PLONK proof

### Proposal

1. Port the KZG stages from BLS12-381 to BN254.
2. If the smaller base field brings the recursive trace down to `2^26`, shard
   it with a `2^25` cap so that two GPUs each prove one shard.
3. Add a standard BN254 PLONK proof (gnark) that verifies the recursive KZG
   proof, for cheap Solidity verification.

### Expected benefits

- **Faster G1 MSMs.** BN254's base field is 254 bits against BLS12-381's 381
  bits; MSMs are typically 1.5–2× faster. FFTs, quotients, LogUp and witness
  generation are unchanged, because both scalar fields use four 64-bit limbs.
- **Cheaper emulated arithmetic in stage 5.** The recursive gadget represents
  BLS12-381 Fq as five 80-bit limbs
  ([`native_field.rs`](../crates/proof-compression/src/recursive/native_field.rs)).
  BN254 needs four, so a multiplication has 16 limb products instead of 25.
  If this arithmetic dominates the `2^27` trace, the trace could halve.
- **Sharding.** The first KZG stage already uses the sharded lowering. Shards
  run as separate GPU jobs, and smaller columns may avoid the constraint-pass
  path. A `2^26` cap gives no benefit once the trace is already `2^26`.

### Costs and risks

- **Security margin.** BN254 is estimated at roughly 100–110 bits after the
  extended tower number field sieve; BLS12-381 at roughly 117–120. BN254 is
  the norm for Ethereum proof systems (SP1, RISC Zero, Aztec), but a single
  break of it would forge proofs for every BN254 system at once. The weakest
  link of the whole system includes the FRI layers' security level, which has
  not been compared here.
- **Two-adicity.** BN254 Fr supports FFT domains up to `2^28`; BLS12-381 Fr up
  to `2^32`. [`shape.rs`](../crates/proof-compression/src/recursive/native_verifier/shape.rs)
  requires `log(trace) + log(quotient factor) <= TWO_ADICITY`. The degree-3
  gate gives a quotient factor of 2, so a `2^27` trace needs exactly `2^28`
  with no headroom; a `2^26` trace restores one bit.
- **Setup.** The Filecoin ceremony is BLS12-381 only. BN254 needs Perpetual
  Powers of Tau (up to `2^28`). The Filecoin import, receipts, caches and test
  plan would be redone.
- **Port scope.** Arkworks curve types, the CUDA build's `FEATURE_BLS12_381`,
  the field-gadget constants, the compact codec, the Solidity verifier and
  every fixture and verifying key change.
- **Gas from the curve alone is small.** Under EIP-1108 the current verifier's
  curve work is about 459,700 gas against 497,148 under EIP-2537. BLS12-381
  pairings are cheaper than BN254's since Pectra. Most of the gas saving comes
  from the final PLONK proof, which can equally be a BLS12-381 PLONK proof
  (gnark's EIP-2537 template, already prototyped in the wrapper branch).
- **The final PLONK proof still recurses over its own curve.** BN254 has no
  pairing-friendly partner curve. The wrapper must emulate the pairings or
  expose an accumulator and fold it into the PLONK pairing check, exactly as on
  BLS12-381.
- **More stages, not fewer.** Plan A keeps all six stages. Any prover time
  saved by BN254 and sharding is partly spent on the wrapper.

### Measurements that decide Plan A

1. The share of the `2^27` recursive trace that is emulated base-field
   arithmetic, from the existing circuit statistics.
2. GPU MSM time for BN254 against BLS12-381 at `2^27` on the RTX PRO 6000.
3. Single-GPU recursive-stage time at `2^26` without constraint passes, before
   adding shards.

Plan A is worth pursuing only if (1) and (2) both show large gains. Its gas
benefit is not specific to BN254.

## Plan B: five stages with a retuned FRI compression

### Proposal

| Stage | Change |
| --- | --- |
| 1. FRI shard proving | Unchanged |
| 2. FRI recursive aggregation | Unchanged |
| 3. FRI compression | Retuned parameters chosen for stage 4's circuit cost; optionally followed by one small tuned Goldilocks layer |
| 4. KZG stage | One circuit, or close to it, verified on-chain directly |
| 5. gnark PLONK wrapper | Optional; verifies stage 4 instead of the recursive KZG proof |

The recursive KZG stage is removed, together with its `2^27` trace, its
`2^27` SRS requirement and its emulated base-field arithmetic. The curve stays
BLS12-381 with the Filecoin parameters and EIP-2537.

### Rationale

Stage 4's in-circuit cost is dominated by verifying stage 3's FRI proof:
roughly the number of queries times the Merkle path lengths times BLAKE3. With
binary folding, each query opens a Merkle path for each of about 25 FRI layers
in addition to the trace commitments, so stage 4 verifies tens of thousands of
BLAKE3 compressions. This is a source-derived estimate, not a measurement.
That workload is why stage 4 needs 11+ partitions and why its proof is tens of
KB. Stage 5 exists only to shrink that proof.

ZisK's BLAKE3 path in PR 610 makes the same transition with one pairing layer
([`setup_recursivef.rs`](https://github.com/0xPolygonHermez/pil2-proofman/blob/971579d5ea1b5ec3f7b1233aac3342d90686b844/setup/pil2-stark/src/commands/setup_recursivef.rs)):

- After its final aggregation layer it adds **recursivef**, an extra
  Goldilocks STARK tuned for the wrap: blowup `2^5`, folding factor `2^4`,
  27 grinding bits, FRI terminal `2^8`, Merkle caps on the last levels.
- A code comment states this gives **41 queries and a `2^19`-row** BN254 AIR.
  That AIR verifies the BLAKE3 STARK directly, at about 64 rows per
  compression using byte-lookup XOR tables, and is verified on-chain.
- A code comment estimates 272,371 gas for a BLAKE3 key. No BLAKE3 proving time
  is published. The PR is an open draft.

ix's stage 4 performs the same role at roughly `2^28` total rows. Stage 3's
parameters account for a large factor: 100 binary-folding queries against 41
queries folded by 16. ZisK's custom BLAKE3 layout accounts for the rest.

### Wrapper on top of stage 4

A gnark PLONK proof can verify stage 4 just as it verifies the current stage-5
packet, provided stage 4's proof is small. A single-circuit stage-4 proof has
about the shape of the current stage-5 packet, and the wrapper circuit would be
cheaper than the current 23.4M constraints:

- **One pairing equation instead of two.** Stage 4 verifies FRI and does no
  curve arithmetic, so it has no deferred inner pairing.
- **Two fewer untrusted G1 points**, the deferred pairing operands.

That plausibly brings the wrapper under `2^24` (16,777,216 constraints), which
halves its proving time and memory. If stage 4 keeps many partitions, the
wrapper grows with its commitment count and transcript bytes, plausibly toward
`2^26`, and a stage like today's recursive KZG stage is needed again.

Stage 4 itself cannot be a gnark proof: a 96-byte BLAKE3 XOF, two
compressions, costs 261,201 gnark constraints including table overhead, so
thousands of compressions are out of reach for generic PLONK gates. The
specialized GPU prover must absorb the BLAKE3 work.

### Gas outcomes

| Final proof | Gas, approximate | Proof |
| --- | ---: | --- |
| Stage 4 verified directly, current Solidity verifier design | 600,000–750,000 execution | Same shape as today's 2,181-byte packet, without the deferred pairing |
| Stage 4 plus gnark PLONK wrapper | 420,000–450,000 all-in | 1,184 bytes in the Solidity encoding at `m = 1` |
| Stage 4 with fflonk-style packing, verified directly | ZisK reports 270,000–330,000 on BN254 | About 2.2 KB; changes the PCS |

Packing commits many polynomials into a few combined polynomials with one
SHPLONK opening. It is a later, larger change and is not part of the first
experiment.

### Stage-3 retuning experiment

**Question.** Can stage 3 parameters bring stage 4 down to one partition, or
close to it, at an acceptable stage-3 cost?

**Variables**, in increasing order of prover cost:

| Parameter | Baseline | Candidates | Expected effect on stage 4 | Stage-3 cost |
| --- | --- | --- | --- | --- |
| `max_log_arity` | 1 | 3, 4 | Each query opens 3–4× fewer FRI Merkle paths | Small |
| `cap_height` | 0 | 4, 6 | Every Merkle path loses that many levels | A few KB of caps in the proof |
| `query_proof_of_work_bits` | 20 | 24–27 | Fewer queries at equal security | Grinding time, seconds |
| `log_blowup` | 2 | 3, 4, 5 | Fewer queries, about 50–67 at blowup 8–16 | Larger LDE; stage 3 already peaks at 213 GiB |

The query count for each combination must be derived from the project's
security target, not copied from ZisK. Record the conjectured and proven
security levels for each candidate.

**Procedure.**

1. Record the baseline: stage 3 proof size, stage 4 circuit statistics
   (rows by gadget, BLAKE3 compression count), partition count, stage 4 proof
   size and stage 4 time, from the saved aggregate root used by the existing
   benchmarks.
2. Change only stage 3's parameters, which `pipeline/root.rs` currently copies
   from the root key. The root key and stages 1–2 stay unchanged.
3. For each candidate, prove stage 3, then construct stage 4's circuit and
   layout without KZG proving to obtain its size and partition count. The FRI
   stage has a `--check-only` mode; the KZG worker has no equivalent, so this
   step needs a small sizing entry point. Run full stage-4 proving only for
   the candidates that reduce partitions.
4. If blowup is needed but stage 3's memory does not allow it, measure the
   alternative of one additional small Goldilocks layer after stage 3 with the
   high-blowup parameters, as ZisK does.
5. For the best candidate, measure the end-to-end time from aggregate root to
   final stage-4 proof, against the baseline 61 + 165 + 107 s.

**Outputs.** For each candidate: stage-3 time, peak host RSS and proof size;
stage-4 BLAKE3 compressions, total rows, partition count, peak VRAM, time and
proof size; and the security levels above.

**Decision.**

| Result | Next step |
| --- | --- |
| Stage 4 fits in one circuit | Adopt Plan B. Point the direct Solidity verifier and the wrapper at stage 4, and remove the recursive KZG stage. |
| Stage 4 drops to two or three partitions | Measure the wrapper circuit for that shape. Decide whether a small stage 4 plus wrapper beats the six-stage chain. |
| Stage 4 still needs many partitions | Keep the six-stage chain. Continue the wrapper's work toward `2^24`, and consider a BLAKE3-specialized stage-4 layout before revisiting Plan B. |

### Risks

- ix's stage-3 proof spans multiple circuits with LogUp; ZisK's recursivef is a
  single AIR. ix's stage 4 may not reach ZisK's compactness from parameters
  alone.
- Stage 4's generic Plonkish BLAKE3 may cost more rows per compression than
  ZisK's 64-row layout. The gadget-level row counts from step 1 show how much.
- ZisK's figures come from code comments and documentation in a draft PR.
- Changing stage 3 changes the stage-4 circuit, its fixed preprocessing and
  every downstream verifying key, verifier key and fixture.

## Comparison

| | Plan A | Plan B |
| --- | --- | --- |
| Stages | Six | Five, or four without the wrapper |
| Curve recursion layers | Two (recursive KZG, wrapper) | None without the wrapper; one with it |
| Curve and setup | BN254, Perpetual Powers of Tau | BLS12-381, Filecoin (unchanged) |
| Security margin | Reduced, about 100–110 bits | Unchanged |
| First experiment | Port-dependent; trace-share and MSM benchmarks first | Parameter change only; no protocol redesign |
| Gas | About 300,000 class with the wrapper | 600,000–750,000 direct; about 420,000–450,000 with the wrapper |
| Main risk | Large port for an unmeasured speedup | Stage 4 may not shrink enough |

Recommended order: run the stage-3 retuning experiment first, then decide
whether the wrapper is still needed and on which stage. Evaluate Plan A only if
prover time remains the bottleneck afterwards and the trace-share and MSM
measurements both show large gains.

## Choosing the terminal BN254 PLONK relation

Plan A initially retains a separate PLONK wrapper, but the recursive KZG
stage and the terminal wrapper can instead be replaced by one gnark proof:

| Path after first KZG | Relation proved by gnark | Tradeoff to measure |
| --- | --- | --- |
| Recursive KZG, then PLONK | Verify the compact recursive packet, including its opening equation and the deferred first-stage pairing equation | Smaller terminal circuit; retains the native recursive proving stage and its GPU implementation path |
| Direct PLONK | Verify the complete first KZG proof, including its opening pairing equation | Removes one proving stage; moves the larger first-proof verifier into gnark |

Both paths end in a standard BN254 PLONK proof with the independently expected
claim digest as public input. Direct PLONK requires an adapter for the full
first-stage verifier shape; it is not a change of proof encoding or a switch
of the polynomial commitment backend. The current Init first proof has 19
partitions, whereas the existing recursive output has two traces. Constraint
counts from the native recursive frontend do not directly predict gnark's
constraint count or padded domain.

Compile and size both relations before selecting the production path. Pin
the appropriate verifying key, preserve BLAKE3 transcript and canonical
encoding constraints, bind the original claim, and enforce every required
pairing inside the terminal circuit. Compare padded domains, witness/key
memory and total proving time across the complete path, with setup/key
preparation reported separately. Include the availability and cost of GPU
proving for each backend; removing a stage alone does not establish a faster
pipeline. Retuning FRI to reduce the first KZG proof remains complementary to
either choice.

### BN254 gnark wrapper implementation plan

Implementation update, 2026-10-16: the actual authenticated Ignition Init
packet now compiles, proves and verifies through the BN254 helper. The measured
2^25 wrapper had 17,996,081 constraints; core proving took 104.33 seconds. The
subsequent classic-GLV circuit has 14,689,440 constraints plus two public rows,
fitting `2^24` with 2,087,774 rows of headroom. That smaller circuit now proves
and verifies the full Init packet: 53.79 seconds core proving, 73.70 seconds
for the fresh prover process and 25.19 GiB peak RSS. See the
[full benchmark and BLS comparison](plonk-wrapper-status.md#bn254-224-full-init-proof-benchmark).
The shared exporter, curve-specific helper selection, SRS/cache formats and
pinned-admission verifier catalog are implemented. SP1's complete `2^25`
Lagrange basis passed validation against our admitted monomial powers and was
reused for ix's 2^25 keys. Component profiling and batching measurements are
recorded in the wrapper status. The 2^24 basis and keys were generated locally
and are cached. The same proof also passes the adapted SP1 Solidity verifier
on Anvil at 320,103 total transaction gas through ix's expected-claim adapter;
see the [EVM record](../contracts/plonk/README.md#actual-bn254-init-proof-on-anvil).
Full CLI linking remains separate work.
Terminal development-SRS wrapping
remains rejected; the implementation uses authenticated Ignition directly.

The first implementation wraps the verified Init recursive KZG packet with a
standard BN254 gnark PLONK proof. Reuse the BLAKE3 implementation, exported
scalar verifier program, artifact lifecycle and native verification oracle.
Preserve the BLS backend while selecting the curve explicitly in each build.

1. **Export the BN254 verification relation.** Separate the common verifier
   graph/opening export from the BLS-only direct Solidity exporter. The
   baseline `plonk` feature selected `solidity`, which selected BLS12-381, and
   its exporter required Filecoin. Add a curve-tagged verifying key and explicit
   development
   export path that pins the verifying key digest, independently expected
   claim and original statement. Derive dimensions from the codec; retain
   the compact two-trace recursive shape for this first port.
2. **Port the gnark circuit and encodings.** Compile over BN254 Fr and use
   BN254 base-field, G1/G2, complete MSM and pairing gadgets. Preserve the
   BLAKE3 transcript and two public 128-bit claim-digest limbs. Implement ix's
   canonical 32-byte G1 encoding, including byte order, sign and infinity;
   gnark's native serialization must not be assumed interchangeable. Pack each
   deferred point as two 16-byte halves instead of two 24-byte halves. Check
   untrusted points on curve and use BN254's cofactor-one G1 property without
   retaining BLS subgroup-check multiplications. Validate G2 transport and
   trusted anchors independently.
3. **Preserve both pairing obligations and setup policy.** Constrain the
   recursive proof's opening pairing and its deferred first-stage pairing.
   The baseline Go verifying key assumed identical Filecoin anchors; the BN254
   development stages use different seeds, so each equation must use its own
   pinned keys. Keep the equations separate initially. Add explicit
   development opt-in to export/prove/verify and propagate setup class through
   artifacts; production acceptance must continue to reject known-trapdoor
   proofs. Parameterize the outer PLONK setup binding rather than assuming
   its anchors must equal an inner proof's anchors.
4. **Port the PLONK backend and parameter interchange.** Select BN254 for
   constraint-system, witness, key and proof construction. Version the SRS
   transport, cache identities, manifests and verifying key catalogs so BLS
   and BN254 artifacts cannot be mixed. For domain `N`, prepare `N+3` monomial
   powers and `N` Lagrange points, checking the authenticated setup's declared
   degree before allocation. Keep deterministic key/Lagrange preparation
   separately measurable from proving and preserve the existing memory
   release ordering around large conversions.
5. **Establish correctness and size before full proving.** Differentially
   compare point/scalar bytes, BLAKE3 challenges, scalar relations, MSM
   operands and pairings with Rust. Exercise infinity, opposite points,
   noncanonical encodings, changed claims, wrong verifying keys and invalid
   deferred pairings through circuit constraints, bypassing host
   preverification. Compile the real Init wrapper, measure incremental
   constraints and padded domain, and check whether it fits `2^24` rather
   than extrapolating native frontend rows. Prove and verify a small complete
   BN254 PLONK fixture, then the real Init wrapper under development setup.
6. **Integrate CLI and contract verification.** Select and package the helper
   through Lake and `ix compress --plonk`, preserve the original claim,
   authenticate the verifying key catalog and derive the two public limbs
   from the caller's expected digest. Export the standard BN254 PLONK Solidity
   verifier and test agreement with native verification, including negative
   inputs. Gnark GPU acceleration is a separate workstream from KZG CUDA
   parity and follows a validated CPU proof.

The first reviewable milestone is **existing Init packet export, BN254 gnark
compilation, valid/invalid witness checks and a phase-by-phase constraint
report**. It reuses the completed CPU KZG run and can proceed alongside CUDA
work. Production requires an authenticated BN254 ceremony import, reviewed
verifying keys and fresh inner KZG proofs under production parameters;
wrapping a development proof does not upgrade its setup security.

### BN254 trusted setup research (2026-10-16)

**Investigate Aztec Ignition first for the current sizes; retain Perpetual
Powers of Tau as a larger-capacity alternative.** Both provide a reusable
BN254 phase-one basis. PLONK needs deterministic circuit-key preparation,
not a circuit-specific contribution ceremony; Groth16's phase two is a
different requirement. See the [snarkjs setup distinction](https://github.com/iden3/snarkjs/blob/22003fbcde78608be902520661832db7933d279e/README.md#15-setup).
This research selects candidates, not an authorized production setup.

#### What SP1 actually uses

At SP1 revision `02fa30185ecd658174b211d56128b14867ab8e81`, the non-development
PLONK build calls `DownloadAndSaveAztecIgnitionSrs(174)`, derives Lagrange
points and invokes gnark PLONK setup. Its converter selects `MAIN IGNITION`;
the observed manifest has 176 valid participants, so index 174 selects its
last two contributions, positions 196 and 197. This establishes the source
path, not a fresh audit of SP1's prebuilt release bundles.
[Build](https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/sp1/build.go#L108-L171),
[converter](https://github.com/succinctlabs/sp1/blob/02fa30185ecd658174b211d56128b14867ab8e81/crates/recursion/gnark-ffi/go/sp1/trusted_setup/trusted_setup.go#L69-L131).

Succinct's separate Groth16 ceremony tooling defaults to
`powersOfTau28_hez_final_24.ptau` from Perpetual Powers of Tau, then initializes
circuit-specific phase two. That is not its PLONK setup path.
[Groth16 initialization](https://github.com/succinctlabs/semaphore-gnark-11/blob/6d6ebc3608e609ec879e9ba99abee6b6b97d937d/scripts/initialize_trusted_setup.py#L35-L45),
[phase-one download](https://github.com/succinctlabs/semaphore-gnark-11/blob/6d6ebc3608e609ec879e9ba99abee6b6b97d937d/scripts/trusted_setup.py#L59-L80).

#### Capacity and artifact choices

The [Ignition manifest](https://aztec-ignition.s3.amazonaws.com/MAIN%20IGNITION/manifest.json)
reports 100,800,000 G1 points in twenty transcripts of 5,040,000 points.
The [format specification](https://github.com/AztecProtocol/ignition-verification/blob/c333ec4775045139f86732abfbbd65728404ab7f/Transcript_spec.md)
describes powers starting at `tau * G1`. SP1 preserves that shifted basis and
sets the verifying key's G1 base to its first entry. It does not prepend the
canonical generator. The generic ix SRS/PCS paths use their supplied G1
base, but a shifted-basis interoperability test is still required.

| ix target | Required G1 entries | Fits Ignition's recorded capacity? |
| --- | ---: | --- |
| First KZG, trace `2^24` | 16,777,216 | Yes |
| Recursive KZG, trace `2^26` | 67,108,864 | Yes |
| gnark PLONK, domain `2^24` | 16,777,219 | Yes |
| gnark PLONK, domain `2^25` | 33,554,435 | Yes |
| gnark PLONK, domain `2^26` | 67,108,867 | Yes |
| Native trace or gnark domain `2^27` | At least 134,217,728 | No |

These counts follow ix's `srs(height)` use and gnark's `N+3` monomial / `N`
Lagrange requirements. The quotient factor two expands the evaluation domain;
it does not double ix's required SRS prefix. Halving the recursive trace
therefore makes Ignition large enough for the measured pipeline.
[ix setup](../crates/proof-compression/src/pipeline/setup.rs),
[gnark parameter export](../crates/proof-compression/src/pipeline/plonk.rs).

The linked [Perpetual Powers of Tau repository](https://github.com/privacy-ethereum/perpetualpowersoftau/tree/b077232729db7c9eb65b63c4aaaa0ac4a1b0bba2)
documents BN254 parameters through power 28 and prepared files from
contribution 0080 plus its beacon. It is archived, but its artifact endpoints
remain reachable. The older `powersOfTau28_hez_final_*` family derives from
54 contributions plus a beacon and has published BLAKE2b-512 digests in
[snarkjs](https://github.com/iden3/snarkjs/blob/22003fbcde78608be902520661832db7933d279e/README.md#7-prepare-phase-2).
These are different finalized snapshots; their anchors and hashes must not
be mixed.

For the current native `2^26` trace, a power-26 `.ptau` is sufficient.
Its monomial G1 section contains `2^27 - 1` points, not merely `2^26`.
A power-25 file has `2^26 - 1` entries and is one entry short of the native
trace's requirement. Check section counts rather than inferring capacity
from a filename. KZG uses the tau powers and G2 anchors; the additional
Groth16 alpha/beta and prepared sections need not be retained in our cache.
[Accumulator layout](https://github.com/iden3/snarkjs/blob/22003fbcde78608be902520661832db7933d279e/src/powersoftau_new.js),
[truncation layout](https://github.com/iden3/snarkjs/blob/22003fbcde78608be902520661832db7933d279e/src/powersoftau_truncate.js).

HEAD requests reported 77,309,494,424 bytes for
[`powersOfTau28_hez_final_26.ptau`](https://circom.info/powersOfTau28_hez_final_26.ptau)
and 77,309,504,658 bytes for
[`ppot_0080_26.ptau`](https://pse-trusted-setup-ppot.s3.eu-central-1.amazonaws.com/pot28_0080/ppot_0080_26.ptau),
about 72 GiB each. A retained `2^26` G1 prefix requires about 4 GiB for
uncompressed 64-byte coordinates, plus metadata; it does not require keeping
all prepared sections. The published candidate digest for the older file is:

```text
powersOfTau28_hez_final_26.ptau — BLAKE2b-512
418dee4a74b9592198bd8fd02ad1aea76f9cf3085f206dfd7d594c9e264ae919611b1459a1cc920c2f143417744ba9edd7b8d51e44be9452344a225ff7eead19
```

This digest is copied from the pinned snarkjs source above, not verified
against a downloaded file. The 0080 README/index inspected here did not
provide an equivalent file digest. HTTP metadata and multipart ETags are not
substitutes for a trusted cryptographic receipt.

#### Import and authentication work

The [Ignition importer](../crates/proof-compression/src/kzg/srs/ignition.rs)
and its [CLI](../crates/proof-compression/examples/kzg_ignition_import.rs)
implement caller-pinned source inventories, bounded transcript validation,
shifted-basis checks and authenticated prefix caches. A portable admission
descriptor binds the exact source inventory, full degree and verifier
anchors under a separate trusted digest. The pipeline can select these
parameters with explicit admission and cache pins; local verification needs
only the admission, expected claim and independently trusted verifying key.
The verifying key catalog can bind a production key to an admitted setup.
Its BN254 catalog remains empty and production-only: producing files
does not authorize a release key. Source inspection remains an untrusted
inventory, and no ceremony pin is admitted automatically. Import/admission
and pipeline validation now pass: 249 BN254 and 238 BLS12-381 CPU tests
(five ignored on each), thirty CUDA checks per curve, and Clippy on both
curves. Complete cold and warm Init proofs under Ignition and independent
CPU verification also pass.
[Usage and limits](../crates/proof-compression/README.md#ignition-parameter-import),
[pipeline selection](../crates/proof-compression/README.md#admitted-ignition-pipeline).

The [gnark Ignition verifier](https://github.com/Consensys-Incorporated/gnark-ignition-verifier/tree/ca240270d7f48d4c9ce0970b20938bce8a8a6c00)
provides useful parsing and algebraic checks. SP1 pins the older revision
`10693546ab33`; its [contribution checker](https://github.com/Consensys/gnark-ignition-verifier/blob/10693546ab33/ignition/contribution.go)
checks embedded checksums, subgroup membership and power relations, but
explicitly omits participant-signature verification. The converter also
loads an unpinned remote manifest. These checks alone do not authenticate a
particular ceremony endpoint, and checking the final two contributions is
not verification of the entire participant chain.

The initial research fetched source files, the small Ignition manifest and
HTTP headers. Subsequent provisioning downloaded all forty transcript files
from contributions 196 and 197. All forty participant signatures verified
using EIP-191 over each complete file's SHA256; both participants' first G1
and contribution G2 anchors matched the historical records in
[Aztec's verification repository at `c333ec47`](https://github.com/AztecProtocol/ignition-verification/tree/c333ec4775045139f86732abfbbd65728404ab7f).
The source inventory's BLAKE2b-512 hashes were matched to that evidence before
import. This authenticates the selected participant snapshot, without
replaying the entire ceremony or proving secret erasure. The distinct
`sealed` snapshot is not part of this import.

The retained `2^26` prefix passed bounded import and progression checks in
211.88 seconds with 0.134 GiB peak RSS. Full cache authentication/loading took
5.54 seconds with 4.532 GiB peak RSS; loading two verifier anchors took
4.31 milliseconds. The cache, source transcripts, admission, signature
evidence and receipts are stored at
`s3://argument-kzg-params-063002298335-us-east-1-an/bn254/ignition/main-197/`;
all 116 objects passed size and SHA-256 verification after upload. The local
copy and host-specific `setup.env` remain under
`/opt/dlami/nvme/ix-bn254/parameters/ignition/`. See the
[restore commands and pinned digests](../crates/proof-compression/README.md#ignition-parameter-import)
for another host. Public degree remains
100,799,999 for every loaded prefix, with the shifted `tau * G1` basis
preserved. No Perpetual Powers of Tau artifact or SP1 release bundle has been
downloaded or authenticated in this work.

The real Init GPU pipeline completed in **284.30 seconds** with cold fixed
preprocessing and **181.13 seconds** with it reused. First KZG took
210.89/135.94 seconds and recursion took 72.69/44.56 seconds, cold/warm.
Both stages retain the admitted setup identity and full public degree.
Recursion has 61,151,377 frontend rows and still pads to `2^26`; the first
stage retains nineteen circuits. Both 1,917-byte envelopes passed independent
CPU verification and seven negative checks per run. The envelopes, 1,542-byte
verifying keys and both stages' compact proofs are byte-identical across runs.
The verifying key uses the shared BLS `VerifyingKey` structure with BN254
version 7 and an explicit local verifying key digest; it is not a bundled
verifying key catalog entry. These single runs have uncontrolled OS page
cache and do not isolate a ceremony-related speedup over development
parameters. Artifacts and checks are recorded in
`/opt/dlami/nvme/ix-bn254/ignition-validation/experiment.json`.
[Measurements and artifact locations](../crates/proof-compression/README.md#real-init-with-ignition).

Remaining production work:

1. Implement and validate the Rust/gnark conversion against small
   authenticated prefixes: commitments, openings, shifted anchors and
   Lagrange conversion. Measure full key preparation with explicit resource
   approval, then prove the terminal PLONK wrapper under the admitted setup.
2. Review and authorize the resulting verifying keys and catalog entries
   separately from generating them. Perpetual Powers of Tau remains
   a separate fallback requiring its own authenticated artifact pins, parser
   and conversion validation.

## BN254 GPU integration plan

This section is the implementation plan for the optional BN254 backend. The
architecture proposals and benchmark figures above are historical context;
they do not establish BN254 performance or the current wrapper circuit size.
In particular, a smaller field does not establish an MSM speedup, a smaller
recursive domain, or unchanged FFT/lookup/quotient timings. Those are
measurements required below. CPU pipeline wiring is a prerequisite for these
steps, and does not by itself make a real Init compression run practical.

The real Init CPU measurement now establishes 61,151,005 BN254 recursive
frontend rows, padding to `2^26`, against 118,389,942 rows and `2^27` in the
historical BLS reference. The recursive witness and external pairings pass;
the complete Init development pipeline and independent envelope verification
also pass. A matched one-GPU development run now completes both KZG stages
in 276.00 seconds for BN254 versus 378.19 seconds for BLS, with cold fixed
preprocessing and prepared SRS caches. BN254 matches the CPU proof bytes at
both stages. See the
[GPU measurement](../crates/proof-compression/README.md#matched-init-gpu-comparison)
and [CPU details](../crates/proof-compression/README.md#real-input-measurements).
This measures complete curve-specific pipelines; it does not isolate an MSM
speedup or establish the benefit of splitting across GPUs.

### Scope and source baseline

The first deliverable is GPU support for the existing KZG pipeline: saved Init
proof, Goldilocks FRI compression, first BN254 KZG proof, recursive BN254 KZG
proof, and native verification. BLS12-381 remains the default and the
comparison baseline. Each executable selects one KZG curve; comparison runs
use separate binaries, build directories, setup caches, and artifact
directories. The Goldilocks FRI backend remains present in either GPU build.

At the CPU baseline `52c61479`, the reusable bridge contained BLS-specific
assumptions in several places:

- [`Cargo.toml`](../crates/proof-compression/Cargo.toml) made `cuda` select
  BLS12-381. [`build.rs`](../crates/proof-compression/build.rs) selected
  `FEATURE_BLS12_381` and `MAX_LG_DOMAIN_SIZE=32`.
- [`cuda/kzg.cu`](../crates/proof-compression/cuda/kzg.cu) included
  `ff/bls12-381.hpp` and defined the affine upload layout.
  [`src/kzg/cuda.rs`](../crates/proof-compression/src/kzg/cuda.rs) imported
  BLS types, checked their layout, and returned six-limb projective coordinates.
- [`src/kzg/cuda/srs_cache.rs`](../crates/proof-compression/src/kzg/cuda/srs_cache.rs)
  had both six-limb output pointers and fixed 96/104-byte point accounting.
  [`cuda/kzg_srs.cuh`](../crates/proof-compression/cuda/kzg_srs.cuh) provides
  native MSM scratch estimates, resident points, and batched uploads.
- [`lakefile.lean`](../lakefile.lean) builds and installs the worker with its
  feature selection and shared Goldilocks runtime.
  [`flake.nix`](../flake.nix) provides the opt-in CUDA toolkit shell and
  runtime-driver plumbing. Both must preserve CPU-only builds.

Use the existing sppark pin from the crate manifest,
`114feb69ebfe029e2caa5e6c2d372c695e5d4da8`, shared with multi-stark. Its
[`ff/alt_bn128.hpp`](https://github.com/argumentcomputer/sppark/blob/114feb69ebfe029e2caa5e6c2d372c695e5d4da8/ff/alt_bn128.hpp)
already supplies BN254 Fq/Fr and `FEATURE_BN254`. Its
[`ntt/parameters.cuh`](https://github.com/argumentcomputer/sppark/blob/114feb69ebfe029e2caa5e6c2d372c695e5d4da8/ntt/parameters.cuh)
selects the BN254 table with `S = 28` in
[`ntt/parameters/alt_bn128.h`](https://github.com/argumentcomputer/sppark/blob/114feb69ebfe029e2caa5e6c2d372c695e5d4da8/ntt/parameters/alt_bn128.h).
No dependency update is needed to begin the port. The BN254 host field types
use `blst_256_t` through `blst_t.hpp`; retain the `blst` dependency, include
path, and portable host linkage while those types require them.

### Targeted implementation steps

**1. Select the CUDA curve and make its ABI explicit.** Change the feature
graph, build flags, C++ field include, Rust curve imports, and native point
layouts together in one focused PR. Preserve the symbol isolation from
Goldilocks in [`kzg_sppark.cuh`](../crates/proof-compression/cuda/kzg_sppark.cuh).
Use curve-dependent limb aliases for all projective result pointers,
including cached and resident MSM paths; derive allocation sizes from the
actual selected types. Prove the following contracts with Rust layout
assertions and C++ `static_assert`s on the supported Linux x86-64 target:

| Value crossing the bridge | BLS12-381 | BN254 |
| --- | ---: | ---: |
| Fr limb storage | 32 bytes, four `u64` limbs | 32 bytes, four `u64` limbs |
| Fq limb storage | 48 bytes, six `u64` limbs | 32 bytes, four `u64` limbs |
| Arkworks affine upload, including infinity and padding | 104 bytes | 72 bytes |
| Affine `y` / infinity offsets | 48 / 96 bytes | 32 / 64 bytes |
| Device affine coordinates | 96 bytes | 64 bytes |
| Native projective result, three Fq coordinates | 144 bytes | 96 bytes |

These are memory layouts, not serialized proof encodings. Verify both Fq and
Fr Montgomery modulus, radix, limb order and representation of one; equal
storage width alone does not permit copying values between curves. Preserve
the conversion from Arkworks' infinity flag to sppark affine `(0, 0)` and
projective `Z = 0`.

The target build matrix is below. All rows start with
`--no-default-features`; retain a separate check of the existing default
build, which includes the BLS terminal backends.

| Feature selection | Intended backend |
| --- | --- |
| `bls12-381,parallel` | BLS CPU worker and library |
| `bn254,parallel` | BN254 CPU worker and library |
| `bls12-381,parallel,cuda` | BLS KZG CUDA plus Goldilocks CUDA |
| `bn254,parallel,cuda` | BN254 KZG CUDA plus Goldilocks CUDA |

Both CUDA library test targets compile, and all 30 CUDA-module checks pass
on each curve: 12 host/ABI checks and 18 GPU checks. Coverage includes field
arithmetic, NTT roots, FFTs, MSM/cache paths, polynomial operations, dense and
forced-pass constraints, concurrency and two-device resident admission.
Separate CPU and CUDA binaries also produce identical proof and verifier
bytes for a two-circuit development fixture at 4,096/8,192 rows on both
curves, covering dense, forced-pass and cached-SRS modes. Cross-verification
and changed-claim/evaluation/pin/curve rejection pass. This fixture excludes
FRI compression and recursive KZG proving. Separate full saved Init GPU runs
complete both KZG stages on each curve; BN254's proofs match its CPU run
exactly and pass the original CPU worker's verifier. BLS's full-size CPU/GPU
byte comparison remains pending. The Lake configuration typechecks and its
seven curve/feature argument cases pass; complete CLI linking remains pending.
Lake's `IX_KZG_CURVE` selects the curve
for both the `ix` library and the existing worker target, with BLS terminal
features omitted for BN254.
The source also parameterizes native layouts, MSM result buffers, SRS-cache
point accounting and FFT domain limits, and adds a host field-representation
check. See the
[implementation status](../crates/proof-compression/README.md#curve-selection-and-validation-status).

Reject simultaneous BLS and BN selection. Keep BLS-only Solidity/PLONK
features from silently selecting the wrong curve. Thread the worker's curve
selection through Lake's build arguments and artifact trace, preserve the
native runtime/rpath packaging, and keep CPU builds independent of nvcc.
Acceptance: the feature matrix compiles with the intended field instantiation
and ABI assertions; rebuilding one curve cannot reuse the other's worker or
parameters. Do not enable BN254 GPU proving by default before the following
parity gates pass.

**2. Establish field, FFT, and polynomial parity.** Parameterize the Rust and
native FFT bounds: BN254 permits `log(domain) <= 28`; retain existing BLS
implementation limits unless separately justified. The BLS native bridge
retains `lg <= 31`; the BN254 bridge now checks `lg <= 28` on both sides of
the FFI. Changing only the NTT macro is insufficient.
Reject unsupported trace-plus-quotient domains before allocation. In
particular, quotient factor two at trace `2^27` consumes the complete BN254
domain limit; this does not imply that the device can admit it.

Extend [`cuda/tests.rs`](../crates/proof-compression/src/kzg/cuda/tests.rs)
with small deterministic CPU/GPU comparisons for scalar arithmetic,
subgroup and arbitrary-coset forward/inverse FFTs, zero-padding, batched
column order, resident inputs, evaluation, division by `X-z`, and quotient
openings. Check the actual root-of-unity convention against Arkworks and
`Scalar`; a round trip alone can conceal a consistent ordering error. Include
maximum-domain rejection tests that do not allocate maximum-sized arrays.
Acceptance: exact field-element equality with the CPU reference, preserved
input/output order, and explicit errors for unsupported domains.

**3. Establish MSM and SRS-cache parity.** Compare normalized affine results
against Arkworks for ordinary, chunked, resident-scalar, cached-SRS and
division-plus-MSM paths. Cover zero scalars, infinity, opposite points,
repeated points, non-multiple chunk tails, and structured columns that trigger
the normalization optimization. Keep fresh mutable MSM workspace distinct
from immutable uploaded SRS ranges. Verify eviction, re-upload, SRS-owner
isolation, offsets, and cleanup after native failures.

Audit every persistent, temporary, staging, bucket and point-memory estimate,
including the fixed sizes in `srs_cache.rs` and native estimates from
`ix_kzg_srs_plan`. Smaller points do not shrink scalar columns, FFT buffers or
all MSM scratch in the same proportion. Acceptance: exact commitment parity,
no stale range reuse, and admission accounting consistent with actual native
allocations for the measured small shapes.

**4. Port lookup, quotient, and constraint-pass execution.** Review the paired
Rust and CUDA implementations together:
[`lookup.rs`](../crates/proof-compression/src/kzg/cuda/lookup.rs) /
[`kzg_lookup.cuh`](../crates/proof-compression/cuda/kzg_lookup.cuh),
[`quotient.rs`](../crates/proof-compression/src/kzg/cuda/quotient.rs) /
[`kzg_quotient.cuh`](../crates/proof-compression/cuda/kzg_quotient.cuh), and
[`passes.rs`](../crates/proof-compression/src/kzg/cuda/passes.rs) /
[`kzg_passes.cuh`](../crates/proof-compression/cuda/kzg_passes.cuh).
Their 32-byte Fr descriptors can retain their ABI, subject to assertions, but
their arithmetic and domain constants must use BN254. Compare LogUp totals,
lookup columns and quotient chunks against CPU output, including next-row
access, cosets, resident inputs, streaming mode, and forced constraint passes.
Check device-lease admission, rejection, stream completion and buffer lifetime
on both success and failure.

Include pinned host staging, device-pool reservations, resident coefficient
limits, and SRS/workspace eviction in the memory audit. Preserve the transfer
timing and NVTX hooks in
[`kzg_transfer.cuh`](../crates/proof-compression/cuda/kzg_transfer.cuh) and
[`kzg_profile.cuh`](../crates/proof-compression/cuda/kzg_profile.cuh).
Acceptance: CPU/GPU parity in both dense and pass execution, bounded transfer
buffers, and useful errors when no selected GPU admits the work. GPU runs
must report any intentional CPU path, such as tiny shapes or disk-backed
columns, so a successful smoke test cannot conceal an unused backend.

**5. Validate the complete development pipeline on a small saved Init
fixture.** Use one saved proof, trusted root key and expected public claim,
with fixed stage parameters and explicit `--dev-srs`. Build CPU and CUDA
workers separately for each curve. Preserve curve-specific artifact
directories and verifying keys. Compare canonical proof bytes between CPU and GPU
for the same curve, setup and transcript at the FRI, first-KZG and recursive
KZG boundaries, and verify every output with the native verifier. BLS and
BN254 proofs are not expected to have identical bytes to each other.

The fixture must exercise GPU operations: record dispatch, and where the
smallest valid proof falls below an acceleration threshold, add a targeted
component parity case above that threshold. Include saved-stage replay,
portable verifying key loading, altered-claim and deferred-pairing rejection, and
cross-curve artifact rejection. Acceptance: exact CPU/GPU proof parity and
native verification for both curves, with logs proving that the intended GPU
paths ran. This gate validates integration, not production setup security or
production-scale resource use.

**6. Profile increasing sizes, then the real Init proof.** Start with selected
small kernel dimensions and the small pipeline fixture; use their measured
working sets to choose the next size. Size the real Init verifier circuits
before allocating proving traces or parameters. Report total rows, maximum
trace and quotient domains, columns, lookup/table shape, partition count, and
recursive public-input/commitment counts for both curves on the same source
proof. Advance to one real Init run on one GPU only when host and device
memory estimates fit, then measure any multi-GPU configuration separately.

Do not introduce recursive sharding merely because two GPUs are available.
After sizing, compare one trace with candidate partition caps, including
extra commitments, lookups, aggregation/recursive-verifier work, proof bytes,
SRS replication, transfer traffic and total GPU-seconds. Existing scheduling
of columns or MSM chunks across devices is distinct from adding independently
proved recursive shards. Choose sharding only when the measured aggregate
cost and memory requirements justify it; revise the circuit/verifying key boundary
in a separate PR.

### Reports and run permissions

Each step should attach its scoped source changes and a validation report;
unexecuted checks remain marked pending. Parity reports identify the fixture
digest, root/verifying key/setup identities, exact feature set, source revisions,
commands, proof hashes, verification results and CPU/GPU dispatch. Performance
reports additionally record GPU model/count, driver/toolkit and compiled SM
architectures, cold versus warm cache state, per-stage wall time, CPU witness
time, kernel/transfer time, peak host RSS and VRAM, pinned/resident/SRS-cache
bytes, pass count, cache hits/evictions, and final proof sizes. Report
profiling overhead separately where relevant. Compare the same source proof
and explicitly identify any different circuit shape or partition policy.

No builds, tests, circuit sizing or benchmark runs are authorized by this
plan. Before a cold build, full proof, large sizing run or benchmark sweep,
request machine time with the exact target and dimensions plus a resource
estimate grounded in the preceding measurements. Do not guess full-run times
from the historical BLS figures. Once authorized, use default machine
parallelism; do not impose `--jobs`, test-thread or Rayon caps. Device choices
for a one-GPU versus multi-GPU comparison are experimental inputs and must be
recorded.

### Separate production and terminal-wrapper gates

GPU correctness is only one production requirement. BN254 still needs an
authenticated production SRS with validated anchors, adequate public degree,
an authenticated import/receipt, curve-separated cache identities, and
reproducible verifying keys. Select and audit its provenance separately;
Filecoin parameters cannot supply this gate. Development SRS results remain
known-trapdoor experiments even after every GPU check passes.

The final off-the-shelf gnark BN254 PLONK wrapper is a separate workstream.
Port and validate its custom ix verifier circuit and pairing obligations,
then establish CPU correctness and measure its own constraints, witness,
setup/proving memory and time. The CUDA kernels in this crate accelerate the
custom KZG prover; they do not accelerate gnark PLONK. Any GPU integration
for gnark requires its own backend selection, compatibility/serialization
checks, CPU/GPU proof and native/Solidity verification gates, and resource
report. End-to-end production claims must include that terminal stage and
the authenticated-setup gate, not only KZG kernel timings.
