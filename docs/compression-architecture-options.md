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
[`bls-plonk-wrapper-status.md`](bls-plonk-wrapper-status.md), multi-stark
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
| 6. gnark PLONK wrapper | under 1 KB | BLS12-381, CPU | 23,358,575 constraints, `N = 2^25`; proving not yet measured |

Stage timings are the one-GPU warm runs recorded in multi-stark
`docs/kzg-merge-plan.md`. The partition rule is
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
  every fixture and profile change.
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
  every downstream profile, verifier key and fixture.

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
