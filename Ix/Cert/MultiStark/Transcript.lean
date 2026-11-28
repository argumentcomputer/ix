import Ix.Cert.MultiStark.Types
import Ix.Cert.MultiStark.Wire
import CertiFriP3.DomainSep
import CertiFri.TensorBatching
import CertiFri.Verifier

/-! # Multi-STARK Protocol `v6` Fiat–Shamir Transcript (`Ix.Cert.MultiStark.Transcript`)

Exact replay of `multi-stark` Protocol `v6`'s batch and per-shard Fiat–Shamir transcript
over `Fp^3 = Fp[X]/(X^3 - X - 1)`, native BLAKE3 `derive_key` (`v6TranscriptBatchContext`,
`CertiFri.P3.challenger3V6Batch`), and multilinear tensor FRI batching (`FriBatching::Tensor`,
`CertiFri.Fri.{tensorNumChallenges, tensorWeights}`), failing closed if rejection sampling
ever exhausts `rejectionFuel`.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Observe a `Nat` as a Goldilocks base field element (8 LE bytes). -/
def observeNat (s : ChallengerState) (n : Nat) : ChallengerState :=
  s.observe3 (.base (Goldilocks.ofNat n))

/-- Observe a single-root Merkle cap (`cap_height = 0`). -/
def observeCap? (s : ChallengerState) (cap : Array D) : Option ChallengerState :=
  if h : cap.size = 1 then
    some (s.observe3 (.digest cap[0]))
  else
    none

/-- Fail-closed rejection sampling of a base field element under `v6Batch` BLAKE3 `derive_key`
(never substitutes `0` on fuel exhaustion). -/
def sampleBaseStrict (fuel : Nat) (s : ChallengerState) : Option (F × ChallengerState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let (w, s') := ChallengerState.sampleWord (blake3Transcript .v6Batch) s
    match Goldilocks.ofCanonical? w with
    | some a => some (a, s')
    | none => sampleBaseStrict fuel s'

/-- Fail-closed cubic extension-field challenge sampling (`c0`, `c1`, `c2`). -/
def sampleExtStrict (s : ChallengerState) : Option (EF × ChallengerState) := do
  let (c0, s1) ← sampleBaseStrict ChallengerState.rejectionFuel s
  let (c1, s2) ← sampleBaseStrict ChallengerState.rejectionFuel s1
  let (c2, s3) ← sampleBaseStrict ChallengerState.rejectionFuel s2
  pure (⟨c0, c1, c2⟩, s3)

/-- Sample `count` independent cubic extension-field challenges, threading `ChallengerState`. -/
def sampleExtManyStrict : Nat → ChallengerState → Option (Array EF × ChallengerState)
  | 0, s => some (#[], s)
  | n + 1, s => do
    let (r, s1) ← sampleExtStrict s
    let (rs, s2) ← sampleExtManyStrict n s1
    pure (#[r] ++ rs, s2)

/-- Domain-separated initial Protocol `v6` challenger seed (`SystemDeserialize.lean:338-339`,
`StarkVerifier.lean:87-94`): `b"multi-stark/v6"` followed by `[3, 2, 0, 1]`
(`ext_deg = 3`, `modulus_tag = 2`, `merkle_mode = 0`, `fri_batching = 1`) and the
7 protocol parameters as u64 LE. -/
def initialChallenger (p : StarkParams) : ChallengerState :=
  let s := ChallengerState.new "multi-stark/v6".toUTF8
  let s := observeNat s 3
  let s := observeNat s 2
  let s := observeNat s 0
  let s := observeNat s 1
  let s := observeNat s p.logBlowup
  let s := observeNat s p.capHeight
  let s := observeNat s p.logFinalPolyLen
  let s := observeNat s p.maxLogArity
  let s := observeNat s p.numQueries
  let s := observeNat s p.commitPowBits
  observeNat s p.queryPowBits

/-- Observe Protocol `v6` system shape (`SystemDeserialize.lean:340-343`):
`ext_deg = 3`, `modulus_tag = 2`, the canonical recomputed `vk_digest` of `sys.circuits`
(`computeVkDigest sys.circuits`), `circuits.size`, and 7 limbs per circuit. -/
def observeShape (s : ChallengerState) (sys : StarkSystem) : ChallengerState :=
  let s := observeNat s 3
  let s := observeNat s 2
  let s := s.observe3 (.digest (computeVkDigest sys.circuits))
  let s := observeNat s sys.circuits.size
  sys.circuits.foldl (init := s) fun acc c =>
    let acc := observeNat acc c.constraintCount
    let acc := observeNat acc c.maxConstraintDegree
    let acc := observeNat acc c.preprocessedHeight
    let acc := observeNat acc c.preprocessedWidth
    let acc := observeNat acc c.mainWidth
    let acc := observeNat acc c.stage2Width
    observeNat acc (max 1 c.lookupGroupSize)

/-- Observe length-prefixed claims (`multi-stark/src/prover.rs`). -/
def observeClaims (s : ChallengerState) (claims : Array (Array F)) : ChallengerState :=
  let s := observeNat s claims.size
  claims.foldl (init := s) fun acc cl =>
    let acc := observeNat acc cl.size
    cl.foldl (init := acc) fun acc' v => acc'.observe3 (.base v)

/-- Sample lookup challenges `β, γ ∈ Fp^3` and observe each back into the transcript
(`Transcript.lean:76-79`). -/
def sampleLookupChallenges (s : ChallengerState) : Option (EF × EF × ChallengerState) := do
  let (beta, s1) ← sampleExtStrict s
  let s1 := s1.observe3 (.ext beta)
  let (gamma, s2) ← sampleExtStrict s1
  let s2 := s2.observe3 (.ext gamma)
  pure (beta, gamma, s2)

/-- Batch preamble transcript up to and including `(β, γ)` (`Transcript.lean:68-82`). -/
def batchChallenger (sys : StarkSystem) (preamble : BatchPreamble) :
    Option (ChallengerState × EF × EF) := do
  let s := observeShape (initialChallenger sys.params) sys
  let s ← match sys.preprocessedCommit with
    | none => some s
    | some cap => observeCap? s cap
  let s := observeNat s preamble.headers.size
  let s ← preamble.headers.foldlM (init := s) fun acc h => do
    let acc := h.active.foldl (init := acc) fun a b => observeNat a (if b then 1 else 0)
    let acc ← observeCap? acc h.stage1Trace
    let acc := observeNat acc h.logDegrees.size
    let acc := h.logDegrees.foldl (init := acc) fun a ld => observeNat a ld
    pure (observeClaims acc h.claims)
  let s := observeNat s preamble.messages.size
  let s := preamble.messages.foldl (init := s) fun acc m =>
    let acc := observeNat acc m.args.size
    let acc := m.args.foldl (init := acc) fun a v => a.observe3 (.base v)
    acc.observe3 (.base m.multiplicity)
  let (beta, gamma, s) ← sampleLookupChallenges s
  pure (s, beta, gamma)

/-- Per-shard transcript fork from the shared batch challenger (`Transcript.lean:84-94`):
observe `shard`, `stage_2_trace`, `intermediate_accumulators`, sample `α_air` (not observed back),
observe `quotient_chunks`, sample `ζ` (not observed back). -/
def shardAirChallenges (batchState : ChallengerState) (shardIdx : Nat) (proof : ShardProof) :
    Option (EF × EF × ChallengerState) := do
  let s := observeNat batchState shardIdx
  let s ← observeCap? s proof.commitments.stage2Trace
  let s := proof.intermediateAccumulators.foldl (init := s) fun acc v => acc.observe3 (.ext v)
  let (alphaAir, s) ← sampleExtStrict s
  let s ← observeCap? s proof.commitments.quotientChunks
  let (zeta, s) ← sampleExtStrict s
  pure (alphaAir, zeta, s)

/-- FRI challenges for `FriBatching::Tensor` (`Pcs.lean:821-850`). -/
structure TensorFriChallenges (EF : Type) where
  schedule : Fri.TensorSchedule EF
  betas : Array EF
  powOk : Bool
  indices : Array Nat

/-- Derive `FriBatching::Tensor` FRI challenges from the post-`ζ` Multi-STARK challenger state
(`Pcs.lean:817-850`):
1. Observe opened values (`stage1`, `stage2`, `quotient`, optional `preprocessed`).
2. Compute `maxWidth` (max matrix width in `shape`) and `maxOpenings` (max opening count at
   any single height `logDegree + logBlowup`).
3. Sample `kCol = tensorNumChallenges maxWidth` column challenges and
   `kOpen = tensorNumChallenges maxOpenings` opening challenges sequentially while threading
   the challenger's output buffer (`sampleExtManyStrict`), and expand `colWeights`, `openWeights`.
4. Run FRI commit phase (`observe3 (.digest commit)`, `checkWitness`, `sampleExtStrict`).
5. Observe `Fri.finalMessage rounds proof.finalPoly`, check `queryPowWitness`, and sample
   `numQueries` domain indices. -/
def shardFriChallenges (postZeta : ChallengerState) (params : FriParams) (shape : Fri.ClaimShape)
    (values : Array EF) (proof : FriProof F EF D (PrunedPaths D) (PrunedPaths D)) :
    Option (TensorFriChallenges EF) := do
  let n := Fri.logMaxHeight params.logBlowup shape
  let rounds := Fri.numRounds params shape
  let s0 : ChallengerState := { postZeta with output := [] }
  let s := values.foldl (init := s0) fun acc v => acc.observe3 (.ext v)
  let maxWidth := shape.flatten.foldl (fun acc m => max acc m.width) 0
  let pRefs := Fri.pointRefs params.logBlowup shape
  let maxOpenings :=
    (pRefs.map (·.logHeight)).eraseDups.foldl
      (fun acc h => max acc (pRefs.countP (fun p => p.logHeight == h))) 0
  let kCol := Fri.tensorNumChallenges maxWidth
  let kOpen := Fri.tensorNumChallenges maxOpenings
  let (colChals, s1) ← sampleExtManyStrict kCol s
  let (openChals, s2) ← sampleExtManyStrict kOpen s1
  let schedule : Fri.TensorSchedule EF := {
    colChallenges := colChals
    openChallenges := openChals
    colWeights := Fri.tensorWeights colChals maxWidth
    openWeights := Fri.tensorWeights openChals maxOpenings
  }
  -- Commit phase: observe round commit, check PoW witness, sample beta_i (fail-closed).
  let mut betas := Array.mkEmpty rounds
  let mut powOk := true
  let mut st := s2
  for i in [0:rounds] do
    let some commit := proof.commitPhaseCommits[i]? | none
    let some wit := proof.commitPowWitnesses[i]? | none
    st := st.observe3 (.digest commit)
    let (ok, st1) := challenger3V6Batch.checkWitness st params.commitPowBits wit
    powOk := powOk && ok
    let (beta, st2) ← sampleExtStrict st1
    betas := betas.push beta
    st := st2
  st := challenger3V6Batch.observeAll st (Fri.finalMessage rounds proof.finalPoly)
  let (qPowOk, stFinal) := challenger3V6Batch.checkWitness st params.queryPowBits proof.queryPowWitness
  let indices := (challenger3V6Batch.sampleIndices n params.numQueries stFinal).toArray
  pure {
    schedule := schedule
    betas := betas
    powOk := powOk && qPowOk
    indices := indices
  }

end Ix.Cert.MultiStark
