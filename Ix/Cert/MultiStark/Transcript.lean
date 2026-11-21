import Ix.Cert.MultiStark.Types
import CertiFriP3.Challenger
import CertiFri.Verifier

/-! # Multi-STARK Fiat–Shamir Transcript (`Ix.Cert.MultiStark.Transcript`)

Exact replay of `multi-stark`'s batch and per-shard Fiat–Shamir transcript
(`multi-stark/src/{types.rs,system.rs,prover.rs,batch.rs,verifier.rs}`) over
`CertiFri.P3.challenger`, reusing `CertiFri.Fri.{commitPhase, finalMessage}`
and failing closed if rejection sampling ever exhausts `rejectionFuel`.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Observe a `Nat` as a Goldilocks base field element (8 LE bytes). -/
def observeNat (s : ChallengerState) (n : Nat) : ChallengerState :=
  s.observe (.base (Goldilocks.ofNat n))

/-- Observe a single-root Merkle cap (`cap_height = 0`). -/
def observeCap? (s : ChallengerState) (cap : Array D) : Option ChallengerState :=
  if h : cap.size = 1 then
    some (s.observe (.digest cap[0]))
  else
    none

/-- Fail-closed rejection sampling of a base field element (never substitutes `0`
on fuel exhaustion). -/
def sampleBaseStrict (fuel : Nat) (s : ChallengerState) : Option (F × ChallengerState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let (w, s') := ChallengerState.sampleWord blake3 s
    match Goldilocks.ofCanonical? w with
    | some a => some (a, s')
    | none => sampleBaseStrict fuel s'

/-- Fail-closed extension-field challenge sampling (`c0` then `c1`). -/
def sampleExtStrict (s : ChallengerState) : Option (EF × ChallengerState) := do
  let (c0, s1) ← sampleBaseStrict ChallengerState.rejectionFuel s
  let (c1, s2) ← sampleBaseStrict ChallengerState.rejectionFuel s1
  pure (⟨c0, c1⟩, s2)

/-- Domain-separated initial challenger seed (`multi-stark/src/types.rs:339-351`):
`b"multi-stark/v0"` followed by the 7 protocol parameters as u64 LE. -/
def initialChallenger (p : StarkParams) : ChallengerState :=
  let s := ChallengerState.new "multi-stark/v0".toUTF8
  let s := observeNat s p.logBlowup
  let s := observeNat s p.capHeight
  let s := observeNat s p.logFinalPolyLen
  let s := observeNat s p.maxLogArity
  let s := observeNat s p.numQueries
  let s := observeNat s p.commitPowBits
  observeNat s p.queryPowBits

/-- Observe system shape (`multi-stark/src/system.rs:289-302`). -/
def observeShape (s : ChallengerState) (sys : StarkSystem) : ChallengerState :=
  let s := observeNat s sys.circuits.size
  sys.circuits.foldl (init := s) fun acc c =>
    let acc := observeNat acc c.constraintCount
    let acc := observeNat acc c.maxConstraintDegree
    let acc := observeNat acc c.preprocessedHeight
    let acc := observeNat acc c.preprocessedWidth
    let acc := observeNat acc c.mainWidth
    let acc := observeNat acc c.stage2Width
    observeNat acc (max 1 c.lookupGroupSize)

/-- Observe length-prefixed claims (`multi-stark/src/prover.rs:283-289`). -/
def observeClaims (s : ChallengerState) (claims : Array (Array F)) : ChallengerState :=
  let s := observeNat s claims.size
  claims.foldl (init := s) fun acc cl =>
    let acc := observeNat acc cl.size
    cl.foldl (init := acc) fun acc' v => acc'.observe (.base v)

/-- Sample lookup challenges `β, γ` and observe each back into the transcript
(`multi-stark/src/prover.rs:293-301`, `Transcript.lean:75-78`). -/
def sampleLookupChallenges (s : ChallengerState) : Option (EF × EF × ChallengerState) := do
  let (beta, s1) ← sampleExtStrict s
  let s1 := s1.observe (.ext beta)
  let (gamma, s2) ← sampleExtStrict s1
  let s2 := s2.observe (.ext gamma)
  pure (beta, gamma, s2)

/-- Batch preamble transcript up to and including `(β, γ)` (`multi-stark/src/batch.rs:272-302`). -/
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
    let acc := m.args.foldl (init := acc) fun a v => a.observe (.base v)
    acc.observe (.base m.multiplicity)
  let (beta, gamma, s) ← sampleLookupChallenges s
  pure (s, beta, gamma)

/-- Per-shard transcript fork from the shared batch challenger:
observe `shard`, `stage_2_trace`, `intermediate_accumulators`, sample `α_air` (not observed back),
observe `quotient_chunks`, sample `ζ` (not observed back). -/
def shardAirChallenges (batchState : ChallengerState) (shardIdx : Nat) (proof : ShardProof) :
    Option (EF × EF × ChallengerState) := do
  let s := observeNat batchState shardIdx
  let s ← observeCap? s proof.commitments.stage2Trace
  let s := proof.intermediateAccumulators.foldl (init := s) fun acc v => acc.observe (.ext v)
  let (alphaAir, s) ← sampleExtStrict s
  let s ← observeCap? s proof.commitments.quotientChunks
  let (zeta, s) ← sampleExtStrict s
  pure (alphaAir, zeta, s)

/-- Derive FRI `Challenges` from the post-`ζ` Multi-STARK challenger state:
observe ONLY opened values (commitments were already absorbed and opening points
`ζ, ζ·g` are never absorbed in `multi-stark`), then sample `α_fri`, run
`Fri.commitPhase`, absorb `Fri.finalMessage`, check `queryPowWitness`, and
sample `numQueries` domain indices. -/
def shardFriChallenges (postZeta : ChallengerState) (params : FriParams) (shape : Fri.ClaimShape)
    (values : Array EF) (proof : FriProof F EF D (PrunedPaths D) (PrunedPaths D)) :
    Option (Fri.Challenges EF) := do
  let n := Fri.logMaxHeight params.logBlowup shape
  let rounds := Fri.numRounds params shape
  let s := values.foldl (init := postZeta) fun acc v => acc.observe (.ext v)
  let (alphaFri, s) ← sampleExtStrict s
  -- Commit phase: observe round commit, check PoW witness, sample beta_i (fail-closed).
  let mut betas := Array.mkEmpty rounds
  let mut powOk := true
  let mut st := s
  for i in [0:rounds] do
    let some commit := proof.commitPhaseCommits[i]? | none
    let some wit := proof.commitPowWitnesses[i]? | none
    st := st.observe (.digest commit)
    let (ok, st1) := challenger.checkWitness st params.commitPowBits wit
    powOk := powOk && ok
    let (beta, st2) ← sampleExtStrict st1
    betas := betas.push beta
    st := st2
  st := challenger.observeAll st (Fri.finalMessage rounds proof.finalPoly)
  let (qPowOk, stFinal) := challenger.checkWitness st params.queryPowBits proof.queryPowWitness
  let indices := (challenger.sampleIndices n params.numQueries stFinal).toArray
  pure {
    alpha := alphaFri
    betas := betas
    powOk := powOk && qPowOk
    indices := indices
  }

end Ix.Cert.MultiStark
