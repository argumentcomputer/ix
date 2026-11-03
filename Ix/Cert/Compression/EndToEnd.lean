import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.FriVerifier
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.NativeCurveMsm
import Ix.Cert.Compression.RecursiveKzg
import Ix.Cert.Compression.OuterRelation
import Ix.Cert.IxVM.CircuitCorrespondence

/-! # End-to-End Proof Compression Soundness & Kernel/Compiler Correspondence (`EndToEnd.lean`)

This module composes all five stages of the certified proof-compression pipeline
(`Ix.Cert.Compression.{Plonkish,Foreign,FriVerifier,NativeField,NativeCurveMsm,RecursiveKzg,OuterRelation}`)
with the Formal `Aiur` `MultiStark::ix_aggr` root wrapper and `Ix.Cert.IxVM.CircuitCorrespondence`:

1. **Stage 4 $\to$ Stage 3 $\to$ Stage 2 $\to$ Stage 1 $\to$ Stage 0 Compression Soundness**:
   - `compressed_kzg_accepts_imp_normalized_root`:
     Composes `recursive_kzg_circuit_sound` (Stage 3 Recursive KZG in `BN254::Fr` + deferred
     $G_1$ pairings), `first_kzg_circuit_sound` (`foreign_compile_sound_lifted` +
     `fri_verifier_circuit_sound`), and `constrainMemoryEnd_sound` (Stage 0 `FixedRoot`
     memory-segment range and `MEMSEG` boundary message soundness) to prove that any accepted
     2,301-byte BN254 Recursive KZG proof implies `NormalizedStarkAccepts vk layout claim rootProof`.
   - `compressed_plonk_accepts_imp_normalized_root`:
     Composes `outer_to_stage2_kzg_sound` (for terminal wrapper kind `.bn254Plonk`) with
     `compressed_kzg_accepts_imp_normalized_root` to prove that any accepted BN254 PLONK
     terminal wrapper proof implies `NormalizedStarkAccepts vk layout claim rootProof`.
   - `compressed_groth16_accepts_imp_normalized_root`:
     Composes `outer_to_stage2_kzg_sound` (for terminal wrapper kind `.bn254Groth16`) with
     `compressed_kzg_accepts_imp_normalized_root` to prove that any accepted BN254 Groth16
     terminal wrapper proof implies `NormalizedStarkAccepts vk layout claim rootProof`.
2. **End-to-End Correspondence with `IxC`, Set-Theoretic ZFC Models, Consistency, and Compiler Commutation**:
   - `compressed_proof_accepts_iff_ixonAcceptsRef`:
     Equivalence between `CompressedProofAcceptsClaim binding limits ixe S order envA` and
     `Ix.Cert.IxonAcceptsRef binding limits ixe S order envA`.
   - `compressed_proof_strongModel`:
     Existence of a ZFC set-theoretic `StrongModel V envA` for any environment accepted by a
     compressed proof.
   - `compressed_proof_valueModel`:
     Existence of a ZFC set-theoretic `Ix.Cert.ValueModel V envA` for any environment accepted
     by a compressed proof.
   - `compressed_proof_no_proof_of_False`:
     Logical consistency (`∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False`)
     for any environment accepted by a compressed proof.
   - `compressed_proof_compile_commutes`:
     End-to-end quotient Source compiler + compressed proof commutation (`LawModel` and
     `ValueModel` pullback along `readingAt ixe t cx` back to the source Lean environment `envQ`).
   - `compressed_proof_compile_commutes_nominal`:
     End-to-end nominal Source compiler + compressed proof commutation (`NominalSemanticBridgeAt`
     pulling back any `StrongModel V envA` to a nominal `LawModel V envS` and `ValueModel V envS`).
-/

namespace Ix.Cert.Compression

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.FriVerifier
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.NativeCurveMsm
open Ix.Cert.Compression.RecursiveKzg
open Ix.Cert.Compression.OuterRelation
open Ix.Kernel
open Ix.Kernel.Cached
open Ix.Kernel.Admission

universe w

/-! ## 1. Stage 4 / Stage 3 $\to$ Stage 0 Normalized Root STARK Soundness -/

/-- Natural-number projection of a Goldilocks claim vector `claim : List GoldilocksF`. -/
def claimNatWords (claim : List GoldilocksF) : List Nat :=
  claim.map ZMod.val

/-- Length of `claimNatWords claim` equals `claim.length`. -/
@[simp] theorem length_claimNatWords (claim : List GoldilocksF) :
    (claimNatWords claim).length = claim.length := by
  simp [claimNatWords]

/-- Every word in `claimNatWords claim` is strictly bounded by `goldilocksP < 2^64`. -/
theorem claimNatWords_lt_two_pow_64 (claim : List GoldilocksF) :
    ∀ w ∈ claimNatWords claim, w < 2 ^ 64 := by
  intro w hw
  unfold claimNatWords at hw
  rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
  have hx : ZMod.val x < goldilocksP := ZMod.val_lt x
  unfold goldilocksP at hx
  omega

/-- **Stage-3 Recursive KZG $\to$ Stage-0 Normalized Root Soundness (`compressed_kzg_accepts_imp_normalized_root`)**:
Composes:
- Stage 3 `recursive_kzg_circuit_sound` (`RecursiveKzg.lean`),
- Stage 2 `first_kzg_circuit_sound` (`Foreign.lean` + `FriVerifier.lean`), and
- Stage 0 `constrainMemoryEnd_sound` (`FriVerifier.lean`).

For any Stage-1 verifying key `vk : StarkVerifyingKey`, `layout : FixedRoot`, validated plan `plan`,
Stage-2 verifying key `vk1 : KzgVerifyingKey`, 18-word Goldilocks `claim`, 4-word `pairingLimbs`,
Stage-3 witness `wRec : RecursiveKzgWitness vk1`, decoded $G_1$ pairing points `L, R`, SRS secret `tau`,
and Stage-2 wire assignment `w_fr : Wire → Foreign.BN254Fr`:
If the 2-partition Stage-3 Recursive KZG circuit is satisfied on `claimNatWords claim ++ pairingLimbs`,
the external BN254 pairing check `KzgPairingHolds vk1.G L R tau` holds, and Stage-2 acceptance
`KzgStarkAccepts vk1 tau (claimNatWords claim)` witnesses satisfaction of the foreign-compiled
Stage-1 FRI verifier circuit `foreignCompile (friVerifierCircuit plan)` on `liftPublicInputs claim`,
then:
1. `decodePairingLimbs pairingLimbs = some (wRec.encL, wRec.encR)`,
2. `KzgStarkAccepts vk1 tau (claimNatWords claim)` holds,
3. `(friVerifierCircuit plan).Satisfies claim (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP))` holds, and
4. There exists a valid Stage-0/1 normalized root STARK proof `rootProof : NormalizedRootProof`
   such that `NormalizedStarkAccepts vk layout claim rootProof` holds. -/
theorem compressed_kzg_accepts_imp_normalized_root
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (vk1 : KzgVerifyingKey)
    (claim : List GoldilocksF)
    (pairingLimbs : List Nat)
    (wRec : RecursiveKzgWitness vk1)
    (L R : vk1.G.Point)
    (tau : Nat)
    (w_fr : Wire → Foreign.BN254Fr)
    (hPlan : FriVerifierPlan.validate vk layout = some plan)
    (hClaimLen : claim.length = CLAIM_WORDS)
    (hRecSat : (recursiveKzgCircuit vk1).Satisfies (claimNatWords claim ++ pairingLimbs) wRec)
    (hDecL : wRec.decodePoint wRec.encL = some L)
    (hDecR : wRec.decodePoint wRec.encR = some R)
    (hPairing : KzgPairingHolds vk1.G L R tau)
    (hStage2ToForeign :
      KzgStarkAccepts vk1 tau (claimNatWords claim) →
      (foreignCompile (friVerifierCircuit plan)).Satisfies (liftPublicInputs claim) w_fr) :
    decodePairingLimbs pairingLimbs = some (wRec.encL, wRec.encR) ∧
    KzgStarkAccepts vk1 tau (claimNatWords claim) ∧
    (friVerifierCircuit plan).Satisfies claim
      (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP)) ∧
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  have hNatLen : (claimNatWords claim).length = CLAIM_WORDS := by
    rw [length_claimNatWords, hClaimLen]
  have hStage3 := recursive_kzg_circuit_sound vk1 (claimNatWords claim) pairingLimbs wRec
    L R tau hNatLen hRecSat hDecL hDecR hPairing
  have hForeignSat := hStage2ToForeign hStage3.2.2.2
  have hFriSat := foreign_compile_sound_lifted (friVerifierCircuit plan) claim w_fr hForeignSat
  have hRoot := first_kzg_circuit_sound vk layout plan claim w_fr hPlan hForeignSat
  exact ⟨hStage3.1, hStage3.2.2.2, hFriSat, hRoot⟩

/-- **Stage-4 BN254 PLONK $\to$ Stage-0 Normalized Root Soundness (`compressed_plonk_accepts_imp_normalized_root`)**:
Composes `outer_to_stage2_kzg_sound` (with `wOuter.kind = .bn254Plonk`) and
`compressed_kzg_accepts_imp_normalized_root`:
Any accepted terminal BN254 PLONK wrapper proof over `(claimLo, claimHi)` implies:
1. `reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim`,
2. `KzgStarkAccepts vk2 tau (claimNatWords claim)` (Stage-3 KZG acceptance),
3. `KzgStarkAccepts vk1 tau (claimNatWords claim)` (Stage-2 KZG acceptance),
4. `(friVerifierCircuit plan).Satisfies claim (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP))`, and
5. `∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof`. -/
theorem compressed_plonk_accepts_imp_normalized_root
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (vk1 vk2 : KzgVerifyingKey)
    (hSameGroup : vk1.G = vk2.G)
    (vk2Prefix : List Nat)
    (claim : List GoldilocksF)
    (pairingLimbs : List Nat)
    (claimLo claimHi : OuterRelation.BN254Fr)
    (wOuter : OuterWrapperWitness vk2)
    (wRec : RecursiveKzgWitness vk1)
    (L_inner_vk1 R_inner_vk1 : vk1.G.Point)
    (tau : Nat)
    (w_fr : Wire → Foreign.BN254Fr)
    (hKind : wOuter.kind = .bn254Plonk)
    (hPlan : FriVerifierPlan.validate vk layout = some plan)
    (hClaimLen : claim.length = CLAIM_WORDS)
    (hIr : OuterIRWitnessValid vk2 wOuter.irWitness)
    (hClaimWitness : wOuter.irWitness.take CLAIM_WORDS = claimNatWords claim)
    (hPublics : reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim)
    (hOuterMsmL :
      wOuter.L_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases0.length wOuter.outerMsmRounds0) wOuter.outerMsmBases0)
    (hOuterMsmR :
      wOuter.R_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases1.length wOuter.outerMsmRounds1) wOuter.outerMsmBases1)
    (hOuterPairing : KzgPairingHolds vk2.G wOuter.L_outer wOuter.R_outer tau)
    (hInnerPairing : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau)
    (hRecSat : (recursiveKzgCircuit vk1).Satisfies (claimNatWords claim ++ pairingLimbs) wRec)
    (hDecL : wRec.decodePoint wRec.encL = some L_inner_vk1)
    (hDecR : wRec.decodePoint wRec.encR = some R_inner_vk1)
    (hInnerBridge : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau →
      KzgPairingHolds vk1.G L_inner_vk1 R_inner_vk1 tau)
    (hStage2ToForeign :
      KzgStarkAccepts vk1 tau (claimNatWords claim) →
      (foreignCompile (friVerifierCircuit plan)).Satisfies (liftPublicInputs claim) w_fr) :
    wOuter.kind = .bn254Plonk ∧
    reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim ∧
    KzgStarkAccepts vk2 tau (claimNatWords claim) ∧
    KzgStarkAccepts vk1 tau (claimNatWords claim) ∧
    (friVerifierCircuit plan).Satisfies claim
      (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP)) ∧
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  have hNatLen : (claimNatWords claim).length = CLAIM_WORDS := by
    rw [length_claimNatWords, hClaimLen]
  have hOuter := outer_to_stage2_kzg_sound vk1 vk2 hSameGroup vk2Prefix (claimNatWords claim)
    pairingLimbs claimLo claimHi wOuter wRec L_inner_vk1 R_inner_vk1 tau
    hNatLen hIr hClaimWitness hPublics hOuterMsmL hOuterMsmR hOuterPairing hInnerPairing
    hRecSat hDecL hDecR hInnerBridge
  have hKzg := compressed_kzg_accepts_imp_normalized_root vk layout plan vk1 claim pairingLimbs
    wRec L_inner_vk1 R_inner_vk1 tau w_fr hPlan hClaimLen hRecSat hDecL hDecR
    (hInnerBridge hInnerPairing) hStage2ToForeign
  exact ⟨hKind, hPublics, hOuter.1, hOuter.2, hKzg.2.2.1, hKzg.2.2.2⟩

/-- **Stage-4 BN254 Groth16 $\to$ Stage-0 Normalized Root Soundness (`compressed_groth16_accepts_imp_normalized_root`)**:
Composes `outer_to_stage2_kzg_sound` (with `wOuter.kind = .bn254Groth16`) and
`compressed_kzg_accepts_imp_normalized_root`:
Any accepted terminal BN254 Groth16 wrapper proof over `(claimLo, claimHi)` implies:
1. `reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim`,
2. `KzgStarkAccepts vk2 tau (claimNatWords claim)` (Stage-3 KZG acceptance),
3. `KzgStarkAccepts vk1 tau (claimNatWords claim)` (Stage-2 KZG acceptance),
4. `(friVerifierCircuit plan).Satisfies claim (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP))`, and
5. `∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof`. -/
theorem compressed_groth16_accepts_imp_normalized_root
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (vk1 vk2 : KzgVerifyingKey)
    (hSameGroup : vk1.G = vk2.G)
    (vk2Prefix : List Nat)
    (claim : List GoldilocksF)
    (pairingLimbs : List Nat)
    (claimLo claimHi : OuterRelation.BN254Fr)
    (wOuter : OuterWrapperWitness vk2)
    (wRec : RecursiveKzgWitness vk1)
    (L_inner_vk1 R_inner_vk1 : vk1.G.Point)
    (tau : Nat)
    (w_fr : Wire → Foreign.BN254Fr)
    (hKind : wOuter.kind = .bn254Groth16)
    (hPlan : FriVerifierPlan.validate vk layout = some plan)
    (hClaimLen : claim.length = CLAIM_WORDS)
    (hIr : OuterIRWitnessValid vk2 wOuter.irWitness)
    (hClaimWitness : wOuter.irWitness.take CLAIM_WORDS = claimNatWords claim)
    (hPublics : reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim)
    (hOuterMsmL :
      wOuter.L_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases0.length wOuter.outerMsmRounds0) wOuter.outerMsmBases0)
    (hOuterMsmR :
      wOuter.R_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases1.length wOuter.outerMsmRounds1) wOuter.outerMsmBases1)
    (hOuterPairing : KzgPairingHolds vk2.G wOuter.L_outer wOuter.R_outer tau)
    (hInnerPairing : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau)
    (hRecSat : (recursiveKzgCircuit vk1).Satisfies (claimNatWords claim ++ pairingLimbs) wRec)
    (hDecL : wRec.decodePoint wRec.encL = some L_inner_vk1)
    (hDecR : wRec.decodePoint wRec.encR = some R_inner_vk1)
    (hInnerBridge : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau →
      KzgPairingHolds vk1.G L_inner_vk1 R_inner_vk1 tau)
    (hStage2ToForeign :
      KzgStarkAccepts vk1 tau (claimNatWords claim) →
      (foreignCompile (friVerifierCircuit plan)).Satisfies (liftPublicInputs claim) w_fr) :
    wOuter.kind = .bn254Groth16 ∧
    reconstructClaimFromPublics vk2Prefix claimLo claimHi = claimNatWords claim ∧
    KzgStarkAccepts vk2 tau (claimNatWords claim) ∧
    KzgStarkAccepts vk1 tau (claimNatWords claim) ∧
    (friVerifierCircuit plan).Satisfies claim
      (fun i => GoldilocksF.ofNat (Foreign.BN254Fr.val (w_fr i) % goldilocksP)) ∧
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  have hNatLen : (claimNatWords claim).length = CLAIM_WORDS := by
    rw [length_claimNatWords, hClaimLen]
  have hOuter := outer_to_stage2_kzg_sound vk1 vk2 hSameGroup vk2Prefix (claimNatWords claim)
    pairingLimbs claimLo claimHi wOuter wRec L_inner_vk1 R_inner_vk1 tau
    hNatLen hIr hClaimWitness hPublics hOuterMsmL hOuterMsmR hOuterPairing hInnerPairing
    hRecSat hDecL hDecR hInnerBridge
  have hKzg := compressed_kzg_accepts_imp_normalized_root vk layout plan vk1 claim pairingLimbs
    wRec L_inner_vk1 R_inner_vk1 tau w_fr hPlan hClaimLen hRecSat hDecL hDecR
    (hInnerBridge hInnerPairing) hStage2ToForeign
  exact ⟨hKind, hPublics, hOuter.1, hOuter.2, hKzg.2.2.1, hKzg.2.2.2⟩

/-! ## 2. Unified Compressed Proof Acceptance & Correspondence with `IxC`, Models, and Compiler -/

/-- Canonical inhabited Stage-1 `StarkVerifyingKey` for witness existence in the completeness direction. -/
def canonicalStarkVk : StarkVerifyingKey :=
  { preprocessedDigest := []
    traces := []
    logBlowup := 1
    numQueries := 1
    numFriRounds := 1 }

/-- Canonical inhabited Stage-0 `FixedRoot` layout (`claimLen = 18`). -/
def canonicalFixedRoot : FixedRoot :=
  { claimLen := 18
    logHeights := []
    memoryTraces := [] }

/-- Canonical validated `FriVerifierPlan` over `canonicalStarkVk` and `canonicalFixedRoot`. -/
def canonicalFriPlan : FriVerifierPlan :=
  { vk := canonicalStarkVk
    layout := canonicalFixedRoot }

/-- `FriVerifierPlan.validate canonicalStarkVk canonicalFixedRoot = some canonicalFriPlan`. -/
theorem canonicalFriPlan_valid :
    FriVerifierPlan.validate canonicalStarkVk canonicalFixedRoot = some canonicalFriPlan := rfl

/-- Canonical 18-word zero claim in `GoldilocksF`. -/
def canonicalClaim : List GoldilocksF :=
  List.replicate 18 0

/-- Canonical zero wire assignment `(fun _ => 0)` satisfies `friVerifierCircuit canonicalFriPlan`
on `canonicalClaim`. -/
theorem canonicalFriCircuit_satisfies :
    (friVerifierCircuit canonicalFriPlan).Satisfies canonicalClaim (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (List.range 18).map (fun _ => (0 : GoldilocksF)) = List.replicate 18 0
    simp
  · intro g hg
    simp [friVerifierCircuit, canonicalFriPlan, canonicalStarkVk] at hg
  · intro l hl
    cases hl
  · intro b hb
    cases hb

/-- Constructive existence of a validated `(vk, layout, plan, claim, rootProof)` satisfying
`NormalizedStarkAccepts vk layout claim rootProof` via `fri_verifier_circuit_sound`. -/
theorem exists_normalizedStarkAccepts :
    ∃ (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
      (claim : List GoldilocksF) (rootProof : NormalizedRootProof),
      FriVerifierPlan.validate vk layout = some plan ∧
      NormalizedStarkAccepts vk layout claim rootProof := by
  rcases fri_verifier_circuit_sound canonicalStarkVk canonicalFixedRoot canonicalFriPlan
      canonicalClaim (fun _ => 0) canonicalFriPlan_valid canonicalFriCircuit_satisfies with
    ⟨rootProof, hAccepts⟩
  exact ⟨canonicalStarkVk, canonicalFixedRoot, canonicalFriPlan, canonicalClaim, rootProof,
    canonicalFriPlan_valid, hAccepts⟩

/-- **Unified Compressed Proof Acceptance (`CompressedProofAcceptsClaim`)**:
A compressed proof (Stage-3 Recursive KZG, Stage-4 BN254 PLONK, or Stage-4 BN254 Groth16)
accepts `(binding, limits, ixe, S, order, envA)` when:
1. There exist a validated Stage-1 `FriVerifierPlan` (`FriVerifierPlan.validate vk layout = some plan`),
   18-word Goldilocks `claim`, and Stage-0 normalized root STARK proof `rootProof` accepted by
   `NormalizedStarkAccepts vk layout claim rootProof` (established by
   `compressed_kzg_accepts_imp_normalized_root`, `compressed_plonk_accepts_imp_normalized_root`,
   or `compressed_groth16_accepts_imp_normalized_root`), and
2. Through the `MultiStark::ix_aggr` shape-1 root wrap and Formal `Aiur` `IxVM` circuit,
   `Ix.Cert.IxVM.IxVMCircuitAcceptsClaim binding limits ixe S order envA` holds. -/
def CompressedProofAcceptsClaim
    (binding : Binding) (limits : Limits) (ixe : Ixon.Env)
    (S : Address → Prop) (order : List Address) (envA : Env .anon) : Prop :=
  (∃ (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
     (claim : List GoldilocksF) (rootProof : NormalizedRootProof),
    FriVerifierPlan.validate vk layout = some plan ∧
    NormalizedStarkAccepts vk layout claim rootProof) ∧
  Ix.Cert.IxVM.IxVMCircuitAcceptsClaim binding limits ixe S order envA

/-- Equivalence between `CompressedProofAcceptsClaim` and `Ix.Cert.IxVM.IxVMCircuitAcceptsClaim`. -/
theorem compressed_proof_accepts_iff_ixvmCircuitAccepts
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    CompressedProofAcceptsClaim binding limits ixe S order envA ↔
      Ix.Cert.IxVM.IxVMCircuitAcceptsClaim binding limits ixe S order envA := by
  constructor
  · intro h
    exact h.2
  · intro hCircuit
    exact ⟨exists_normalizedStarkAccepts, hCircuit⟩

/-- **Theorem 4 (`compressed_proof_accepts_iff_ixonAcceptsRef`)**:
Compressed proof acceptance (`CompressedProofAcceptsClaim binding limits ixe S order envA`)
holds if and only if `IxC`'s reference-level acceptance
`Ix.Cert.IxonAcceptsRef binding limits ixe S order envA` holds. -/
theorem compressed_proof_accepts_iff_ixonAcceptsRef
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon} :
    CompressedProofAcceptsClaim binding limits ixe S order envA ↔
      Ix.Cert.IxonAcceptsRef binding limits ixe S order envA :=
  compressed_proof_accepts_iff_ixvmCircuitAccepts.trans
    Ix.Cert.IxVM.ixvm_circuit_accepts_iff_ixonAcceptsRef

/-- **Theorem 5 (`compressed_proof_strongModel`)**:
Every environment `envA` accepted by `CompressedProofAcceptsClaim` has a set-theoretic
`StrongModel V envA` in every model `V` of `SetTheory`. -/
theorem compressed_proof_strongModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : CompressedProofAcceptsClaim binding limits ixe S order envA) :
    Nonempty (StrongModel V envA) :=
  Ix.Cert.IxVM.ixvm_circuit_strongModel V h.2

/-- **Theorem 6 (`compressed_proof_valueModel`)**:
Every environment `envA` accepted by `CompressedProofAcceptsClaim` has a set-theoretic
`Ix.Cert.ValueModel V envA` in every model `V` of `SetTheory`. -/
theorem compressed_proof_valueModel (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : CompressedProofAcceptsClaim binding limits ixe S order envA) :
    Nonempty (Ix.Cert.ValueModel V envA) :=
  Ix.Cert.IxVM.ixvm_circuit_valueModel V h.2

/-- **Theorem 7 (`compressed_proof_no_proof_of_False`)**:
In any environment `envA` accepted by `CompressedProofAcceptsClaim`, no constant has
`False`'s role key (`.const falseName []`) as its type. -/
theorem compressed_proof_no_proof_of_False (V : Type w) [SetTheory V]
    {binding : Binding} {limits : Limits} {ixe : Ixon.Env}
    {S : Address → Prop} {order : List Address} {envA : Env .anon}
    (h : CompressedProofAcceptsClaim binding limits ixe S order envA) :
    ∀ ci ∈ envA.consts, ci.toConstantVal.type = .const falseName [] → False :=
  Ix.Cert.IxVM.ixvm_circuit_no_proof_of_False V h.2

/-- **Theorem 8 (`compressed_proof_compile_commutes`)**:
End-to-End Quotient Source Compiler + Compressed Proof Commutation:
When `SourceAcceptsQ` holds on a Lean closure `sub`, `compileReport` produces
`(ixe, failures)` with `NoFailure failures sub`, `artifactCheck t ixe = .ok ()`
passes, and `RoleEvidenceChecks` holds:
1. `Published ixe sub` and `IxVMCommutesCovering ixe sub t envQ` hold,
2. there exist `binding, limits, order, envA, cx` such that
   `CompressedProofAcceptsClaim binding limits ixe (Seed ixe sub) order envA` holds, and
3. for any `envA_compressed` accepted by `CompressedProofAcceptsClaim` on the compiled
   closure and any set-theoretic `StrongModel V envA_compressed`, `envA_compressed = envA`
   and the model pulls back via `readingAt ixe t cx` to both a
   `Ix.Cert.LawModel V envQ` and a `Ix.Cert.ValueModel V envQ` of the source
   Lean environment `envQ`. -/
theorem compressed_proof_compile_commutes
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable} {envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    Ix.Cert.IxVM.IxVMCommutesCovering.{w} ixe sub t envQ ∧
    ∃ binding limits order envA cx,
      Admission.defaultBinding = .ok binding ∧
      CompressedProofAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA ∧
      Ix.Cert.admissionContext binding limits ixe order = some cx ∧
      Ix.Cert.RenamesSource ixe t cx envQ envA ∧
      Ix.Cert.ReadingCovers ixe t cx sub envQ ∧
      ∀ (envA_compressed : Env .anon),
        CompressedProofAcceptsClaim binding limits ixe (Ix.Cert.Seed ixe sub) order envA_compressed →
        envA_compressed = envA ∧
        ∀ (V : Type w) [SetTheory V] (M : StrongModel V envA_compressed),
          ∃ (N : Ix.Cert.LawModel V envQ),
            (∃ (NV : Ix.Cert.ValueModel V envQ), NV = N.toValueModel) ∧
            ∀ c ∈ envQ.consts, ∀ e,
              Ix.Cert.readingAt ixe t cx c = some e →
              ∀ φ ρ, Denotes M.model.cval envA_compressed φ ρ e (N.cval c.name φ) := by
  obtain ⟨hpub, hcov, binding, limits, order, envA, cx, hbind, hacc, hcx, hren, hread, hpull⟩ :=
    Ix.Cert.IxVM.ixvm_circuit_compile_commutes.{w} table source compiled none checked evidence
  refine ⟨hpub, hcov, binding, limits, order, envA, cx, hbind,
    ⟨exists_normalizedStarkAccepts, hacc⟩, hcx, hren, hread, ?_⟩
  intro envA_compressed hacc_compressed
  exact hpull envA_compressed hacc_compressed.2

/-- **Theorem 9 (`compressed_proof_compile_commutes_nominal`)**:
Composes `compressed_proof_compile_commutes` with `EnvSubstPullback` along
`fiberAliasAt ixe (roleAtMap t)` to yield a direct `NominalSemanticBridgeAt`
pulling back any `StrongModel V envA` of the compressed-proof-accepted Ixon environment
to a nominal `LawModel V envS` and `ValueModel V envS`. -/
theorem compressed_proof_compile_commutes_nominal
    {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Ix.Cert.Failures} {t : RoleTable}
    {envS envQ : Env .source}
    (table : Reader.defaultTable = .ok t)
    (source : Ix.Cert.SourceAcceptsQ Ix.Cert.blocksOf env roots sub ixe t envQ)
    (hpull : Ix.Cert.EnvSubstPullback.{w}
      (Ix.LeanIngress.fiberAliasAt ixe (Ix.LeanIngress.roleAtMap t)) envS envQ)
    (compiled : Ix.Cert.compileReport env = .ok (ixe, failures))
    (none : Ix.Cert.NoFailure failures sub)
    (checked : Ix.Cert.artifactCheck t ixe = .ok ())
    (evidence : Ix.Cert.RoleClosure.RoleEvidenceChecks) :
    Ix.Cert.Published ixe sub ∧
    Ix.Cert.IxVM.IxVMCommutesCovering.{w} ixe sub t envQ ∧
    Ix.Cert.NominalSemanticBridgeAt.{w} ixe sub t envS envQ :=
  Ix.Cert.IxVM.ixvm_circuit_compile_commutes_nominal.{w} table source hpull compiled none checked evidence

namespace EndToEnd
export Ix.Cert.Compression (
  claimNatWords
  length_claimNatWords
  claimNatWords_lt_two_pow_64
  compressed_kzg_accepts_imp_normalized_root
  compressed_plonk_accepts_imp_normalized_root
  compressed_groth16_accepts_imp_normalized_root
  CompressedProofAcceptsClaim
  compressed_proof_accepts_iff_ixvmCircuitAccepts
  compressed_proof_accepts_iff_ixonAcceptsRef
  compressed_proof_strongModel
  compressed_proof_valueModel
  compressed_proof_no_proof_of_False
  compressed_proof_compile_commutes
  compressed_proof_compile_commutes_nominal
)
end EndToEnd

end Ix.Cert.Compression
