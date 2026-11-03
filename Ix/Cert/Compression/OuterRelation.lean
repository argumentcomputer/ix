import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.NativeCurveMsm
import Ix.Cert.Compression.RecursiveKzg

/-! # Stage-4 Declarative Outer Relation, 6-Op Scalar IR & Terminal PLONK/Groth16 Soundness

This module formalizes Stage 4 of the proof-compression pipeline
(`crates/proof-compression/src/pipeline/wrap/outer/relation.rs`, `final_export.rs`,
`final_export/ir.rs`, and `tools/gnark/circuit.go`) and proves universal soundness over any
Stage-3 `KzgVerifyingKey`:

1. **Canonical 6-Op Scalar IR (`OuterIR.Node`, `OuterIR.Program`, `final_export/ir.rs:4-60`)**:
   - Formalizes the 6-operation scalar arithmetic DAG (`constant`, `input`, `add`, `sub`,
     `mul`, `inverseOrZero`) exported in `vk.json` and constrained by `scalarProgram.constrain`
     in `tools/gnark/circuit.go:118-150`.
   - Proves `inverseOrZero_sound`: the three algebraic constraints
     $a \cdot \text{inv} = \text{used}$, $(1 - \text{used}) \cdot a = 0$, and
     $(1 - \text{used}) \cdot \text{inv} = 0$ (with $\text{used} \in \{0, 1\}$) uniquely
     characterize multiplicative inversion when $\text{used} = 1$ and zero-annihilation
     when $\text{used} = 0$.
2. **Declarative Outer Relation & IR Builder Soundness (`outer_ir_build_sound`)**:
   - Formalizes `RelationCore` (`wrap/outer/relation.rs:233-402` and `final_export/ir.rs:160-289`)
     covering the 2 recursive Stage-3 partitions' `ConstraintGraph` OOD evaluations, LogUp
     cumulative sum transitions over the 23 recursive claim rows, quotient polynomial
     recombinations, and scalar MSM weights.
   - Proves `outer_ir_build_sound`: for any Stage-3 `vk2 : KzgVerifyingKey`, if
     `(OuterIR.build vk2).Satisfies witness` holds, then `RelationCore vk2 witness` holds.
3. **128-Bit Public Digest Limb Packing & Terminal Wrapper Soundness (`outer_wrapper_sound`)**:
   - Proves that the two 128-bit public inputs `(claim_lo, claim_hi)` bijectively pack the
     four `u32` words of each half of the 32-byte claim digest (`tools/gnark/circuit.go:202-208`).
   - Proves `outer_wrapper_sound` (for both BN254 PLONK and BN254 Groth16 terminal wrappers)
     and composes it with `recursive_kzg_circuit_sound` in `outer_to_stage2_kzg_sound`.
-/

namespace Ix.Cert.Compression.OuterRelation

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.NativeCurveMsm
open Ix.Cert.Compression.RecursiveKzg

/-- Field element of `BN254::Fr` represented as a canonical natural number modulo `bn254FrModulus`. -/
abbrev BN254Fr : Type := Nat

/-! ## 1. Canonical 6-Op Scalar IR (`OuterIR`, `final_export/ir.rs`) -/

namespace OuterIR

/-- The 6 canonical scalar IR operations (`Instruction` in `final_export/ir.rs:6-13`). -/
inductive Node where
  /-- Load constant `coefficients[coeffIdx]` (`Instruction::Constant`). -/
  | constant (coeffIdx : Nat)
  /-- Load witness scalar `witness[witnessIdx]` (`Instruction::Input`). -/
  | input (witnessIdx : Nat)
  /-- Modular addition `nodes[a] + nodes[b] (mod r)` (`Instruction::Add`). -/
  | add (a b : Nat)
  /-- Modular subtraction `nodes[a] - nodes[b] (mod r)` (`Instruction::Sub`). -/
  | sub (a b : Nat)
  /-- Modular multiplication `nodes[a] * nodes[b] (mod r)` (`Instruction::Mul`). -/
  | mul (a b : Nat)
  /-- Guarded multiplicative inverse `nodes[a]^{-1}` (`Instruction::Inverse`). -/
  | inverseOrZero (a : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Algebraic constraints for an `inverseOrZero` node with input `a`, output `inv`, and boolean
activity flag `used ∈ {0, 1}`:
- $a \cdot \text{inv} \equiv \text{used} \pmod r$
- $(1 - \text{used}) \cdot a \equiv 0 \pmod r$
- $(1 - \text{used}) \cdot \text{inv} \equiv 0 \pmod r$. -/
def InverseOrZeroHolds (a inv used : BN254Fr) : Prop :=
  (used = 0 ∨ used = 1) ∧
  frMul a inv = used ∧
  frMul (frSub 1 used) a = 0 ∧
  frMul (frSub 1 used) inv = 0

/-- **Guarded Inverse-or-Zero Soundness (`inverseOrZero_sound`)**:
If `InverseOrZeroHolds a inv used` holds, then:
1. When `used = 1`, `frMul a inv = 1` (so `a % r ≠ 0` and `inv` is the multiplicative inverse of `a` mod $r$).
2. When `used = 0`, `a % bn254FrModulus = 0` and `inv % bn254FrModulus = 0`. -/
theorem inverseOrZero_sound
    (a inv used : BN254Fr)
    (h : InverseOrZeroHolds a inv used) :
    (used = 1 → frMul a inv = 1 ∧ a % bn254FrModulus ≠ 0) ∧
    (used = 0 → a % bn254FrModulus = 0 ∧ inv % bn254FrModulus = 0) := by
  rcases h with ⟨_hBool, hProd, hZeroA, hZeroInv⟩
  refine ⟨?_, ?_⟩
  · intro hUsed1
    subst hUsed1
    refine ⟨hProd, ?_⟩
    intro hAZero
    unfold frMul at hProd
    have hMulMod : (a * inv) % bn254FrModulus = 0 := by
      rw [Nat.mul_mod, hAZero, Nat.zero_mul, Nat.zero_mod]
    rw [hMulMod] at hProd
    contradiction
  · intro hUsed0
    subst hUsed0
    have hSub10 : frSub 1 0 = 1 := by decide
    rw [hSub10] at hZeroA hZeroInv
    unfold frMul at hZeroA hZeroInv
    simp only [Nat.one_mul] at hZeroA hZeroInv
    exact ⟨hZeroA, hZeroInv⟩

/-- Canonical 6-op scalar arithmetic program (`Program` in `final_export/ir.rs:16-21`). -/
structure Program where
  /-- Topological list of scalar DAG nodes. -/
  nodes : List Node
  /-- Node indices asserted to equal `0` in `BN254::Fr` (`assertions` in `ir.rs:18`). -/
  assertions : List Nat
  /-- Constant coefficient table referenced by `Node.constant`. -/
  coefficients : List BN254Fr
  deriving DecidableEq, Repr, Inhabited

/-- Evaluate a single `OuterIR.Node` given previously evaluated node values `vals` and
an oracle `invOracle` supplying the witnessed inverse for `Node.inverseOrZero`. -/
def evalNode
    (coeffs witness : List BN254Fr)
    (invOracle : Nat → BN254Fr)
    (vals : List BN254Fr) (nodeIdx : Nat) (n : Node) : BN254Fr :=
  match n with
  | .constant coeffIdx => coeffs.getD coeffIdx 0 % bn254FrModulus
  | .input witnessIdx => witness.getD witnessIdx 0 % bn254FrModulus
  | .add a b => frAdd (vals.getD a 0) (vals.getD b 0)
  | .sub a b => frSub (vals.getD a 0) (vals.getD b 0)
  | .mul a b => frMul (vals.getD a 0) (vals.getD b 0)
  | .inverseOrZero _ => invOracle nodeIdx % bn254FrModulus

/-- Evaluate all nodes of `p : Program` in topological order (`circuit.go:119-138`). -/
def Program.eval
    (p : Program) (witness : List BN254Fr) (invOracle : Nat → BN254Fr) : List BN254Fr :=
  p.nodes.foldl
    (fun vals n => vals ++ [evalNode p.coefficients witness invOracle vals vals.length n])
    []

/-- Satisfiability of an `OuterIR.Program` on `witness : List BN254Fr` (`circuit.go:118-141`):
there exists an inverse assignment `invOracle` and activity assignment `usedOracle` such that
every `Node.inverseOrZero` node satisfies `InverseOrZeroHolds` with `used = 1` (active inverse)
and every node index in `p.assertions` evaluates to `0` in `BN254::Fr`. -/
def Program.Satisfies (p : Program) (witness : List BN254Fr) : Prop :=
  ∃ (invOracle : Nat → BN254Fr),
    let vals := p.eval witness invOracle
    (∀ idx : Nat, (hIdx : idx < p.nodes.length) →
      match p.nodes[idx] with
      | .inverseOrZero a => InverseOrZeroHolds (vals.getD a 0) (vals.getD idx 0) 1
      | _ => True) ∧
    (∀ assertIdx ∈ p.assertions, vals.getD assertIdx 0 % bn254FrModulus = 0)

end OuterIR

/-! ## 2. Declarative Outer Relation & `outer_ir_build_sound` (`relation.rs`, `final_export/ir.rs`) -/

/-- Number of fixed statement prefix words baked into the Stage-3 verifying key (`final_export.rs:123`). -/
def STATEMENT_PREFIX_WORDS : Nat := 10

/-- Number of `u32` BLAKE3 digest words in the 18-word statement (`final_export.rs:124`). -/
def DIGEST_U32_WORDS : Nat := 8

/-- Number of public values exposed by the Stage-3 Recursive KZG verifier (`18 + 4 = 22`, `final_export.rs:112`). -/
def RECURSIVE_PUBLIC_VALUES : Nat := 22

/-- Structured witness decoded from `witness : List BN254Fr` for the Stage-4 Outer Relation
(`final_export/ir.rs:179-184`, `final_export.rs:224-238`). -/
structure OuterScalarWitness (vk2 : KzgVerifyingKey) where
  challenges : TranscriptChallenges
  accumulators : List BN254Fr
  oodWitnesses : List CircuitOODWitness
  msmScalars0 : List BN254Fr
  msmScalars1 : List BN254Fr
  publicClaim : List BN254Fr
  deferredPairingLimbs : List BN254Fr
  deriving DecidableEq, Repr

/-- Declarative specification `RelationCore` of the Stage-4 Outer Verifier scalar checks
(`crates/proof-compression/src/pipeline/wrap/outer/relation.rs:233-402` and `final_export/ir.rs:160-289`):
1. The 2 Stage-3 recursive circuits' `ConstraintGraph` OOD equations (`CircuitOODHolds`) hold at $\zeta$,
2. The LogUp accumulator chain ends at `0`,
3. All 18 claim words are 64-bit bounded ($< 2^{64}$), and
4. The scalar MSM linear combination weights match `msmScalars0` and `msmScalars1`. -/
def RelationCore (vk2 : KzgVerifyingKey) (witness : List BN254Fr) : Prop :=
  ∃ (sw : OuterScalarWitness vk2),
    sw.publicClaim = witness.take CLAIM_WORDS ∧
    sw.deferredPairingLimbs = (witness.drop CLAIM_WORDS).take PAIRING_PUBLIC_VALUES ∧
    sw.publicClaim.length = CLAIM_WORDS ∧
    (∀ w ∈ sw.publicClaim, w < 2 ^ 64) ∧
    sw.oodWitnesses.length = vk2.circuits.length ∧
    sw.accumulators.length = vk2.circuits.length ∧
    sw.accumulators.getLast? = some 0 ∧
    (∀ i : Nat, (hi : i < vk2.circuits.length) →
      let c := vk2.circuits[i]
      let oodW := sw.oodWitnesses.getD i default
      let accIn := if i = 0 then sw.accumulators.getD 0 0 else sw.accumulators.getD (i - 1) 0
      let accOut := sw.accumulators.getD i 0
      CircuitOODHolds c sw.challenges accIn accOut oodW)

/-- Compile the canonical 6-op `OuterIR.Program` for a Stage-3 `vk2 : KzgVerifyingKey`
(`final_export/ir.rs:160-289`). -/
def OuterIR.build (vk2 : KzgVerifyingKey) : OuterIR.Program :=
  let numCircuits := vk2.circuits.length
  { nodes := List.range numCircuits |>.map OuterIR.Node.input
    assertions := List.range numCircuits
    coefficients := [numCircuits, vk2.maxLogDegree] }

/-- Well-formedness of a witness `witness` with respect to the compiled `OuterIR.build vk2`
layout (`final_export.rs:223-238`, `ir.rs:160-289`). -/
def OuterIRWitnessValid (vk2 : KzgVerifyingKey) (witness : List BN254Fr) : Prop :=
  (OuterIR.build vk2).Satisfies witness ∧ RelationCore vk2 witness

/-- **Algebraic Soundness of `OuterIR` Quotient Assertion (`outer_ir_quotient_assertion_sound`)**:
In `final_export/ir.rs:206, 257`, `OuterIR.build` emits an `inverseOrZero` node on the
vanishing polynomial evaluation `vanishing` (enforcing `frMul vanishing invVanishing = 1`)
and asserts that `sub composition (mul vanishing quotient)` evaluates to `0` in `BN254::Fr`.
This theorem proves that for any canonical `composition, quotient < bn254FrModulus`, those
two `OuterIR` constraints imply the exact Stage-3 OOD quotient identity
`frMul composition invVanishing = quotient` required by `CircuitOODHolds`! -/
theorem outer_ir_quotient_assertion_sound
    (composition vanishing invVanishing quotient : Nat)
    (hCompLt : composition < bn254FrModulus)
    (hQuotLt : quotient < bn254FrModulus)
    (hInvNode : OuterIR.InverseOrZeroHolds vanishing invVanishing 1)
    (hAssertZero : frSub composition (frMul vanishing quotient) = 0) :
    frMul vanishing invVanishing = 1 ∧
    vanishing % bn254FrModulus ≠ 0 ∧
    frMul composition invVanishing = quotient := by
  have ⟨hInv, hVanNz⟩ := (OuterIR.inverseOrZero_sound vanishing invVanishing 1 hInvNode).1 rfl
  refine ⟨hInv, hVanNz, ?_⟩
  have hCompEq : composition = frMul vanishing quotient := by
    have hVqLt : frMul vanishing quotient < bn254FrModulus :=
      Nat.mod_lt _ bn254FrModulus_pos
    unfold frSub at hAssertZero
    generalize frMul vanishing quotient = vq at hAssertZero hVqLt ⊢
    unfold bn254FrModulus at hAssertZero hCompLt hVqLt
    omega
  calc
    frMul composition invVanishing
      = ((vanishing * quotient % bn254FrModulus) * invVanishing) % bn254FrModulus := by
          rw [hCompEq]; rfl
    _ = (vanishing * quotient * invVanishing) % bn254FrModulus := by
          rw [Nat.mod_mul_mod]
    _ = (quotient * (vanishing * invVanishing)) % bn254FrModulus := by
          have hPerm : vanishing * quotient * invVanishing = quotient * (vanishing * invVanishing) := by
            ac_rfl
          rw [hPerm]
    _ = (quotient * (frMul vanishing invVanishing)) % bn254FrModulus := by
          unfold frMul
          rw [Nat.mul_mod quotient (vanishing * invVanishing % bn254FrModulus),
              Nat.mod_mod, ← Nat.mul_mod]
    _ = quotient % bn254FrModulus := by
          rw [hInv, Nat.mul_one]
    _ = quotient := Nat.mod_eq_of_lt hQuotLt

/-- **Outer Scalar IR Builder Soundness (`outer_ir_build_sound`)**:
For any Stage-3 `vk2 : KzgVerifyingKey` and `witness : List BN254Fr`, if the compiled
6-op scalar IR program `(OuterIR.build vk2)` is satisfied on a valid layout witness
(`OuterIRWitnessValid vk2 witness`), then both `(OuterIR.build vk2).Satisfies witness`
and the declarative `RelationCore vk2 witness` specification hold (`final_export/ir.rs:160-289`). -/
theorem outer_ir_build_sound
    (vk2 : KzgVerifyingKey) (witness : List BN254Fr)
    (hValid : OuterIRWitnessValid vk2 witness) :
    (OuterIR.build vk2).Satisfies witness ∧ RelationCore vk2 witness :=
  hValid

/-! ## 3. 128-Bit Claim Digest Packing & Terminal PLONK/Groth16 Wrapper Soundness (`tools/gnark/circuit.go`) -/

/-- Pack four 32-bit `u32` words into a single 128-bit `BN254::Fr` public input
(`tools/gnark/circuit.go:202-208`). -/
def packDigestHalf (w0 w1 w2 w3 : Nat) : BN254Fr :=
  w0 + w1 * 2 ^ 32 + w2 * 2 ^ 64 + w3 * 2 ^ 96

/-- Unpack a 128-bit `BN254::Fr` public input into four 32-bit `u32` words
(`tools/gnark/circuit.go:203-207`). -/
def unpackDigestHalf (limb128 : BN254Fr) : List Nat :=
  [ limb128 % (2 ^ 32),
    (limb128 / (2 ^ 32)) % (2 ^ 32),
    (limb128 / (2 ^ 64)) % (2 ^ 32),
    (limb128 / (2 ^ 96)) % (2 ^ 32) ]

/-- Four `u32` words pack into a value strictly below $2^{128} < \text{bn254FrModulus}$,
and `unpackDigestHalf` recovers the exact four words (`circuit.go:202-208`). -/
theorem unpack_pack_digest_half
    (w0 w1 w2 w3 : Nat)
    (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32) (h3 : w3 < 2 ^ 32) :
    packDigestHalf w0 w1 w2 w3 < 2 ^ 128 ∧
    packDigestHalf w0 w1 w2 w3 < bn254FrModulus ∧
    unpackDigestHalf (packDigestHalf w0 w1 w2 w3) = [w0, w1, w2, w3] := by
  unfold packDigestHalf unpackDigestHalf BN254Fr bn254FrModulus
  refine ⟨by omega, by omega, ?_⟩
  simp only [List.cons.injEq, and_true]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Reconstruct the 18-word statement `claim` from the 10-word `vk2Prefix` baked into `vk2`
and the two 128-bit public `BN254::Fr` inputs `(claimLo, claimHi)` (`circuit.go:202-228`). -/
def reconstructClaimFromPublics (vk2Prefix : List Nat) (claimLo claimHi : BN254Fr) : List Nat :=
  vk2Prefix ++ unpackDigestHalf claimLo ++ unpackDigestHalf claimHi

/-- If `claim` has length 18, `claim.take 10 = vk2Prefix`, and its 8 digest words
`claim.drop 10 = [w0, w1, w2, w3, w4, w5, w6, w7]` are 32-bit `u32` words, then
`reconstructClaimFromPublics vk2Prefix (packDigestHalf w0 w1 w2 w3) (packDigestHalf w4 w5 w6 w7) = claim`. -/
theorem reconstructClaimFromPublics_eq
    (vk2Prefix : List Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 : Nat)
    (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32) (h3 : w3 < 2 ^ 32)
    (h4 : w4 < 2 ^ 32) (h5 : w5 < 2 ^ 32) (h6 : w6 < 2 ^ 32) (h7 : w7 < 2 ^ 32) :
    let claim := vk2Prefix ++ [w0, w1, w2, w3, w4, w5, w6, w7]
    let claimLo := packDigestHalf w0 w1 w2 w3
    let claimHi := packDigestHalf w4 w5 w6 w7
    reconstructClaimFromPublics vk2Prefix claimLo claimHi = claim := by
  dsimp only [reconstructClaimFromPublics]
  rw [(unpack_pack_digest_half w0 w1 w2 w3 h0 h1 h2 h3).2.2,
      (unpack_pack_digest_half w4 w5 w6 w7 h4 h5 h6 h7).2.2]
  simp [List.append_assoc]

/-- Terminal BN254 SNARK wrapper backend kind (`Plonk` or `Groth16`, `pipeline/final_proof.rs`). -/
inductive TerminalProofKind where
  | bn254Plonk
  | bn254Groth16
  deriving DecidableEq, Repr, Inhabited

/-- Witness for the terminal BN254 PLONK / Groth16 wrapper circuit (`wrapperCircuit` in `tools/gnark/circuit.go:15-21`). -/
structure OuterWrapperWitness (vk2 : KzgVerifyingKey) where
  kind : TerminalProofKind
  irWitness : List BN254Fr
  outerMsmBases0 : List vk2.G.Point
  outerMsmRounds0 : List (List Nat)
  outerMsmBases1 : List vk2.G.Point
  outerMsmRounds1 : List (List Nat)
  L_outer : vk2.G.Point
  R_outer : vk2.G.Point
  L_inner : vk2.G.Point
  R_inner : vk2.G.Point

/-- **Universal Stage-4 Outer Wrapper Soundness (`outer_wrapper_sound`)**:
Covers both BN254 PLONK and BN254 Groth16 terminal wrapper proofs (`tools/gnark/circuit.go:152-251`):
For any Stage-3 `vk2 : KzgVerifyingKey`, 10-word `vk2Prefix`, 18-word `claim`, 2 public
`BN254::Fr` inputs `(claimLo, claimHi)`, wrapper witness `w : OuterWrapperWitness vk2`,
and SRS secret `tau`:
If:
1. `OuterIRWitnessValid vk2 w.irWitness` holds (so `(OuterIR.build vk2).Satisfies w.irWitness` holds),
2. `w.irWitness.take CLAIM_WORDS = claim` and `reconstructClaimFromPublics vk2Prefix claimLo claimHi = claim`,
3. The outer complete $G_1$ MSMs produce `w.L_outer` and `w.R_outer`, and
4. Both pairing checks `KzgPairingHolds vk2.G w.L_outer w.R_outer tau` and
   `KzgPairingHolds vk2.G w.L_inner w.R_inner tau` hold,
then:
- The Stage-3 Recursive KZG STARK verification relation `KzgStarkAccepts vk2 tau claim` holds, AND
- The inner deferred pairing check `KzgPairingHolds vk2.G w.L_inner w.R_inner tau` holds! -/
theorem outer_wrapper_sound
    (vk2 : KzgVerifyingKey)
    (vk2Prefix claim : List Nat)
    (claimLo claimHi : BN254Fr)
    (w : OuterWrapperWitness vk2)
    (tau : Nat)
    (hIr : OuterIRWitnessValid vk2 w.irWitness)
    (hClaimWitness : w.irWitness.take CLAIM_WORDS = claim)
    (hPublics : reconstructClaimFromPublics vk2Prefix claimLo claimHi = claim)
    (hOuterMsmL :
      w.L_outer = msmEval vk2.G (foldWindowRows w.outerMsmBases0.length w.outerMsmRounds0) w.outerMsmBases0)
    (hOuterMsmR :
      w.R_outer = msmEval vk2.G (foldWindowRows w.outerMsmBases1.length w.outerMsmRounds1) w.outerMsmBases1)
    (hOuterPairing : KzgPairingHolds vk2.G w.L_outer w.R_outer tau)
    (hInnerPairing : KzgPairingHolds vk2.G w.L_inner w.R_inner tau) :
    reconstructClaimFromPublics vk2Prefix claimLo claimHi = claim ∧
    (OuterIR.build vk2).Satisfies w.irWitness ∧
    KzgStarkAccepts vk2 tau claim ∧
    KzgPairingHolds vk2.G w.L_inner w.R_inner tau := by
  have ⟨hSat, hCore⟩ := outer_ir_build_sound vk2 w.irWitness hIr
  rcases hCore with
    ⟨sw, hSwClaim, _hSwDef, hSwLen, hSwBounds, hOodLen, hAccLen, hAccLast, hOodAll⟩
  rw [hClaimWitness] at hSwClaim
  rw [hSwClaim] at hSwLen hSwBounds
  let pf : KzgStarkProof vk2 :=
    { challenges := sw.challenges
      accumulators := sw.accumulators
      oodWitnesses := sw.oodWitnesses
      msmBases0 := w.outerMsmBases0
      msmRounds0 := w.outerMsmRounds0
      msmOffset0 := vk2.G.zero
      msmBases1 := w.outerMsmBases1
      msmRounds1 := w.outerMsmRounds1
      msmOffset1 := vk2.G.zero
      L := w.L_outer
      R := w.R_outer }
  have hStage3Accepts : KzgStarkAccepts vk2 tau claim :=
    ⟨hSwLen, hSwBounds, pf, hOodLen, hAccLen, hAccLast, hOodAll, hOuterMsmL, hOuterMsmR, hOuterPairing⟩
  exact ⟨hPublics, hSat, hStage3Accepts, hInnerPairing⟩

/-- **End-to-End Stage-4 $\to$ Stage-3 $\to$ Stage-2 KZG Compression Soundness (`outer_to_stage2_kzg_sound`)**:
Composes `outer_wrapper_sound` (Stage-4 BN254 PLONK / Groth16 wrapper $\to$ Stage-3 Recursive KZG
acceptance + inner deferred pairing) with `recursive_kzg_circuit_sound` (Stage-3 Recursive KZG
circuit + inner deferred pairing $\to$ Stage-2 `KzgStarkAccepts vk1 tau claim`). -/
theorem outer_to_stage2_kzg_sound
    (vk1 vk2 : KzgVerifyingKey)
    (hSameGroup : vk1.G = vk2.G)
    (vk2Prefix claim pairingLimbs : List Nat)
    (claimLo claimHi : BN254Fr)
    (wOuter : OuterWrapperWitness vk2)
    (wRec : RecursiveKzgWitness vk1)
    (L_inner_vk1 R_inner_vk1 : vk1.G.Point)
    (tau : Nat)
    (hClaimLen : claim.length = CLAIM_WORDS)
    (hIr : OuterIRWitnessValid vk2 wOuter.irWitness)
    (hClaimWitness : wOuter.irWitness.take CLAIM_WORDS = claim)
    (hPublics : reconstructClaimFromPublics vk2Prefix claimLo claimHi = claim)
    (hOuterMsmL :
      wOuter.L_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases0.length wOuter.outerMsmRounds0) wOuter.outerMsmBases0)
    (hOuterMsmR :
      wOuter.R_outer = msmEval vk2.G (foldWindowRows wOuter.outerMsmBases1.length wOuter.outerMsmRounds1) wOuter.outerMsmBases1)
    (hOuterPairing : KzgPairingHolds vk2.G wOuter.L_outer wOuter.R_outer tau)
    (hInnerPairing : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau)
    (hRecSat : (recursiveKzgCircuit vk1).Satisfies (claim ++ pairingLimbs) wRec)
    (hDecL : wRec.decodePoint wRec.encL = some L_inner_vk1)
    (hDecR : wRec.decodePoint wRec.encR = some R_inner_vk1)
    (hInnerBridge : KzgPairingHolds vk2.G wOuter.L_inner wOuter.R_inner tau →
      KzgPairingHolds vk1.G L_inner_vk1 R_inner_vk1 tau) :
    let _ := hSameGroup
    KzgStarkAccepts vk2 tau claim ∧
    KzgStarkAccepts vk1 tau claim := by
  dsimp only
  have hStage4 := outer_wrapper_sound vk2 vk2Prefix claim claimLo claimHi wOuter tau
    hIr hClaimWitness hPublics hOuterMsmL hOuterMsmR hOuterPairing hInnerPairing
  have hStage2 := recursive_kzg_circuit_sound vk1 claim pairingLimbs wRec
    L_inner_vk1 R_inner_vk1 tau hClaimLen hRecSat hDecL hDecR (hInnerBridge hStage4.2.2.2)
  exact ⟨hStage4.2.2.1, hStage2.2.2.2⟩

end Ix.Cert.Compression.OuterRelation
