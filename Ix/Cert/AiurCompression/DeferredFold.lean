import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.Bls12381.OuterRelation

/-! # Multi-Stage Deferred Pairing Fold Soundness & Canonical Affine `u80` Output Codecs

Formalizes the algebraic soundness of the deferred KZG pairing accumulator folded across the
Lean-compiled Aiur compression chain (`CompressNarrowFixed` → `CompressFinalNarrow` → outer
pure-Rust `aiur_backend::plonk::native` PLONK `ix-aiur-scs-v1` + two-pair `PairingCheck` in
`stages/terminal.rs`), over BN254, together with standalone BLS12-381 subgroup-enforced
deferred-fold arithmetic and affine codec lemmas:

1. **BN254 Deferred Pairing Accumulation (`bn254_l3_deferred_fold_sound`,
   `bn254_kstage_deferred_fold_sound`):**
   - Stage 1 (`CompressNarrowFixed::step_v1`): folds `acc₁ = cur₁ + w₁ · (0, 0)` from infinity,
     so `deferredPairVal acc₁ = deferredPairVal cur₁`.
   - Stage 2 (`CompressFinalNarrow::verify_accumulator_v1`): folds `acc₂ = cur₂ + w₂ · acc₁`.
   - Proves that if `deferredPairVal acc₂ = 1`, then EITHER both `cur₁` (`CompressGL`) and
     `cur₂` (`CompressNarrowFixed`) pass their pairing checks individually (`= 1`), OR `w₂`
     hits the algebraic bad fold-challenge set of size `≤ 1` out of `bn254FrModulus` (`≤ 2^{-253}`).
   - Proves the inductive `k`-stage generalization covering arbitrary multi-stage chains.
2. **BLS12-381 Subgroup-Enforced Deferred Pairing Arithmetic
   (`bls12381_l3_deferred_fold_sound`, `bls12381_kstage_deferred_fold_sound`):**
   - Standalone algebraic/arithmetic lemmas enforcing `InPrimeSubgroupG1` on every deferred
     accumulator point (rejecting small-order cofactor torsion points).
3. **Canonical Affine `u80` Terminal Output Word Codecs & Decoders (`bn254AffineU80_injective`,
   `decodeBn254AffineU80PointWords`, `Bn254AffineCodec`, `Bn254PackedAccCodec`,
   `bls12381AffineU80_injective`):**
   - Exact mathematical model and total field-word decoder of `CompressFinalNarrow::verify_accumulator_v1`'s
     18-word BN254 output (`2 × (4 × u80/u14 + infinity)`, matching the `affine-u80-v1` layout in
     `crates/proof-compression/src/aiur_backend/plonk/scs.rs` and `stages/terminal.rs`)
     and the 4-word packed accumulator (`KzgAccumulator::pack`), plus the 22-word BLS12-381
     `5 × u80/u61` coordinate injectivity lemma.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.OuterRelation

/-! ## 1. BN254 Deferred Pairing Accumulation Soundness -/

/-- Pairing evaluation of a deferred KZG pair `(a, b) ∈ G1 × G1` against anchors `(g₂, τ·g₂)`:
`e(a, g₂) · e(b, τ·g₂) ∈ GT`. -/
def bn254DeferredVal (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (pair : bp.G1 × bp.G1) : bp.GT :=
  bp.e pair.1 anchors.1 * bp.e pair.2 anchors.2

/-- Single deferred accumulator fold step `acc = cur + w · prev`, matching
`CompressBNPacked::fold` (`MultiStark/MultiStark/BN/CompressBNPacked.lean:71-78`). -/
def bn254FoldStep (bp : BilinearPairing) (w : BN254Fr)
    (prev cur : bp.G1 × bp.G1) : bp.G1 × bp.G1 :=
  (cur.1 + bp.smul w prev.1, cur.2 + bp.smul w prev.2)

/-- Fold an arbitrary list of `(weight, curPair)` stages starting from `(0, 0)`. -/
def bn254FoldChain (bp : BilinearPairing) :
    List (BN254Fr × (bp.G1 × bp.G1)) → bp.G1 × bp.G1
  | [] => (0, 0)
  | (w, cur) :: rest => bn254FoldStep bp w (bn254FoldChain bp rest) cur

theorem bn254_e_zero (bp : BilinearPairing) (H : bp.G2) : bp.e 0 H = 1 := by
  have h := bp.e_add 0 0 H
  rw [zero_add] at h
  have h1 : bp.e 0 H * 1 = bp.e 0 H * bp.e 0 H := by simpa using h
  exact (mul_left_cancel h1).symm

theorem bn254DeferredVal_zero (bp : BilinearPairing) (anchors : bp.G2 × bp.G2) :
    bn254DeferredVal bp anchors (0, 0) = 1 := by
  simp [bn254DeferredVal, bn254_e_zero]

theorem bn254DeferredVal_foldStep (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w : BN254Fr) (prev cur : bp.G1 × bp.G1) :
    bn254DeferredVal bp anchors (bn254FoldStep bp w prev cur) =
      bn254DeferredVal bp anchors cur * (bn254DeferredVal bp anchors prev) ^ w.val := by
  unfold bn254DeferredVal bn254FoldStep
  rw [bp.e_add, bp.e_add, bp.e_smul, bp.e_smul, mul_pow]
  ac_rfl

/-- **Single-Step BN254 Fold Soundness (`bn254_foldStep_sound`):**
If `cur + w · prev` passes the BN254 pairing check (`= 1`), then EITHER both `cur` and `prev`
pass individually (`= 1`), OR `w` actually passes AND belongs to the bad challenge set of size
`≤ 1` out of `bn254FrModulus` (`≤ 2^{-253}`). -/
theorem bn254_foldStep_sound (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w : BN254Fr) (prev cur : bp.G1 × bp.G1)
    (hAcc : bn254DeferredVal bp anchors (bn254FoldStep bp w prev cur) = 1) :
    (bn254DeferredVal bp anchors cur = 1 ∧ bn254DeferredVal bp anchors prev = 1) ∨
      (bn254DeferredVal bp anchors (bn254FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors (bn254FoldStep bp w' prev cur) = 1).card ≤ 1) := by
  by_cases hboth : bn254DeferredVal bp anchors cur = 1 ∧ bn254DeferredVal bp anchors prev = 1
  · exact Or.inl hboth
  · right
    refine ⟨hAcc, ?_⟩
    have hfilt :
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors (bn254FoldStep bp w' prev cur) = 1) =
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors cur * (bn254DeferredVal bp anchors prev) ^ w'.val = 1) := by
      ext w'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bn254DeferredVal_foldStep]
    rw [hfilt]
    exact folded_pairing_bad_card bp.gt_pow_order hboth

/-- **L3 Two-Stage Deferred Pairing Fold Soundness (`bn254_l3_deferred_fold_sound`):**
Models the exact L3 Aiur compression fold chain:
- Stage 1 (`CompressNarrowFixed::step_v1`): `acc₁ = fold(w₁, (0, 0), cur₁)` (verifying CompressGL),
- Stage 2 (`CompressFinalNarrow::verify_accumulator_v1`): `acc₂ = fold(w₂, acc₁, cur₂)` (verifying NarrowFixed).
If the terminal pairing check `bn254DeferredVal bp anchors acc₂ = 1` holds, then EITHER BOTH
`CompressGL`'s pairing check `cur₁` AND `CompressNarrowFixed`'s pairing check `cur₂` hold
individually (`= 1`), OR the actual challenge `w₂` satisfied the folded check AND landed in
the bad fold-challenge set of size `≤ 1` out of `bn254FrModulus` (`≤ 2^{-253}`). -/
theorem bn254_l3_deferred_fold_sound (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w₁ w₂ : BN254Fr) (cur₁ cur₂ : bp.G1 × bp.G1)
    (hTerm : bn254DeferredVal bp anchors
      (bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1) :
    (bn254DeferredVal bp anchors cur₁ = 1 ∧ bn254DeferredVal bp anchors cur₂ = 1) ∨
      (bn254DeferredVal bp anchors
        (bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors
            (bn254FoldStep bp w' (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1).card ≤ 1) := by
  have hacc1 : bn254DeferredVal bp anchors (bn254FoldStep bp w₁ (0, 0) cur₁) =
      bn254DeferredVal bp anchors cur₁ := by
    rw [bn254DeferredVal_foldStep, bn254DeferredVal_zero, one_pow, mul_one]
  rcases bn254_foldStep_sound bp anchors w₂ (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂ hTerm with
    ⟨h2, h1⟩ | hbad
  · rw [hacc1] at h1
    exact Or.inl ⟨h1, h2⟩
  · exact Or.inr hbad

/-- Honest preservation helper: if every stage in `stages` passes individually, the folded chain
passes too. -/
theorem bn254DeferredVal_foldChain_one (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (stages : List (BN254Fr × (bp.G1 × bp.G1)))
    (hall : ∀ s ∈ stages, bn254DeferredVal bp anchors s.2 = 1) :
    bn254DeferredVal bp anchors (bn254FoldChain bp stages) = 1 := by
  induction stages with
  | nil => exact bn254DeferredVal_zero bp anchors
  | cons hd tl ih =>
    rcases hd with ⟨w, cur⟩
    simp only [bn254FoldChain, bn254DeferredVal_foldStep]
    rw [hall (w, cur) List.mem_cons_self,
      ih fun s hs => hall s (List.mem_cons_of_mem _ hs), one_pow, mul_one]

/-- **Inductive `k`-Stage Deferred Fold Soundness (`bn254_kstage_deferred_fold_sound`):**
For any `k`-stage fold chain (covering L3, L4, L5 manifests uniformly), if the final
accumulator passes the BN254 pairing check, then EITHER every stage's deferred pairing check
holds individually (`= 1`), OR an actual stage `i : Fin stages.length` had its concrete
challenge `w = stages[i].1` satisfy the folded pairing check while falling into a bad set of
cardinality `≤ 1` out of `bn254FrModulus`. -/
theorem bn254_kstage_deferred_fold_sound (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (stages : List (BN254Fr × (bp.G1 × bp.G1)))
    (hFinal : bn254DeferredVal bp anchors (bn254FoldChain bp stages) = 1) :
    (∀ s ∈ stages, bn254DeferredVal bp anchors s.2 = 1) ∨
      (∃ i : Fin stages.length,
        let w := (stages[i.val]'i.isLt).1
        let cur := (stages[i.val]'i.isLt).2
        let prev := bn254FoldChain bp (stages.drop (i.val + 1))
        bn254DeferredVal bp anchors (bn254FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors (bn254FoldStep bp w' prev cur) = 1).card ≤ 1) := by
  induction stages with
  | nil =>
    exact Or.inl fun _ h => absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨w, cur⟩ := hd
    simp only [bn254FoldChain] at hFinal
    rcases bn254_foldStep_sound bp anchors w (bn254FoldChain bp tl) cur hFinal with
      ⟨hcur, hprev⟩ | hbad
    · rcases ih hprev with hall | ⟨j, hbadPrev⟩
      · exact Or.inl fun s hs => by
          rcases List.mem_cons.mp hs with rfl | htl
          · exact hcur
          · exact hall s htl
      · exact Or.inr ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, hbadPrev⟩
    · exact Or.inr ⟨⟨0, Nat.zero_lt_succ _⟩, hbad⟩

/-- **Non-Vacuity of `bn254_kstage_deferred_fold_sound`:**
On any list of honest stages (`∀ s ∈ stages, bn254DeferredVal bp anchors s.2 = 1`), the bad-event
escape disjunct is provably FALSE for every `i : Fin stages.length`. -/
theorem bn254_kstage_deferred_fold_nonvacuous (bp : BilinearPairing) (anchors : bp.G2 × bp.G2)
    (stages : List (BN254Fr × (bp.G1 × bp.G1)))
    (hall : ∀ s ∈ stages, bn254DeferredVal bp anchors s.2 = 1) :
    ¬ ∃ i : Fin stages.length,
        let w := (stages[i.val]'i.isLt).1
        let cur := (stages[i.val]'i.isLt).2
        let prev := bn254FoldChain bp (stages.drop (i.val + 1))
        bn254DeferredVal bp anchors (bn254FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp anchors (bn254FoldStep bp w' prev cur) = 1).card ≤ 1 := by
  rintro ⟨i, _, hcard⟩
  have hcur : bn254DeferredVal bp anchors (stages[i.val]'i.isLt).2 = 1 :=
    hall _ (List.getElem_mem i.isLt)
  have hprev : bn254DeferredVal bp anchors (bn254FoldChain bp (stages.drop (i.val + 1))) = 1 :=
    bn254DeferredVal_foldChain_one bp anchors _ fun s hs => hall s (List.mem_of_mem_drop hs)
  have hmem : ∀ w' : BN254Fr, w' ∈ Finset.univ.filter fun w' : BN254Fr =>
      bn254DeferredVal bp anchors
        (bn254FoldStep bp w' (bn254FoldChain bp (stages.drop (i.val + 1))) (stages[i.val]'i.isLt).2) = 1 := by
    intro w'
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [bn254DeferredVal_foldStep, hcur, hprev, one_pow, mul_one]⟩
  exact zero_ne_one (Finset.card_le_one.mp hcard 0 (hmem 0) 1 (hmem 1))

/-! ## 2. BLS12-381 Subgroup-Enforced Deferred Pairing Accumulation Soundness -/

/-- Pairing evaluation of a deferred BLS12-381 KZG pair `(a, b) ∈ G1 × G1` against anchors. -/
def bls12381DeferredVal (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (pair : bp.G1 × bp.G1) : bp.GT :=
  bp.e pair.1 anchors.1 * bp.e pair.2 anchors.2

/-- Both points of a deferred BLS12-381 pair lie in the prime-order subgroup `G1`. -/
def BlsPairInSubgroup (bp : Bls12381BilinearPairing) (pair : bp.G1 × bp.G1) : Prop :=
  bp.InPrimeSubgroupG1 pair.1 ∧ bp.InPrimeSubgroupG1 pair.2

/-- Single deferred accumulator fold step over BLS12-381. -/
def bls12381FoldStep (bp : Bls12381BilinearPairing) (w : BLS12381Fr)
    (prev cur : bp.G1 × bp.G1) : bp.G1 × bp.G1 :=
  (cur.1 + bp.smul w prev.1, cur.2 + bp.smul w prev.2)

/-- Fold an arbitrary list of BLS12-381 stages starting from `(0, 0)`. -/
def bls12381FoldChain (bp : Bls12381BilinearPairing) :
    List (BLS12381Fr × (bp.G1 × bp.G1)) → bp.G1 × bp.G1
  | [] => (0, 0)
  | (w, cur) :: rest => bls12381FoldStep bp w (bls12381FoldChain bp rest) cur

theorem blsPairInSubgroup_zero (bp : Bls12381BilinearPairing) :
    BlsPairInSubgroup bp (0, 0) :=
  ⟨bp.inSubgroup_zero, bp.inSubgroup_zero⟩

theorem blsPairInSubgroup_foldStep (bp : Bls12381BilinearPairing) (w : BLS12381Fr)
    {prev cur : bp.G1 × bp.G1}
    (hp : BlsPairInSubgroup bp prev) (hc : BlsPairInSubgroup bp cur) :
    BlsPairInSubgroup bp (bls12381FoldStep bp w prev cur) :=
  ⟨bp.inSubgroup_add hc.1 (bp.inSubgroup_smul w hp.1),
   bp.inSubgroup_add hc.2 (bp.inSubgroup_smul w hp.2)⟩

theorem bls12381_e_zero (bp : Bls12381BilinearPairing) (H : bp.G2) : bp.e 0 H = 1 := by
  have h := bp.e_add H bp.inSubgroup_zero bp.inSubgroup_zero
  rw [zero_add] at h
  have h1 : bp.e 0 H * 1 = bp.e 0 H * bp.e 0 H := by simpa using h
  exact (mul_left_cancel h1).symm

theorem bls12381DeferredVal_zero (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2) :
    bls12381DeferredVal bp anchors (0, 0) = 1 := by
  simp [bls12381DeferredVal, bls12381_e_zero]

theorem bls12381DeferredVal_foldStep (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w : BLS12381Fr) {prev cur : bp.G1 × bp.G1}
    (hp : BlsPairInSubgroup bp prev) (hc : BlsPairInSubgroup bp cur) :
    bls12381DeferredVal bp anchors (bls12381FoldStep bp w prev cur) =
      bls12381DeferredVal bp anchors cur * (bls12381DeferredVal bp anchors prev) ^ w.val := by
  unfold bls12381DeferredVal bls12381FoldStep
  rw [bp.e_add anchors.1 hc.1 (bp.inSubgroup_smul w hp.1),
    bp.e_add anchors.2 hc.2 (bp.inSubgroup_smul w hp.2),
    bp.e_smul w anchors.1 hp.1, bp.e_smul w anchors.2 hp.2, mul_pow]
  ac_rfl

/-- **Single-Step BLS12-381 Subgroup-Enforced Fold Soundness (`bls12381_foldStep_sound`):**
When both `prev` and `cur` satisfy `BlsPairInSubgroup bp` and `cur + w · prev` passes the
pairing check (`= 1`), then `cur + w · prev` remains in the prime-order subgroup AND EITHER
both `cur` and `prev` pass individually OR `w` actually passes AND belongs to the bad challenge
set of size `≤ 1` out of `bls12381FrModulus` (`≤ 2^{-254}`). -/
theorem bls12381_foldStep_sound (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w : BLS12381Fr) {prev cur : bp.G1 × bp.G1}
    (hp : BlsPairInSubgroup bp prev) (hc : BlsPairInSubgroup bp cur)
    (hAcc : bls12381DeferredVal bp anchors (bls12381FoldStep bp w prev cur) = 1) :
    BlsPairInSubgroup bp (bls12381FoldStep bp w prev cur) ∧
    ((bls12381DeferredVal bp anchors cur = 1 ∧ bls12381DeferredVal bp anchors prev = 1) ∨
      (bls12381DeferredVal bp anchors (bls12381FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors (bls12381FoldStep bp w' prev cur) = 1).card ≤ 1)) := by
  refine ⟨blsPairInSubgroup_foldStep bp w hp hc, ?_⟩
  by_cases hboth : bls12381DeferredVal bp anchors cur = 1 ∧ bls12381DeferredVal bp anchors prev = 1
  · exact Or.inl hboth
  · right
    refine ⟨hAcc, ?_⟩
    have hfilt :
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors (bls12381FoldStep bp w' prev cur) = 1) =
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors cur * (bls12381DeferredVal bp anchors prev) ^ w'.val = 1) := by
      ext w'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        bls12381DeferredVal_foldStep bp anchors w' hp hc]
    rw [hfilt]
    exact bls12381_folded_pairing_bad_card bp.gt_pow_order hboth

/-- **L3 Two-Stage BLS12-381 Subgroup-Enforced Deferred Fold Soundness
(`bls12381_l3_deferred_fold_sound`):**
When both stage pairs lie in the BLS12-381 prime-order `G1` subgroup and the folded terminal
accumulator passes the pairing check, then the terminal accumulator lies in `G1` AND EITHER
both stage checks hold individually (`= 1`) OR the actual challenge `w₂` satisfied the folded
check AND hit a bad set of cardinality `≤ 1` out of `bls12381FrModulus` (`≤ 2^{-254}`). -/
theorem bls12381_l3_deferred_fold_sound (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (w₁ w₂ : BLS12381Fr) {cur₁ cur₂ : bp.G1 × bp.G1}
    (hc₁ : BlsPairInSubgroup bp cur₁) (hc₂ : BlsPairInSubgroup bp cur₂)
    (hTerm : bls12381DeferredVal bp anchors
      (bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1) :
    BlsPairInSubgroup bp (bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) ∧
    ((bls12381DeferredVal bp anchors cur₁ = 1 ∧ bls12381DeferredVal bp anchors cur₂ = 1) ∨
      (bls12381DeferredVal bp anchors
        (bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors
            (bls12381FoldStep bp w' (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1).card ≤ 1)) := by
  have hsub1 : BlsPairInSubgroup bp (bls12381FoldStep bp w₁ (0, 0) cur₁) :=
    blsPairInSubgroup_foldStep bp w₁ (blsPairInSubgroup_zero bp) hc₁
  have hacc1 : bls12381DeferredVal bp anchors (bls12381FoldStep bp w₁ (0, 0) cur₁) =
      bls12381DeferredVal bp anchors cur₁ := by
    rw [bls12381DeferredVal_foldStep bp anchors w₁ (blsPairInSubgroup_zero bp) hc₁,
      bls12381DeferredVal_zero, one_pow, mul_one]
  obtain ⟨hsub2, hres⟩ := bls12381_foldStep_sound bp anchors w₂ hsub1 hc₂ hTerm
  refine ⟨hsub2, ?_⟩
  rcases hres with ⟨h2, h1⟩ | hbad
  · rw [hacc1] at h1
    exact Or.inl ⟨h1, h2⟩
  · exact Or.inr hbad

/-- Subgroup preservation along an arbitrary BLS12-381 fold chain. -/
theorem blsPairInSubgroup_foldChain (bp : Bls12381BilinearPairing)
    (stages : List (BLS12381Fr × (bp.G1 × bp.G1)))
    (hSub : ∀ s ∈ stages, BlsPairInSubgroup bp s.2) :
    BlsPairInSubgroup bp (bls12381FoldChain bp stages) := by
  induction stages with
  | nil => exact blsPairInSubgroup_zero bp
  | cons hd tl ih =>
    exact blsPairInSubgroup_foldStep bp hd.1
      (ih fun s hs => hSub s (List.mem_cons_of_mem _ hs))
      (hSub hd List.mem_cons_self)

/-- Honest preservation helper: if every BLS12-381 stage lies in `G1` and passes individually,
the folded chain passes too. -/
theorem bls12381DeferredVal_foldChain_one (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (stages : List (BLS12381Fr × (bp.G1 × bp.G1)))
    (hSub : ∀ s ∈ stages, BlsPairInSubgroup bp s.2)
    (hall : ∀ s ∈ stages, bls12381DeferredVal bp anchors s.2 = 1) :
    bls12381DeferredVal bp anchors (bls12381FoldChain bp stages) = 1 := by
  induction stages with
  | nil => exact bls12381DeferredVal_zero bp anchors
  | cons hd tl ih =>
    rcases hd with ⟨w, cur⟩
    have htlSub : ∀ s ∈ tl, BlsPairInSubgroup bp s.2 :=
      fun s hs => hSub s (List.mem_cons_of_mem _ hs)
    have hprevSub : BlsPairInSubgroup bp (bls12381FoldChain bp tl) :=
      blsPairInSubgroup_foldChain bp tl htlSub
    have hcurSub : BlsPairInSubgroup bp cur := hSub (w, cur) List.mem_cons_self
    simp only [bls12381FoldChain]
    rw [bls12381DeferredVal_foldStep bp anchors w hprevSub hcurSub,
      hall (w, cur) List.mem_cons_self,
      ih htlSub fun s hs => hall s (List.mem_cons_of_mem _ hs), one_pow, mul_one]

/-- **Inductive `k`-Stage BLS12-381 Subgroup-Enforced Fold Soundness:**
Generalizes `bls12381_l3_deferred_fold_sound` to arbitrary `k`-stage chains, binding the bad
event strictly to an actual stage `i : Fin stages.length`. -/
theorem bls12381_kstage_deferred_fold_sound (bp : Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
    (stages : List (BLS12381Fr × (bp.G1 × bp.G1)))
    (hSub : ∀ s ∈ stages, BlsPairInSubgroup bp s.2)
    (hFinal : bls12381DeferredVal bp anchors (bls12381FoldChain bp stages) = 1) :
    BlsPairInSubgroup bp (bls12381FoldChain bp stages) ∧
    ((∀ s ∈ stages, bls12381DeferredVal bp anchors s.2 = 1) ∨
      (∃ i : Fin stages.length,
        let w := (stages[i.val]'i.isLt).1
        let cur := (stages[i.val]'i.isLt).2
        let prev := bls12381FoldChain bp (stages.drop (i.val + 1))
        BlsPairInSubgroup bp prev ∧
        BlsPairInSubgroup bp cur ∧
        bls12381DeferredVal bp anchors (bls12381FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors (bls12381FoldStep bp w' prev cur) = 1).card ≤ 1)) := by
  induction stages with
  | nil =>
    exact ⟨blsPairInSubgroup_zero bp, Or.inl fun _ h => absurd h List.not_mem_nil⟩
  | cons hd tl ih =>
    obtain ⟨w, cur⟩ := hd
    have hcurSub : BlsPairInSubgroup bp cur := hSub (w, cur) List.mem_cons_self
    have htlSub : ∀ s ∈ tl, BlsPairInSubgroup bp s.2 :=
      fun s hs => hSub s (List.mem_cons_of_mem _ hs)
    have hchainSub : BlsPairInSubgroup bp (bls12381FoldChain bp tl) :=
      blsPairInSubgroup_foldChain bp tl htlSub
    simp only [bls12381FoldChain] at hFinal ⊢
    obtain ⟨hsubOut, hstep⟩ := bls12381_foldStep_sound bp anchors w hchainSub hcurSub hFinal
    refine ⟨hsubOut, ?_⟩
    rcases hstep with ⟨hcur, hprev⟩ | hbad
    · rcases (ih htlSub hprev).2 with hall | ⟨j, hbadPrev⟩
      · exact Or.inl fun s hs => by
          rcases List.mem_cons.mp hs with rfl | htl
          · exact hcur
          · exact hall s htl
      · exact Or.inr ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, hbadPrev⟩
    · exact Or.inr ⟨⟨0, Nat.zero_lt_succ _⟩, hchainSub, hcurSub, hbad⟩

/-- **Non-Vacuity of `bls12381_kstage_deferred_fold_sound`:**
On any list of honest prime-subgroup stages (`∀ s ∈ stages, BlsPairInSubgroup bp s.2` and
`bls12381DeferredVal bp anchors s.2 = 1`), the bad-event escape disjunct is provably FALSE
for every `i : Fin stages.length`. -/
theorem bls12381_kstage_deferred_fold_nonvacuous (bp : Bls12381BilinearPairing)
    (anchors : bp.G2 × bp.G2)
    (stages : List (BLS12381Fr × (bp.G1 × bp.G1)))
    (hSub : ∀ s ∈ stages, BlsPairInSubgroup bp s.2)
    (hall : ∀ s ∈ stages, bls12381DeferredVal bp anchors s.2 = 1) :
    ¬ ∃ i : Fin stages.length,
        let w := (stages[i.val]'i.isLt).1
        let cur := (stages[i.val]'i.isLt).2
        let prev := bls12381FoldChain bp (stages.drop (i.val + 1))
        BlsPairInSubgroup bp prev ∧
        BlsPairInSubgroup bp cur ∧
        bls12381DeferredVal bp anchors (bls12381FoldStep bp w prev cur) = 1 ∧
        (Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp anchors (bls12381FoldStep bp w' prev cur) = 1).card ≤ 1 := by
  rintro ⟨i, hprevSub, hcurSub, _, hcard⟩
  have hcur : bls12381DeferredVal bp anchors (stages[i.val]'i.isLt).2 = 1 :=
    hall _ (List.getElem_mem i.isLt)
  have hprev : bls12381DeferredVal bp anchors (bls12381FoldChain bp (stages.drop (i.val + 1))) = 1 :=
    bls12381DeferredVal_foldChain_one bp anchors _
      (fun s hs => hSub s (List.mem_of_mem_drop hs))
      (fun s hs => hall s (List.mem_of_mem_drop hs))
  have hmem : ∀ w' : BLS12381Fr, w' ∈ Finset.univ.filter fun w' : BLS12381Fr =>
      bls12381DeferredVal bp anchors
        (bls12381FoldStep bp w' (bls12381FoldChain bp (stages.drop (i.val + 1))) (stages[i.val]'i.isLt).2) = 1 := by
    intro w'
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by
      rw [bls12381DeferredVal_foldStep bp anchors w' hprevSub hcurSub, hcur, hprev, one_pow, mul_one]⟩
  exact zero_ne_one (Finset.card_le_one.mp hcard 0 (hmem 0) 1 (hmem 1))

/-! ## 3. Canonical Affine `u80` Terminal Output Word Encodings (`affine-u80-v1`, `plonk/scs.rs`) -/

/-- Canonical 4-limb `u80`/`u14` BN254 `Fq` coordinate (`affine-u80-v1` terminal output encoding
in `crates/proof-compression/src/aiur_backend/plonk/scs.rs` and `aiur_backend::plonk::native`). -/
structure Bn254AffineU80Coord where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  h0 : w0 < 2 ^ 80
  h1 : w1 < 2 ^ 80
  h2 : w2 < 2 ^ 80
  h3 : w3 < 2 ^ 14
  hRange : w0 + 2 ^ 80 * w1 + 2 ^ 160 * w2 + 2 ^ 240 * w3 < bn254FqModulus

def Bn254AffineU80Coord.toNat (c : Bn254AffineU80Coord) : Nat :=
  c.w0 + 2 ^ 80 * c.w1 + 2 ^ 160 * c.w2 + 2 ^ 240 * c.w3

theorem Bn254AffineU80Coord.toNat_injective {c₁ c₂ : Bn254AffineU80Coord}
    (h : c₁.toNat = c₂.toNat) :
    c₁.w0 = c₂.w0 ∧ c₁.w1 = c₂.w1 ∧ c₁.w2 = c₂.w2 ∧ c₁.w3 = c₂.w3 := by
  unfold Bn254AffineU80Coord.toNat at h
  have := c₁.h0; have := c₁.h1; have := c₁.h2; have := c₁.h3
  have := c₂.h0; have := c₂.h1; have := c₂.h2; have := c₂.h3
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Canonical 9-word BN254 affine `G1` point output (`x` limbs `0..3`, `y` limbs `4..7`,
boolean `infinity` word `8`), matching the `affine-u80-v1` layout in
`crates/proof-compression/src/aiur_backend/plonk/scs.rs` and `stages/terminal.rs`. -/
structure Bn254AffineU80Point where
  x : Bn254AffineU80Coord
  y : Bn254AffineU80Coord
  infinity : Bool
  inf_iff_zero : infinity = true ↔ x.toNat = 0 ∧ y.toNat = 0

/-- Exact 9-word representation of a BN254 affine output point. -/
def Bn254AffineU80Point.words (p : Bn254AffineU80Point) : List Nat :=
  [p.x.w0, p.x.w1, p.x.w2, p.x.w3, p.y.w0, p.y.w1, p.y.w2, p.y.w3, if p.infinity then 1 else 0]

/-- Exact injectivity of the 9-word BN254 `affine-u80-v1` point encoding:
equal decoded `(x, y)` coordinates uniquely fix all 9 output words (including `infinity`). -/
theorem bn254AffineU80_injective {p₁ p₂ : Bn254AffineU80Point}
    (hx : p₁.x.toNat = p₂.x.toNat) (hy : p₁.y.toNat = p₂.y.toNat) :
    p₁.words = p₂.words := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := Bn254AffineU80Coord.toNat_injective hx
  obtain ⟨hy0, hy1, hy2, hy3⟩ := Bn254AffineU80Coord.toNat_injective hy
  have hinf : p₁.infinity = p₂.infinity := by
    cases h1 : p₁.infinity <;> cases h2 : p₂.infinity
    · rfl
    · have hz := p₂.inf_iff_zero.mp h2
      rw [← hx, ← hy] at hz
      have := p₁.inf_iff_zero.mpr hz
      rw [h1] at this; exact absurd this (by decide)
    · have hz := p₁.inf_iff_zero.mp h1
      rw [hx, hy] at hz
      have := p₂.inf_iff_zero.mpr hz
      rw [h2] at this; exact absurd this (by decide)
    · rfl
  simp [Bn254AffineU80Point.words, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, hinf]

/-- Canonical 5-limb `u80`/`u61` BLS12-381 `Fq` coordinate (381 bits `< 4 * 80 + 61 = 381`,
matching `Ix.Cert.Compression.Bls12381.Field`'s `5 × 80`-bit representation). -/
structure Bls12381AffineU80Coord where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  w4 : Nat
  h0 : w0 < 2 ^ 80
  h1 : w1 < 2 ^ 80
  h2 : w2 < 2 ^ 80
  h3 : w3 < 2 ^ 80
  h4 : w4 < 2 ^ 61
  hRange : w0 + 2 ^ 80 * w1 + 2 ^ 160 * w2 + 2 ^ 240 * w3 + 2 ^ 320 * w4 < bls12381FqModulus

def Bls12381AffineU80Coord.toNat (c : Bls12381AffineU80Coord) : Nat :=
  c.w0 + 2 ^ 80 * c.w1 + 2 ^ 160 * c.w2 + 2 ^ 240 * c.w3 + 2 ^ 320 * c.w4

theorem Bls12381AffineU80Coord.toNat_injective {c₁ c₂ : Bls12381AffineU80Coord}
    (h : c₁.toNat = c₂.toNat) :
    c₁.w0 = c₂.w0 ∧ c₁.w1 = c₂.w1 ∧ c₁.w2 = c₂.w2 ∧ c₁.w3 = c₂.w3 ∧ c₁.w4 = c₂.w4 := by
  unfold Bls12381AffineU80Coord.toNat at h
  have := c₁.h0; have := c₁.h1; have := c₁.h2; have := c₁.h3; have := c₁.h4
  have := c₂.h0; have := c₂.h1; have := c₂.h2; have := c₂.h3; have := c₂.h4
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Canonical 11-word BLS12-381 affine `G1` point output (`5 + 5 + 1` words). -/
structure Bls12381AffineU80Point where
  x : Bls12381AffineU80Coord
  y : Bls12381AffineU80Coord
  infinity : Bool
  inf_iff_zero : infinity = true ↔ x.toNat = 0 ∧ y.toNat = 0

def Bls12381AffineU80Point.words (p : Bls12381AffineU80Point) : List Nat :=
  [p.x.w0, p.x.w1, p.x.w2, p.x.w3, p.x.w4,
   p.y.w0, p.y.w1, p.y.w2, p.y.w3, p.y.w4, if p.infinity then 1 else 0]

/-- Exact injectivity of the 11-word BLS12-381 `5 × 80`-bit affine point encoding. -/
theorem bls12381AffineU80_injective {p₁ p₂ : Bls12381AffineU80Point}
    (hx : p₁.x.toNat = p₂.x.toNat) (hy : p₁.y.toNat = p₂.y.toNat) :
    p₁.words = p₂.words := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := Bls12381AffineU80Coord.toNat_injective hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := Bls12381AffineU80Coord.toNat_injective hy
  have hinf : p₁.infinity = p₂.infinity := by
    cases h1 : p₁.infinity <;> cases h2 : p₂.infinity
    · rfl
    · have hz := p₂.inf_iff_zero.mp h2
      rw [← hx, ← hy] at hz
      have := p₁.inf_iff_zero.mpr hz
      rw [h1] at this; exact absurd this (by decide)
    · have hz := p₁.inf_iff_zero.mp h1
      rw [hx, hy] at hz
      have := p₂.inf_iff_zero.mpr hz
      rw [h2] at this; exact absurd this (by decide)
    · rfl
  simp [Bls12381AffineU80Point.words, hx0, hx1, hx2, hx3, hx4, hy0, hy1, hy2, hy3, hy4, hinf]

/-! ## 4. Total `BN254Fr` Field-Word Decoders for `affine-u80-v1` (18 words) & Packed Accumulators (4 words) -/

/-- The 9 `BN254Fr` field words corresponding to a canonical `Bn254AffineU80Point`. -/
def Bn254AffineU80Point.fieldWords (p : Bn254AffineU80Point) : List BN254Fr :=
  p.words.map fun n => (n : BN254Fr)

/-- Canonical `0` coordinate in `4 × u80/u14` representation. -/
def bn254AffineZeroCoord : Bn254AffineU80Coord where
  w0 := 0
  w1 := 0
  w2 := 0
  w3 := 0
  h0 := by decide
  h1 := by decide
  h2 := by decide
  h3 := by decide
  hRange := by decide

/-- Canonical 9-word infinity point `(0, 0, true)` (`[0,0,0,0, 0,0,0,0, 1]`). -/
def bn254AffineInfinityPoint : Bn254AffineU80Point where
  x := bn254AffineZeroCoord
  y := bn254AffineZeroCoord
  infinity := true
  inf_iff_zero := by simp [Bn254AffineU80Coord.toNat, bn254AffineZeroCoord]

/-- Canonical 9-word `BN254Fr` encoding of the point at infinity. -/
def bn254AffineInfinityWords : List BN254Fr :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Canonical 18-word `BN254Fr` encoding of the zero deferred pair `(0, 0)`. -/
def bn254AffineZeroPairWords : List BN254Fr :=
  bn254AffineInfinityWords ++ bn254AffineInfinityWords

/-- Decode four `BN254Fr` limbs into a canonical `4 × u80/u14` BN254 `Fq` coordinate,
matching the `affine-u80-v1` coordinate representation in
`crates/proof-compression/src/aiur_backend/fq.rs` and `stages/terminal.rs`. -/
def decodeBn254AffineU80Coord (f0 f1 f2 f3 : BN254Fr) : Option Bn254AffineU80Coord :=
  if h0 : f0.val < 2 ^ 80 then
    if h1 : f1.val < 2 ^ 80 then
      if h2 : f2.val < 2 ^ 80 then
        if h3 : f3.val < 2 ^ 14 then
          if hR : f0.val + 2 ^ 80 * f1.val + 2 ^ 160 * f2.val + 2 ^ 240 * f3.val < bn254FqModulus then
            some ⟨f0.val, f1.val, f2.val, f3.val, h0, h1, h2, h3, hR⟩
          else none
        else none
      else none
    else none
  else none

/-- Decode nine `BN254Fr` output words into a canonical `Bn254AffineU80Point`, matching
`g1::decode_affine_words` / `check_bn254_native_outputs` (`stages/terminal.rs`):
- `x` limbs `0..3` and `y` limbs `4..7` are canonical `4 × u80/u14` `Fq` coordinates;
- word `8` is boolean (`0` or `1`);
- `infinity = 1 ↔ x = 0 ∧ y = 0`. -/
def decodeBn254AffineU80PointWords : List BN254Fr → Option Bn254AffineU80Point
  | [x0, x1, x2, x3, y0, y1, y2, y3, inf] =>
    match decodeBn254AffineU80Coord x0 x1 x2 x3, decodeBn254AffineU80Coord y0 y1 y2 y3 with
    | some xc, some yc =>
      if _hInf : inf.val = 1 then
        if hZero : xc.toNat = 0 ∧ yc.toNat = 0 then
          some ⟨xc, yc, true, ⟨fun _ => hZero, fun _ => rfl⟩⟩
        else none
      else if _hFin : inf.val = 0 then
        if hNz : ¬ (xc.toNat = 0 ∧ yc.toNat = 0) then
          some ⟨xc, yc, false, ⟨fun h => absurd h (by decide), fun hz => absurd hz hNz⟩⟩
        else none
      else none
    | _, _ => none
  | _ => none

theorem decodeBn254AffineU80Coord_zero :
    decodeBn254AffineU80Coord 0 0 0 0 = some bn254AffineZeroCoord := by
  have h0 : (0 : BN254Fr).val = 0 := ZMod.val_zero
  simp [decodeBn254AffineU80Coord, bn254AffineZeroCoord, h0]

theorem decodeBn254AffineU80PointWords_infinity :
    decodeBn254AffineU80PointWords bn254AffineInfinityWords = some bn254AffineInfinityPoint := by
  have h1 : (1 : BN254Fr).val = 1 := ZMod.val_one bn254FrModulus
  simp [decodeBn254AffineU80PointWords, bn254AffineInfinityWords, bn254AffineInfinityPoint,
    decodeBn254AffineU80Coord_zero, Bn254AffineU80Coord.toNat, bn254AffineZeroCoord, h1]

theorem decodeBn254AffineU80Coord_eq_some {f0 f1 f2 f3 : BN254Fr} {c : Bn254AffineU80Coord}
    (h : decodeBn254AffineU80Coord f0 f1 f2 f3 = some c) :
    (c.w0 : BN254Fr) = f0 ∧ (c.w1 : BN254Fr) = f1 ∧
    (c.w2 : BN254Fr) = f2 ∧ (c.w3 : BN254Fr) = f3 := by
  unfold decodeBn254AffineU80Coord at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨ZMod.natCast_zmod_val f0, ZMod.natCast_zmod_val f1,
    ZMod.natCast_zmod_val f2, ZMod.natCast_zmod_val f3⟩

/-- Every 9-word sequence accepted by `decodeBn254AffineU80PointWords` equals the exact
canonical `fieldWords` of the decoded point (proving strict injectivity on `BN254Fr` words). -/
theorem decodeBn254AffineU80PointWords_roundtrip {ws : List BN254Fr} {p : Bn254AffineU80Point}
    (h : decodeBn254AffineU80PointWords ws = some p) :
    ws = p.fieldWords := by
  match ws with
  | [x0, x1, x2, x3, y0, y1, y2, y3, inf] =>
    unfold decodeBn254AffineU80PointWords at h
    cases hx : decodeBn254AffineU80Coord x0 x1 x2 x3 with
    | none => simp [hx] at h
    | some xc =>
      cases hy : decodeBn254AffineU80Coord y0 y1 y2 y3 with
      | none => simp [hx, hy] at h
      | some yc =>
        simp only [hx, hy] at h
        obtain ⟨hx0, hx1, hx2, hx3⟩ := decodeBn254AffineU80Coord_eq_some hx
        obtain ⟨hy0, hy1, hy2, hy3⟩ := decodeBn254AffineU80Coord_eq_some hy
        split_ifs at h with hInf hZero hFin hNz
        · simp only [Option.some.injEq] at h
          subst h
          have hinfEq : (1 : BN254Fr) = inf := by
            have hcast : ((inf.val : Nat) : BN254Fr) = inf := ZMod.natCast_zmod_val inf
            rw [hInf] at hcast
            simpa using hcast
          simp [Bn254AffineU80Point.fieldWords, Bn254AffineU80Point.words,
            hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, hinfEq]
        · simp only [Option.some.injEq] at h
          subst h
          have hinfEq : (0 : BN254Fr) = inf := by
            have hcast : ((inf.val : Nat) : BN254Fr) = inf := ZMod.natCast_zmod_val inf
            rw [hFin] at hcast
            simpa using hcast
          simp [Bn254AffineU80Point.fieldWords, Bn254AffineU80Point.words,
            hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, hinfEq]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    simp [decodeBn254AffineU80PointWords] at h

theorem decodeBn254AffineU80PointWords_injective {ws₁ ws₂ : List BN254Fr} {p : Bn254AffineU80Point}
    (h₁ : decodeBn254AffineU80PointWords ws₁ = some p)
    (h₂ : decodeBn254AffineU80PointWords ws₂ = some p) :
    ws₁ = ws₂ :=
  (decodeBn254AffineU80PointWords_roundtrip h₁).trans
    (decodeBn254AffineU80PointWords_roundtrip h₂).symm

/-- Constructive rejection of malformed `affine-u80-v1` flags:
1. Any non-boolean infinity word (`inf.val ≠ 0 ∧ inf.val ≠ 1`) is rejected (`none`);
2. Setting `inf = 1` with nonzero `x0` is rejected (`none`);
3. Setting `inf = 0` with all-zero coordinates `(0, 0)` is rejected (`none`). -/
theorem decodeBn254AffineU80PointWords_rejects_bad_flag
    (x0 x1 x2 x3 y0 y1 y2 y3 inf : BN254Fr) :
    (inf.val ≠ 0 → inf.val ≠ 1 →
      decodeBn254AffineU80PointWords [x0, x1, x2, x3, y0, y1, y2, y3, inf] = none) ∧
    (x0 ≠ 0 →
      decodeBn254AffineU80PointWords [x0, x1, x2, x3, y0, y1, y2, y3, 1] = none) ∧
    decodeBn254AffineU80PointWords [0, 0, 0, 0, 0, 0, 0, 0, 0] = none := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0 h1
    simp only [decodeBn254AffineU80PointWords]
    cases hx : decodeBn254AffineU80Coord x0 x1 x2 x3 <;>
      cases hy : decodeBn254AffineU80Coord y0 y1 y2 y3 <;>
      simp [h0, h1]
  · intro hx0
    simp only [decodeBn254AffineU80PointWords]
    cases hx : decodeBn254AffineU80Coord x0 x1 x2 x3 with
    | none => simp
    | some xc =>
      cases hy : decodeBn254AffineU80Coord y0 y1 y2 y3 with
      | none => simp
      | some yc =>
        have h1 : (1 : BN254Fr).val = 1 := ZMod.val_one bn254FrModulus
        have hxc := (decodeBn254AffineU80Coord_eq_some hx).1
        have hnz : xc.toNat ≠ 0 := by
          intro hz
          unfold Bn254AffineU80Coord.toNat at hz
          have hw0 : xc.w0 = 0 := by omega
          rw [hw0, Nat.cast_zero] at hxc
          exact hx0 hxc.symm
        simp [h1, hnz]
  · have h0 : (0 : BN254Fr).val = 0 := ZMod.val_zero
    simp [decodeBn254AffineU80PointWords, decodeBn254AffineU80Coord_zero,
      Bn254AffineU80Coord.toNat, bn254AffineZeroCoord, h0]

/-- Canonical curve-point decoder from a range-checked 9-word `Bn254AffineU80Point` into `bp.G1`
(modeling on-curve `G1` decoding in `crates/proof-compression/src/aiur_backend/g1.rs` and
`check_bn254_native_outputs` in `stages/terminal.rs`). -/
structure Bn254AffineCodec (bp : BilinearPairing) where
  decodePoint : Bn254AffineU80Point → Option bp.G1
  decode_infinity : ∀ p : Bn254AffineU80Point, p.infinity = true → decodePoint p = some 0

/-- Decode the 18 `BN254Fr` terminal output words (`2 × 9` `affine-u80-v1` words) into a
deferred pairing operand pair `(d0, d1) ∈ bp.G1 × bp.G1`. -/
def decodeBn254AffinePairWords {bp : BilinearPairing} (codec : Bn254AffineCodec bp)
    (ws : List BN254Fr) : Option (bp.G1 × bp.G1) :=
  if ws.length = 18 then
    match decodeBn254AffineU80PointWords (ws.take 9),
          decodeBn254AffineU80PointWords (ws.drop 9) with
    | some p0, some p1 =>
      match codec.decodePoint p0, codec.decodePoint p1 with
      | some g0, some g1 => some (g0, g1)
      | _, _ => none
    | _, _ => none
  else none

theorem decodeBn254AffinePairWords_zeroPair {bp : BilinearPairing}
    (codec : Bn254AffineCodec bp) :
    decodeBn254AffinePairWords codec bn254AffineZeroPairWords = some (0, 0) := by
  have hlen : bn254AffineZeroPairWords.length = 18 := rfl
  have htake : bn254AffineZeroPairWords.take 9 = bn254AffineInfinityWords := rfl
  have hdrop : bn254AffineZeroPairWords.drop 9 = bn254AffineInfinityWords := rfl
  simp only [decodeBn254AffinePairWords, hlen, ite_true, htake, hdrop,
    decodeBn254AffineU80PointWords_infinity,
    codec.decode_infinity bn254AffineInfinityPoint rfl]

/-- Canonical decoder for the 4-word packed deferred accumulator (`KzgAccumulator::pack`,
`[Field; 4]` returned by `CompressNarrowFixed::step_v1` and unpacked by
`CompressFinalNarrow::previous`) into `bp.G1 × bp.G1`. -/
structure Bn254PackedAccCodec (bp : BilinearPairing) where
  decodePacked : List BN254Fr → Option (bp.G1 × bp.G1)
  decode_len : ∀ ws pair, decodePacked ws = some pair → ws.length = 4

end Ix.Cert.AiurCompression
