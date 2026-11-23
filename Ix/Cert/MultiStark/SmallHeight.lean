import CertiFriProofs.Theory.PcsRbr.Decode
import CertiFriProofs.Exec.Extract
import Ix.Cert.MultiStark.FieldModel

/-! # Small-Height (`ℓ = 0`, `ℓ = 1`) and Off-Domain Tight Decoding (Protocol `v6`, `Fp^3`)

CertiFRI's `CertiFri.DecodeMargin` loses `2` points to `B.erase z` on both sides
(`D.card + d + 3 ≤ 2 * θ * D.card`), which degenerates to `θ = 1` (`δ = 0`) when a
matrix has height `1` (`ℓ = 0`, LDE domain size `|D| = 4`, degree bound `d = 1`).

In Protocol `v6` Multi-STARK, the OOD opening point `ζ` is sampled uniformly from the cubic
extension `K = Fp[X] / (X^3 - X - 1)` (`|K| = p^3 ≈ 2^192`) and every opening point is either
`ζ` or `ζ · g` with `g ∈ Fp \ {0}`. Whenever `ζ ∉ Fp` (`ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0`, which fails
with probability only `1 / |Fp|^2 ≈ 2^-128`), neither `ζ` nor `ζ · g` belongs to the
base-field coset `D ⊆ Fp ⊆ K`.

This module proves:
1. `DecodeMarginOff`: when `z ∉ D`, no point is erased from `B`, tightening the
   unique-decoding margin to `D.card + d + 1 ≤ 2 * θ * D.card` (`2δ + ρ + 1/|D| ≤ 1`).
2. `decodeOff` & `eval_decodeOff_of_claimsHoldOff`: off-domain extractor and
   extraction theorem for any `z ∉ D`.
3. `not_mem_baseCoset_of_not_base`: `ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0` implies `ζ ∉ D` and `ζ · g ∉ D`
   for every base-field coset `D ⊆ Fp ⊆ K` and `g ≠ 0` in `Fp`.
4. `card_in_baseField` & `prob_in_baseField_eq`: the probability that a uniformly sampled
   `ζ ∈ K` lands in `Fp` (`ζ.c1 = 0 ∧ ζ.c2 = 0`) is exact `1 / Goldilocks.order ^ 2`.
5. `card_zeta_in_domain_or_shift_le` & `prob_zeta_in_domain_or_shift_le`: tight
   `2 * |D| / |K|` (`≈ 2^-169` for `|D| = 2^22` in `Fp^3`).

Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3 Polynomial

section OffDomain

variable {F : Type*} [Field F]

/-- Tight unique-decoding margin when opening points lie outside the evaluation domain `D`:
two subsets `B, B' ⊆ D` of size at least `θ * |D|` share at least `d + 1` points. -/
def DecodeMarginOff (D : Finset F) (d : ℕ) (θ : ℝ) : Prop :=
  (D.card : ℝ) + d + 1 ≤ 2 * θ * D.card

open Classical in
/-- Off-domain polynomial decoder: a polynomial of degree at most `d` agreeing with `f`
on a subset `B ⊆ D` of size at least `θ * |D|`, or `0` if none exists. -/
noncomputable def decodeOff (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) : F[X] :=
  if h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x
  then Classical.choose h else 0

theorem degree_decodeOff_lt (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) :
    (decodeOff D d θ f).degree < (d + 1 : ℕ) := by
  unfold decodeOff
  split
  · next h => exact (Classical.choose_spec h).1
  · rw [degree_zero]; exact WithBot.bot_lt_coe _

theorem decodeOff_eq {D : Finset F} {d : ℕ} {θ : ℝ} (hm : DecodeMarginOff D d θ)
    {f : F → F} {P : F[X]} (hP : P.degree < (d + 1 : ℕ))
    {B : Finset F} (hB : B ⊆ D) (hcard : θ * D.card ≤ B.card) (hf : ∀ x ∈ B, f x = P.eval x) :
    decodeOff D d θ f = P := by
  have h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x := ⟨P, hP, B, hB, hcard, hf⟩
  obtain ⟨hQ, B', hB', hcard', hf'⟩ := Classical.choose_spec h
  rw [decodeOff, dite_eq_left h]
  refine eq_of_agree_of_card hQ hP hB' hB ?_ hf' hf
  have hle : ((D.card + (d + 1) : ℕ) : ℝ) ≤ ((B'.card + B.card : ℕ) : ℝ) := by
    unfold DecodeMarginOff at hm
    push_cast
    linarith
  exact Nat.cast_le.mp hle

open Classical in
theorem decodeOff_congr {f g : F → F} (D : Finset F) (d : ℕ) (θ : ℝ) (h : ∀ x ∈ D, f x = g x) :
    decodeOff D d θ f = decodeOff D d θ g := by
  have hpred : (fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x) =
      fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, g x = P.eval x := by
    funext P
    refine propext (and_congr_right fun _ => exists_congr fun B => and_congr_right fun hB =>
      and_congr_right fun _ => forall₂_congr fun x hx => ?_)
    rw [h x (hB hx)]
  have key : ∀ p q : F[X] → Prop, p = q →
      (if h : ∃ P, p P then Classical.choose h else (0 : F[X])) =
        if h : ∃ P, q P then Classical.choose h else 0 := by
    rintro p q rfl; rfl
  exact key _ _ hpred

/-- **Off-domain extraction:** when `ClaimsHoldOff D d θ claims` holds and a claim's opening
point `z` lies outside `D`, the claimed value equals `(decodeOff D d θ f).eval z` under
the tight margin `DecodeMarginOff D d θ`. -/
theorem eval_decodeOff_of_claimsHoldOff {D : Finset F} {d : ℕ} {θ : ℝ}
    (hm : DecodeMarginOff D d θ) {m : ℕ} {claims : Fin m → Claim F}
    (h : PcsRbr.ClaimsHoldOff D d θ claims) (k : Fin m) (hz : (claims k).z ∉ D) :
    (decodeOff D d θ (claims k).f).eval (claims k).z = (claims k).y ∧
      (decodeOff D d θ (claims k).f).degree < (d + 1 : ℕ) := by
  refine ⟨?_, degree_decodeOff_lt D d θ _⟩
  obtain ⟨B, hBD, hB, hk⟩ := h
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  have hf : ∀ x ∈ B, (claims k).f x = P.eval x := fun x hx =>
    hPB x hx (fun heq => hz (heq ▸ hBD hx))
  rw [decodeOff_eq hm hP hBD hB hf]
  exact hPz

omit [Field F] in
/-- Executable rate inequality implies `DecodeMarginOff` at every height (including `ℓ = 0`!). -/
theorem decodeMarginOff_of_rate {D : Finset F} {d : ℕ} {δ : ℝ}
    (hpos : 0 < D.card)
    (hrate : 2 * δ + (d : ℝ) / D.card + 1 / D.card ≤ 1) :
    DecodeMarginOff D d (1 - δ) := by
  unfold DecodeMarginOff
  have hD : (0 : ℝ) < D.card := Nat.cast_pos.mpr hpos
  have hmul := mul_le_mul_of_nonneg_right hrate (le_of_lt hD)
  field_simp [ne_of_gt hD] at hmul
  linarith

omit [Field F] in
/-- Concrete `logBlowup = 2` check: at `δ = 1/4`, `DecodeMarginOff` holds for EVERY
trace height `2^ℓ` (`ℓ ≥ 0`, i.e., `|D| = 4 * 2^ℓ`, `d = 2^ℓ`), including `ℓ = 0` and `ℓ = 1`! -/
theorem decodeMarginOff_blowup2_all_heights {D : Finset F} {ℓ : ℕ}
    (hcard : D.card = 4 * 2 ^ ℓ) :
    DecodeMarginOff D (2 ^ ℓ) (1 - 1 / 4) := by
  unfold DecodeMarginOff
  rw [hcard]
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  push_cast
  linarith

omit [Field F] in
/-- For a constant polynomial (`d = 0`), `DecodeMarginOff D 0 (1 - δ)` holds up to the full
rate `2 * δ + 1 / |D| ≤ 1`, which at `|D| = 4` (`logBlowup = 2, ℓ = 0`) allows `δ ≤ 3/8`
and even at `|D| = 2` (`logBlowup = 1, ℓ = 0`) allows `δ ≤ 1/4`. -/
theorem decodeMarginOff_const {D : Finset F} {δ : ℝ}
    (hpos : 0 < D.card) (hrate : 2 * δ + 1 / D.card ≤ 1) :
    DecodeMarginOff D 0 (1 - δ) := by
  apply decodeMarginOff_of_rate hpos
  simpa using hrate

/-- If `P : F[X]` has `P.degree < 1`, then `P = C (P.coeff 0)` is constant. -/
theorem eq_C_of_degree_lt_one {P : F[X]} (h : P.degree < (1 : ℕ)) :
    P = C (P.coeff 0) := by
  exact Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ (by exact_mod_cast h))

end OffDomain

section ExtensionOffDomain

/-- An element `ζ : K` with `ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0` is not in the image of `Fp3Model.embedHom`. -/
theorem not_in_baseField_of_not_base {ζ : K} (h : ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0) (x : Fp) :
    ζ ≠ Fp3Model.embedHom x := by
  intro heq
  rcases h with h1 | h2
  · exact h1 (congrArg Fp3Model.c1 heq)
  · exact h2 (congrArg Fp3Model.c2 heq)

/-- Multiplying an off-base-field element `ζ` (`ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0`) by any nonzero base-field
element `g ∈ Fp \ {0}` remains off the base field. -/
theorem mul_base_not_base {ζ : K} (hζ : ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0) {g : Fp} (hg : g ≠ 0) :
    (ζ * Fp3Model.embedHom g).c1 ≠ 0 ∨ (ζ * Fp3Model.embedHom g).c2 ≠ 0 := by
  have hc1 : (ζ * Fp3Model.embedHom g).c1 = ζ.c1 * g := by
    change ζ.c0 * 0 + ζ.c1 * g + ζ.c1 * 0 + ζ.c2 * 0 + ζ.c2 * 0 = ζ.c1 * g
    ring
  have hc2 : (ζ * Fp3Model.embedHom g).c2 = ζ.c2 * g := by
    change ζ.c0 * 0 + ζ.c1 * 0 + ζ.c2 * g + ζ.c2 * 0 = ζ.c2 * g
    ring
  rw [hc1, hc2]
  rcases hζ with h1 | h2
  · exact Or.inl (mul_ne_zero h1 hg)
  · exact Or.inr (mul_ne_zero h2 hg)

/-- If every element of a coset `D ⊆ K` lies in the base field `Fp` (`c1 = 0 ∧ c2 = 0`),
and `ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0`, then neither `ζ` nor `ζ * g` (for `g ∈ Fp \ {0}`) belongs to `D`. -/
theorem not_mem_baseCoset_of_not_base {D : Finset K}
    (hD : ∀ x ∈ D, x.c1 = 0 ∧ x.c2 = 0) {ζ : K} (hζ : ζ.c1 ≠ 0 ∨ ζ.c2 ≠ 0) :
    ζ ∉ D ∧ ∀ g : Fp, g ≠ 0 → ζ * Fp3Model.embedHom g ∉ D := by
  refine ⟨fun hmem => ?_, fun g hg hmem => ?_⟩
  · have h0 := hD ζ hmem
    rcases hζ with h1 | h2
    · exact h1 h0.1
    · exact h2 h0.2
  · have h0 := hD _ hmem
    rcases mul_base_not_base hζ hg with h1 | h2
    · exact h1 h0.1
    · exact h2 h0.2

/-- Every element of a two-adic coset generated by base-field `shift` and `ω` has `c1 = 0 ∧ c2 = 0`. -/
theorem baseCoset_c1_c2_eq_zero {shift ω : Fp} {n j : ℕ} {x : K}
    (hx : x ∈ (CertiFri.twoAdicDomain (Fp3Model.embedHom ω) n j).image (Fp3Model.embedHom shift * ·)) :
    x.c1 = 0 ∧ x.c2 = 0 := by
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  unfold CertiFri.twoAdicDomain at hy
  rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
  let shift' : GoldilocksField := shift
  let ω' : GoldilocksField := ω
  have hpow : Fp3Model.embedHom shift' * (Fp3Model.embedHom ω' ^ 2 ^ j) ^ i =
      Fp3Model.embedHom (shift' * (ω' ^ 2 ^ j) ^ i) := by
    rw [← map_pow, ← map_pow, ← map_mul]
  change (Fp3Model.embedHom shift' * (Fp3Model.embedHom ω' ^ 2 ^ j) ^ i).c1 = 0 ∧
    (Fp3Model.embedHom shift' * (Fp3Model.embedHom ω' ^ 2 ^ j) ^ i).c2 = 0
  rw [hpow]
  exact ⟨rfl, rfl⟩

/-- Exact cardinality of the base subfield `Fp ⊆ K` (`c1 = 0 ∧ c2 = 0`) is `Goldilocks.order`. -/
theorem card_in_baseField :
    (Finset.univ.filter (fun z : K => z.c1 = 0 ∧ z.c2 = 0)).card = CertiFri.P3.Goldilocks.order := by
  have heq : (Finset.univ.filter (fun z : K => z.c1 = 0 ∧ z.c2 = 0)) =
      Finset.univ.image (fun x : GoldilocksField => Fp3Model.embedHom x) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨z.c0, Fp3Model.ext rfl h1.symm h2.symm⟩
    · rintro ⟨x, rfl⟩; exact ⟨rfl, rfl⟩
  rw [heq, Finset.card_image_of_injective _ Fp3Model.embedHom_injective, Finset.card_univ, ZMod.card]

/-- Exact fraction of `K = Fp^3` lying in the base field `Fp` is `1 / Goldilocks.order ^ 2` (`≈ 2^-128`). -/
theorem prob_in_baseField_eq :
    ((Finset.univ.filter (fun z : K => z.c1 = 0 ∧ z.c2 = 0)).card : ℝ) / Fintype.card K =
      1 / ((CertiFri.P3.Goldilocks.order : ℝ) ^ 2) := by
  rw [card_in_baseField, K.card_K]
  have hp : (CertiFri.P3.Goldilocks.order : ℝ) ≠ 0 := by
    unfold CertiFri.P3.Goldilocks.order; norm_num
  push_cast
  field_simp [hp]

set_option linter.constructorNameAsVariable false in
/-- **Tight off-domain cardinality bound (`ζ ∉ D ∪ g⁻¹ • D`):**
For any finite evaluation domain `D : Finset K` and nonzero shift `g : K`,
at most `2 * D.card` challenges `ζ ∈ K` satisfy `ζ ∈ D ∨ ζ * g ∈ D`.
In Goldilocks `Fp^3` (`|K| ≈ 2^192`) with `|D| = 2^22`, this yields
`2 * |D| / |K| ≈ 2^-169` (`169` bits). -/
theorem card_zeta_in_domain_or_shift_le (D : Finset K) {g : K} (hg : g ≠ 0) :
    (Finset.univ.filter (fun z : K => z ∈ D ∨ z * g ∈ D)).card ≤ 2 * D.card := by
  classical
  have hsub : Finset.univ.filter (fun z : K => z ∈ D ∨ z * g ∈ D) ⊆
      D ∪ D.image (fun x => x * g⁻¹) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rcases hz with h1 | h2
    · exact Finset.mem_union_left _ h1
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z * g, h2, ?_⟩)
      rw [mul_assoc, mul_inv_cancel₀ hg, mul_one]
  calc (Finset.univ.filter (fun z : K => z ∈ D ∨ z * g ∈ D)).card
      ≤ (D ∪ D.image (fun x => x * g⁻¹)).card := Finset.card_le_card hsub
    _ ≤ D.card + (D.image (fun x => x * g⁻¹)).card := Finset.card_union_le _ _
    _ ≤ D.card + D.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * D.card := by omega

set_option linter.constructorNameAsVariable false in
/-- **Tight off-domain probability bound:**
`Pr_{ζ ← K}[ζ ∈ D ∨ ζ * g ∈ D] ≤ 2 * |D| / |K|`. -/
theorem prob_zeta_in_domain_or_shift_le (D : Finset K) {g : K} (hg : g ≠ 0) :
    ((Finset.univ.filter (fun z : K => z ∈ D ∨ z * g ∈ D)).card : ℝ) / Fintype.card K ≤
      (2 * D.card : ℝ) / Fintype.card K := by
  have hpos : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  apply div_le_div_of_nonneg_right _ hpos
  exact_mod_cast card_zeta_in_domain_or_shift_le D hg

/-- **Subgroup-coset shift invariance:** if `D = shift • S` is a coset of a multiplicative
subgroup `S ≤ Kˣ` and `g ∈ S` (which holds for every trace generator `ω_ℓ` inside the maximal
two-adic LDE subgroup `H_M`), then `ζ ∉ shift • S` automatically implies `ζ * g ∉ shift • S`. -/
theorem not_mem_coset_mul_of_mem_subgroup {S : Subgroup Kˣ} {shift : Kˣ}
    {ζ : K} {g : Kˣ} (hg : g ∈ S)
    (hζ : ∀ s ∈ S, ζ ≠ ((shift * s : Kˣ) : K)) :
    ∀ s ∈ S, ζ * (g : K) ≠ ((shift * s : Kˣ) : K) := by
  intro s hs heq
  apply hζ (s * g⁻¹) (S.mul_mem hs (S.inv_mem hg))
  have hmul : ζ * (g : K) * ((g⁻¹ : Kˣ) : K) = ((shift * s : Kˣ) : K) * ((g⁻¹ : Kˣ) : K) :=
    congrArg (fun x : K => x * ((g⁻¹ : Kˣ) : K)) heq
  have hl : ζ * (g : K) * ((g⁻¹ : Kˣ) : K) = ζ := by
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hr : ((shift * s : Kˣ) : K) * ((g⁻¹ : Kˣ) : K) = ((shift * (s * g⁻¹) : Kˣ) : K) := by
    rw [← Units.val_mul, mul_assoc]
  rw [hl, hr] at hmul
  exact hmul

end ExtensionOffDomain

end Ix.Cert.MultiStark
