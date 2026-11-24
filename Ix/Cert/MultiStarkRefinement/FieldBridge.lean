import Ix.Cert.MultiStark.FieldModel
import Ix.Cert.MultiStark.Air
import Aiur.Library.Field.Goldilocks

/-! # Goldilocks & Quadratic Extension Field Bridge (`FieldBridge`)

Refines every Goldilocks base-field and degree-2 extension operation in
`Aiur.Library.Field.Goldilocks` and `MultiStark.Source.starkVerifier`
onto `CertiFri.P3.{Goldilocks, GoldilocksExt}` and `Ix.Cert.MultiStark.{Fp, K}`:
- `gl_val` / `gl_lt_p` / `gl_to_bytes` canonical 8-byte little-endian encoding & uniqueness,
- `gl_inverse` and `eg_inverse` witness-constraint specifications (`x * (x*iv - 1) = 0 ∧ iv * (x*iv - 1) = 0`),
- `eg_add`, `eg_sub`, `eg_neg`, `eg_mul`, `eg_div`, `eg_eq`, `ext_is_zero`,
- `pair_mul` (`K[u]/(u^2 - 7)` arithmetic for LogUp constraints),
- `two_adic_gen` (all `0 ≤ b ≤ 32` matching `Goldilocks.twoAdicGenerator`),
- `quotient_degree_of` (matching `SysCircuit.quotientDegree`),
- `ext_exp_pow2`, `from_ext_basis`, and `trace_selectors`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open CertiFri CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. Canonical 8-Byte Little-Endian Goldilocks Encoding (`gl_val`, `gl_lt_p`, `gl_to_bytes`) -/

/-- Exact natural-number value of 8 little-endian bytes (`UInt8`). -/
def leBytes8Nat (b : Fin 8 → UInt8) : Nat :=
  (b 0).toNat + 256 * (b 1).toNat + 65536 * (b 2).toNat + 16777216 * (b 3).toNat +
  4294967296 * (b 4).toNat + 1099511627776 * (b 5).toNat +
  281474976710656 * (b 6).toNat + 72057594037927936 * (b 7).toNat

/-- Model of `Fields::is_zero(x)` over `Fp`. -/
def isZeroFp (x : Fp) : Fp := if x = 0 then 1 else 0

/-- Model of `Goldilocks::gl_val(x)` (`Aiur/Aiur/Library/Field/Goldilocks.lean:21-26`). -/
def glValModel (b : Fin 8 → UInt8) : Fp :=
  ((b 0).toNat : Fp) + 256 * ((b 1).toNat : Fp) + 65536 * ((b 2).toNat : Fp) +
  16777216 * ((b 3).toNat : Fp) + 4294967296 * ((b 4).toNat : Fp) +
  1099511627776 * ((b 5).toNat : Fp) + 281474976710656 * ((b 6).toNat : Fp) +
  72057594037927936 * ((b 7).toNat : Fp)

/-- Model of `Goldilocks::gl_lt_p(x)` (`Aiur/Aiur/Library/Field/Goldilocks.lean:28-34`). -/
def glLtPModel (b : Fin 8 → UInt8) : Fp :=
  let hiMax := isZeroFp (((b 4).toNat : Fp) + ((b 5).toNat : Fp) +
    ((b 6).toNat : Fp) + ((b 7).toNat : Fp) - 1020)
  let loZero := isZeroFp (((b 0).toNat : Fp) + ((b 1).toNat : Fp) +
    ((b 2).toNat : Fp) + ((b 3).toNat : Fp))
  1 - hiMax * (1 - loZero)

theorem glValModel_eq_natCast (b : Fin 8 → UInt8) :
    glValModel b = (leBytes8Nat b : Fp) := by
  unfold glValModel leBytes8Nat
  push_cast
  ring

private theorem sum4_bytes_eq_1020_iff (b4 b5 b6 b7 : UInt8) :
    (((b4.toNat : Fp) + (b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) - 1020 = 0) ↔
      (b4.toNat = 255 ∧ b5.toNat = 255 ∧ b6.toNat = 255 ∧ b7.toNat = 255) := by
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  have hsum_cast : ((b4.toNat : Fp) + (b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) =
      ((b4.toNat + b5.toNat + b6.toNat + b7.toNat : Nat) : Fp) := by push_cast; ring
  have h1020 : (1020 : Fp) = ((1020 : Nat) : Fp) := rfl
  rw [sub_eq_zero, hsum_cast, h1020, ZMod.natCast_eq_natCast_iff']
  have hlt1 : b4.toNat + b5.toNat + b6.toNat + b7.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hlt2 : 1020 < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; decide
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  omega

private theorem sum4_bytes_eq_zero_iff (b0 b1 b2 b3 : UInt8) :
    (((b0.toNat : Fp) + (b1.toNat : Fp) + (b2.toNat : Fp) + (b3.toNat : Fp)) = 0) ↔
      (b0.toNat = 0 ∧ b1.toNat = 0 ∧ b2.toNat = 0 ∧ b3.toNat = 0) := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have hsum_cast : ((b0.toNat : Fp) + (b1.toNat : Fp) + (b2.toNat : Fp) + (b3.toNat : Fp)) =
      ((b0.toNat + b1.toNat + b2.toNat + b3.toNat : Nat) : Fp) := by push_cast; ring
  have h0cast : (0 : Fp) = ((0 : Nat) : Fp) := rfl
  rw [hsum_cast, h0cast, ZMod.natCast_eq_natCast_iff']
  have hlt1 : b0.toNat + b1.toNat + b2.toNat + b3.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hlt2 : 0 < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; decide
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  omega

/-- Exact specification of `Goldilocks::gl_lt_p`: returns `1` iff the 8 little-endian bytes
represent a canonical Goldilocks element strictly less than `p = 2^64 - 2^32 + 1`. -/
theorem glLtPModel_eq_one_iff (b : Fin 8 → UInt8) :
    glLtPModel b = 1 ↔ leBytes8Nat b < Goldilocks.order := by
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt
  have h2 := (b 2).toNat_lt; have h3 := (b 3).toNat_lt
  have h4 := (b 4).toNat_lt; have h5 := (b 5).toNat_lt
  have h6 := (b 6).toNat_lt; have h7 := (b 7).toNat_lt
  unfold glLtPModel isZeroFp
  have hhi_iff := sum4_bytes_eq_1020_iff (b 4) (b 5) (b 6) (b 7)
  have hlo_iff := sum4_bytes_eq_zero_iff (b 0) (b 1) (b 2) (b 3)
  have h10 : (1 : Fp) ≠ 0 := by decide
  by_cases hhi : ((b 4).toNat : Fp) + ((b 5).toNat : Fp) + ((b 6).toNat : Fp) + ((b 7).toNat : Fp) - 1020 = 0
  · simp only [hhi, ↓reduceIte]
    have hhi_vals := hhi_iff.mp hhi
    by_cases hlo : ((b 0).toNat : Fp) + ((b 1).toNat : Fp) + ((b 2).toNat : Fp) + ((b 3).toNat : Fp) = 0
    · simp only [hlo, ↓reduceIte, sub_self, mul_zero, sub_zero, true_iff]
      have hlo_vals := hlo_iff.mp hlo
      unfold leBytes8Nat Goldilocks.order
      omega
    · simp only [hlo, ↓reduceIte, sub_zero, mul_one, sub_self, h10.symm, false_iff, not_lt]
      have hlo_ne : ¬ ((b 0).toNat = 0 ∧ (b 1).toNat = 0 ∧ (b 2).toNat = 0 ∧ (b 3).toNat = 0) :=
        mt hlo_iff.mpr hlo
      unfold leBytes8Nat Goldilocks.order
      omega
  · simp only [hhi, ↓reduceIte, zero_mul, sub_zero, true_iff]
    have hhi_ne : ¬ ((b 4).toNat = 255 ∧ (b 5).toNat = 255 ∧ (b 6).toNat = 255 ∧ (b 7).toNat = 255) :=
      mt hhi_iff.mpr hhi
    unfold leBytes8Nat Goldilocks.order
    omega

/-- `Goldilocks::gl_to_bytes` determines a unique canonical 8-byte little-endian encoding
for any `v : Fp`, matching `v.val` byte-for-byte. -/
theorem gl_to_bytes_spec {v : Fp} {b : Fin 8 → UInt8}
    (hval : glValModel b = v) (hlt : glLtPModel b = 1) :
    leBytes8Nat b = v.val ∧
    ∀ i : Fin 8, (b i).toNat = (v.val / 2 ^ (8 * i.val)) % 256 := by
  have hltp : leBytes8Nat b < Aiur.Library.U32.Goldilocks.modulus :=
    (glLtPModel_eq_one_iff b).mp hlt
  have hnat : leBytes8Nat b = v.val := by
    have hv : (leBytes8Nat b : Fp) = (v.val : Fp) := by
      rw [← glValModel_eq_natCast, hval, ZMod.natCast_zmod_val]
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hv
    rw [Nat.mod_eq_of_lt hltp, Nat.mod_eq_of_lt (ZMod.val_lt v)] at hmod
    exact hmod
  refine ⟨hnat, fun i => ?_⟩
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt
  have h2 := (b 2).toNat_lt; have h3 := (b 3).toNat_lt
  have h4 := (b 4).toNat_lt; have h5 := (b 5).toNat_lt
  have h6 := (b 6).toNat_lt; have h7 := (b 7).toNat_lt
  rw [← hnat]
  unfold leBytes8Nat
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- Uniqueness of `Goldilocks::gl_to_bytes`: two canonical byte arrays with the same field value
are equal. -/
theorem gl_to_bytes_unique {v : Fp} {b₁ b₂ : Fin 8 → UInt8}
    (hv1 : glValModel b₁ = v) (hl1 : glLtPModel b₁ = 1)
    (hv2 : glValModel b₂ = v) (hl2 : glLtPModel b₂ = 1) :
    b₁ = b₂ := by
  funext i
  have h1 := (gl_to_bytes_spec hv1 hl1).2 i
  have h2 := (gl_to_bytes_spec hv2 hl2).2 i
  exact UInt8.toNat_inj.mp (h1.trans h2.symm)

/-! ## 2. Base & Extension Field Inversion Constraints (`gl_inverse`, `eg_inverse`) -/

/-- Exact constraint specification of `Goldilocks::gl_inverse` (`Goldilocks.lean:48-54`):
`x * (x * iv - 1) = 0 ∧ iv * (x * iv - 1) = 0` forces `iv = x⁻¹` in `Fp` (including `0⁻¹ = 0`). -/
theorem gl_inverse_spec {x iv : Fp}
    (h1 : x * (x * iv - 1) = 0) (h2 : iv * (x * iv - 1) = 0) :
    iv = x⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    simp only [zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero] at h2
    simp [h2]
  · have hmul : x * iv - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hx
    have hmul1 : x * iv = 1 := sub_eq_zero.mp hmul
    exact eq_inv_of_mul_eq_one_right hmul1

/-- Exact constraint specification of `Goldilocks::gl_inv_nonzero` (`Goldilocks.lean:56-60`):
`x * iv = 1` strictly rejects `x = 0` and forces `iv = x⁻¹` in `Fp`. -/
theorem gl_inv_nonzero_spec {x iv : Fp} (h : x * iv = 1) :
    x ≠ 0 ∧ iv = x⁻¹ := by
  have hx : x ≠ 0 := by
    intro h0; subst h0; simp at h
  exact ⟨hx, eq_inv_of_mul_eq_one_right h⟩

/-- Exact constraint specification of cubic adjugate/norm inversion in `K = Fp[X] / (X^3 - X - 1)`:
with `norm = K.norm a` and `ninv` satisfying `gl_inverse` constraints for `norm`,
`⟨a.adjugate.c0 * ninv, a.adjugate.c1 * ninv, a.adjugate.c2 * ninv⟩ = a⁻¹` in `K`. -/
theorem eg_inverse_spec {a : K} {ninv : Fp}
    (h1 : K.norm a * (K.norm a * ninv - 1) = 0)
    (h2 : ninv * (K.norm a * ninv - 1) = 0) :
    (⟨a.adjugate.c0 * ninv, a.adjugate.c1 * ninv, a.adjugate.c2 * ninv⟩ : K) = a⁻¹ := by
  have hninv : ninv = (K.norm a)⁻¹ := gl_inverse_spec h1 h2
  subst hninv
  let g : GoldilocksField := Fp3Model.norm a
  change (⟨Fp3Model.c0 a.adjugate * g⁻¹, Fp3Model.c1 a.adjugate * g⁻¹,
    Fp3Model.c2 a.adjugate * g⁻¹⟩ : K) = Fp3Model.inv a
  unfold Fp3Model.inv
  change _ = if g = 0 then 0 else Fp3Model.embedHom g⁻¹ * a.adjugate
  by_cases hg : g = 0
  · rw [ite_eq_left hg, hg, inv_zero]
    ext <;> simp
  · rw [ite_eq_right hg]
    ext <;> simp only [Fp3Model.mul_c0, Fp3Model.mul_c1, Fp3Model.mul_c2,
      Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2] <;> ring

/-- Exact constraint specification of `Pcs::eg3_inv_nonzero` (`Pcs.lean:40-49`):
`K.norm a * ninv = 1` strictly rejects `a = 0` and forces
`⟨a.adjugate.c0 * ninv, a.adjugate.c1 * ninv, a.adjugate.c2 * ninv⟩ = a⁻¹` in `K = Fp[X] / (X^3 - X - 1)`. -/
theorem eg_inv_nonzero_spec {a : K} {ninv : Fp}
    (h : K.norm a * ninv = 1) :
    a ≠ 0 ∧ (⟨a.adjugate.c0 * ninv, a.adjugate.c1 * ninv, a.adjugate.c2 * ninv⟩ : K) = a⁻¹ := by
  obtain ⟨hnorm_ne, hninv⟩ := gl_inv_nonzero_spec h
  have ha_ne : a ≠ 0 := by
    intro h0; subst h0
    exact hnorm_ne (by decide)
  refine ⟨ha_ne, ?_⟩
  subst hninv
  let g : GoldilocksField := Fp3Model.norm a
  have hg : g ≠ 0 := hnorm_ne
  change (⟨Fp3Model.c0 a.adjugate * g⁻¹, Fp3Model.c1 a.adjugate * g⁻¹,
    Fp3Model.c2 a.adjugate * g⁻¹⟩ : K) = Fp3Model.inv a
  unfold Fp3Model.inv
  change _ = if g = 0 then 0 else Fp3Model.embedHom g⁻¹ * a.adjugate
  rw [ite_eq_right hg]
  ext <;> simp only [Fp3Model.mul_c0, Fp3Model.mul_c1, Fp3Model.mul_c2,
    Fp3Model.embedHom_apply, Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2] <;> ring

/-- Exact constraint specification of `Pcs::eg3_div_nonzero` (`Pcs.lean:51-53`):
`K.norm b * ninv = 1` strictly rejects `b = 0` and forces
`a * ⟨b.adjugate.c0 * ninv, b.adjugate.c1 * ninv, b.adjugate.c2 * ninv⟩ = a * b⁻¹` in `K`. -/
theorem eg_div_nonzero_spec {a b : K} {ninv : Fp}
    (h : K.norm b * ninv = 1) :
    b ≠ 0 ∧ a * (⟨b.adjugate.c0 * ninv, b.adjugate.c1 * ninv, b.adjugate.c2 * ninv⟩ : K) = a * b⁻¹ := by
  obtain ⟨hb_ne, hinv⟩ := eg_inv_nonzero_spec h
  exact ⟨hb_ne, by rw [hinv]⟩

/-- `Pcs::eg3_add` refines `CertiFri.P3.GoldilocksExt3.add` in `K`. -/
theorem eg_add_refines (a b : EF) :
    (⟨baseToFp a.c0 + baseToFp b.c0, baseToFp a.c1 + baseToFp b.c1,
      baseToFp a.c2 + baseToFp b.c2⟩ : K) =
      extToModel (a.add b) :=
  (goldilocksExtRefines.map_add a b).symm

/-- `Pcs::eg3_sub` refines `CertiFri.P3.GoldilocksExt3.sub` in `K`. -/
theorem eg_sub_refines (a b : EF) :
    (⟨baseToFp a.c0 - baseToFp b.c0, baseToFp a.c1 - baseToFp b.c1,
      baseToFp a.c2 - baseToFp b.c2⟩ : K) =
      extToModel (a.sub b) :=
  (goldilocksExtRefines.map_sub a b).symm

/-- `Pcs::eg3_neg` refines `CertiFri.P3.GoldilocksExt3.neg` in `K`. -/
theorem eg_neg_refines (a : EF) :
    (⟨(0 : Fp) - baseToFp a.c0, (0 : Fp) - baseToFp a.c1, (0 : Fp) - baseToFp a.c2⟩ : K) =
      extToModel a.neg := by
  have h : -(extToModel a) = extToModel a.neg := (goldilocksExtRefines.map_neg a).symm
  rw [← h]
  ext <;> (simp only [extToModel, GoldilocksExt3.toModel, Fp3Model.neg_c0, Fp3Model.neg_c1,
    Fp3Model.neg_c2, zero_sub]; rfl)

/-- `Pcs::eg3_mul` refines `CertiFri.P3.GoldilocksExt3.mul` in `K`. -/
theorem eg_mul_refines (a b : EF) :
    (⟨baseToFp a.c0 * baseToFp b.c0 + baseToFp a.c1 * baseToFp b.c2 + baseToFp a.c2 * baseToFp b.c1,
      baseToFp a.c0 * baseToFp b.c1 + baseToFp a.c1 * baseToFp b.c0 +
        baseToFp a.c1 * baseToFp b.c2 + baseToFp a.c2 * baseToFp b.c1 + baseToFp a.c2 * baseToFp b.c2,
      baseToFp a.c0 * baseToFp b.c2 + baseToFp a.c1 * baseToFp b.c1 +
        baseToFp a.c2 * baseToFp b.c0 + baseToFp a.c2 * baseToFp b.c2⟩ : K) =
      extToModel (a.mul b) :=
  (goldilocksExtRefines.map_mul a b).symm

private lemma extToModel_add (a b : EF) : extToModel (a.add b) = extToModel a + extToModel b :=
  goldilocksExtRefines.map_add a b

private lemma extToModel_sub (a b : EF) : extToModel (a.sub b) = extToModel a - extToModel b :=
  goldilocksExtRefines.map_sub a b

private lemma extToModel_mul (a b : EF) : extToModel (a.mul b) = extToModel a * extToModel b :=
  goldilocksExtRefines.map_mul a b

private lemma extToModel_inv (a : EF) : extToModel a.inv = (extToModel a)⁻¹ :=
  goldilocksExtRefines.map_inv a

/-- `Pcs::eg3_div_nonzero` refines `CertiFri.P3.GoldilocksExt3.mul a b.inv` in `K`. -/
theorem eg_div_refines (a b : EF) :
    extToModel a * (extToModel b)⁻¹ = extToModel (a.mul b.inv) := by
  rw [extToModel_mul, extToModel_inv]

/-- `Pcs::eg3_eq` returns `1` iff the two `GoldilocksExt3` elements are equal. -/
theorem eg_eq_iff (a b : EF) :
    isZeroFp (baseToFp a.c0 - baseToFp b.c0) * isZeroFp (baseToFp a.c1 - baseToFp b.c1) *
      isZeroFp (baseToFp a.c2 - baseToFp b.c2) = 1 ↔ a = b := by
  have h10 : (1 : Fp) ≠ 0 := by decide
  unfold isZeroFp
  constructor
  · intro h
    by_cases h0 : baseToFp a.c0 - baseToFp b.c0 = 0
    · simp only [h0, ↓reduceIte, one_mul] at h
      by_cases h1 : baseToFp a.c1 - baseToFp b.c1 = 0
      · simp only [h1, ↓reduceIte, one_mul] at h
        by_cases h2 : baseToFp a.c2 - baseToFp b.c2 = 0
        · have hmod : extToModel a = extToModel b := by
            ext
            · exact sub_eq_zero.mp h0
            · exact sub_eq_zero.mp h1
            · exact sub_eq_zero.mp h2
          exact decide_eq_true_iff.mp ((goldilocksExtRefines.beq_iff a b).mpr hmod)
        · simp only [h2, ↓reduceIte] at h; exact absurd h.symm h10
      · simp only [h1, ↓reduceIte, zero_mul] at h; exact absurd h.symm h10
    · simp only [h0, ↓reduceIte, zero_mul] at h; exact absurd h.symm h10
  · rintro rfl
    simp

/-- `StarkVerifier::ext_is_zero` returns `1` iff the extension element is `GoldilocksExt3.zero`. -/
theorem ext_is_zero_iff (e : EF) :
    isZeroFp (baseToFp e.c0) * isZeroFp (baseToFp e.c1) * isZeroFp (baseToFp e.c2) = 1 ↔
      e = GoldilocksExt3.zero := by
  have hz0 : baseToFp GoldilocksExt3.zero.c0 = 0 := by decide
  have hz1 : baseToFp GoldilocksExt3.zero.c1 = 0 := by decide
  have hz2 : baseToFp GoldilocksExt3.zero.c2 = 0 := by decide
  simpa [hz0, hz1, hz2] using eg_eq_iff e GoldilocksExt3.zero

/-! ## 3. `StarkVerifier` Algebraic Helpers (`triple_mul`, `two_adic_gen`, `quotient_degree_of`, `ext_exp_pow2`, `from_ext_basis`) -/

/-- `StarkVerifier::triple_mul` refines `Ix.Cert.MultiStark.tripleMul` in `K × K × K`
(modulo `X^3 - X - 1`). -/
theorem triple_mul_refines (a0 a1 a2 b0 b1 b2 : EF) :
    let (r0, r1, r2) := tripleMul a0 a1 a2 b0 b1 b2
    extToModel r0 =
      extToModel a0 * extToModel b0 + extToModel a1 * extToModel b2 + extToModel a2 * extToModel b1 ∧
    extToModel r1 =
      extToModel a0 * extToModel b1 + extToModel a1 * extToModel b0 +
      extToModel a1 * extToModel b2 + extToModel a2 * extToModel b1 + extToModel a2 * extToModel b2 ∧
    extToModel r2 =
      extToModel a0 * extToModel b2 + extToModel a1 * extToModel b1 +
      extToModel a2 * extToModel b0 + extToModel a2 * extToModel b2 := by
  unfold tripleMul
  dsimp only
  simp only [extToModel_add, extToModel_sub, extToModel_mul]
  refine ⟨by ring, by ring, by ring⟩

/-- Repeated squaring starting from the primitive `2^32`-th root of unity (`1753635133440165772`),
structurally recursive on the distance `32 - bits` for kernel reduction. -/
def twoAdicGenStep : Nat → Fp
  | 0 => (1753635133440165772 : Fp)
  | k + 1 =>
    let g := twoAdicGenStep k
    g * g

/-- Exact model of `StarkVerifier::two_adic_gen` (`StarkVerifier.lean:119-127`). -/
def twoAdicGenModel (bits : Nat) : Fp :=
  if bits = 0 then 1
  else if bits ≤ 32 then twoAdicGenStep (32 - bits)
  else 0

/-- `StarkVerifier::two_adic_gen(b)` equals `baseToFp (Goldilocks.twoAdicGenerator b)` for
every valid domain log-size `b ≤ 32`. -/
theorem two_adic_gen_refines :
    ∀ b : Fin 33, twoAdicGenModel b.val = baseToFp (Goldilocks.twoAdicGenerator b.val) := by
  decide

/-- Exact model of `StarkVerifier::quotient_degree_of` (`StarkVerifier.lean:340-349`). -/
def quotientDegreeOfModel (md : Nat) : Nat :=
  match md with
  | 0 | 1 | 2 => 1
  | 3 => 2
  | 4 | 5 => 4
  | 6 | 7 | 8 | 9 => 8
  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => 16
  | _ => 32

/-- `StarkVerifier::quotient_degree_of(md)` agrees identically with `SysCircuit.quotientDegree`
for every constraint degree `md ≤ 33`. -/
theorem quotient_degree_of_refines :
    ∀ md : Fin 34,
      quotientDegreeOfModel md.val =
        SysCircuit.quotientDegree
          { mainWidth := 0, preprocessedWidth := 0, preprocessedHeight := 0
            maxConstraintDegree := md.val, lookupGroupSize := 1
            nodes := #[], zeros := #[], lookups := #[] } := by
  decide

/-- Exact model of `StarkVerifier::ext_exp_pow2` (`StarkVerifier.lean:112-117`) in `K`. -/
def extExpPow2Model : K → Nat → K
  | e, 0 => e
  | e, k + 1 => extExpPow2Model (e * e) k

/-- `StarkVerifier::ext_exp_pow2` refines `Ix.Cert.MultiStark.efPow2` in `K`. -/
theorem ext_exp_pow2_refines :
    ∀ (k : Nat) (e : EF), extExpPow2Model (extToModel e) k = extToModel (efPow2 e k)
  | 0, _ => rfl
  | k + 1, e => by
    unfold extExpPow2Model efPow2
    rw [← extToModel_mul]
    exact ext_exp_pow2_refines k (e.mul e)

/-- `StarkVerifier::from_ext_basis(c0, c1, c2)` refines `c0 + c1 * ⟨0, 1, 0⟩ + c2 * ⟨0, 0, 1⟩` in `K`. -/
theorem from_ext_basis_refines (c0 c1 c2 : EF) :
    extToModel c0 + extToModel c1 * (⟨0, 1, 0⟩ : K) + extToModel c2 * (⟨0, 0, 1⟩ : K) =
      extToModel (c0.add ((c1.mul ⟨Goldilocks.zero, Goldilocks.one, Goldilocks.zero⟩).add
        (c2.mul ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.one⟩))) := by
  have hx1 : extToModel ⟨Goldilocks.zero, Goldilocks.one, Goldilocks.zero⟩ = ⟨0, 1, 0⟩ := by
    ext <;> decide
  have hx2 : extToModel ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.one⟩ = ⟨0, 0, 1⟩ := by
    ext <;> decide
  rw [extToModel_add, extToModel_add, extToModel_mul, extToModel_mul, hx1, hx2, add_assoc]

/-! ## 4. Algebraic Equivalences for Optimized PCS Operations (`rows_pop`, `fri_fold2`, `ro_fold`, `finalize_buckets`) -/

/-- `Pcs::rows_pop` checks `Goldilocks::gl_lt_p(x) == 1` directly on an already range-checked
8-byte `UInt64::U64`; by `gl_to_bytes_unique`, `x` is byte-for-byte identical to any canonical
`Goldilocks::gl_to_bytes(Goldilocks::gl_val(x))` output. -/
theorem rows_pop_canonical_eq {x r : Fin 8 → UInt8}
    (hltX : glLtPModel x = 1)
    (hvalR : glValModel r = glValModel x) (hltR : glLtPModel r = 1) :
    x = r :=
  gl_to_bytes_unique rfl hltX hvalR hltR

/-- Exact Goldilocks inverse of `2`: `2 * 9223372034707292161 = 1` in `Fp` (used by `Pcs::fri_fold2`). -/
theorem goldilocks_inv_two : (2 : Fp) * (9223372034707292161 : Fp) = 1 := by
  decide

theorem goldilocks_inv_two_eq : (9223372034707292161 : Fp) = (2 : Fp)⁻¹ :=
  eq_inv_of_mul_eq_one_right goldilocks_inv_two

/-- Dividing an extension element `e : K` by an embedded base element `⟨s, 0, 0⟩ : K` equals
componentwise multiplication by `s⁻¹ : Fp` (for every `s : Fp`, including `s = 0`).
Certifies the base-inversion optimization in `Pcs::fri_fold2`. -/
theorem eg_div_base_eq (e : K) (s : Fp) :
    e * (⟨s, 0, 0⟩ : K)⁻¹ = ⟨e.c0 * s⁻¹, e.c1 * s⁻¹, e.c2 * s⁻¹⟩ := by
  by_cases hs : s = 0
  · subst hs
    change e * (0 : K)⁻¹ = ⟨Fp3Model.c0 e * (0 : GoldilocksField)⁻¹,
      Fp3Model.c1 e * (0 : GoldilocksField)⁻¹, Fp3Model.c2 e * (0 : GoldilocksField)⁻¹⟩
    simp only [inv_zero, mul_zero]; rfl
  · have hinv : (⟨s, 0, 0⟩ : K)⁻¹ = ⟨s⁻¹, 0, 0⟩ := by
      symm
      apply eq_inv_of_mul_eq_one_right
      ext
      · change s * s⁻¹ + 0 * 0 + 0 * 0 = 1
        simp [mul_inv_cancel₀ hs]
      · change s * 0 + 0 * s⁻¹ + 0 * 0 + 0 * 0 + 0 * 0 = 0
        ring
      · change s * 0 + 0 * 0 + 0 * s⁻¹ + 0 * 0 = 0
        ring
    rw [hinv]
    ext
    · change e.c0 * s⁻¹ + e.c1 * 0 + e.c2 * 0 = e.c0 * s⁻¹; ring
    · change e.c0 * 0 + e.c1 * s⁻¹ + e.c1 * 0 + e.c2 * 0 + e.c2 * 0 = e.c1 * s⁻¹; ring
    · change e.c0 * 0 + e.c1 * 0 + e.c2 * s⁻¹ + e.c2 * 0 = e.c2 * s⁻¹; ring

/-- Original tail-recursive `Pcs::ro_fold(px, pz, alpha, s, ap)` in `K`. -/
def roFoldTail : List Fp → List K → K → K → K → K × K
  | [], _, _, s, ap => (s, ap)
  | x :: xs, z :: zs, alpha, s, ap =>
    roFoldTail xs zs alpha (s + ap * (z - ⟨x, 0, 0⟩)) (ap * alpha)
  | _ :: _, [], _, s, ap => (s, ap)

/-- Ascending Horner-from-tail `Pcs::ro_fold_1pt` / `ro_fold_2pt` in `K`. -/
def roFoldHorner : List Fp → List K → K → K × K
  | [], _, _ => (0, 1)
  | x :: xs, z :: zs, alpha =>
    let (s, pw) := roFoldHorner xs zs alpha
    ((z - ⟨x, 0, 0⟩) + alpha * s, alpha * pw)
  | _ :: _, [], _ => (0, 1)

/-- `ro_fold_1pt` / `ro_fold_2pt` produces the exact same `(sum, ap * alpha^w)` as
tail-recursive `ro_fold` when shifted by `(acc, ap)` (for equal-length lists). -/
theorem roFoldHorner_refines_tail :
    ∀ (xs : List Fp) (zs : List K) (alpha acc ap : K),
      xs.length = zs.length →
      let (s, pw) := roFoldHorner xs zs alpha
      roFoldTail xs zs alpha acc ap = (acc + ap * s, ap * pw)
  | [], [], _, acc, ap, _ => by
    simp [roFoldHorner, roFoldTail]
  | x :: xs, z :: zs, alpha, acc, ap, hlen => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    unfold roFoldHorner roFoldTail
    dsimp only
    rw [roFoldHorner_refines_tail xs zs alpha (acc + ap * (z - ⟨x, 0, 0⟩)) (ap * alpha) hlen]
    simp only [Prod.mk.injEq]
    constructor <;> ring

/-- Distributivity certifying `Pcs::finalize_buckets`: accumulating `(ro0, ro1)` per height
bucket and multiplying by `(q0, q1)` once per distinct height equals per-opening `q * s_i`. -/
theorem bucket_finalize_distributes (q0 q1 : K) (s0s s1s : List K) :
    (s0s.map (q0 * ·)).sum + (s1s.map (q1 * ·)).sum = q0 * s0s.sum + q1 * s1s.sum := by
  rw [List.sum_map_mul_left, List.sum_map_mul_left]
  simp

end Ix.Cert.MultiStarkRefinement
