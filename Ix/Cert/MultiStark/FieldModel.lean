import Aiur.Library.U32.Goldilocks
import CertiFriP3.GoldilocksExt
import CertiFriProofs.Exec.Setup
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.ModEq

/-! # Goldilocks & Quadratic Extension `CertiFri.Exec.FieldModel` + `WellFormed` (Gap 1a)

Proves that `CertiFri.P3.Goldilocks` and `CertiFri.P3.GoldilocksExt` implement the
mathematical prime field `Fp = ZMod 18446744069414584321` and its quadratic extension
`K = Fp[X] / (X^2 - 7)` satisfying `CertiFri.Exec.FieldModel` and `CertiFri.Exec.WellFormed`
for all shapes with `logMaxHeight ≤ 32`. Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Prime modulus `p = 2^64 - 2^32 + 1` of the Goldilocks field. -/
abbrev Fp : Type := Aiur.Library.U32.Goldilocks.F

private theorem goldilocks_order_eq : Goldilocks.order = Aiur.Library.U32.Goldilocks.modulus := rfl

private theorem p64_toNat : (0xFFFFFFFF00000001 : UInt64).toNat = Goldilocks.order := rfl
private theorem eps_toNat : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl

/-! ## 1. Model Quadratic Extension Field `K = Fp[u] / (u^2 - 7)` -/

/-- Fast O(log e) modular exponentiation by structural recursion on LSB-first bit list. -/
private def evalBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * evalBits bs

private def powModBits (base mod : Nat) : List Bool → Nat
  | [] => 1 % mod
  | b :: bs =>
    let r := powModBits base mod bs
    let sq := (r * r) % mod
    if b then (sq * base) % mod else sq

private theorem powModBits_spec (base : Nat) (bs : List Bool) :
    ((powModBits base Aiur.Library.U32.Goldilocks.modulus bs : Nat) : Fp) =
      (base : Fp) ^ (evalBits bs) := by
  induction bs with
  | nil => simp [powModBits, evalBits]
  | cons b bs ih =>
    unfold powModBits evalBits
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true, ZMod.natCast_mod, Nat.cast_mul, ih]
    · rw [← sq, ← pow_mul, mul_comm, Nat.zero_add]
    · rw [← sq, ← pow_mul, mul_comm (evalBits bs) 2, pow_add, pow_one, mul_comm]

/-- Repeated squaring `x^(2^k) mod p` (structural on `k`, 31 steps for `2^31`). -/
private def sqModN (mod : Nat) : Nat → Nat → Nat
  | 0, x => x % mod
  | k + 1, x => sqModN mod k ((x * x) % mod)

private theorem sqModN_spec : ∀ (k x : Nat),
    ((sqModN Aiur.Library.U32.Goldilocks.modulus k x : Nat) : Fp) =
      (x : Fp) ^ (2 ^ k)
  | 0, x => by simp [sqModN]
  | k + 1, x => by
    rw [sqModN, sqModN_spec k, ZMod.natCast_mod, Nat.cast_mul, ← sq, ← pow_mul,
      show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

/-- `(p - 1) / 2 = 2^63 - 2^31 = 2^31 * (2^32 - 1)` in LSB-first binary:
31 zeros followed by 32 ones! -/
private def halfOrderBits : List Bool :=
  List.replicate 31 false ++ List.replicate 32 true

set_option maxRecDepth 4000 in
/-- `7` is a quadratic non-residue in `Fp`: `7^((p - 1)/2) = -1 ≠ 1`. -/
theorem seven_pow_half : (7 : Fp) ^ ((Goldilocks.order - 1) / 2) = -1 := by
  have heq : (Goldilocks.order - 1) / 2 = evalBits halfOrderBits := by decide
  have hval : powModBits 7 Aiur.Library.U32.Goldilocks.modulus halfOrderBits =
      Aiur.Library.U32.Goldilocks.modulus - 1 := by decide
  have h7 : (7 : Fp) = ((7 : Nat) : Fp) := rfl
  rw [h7, heq, ← powModBits_spec, hval]
  decide

theorem not_isSquare_seven : ¬ IsSquare (7 : Fp) := by
  rintro ⟨r, hr⟩
  have h1 : r ≠ 0 := by
    intro h0; subst h0; simp at hr
    exact (by decide : (7 : Fp) ≠ 0) hr
  have hfermat : r ^ (Goldilocks.order - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h1
  have h2 : (7 : Fp) ^ ((Goldilocks.order - 1) / 2) = 1 := by
    rw [hr, ← sq, ← pow_mul]
    have hexp : 2 * ((Goldilocks.order - 1) / 2) = Goldilocks.order - 1 := by decide
    rw [hexp]
    exact hfermat
  rw [seven_pow_half] at h2
  exact (by decide : (-1 : Fp) ≠ 1) h2

/-- Mathematical quadratic extension `K = Fp[u] / (u^2 - 7)`. -/
@[ext]
structure K where
  c0 : Fp
  c1 : Fp
  deriving DecidableEq

namespace K

def zero : K := ⟨0, 0⟩
def one : K := ⟨1, 0⟩
def add (a b : K) : K := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def sub (a b : K) : K := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
def neg (a : K) : K := ⟨-a.c0, -a.c1⟩
def mul (a b : K) : K := ⟨a.c0 * b.c0 + 7 * (a.c1 * b.c1), a.c0 * b.c1 + a.c1 * b.c0⟩
def norm (a : K) : Fp := a.c0 * a.c0 - 7 * (a.c1 * a.c1)
def inv (a : K) : K :=
  let s := (norm a)⁻¹
  ⟨a.c0 * s, -(a.c1 * s)⟩

instance : Zero K := ⟨zero⟩
instance : One K := ⟨one⟩
instance : Add K := ⟨add⟩
instance : Sub K := ⟨sub⟩
instance : Neg K := ⟨neg⟩
instance : Mul K := ⟨mul⟩
instance : Inv K := ⟨inv⟩
instance : Div K := ⟨fun a b => mul a (inv b)⟩
instance : NatCast K := ⟨fun n => ⟨(n : Fp), 0⟩⟩
instance : IntCast K := ⟨fun n => ⟨(n : Fp), 0⟩⟩
instance : NNRatCast K := ⟨fun q => ⟨(q : Fp), 0⟩⟩
instance : RatCast K := ⟨fun q => ⟨(q : Fp), 0⟩⟩

@[simp] lemma zero_c0 : (0 : K).c0 = 0 := rfl
@[simp] lemma zero_c1 : (0 : K).c1 = 0 := rfl
@[simp] lemma one_c0 : (1 : K).c0 = 1 := rfl
@[simp] lemma one_c1 : (1 : K).c1 = 0 := rfl
@[simp] lemma add_c0 (a b : K) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] lemma add_c1 (a b : K) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] lemma sub_c0 (a b : K) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] lemma sub_c1 (a b : K) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] lemma neg_c0 (a : K) : (-a).c0 = -a.c0 := rfl
@[simp] lemma neg_c1 (a : K) : (-a).c1 = -a.c1 := rfl
@[simp] lemma mul_c0 (a b : K) : (a * b).c0 = a.c0 * b.c0 + 7 * (a.c1 * b.c1) := rfl
@[simp] lemma mul_c1 (a b : K) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
@[simp] lemma inv_c0 (a : K) : a⁻¹.c0 = a.c0 * (norm a)⁻¹ := rfl
@[simp] lemma inv_c1 (a : K) : a⁻¹.c1 = -(a.c1 * (norm a)⁻¹) := rfl
@[simp] lemma div_c0 (a b : K) : (a / b).c0 = (a * b⁻¹).c0 := rfl
@[simp] lemma div_c1 (a b : K) : (a / b).c1 = (a * b⁻¹).c1 := rfl
@[simp] lemma natCast_c0 (n : ℕ) : (n : K).c0 = (n : Fp) := rfl
@[simp] lemma natCast_c1 (n : ℕ) : (n : K).c1 = 0 := rfl
@[simp] lemma intCast_c0 (n : ℤ) : (n : K).c0 = (n : Fp) := rfl
@[simp] lemma intCast_c1 (n : ℤ) : (n : K).c1 = 0 := rfl
@[simp] lemma nnratCast_c0 (q : ℚ≥0) : (q : K).c0 = (q : Fp) := rfl
@[simp] lemma nnratCast_c1 (q : ℚ≥0) : (q : K).c1 = 0 := rfl
@[simp] lemma ratCast_c0 (q : ℚ) : (q : K).c0 = (q : Fp) := rfl
@[simp] lemma ratCast_c1 (q : ℚ) : (q : K).c1 = 0 := rfl

lemma norm_eq_zero_iff (a : K) : norm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    unfold norm at h
    by_cases h1 : a.c1 = 0
    · have h0 : a.c0 * a.c0 = 0 := by simpa [h1] using h
      have hc0 : a.c0 = 0 := mul_self_eq_zero.mp h0
      exact K.ext hc0 h1
    · exfalso
      apply not_isSquare_seven
      refine ⟨a.c0 * a.c1⁻¹, ?_⟩
      have hsq : a.c0 * a.c0 = 7 * (a.c1 * a.c1) := sub_eq_zero.mp h
      field_simp [h1]
      linear_combination -hsq
  · rintro rfl; simp [norm]

instance : CommRing K where
  add_assoc a b c := K.ext (by simp [add_assoc]) (by simp [add_assoc])
  zero_add a := K.ext (by simp) (by simp)
  add_zero a := K.ext (by simp) (by simp)
  add_comm a b := K.ext (by simp [add_comm]) (by simp [add_comm])
  neg_add_cancel a := K.ext (by simp) (by simp)
  sub_eq_add_neg a b := K.ext (by simp [sub_eq_add_neg]) (by simp [sub_eq_add_neg])
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := K.ext (by simp) (by simp)
  natCast_succ n := K.ext (by simp) (by simp)
  intCast_ofNat n := K.ext (by simp) (by simp)
  intCast_negSucc n := K.ext (by simp) (by simp)
  mul_assoc a b c := K.ext (by simp; ring) (by simp; ring)
  one_mul a := K.ext (by simp) (by simp)
  mul_one a := K.ext (by simp) (by simp)
  left_distrib a b c := K.ext (by simp; ring) (by simp; ring)
  right_distrib a b c := K.ext (by simp; ring) (by simp; ring)
  zero_mul a := K.ext (by simp) (by simp)
  mul_zero a := K.ext (by simp) (by simp)
  mul_comm a b := K.ext (by simp; ring) (by simp; ring)

private lemma embed_inv (x : Fp) : (⟨x, 0⟩ : K)⁻¹ = ⟨x⁻¹, 0⟩ := by
  apply K.ext
  · simp [norm]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
  · simp

instance : Field K where
  exists_pair_ne := ⟨0, 1, fun h => (by decide : (0 : Fp) ≠ 1) (congrArg K.c0 h)⟩
  inv_zero := K.ext (by simp [norm]) (by simp [norm])
  mul_inv_cancel a ha := by
    have hn : norm a ≠ 0 := mt (norm_eq_zero_iff a).mp ha
    apply K.ext
    · simp only [mul_c0, inv_c0, inv_c1, one_c0]
      have : a.c0 * (a.c0 * (norm a)⁻¹) + 7 * (a.c1 * -(a.c1 * (norm a)⁻¹)) =
          norm a * (norm a)⁻¹ := by unfold norm; ring
      rw [this, mul_inv_cancel₀ hn]
    · simp only [mul_c1, inv_c0, inv_c1, one_c1]
      ring
  div_eq_mul_inv _ _ := rfl
  nnratCast_def q := by
    apply K.ext
    · simp only [nnratCast_c0, div_c0, mul_c0, natCast_c0, natCast_c1]
      have h : (⟨(q.den : Fp), 0⟩ : K)⁻¹ = ⟨(q.den : Fp)⁻¹, 0⟩ := embed_inv _
      change (q : Fp) = (q.num : Fp) * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c0 +
        7 * (0 * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c1)
      rw [h, NNRat.cast_def, div_eq_mul_inv]
      simp
    · simp only [nnratCast_c1, div_c1, mul_c1, natCast_c0, natCast_c1]
      have h : (⟨(q.den : Fp), 0⟩ : K)⁻¹ = ⟨(q.den : Fp)⁻¹, 0⟩ := embed_inv _
      change (0 : Fp) = (q.num : Fp) * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c1 +
        0 * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c0
      rw [h]; simp
  ratCast_def q := by
    apply K.ext
    · simp only [ratCast_c0, div_c0, mul_c0, intCast_c0, intCast_c1]
      have h : (⟨(q.den : Fp), 0⟩ : K)⁻¹ = ⟨(q.den : Fp)⁻¹, 0⟩ := embed_inv _
      change (q : Fp) = (q.num : Fp) * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c0 +
        7 * (0 * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c1)
      rw [h, Rat.cast_def, div_eq_mul_inv]
      simp
    · simp only [ratCast_c1, div_c1, mul_c1, intCast_c0, intCast_c1]
      have h : (⟨(q.den : Fp), 0⟩ : K)⁻¹ = ⟨(q.den : Fp)⁻¹, 0⟩ := embed_inv _
      change (0 : Fp) = (q.num : Fp) * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c1 +
        0 * ((⟨(q.den : Fp), 0⟩ : K)⁻¹).c0
      rw [h]; simp
  nnqsmul q a := ⟨(q : Fp) * a.c0, (q : Fp) * a.c1⟩
  nnqsmul_def q a := K.ext (by simp) (by simp)
  qsmul q a := ⟨(q : Fp) * a.c0, (q : Fp) * a.c1⟩
  qsmul_def q a := K.ext (by simp) (by simp)

/-- Canonical equivalence `K ≃ Fp × Fp`. -/
def equivProd : K ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype K := Fintype.ofEquiv (Fp × Fp) equivProd.symm

/-- Canonical embedding `Fp →+* K`. -/
def embedHom : Fp →+* K where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

lemma card_K : Fintype.card K = Goldilocks.order ^ 2 := by
  have h1 : Fintype.card K = Fintype.card (Fp × Fp) := Fintype.card_congr equivProd
  have h2 : Fintype.card (Fp × Fp) = Fintype.card Fp * Fintype.card Fp := Fintype.card_prod Fp Fp
  have h3 : Fintype.card Fp = Aiur.Library.U32.Goldilocks.modulus := by
    convert ZMod.card Aiur.Library.U32.Goldilocks.modulus
  rw [h1, h2, h3, sq, goldilocks_order_eq]

end K

/-! ## 2. Executable `CertiFri.P3.Goldilocks` → `Fp` Refinement -/

def baseToFp (a : Goldilocks) : Fp := (a.toNat : Fp)

private lemma natCast_p : (Goldilocks.order : Fp) = 0 := by
  rw [goldilocks_order_eq]; exact ZMod.natCast_self _

private lemma ofUInt64_toFp (x : UInt64) :
    baseToFp (Goldilocks.ofUInt64 x) = (x.toNat : Fp) := by
  unfold baseToFp Goldilocks.ofUInt64 Goldilocks.toNat
  split_ifs with h
  · rfl
  · have hle : (0xFFFFFFFF00000001 : UInt64) ≤ x := UInt64.not_lt.mp h
    have hsub : (x - 0xFFFFFFFF00000001).toNat = x.toNat - Goldilocks.order := by
      rw [UInt64.toNat_sub_of_le _ _ hle, p64_toNat]
    have hge : Goldilocks.order ≤ x.toNat := by
      rw [← p64_toNat]; exact UInt64.le_iff_toNat_le.mp hle
    rw [hsub, Nat.cast_sub hge, natCast_p, sub_zero]

private lemma baseToFp_inj : Function.Injective baseToFp := by
  intro a b h
  have ha : a.toNat < Aiur.Library.U32.Goldilocks.modulus := a.toNat_lt_order
  have hb : b.toNat < Aiur.Library.U32.Goldilocks.modulus := b.toNat_lt_order
  have hmod := (ZMod.natCast_eq_natCast_iff' a.toNat b.toNat _).mp h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
  exact Goldilocks.ext (UInt64.toNat_inj.mp hmod)

private lemma baseToFp_add (a b : Goldilocks) :
    baseToFp (Goldilocks.add a b) = baseToFp a + baseToFp b := by
  unfold Goldilocks.add
  dsimp only
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hb : b.val.toNat < Goldilocks.order := b.toNat_lt_order
  have hbp : b.val ≤ 0xFFFFFFFF00000001 :=
    UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
  have hnb : (0xFFFFFFFF00000001 - b.val).toNat = Goldilocks.order - b.val.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hbp, p64_toNat]
  split_ifs with h
  · rw [ofUInt64_toFp, UInt64.toNat_sub_of_le _ _ h, hnb]
    have hle : Goldilocks.order - b.val.toNat ≤ a.val.toNat := by
      rw [← hnb]; exact UInt64.le_iff_toNat_le.mp h
    have heq : a.val.toNat - (Goldilocks.order - b.val.toNat) + Goldilocks.order =
        a.val.toNat + b.val.toNat := by omega
    have hcast : ((a.val.toNat - (Goldilocks.order - b.val.toNat) + Goldilocks.order : Nat) : Fp) =
        ((a.val.toNat + b.val.toNat : Nat) : Fp) := congrArg Nat.cast heq
    simpa [Nat.cast_add, natCast_p, baseToFp, Goldilocks.toNat] using hcast
  · rw [ofUInt64_toFp]
    have hlt : a.val.toNat < Goldilocks.order - b.val.toNat := by
      have := mt UInt64.le_iff_toNat_le.mpr h
      rw [hnb] at this; omega
    have hsum : (a.val + b.val).toNat = a.val.toNat + b.val.toNat := by
      rw [UInt64.toNat_add]
      have : a.val.toNat + b.val.toNat < 2 ^ 64 := by
        unfold Goldilocks.order at *; omega
      exact Nat.mod_eq_of_lt this
    rw [hsum, Nat.cast_add]; rfl

private lemma baseToFp_sub (a b : Goldilocks) :
    baseToFp (Goldilocks.sub a b) = baseToFp a - baseToFp b := by
  unfold Goldilocks.sub
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hb : b.val.toNat < Goldilocks.order := b.toNat_lt_order
  split_ifs with h
  · rw [ofUInt64_toFp, UInt64.toNat_sub_of_le _ _ h]
    have hle : b.val.toNat ≤ a.val.toNat := UInt64.le_iff_toNat_le.mp h
    rw [Nat.cast_sub hle]; rfl
  · rw [ofUInt64_toFp]
    have hlt : a.val.toNat < b.val.toNat := by
      have := mt UInt64.le_iff_toNat_le.mpr h; omega
    have hbp : b.val ≤ 0xFFFFFFFF00000001 :=
      UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
    have hnb : (0xFFFFFFFF00000001 - b.val).toNat = Goldilocks.order - b.val.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hbp, p64_toNat]
    have hsum : (a.val + (0xFFFFFFFF00000001 - b.val)).toNat =
        a.val.toNat + (Goldilocks.order - b.val.toNat) := by
      rw [UInt64.toNat_add, hnb]
      have : a.val.toNat + (Goldilocks.order - b.val.toNat) < 2 ^ 64 := by
        unfold Goldilocks.order at *; omega
      exact Nat.mod_eq_of_lt this
    rw [hsum]
    have heq : (a.val.toNat + (Goldilocks.order - b.val.toNat)) + b.val.toNat =
        a.val.toNat + Goldilocks.order := by omega
    have hcast : (((a.val.toNat + (Goldilocks.order - b.val.toNat)) + b.val.toNat : Nat) : Fp) =
        ((a.val.toNat + Goldilocks.order : Nat) : Fp) := congrArg Nat.cast heq
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, natCast_p, add_zero] at hcast
    exact eq_sub_of_add_eq (by rw [Nat.cast_add]; exact hcast)

private lemma baseToFp_neg (a : Goldilocks) :
    baseToFp (Goldilocks.neg a) = -baseToFp a := by
  unfold Goldilocks.neg
  rw [ofUInt64_toFp]
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hap : a.val ≤ 0xFFFFFFFF00000001 :=
    UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
  rw [UInt64.toNat_sub_of_le _ _ hap, p64_toNat]
  rw [Nat.cast_sub (le_of_lt ha), natCast_p, zero_sub]; rfl

private lemma uint64_and_eps (x : UInt64) : (x &&& 0xFFFFFFFF).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private lemma uint64_shr32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]
  have : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [this, Nat.shiftRight_eq_div_pow]

private lemma mul_lt_two_pow_64 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x * y ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

private lemma mulHigh_spec (a b : UInt64) :
    (Goldilocks.mulHigh a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  unfold Goldilocks.mulHigh
  dsimp only
  set a0 := a &&& 0xFFFFFFFF
  set a1 := a >>> 32
  set b0 := b &&& 0xFFFFFFFF
  set b1 := b >>> 32
  have ha0 : a0.toNat = a.toNat % 2 ^ 32 := uint64_and_eps a
  have ha1 : a1.toNat = a.toNat / 2 ^ 32 := uint64_shr32 a
  have hb0 : b0.toNat = b.toNat % 2 ^ 32 := uint64_and_eps b
  have hb1 : b1.toNat = b.toNat / 2 ^ 32 := uint64_shr32 b
  have ha_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have hb_lt : b.toNat < 2 ^ 64 := b.toNat_lt
  have ha0_lt : a0.toNat < 2 ^ 32 := by rw [ha0]; exact Nat.mod_lt _ (by decide)
  have ha1_lt : a1.toNat < 2 ^ 32 := by rw [ha1]; omega
  have hb0_lt : b0.toNat < 2 ^ 32 := by rw [hb0]; exact Nat.mod_lt _ (by decide)
  have hb1_lt : b1.toNat < 2 ^ 32 := by rw [hb1]; omega
  have hp00 : a0.toNat * b0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := mul_lt_two_pow_64 ha0_lt hb0_lt
  have hp01 : a0.toNat * b1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := mul_lt_two_pow_64 ha0_lt hb1_lt
  have hp10 : a1.toNat * b0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := mul_lt_two_pow_64 ha1_lt hb0_lt
  have hp11 : a1.toNat * b1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := mul_lt_two_pow_64 ha1_lt hb1_lt
  have hmul_a0b0 : (a0 * b0).toNat = a0.toNat * b0.toNat := by
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hmul_a0b1 : (a0 * b1).toNat = a0.toNat * b1.toNat := by
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hmul_a1b0 : (a1 * b0).toNat = a1.toNat * b0.toNat := by
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hmul_a1b1 : (a1 * b1).toNat = a1.toNat * b1.toNat := by
    rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  set mid := a0 * b1 + ((a0 * b0) >>> 32)
  have hmid : mid.toNat = a0.toNat * b1.toNat + (a0.toNat * b0.toNat) / 2 ^ 32 := by
    change (a0 * b1 + ((a0 * b0) >>> 32)).toNat = _
    rw [UInt64.toNat_add, hmul_a0b1, uint64_shr32 (a0 * b0), hmul_a0b0]
    exact Nat.mod_eq_of_lt (by omega)
  set mid2 := a1 * b0 + (mid &&& 0xFFFFFFFF)
  have hmid2 : mid2.toNat = a1.toNat * b0.toNat + mid.toNat % 2 ^ 32 := by
    change (a1 * b0 + (mid &&& 0xFFFFFFFF)).toNat = _
    rw [UInt64.toNat_add, hmul_a1b0, uint64_and_eps mid]
    have hm_lt : mid.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    exact Nat.mod_eq_of_lt (by omega)
  have hmid_lt : mid.toNat < 2 ^ 64 := mid.toNat_lt
  have hmid2_lt : mid2.toNat < 2 ^ 64 := mid2.toNat_lt
  have hres : (a1 * b1 + (mid >>> 32) + (mid2 >>> 32)).toNat =
      a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 + mid2.toNat / 2 ^ 32 := by
    have hstep1 : (a1 * b1 + (mid >>> 32)).toNat = a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, hmul_a1b1, uint64_shr32 mid]
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, hstep1, uint64_shr32 mid2]
    exact Nat.mod_eq_of_lt (by omega)
  change (a1 * b1 + (mid >>> 32) + (mid2 >>> 32)).toNat * 2 ^ 64 + (a * b).toNat = _
  rw [hres, UInt64.toNat_mul]
  have ha_split : a.toNat = a1.toNat * 2 ^ 32 + a0.toNat := by rw [ha1, ha0]; omega
  have hb_split : b.toNat = b1.toNat * 2 ^ 32 + b0.toNat := by rw [hb1, hb0]; omega
  have hprod : a.toNat * b.toNat =
      (a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 + mid2.toNat / 2 ^ 32) * 2 ^ 64 +
      ((mid2.toNat % 2 ^ 32) * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32) := by
    have hm1 := Nat.div_add_mod mid.toNat (2 ^ 32)
    have hm2 := Nat.div_add_mod mid2.toNat (2 ^ 32)
    have h00 := Nat.div_add_mod (a0.toNat * b0.toNat) (2 ^ 32)
    rw [ha_split, hb_split]
    zify at hm1 hm2 h00 hmid hmid2 ⊢
    linear_combination -h00 - (2 ^ 32 : Int) * hmid - (2 ^ 32 : Int) * hm1 -
      (2 ^ 32 : Int) * hmid2 - (2 ^ 32 : Int) * hm2
  have hrem_lt : (mid2.toNat % 2 ^ 32) * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32 < 2 ^ 64 := by
    have := Nat.mod_lt mid2.toNat (show 0 < 2 ^ 32 by decide)
    have := Nat.mod_lt (a0.toNat * b0.toNat) (show 0 < 2 ^ 32 by decide)
    omega
  have hmod : (a.toNat * b.toNat) % 2 ^ 64 =
      (mid2.toNat % 2 ^ 32) * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32 := by
    rw [hprod, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hrem_lt]
  rw [hmod]
  omega

private lemma pow64_mod_p : ((2 ^ 64 : Nat) : Fp) = ((2 ^ 32 - 1 : Nat) : Fp) := by decide

private lemma reduce128_toFp (hi lo : UInt64) :
    baseToFp (Goldilocks.reduce128 hi lo) =
      (hi.toNat : Fp) * ((2 ^ 64 : Nat) : Fp) + (lo.toNat : Fp) := by
  unfold Goldilocks.reduce128
  dsimp only
  rw [ofUInt64_toFp]
  set hh := hi >>> 32
  set hl := hi &&& 0xFFFFFFFF
  have hhh : hh.toNat = hi.toNat / 2 ^ 32 := uint64_shr32 hi
  have hhl : hl.toNat = hi.toNat % 2 ^ 32 := uint64_and_eps hi
  have hhi_split : hi.toNat = hh.toNat * 2 ^ 32 + hl.toNat := by rw [hhh, hhl]; omega
  have hhh_lt : hh.toNat < 2 ^ 32 := by rw [hhh]; have := hi.toNat_lt; omega
  have hhl_lt : hl.toNat < 2 ^ 32 := by rw [hhl]; exact Nat.mod_lt _ (by decide)
  set t0 := if lo < hh then lo - hh - 0xFFFFFFFF else lo - hh
  have ht0 : (t0.toNat : Fp) = (lo.toNat : Fp) - (hh.toNat : Fp) := by
    dsimp only [t0]
    split_ifs with hlt
    · have hlo_lt : lo.toNat < hh.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hsub1 : (lo - hh).toNat = 2 ^ 64 + lo.toNat - hh.toNat := by
        rw [UInt64.toNat_sub]
        have : lo.toNat < 2 ^ 64 := lo.toNat_lt
        omega
      have hge_eps : (0xFFFFFFFF : UInt64) ≤ lo - hh := by
        rw [UInt64.le_iff_toNat_le, hsub1, eps_toNat]; omega
      rw [UInt64.toNat_sub_of_le _ _ hge_eps, hsub1, eps_toNat]
      have hnat : (2 ^ 64 + lo.toNat - hh.toNat - (2 ^ 32 - 1)) + hh.toNat =
          lo.toNat + Goldilocks.order := by
        unfold Goldilocks.order; omega
      have hc := congrArg (Nat.cast (R := Fp)) hnat
      simp only [Nat.cast_add, natCast_p, add_zero] at hc
      exact eq_sub_of_add_eq hc
    · have hle : hh ≤ lo := UInt64.not_lt.mp hlt
      rw [UInt64.toNat_sub_of_le _ _ hle, Nat.cast_sub (UInt64.le_iff_toNat_le.mp hle)]
  set t1 := hl * 0xFFFFFFFF
  have ht1 : t1.toNat = hl.toNat * (2 ^ 32 - 1) := by
    dsimp only [t1]
    rw [UInt64.toNat_mul, eps_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  set t2 := t0 + t1
  have ht2_res : ((if t2 < t1 then t2 + 0xFFFFFFFF else t2).toNat : Fp) =
      (t0.toNat : Fp) + (t1.toNat : Fp) := by
    split_ifs with hcarry
    · have hsum_ge : 2 ^ 64 ≤ t0.toNat + t1.toNat := by
        have hlt := UInt64.lt_iff_toNat_lt.mp hcarry
        rw [UInt64.toNat_add] at hlt
        by_contra h
        push Not at h
        rw [Nat.mod_eq_of_lt h] at hlt
        omega
      have ht2_val : t2.toNat = t0.toNat + t1.toNat - 2 ^ 64 := by
        rw [UInt64.toNat_add]
        have h0 := t0.toNat_lt; have h1 := t1.toNat_lt
        omega
      have ht2_lt : t2.toNat < t1.toNat := UInt64.lt_iff_toNat_lt.mp hcarry
      have hadd_no_ov : t2.toNat + (2 ^ 32 - 1) < 2 ^ 64 := by
        rw [ht1] at ht2_lt; omega
      rw [UInt64.toNat_add, eps_toNat, Nat.mod_eq_of_lt hadd_no_ov, ht2_val]
      have hnat : (t0.toNat + t1.toNat - 2 ^ 64) + (2 ^ 32 - 1) + Goldilocks.order =
          t0.toNat + t1.toNat := by
        unfold Goldilocks.order; omega
      have hc := congrArg (Nat.cast (R := Fp)) hnat
      rw [Nat.cast_add, Nat.cast_add, natCast_p, add_zero, Nat.cast_add] at hc
      rw [Nat.cast_add]; exact hc
    · have hsum_lt : t0.toNat + t1.toNat < 2 ^ 64 := by
        have hge := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hcarry)
        rw [UInt64.toNat_add] at hge
        by_contra h
        push Not at h
        have h0 := t0.toNat_lt; have h1 := t1.toNat_lt
        omega
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum_lt, Nat.cast_add]
  rw [ht2_res, ht0, ht1, hhi_split, pow64_mod_p]
  have h96' : ((2 ^ 32 : Nat) : Fp) * ((2 ^ 32 - 1 : Nat) : Fp) = -1 := by decide
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  linear_combination -(hh.toNat : Fp) * h96'

private lemma baseToFp_mul (a b : Goldilocks) :
    baseToFp (Goldilocks.mul a b) = baseToFp a * baseToFp b := by
  unfold Goldilocks.mul
  rw [reduce128_toFp]
  have h := mulHigh_spec a.val b.val
  have hc := congrArg (Nat.cast (R := Fp)) h
  simpa [Nat.cast_add, Nat.cast_mul, baseToFp, Goldilocks.toNat] using hc

private lemma invLoop_spec (a : Goldilocks) (ha : baseToFp a ≠ 0)
    (r0 r1 t0 t1 : UInt64) (odd : Bool)
    (hr1_pos : 0 < r1.toNat)
    (hle : r1.toNat ≤ r0.toNat)
    (hr0 : r0.toNat ≤ Goldilocks.order)
    (hinv : t1.toNat * r0.toNat + t0.toNat * r1.toNat = Goldilocks.order)
    (hgcd : Nat.gcd r0.toNat r1.toNat = 1)
    (hr1_eq : (r1.toNat : Fp) = (if odd then -(t1.toNat : Fp) else (t1.toNat : Fp)) * baseToFp a)
    (hr0_eq : (r0.toNat : Fp) = (if odd then (t0.toNat : Fp) else -(t0.toNat : Fp)) * baseToFp a) :
    baseToFp (Goldilocks.invLoop r0 r1 t0 t1 odd) = (baseToFp a)⁻¹ := by
  unfold Goldilocks.invLoop
  by_cases h1 : r1 ≤ 1
  · simp only [h1, ↓reduceDIte]
    have hr1_le1 : r1.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp h1
    have hr1_one : r1.toNat = 1 := by omega
    have heq : r1 = 1 := UInt64.toNat_inj.mp hr1_one
    simp only [heq, ↓reduceIte]
    have ht1_le : t1.toNat ≤ Goldilocks.order := by
      have : r0.toNat ≥ 1 := by omega
      nlinarith only [hinv, this]
    have hcoeff : baseToFp (if odd then Goldilocks.ofUInt64 (0xFFFFFFFF00000001 - t1)
        else Goldilocks.ofUInt64 t1) = (if odd then -(t1.toNat : Fp) else (t1.toNat : Fp)) := by
      cases odd
      · simp [ofUInt64_toFp]
      · simp only [ite_true, ofUInt64_toFp]
        have ht1p : t1 ≤ 0xFFFFFFFF00000001 := UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; exact ht1_le)
        rw [UInt64.toNat_sub_of_le _ _ ht1p, p64_toNat, Nat.cast_sub ht1_le, natCast_p, zero_sub]
    rw [hcoeff]
    have hone : (if odd then -(t1.toNat : Fp) else (t1.toNat : Fp)) * baseToFp a = 1 := by
      rw [← hr1_eq, hr1_one]; simp
    exact eq_inv_of_mul_eq_one_left hone
  · simp only [h1, ↓reduceDIte]
    have hr1_gt1 : 1 < r1.toNat := by
      have := mt UInt64.le_iff_toNat_le.mpr h1
      have : (1 : UInt64).toNat = 1 := rfl
      omega
    have hmod_lt : (r0 % r1).toNat < r1.toNat := by
      rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hr1_pos
    have hmod_pos : 0 < (r0 % r1).toNat := by
      rw [UInt64.toNat_mod]
      by_contra h0
      have hdiv : r1.toNat ∣ r0.toNat := Nat.dvd_of_mod_eq_zero (by omega)
      have := Nat.gcd_eq_right hdiv
      omega
    have hdivmod : r0.toNat = (r0.toNat / r1.toNat) * r1.toNat + r0.toNat % r1.toNat := by
      have := Nat.div_add_mod r0.toNat r1.toNat; linarith
    have hq_nat : (r0 / r1).toNat = r0.toNat / r1.toNat := UInt64.toNat_div _ _
    have hrem_nat : (r0 % r1).toNat = r0.toNat % r1.toNat := UInt64.toNat_mod _ _
    have hqt1_le : (r0.toNat / r1.toNat) * t1.toNat + t0.toNat ≤ Goldilocks.order := by
      have hmul : (t0.toNat + (r0.toNat / r1.toNat) * t1.toNat) * r1.toNat +
          t1.toNat * (r0.toNat % r1.toNat) = Goldilocks.order := by
        nlinarith only [hdivmod, hinv]
      have h1le : (t0.toNat + (r0.toNat / r1.toNat) * t1.toNat) * 1 ≤
          (t0.toNat + (r0.toNat / r1.toNat) * t1.toNat) * r1.toNat :=
        Nat.mul_le_mul_left _ hr1_pos
      omega
    have hord_lt : Goldilocks.order < 2 ^ 64 := by unfold Goldilocks.order; decide
    have hqt1_no_ov : ((r0 / r1) * t1).toNat = (r0.toNat / r1.toNat) * t1.toNat := by
      rw [UInt64.toNat_mul, hq_nat]
      exact Nat.mod_eq_of_lt (by omega)
    have ht2_no_ov : (t0 + (r0 / r1) * t1).toNat = t0.toNat + (r0.toNat / r1.toNat) * t1.toNat := by
      rw [UInt64.toNat_add, hqt1_no_ov]
      exact Nat.mod_eq_of_lt (by omega)
    apply invLoop_spec a ha r1 (r0 % r1) t1 (t0 + r0 / r1 * t1) (!odd)
    · exact hmod_pos
    · omega
    · omega
    · rw [ht2_no_ov, hrem_nat]; nlinarith only [hdivmod, hinv]
    · rw [hrem_nat]
      have := Nat.gcd_rec r1.toNat r0.toNat
      rw [Nat.gcd_comm] at this
      rw [Nat.gcd_comm, ← this]; exact hgcd
    · rw [hrem_nat, ht2_no_ov]
      have hsub_cast : ((r0.toNat % r1.toNat : Nat) : Fp) =
          (r0.toNat : Fp) - ((r0.toNat / r1.toNat : Nat) : Fp) * (r1.toNat : Fp) := by
        have hc := congrArg (Nat.cast (R := Fp)) hdivmod
        push_cast at hc
        linear_combination -hc
      rw [hsub_cast, hr0_eq, hr1_eq]
      cases odd <;> simp <;> ring
    · cases odd <;> simpa using hr1_eq
termination_by r1.toNat

private lemma baseToFp_inv (a : Goldilocks) :
    baseToFp (Goldilocks.inv a) = (baseToFp a)⁻¹ := by
  by_cases ha : baseToFp a = 0
  · have hz : baseToFp Goldilocks.zero = 0 := by decide
    have ha0 : a = Goldilocks.zero := baseToFp_inj (ha.trans hz.symm)
    subst ha0
    rw [hz, inv_zero]
    unfold Goldilocks.inv Goldilocks.invLoop
    decide
  · have ha_pos : 0 < a.toNat := by
      by_contra h0
      have : a.toNat = 0 := by omega
      apply ha; simp [baseToFp, this]
    have ha_lt : a.toNat < Goldilocks.order := a.toNat_lt_order
    have hprime : Nat.Prime Goldilocks.order := by
      rw [goldilocks_order_eq]; exact Aiur.Library.U32.Goldilocks.modulus_prime
    have hcop : Nat.gcd Goldilocks.order a.toNat = 1 :=
      (hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha_pos ha_lt)).gcd_eq_one
    unfold Goldilocks.inv
    apply invLoop_spec a ha 0xFFFFFFFF00000001 a.val 0 1 false
    · exact ha_pos
    · rw [p64_toNat]; exact le_of_lt ha_lt
    · rw [p64_toNat]
    · rw [p64_toNat]; simp
    · rw [p64_toNat]; exact hcop
    · simp [baseToFp, Goldilocks.toNat]
    · rw [p64_toNat]; simp [natCast_p]

/-! ## 3. `CertiFri.Exec.FieldModel` and `WellFormed` Instances -/

private lemma baseToFp_zero : baseToFp Goldilocks.zero = 0 := by decide
private lemma baseToFp_one : baseToFp Goldilocks.one = 1 := by decide

def goldilocksBaseRefines : Refines Goldilocks K where
  toModel a := K.embedHom (baseToFp a)
  map_zero := by apply K.ext <;> [exact baseToFp_zero; rfl]
  map_one := by apply K.ext <;> [exact baseToFp_one; rfl]
  map_add a b := by change K.embedHom (baseToFp (Goldilocks.add a b)) = _; rw [baseToFp_add, map_add]
  map_sub a b := by change K.embedHom (baseToFp (Goldilocks.sub a b)) = _; rw [baseToFp_sub, map_sub]
  map_mul a b := by change K.embedHom (baseToFp (Goldilocks.mul a b)) = _; rw [baseToFp_mul, map_mul]
  map_neg a := by change K.embedHom (baseToFp (Goldilocks.neg a)) = _; rw [baseToFp_neg, map_neg]
  map_inv a := by change K.embedHom (baseToFp (Goldilocks.inv a)) = _; rw [baseToFp_inv, map_inv₀]
  beq_iff a b := by
    change decide (a = b) = true ↔ K.embedHom (baseToFp a) = K.embedHom (baseToFp b)
    rw [decide_eq_true_iff]
    constructor
    · intro h; rw [h]
    · intro h
      have h0 : baseToFp a = baseToFp b := congrArg K.c0 h
      exact baseToFp_inj h0

def extToModel (e : GoldilocksExt) : K := ⟨baseToFp e.c0, baseToFp e.c1⟩

def goldilocksExtRefines : Refines GoldilocksExt K where
  toModel := extToModel
  map_zero := by apply K.ext <;> exact baseToFp_zero
  map_one := by apply K.ext <;> [exact baseToFp_one; exact baseToFp_zero]
  map_add a b := by
    have h : extToModel (GoldilocksExt.add a b) = extToModel a + extToModel b := by
      unfold extToModel GoldilocksExt.add
      dsimp only
      rw [baseToFp_add, baseToFp_add]; rfl
    exact h
  map_sub a b := by
    have h : extToModel (GoldilocksExt.sub a b) = extToModel a - extToModel b := by
      unfold extToModel GoldilocksExt.sub
      dsimp only
      rw [baseToFp_sub, baseToFp_sub]; rfl
    exact h
  map_mul a b := by
    have h7 : baseToFp GoldilocksExt.nonResidue = 7 := by decide
    have h : extToModel (GoldilocksExt.mul a b) = extToModel a * extToModel b := by
      unfold extToModel GoldilocksExt.mul
      dsimp only
      rw [baseToFp_add, baseToFp_add, baseToFp_mul, baseToFp_mul, baseToFp_mul,
        baseToFp_mul, baseToFp_mul, h7]; rfl
    exact h
  map_neg a := by
    have h : extToModel (GoldilocksExt.neg a) = -(extToModel a) := by
      unfold extToModel GoldilocksExt.neg
      dsimp only
      rw [baseToFp_neg, baseToFp_neg]; rfl
    exact h
  map_inv a := by
    have h7 : baseToFp GoldilocksExt.nonResidue = 7 := by decide
    have h : extToModel (GoldilocksExt.inv a) = (extToModel a)⁻¹ := by
      unfold extToModel GoldilocksExt.inv
      dsimp only
      rw [baseToFp_neg, baseToFp_mul, baseToFp_mul, baseToFp_inv, baseToFp_sub,
        baseToFp_mul, baseToFp_mul, baseToFp_mul, h7]; rfl
    exact h
  beq_iff a b := by
    change decide (a = b) = true ↔ extToModel a = extToModel b
    rw [decide_eq_true_iff]
    constructor
    · intro h; rw [h]
    · intro h
      have hc0 := baseToFp_inj (congrArg K.c0 h)
      have hc1 := baseToFp_inj (congrArg K.c1 h)
      cases a; cases b; simp_all

private lemma baseToFp_surj : Function.Surjective baseToFp := by
  intro y
  have hy : y.val < Goldilocks.order := by
    rw [goldilocks_order_eq]; exact ZMod.val_lt y
  have hy64 : y.val < 2 ^ 64 := lt_trans hy (by unfold Goldilocks.order; decide)
  have hofNat : (UInt64.ofNat y.val).toNat = y.val := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hy64]
  have hlt : UInt64.ofNat y.val < 0xFFFFFFFF00000001 := by
    rw [UInt64.lt_iff_toNat_lt, hofNat, p64_toNat]
    exact hy
  refine ⟨⟨UInt64.ofNat y.val, hlt⟩, ?_⟩
  unfold baseToFp Goldilocks.toNat
  dsimp only
  rw [hofNat]
  exact ZMod.natCast_zmod_val y

/-- Certified `CertiFri.Exec.FieldModel` instance for `CertiFri.P3.{Goldilocks, GoldilocksExt}` over `K`. -/
def goldilocksFieldModel : Exec.FieldModel Goldilocks GoldilocksExt K where
  base := goldilocksBaseRefines
  ext := goldilocksExtRefines
  embed a := K.ext rfl baseToFp_zero.symm
  surj y := by
    obtain ⟨a0, h0⟩ := baseToFp_surj y.c0
    obtain ⟨a1, h1⟩ := baseToFp_surj y.c1
    exact ⟨⟨a0, a1⟩, K.ext h0 h1⟩

/-- Every entry `k ≤ 32` of `Goldilocks.twoAdicGenerators` is a primitive `2^k`-th root of unity in `Fp`. -/
private theorem twoAdicGenerator_isPrimitiveRoot_fp :
    ∀ k : Fin 33, IsPrimitiveRoot (baseToFp (Goldilocks.twoAdicGenerator k.val)) (2 ^ k.val) := by
  have h32 : IsPrimitiveRoot (baseToFp (Goldilocks.twoAdicGenerator 32)) (2 ^ 32) := by
    have hg32 : baseToFp (Goldilocks.twoAdicGenerator 32) = ((1753635133440165772 : Nat) : Fp) := by decide
    have hpow : (baseToFp (Goldilocks.twoAdicGenerator 32)) ^ (2 ^ 31) = -1 := by
      have hsq31 : sqModN Aiur.Library.U32.Goldilocks.modulus 31 1753635133440165772 =
          Aiur.Library.U32.Goldilocks.modulus - 1 := by decide
      rw [hg32, ← sqModN_spec 31 1753635133440165772, hsq31]
      decide
    have h2 : (2 : Nat) ^ 32 = 2 * 2 ^ 31 := rfl
    have hneg : (-1 : Fp) ≠ 1 := by decide
    rw [IsPrimitiveRoot.iff_def]
    refine ⟨by rw [h2, pow_mul', hpow]; norm_num, ?_⟩
    intro l hl
    have hdvd : orderOf (baseToFp (Goldilocks.twoAdicGenerator 32)) ∣ 2 ^ 32 :=
      orderOf_dvd_of_pow_eq_one (by rw [h2, pow_mul', hpow]; norm_num)
    obtain ⟨m, hmle, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hm32 : m = 32 := by
      by_contra hne
      have hml : m ≤ 31 := by omega
      have hdiv31 : orderOf (baseToFp (Goldilocks.twoAdicGenerator 32)) ∣ 2 ^ 31 := by
        rw [hm]; exact Nat.pow_dvd_pow 2 hml
      have h1 : (baseToFp (Goldilocks.twoAdicGenerator 32)) ^ (2 ^ 31) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hdiv31
      exact hneg (hpow.symm.trans h1)
    rw [← hm32, ← hm]
    exact orderOf_dvd_of_pow_eq_one hl
  have hsq_nat : ∀ k : Fin 32,
      (Goldilocks.twoAdicGenerator k.val).toNat =
      ((Goldilocks.twoAdicGenerator (k.val + 1)).toNat *
       (Goldilocks.twoAdicGenerator (k.val + 1)).toNat) % Aiur.Library.U32.Goldilocks.modulus := by
    decide
  have hsq : ∀ k : Fin 32,
      baseToFp (Goldilocks.twoAdicGenerator k.val) =
      (baseToFp (Goldilocks.twoAdicGenerator (k.val + 1))) ^ 2 := by
    intro k
    unfold baseToFp
    rw [hsq_nat k, ZMod.natCast_mod, Nat.cast_mul, sq]
  intro k
  have hpow_eq : ∀ d : Nat, (hd : d ≤ 32) →
      baseToFp (Goldilocks.twoAdicGenerator (32 - d)) =
      (baseToFp (Goldilocks.twoAdicGenerator 32)) ^ (2 ^ d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have hstep := hsq ⟨32 - (d + 1), by omega⟩
      have heq : 32 - (d + 1) + 1 = 32 - d := by omega
      rw [hstep, heq, ih (by omega), ← pow_mul, ← pow_succ]
  have hk_eq : k.val = 32 - (32 - k.val) := by omega
  rw [hk_eq, hpow_eq (32 - k.val) (by omega)]
  have hmul : 2 ^ (32 - k.val) * 2 ^ (32 - (32 - k.val)) = 2 ^ 32 := by
    rw [← pow_add]; congr 1; omega
  have hdiv : 2 ^ 32 / 2 ^ (32 - k.val) = 2 ^ (32 - (32 - k.val)) :=
    Nat.div_eq_of_eq_mul_right (Nat.pow_pos (by decide)) hmul.symm
  rw [← hdiv]
  exact h32.pow_of_dvd (pow_ne_zero (32 - k.val) (by decide : (2 : Nat) ≠ 0)) ⟨_, hmul.symm⟩

/-- Certified `CertiFri.Exec.WellFormed` for `goldilocksFieldModel` on any shape
with `logMaxHeight ≤ 32`. -/
theorem goldilocksWellFormed (params : FriParams) (shape : Fri.ClaimShape)
    (hn : Fri.logMaxHeight params.logBlowup shape ≤ 32) :
    Exec.WellFormed goldilocksFieldModel params shape where
  prim := by
    have hfp := twoAdicGenerator_isPrimitiveRoot_fp ⟨Fri.logMaxHeight params.logBlowup shape, by omega⟩
    exact hfp.map_of_injective K.embedHom.injective
  shift_ne := by
    intro h
    have h0 : baseToFp Goldilocks.generator = 0 := congrArg K.c0 h
    exact (by decide : baseToFp Goldilocks.generator ≠ 0) h0

end Ix.Cert.MultiStark

