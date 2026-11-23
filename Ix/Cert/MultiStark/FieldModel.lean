import Aiur.Library.U32.Goldilocks
import CertiFriP3.GoldilocksExt3
import CertiFriProofs.P3.GoldilocksExt3

/-! # Goldilocks & Cubic Extension `CertiFri.Exec.FieldModel` + `WellFormed` (Protocol `v6`)

Delegates directly to `CertiFriProofs.P3.GoldilocksExt3`, proving that
`CertiFri.P3.Goldilocks` and `CertiFri.P3.GoldilocksExt3` implement the
mathematical prime field `Fp = ZMod 18446744069414584321` and its irreducible
cubic trinomial extension `K = Fp[X] / (X^3 - X - 1)` (`|K| = p^3 ≈ 2^192`)
satisfying `CertiFri.Exec.FieldModel` and `CertiFri.Exec.WellFormed` for all
shapes with `logMaxHeight ≤ 32`. Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Prime modulus `p = 2^64 - 2^32 + 1` of the Goldilocks field. -/
abbrev Fp : Type := Aiur.Library.U32.Goldilocks.F

/-- Mathematical cubic extension `K = Fp[X] / (X^3 - X - 1)` (`|K| = p^3 ≈ 2^192`). -/
abbrev K : Type := Fp3Model

namespace K

abbrev c0 : K → Fp := Fp3Model.c0
abbrev c1 : K → Fp := Fp3Model.c1
abbrev c2 : K → Fp := Fp3Model.c2
abbrev embedHom : Fp →+* K := Fp3Model.embedHom
abbrev adjugate : K → K := Fp3Model.adjugate
abbrev norm : K → Fp := Fp3Model.norm

lemma card_K : Fintype.card K = Goldilocks.order ^ 3 :=
  Fp3Model.card_fp3Model

@[simp] lemma natCast_c0 (n : ℕ) : (n : K).c0 = (n : Fp) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.cast_succ, ih]; rfl

@[simp] lemma natCast_c1 (n : ℕ) : (n : K).c1 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.cast_succ, ih]; rfl

@[simp] lemma natCast_c2 (n : ℕ) : (n : K).c2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.cast_succ, ih]; rfl

end K

/-- Canonical embedding of executable `CertiFri.P3.Goldilocks` into `Fp = ZMod p`. -/
def baseToFp (a : Goldilocks) : Fp := Goldilocks.toZMod a

/-- Canonical embedding of executable `CertiFri.P3.GoldilocksExt3` into `K = Fp3Model`. -/
def extToModel (e : GoldilocksExt3) : K := GoldilocksExt3.toModel e

/-- Certified `Refines` instance for `CertiFri.P3.Goldilocks` into `K = Fp3Model`. -/
def goldilocksBaseRefines : Refines Goldilocks K := goldilocksBase_refines_fp3

/-- Certified `Refines` instance for `CertiFri.P3.GoldilocksExt3` into `K = Fp3Model`. -/
def goldilocksExtRefines : Refines GoldilocksExt3 K := goldilocksExt3_refines

/-- Certified `CertiFri.Exec.FieldModel` instance for
`CertiFri.P3.{Goldilocks, GoldilocksExt3}` over `K = Fp3Model`. -/
def goldilocksFieldModel : Exec.FieldModel Goldilocks GoldilocksExt3 K :=
  goldilocksExt3_fieldModel

/-- Certified `CertiFri.Exec.WellFormed` for `goldilocksFieldModel` on any shape
with `logMaxHeight ≤ 32`. -/
theorem goldilocksWellFormed (params : FriParams) (shape : Fri.ClaimShape)
    (hn : Fri.logMaxHeight params.logBlowup shape ≤ 32) :
    Exec.WellFormed goldilocksFieldModel params shape :=
  goldilocksExt3_wellFormed params shape hn

end Ix.Cert.MultiStark
