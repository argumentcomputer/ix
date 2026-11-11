module

public import IxC.Kernel.Model.Open.Core
import IxC.Kernel.Verify.Shift

@[expose] public section

/-!
# The rules' soundness over the public `Model`: proof irrelevance and equality

* `DefEq.proofIrrel`: two terms whose types are propositions denote the proof point.
* `Red.deltaThm`: a theorem and its value are both members of its statement, a proposition,
  so they denote alike.
* `Red.eqProof`: a proof of `a = b` makes `a` and `b` denote alike (`Model.eq_equality`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-- A term with no free variable has every assignment as a context. -/
theorem Ctx.of_closed {σ : Nat → V} {e : Expr md} (hf : e.hasFvar = false) : Ctx M φ σ e := by
  intro l hl
  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hf] at hl
  exact nomatch hl

/-- **A proof is the proof point**: a graded denotation of a term whose type's type reduces to
`Sort u`, with `u` of value `0`, is `pt`. -/
theorem proof_pt {d : Nat} {a ta tta : Expr md} {u : Level} (ha : InferIOS M φ d a ta)
    (hta : InferIOS M φ d ta tta) (hu : RedS M φ d tta (.sort u)) (hu0 : Level.eval φ u = 0)
    (hfa : Frame d a) {σ : Nat → V} (hC : Ctx M φ σ a) {v : V} (hv : Den M φ σ a v)
    (hg : Gr M φ σ a) : v = pt := by
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨hftta, hsubtta, kta⟩ := hta hfta
  obtain ⟨-, -, ku⟩ := hu hftta
  obtain ⟨T, hT, hgT, hvT⟩ := ka σ hC v hv hg
  obtain ⟨TT, hTT, hgTT, hTTT⟩ := kta σ (hC.of_subset hsubta) T hT hgT
  obtain ⟨hTTu, -⟩ := ku σ ((hC.of_subset hsubta).of_subset hsubtta) TT hTT hgTT
  cases hTTu
  rw [hu0, univ_zero] at hTTT
  exact eq_pt_of_mem_univZero hTTT hvT

/-- **Proof irrelevance** (`DefEq.proofIrrel`). -/
theorem DefEq.proofIrrel_sound {d : Nat} {a ta tta b tb ttb : Expr md} {u v : Level}
    (ha : InferIOS M φ d a ta) (hta : InferIOS M φ d ta tta) (hu : RedS M φ d tta (.sort u))
    (hu0 : ∀ φ, Level.eval φ u = 0)
    (hb : InferIOS M φ d b tb) (htb : InferIOS M φ d tb ttb) (hv : RedS M φ d ttb (.sort v))
    (hv0 : ∀ φ, Level.eval φ v = 0) : DefEqS M φ d a b :=
  fun hfa hfb _ hCa hCb _ _ hx hy hga hgb =>
    (proof_pt ha hta hu (hu0 φ) hfa hCa hx hga).trans
      (proof_pt hb htb hv (hv0 φ) hfb hCb hy hgb).symm

/-- **A theorem unfolds to its value** (`Red.deltaThm`): both are members of the theorem's
statement, which is a proposition, so both denote the proof point. -/
theorem Red.deltaThm_sound (hsc : StoredClosed env) {d : Nat} {n : Key md} {us : List Level}
    {cv : ConstantVal md} {value vt s : Expr md} {u : Level}
    (hf : env.find? n = some (.thmInfo cv value)) (hus : us.length = cv.levelParams.length)
    (hvf : value.hasFvar = false) (hvb : value.looseBVarsBounded 0 = true)
    (hvt : InferFullS M φ d (value.instantiateLevelParams cv.levelParams us) vt)
    (hd : DefEqS M φ d vt (cv.type.instantiateLevelParams cv.levelParams us))
    (hs : InferFullS M φ d (cv.type.instantiateLevelParams cv.levelParams us) s)
    (hr : RedS M φ d s (.sort u)) (hu0 : ∀ φ, Level.eval φ u = 0) :
    RedS M φ d (.const n us) (value.instantiateLevelParams cv.levelParams us) := by
  have hvf' : (value.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hvf
  have hvb' : (value.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hvb
  intro _
  refine ⟨Frame.of_closed hvf' hvb', LeavesSub.of_closed hvf', fun σ _ v hv _ => ?_⟩
  obtain ⟨hftT, -⟩ := const_type_frame (d := d) (us := us) hsc hf
  obtain ⟨hfvt, hsubvt, kvt⟩ := hvt (Frame.of_closed hvf' hvb')
  obtain ⟨x, X, hx, hgx, hX, hgX, hxX⟩ := kvt σ (Ctx.of_closed hvf')
  obtain ⟨hfs, hsubs, ks⟩ := hs hftT
  have hCT : Ctx M φ σ (cv.type.instantiateLevelParams cv.levelParams us) :=
    Ctx.of_closed (by
      rw [Expr.hasFvar_instantiateLevelParams]
      exact (hsc _ (List.mem_of_find?_eq_some hf)).1.1)
  obtain ⟨T, S, hT, hgT, hS, hgS, hTS⟩ := ks σ hCT
  obtain ⟨-, -, ku⟩ := hr hfs
  obtain ⟨hSu, -⟩ := ku σ (hCT.of_subset hsubs) S hS hgS
  cases hSu
  rw [hu0 φ, univ_zero] at hTS
  obtain rfl := hd hfvt hftT σ ((Ctx.of_closed hvf').of_subset hsubvt) hCT _ _ hX hT hgX hgT
  obtain ⟨T', hc, hT', -, hcT'⟩ := const_typed (M := M) (φ := φ) hsc hf hus σ
  obtain rfl := DenotesO.functional hT' hT
  obtain rfl := DenotesO.functional hv hc
  rw [eq_pt_of_mem_univZero hTS hcT', ← eq_pt_of_mem_univZero hTS hxX]
  exact ⟨hx, hgx⟩

/-- **An equation's proof rewrites its left side** (`Red.eqProof`): `Eq` denotes equality
(`Model.eq_equality`), so a member of `@Eq T a b`'s denotation makes `a` and `b` denote
alike. -/
theorem Red.eqProof_sound {d : Nat} {a b p T ta tb sT : Expr md} {u v : Level}
    (hp : InferFullS M φ d p (.app (.app (.app (.const eqName [u]) T) a) b))
    (hpw : p.wscopedB d = true) (hpb : p.looseBVarsBounded 0 = true)
    (hpl : ∀ l ∈ p.fvarLeaves, l ∈ a.fvarLeaves)
    (hta : InferFullS M φ d a ta) (hdta : DefEqS M φ d ta T)
    (htb : InferFullS M φ d b tb) (hdtb : DefEqS M φ d tb T)
    (hsT : InferFullS M φ d T sT) (hv : RedS M φ d sT (.sort v))
    (huv : ∀ φ, Level.eval φ v = Level.eval φ u) : RedS M φ d a b := by
  intro hfa
  have hfp : Frame d p := ⟨Expr.WScoped.of_wscopedB hpw, hpb, fun l hl => hfa.2.2 l (hpl l hl)⟩
  obtain ⟨hfE, hsubE, kp⟩ := hp hfp
  obtain ⟨hfETa, hfb⟩ := Frame.app_iff.1 hfE
  obtain ⟨hfET, hfa'⟩ := Frame.app_iff.1 hfETa
  obtain ⟨-, hfT⟩ := Frame.app_iff.1 hfET
  have hsubb : LeavesSub b a := fun l hl =>
    hpl l (hsubE l (by simp [Expr.fvarLeaves, hl]))
  have hsubT : LeavesSub T a := fun l hl =>
    hpl l (hsubE l (by simp [Expr.fvarLeaves, hl]))
  refine ⟨hfb, hsubb, fun σ hC x hx _ => ?_⟩
  obtain ⟨P, PT, -, -, hPT, -, hP⟩ := kp σ (hC.of_subset hpl)
  obtain ⟨A, S, hA, hgA, hS, hgS, hAS⟩ := (hsT hfT).2.2 σ (hC.of_subset hsubT)
  obtain ⟨-, -, ksv⟩ := hv (hsT hfT).1
  obtain ⟨hSv, -⟩ := ksv σ ((hC.of_subset hsubT).of_subset (hsT hfT).2.1) S hS hgS
  cases hSv
  rw [huv φ] at hAS
  obtain ⟨x', X, hx', -, hX, hgX, hxX⟩ := (hta hfa).2.2 σ hC
  obtain rfl := DenotesO.functional hx' hx
  obtain rfl := hdta (hta hfa).1 hfT σ (hC.of_subset (hta hfa).2.1) (hC.of_subset hsubT) _ _ hX
    hA hgX hgA
  obtain ⟨y, Y, hy, hgy, hY, hgY, hyY⟩ := (htb hfb).2.2 σ (hC.of_subset hsubb)
  obtain rfl := hdtb (htb hfb).1 hfT σ ((hC.of_subset hsubb).of_subset (htb hfb).2.1)
    (hC.of_subset hsubT) _ _ hY hA hgY hgA
  cases hPT with
  | app hETa hb' =>
    cases hETa with
    | app hET ha' =>
      cases hET with
      | app hE hT' =>
        obtain rfl := DenotesO.functional hT' hA
        obtain rfl := DenotesO.functional ha' hx
        obtain rfl := DenotesO.functional hb' hy
        have heq := M.eq_equality u φ ρ₀ _ _ _ _ (DenotesO.to_denotes hE rfl) hAS hxX hyY
        rw [heq] at hP
        rw [eq_of_mem_eqv hP]
        exact ⟨hy, hgy⟩

end Ix.Kernel.Open
