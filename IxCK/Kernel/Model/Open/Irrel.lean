module

public import IxCK.Kernel.Model.Open.Core
import IxCK.Kernel.Verify.Shift

@[expose] public section

/-!
# The rules' soundness over the public `Model`: proof irrelevance and equality

* `DefEq.proofIrrel`: two terms whose types are propositions denote the proof point.
* `DefEq.proofIrrelTy`: so do two terms whose types are definitionally equal, the first a
  proposition.
* `Red.deltaThm`: a theorem and its value are both members of its statement, a proposition,
  so they denote alike. The rule checks the value at the theorem's own level parameters and
  in the empty context; its premises are read at the assignment the use's levels induce.
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

/-- **Proof irrelevance at a compared type** (`DefEq.proofIrrelTy`): `a`'s type is a
proposition, so `a` denotes the proof point; `b`'s type denotes the same set, so `b` does
too. -/
theorem DefEq.proofIrrelTy_sound {d : Nat} {a ta tta b tb : Expr md} {u : Level}
    (ha : InferIOS M φ d a ta) (hta : InferIOS M φ d ta tta) (hu : RedS M φ d tta (.sort u))
    (hu0 : ∀ φ, Level.eval φ u = 0) (hb : InferIOS M φ d b tb) (hd : DefEqS M φ d ta tb) :
    DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb x y hx hy hga hgb
  obtain ⟨hfta, hsubta, ka⟩ := ha hfa
  obtain ⟨hftta, hsubtta, kta⟩ := hta hfta
  obtain ⟨-, -, ku⟩ := hu hftta
  obtain ⟨T, hT, hgT, hxT⟩ := ka σ hCa x hx hga
  obtain ⟨TT, hTT, hgTT, hTTT⟩ := kta σ (hCa.of_subset hsubta) T hT hgT
  obtain ⟨hTTu, -⟩ := ku σ ((hCa.of_subset hsubta).of_subset hsubtta) TT hTT hgTT
  cases hTTu
  rw [hu0, univ_zero] at hTTT
  obtain ⟨hftb, hsubtb, kb⟩ := hb hfb
  obtain ⟨Tb, hTb, hgTb, hyTb⟩ := kb σ hCb y hy hgb
  obtain rfl := hd hfta hftb σ (hCa.of_subset hsubta) (hCb.of_subset hsubtb) T Tb hT hTb hgT hgTb
  exact (eq_pt_of_mem_univZero hTTT hxT).trans (eq_pt_of_mem_univZero hTTT hyTb).symm

/-- **A theorem unfolds to its value** (`Red.deltaThm`). The rule checks the value against
the theorem's type at the theorem's own level parameters and in the empty context. Read at
the assignment the use's levels induce, the value is a member of the statement, a
proposition, and so is the theorem: both denote the proof point. At `φ` the instantiated
value denotes what the value denotes there (`DenotesO.instantiateLevelParams`). -/
theorem Red.deltaThm_sound (hsc : StoredClosed env) {d : Nat} {n : Key md} {us : List Level}
    {cv : ConstantVal md} {value vt s : Expr md} {u : Level}
    (hf : env.find? n = some (.thmInfo cv value)) (hus : us.length = cv.levelParams.length)
    (hvf : value.hasFvar = false) (hvb : value.looseBVarsBounded 0 = true)
    (hvt : InferFullS M (Level.substFn φ cv.levelParams us) 0 value vt)
    (hd : DefEqS M (Level.substFn φ cv.levelParams us) 0 vt cv.type)
    (hs : InferFullS M (Level.substFn φ cv.levelParams us) 0 cv.type s)
    (hr : RedS M (Level.substFn φ cv.levelParams us) 0 s (.sort u))
    (hu0 : ∀ φ, Level.eval φ u = 0) :
    RedS M φ d (.const n us) (value.instantiateLevelParams cv.levelParams us) := by
  have hcp : CvalParams M.cval env := M.cval_params
  have hvf' : (value.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hvf
  have hvb' : (value.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hvb
  have htf : cv.type.hasFvar = false := (hsc _ (List.mem_of_find?_eq_some hf)).1.1
  have htb : cv.type.looseBVarsBounded 0 = true := (hsc _ (List.mem_of_find?_eq_some hf)).1.2
  intro _
  refine ⟨Frame.of_closed hvf' hvb', LeavesSub.of_closed hvf', fun σ _ v hv _ => ?_⟩
  obtain ⟨hfvt, hsubvt, kvt⟩ := hvt (Frame.of_closed hvf hvb)
  obtain ⟨x, X, hx, hgx, hX, hgX, hxX⟩ := kvt σ (Ctx.of_closed hvf)
  obtain ⟨hfs, hsubs, ks⟩ := hs (Frame.of_closed htf htb)
  have hCT : Ctx M (Level.substFn φ cv.levelParams us) σ cv.type := Ctx.of_closed htf
  obtain ⟨T, S, hT, hgT, hS, hgS, hTS⟩ := ks σ hCT
  obtain ⟨-, -, ku⟩ := hr hfs
  obtain ⟨hSu, -⟩ := ku σ (hCT.of_subset hsubs) S hS hgS
  cases hSu
  rw [hu0, univ_zero] at hTS
  obtain rfl := hd hfvt (Frame.of_closed htf htb) σ ((Ctx.of_closed hvf).of_subset hsubvt) hCT
    _ _ hX hT hgX hgT
  obtain ⟨T', hc, hT', -, hcT'⟩ := const_typed (M := M) (φ := φ) hsc hf hus σ
  obtain rfl := DenotesO.functional ((DenotesO.instantiateLevelParams hcp _ us _ ρ₀ _).1 hT') hT
  obtain rfl := DenotesO.functional hv hc
  rw [eq_pt_of_mem_univZero hTS hcT', ← eq_pt_of_mem_univZero hTS hxX]
  exact ⟨(DenotesO.instantiateLevelParams hcp _ us _ ρ₀ _).2 hx,
    (GradedBy.instantiateLevelParamsO hcp _ us _ ρ₀).2 hgx⟩

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

/-- **Closed conversion between reduced forms** (`Red.defEqClosed`). -/
theorem Red.defEqClosed_sound {d : Nat} {a a' b b' ta tb : Expr md}
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (ha'f : a'.hasFvar = false) (ha'b : a'.looseBVarsBounded 0 = true)
    (hb'f : b'.hasFvar = false) (hb'b : b'.looseBVarsBounded 0 = true)
    (sia : InferFullS M φ 0 a' ta) (sra : RedS M φ 0 a' a)
    (sib : InferFullS M φ 0 b' tb) (srb : RedS M φ 0 b' b)
    (sde : DefEqS M φ 0 a' b') :
    RedS M φ d a b := by
  intro _
  have hfa' : Frame 0 a' := Frame.of_closed ha'f ha'b
  have hfb' : Frame 0 b' := Frame.of_closed hb'f hb'b
  refine ⟨Frame.of_closed hbf hbb, LeavesSub.of_closed hbf, fun σ _ x hx _ => ?_⟩
  obtain ⟨x', _, hx', hgx', -, -, -⟩ := (sia hfa').2.2 σ (Ctx.of_closed ha'f)
  obtain ⟨hxa, -⟩ := (sra hfa').2.2 σ (Ctx.of_closed ha'f) x' hx' hgx'
  obtain rfl := DenotesO.functional hxa hx
  obtain ⟨y', _, hy', hgy', -, -, -⟩ := (sib hfb').2.2 σ (Ctx.of_closed hb'f)
  obtain ⟨hyb, hgyb⟩ := (srb hfb').2.2 σ (Ctx.of_closed hb'f) y' hy' hgy'
  obtain rfl := sde hfa' hfb' σ (Ctx.of_closed ha'f) (Ctx.of_closed hb'f) x' y' hx' hy' hgx' hgy'
  exact ⟨hyb, hgyb⟩

/-- **Closed equality reflection** (`DefEq.eqProof`). -/
theorem DefEq.eqProof_sound {d : Nat} {a b p T ta tb sT : Expr md} {u v : Level}
    (haf : a.hasFvar = false) (hab : a.looseBVarsBounded 0 = true)
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hpf : p.hasFvar = false) (hpb : p.looseBVarsBounded 0 = true)
    (hp : InferFullS M φ 0 p (.app (.app (.app (.const eqName [u]) T) a) b))
    (hta : InferFullS M φ 0 a ta) (hdta : DefEqS M φ 0 ta T)
    (htb : InferFullS M φ 0 b tb) (hdtb : DefEqS M φ 0 tb T)
    (hsT : InferFullS M φ 0 T sT) (hv : RedS M φ 0 sT (.sort v))
    (huv : ∀ φ, Level.eval φ v = Level.eval φ u) :
    DefEqS M φ d a b := by
  intro _ _ σ _ _ x y hx hy _ _
  have hfp : Frame 0 p := Frame.of_closed hpf hpb
  have hfa : Frame 0 a := Frame.of_closed haf hab
  have hfb : Frame 0 b := Frame.of_closed hbf hbb
  obtain ⟨hfE, hsubE, kp⟩ := hp hfp
  obtain ⟨hfETa, -⟩ := Frame.app_iff.1 hfE
  obtain ⟨hfET, -⟩ := Frame.app_iff.1 hfETa
  obtain ⟨-, hfT⟩ := Frame.app_iff.1 hfET
  have hCp : Ctx M φ σ p := Ctx.of_closed hpf
  have hCT : Ctx M φ σ T :=
    hCp.of_subset (fun l hl => hsubE l (by simp [Expr.fvarLeaves, hl]))
  obtain ⟨P, PT, -, -, hPT, -, hP⟩ := kp σ hCp
  obtain ⟨A, S, hA, hgA, hS, hgS, hAS⟩ := (hsT hfT).2.2 σ hCT
  obtain ⟨-, -, ksv⟩ := hv (hsT hfT).1
  obtain ⟨hSv, -⟩ := ksv σ (hCT.of_subset (hsT hfT).2.1) S hS hgS
  cases hSv
  rw [huv φ] at hAS
  obtain ⟨x', X, hx', -, hX, hgX, hxX⟩ := (hta hfa).2.2 σ (Ctx.of_closed haf)
  obtain rfl := DenotesO.functional hx' hx
  obtain rfl := hdta (hta hfa).1 hfT σ ((Ctx.of_closed haf).of_subset (hta hfa).2.1) hCT
    _ _ hX hA hgX hgA
  obtain ⟨y', Y, hy', -, hY, hgY, hyY⟩ := (htb hfb).2.2 σ (Ctx.of_closed hbf)
  obtain rfl := DenotesO.functional hy' hy
  obtain rfl := hdtb (htb hfb).1 hfT σ ((Ctx.of_closed hbf).of_subset (htb hfb).2.1) hCT
    _ _ hY hA hgY hgA
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
        exact eq_of_mem_eqv hP

/-- **Closed level instantiation of a conversion** (`DefEq.instClosed`). -/
theorem DefEq.instClosed_sound {d : Nat} {ks : List LevelParam} {us : List Level}
    {a b : Expr md}
    (haf : a.hasFvar = false) (hab : a.looseBVarsBounded 0 = true)
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (sde : DefEqS M (Level.substFn φ ks us) 0 a b) :
    DefEqS M φ d (a.instantiateLevelParams ks us) (b.instantiateLevelParams ks us) := by
  intro _ _ σ _ _ x y hx hy hgx hgy
  exact sde (Frame.of_closed haf hab) (Frame.of_closed hbf hbb) σ
    (Ctx.of_closed haf) (Ctx.of_closed hbf) x y
    ((DenotesO.instantiateLevelParams M.cval_params ks us a ρ₀ x).1 hx)
    ((DenotesO.instantiateLevelParams M.cval_params ks us b ρ₀ y).1 hy)
    ((GradedBy.instantiateLevelParamsO M.cval_params ks us a ρ₀).1 hgx)
    ((GradedBy.instantiateLevelParamsO M.cval_params ks us b ρ₀).1 hgy)

/-- **`PiRed.ofRed` is sound over `Model`.** -/
theorem PiRed.ofRed_sound {d : Nat} {e e' : Expr md} (h : RedS M φ d e e') :
    PiRedS M φ d e e' := fun hf => (h hf).2.2

/-- **`PiRed.app` is sound over `Model`.** -/
theorem PiRed.app_sound {d : Nat} {f f' a a' : Expr md}
    (sf : PiRedS M φ d f f') (sa : PiRedS M φ d a a') :
    PiRedS M φ d (.app f a) (.app f' a') := by
  intro hf σ hC v hv hg
  obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hf
  cases hv with
  | app hF hX =>
    obtain ⟨hgf, hga, r, A, F', X', B, hF', hX', hm, hx, h0⟩ := Gr.app_iff.1 hg
    have hCf : Ctx M φ σ f := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCa : Ctx M φ σ a := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    obtain ⟨hF₂, hgf₂⟩ := sf hff σ hCf _ hF hgf
    obtain ⟨hX₂, hga₂⟩ := sa hfa σ hCa _ hX hga
    obtain rfl := DenotesO.functional hF' hF
    obtain rfl := DenotesO.functional hX' hX
    exact ⟨.app hF₂ hX₂, Gr.app_iff.2 ⟨hgf₂, hga₂, r, A, _, _, B, hF₂, hX₂, hm, hx, h0⟩⟩

/-- **`PiRed.forallE` is sound over `Model`.** -/
theorem PiRed.forallE_sound {d : Nat} {A A' B B' : Expr md} {mb : BinderMeta}
    (hB'ws : B'.wscopedB d = true)
    (sA : PiRedS M φ d A A')
    (sB : PiRedS M φ (d + 1) (B.instantiate1 (.fvar d A)) (B'.instantiate1 (.fvar d A))) :
    PiRedS M φ d (.forallE A B mb) (.forallE A' B' mb) := by
  intro hf σ hC v hv hg
  have hp := Frame.pi_parts hf
  obtain ⟨hgA, hgB⟩ := Gr.pi_iff.1 hg
  have hCA : Ctx M φ σ A := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCB : Ctx M φ σ B := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hfresh : ∀ l ∈ B.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
  have hfresh' : ∀ l ∈ B'.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped (Expr.WScoped.of_wscopedB hB'ws) l hl).1
  cases hv with
  | pi hA hB hP =>
    obtain ⟨hA', hgA'⟩ := sA hp.ty σ hCA _ hA hgA
    have hstep : ∀ x, x ∈ˢ _ →
        DenotesO M.cval env φ σ (push x ρ₀) B' _ ∧
        GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) B' := fun x hx => by
      have hCx := Ctx.open hp.ty.1 hp.ws hCA hCB hA hx hgA
      have hBx : Den M φ (setAt σ d x) (B.instantiate1 (.fvar d A)) _ :=
        (DenotesO.open_fvar hfresh ρ₀ _).2 (hB x hx)
      have hgBx : Gr M φ (setAt σ d x) (B.instantiate1 (.fvar d A)) :=
        (GradedBy.open_fvarO hfresh ρ₀).2 (hgB _ hA x hx)
      obtain ⟨hB', hgB'⟩ := sB hp.open (setAt σ d x) hCx _ hBx hgBx
      exact ⟨(DenotesO.open_fvar hfresh' ρ₀ _).1 hB', (GradedBy.open_fvarO hfresh' ρ₀).1 hgB'⟩
    refine ⟨.pi hA' (fun x hx => (hstep x hx).1) hP, Gr.pi_iff.2 ⟨hgA', fun _ hA'' x hx => ?_⟩⟩
    obtain rfl := DenotesO.functional hA'' hA'
    exact (hstep x hx).2

/-- **`PiRed.lam` is sound over `Model`.** -/
theorem PiRed.lam_sound {d : Nat} {A A' B B' : Expr md} {mb : BinderMeta}
    (hB'ws : B'.wscopedB d = true)
    (sA : PiRedS M φ d A A')
    (sB : PiRedS M φ (d + 1) (B.instantiate1 (.fvar d A)) (B'.instantiate1 (.fvar d A))) :
    PiRedS M φ d (.lam A B mb) (.lam A' B' mb) := by
  intro hf σ hC v hv hg
  have hp := Frame.lam_parts hf
  obtain ⟨hgA, hgB⟩ := Gr.lam_iff.1 hg
  have hCA : Ctx M φ σ A := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCB : Ctx M φ σ B := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hfresh : ∀ l ∈ B.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
  have hfresh' : ∀ l ∈ B'.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped (Expr.WScoped.of_wscopedB hB'ws) l hl).1
  cases hv with
  | lam hA hB hP =>
    obtain ⟨hA', hgA'⟩ := sA hp.ty σ hCA _ hA hgA
    have hstep : ∀ x, x ∈ˢ _ →
        DenotesO M.cval env φ σ (push x ρ₀) B' _ ∧
        GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) B' := fun x hx => by
      have hCx := Ctx.open hp.ty.1 hp.ws hCA hCB hA hx hgA
      have hBx : Den M φ (setAt σ d x) (B.instantiate1 (.fvar d A)) _ :=
        (DenotesO.open_fvar hfresh ρ₀ _).2 (hB x hx)
      have hgBx : Gr M φ (setAt σ d x) (B.instantiate1 (.fvar d A)) :=
        (GradedBy.open_fvarO hfresh ρ₀).2 (hgB _ hA x hx)
      obtain ⟨hB', hgB'⟩ := sB hp.open (setAt σ d x) hCx _ hBx hgBx
      exact ⟨(DenotesO.open_fvar hfresh' ρ₀ _).1 hB', (GradedBy.open_fvarO hfresh' ρ₀).1 hgB'⟩
    refine ⟨.lam hA' (fun x hx => (hstep x hx).1) hP, Gr.lam_iff.2 ⟨hgA', fun _ hA'' x hx => ?_⟩⟩
    obtain rfl := DenotesO.functional hA'' hA'
    exact (hstep x hx).2

/-- **`DefEq.transClosed` is sound over `Model`.** -/
theorem DefEq.transClosed_sound {d : Nat} {a b b' c tb : Expr md}
    (hbf : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hb'f : b'.hasFvar = false) (hb'b : b'.looseBVarsBounded 0 = true)
    (sib : InferFullS M φ 0 b' tb) (spb : PiRedS M φ 0 b' b)
    (sab : DefEqS M φ d a b) (sbc : DefEqS M φ d b c) :
    DefEqS M φ d a c := by
  intro hfa hfc σ hCa hCc x z hx hz hgx hgz
  have hfb' : Frame 0 b' := Frame.of_closed hb'f hb'b
  have hfb : Frame d b := Frame.of_closed hbf hbb
  obtain ⟨y, _, hy', hgy', -, -, -⟩ := (sib hfb').2.2 σ (Ctx.of_closed hb'f)
  obtain ⟨hy, hgy⟩ := spb hfb' σ (Ctx.of_closed hb'f) y hy' hgy'
  exact (sab hfa hfb σ hCa (Ctx.of_closed hbf) x y hx hy hgx hgy).trans
    (sbc hfb hfc σ (Ctx.of_closed hbf) hCc y z hy hz hgy hgz)

end Ix.Kernel.Open
