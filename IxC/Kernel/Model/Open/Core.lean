module

public import IxC.Kernel.Model.Open.Motive
public import IxC.Kernel.Verify.InferLeaves
public import IxC.Kernel.Verify.InstLevels
public import IxC.Kernel.Verify.InferLemmas
public import IxC.Kernel.Semantics.Univ
import IxC.Kernel.Verify.PropWhen

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the structural rules

One lemma per rule, from the motives of its premises (`Open/Motive.lean`), over any
`M : Model V env`. This file has the rules that read no law beyond δ and the gradings:

* `Red`: `refl`, `trans`, the congruences `appFn`/`appArg`/`projArg`, β gated and
  certified, δ;
* `DefEq`: `refl`, `symm`, `redL`, the sort, variable and constant leaves, and the
  congruences (application, projection, `∀`, `λ`);
* `Infer`: sorts, variables, constants, applications certified or skipped at a `never`
  binder, `∀`-formation.

δ and constants need the environment's syntactic well-formedness (`EnvWF`: a stored type or
value is closed), which the kernel establishes for every environment it builds.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## Readings of the term forms -/

theorem Gr.app_iff {σ : Nat → V} {f a : Expr md} :
    Gr M φ σ (.app f a) ↔ Gr M φ σ f ∧ Gr M φ σ a ∧
      ∃ (r : Nat) (A F X : V) (B : V → V), Den M φ σ f F ∧ Den M φ σ a X ∧
        F ∈ˢ piR r A B ∧ X ∈ˢ A ∧ (r = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :=
  Iff.rfl

theorem Gr.lam_iff {σ : Nat → V} {ty b : Expr md} {m : BinderMeta} :
    Gr M φ σ (.lam ty b m) ↔ Gr M φ σ ty ∧
      ∀ A, Den M φ σ ty A → ∀ x, x ∈ˢ A → GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) b :=
  Iff.rfl

theorem Gr.pi_iff {σ : Nat → V} {ty b : Expr md} {m : BinderMeta} :
    Gr M φ σ (.forallE ty b m) ↔ Gr M φ σ ty ∧
      ∀ A, Den M φ σ ty A → ∀ x, x ∈ˢ A → GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) b :=
  Iff.rfl

/-- A term with no free variable and no loose bound variable is framed at every depth. -/
theorem Frame.of_closed {d : Nat} {e : Expr md} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) : Frame d e :=
  ⟨Expr.WScoped.of_not_hasFvar hf, hb, Expr.LeavesBounded.of_not_hasFvar hf⟩

theorem LeavesSub.of_closed {e' e : Expr md} (hf : e'.hasFvar = false) : LeavesSub e' e := by
  intro l hl
  rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hf] at hl
  exact nomatch hl

/-- **δ, inverted**: an unfolding is a stored definition's value at the head's levels,
applied to the spine. -/
theorem unfoldDefinition_inv {e e' : Expr md} (h : unfoldDefinition env e = some e') :
    ∃ (n : Key md) (us : List Level) (cv : ConstantVal md) (value : Expr md)
      (hint : ReducibilityHint),
      e.getAppFn = .const n us ∧ env.find? n = some (.defnInfo cv value hint) ∧
      us.length = cv.levelParams.length ∧
      e' = Expr.mkAppN (value.instantiateLevelParams cv.levelParams us) e.getAppArgs := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · rename_i hlen
    intro h
    simp only [Option.some.injEq] at h
    exact ⟨n, us, cv, value, hint, by first | exact hfn | rfl, by first | exact hf | rfl, hlen,
      h.symm⟩
  · intro h; exact nomatch h

/-- A stored constant's key is its name. -/
theorem find?_name {n : Key md} {ci : ConstantInfo md} (hf : env.find? n = some ci) :
    ci.name = n := by
  simpa using List.find?_some (p := fun c : ConstantInfo md => c.name == n) hf

/-! ## `Red` -/

theorem Red.refl_sound {d : Nat} {e : Expr md} : RedS M φ d e e :=
  fun hf => ⟨hf, fun _ h => h, fun _ _ _ hv hg => ⟨hv, hg⟩⟩

theorem Red.trans_sound {d : Nat} {e₁ e₂ e₃ : Expr md} (h₁ : RedS M φ d e₁ e₂)
    (h₂ : RedS M φ d e₂ e₃) : RedS M φ d e₁ e₃ := by
  intro hf
  obtain ⟨hf₂, hs₂, k₂⟩ := h₁ hf
  obtain ⟨hf₃, hs₃, k₃⟩ := h₂ hf₂
  refine ⟨hf₃, fun l hl => hs₂ l (hs₃ l hl), fun σ hC v hv hg => ?_⟩
  obtain ⟨hv₂, hg₂⟩ := k₂ σ hC v hv hg
  exact k₃ σ (hC.of_subset hs₂) v hv₂ hg₂

theorem Red.appFn_sound {d : Nat} {f f' a : Expr md} (h : RedS M φ d f f') :
    RedS M φ d (.app f a) (.app f' a) := by
  intro hfr
  obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨hff', hsub, k⟩ := h hff
  refine ⟨Frame.app_iff.2 ⟨hff', hfa⟩, fun l hl => ?_, fun σ hC v hv hg => ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    exact hl.elim (fun hl => Or.inl (hsub l hl)) Or.inr
  · cases hv with
    | app hF hX =>
      obtain ⟨hgf, hga, r, A, F', X', B, hF', hX', hm, hx, h0⟩ := Gr.app_iff.1 hg
      have hCf : Ctx M φ σ f := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
      obtain ⟨hF₂, hgf₂⟩ := k σ hCf _ hF hgf
      obtain rfl := DenotesO.functional hF' hF
      obtain rfl := DenotesO.functional hX' hX
      exact ⟨.app hF₂ hX, Gr.app_iff.2 ⟨hgf₂, hga, r, A, _, _, B, hF₂, hX, hm, hx, h0⟩⟩

theorem Red.appArg_sound {d : Nat} {f a a' : Expr md} (h : RedS M φ d a a') :
    RedS M φ d (.app f a) (.app f a') := by
  intro hfr
  obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨hfa', hsub, k⟩ := h hfa
  refine ⟨Frame.app_iff.2 ⟨hff, hfa'⟩, fun l hl => ?_, fun σ hC v hv hg => ?_⟩
  · simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    exact hl.elim Or.inl (fun hl => Or.inr (hsub l hl))
  · cases hv with
    | app hF hX =>
      obtain ⟨hgf, hga, r, A, F', X', B, hF', hX', hm, hx, h0⟩ := Gr.app_iff.1 hg
      have hCa : Ctx M φ σ a := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
      obtain ⟨hX₂, hga₂⟩ := k σ hCa _ hX hga
      obtain rfl := DenotesO.functional hF' hF
      obtain rfl := DenotesO.functional hX' hX
      exact ⟨.app hF hX₂, Gr.app_iff.2 ⟨hgf, hga₂, r, A, _, _, B, hF, hX₂, hm, hx, h0⟩⟩

theorem Red.projArg_sound {d : Nat} {s : Key md} {i : Nat} {e e' : Expr md}
    (h : RedS M φ d e e') : RedS M φ d (.proj s i e) (.proj s i e') := by
  intro hfr
  obtain ⟨hf', hsub, k⟩ := h (Frame.proj_iff.1 hfr)
  refine ⟨Frame.proj_iff.2 hf', fun l hl => ?_, fun σ hC v hv hg => ?_⟩
  · simp only [Expr.fvarLeaves] at hl ⊢
    exact hsub l hl
  · have hC' : Ctx M φ σ e := hC.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
    have hge : Gr M φ σ e := hg
    cases hv with
    | proj_table ht he =>
      obtain ⟨h1, h2⟩ := k σ hC' _ he hge
      exact ⟨.proj_table ht h1, h2⟩
    | proj_fst ht he =>
      obtain ⟨h1, h2⟩ := k σ hC' _ he hge
      exact ⟨.proj_fst ht h1, h2⟩
    | proj_snd ht he =>
      obtain ⟨h1, h2⟩ := k σ hC' _ he hge
      exact ⟨.proj_snd ht h1, h2⟩

/-- The frame and leaves of a β-reduct. -/
theorem beta_frame {d : Nat} {ty body a : Expr md} {mb : BinderMeta}
    (hfr : Frame d (.app (.lam ty body mb) a)) :
    Frame d (body.instantiate1 a) ∧ LeavesSub (body.instantiate1 a) (.app (.lam ty body mb) a) := by
  obtain ⟨hfl, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨hfr', hsub⟩ := (Frame.lam_parts hfl).subst hfa
  refine ⟨hfr', fun l hl => ?_⟩
  rcases hsub l hl with hl | hl
  · simp [Expr.fvarLeaves, hl]
  · simp [Expr.fvarLeaves, hl]

theorem Red.betaGate_sound {d : Nat} {ty body a : Expr md} {mb : BinderMeta}
    (hnev : mb.pw.isNever = true) :
    RedS M φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  intro hfr
  obtain ⟨-, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨hfr', hsub⟩ := beta_frame hfr
  refine ⟨hfr', hsub, fun σ hC v hv hg => ?_⟩
  cases hv with
  | app hL hX =>
    cases hL with
    | lam hA hF hP =>
      obtain ⟨hgl, hga, _, _, F', X', _, hF', hX', hm, hx, -⟩ := Gr.app_iff.1 hg
      obtain ⟨-, hgb⟩ := Gr.lam_iff.1 hgl
      obtain rfl := DenotesO.functional hF' (.lam hA hF hP)
      obtain rfl := DenotesO.functional hX' hX
      have hXA := mem_dom_of_graded (regime_ne_zero_of_isNever hnev φ) hm hx
      have haall := Den.all hX hfa.2.1
      refine ⟨?_, ?_⟩
      · rw [app_lamR_of_mem hXA hP]
        exact (DenotesO.instantiate1_zero haall body ρ₀ _).2 (hF _ hXA)
      · exact (GradedBy.instantiate1_zeroO haall (Gr.all hga hfa.2.1) body ρ₀).2
          (hgb _ hA _ hXA)

theorem Red.beta_sound {d : Nat} {ty body a ta : Expr md} {mb : BinderMeta}
    (hta : InferIOS M φ d a ta) (hd : DefEqS M φ d ta ty) :
    RedS M φ d (.app (.lam ty body mb) a) (body.instantiate1 a) := by
  intro hfr
  obtain ⟨hfl, hfa⟩ := Frame.app_iff.1 hfr
  have hp := Frame.lam_parts hfl
  obtain ⟨hfr', hsub⟩ := beta_frame hfr
  obtain ⟨hfta, hsubta, kta⟩ := hta hfa
  refine ⟨hfr', hsub, fun σ hC v hv hg => ?_⟩
  cases hv with
  | app hL hX =>
    cases hL with
    | lam hA hF hP =>
      obtain ⟨hgl, hga, -⟩ := Gr.app_iff.1 hg
      obtain ⟨hgty, hgb⟩ := Gr.lam_iff.1 hgl
      have hCa : Ctx M φ σ a := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
      have hCty : Ctx M φ σ ty := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
      obtain ⟨T, hT, hgT, hXT⟩ := kta σ hCa _ hX hga
      have hTA := hd hfta hp.ty σ (hCa.of_subset hsubta) hCty _ _ hT hA hgT hgty
      subst hTA
      have haall := Den.all hX hfa.2.1
      refine ⟨?_, ?_⟩
      · rw [app_lamR_of_mem hXT hP]
        exact (DenotesO.instantiate1_zero haall body ρ₀ _).2 (hF _ hXT)
      · exact (GradedBy.instantiate1_zeroO haall (Gr.all hga hfa.2.1) body ρ₀).2
          (hgb _ hA _ hXT)

/-- **δ**: a stored definition's value, at the use's levels, denotes what the constant does
(`Model.defn_value`), and is graded (`Model.graded`). -/
theorem Red.delta_sound (hwf : EnvWF env) {d : Nat} {e e' : Expr md}
    (h : unfoldDefinition env e = some e') : RedS M φ d e e' := by
  intro hfr
  refine ⟨⟨unfoldDefinition_WScoped hwf h hfr.1, unfoldDefinition_looseBVars hwf h hfr.2.1,
      fun l hl => hfr.2.2 l (unfoldDefinition_fvarLeaves hwf h l hl)⟩,
    fun l hl => unfoldDefinition_fvarLeaves hwf h l hl, fun σ _ v hv hg => ?_⟩
  obtain ⟨n, us, cv, value, hint, hfn, hf, hlen, rfl⟩ := unfoldDefinition_inv h
  have hmem := List.mem_of_find?_eq_some hf
  have hname : cv.name = n := find?_name hf
  have hwfv := (hwf _ hmem).2.2.2.2.1 cv value hint rfl
  have hcp : CvalParams M.cval env := M.cval_params
  have hval : Denotes M.cval env (Level.substFn φ cv.levelParams us) ρ₀ value
      (M.cval n (Level.substFn φ cv.levelParams us)) := by
    have hv := M.defn_value cv value hint hmem (Level.substFn φ cv.levelParams us) ρ₀
    rwa [hname] at hv
  have hvalO : Den M φ σ (value.instantiateLevelParams cv.levelParams us)
      (M.cval n (Level.substFn φ cv.levelParams us)) :=
    (DenotesO.instantiateLevelParams hcp cv.levelParams us value ρ₀ _).2
      (DenotesO.of_denotes hval)
  have hconst : Den M φ σ (.const n us) (M.cval n (Level.substFn φ cv.levelParams us)) :=
    DenotesO.const (ci := .defnInfo cv value hint) hf hlen
  have hD : ∀ w, Den M φ σ (.const n us) w ↔
      Den M φ σ (value.instantiateLevelParams cv.levelParams us) w := by
    intro w
    constructor
    · intro hw
      rw [DenotesO.functional hw hconst]
      exact hvalO
    · intro hw
      rw [DenotesO.functional hw hvalO]
      exact hconst
  have hG : Gr M φ σ (.const n us) →
      Gr M φ σ (value.instantiateLevelParams cv.levelParams us) := by
    intro _
    refine (GradedBy.instantiateLevelParamsO hcp cv.levelParams us value ρ₀).2 ?_
    exact GradedBy.toOpen ((M.graded _ hmem _ ρ₀).2 cv value hint rfl) hwfv.1
  have key := GradedBy.mkAppN_headO e.getAppArgs hD hG
  have he : e = Expr.mkAppN (.const n us) e.getAppArgs := by
    rw [← hfn]; exact (Expr.mkAppN_getApp e).symm
  rw [he] at hv hg
  exact ⟨(key.1 v).1 hv, key.2 hg⟩

/-! ## `DefEq` -/

theorem DefEq.refl_sound {d : Nat} {a : Expr md} : DefEqS M φ d a a :=
  fun _ _ _ _ _ _ _ hv hw _ _ => DenotesO.functional hv hw

theorem DefEq.symm_sound {d : Nat} {a b : Expr md} (h : DefEqS M φ d a b) :
    DefEqS M φ d b a :=
  fun hfb hfa σ hCb hCa v w hv hw hgb hga => (h hfa hfb σ hCa hCb w v hw hv hga hgb).symm

theorem DefEq.redL_sound {d : Nat} {a a' b : Expr md} (hr : RedS M φ d a a')
    (h : DefEqS M φ d a' b) : DefEqS M φ d a b := by
  intro hfa hfb σ hCa hCb v w hv hw hga hgb
  obtain ⟨hfa', hsub, k⟩ := hr hfa
  obtain ⟨hv', hga'⟩ := k σ hCa v hv hga
  exact h hfa' hfb σ (hCa.of_subset hsub) hCb v w hv' hw hga' hgb

theorem DefEq.sort_sound {d : Nat} {u v : Level} (h : ∀ φ, Level.eval φ u = Level.eval φ v) :
    DefEqS M φ d (.sort u) (.sort v) := by
  intro _ _ _ _ _ x y hx hy _ _
  cases hx
  cases hy
  rw [h φ]

theorem DefEq.fvar_sound {d i : Nat} {ty₁ ty₂ : Expr md} :
    DefEqS M φ d (.fvar i ty₁) (.fvar i ty₂) := by
  intro _ _ _ _ _ x y hx hy _ _
  cases hx
  cases hy
  rfl

theorem DefEq.const_sound {d : Nat} {n : Key md} {us us' : List Level}
    (h : ∀ φ, Level.EvalEqList φ us us') : DefEqS M φ d (.const n us) (.const n us') := by
  intro _ _ _ _ _ x y hx hy _ _
  cases hx with
  | const hf _ =>
    cases hy with
    | const hf' _ =>
      rw [hf] at hf'
      cases hf'
      exact M.cval_params n _ hf _ _ fun p _ => Level.substFn_of_evalEqList _ (h φ) p

theorem DefEq.app_sound {d : Nat} {f₁ a₁ f₂ a₂ : Expr md} (hf : DefEqS M φ d f₁ f₂)
    (ha : DefEqS M φ d a₁ a₂) : DefEqS M φ d (.app f₁ a₁) (.app f₂ a₂) := by
  intro hfr₁ hfr₂ σ hC₁ hC₂ v w hv hw hg₁ hg₂
  obtain ⟨hff₁, hfa₁⟩ := Frame.app_iff.1 hfr₁
  obtain ⟨hff₂, hfa₂⟩ := Frame.app_iff.1 hfr₂
  obtain ⟨hgf₁, hga₁, -⟩ := Gr.app_iff.1 hg₁
  obtain ⟨hgf₂, hga₂, -⟩ := Gr.app_iff.1 hg₂
  cases hv with
  | app hF₁ hX₁ =>
    cases hw with
    | app hF₂ hX₂ =>
      rw [hf hff₁ hff₂ σ (hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl])
          (hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ _ hF₁ hF₂ hgf₁ hgf₂,
        ha hfa₁ hfa₂ σ (hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl])
          (hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]) _ _ hX₁ hX₂ hga₁ hga₂]

theorem DefEq.proj_sound {d : Nat} {s : Key md} {i : Nat} {e₁ e₂ : Expr md}
    (h : DefEqS M φ d e₁ e₂) : DefEqS M φ d (.proj s i e₁) (.proj s i e₂) := by
  intro hfr₁ hfr₂ σ hC₁ hC₂ v w hv hw hg₁ hg₂
  have hC₁' : Ctx M φ σ e₁ := hC₁.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
  have hC₂' : Ctx M φ σ e₂ := hC₂.of_subset fun l hl => by simpa [Expr.fvarLeaves] using hl
  obtain ⟨P₁, hP₁⟩ : ∃ P, Den M φ σ e₁ P := by
    cases hv with
    | proj_table _ he => exact ⟨_, he⟩
    | proj_fst _ he => exact ⟨_, he⟩
    | proj_snd _ he => exact ⟨_, he⟩
  have hw' : Den M φ σ (.proj s i e₁) w := by
    cases hw with
    | proj_table ht he =>
      rw [← h (Frame.proj_iff.1 hfr₁) (Frame.proj_iff.1 hfr₂) σ hC₁' hC₂' _ _ hP₁ he hg₁ hg₂]
      exact .proj_table ht hP₁
    | proj_fst ht he =>
      rw [← h (Frame.proj_iff.1 hfr₁) (Frame.proj_iff.1 hfr₂) σ hC₁' hC₂' _ _ hP₁ he hg₁ hg₂]
      exact .proj_fst ht hP₁
    | proj_snd ht he =>
      rw [← h (Frame.proj_iff.1 hfr₁) (Frame.proj_iff.1 hfr₂) σ hC₁' hC₂' _ _ hP₁ he hg₁ hg₂]
      exact .proj_snd ht hP₁
  exact DenotesO.functional hv hw'

/-- **Binder congruence, the bodies**: two binders whose domains denote `A` and whose bodies
are definitionally equal opened at a fresh variable of the right domain have bodies that
agree at every member of `A`. -/
theorem binder_bodies {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr md} {σ : Nat → V} {A : V}
    {B₁ B₂ : V → V}
    (hbody : DefEqS M φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hp₁ : BinderParts d ty₁ body₁) (hp₂ : BinderParts d ty₂ body₂)
    (hC₁ : Ctx M φ σ body₁) (hC₂ : Ctx M φ σ body₂) (hCty : Ctx M φ σ ty₂)
    (hA₂ : Den M φ σ ty₂ A) (hgty : Gr M φ σ ty₂)
    (hB₁ : ∀ x, x ∈ˢ A → DenotesO M.cval env φ σ (push x ρ₀) body₁ (B₁ x))
    (hB₂ : ∀ x, x ∈ˢ A → DenotesO M.cval env φ σ (push x ρ₀) body₂ (B₂ x))
    (hg₁ : ∀ x, x ∈ˢ A → GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) body₁)
    (hg₂ : ∀ x, x ∈ˢ A → GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) body₂) :
    ∀ x, x ∈ˢ A → B₁ x = B₂ x := by
  intro x hx
  have hfresh₁ : ∀ l ∈ body₁.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped hp₁.ws l hl).1
  have hfresh₂ : ∀ l ∈ body₂.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped hp₂.ws l hl).1
  have hp₁' : BinderParts d ty₂ body₁ := ⟨hp₂.ty, hp₁.ws, hp₁.lbb, hp₁.leaves⟩
  exact hbody hp₁'.open hp₂.open (setAt σ d x)
    (Ctx.open hp₂.ty.1 hp₁.ws hCty hC₁ hA₂ hx hgty)
    (Ctx.open hp₂.ty.1 hp₂.ws hCty hC₂ hA₂ hx hgty) _ _
    ((DenotesO.open_fvar hfresh₁ ρ₀ _).2 (hB₁ x hx))
    ((DenotesO.open_fvar hfresh₂ ρ₀ _).2 (hB₂ x hx))
    ((GradedBy.open_fvarO hfresh₁ ρ₀).2 (hg₁ x hx))
    ((GradedBy.open_fvarO hfresh₂ ρ₀).2 (hg₂ x hx))

theorem DefEq.forallE_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr md} {m₁ m₂ : BinderMeta}
    (hty : DefEqS M φ d ty₁ ty₂)
    (hbody : DefEqS M φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqS M φ d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂) := by
  intro hfr₁ hfr₂ σ hC₁ hC₂ v w hv hw hg₁ hg₂
  have hp₁ := Frame.pi_parts hfr₁
  have hp₂ := Frame.pi_parts hfr₂
  obtain ⟨hgty₁, hgb₁⟩ := Gr.pi_iff.1 hg₁
  obtain ⟨hgty₂, hgb₂⟩ := Gr.pi_iff.1 hg₂
  have hCty₁ : Ctx M φ σ ty₁ := hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCty₂ : Ctx M φ σ ty₂ := hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCb₁ : Ctx M φ σ body₁ := hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCb₂ : Ctx M φ σ body₂ := hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  cases hv with
  | pi hA₁ hB₁ _ =>
    cases hw with
    | pi hA₂ hB₂ _ =>
      obtain rfl := hty hp₁.ty hp₂.ty σ hCty₁ hCty₂ _ _ hA₁ hA₂ hgty₁ hgty₂
      rw [hpw]
      exact piR_congr (binder_bodies hbody hp₁ hp₂ hCb₁ hCb₂ hCty₂ hA₂ hgty₂ hB₁ hB₂
        (fun x hx => hgb₁ _ hA₁ x hx) (fun x hx => hgb₂ _ hA₂ x hx))

theorem DefEq.lam_sound {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr md} {m₁ m₂ : BinderMeta}
    (hty : DefEqS M φ d ty₁ ty₂)
    (hbody : DefEqS M φ (d + 1) (body₁.instantiate1 (.fvar d ty₂))
      (body₂.instantiate1 (.fvar d ty₂)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqS M φ d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂) := by
  intro hfr₁ hfr₂ σ hC₁ hC₂ v w hv hw hg₁ hg₂
  have hp₁ := Frame.lam_parts hfr₁
  have hp₂ := Frame.lam_parts hfr₂
  obtain ⟨hgty₁, hgb₁⟩ := Gr.lam_iff.1 hg₁
  obtain ⟨hgty₂, hgb₂⟩ := Gr.lam_iff.1 hg₂
  have hCty₁ : Ctx M φ σ ty₁ := hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCty₂ : Ctx M φ σ ty₂ := hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCb₁ : Ctx M φ σ body₁ := hC₁.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCb₂ : Ctx M φ σ body₂ := hC₂.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  cases hv with
  | lam hA₁ hF₁ _ =>
    cases hw with
    | lam hA₂ hF₂ _ =>
      obtain rfl := hty hp₁.ty hp₂.ty σ hCty₁ hCty₂ _ _ hA₁ hA₂ hgty₁ hgty₂
      rw [hpw]
      exact lamR_congr (binder_bodies hbody hp₁ hp₂ hCb₁ hCb₂ hCty₂ hA₂ hgty₂ hF₁ hF₂
        (fun x hx => hgb₁ _ hA₁ x hx) (fun x hx => hgb₂ _ hA₂ x hx))

/-! ## `Infer` -/

theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferS M φ g d (.sort u) (.sort (.succ u)) := by
  have hmem : (univ (Level.eval φ u) : V) ∈ˢ univ (Level.eval φ (.succ u)) := univ_mem_univ _
  cases g with
  | full =>
    intro _
    exact ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl,
      fun _ _ => ⟨_, _, .sort, True.intro, .sort, True.intro, hmem⟩⟩
  | io =>
    intro _
    refine ⟨Frame.of_closed rfl rfl, LeavesSub.of_closed rfl, fun _ _ _ hv _ => ?_⟩
    cases hv
    exact ⟨_, .sort, True.intro, hmem⟩

/-- The frame and leaves of a variable's type. -/
theorem fvar_frame {d idx : Nat} {ty : Expr md} (hfr : Frame d (.fvar idx ty)) :
    Frame d ty ∧ LeavesSub ty (.fvar idx ty) := by
  obtain ⟨hw, -, hL⟩ := hfr
  simp only [Expr.WScoped] at hw
  have hsub : LeavesSub ty (.fvar idx ty) := fun l hl => by simp [Expr.fvarLeaves, hl]
  exact ⟨⟨Expr.WScoped.mono (Nat.le_of_lt hw.1) hw.2,
    hL (idx, ty) (by simp [Expr.fvarLeaves]), fun l hl => hL l (hsub l hl)⟩, hsub⟩

theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr md} :
    InferS M φ g d (.fvar idx ty) ty := by
  cases g with
  | full =>
    intro hfr
    obtain ⟨hft, hsub⟩ := fvar_frame hfr
    refine ⟨hft, hsub, fun _ hC => ?_⟩
    obtain ⟨⟨T, hT, hm⟩, hg⟩ := hC (idx, ty) (by simp [Expr.fvarLeaves])
    exact ⟨_, T, .fvar, True.intro, hT, hg, hm⟩
  | io =>
    intro hfr
    obtain ⟨hft, hsub⟩ := fvar_frame hfr
    refine ⟨hft, hsub, fun _ hC _ hv _ => ?_⟩
    cases hv
    obtain ⟨⟨T, hT, hm⟩, hg⟩ := hC (idx, ty) (by simp [Expr.fvarLeaves])
    exact ⟨T, hT, hg, hm⟩

/-- **A constant's type**: the stored type at the use's levels holds the constant
(`Model.mem`), and is graded (`Model.graded`). -/
theorem const_typed (hwf : EnvWF env) {n : Key md} {us : List Level} {ci : ConstantInfo md}
    (hf : env.find? n = some ci) (hus : us.length = ci.toConstantVal.levelParams.length)
    (σ : Nat → V) :
    ∃ T, Den M φ σ (.const n us) (M.cval n (Level.substFn φ ci.toConstantVal.levelParams us)) ∧
      Den M φ σ (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) T ∧
      Gr M φ σ (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) ∧
      M.cval n (Level.substFn φ ci.toConstantVal.levelParams us) ∈ˢ T := by
  have hmem := List.mem_of_find?_eq_some hf
  have hname : ci.name = n := find?_name hf
  have hwfc := hwf _ hmem
  have hcp : CvalParams M.cval env := M.cval_params
  obtain ⟨T, hT, hm⟩ := M.mem ci hmem (Level.substFn φ ci.toConstantVal.levelParams us) ρ₀
  refine ⟨T, .const hf hus,
    (DenotesO.instantiateLevelParams hcp _ us _ ρ₀ _).2 (DenotesO.of_denotes hT),
    (GradedBy.instantiateLevelParamsO hcp _ us _ ρ₀).2
      (GradedBy.toOpen ((M.graded ci hmem _ ρ₀).1) hwfc.1), ?_⟩
  rw [← hname]
  exact hm

theorem const_type_frame (hwf : EnvWF env) {d : Nat} {n : Key md} {us : List Level}
    {ci : ConstantInfo md} (hf : env.find? n = some ci) :
    Frame d (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) ∧
      LeavesSub (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
        (.const n us) := by
  have hwfc := hwf _ (List.mem_of_find?_eq_some hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
      us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hwfc.1
  have hlb : (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfc.2.2.2.1
  exact ⟨Frame.of_closed hnf hlb, LeavesSub.of_closed hnf⟩

theorem Infer.const_sound (hwf : EnvWF env) {g : Grade} {d : Nat} {n : Key md}
    {us : List Level} {ci : ConstantInfo md} (hf : env.find? n = some ci)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferS M φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  cases g with
  | full =>
    intro _
    obtain ⟨hft, hsub⟩ := const_type_frame (d := d) (us := us) hwf hf
    refine ⟨hft, hsub, fun σ _ => ?_⟩
    obtain ⟨T, hc, hT, hg, hm⟩ := const_typed (M := M) (φ := φ) hwf hf hus σ
    exact ⟨_, T, hc, True.intro, hT, hg, hm⟩
  | io =>
    intro _
    obtain ⟨hft, hsub⟩ := const_type_frame (d := d) (us := us) hwf hf
    refine ⟨hft, hsub, fun σ _ _ hv _ => ?_⟩
    obtain ⟨T, hc, hT, hg, hm⟩ := const_typed (M := M) (φ := φ) hwf hf hus σ
    obtain rfl := DenotesO.functional hv hc
    exact ⟨T, hT, hg, hm⟩

/-- **An application's typing in the sets**: a function in a product applied to a member
of the domain is graded, and lands in the codomain at the argument. -/
theorem app_typed {d : Nat} {f a ty body : Expr md} {mt : BinderMeta} {σ : Nat → V}
    {F X A : V} {B : V → V} (hfa : Frame d a)
    (hF : Den M φ σ f F) (hX : Den M φ σ a X) (hgf : Gr M φ σ f) (hga : Gr M φ σ a)
    (hA : Den M φ σ ty A)
    (hB : ∀ x, x ∈ˢ A → DenotesO M.cval env φ σ (push x ρ₀) body (B x))
    (hP : regime φ mt.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)
    (hgpi : Gr M φ σ (.forallE ty body mt))
    (hFm : F ∈ˢ piR (regime φ mt.pw) A B) (hXA : X ∈ˢ A) :
    Gr M φ σ (.app f a) ∧ Den M φ σ (body.instantiate1 a) (B X) ∧
      Gr M φ σ (body.instantiate1 a) ∧ app F X ∈ˢ B X := by
  have haall := Den.all hX hfa.2.1
  obtain ⟨-, hgb⟩ := Gr.pi_iff.1 hgpi
  exact ⟨Gr.app_iff.2 ⟨hgf, hga, _, A, F, X, B, hF, hX, hFm, hXA, hP⟩,
    (DenotesO.instantiate1_zero haall body ρ₀ _).2 (hB X hXA),
    (GradedBy.instantiate1_zeroO haall (Gr.all hga hfa.2.1) body ρ₀).2 (hgb _ hA _ hXA),
    app_mem_piR hFm hXA (by rw [← univ_zero]; exact hP)⟩

/-- The frame and leaves of an application's inferred type `body[a]`, from the head's type
reducing to `∀ ty, body`. -/
theorem app_frame {d : Nat} {f a tf ty body : Expr md} {mt : BinderMeta}
    (hfa : Frame d a) (hfpi : Frame d (.forallE ty body mt))
    (hsubtf : LeavesSub tf f) (hsubpi : LeavesSub (.forallE ty body mt) tf) :
    Frame d (body.instantiate1 a) ∧ LeavesSub (body.instantiate1 a) (.app f a) := by
  obtain ⟨hfr', hsubr⟩ := (Frame.pi_parts hfpi).subst hfa
  refine ⟨hfr', fun l hl => ?_⟩
  rcases hsubr l hl with hl | hl
  · have hpi : l ∈ (Expr.forallE ty body mt).fvarLeaves := by simp [Expr.fvarLeaves, hl]
    simp [Expr.fvarLeaves, hsubtf l (hsubpi l hpi)]
  · simp [Expr.fvarLeaves, hl]

theorem Infer.app_sound {g : Grade} {d : Nat} {f a tf ty body ta : Expr md} {mt : BinderMeta}
    (htf : InferS M φ g d f tf) (hw : RedS M φ d tf (.forallE ty body mt))
    (hta : InferS M φ g d a ta) (hd : DefEqS M φ d ta ty) :
    InferS M φ g d (.app f a) (body.instantiate1 a) := by
  cases g with
  | full =>
    intro hfr
    obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hfr
    obtain ⟨hftf, hsubtf, ktf⟩ := htf hff
    obtain ⟨hfpi, hsubpi, kw⟩ := hw hftf
    obtain ⟨hfta, hsubta, kta⟩ := hta hfa
    have hpb := Frame.pi_parts hfpi
    obtain ⟨hfr', hsubr⟩ := app_frame hfa hfpi hsubtf hsubpi
    refine ⟨hfr', hsubr, fun σ hC => ?_⟩
    have hCf : Ctx M φ σ f := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCa : Ctx M φ σ a := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCtf := hCf.of_subset hsubtf
    have hCpi := hCtf.of_subset hsubpi
    have hCty : Ctx M φ σ ty := hCpi.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    obtain ⟨F, TF, hF, hgf, hTF, hgtf, hFm⟩ := ktf σ hCf
    obtain ⟨hpi, hgpi⟩ := kw σ hCtf TF hTF hgtf
    obtain ⟨X, TA, hX, hga, hTA, hgta, hXm⟩ := kta σ hCa
    cases hpi with
    | pi hA hB hP =>
      obtain ⟨hgty, -⟩ := Gr.pi_iff.1 hgpi
      obtain rfl := hd hfta hpb.ty σ (hCa.of_subset hsubta) hCty _ _ hTA hA hgta hgty
      obtain ⟨hgapp, hbX, hgbX, hmem⟩ := app_typed hfa hF hX hgf hga hA hB hP hgpi hFm hXm
      exact ⟨_, _, .app hF hX, hgapp, hbX, hgbX, hmem⟩
  | io =>
    intro hfr
    obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hfr
    obtain ⟨hftf, hsubtf, ktf⟩ := htf hff
    obtain ⟨hfpi, hsubpi, kw⟩ := hw hftf
    obtain ⟨hfta, hsubta, kta⟩ := hta hfa
    have hpb := Frame.pi_parts hfpi
    obtain ⟨hfr', hsubr⟩ := app_frame hfa hfpi hsubtf hsubpi
    refine ⟨hfr', hsubr, fun σ hC _ hv hg => ?_⟩
    have hCf : Ctx M φ σ f := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCa : Ctx M φ σ a := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCtf := hCf.of_subset hsubtf
    have hCpi := hCtf.of_subset hsubpi
    have hCty : Ctx M φ σ ty := hCpi.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    cases hv with
    | app hF hX =>
      obtain ⟨hgf, hga, -⟩ := Gr.app_iff.1 hg
      obtain ⟨TF, hTF, hgtf, hFm⟩ := ktf σ hCf _ hF hgf
      obtain ⟨hpi, hgpi⟩ := kw σ hCtf TF hTF hgtf
      obtain ⟨TA, hTA, hgta, hXm⟩ := kta σ hCa _ hX hga
      cases hpi with
      | pi hA hB hP =>
        obtain ⟨hgty, -⟩ := Gr.pi_iff.1 hgpi
        obtain rfl := hd hfta hpb.ty σ (hCa.of_subset hsubta) hCty _ _ hTA hA hgta hgty
        obtain ⟨-, hbX, hgbX, hmem⟩ := app_typed hfa hF hX hgf hga hA hB hP hgpi hFm hXm
        exact ⟨_, hbX, hgbX, hmem⟩

/-- **An application at a `never` binder, with no argument certificate**: the subject's
grading puts the argument in the function's domain, which the function's type fixes (a
graph determines its domain). -/
theorem Infer.appSkip_sound {d : Nat} {f a tf ty body : Expr md} {mt : BinderMeta}
    (htf : InferIOS M φ d f tf) (hw : RedS M φ d tf (.forallE ty body mt))
    (hnev : mt.pw.isNever = true) : InferIOS M φ d (.app f a) (body.instantiate1 a) := by
  intro hfr
  obtain ⟨hff, hfa⟩ := Frame.app_iff.1 hfr
  obtain ⟨hftf, hsubtf, ktf⟩ := htf hff
  obtain ⟨hfpi, hsubpi, kw⟩ := hw hftf
  obtain ⟨hfr', hsubr⟩ := app_frame hfa hfpi hsubtf hsubpi
  refine ⟨hfr', hsubr, fun σ hC v hv hg => ?_⟩
  have hCf : Ctx M φ σ f := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCtf := hCf.of_subset hsubtf
  cases hv with
  | app hF hX =>
    obtain ⟨hgf, hga, r, _, F', X', _, hF', hX', hm', hx', -⟩ := Gr.app_iff.1 hg
    obtain rfl := DenotesO.functional hF' hF
    obtain rfl := DenotesO.functional hX' hX
    obtain ⟨TF, hTF, hgtf, hFm⟩ := ktf σ hCf _ hF' hgf
    obtain ⟨hpi, hgpi⟩ := kw σ hCtf TF hTF hgtf
    cases hpi with
    | pi hA hB hP =>
      have hreg := regime_ne_zero_of_isNever hnev φ
      have hr' : r ≠ 0 := by
        intro h0
        subst h0
        have hpt := eq_pt_of_mem_piR_zero hm'
        rw [hpt] at hFm
        exact not_pt_mem_piR_pos hreg hFm
      have hAA := piR_dom_unique hr' hreg hm' hFm
      rw [hAA] at hx'
      obtain ⟨-, hbX, hgbX, hmem⟩ := app_typed hfa hF' hX' hgf hga hA hB hP hgpi hFm hx'
      exact ⟨_, hbX, hgbX, hmem⟩

theorem mem_univ_congr {n m : Nat} {B : V} (h : n = m) (hB : B ∈ˢ (univ n : V)) :
    B ∈ˢ (univ m : V) :=
  h ▸ hB

/-- A binder datum validated as its codomain sort's zero-ness reads regime `0` exactly where
the sort is `0`. -/
theorem regime_zero_iff {v : Level} {pw : PropWhen} (hz : Level.zeronessOf v = pw)
    (φ : LevelParam → Nat) : regime φ pw = 0 ↔ Level.eval φ v = 0 := by
  subst hz
  unfold regime
  rw [PropWhen.zeronessOf_sound]
  by_cases h : Level.eval φ v = 0 <;> simp [h]

/-- **A `∀` lands in the `imax` of its domain's and codomain's universes.** -/
theorem piR_mem_univ_imax {u v : Level} {pw : PropWhen} (hz : Level.zeronessOf v = pw)
    {A : V} {B : V → V} (hA : A ∈ˢ univ (Level.eval φ u))
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ (Level.eval φ v)) :
    piR (regime φ pw) A B ∈ˢ univ (Level.eval φ (.imax u v)) := by
  rw [piR_zero_agree (regime_zero_iff hz φ) (fun _ _ => rfl)]
  exact Ix.Kernel.Semantics.piR_mem_univ hA hB

/-- The frames of `∀`-formation's premises and conclusion. -/
theorem pi_frames {d : Nat} {ty body : Expr md} {mb : BinderMeta} {u : Level}
    (hfr : Frame d (.forallE ty body mb)) :
    BinderParts d ty body ∧ Frame d (Expr.sort (md := md) u) ∧
      LeavesSub (Expr.sort (md := md) u) (.forallE ty body mb) :=
  ⟨Frame.pi_parts hfr, Frame.of_closed rfl rfl, LeavesSub.of_closed rfl⟩

theorem Infer.forallE_sound {g : Grade} {d : Nat} {ty body s bs : Expr md} {u v : Level}
    {mb : BinderMeta}
    (hs : InferS M φ g d ty s) (hu : RedS M φ d s (.sort u))
    (hbs : InferS M φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedS M φ (d + 1) bs (.sort v)) (hz : Level.zeronessOf v = mb.pw) :
    InferS M φ g d (.forallE ty body mb) (.sort (.imax u v)) := by
  cases g with
  | full =>
    intro hfr
    obtain ⟨hp, hfT, hsubT⟩ := pi_frames (u := .imax u v) hfr
    obtain ⟨hfs, hsubs, ks⟩ := hs hp.ty
    obtain ⟨-, -, ku⟩ := hu hfs
    obtain ⟨hfbs, hsubbs, kbs⟩ := hbs hp.open
    obtain ⟨-, -, kv⟩ := hv hfbs
    refine ⟨hfT, hsubT, fun σ hC => ?_⟩
    have hCty : Ctx M φ σ ty := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCb : Ctx M φ σ body := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    obtain ⟨A, S, hA, hgty, hS, hgS, hAS⟩ := ks σ hCty
    obtain ⟨hSu, -⟩ := ku σ (hCty.of_subset hsubs) S hS hgS
    cases hSu
    have hfresh : ∀ l ∈ body.fvarLeaves, l.1 ≠ d := fun l hl =>
      Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
    have hex : ∀ x, ∃ b, x ∈ˢ A → DenotesO M.cval env φ σ (push x ρ₀) body b ∧
        GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) body ∧ b ∈ˢ univ (Level.eval φ v) := by
      intro x
      rcases Classical.em (x ∈ˢ A) with hx | hx
      · have hCx := Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty
        obtain ⟨b, TB, hb, hgb, hTB, hgTB, hbT⟩ := kbs (setAt σ d x) hCx
        obtain ⟨hTBv, -⟩ := kv (setAt σ d x) (hCx.of_subset hsubbs) TB hTB hgTB
        cases hTBv
        exact ⟨b, fun _ => ⟨(DenotesO.open_fvar hfresh ρ₀ _).1 hb,
          (GradedBy.open_fvarO hfresh ρ₀).1 hgb, hbT⟩⟩
      · exact ⟨x, fun h => absurd h hx⟩
    have hBs : ∀ x, x ∈ˢ A → DenotesO M.cval env φ σ (push x ρ₀) body
        (Classical.choose (hex x)) ∧ GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) body ∧
        Classical.choose (hex x) ∈ˢ univ (Level.eval φ v) :=
      fun x hx => Classical.choose_spec (hex x) hx
    have hP : regime φ mb.pw = 0 → ∀ x, x ∈ˢ A → Classical.choose (hex x) ∈ˢ univ 0 := by
      intro h0 x hx
      exact mem_univ_congr ((regime_zero_iff hz φ).1 h0) (hBs x hx).2.2
    refine ⟨_, _, .pi hA (fun x hx => (hBs x hx).1) hP,
      Gr.pi_iff.2 ⟨hgty, fun A' hA' x hx => ?_⟩, .sort,
      True.intro, piR_mem_univ_imax hz hAS fun x hx => (hBs x hx).2.2⟩
    obtain rfl := DenotesO.functional hA' hA
    exact (hBs x hx).2.1
  | io =>
    intro hfr
    obtain ⟨hp, hfT, hsubT⟩ := pi_frames (u := .imax u v) hfr
    obtain ⟨hfs, hsubs, ks⟩ := hs hp.ty
    obtain ⟨-, -, ku⟩ := hu hfs
    obtain ⟨hfbs, hsubbs, kbs⟩ := hbs hp.open
    obtain ⟨-, -, kv⟩ := hv hfbs
    refine ⟨hfT, hsubT, fun σ hC _ hw hg => ?_⟩
    have hCty : Ctx M φ σ ty := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCb : Ctx M φ σ body := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    obtain ⟨hgty, hgb⟩ := Gr.pi_iff.1 hg
    have hfresh : ∀ l ∈ body.fvarLeaves, l.1 ≠ d := fun l hl =>
      Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
    cases hw with
    | pi hA hB _ =>
      obtain ⟨S, hS, hgS, hAS⟩ := ks σ hCty _ hA hgty
      obtain ⟨hSu, -⟩ := ku σ (hCty.of_subset hsubs) S hS hgS
      cases hSu
      refine ⟨_, .sort, True.intro, piR_mem_univ_imax hz hAS fun x hx => ?_⟩
      have hCx := Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty
      obtain ⟨TB, hTB, hgTB, hbT⟩ := kbs (setAt σ d x) hCx _
        ((DenotesO.open_fvar hfresh ρ₀ _).2 (hB x hx))
        ((GradedBy.open_fvarO hfresh ρ₀).2 (hgb _ hA x hx))
      obtain ⟨hTBv, -⟩ := kv (setAt σ d x) (hCx.of_subset hsubbs) TB hTB hgTB
      cases hTBv
      exact hbT

end Ix.Kernel.Open
