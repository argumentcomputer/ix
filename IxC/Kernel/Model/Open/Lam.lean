module

public import IxC.Kernel.Model.Open.Core
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Leaves

@[expose] public section

/-!
# The rules' soundness over the public `Model`: λ-inference

`Infer.lam` types `λ (x : ty), body` by the opened body's type `bt`, closed back over the
fresh variable: `∀ (x : ty), bt.abstract1 d`. Reading `bt.abstract1 d` with `x` pushed is
reading `bt` with the fresh variable set to `x` (`abstract1_instantiate1`, then
`DenotesO.open_fvar`), so the λ's graph lies in the `∀`'s product fibre by fibre. In regime
`0` the codomain must be a proposition: at the innermost binder the body type's sort says so,
at a chain node the inner `∀`'s own datum, which the rule equates with this one.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-- **The frame of a λ's inferred `∀`**, its leaves, and the round trip of the abstraction:
the opened body's type `bt` is framed one level deeper, and its leaves are the opened body's. -/
theorem lam_type_frame {d : Nat} {ty body bt : Expr md} {mb : BinderMeta}
    (hfr : Frame d (.lam ty body mb)) (hbt : Frame (d + 1) bt)
    (hsub : LeavesSub bt (body.instantiate1 (.fvar d ty))) :
    Frame d (.forallE ty (bt.abstract1 d) mb) ∧
      LeavesSub (.forallE ty (bt.abstract1 d) mb) (.lam ty body mb) ∧
      (bt.abstract1 d).instantiate1 (.fvar d ty) = bt ∧
      ∀ l ∈ (bt.abstract1 d).fvarLeaves, l.1 ≠ d := by
  have hp := Frame.lam_parts hfr
  obtain ⟨hwbt, hbtb, -⟩ := hbt
  have hleaf : Expr.LeafCond d ty bt := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 (hsub l hl) with h2 | h2
    · exact absurd hd (Nat.ne_of_lt (leaves_scoped hp.ws l h2).1)
    · simp only [Expr.fvarLeaves, List.mem_cons] at h2
      rcases h2 with rfl | h3
      · rfl
      · exact absurd hd (Nat.ne_of_lt (leaves_scoped hp.ty.1 l h3).1)
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    Ix.Kernel.abstract1_instantiate1 bt 0 (Expr.fvarConsistent_of_leafCond bt hleaf) hbtb
  have hsubT : LeavesSub (.forallE ty (bt.abstract1 d) mb) (.lam ty body mb) := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with h2 | h2
    · exact Or.inl h2
    · obtain ⟨hlbt, hlne⟩ := Ix.Kernel.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l h2
      rcases Expr.fvarLeaves_instantiate1 body 0 (hsub l hlbt) with h3 | h3
      · exact Or.inr h3
      · simp only [Expr.fvarLeaves, List.mem_cons] at h3
        rcases h3 with rfl | h4
        · exact absurd rfl hlne
        · exact Or.inl h4
  refine ⟨⟨?_, ?_, fun l hl => hfr.2.2 l (hsubT l hl)⟩, hsubT, hround,
    fun l hl => (Ix.Kernel.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l hl).2⟩
  · simp only [Expr.WScoped]
    exact ⟨hp.ty.1, Ix.Kernel.WScoped.abstract1 0 hwbt⟩
  · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hp.ty.2.1, Ix.Kernel.looseBVarsBounded_abstract1 bt 0 hbtb⟩

/-- **A λ and its `∀`, from its body fibre by fibre**: given, at each member `x` of the
domain's denotation `A`, the opened body's graded denotation `F x` and its type's graded
denotation `B x` holding it, and the codomain a proposition in regime `0`, the λ denotes
its graph, the `∀` the product, both graded, the first a member of the second. -/
theorem lam_typed {d : Nat} {ty body bt : Expr md} {mb : BinderMeta} {σ : Nat → V} {A : V}
    {F B : V → V} (hp : BinderParts d ty body)
    (hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt)
    (hfreshT : ∀ l ∈ (bt.abstract1 d).fvarLeaves, l.1 ≠ d)
    (hA : Den M φ σ ty A) (hgty : Gr M φ σ ty)
    (hrow : ∀ x, x ∈ˢ A →
      Den M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) (F x) ∧
      Gr M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) ∧
      Den M φ (setAt σ d x) bt (B x) ∧ Gr M φ (setAt σ d x) bt ∧ F x ∈ˢ B x)
    (hP : regime φ mb.pw = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
    Den M φ σ (.lam ty body mb) (lamR (regime φ mb.pw) A F) ∧ Gr M φ σ (.lam ty body mb) ∧
      Den M φ σ (.forallE ty (bt.abstract1 d) mb) (piR (regime φ mb.pw) A B) ∧
      Gr M φ σ (.forallE ty (bt.abstract1 d) mb) ∧
      lamR (regime φ mb.pw) A F ∈ˢ piR (regime φ mb.pw) A B := by
  have hfresh : ∀ l ∈ body.fvarLeaves, l.1 ≠ d := fun l hl =>
    Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
  have hbt : ∀ x v, Den M φ (setAt σ d x) bt v →
      DenotesO M.cval env φ σ (push x ρ₀) (bt.abstract1 d) v := by
    intro x v hv
    have h : DenotesO M.cval env φ (setAt σ d x) ρ₀
        ((bt.abstract1 d).instantiate1 (.fvar d ty)) v ↔
        DenotesO M.cval env φ σ (push x ρ₀) (bt.abstract1 d) v :=
      DenotesO.open_fvar hfreshT ρ₀ v
    rw [hround] at h
    exact h.1 hv
  have hgbt : ∀ x, Gr M φ (setAt σ d x) bt →
      GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) (bt.abstract1 d) := by
    intro x hg
    have h : GradedBy (DenotesO M.cval env φ (setAt σ d x)) ρ₀
        ((bt.abstract1 d).instantiate1 (.fvar d ty)) ↔
        GradedBy (DenotesO M.cval env φ σ) (push x ρ₀) (bt.abstract1 d) :=
      GradedBy.open_fvarO hfreshT ρ₀
    rw [hround] at h
    exact h.1 hg
  refine ⟨.lam hA (fun x hx => (DenotesO.open_fvar hfresh ρ₀ _).1 (hrow x hx).1) ?_,
    Gr.lam_iff.2 ⟨hgty, fun A' hA' x hx => ?_⟩,
    .pi hA (fun x hx => hbt x _ (hrow x hx).2.2.1) hP,
    Gr.pi_iff.2 ⟨hgty, fun A' hA' x hx => ?_⟩,
    lamR_mem fun x hx => (hrow x hx).2.2.2.2⟩
  · intro h0 x hx
    exact eq_pt_of_mem_univZero (by rw [← univ_zero]; exact hP h0 x hx) (hrow x hx).2.2.2.2
  · obtain rfl := DenotesO.functional hA' hA
    exact (GradedBy.open_fvarO hfresh ρ₀).1 (hrow x hx).2.1
  · obtain rfl := DenotesO.functional hA' hA
    exact hgbt x (hrow x hx).2.2.2.1

/-- **The codomain of a λ is a proposition where its datum says so**: at the innermost
binder the body type's sort is `0` there; at a chain node the inner `∀`'s datum is this
binder's, and a `∀` in regime `0` is a proposition. -/
theorem lam_regime {d : Nat} {ty body bt btt : Expr md} {v : Level} {mb : BinderMeta}
    {σ' : Nat → V} {B : V}
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferIOS M φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedS M φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw)
    (hfbt : Frame (d + 1) bt) (hCbt : Ctx M φ σ' bt) (hB : Den M φ σ' bt B)
    (hgB : Gr M φ σ' bt) (h0 : regime φ mb.pw = 0) : B ∈ˢ univ 0 := by
  cases hpw : body.lamPw with
  | some pwI =>
    obtain ⟨tyI, bI, mbI, rfl⟩ : ∃ tyI bI mbI, body = .lam tyI bI mbI := by
      cases body <;> simp [Expr.lamPw] at hpw
      exact ⟨_, _, _, rfl⟩
    have hpwEq : mb.pw = mbI.pw := by
      have := hchain pwI hpw
      simp only [Expr.lamPw, Option.some.injEq] at hpw
      rw [this, hpw]
    obtain ⟨btI, rfl⟩ := hshape tyI bI mbI rfl
    cases hB with
    | pi _ _ _ =>
      rw [← hpwEq, h0, univ_zero]
      exact piR_zero_mem_univZero
  | none =>
    obtain ⟨hfbtt, hsubbtt, k⟩ := hbtt hpw hfbt
    obtain ⟨TT, hTT, hgTT, hmem⟩ := k σ' hCbt B hB hgB
    obtain ⟨-, -, kv⟩ := hv hpw hfbtt
    obtain ⟨hTv, -⟩ := kv σ' (hCbt.of_subset hsubbtt) TT hTT hgTT
    cases hTv
    exact mem_univ_congr ((regime_zero_iff (hz hpw) φ).1 h0) hmem

/-- **λ-inference** (`Infer.lam`): at the full grade the λ and its `∀` have graded
denotations, the first in the second; at the io grade a graded denotation of the λ is in a
graded denotation of the `∀`. The domain's own sort is not read: a model needs only the
domain's denotation. -/
theorem Infer.lam_sound {g : Grade} {d : Nat} {ty body s bt btt : Expr md} {v : Level}
    {mb : BinderMeta}
    (hs : g = .full → InferFullS M φ d ty s)
    (hbt : InferS M φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt)
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferIOS M φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedS M φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw) :
    InferS M φ g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb) := by
  cases g with
  | full =>
    intro hfr
    have hp := Frame.lam_parts hfr
    obtain ⟨hfbt, hsubbt, kbt⟩ := hbt hp.open
    obtain ⟨hfT, hsubT, hround, hfreshT⟩ := lam_type_frame hfr hfbt hsubbt
    refine ⟨hfT, hsubT, fun σ hC => ?_⟩
    have hCty : Ctx M φ σ ty := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCb : Ctx M φ σ body := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    obtain ⟨A, -, hA, hgty, -⟩ := (hs rfl hp.ty).2.2 σ hCty
    have hex : ∀ x, ∃ p : V × V, x ∈ˢ A →
        Den M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) p.1 ∧
        Gr M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) ∧
        Den M φ (setAt σ d x) bt p.2 ∧ Gr M φ (setAt σ d x) bt ∧ p.1 ∈ˢ p.2 := by
      intro x
      rcases Classical.em (x ∈ˢ A) with hx | hx
      · obtain ⟨b, TB, hb, hgb, hTB, hgTB, hbT⟩ :=
          kbt (setAt σ d x) (Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty)
        exact ⟨(b, TB), fun _ => ⟨hb, hgb, hTB, hgTB, hbT⟩⟩
      · exact ⟨(x, x), fun h => absurd h hx⟩
    have hrow := fun x (hx : x ∈ˢ A) => Classical.choose_spec (hex x) hx
    have hP : regime φ mb.pw = 0 → ∀ x, x ∈ˢ A → (Classical.choose (hex x)).2 ∈ˢ univ 0 :=
      fun h0 x hx => lam_regime hshape hchain hbtt hv hz hfbt
        ((Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty).of_subset hsubbt) (hrow x hx).2.2.1
        (hrow x hx).2.2.2.1 h0
    obtain ⟨hl, hgl, hpi, hgpi, hmem⟩ := lam_typed (F := fun x => (Classical.choose (hex x)).1)
      (B := fun x => (Classical.choose (hex x)).2) hp hround hfreshT hA hgty hrow hP
    exact ⟨_, _, hl, hgl, hpi, hgpi, hmem⟩
  | io =>
    intro hfr
    have hp := Frame.lam_parts hfr
    obtain ⟨hfbt, hsubbt, kbt⟩ := hbt hp.open
    obtain ⟨hfT, hsubT, hround, hfreshT⟩ := lam_type_frame hfr hfbt hsubbt
    refine ⟨hfT, hsubT, fun σ hC w hw hg => ?_⟩
    have hCty : Ctx M φ σ ty := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hCb : Ctx M φ σ body := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
    have hfresh : ∀ l ∈ body.fvarLeaves, l.1 ≠ d := fun l hl =>
      Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
    obtain ⟨hgty, hgb⟩ := Gr.lam_iff.1 hg
    cases hw with
    | @lam _ _ _ _ A F hA hF _ =>
      have hex : ∀ x, ∃ T : V, x ∈ˢ A →
          Den M φ (setAt σ d x) bt T ∧ Gr M φ (setAt σ d x) bt ∧ F x ∈ˢ T := by
        intro x
        rcases Classical.em (x ∈ˢ A) with hx | hx
        · obtain ⟨TB, hTB, hgTB, hbT⟩ :=
            kbt (setAt σ d x) (Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty) (F x)
              ((DenotesO.open_fvar hfresh ρ₀ _).2 (hF x hx))
              ((GradedBy.open_fvarO hfresh ρ₀).2 (hgb _ hA x hx))
          exact ⟨TB, fun _ => ⟨hTB, hgTB, hbT⟩⟩
        · exact ⟨x, fun h => absurd h hx⟩
      have hrow : ∀ x, x ∈ˢ A →
          Den M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) (F x) ∧
          Gr M φ (setAt σ d x) (body.instantiate1 (.fvar d ty)) ∧
          Den M φ (setAt σ d x) bt (Classical.choose (hex x)) ∧
          Gr M φ (setAt σ d x) bt ∧ F x ∈ˢ Classical.choose (hex x) := fun x hx =>
        ⟨(DenotesO.open_fvar hfresh ρ₀ _).2 (hF x hx),
          (GradedBy.open_fvarO hfresh ρ₀).2 (hgb _ hA x hx),
          Classical.choose_spec (hex x) hx⟩
      have hP : regime φ mb.pw = 0 → ∀ x, x ∈ˢ A → Classical.choose (hex x) ∈ˢ univ 0 :=
        fun h0 x hx => lam_regime hshape hchain hbtt hv hz hfbt
          ((Ctx.open hp.ty.1 hp.ws hCty hCb hA hx hgty).of_subset hsubbt) (hrow x hx).2.2.1
          (hrow x hx).2.2.2.1 h0
      obtain ⟨-, -, hpi, hgpi, hmem⟩ := lam_typed (B := fun x => Classical.choose (hex x))
        hp hround hfreshT hA hgty hrow hP
      exact ⟨_, hpi, hgpi, hmem⟩

end Ix.Kernel.Open
