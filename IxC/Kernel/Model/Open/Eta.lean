module

public import IxC.Kernel.Model.Open.Core

@[expose] public section

/-!
# The rules' soundness over the public `Model`: function η

`DefEq.eta`: `b` is a member of a product over the λ's domain, and the λ's body opened at a
fresh variable agrees with `b` applied to it, so on the domain the λ's graph is `b`'s
applications, which are `b` (`SetModel.lamR_eta`). No law of `Model` is read.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-- A framed term stays framed one binder deeper. -/
theorem Frame.succ {d : Nat} {e : Expr md} (h : Frame d e) : Frame (d + 1) e :=
  ⟨Expr.WScoped.mono (Nat.le_succ d) h.1, h.2.1, h.2.2⟩

/-- **A fresh variable is framed** one binder in, at a framed type. -/
theorem Frame.fvar_fresh {d : Nat} {ty : Expr md} (h : Frame d ty) :
    Frame (d + 1) (.fvar d ty) := by
  refine ⟨⟨Nat.lt_succ_self d, h.1⟩, rfl, ?_⟩
  intro l hl
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact h.2.1
  · exact h.2.2 l hl

/-- **Function η** (`DefEq.eta`). -/
theorem DefEq.eta_sound {d : Nat} {ty₁ body₁ b tb ty₂ B : Expr md} {m₁ m₂ : BinderMeta}
    (htb : InferIOS M φ d b tb) (hw : RedS M φ d tb (.forallE ty₂ B m₂))
    (hty : DefEqS M φ d ty₂ ty₁)
    (hbody : DefEqS M φ (d + 1) (body₁.instantiate1 (.fvar d ty₁)) (.app b (.fvar d ty₁)))
    (hpw : m₁.pw = m₂.pw) :
    DefEqS M φ d (.lam ty₁ body₁ m₁) b := by
  intro hfr hfb σ hC hCb v w hv hw' hg hgb
  have hp := Frame.lam_parts hfr
  obtain ⟨hgty₁, hgb₁⟩ := Gr.lam_iff.1 hg
  have hCty₁ : Ctx M φ σ ty₁ := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  have hCb₁ : Ctx M φ σ body₁ := hC.of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  obtain ⟨hftb, hsubtb, ktb⟩ := htb hfb
  obtain ⟨hfpi, hsubpi, kw⟩ := hw hftb
  obtain ⟨Tb, hTb, hgTb, hwTb⟩ := ktb σ hCb w hw' hgb
  have hCtb := hCb.of_subset hsubtb
  obtain ⟨hpi, hgpi⟩ := kw σ hCtb Tb hTb hgTb
  have hp₂ := Frame.pi_parts hfpi
  have hCty₂ : Ctx M φ σ ty₂ :=
    (hCtb.of_subset hsubpi).of_subset fun l hl => by simp [Expr.fvarLeaves, hl]
  obtain ⟨hgty₂, -⟩ := Gr.pi_iff.1 hgpi
  cases hv with
  | @lam _ _ _ _ A₁ F hA₁ hF₁ _ =>
    cases hpi with
    | @pi _ _ _ _ A₂ B₂ hA₂ _ hP₂ =>
      have hAA : A₂ = A₁ := hty hp₂.ty hp.ty σ hCty₂ hCty₁ _ _ hA₂ hA₁ hgty₂ hgty₁
      have hfresh : ∀ l ∈ body₁.fvarLeaves, l.1 ≠ d := fun l hl =>
        Nat.ne_of_lt (leaves_scoped hp.ws l hl).1
      have hagree : ∀ x, x ∈ˢ A₁ → F x = app w x := by
        intro x hx
        have hfx : Den M φ (setAt σ d x) (.fvar d ty₁) x := by
          have h := DenotesO.fvar (cval := M.cval) (env := env) (φ := φ) (σ := setAt σ d x)
            (ρ := ρ₀) (i := d) (ty := ty₁)
          rwa [setAt_self] at h
        have hwx : Den M φ (setAt σ d x) b w := (Den.setAbove hfb.1).2 hw'
        have hCapp : Ctx M φ (setAt σ d x) (.app b (.fvar d ty₁)) := by
          intro l hl
          simp only [Expr.fvarLeaves, List.mem_append, List.mem_cons] at hl
          rcases hl with hl | rfl | hl
          · exact Ctx.setAbove hfb.1 hCb l hl
          · refine ⟨⟨A₁, (Den.setAbove hp.ty.1).2 hA₁, ?_⟩, (Gr.setAbove hp.ty.1).2 hgty₁⟩
            show setAt σ d x d ∈ˢ A₁
            rw [setAt_self]
            exact hx
          · exact Ctx.setAbove hp.ty.1 hCty₁ l hl
        exact hbody hp.open (Frame.app_iff.2 ⟨Frame.succ hfb, Frame.fvar_fresh hp.ty⟩)
          (setAt σ d x)
          (Ctx.open hp.ty.1 hp.ws hCty₁ hCb₁ hA₁ hx hgty₁) hCapp _ _
          ((DenotesO.open_fvar hfresh ρ₀ _).2 (hF₁ x hx)) (.app hwx hfx)
          ((GradedBy.open_fvarO hfresh ρ₀).2 (hgb₁ _ hA₁ x hx))
          (Gr.app_iff.2 ⟨(Gr.setAbove hfb.1).2 hgb, True.intro, _, A₂, w, x, B₂, hwx, hfx,
            hwTb, (by rw [hAA]; exact hx), hP₂⟩)
      rw [hpw, lamR_congr hagree, ← hAA]
      exact lamR_eta hwTb

end Ix.Kernel.Open
