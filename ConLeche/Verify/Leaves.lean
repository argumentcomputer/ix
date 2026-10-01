module

import ConLeche.Kernel.ExprOps
import ConLeche.Verify.Shift
public import ConLeche.Verify.Abstract
import ConLeche.Verify.Knot

public section

/-!
# The free-variable leaf closure

`fvarLeaves e` lists every reachable `fvar` leaf of `e` together with,
hereditarily, the leaves of their type annotations.  The local-context
assumptions (`FvarsOk`) are conditions on exactly this list, so every
syntactic transformation only needs a subset lemma here.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Expr

/-- Closed terms have no leaves. -/
theorem fvarLeaves_eq_nil_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> simp_all [hasFvar, fvarLeaves]

/-- Instantiation only introduces the substituted term's leaves. -/
theorem fvarLeaves_instantiate1 {a : Expr} :
    ∀ (e : Expr) (k : Nat) {l}, l ∈ (e.instantiate1 a k).fvarLeaves →
      l ∈ e.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  intro e
  induction e with
  | bvar i =>
    intro k l hl
    simp only [instantiate1] at hl
    split at hl
    · exact Or.inr hl
    · split at hl <;> simp [fvarLeaves] at hl
  | fvar idx ty _ =>
    intro k l hl
    simp only [instantiate1] at hl
    exact Or.inl hl
  | app f b ihf ihb =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihf k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb k hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam ty body m ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | forallE ty body m ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE ty v body ihty ihv ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases ihv k hl with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | proj s i e ih =>
    intro k l hl
    simp only [instantiate1, fvarLeaves] at hl ⊢
    exact ih k hl
  | sort u => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | const n us => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | lit ll => intro k l hl; simp [instantiate1, fvarLeaves] at hl

/-- Well-scopedness gives bounds and scoping for every closure leaf. -/
theorem WScoped_leaves : ∀ (e : Expr) {d : Nat}, WScoped d e →
    ∀ l ∈ e.fvarLeaves, l.1 < d ∧ WScoped l.1 l.2 := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨hw.1, hw.2⟩
    · obtain ⟨h1, h2⟩ := ih hw.2 l hl
      exact ⟨by omega, h2⟩
  | app f a ihf iha =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hw.1 l hl
    · exact iha hw.2 l hl
  | lam ty body m ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | forallE ty body m ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | letE ty val body ihty ihval ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hw.1 l hl
    · exact ihval hw.2.1 l hl
    · exact ihbody hw.2.2 l hl
  | proj s i e ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves] at hl
    exact ih hw l hl
  | bvar i => intro d _ l hl; simp [fvarLeaves] at hl
  | sort u => intro d _ l hl; simp [fvarLeaves] at hl
  | const n us => intro d _ l hl; simp [fvarLeaves] at hl
  | lit ll => intro d _ l hl; simp [fvarLeaves] at hl

/-- Leaves of a well-scoped term have indices below the scope. -/
theorem fvarLeaves_lt_of_wscoped :
    ∀ {e : Expr} {D : Nat}, WScoped D e → ∀ l ∈ e.fvarLeaves, l.1 < D := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hw.1
    · exact Nat.lt_trans (ih hw.2 l hl) hw.1
  | app f a ihf iha =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hw.1 l hl
    · exact iha hw.2 l hl
  | lam ty body m ihty ihbody =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | forallE ty body m ihty ihbody =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | letE ty val body ihty ihval ihbody =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hw.1 l hl
    · exact ihval hw.2.1 l hl
    · exact ihbody hw.2.2 l hl
  | proj sn i e ih =>
    intro D hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves] at hl
    exact ih hw l hl
  | bvar i => intro D _ l hl; simp [fvarLeaves] at hl
  | sort u => intro D _ l hl; simp [fvarLeaves] at hl
  | const n us => intro D _ l hl; simp [fvarLeaves] at hl
  | lit ll => intro D _ l hl; simp [fvarLeaves] at hl

/-- Abstracting the scope's top index removes exactly its leaves: the
survivors are original leaves strictly below it. -/
theorem fvarLeaves_abstract1_lt {D : Nat} :
    ∀ (e : Expr) (k : Nat), WScoped (D + 1) e →
      ∀ l ∈ (e.abstract1 D k).fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 < D := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl
      have hidx : idx < D := by omega
      rcases hl with rfl | hl
      · exact ⟨by simp [fvarLeaves], hidx⟩
      · exact ⟨by simp [fvarLeaves, hl],
          Nat.lt_trans (fvarLeaves_lt_of_wscoped hw.2 l hl) hidx⟩
  | app f a ihf iha =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := iha k hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | lam ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | forallE ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihval k hw.2.1 l hl
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | proj sn i e ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hw l hl
  | bvar i => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | sort u => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k _ l hl; simp [abstract1, fvarLeaves] at hl

end ConLeche.Expr

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- Annotation only shrinks the free-variable leaf closure (the
projection-elimination path is guarded to stay inside it). -/
theorem annotateCore_leaves_sub {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore mode env fuel d e = .ok e' → WScoped d e →
      e.looseBVarsBounded 0 = true →
      ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves
  | 0, _, _, _, h, _, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, _, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro l hl; exact hl
  | fuel + 1, .fvar idx ty, d, e', h, _, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody] at h
    revert h
    split
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; exact hl
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, .sort u, d, e', h, _, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro l hl; exact hl
  | fuel + 1, .const n us, d, e', h, _, _ => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro l hl; exact hl
  | fuel + 1, .app f a, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨f', a', hf, ha, rfl, -⟩ := annotateCore_app_inv h
    intro l hl
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (annotateCore_leaves_sub fuel f hf hw.1 hb.1 l hl)
    · exact Or.inr (annotateCore_leaves_sub fuel a ha hw.2 hb.2 l hl)
  | fuel + 1, .proj sn i e, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded] at hb
    obtain ⟨e₂, tt, te, he, -, -, us, A, B, cv2, caps2, -, -, -, rfl⟩ :=
      annotateCore_proj_inv h
    have hsub₂ : ∀ l ∈ e₂.fvarLeaves, l ∈ e.fvarLeaves :=
      annotateCore_leaves_sub fuel e he hw hb
    intro l hl
    simp only [fvarLeaves] at hl ⊢
    exact hsub₂ l hl
  | fuel + 1, .forallE ty body m, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_forallE_inv h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    have hwbody' := annotateCore_WScoped fuel
      (body.instantiate1 (.fvar d ty')) hbody (hwty'.instantiate1 0 hw.2)
    have hsubty : ∀ l ∈ ty'.fvarLeaves, l ∈ ty.fvarLeaves :=
      annotateCore_leaves_sub fuel ty hty hw.1 hb.1
    have hsubbody : ∀ l ∈ body'.fvarLeaves,
        l ∈ (body.instantiate1 (.fvar d ty')).fvarLeaves :=
      annotateCore_leaves_sub fuel _ hbody (hwty'.instantiate1 0 hw.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2)
    intro l hl
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (hsubty l hl)
    · obtain ⟨hl', hlt⟩ := fvarLeaves_abstract1_lt body' 0 hwbody' l hl
      have hl2 := hsubbody l hl'
      rcases fvarLeaves_instantiate1 body 0 hl2 with h2 | h2
      · exact Or.inr h2
      · simp only [fvarLeaves, List.mem_cons] at h2
        rcases h2 with rfl | h2
        · omega
        · exact Or.inl (hsubty l h2)
  | fuel + 1, .lam ty body m, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', body', pw, hty, hbody, rfl⟩ := annotateCore_lam_inv h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    have hwbody' := annotateCore_WScoped fuel
      (body.instantiate1 (.fvar d ty')) hbody (hwty'.instantiate1 0 hw.2)
    have hsubty : ∀ l ∈ ty'.fvarLeaves, l ∈ ty.fvarLeaves :=
      annotateCore_leaves_sub fuel ty hty hw.1 hb.1
    have hsubbody : ∀ l ∈ body'.fvarLeaves,
        l ∈ (body.instantiate1 (.fvar d ty')).fvarLeaves :=
      annotateCore_leaves_sub fuel _ hbody (hwty'.instantiate1 0 hw.2)
        (looseBVarsBounded_instantiate1 body 0 hb.2)
    intro l hl
    simp only [fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (hsubty l hl)
    · obtain ⟨hl', hlt⟩ := fvarLeaves_abstract1_lt body' 0 hwbody' l hl
      have hl2 := hsubbody l hl'
      rcases fvarLeaves_instantiate1 body 0 hl2 with h2 | h2
      · exact Or.inr h2
      · simp only [fvarLeaves, List.mem_cons] at h2
        rcases h2 with rfl | h2
        · omega
        · exact Or.inl (hsubty l h2)
  | fuel + 1, .letE ty v b, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨ty', v', -, -, hbody, -⟩ := annotateCore_letE_inv h
    have hsub := annotateCore_leaves_sub fuel _ hbody
      (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
      (looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
    intro l hl
    simp only [fvarLeaves, List.mem_append]
    rcases fvarLeaves_instantiate1 b 0 (hsub l hl) with h2 | h2
    · exact Or.inr h2
    · exact Or.inl (Or.inr h2)
  | fuel + 1, .lit l, d, e', h, _, _ => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?natCase
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; intro l' hl'; exact hl'
    case natCase =>
      dsimp only [annotateBody] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; intro l' hl'; exact hl'

end ConLeche
