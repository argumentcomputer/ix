/-
  Ix.Theory.Confluence: Confluence via NbE.

  If two expressions are definitionally equal (`IsDefEq`), their NbE normal
  forms are themselves definitionally equal. This replaces the traditional
  Church-Rosser / parallel reduction approach with a direct NbE argument.

  **Why not syntactic confluence?** The stronger claim that def-eq terms
  NbE to the *same* expression is false due to:
  1. Eta: `.lam A (.app e.lift (.bvar 0)) ≈ e` but NbE gives different results
     (lambda wrapper vs bare neutral).
  2. Extra axioms: `lhs ≈ rhs` but both are NbE-stable distinct normal forms.
  3. Proof irrelevance: `h ≈ h'` for proofs of the same Prop, but different
     normal forms.
  Syntactic confluence would require typed NbE (eta-long normal forms) or
  extending `isDefEq_s` with eta/proofIrrel — Phase 9+ material.

  Reference: docs/theory/kernel.md Part VI (lines 566-598).
-/
import Ix.Theory.NbESoundness
import Ix.Theory.DefEq

namespace Ix.Theory

open SExpr

/-! ## Confluence up to definitional equality

    The main result: NbE normal forms of def-eq terms are themselves def-eq.
    Follows directly from `nbe_preservation` + transitivity/symmetry of `IsDefEq`. -/

/-- **Confluence**: if `e₁ ≡ e₂ : A` and both NbE's succeed,
    the normal forms are definitionally equal at the same type. -/
theorem confluence_defeq
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    (hextra_nf : ∀ df (ls : List SLevel) d, env.defeqs df →
      (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
      (∀ f v fq (e' : TExpr), eval_s f (df.lhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.lhs.instL ls) ∧
      (∀ f v fq (e' : TExpr), eval_s f (df.rhs.instL ls) (fvarEnv d) = some v →
        quote_s fq v d = some e' → e' = df.rhs.instL ls))
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    (hctx : CtxScoped Γ)
    {d : Nat} (hd : d = Γ.length)
    {f₁ f₂ : Nat} {e₁' e₂' : TExpr}
    (hnbe₁ : nbe_s f₁ e₁ (fvarEnv d) d = some e₁')
    (hnbe₂ : nbe_s f₂ e₂ (fvarEnv d) d = some e₂') :
    IsDefEq env uvars litType projType Γ e₁' e₂' A := by
  -- From nbe_preservation: NbEProp for both sides
  have ⟨hp₁, hp₂⟩ := h.nbe_preservation henv hlt hpt_closed hpt hpt_inst hextra_nf hctx hd
  -- Decompose nbe into eval + quote for each side
  simp only [nbe_s, bind, Option.bind] at hnbe₁ hnbe₂
  cases hev₁ : eval_s f₁ e₁ (fvarEnv d) with
  | none => simp [hev₁] at hnbe₁
  | some v₁ =>
    simp [hev₁] at hnbe₁
    cases hev₂ : eval_s f₂ e₂ (fvarEnv d) with
    | none => simp [hev₂] at hnbe₂
    | some v₂ =>
      simp [hev₂] at hnbe₂
      -- Apply NbEProp: e₁ ≡ e₁' and e₂ ≡ e₂'
      have h₁ := hp₁ f₁ v₁ f₁ e₁' hev₁ hnbe₁
      have h₂ := hp₂ f₂ v₂ f₂ e₂' hev₂ hnbe₂
      -- Chain: e₁' ≡ e₁ ≡ e₂ ≡ e₂'
      exact .trans (.symm h₁) (.trans h h₂)

/-! ## NbE produces fixed points

    The NbE of a well-typed term is an NbE fixed point (idempotent).
    This is a purely computational result — no typing sorries needed. -/

/-- NbE of a well-typed term is an NbE fixed point: `nbe(nbe(e)) = nbe(e)`. -/
theorem nbe_normal_form
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt_closed : ∀ t i s sType k, ClosedN s k → ClosedN sType k →
      ClosedN (projType t i s sType) k)
    {Γ : List TExpr} {e A : TExpr}
    (h : HasType env uvars litType projType Γ e A)
    (hctx : CtxScoped Γ)
    {d : Nat} (hd : d = Γ.length)
    {f : Nat} {e' : TExpr}
    (hnbe : nbe_s f e (fvarEnv d) d = some e') :
    ∃ f', nbe_s f' e' (fvarEnv (L := SLevel) d) d = some e' := by
  subst hd
  -- Decompose nbe into eval + quote
  simp only [nbe_s, bind, Option.bind] at hnbe
  cases hev : eval_s f e (fvarEnv (List.length Γ)) with
  | none => simp [hev] at hnbe
  | some v =>
    simp [hev] at hnbe
    -- Get well-scopedness from typing
    have hcl := (h.closedN henv hlt hpt_closed hctx).1
    -- Get ValWF from eval_preserves_wf
    have hwf := eval_preserves_wf hev
      (by rw [fvarEnv_length]; exact hcl) (EnvWF_fvarEnv _)
    -- Apply nbe_stable
    exact nbe_stable f v _ e' hwf hnbe

/-! ## Conditional syntactic confluence

    When the computational checker `isDefEq_s` agrees, the normal forms are
    syntactically equal. This is a direct wrapper around `isDefEq_sound`. -/

/-- **Syntactic confluence** (conditional): if two values pass `isDefEq_s`,
    they quote to the same expression. -/
theorem confluence_syntactic
    [BEq L] [LawfulBEq L] {v₁ v₂ : SVal L} {d : Nat}
    (hwf₁ : ValWF v₁ d) (hwf₂ : ValWF v₂ d)
    {fuel : Nat}
    (hdeq : isDefEq_s fuel v₁ v₂ d = some true) :
    ∃ fq₁ fq₂ e, quote_s fq₁ v₁ d = some e ∧ quote_s fq₂ v₂ d = some e :=
  isDefEq_sound hdeq hwf₁ hwf₂

/-! ## Computational def-eq reflects typing

    If the computational `isDefEq_s` succeeds and one side is well-typed,
    both sides are definitionally equal in the typing judgment. -/

/-- `isDefEq_s` returning `true` implies `IsDefEq` in the typing judgment,
    given that the quoted expression is well-typed. -/
theorem isDefEq_s_reflects_typing
    {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    {v₁ v₂ : SVal SLevel} {d : Nat}
    (hwf₁ : ValWF v₁ d) (hwf₂ : ValWF v₂ d)
    {fuel : Nat}
    (hdeq : isDefEq_s fuel v₁ v₂ d = some true)
    {fq₁ fq₂ : Nat} {e₁ e₂ : TExpr}
    (hq₁ : quote_s fq₁ v₁ d = some e₁)
    (hq₂ : quote_s fq₂ v₂ d = some e₂)
    {Γ : List TExpr} {A : TExpr}
    (hty : HasType env uvars litType projType Γ e₁ A) :
    IsDefEq env uvars litType projType Γ e₁ e₂ A := by
  -- By isDefEq_sound, v₁ and v₂ quote to the SAME expression
  obtain ⟨fq₁', fq₂', e, hq₁', hq₂'⟩ := isDefEq_sound hdeq hwf₁ hwf₂
  -- Quoting is deterministic (fuel monotonicity): e₁ = e and e₂ = e
  have he₁ : e₁ = e := by
    have := quote_fuel_mono hq₁ (Nat.le_max_left fq₁ fq₁')
    have := quote_fuel_mono hq₁' (Nat.le_max_right fq₁ fq₁')
    simp_all
  have he₂ : e₂ = e := by
    have := quote_fuel_mono hq₂ (Nat.le_max_left fq₂ fq₂')
    have := quote_fuel_mono hq₂' (Nat.le_max_right fq₂ fq₂')
    simp_all
  -- e₁ = e₂, so HasType gives IsDefEq directly
  subst he₁; subst he₂
  exact hty

/-! ## Sanity checks -/

-- Confluence: beta-reduced and unreduced forms are def-eq after NbE
-- (.app (.lam (.sort 0) (.bvar 0)) (.lit 5)) NbE's to (.lit 5)
#guard nbe_s 20 (.app (.lam (.sort 0) (.bvar 0)) (.lit 5) : SExpr Nat) [] 0 ==
    some (.lit 5)
-- (.lit 5) NbE's to (.lit 5)
#guard nbe_s 20 (.lit 5 : SExpr Nat) [] 0 == some (.lit 5)

-- Let-reduction: (.letE (.sort 0) (.lit 42) (.bvar 0)) and (.lit 42) both NbE to (.lit 42)
#guard nbe_s 20 (.letE (.sort 0) (.lit 42) (.bvar 0) : SExpr Nat) [] 0 ==
    some (.lit 42)

-- Nested beta: (fun x y => x) 1 2 and (fun y => 1) 2 both NbE to 1
#guard nbe_s 40
    (.app (.app (.lam (.sort 0) (.lam (.sort 0) (.bvar 1))) (.lit 1)) (.lit 2) : SExpr Nat)
    [] 0 == some (.lit 1)
#guard nbe_s 40
    (.app (.lam (.sort 0) (.lit 1)) (.lit 2) : SExpr Nat) [] 0 == some (.lit 1)

end Ix.Theory
