/-
  Ix.Theory.TypingLemmas: Structural lemmas for the IsDefEq typing judgment.

  Proves environment monotonicity and weakening.
  Prerequisites for Phase 5 (NbE soundness bridge).

  Reference: docs/theory/kernel.md Part IV (lines 449-495).
-/
import Ix.Theory.Typing

namespace Ix.Theory

open SExpr

/-! ## Environment Monotonicity -/

theorem IsDefEq.envMono {env env' : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    (hle : env ≤ env') :
    IsDefEq env' uvars litType projType Γ e₁ e₂ A := by
  induction h with
  | bvar lookup => exact .bvar lookup
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF hc hwf hwf' hlen heq =>
    exact .constDF (hle.constants hc) hwf hwf' hlen heq
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra hdf hwf hlen => exact .extra (hle.defeqs hdf) hwf hlen
  | letDF _ _ _ ih1 ih2 ih3 => exact .letDF ih1 ih2 ih3
  | letZeta _ _ _ ih1 ih2 ih3 => exact .letZeta ih1 ih2 ih3
  | litDF => exact .litDF
  | projDF _ ih => exact .projDF ih

/-! ## LiftCtx: Context transformation for weakening -/

inductive LiftCtx (n : Nat) : Nat → List TExpr → List TExpr → Prop where
  | base : Δ.length = n → LiftCtx n 0 Γ (Δ ++ Γ)
  | step : LiftCtx n k Γ Γ' →
           LiftCtx n (k+1) (A :: Γ) (A.liftN n k :: Γ')

/-! ## Lookup lemmas -/

theorem Lookup.prepend {Γ : List TExpr} {i : Nat} {ty : TExpr}
    (Δ : List TExpr) (hl : Lookup Γ i ty) :
    Lookup (Δ ++ Γ) (Δ.length + i) (ty.liftN Δ.length) := by
  induction Δ with
  | nil => simp [liftN_zero]; exact hl
  | cons D Δ' ih =>
    rw [List.length_cons, liftN_succ, Nat.add_right_comm]
    exact .succ ih

theorem Lookup.liftN {Γ : List TExpr} {i : Nat} {ty : TExpr}
    (hl : Lookup Γ i ty) {n k : Nat} {Γ' : List TExpr}
    (hctx : LiftCtx n k Γ Γ') :
    Lookup Γ' (liftVar n i k) (ty.liftN n k) := by
  induction hl generalizing n k Γ' with
  | @zero A Γ₀ =>
    cases hctx with
    | @base _ Δ hlen =>
      subst hlen
      exact .prepend Δ .zero
    | step hctx' =>
      rw [liftVar_lt (Nat.zero_lt_succ _)]
      conv => rhs; rw [← lift_liftN']
      exact .zero
  | @succ Γ₀ m tyInner A _ ih =>
    cases hctx with
    | @base _ Δ hlen =>
      subst hlen
      exact .prepend Δ (.succ ‹_›)
    | step hctx' =>
      rw [liftVar_succ]
      conv => rhs; rw [← lift_liftN']
      exact .succ (ih hctx')

/-! ## Environment well-formedness for weakening -/

/-- Well-formedness conditions on the environment needed for weakening:
    all constant types and defeq entries are closed (no free bvars). -/
structure SEnv.WFClosed (env : SEnv) : Prop where
  constClosed : ∀ c ci, env.constants c = some ci → ci.type.Closed
  defeqClosed : ∀ df, env.defeqs df → df.lhs.Closed ∧ df.rhs.Closed ∧ df.type.Closed

/-! ## General weakening (liftN) -/

theorem IsDefEq.liftN {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    {n k : Nat} {Γ' : List TExpr}
    (hctx : LiftCtx n k Γ Γ') :
    IsDefEq env uvars litType projType Γ'
      (e₁.liftN n k) (e₂.liftN n k) (A.liftN n k) := by
  induction h generalizing n k Γ' with
  | bvar lookup =>
    simp only [SExpr.liftN]
    exact .bvar (lookup.liftN hctx)
  | symm _ ih => exact .symm (ih hctx)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hctx) (ih2 hctx)
  | sortDF hwf1 hwf2 heq =>
    simp only [SExpr.liftN]
    exact .sortDF hwf1 hwf2 heq
  | constDF hc hwf hwf' hlen heq =>
    simp only [SExpr.liftN]
    rw [ClosedN.liftN_eq ((henv.constClosed _ _ hc).instL _) (Nat.zero_le _)]
    exact .constDF hc hwf hwf' hlen heq
  | appDF _ _ ih_f ih_a =>
    simp only [SExpr.liftN]
    rw [liftN_inst_hi]
    exact .appDF (ih_f hctx) (ih_a hctx)
  | lamDF _ _ ih_A ih_body =>
    simp only [SExpr.liftN]
    exact .lamDF (ih_A hctx) (ih_body (.step hctx))
  | forallEDF _ _ ih_A ih_body =>
    simp only [SExpr.liftN]
    exact .forallEDF (ih_A hctx) (ih_body (.step hctx))
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hctx) (ih2 hctx)
  | beta _ _ ih_body ih_arg =>
    simp only [SExpr.liftN]
    rw [liftN_inst_hi, liftN_inst_hi]
    exact .beta (ih_body (.step hctx)) (ih_arg hctx)
  | eta _ ih =>
    simp only [SExpr.liftN, liftVar_lt (Nat.zero_lt_succ _)]
    rw [← lift_liftN']
    exact .eta (ih hctx)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel (ih1 hctx) (ih2 hctx) (ih3 hctx)
  | extra hdf hwf hlen =>
    have ⟨hcl_l, hcl_r, hcl_t⟩ := henv.defeqClosed _ hdf
    rw [(hcl_l.instL _).liftN_eq (Nat.zero_le _),
        (hcl_r.instL _).liftN_eq (Nat.zero_le _),
        (hcl_t.instL _).liftN_eq (Nat.zero_le _)]
    exact .extra hdf hwf hlen
  | letDF _ _ _ ih_ty ih_val ih_body =>
    simp only [SExpr.liftN]
    rw [liftN_inst_hi]
    exact .letDF (ih_ty hctx) (ih_val hctx) (ih_body (.step hctx))
  | letZeta _ _ _ ih_ty ih_val ih_body =>
    simp only [SExpr.liftN]
    rw [liftN_inst_hi, liftN_inst_hi]
    exact .letZeta (ih_ty hctx) (ih_val hctx) (ih_body (.step hctx))
  | litDF =>
    rw [hlt.liftN_eq (Nat.zero_le _)]
    simp only [SExpr.liftN]
    exact .litDF
  | projDF _ ih =>
    simp only [SExpr.liftN]
    rw [hpt]
    exact .projDF (ih hctx)

/-- Single-step weakening: add one type at the front of the context. -/
theorem IsDefEq.weakening {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    {Γ : List TExpr} {e₁ e₂ A B : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A) :
    IsDefEq env uvars litType projType (B :: Γ)
      e₁.lift e₂.lift A.lift :=
  h.liftN henv hlt hpt (.base (Δ := [B]) rfl)

/-! ## InstCtx: Context transformation for substitution -/

inductive InstCtx (env : SEnv) (uvars : Nat) (litType : TExpr)
    (projType : Nat → Nat → TExpr → TExpr → TExpr) :
    Nat → List TExpr → TExpr → List TExpr → Prop where
  | base : HasType env uvars litType projType Γ a A →
           InstCtx env uvars litType projType 0 (A :: Γ) a Γ
  | step : InstCtx env uvars litType projType k Γ a Γ' →
           InstCtx env uvars litType projType (k+1) (B :: Γ) a (B.inst a k :: Γ')

/-! ## Lookup under substitution -/

theorem Lookup.instN {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    {Γ : List TExpr} {i : Nat} {ty : TExpr}
    (hl : Lookup Γ i ty)
    {k : Nat} {a : TExpr} {Γ' : List TExpr}
    (hctx : InstCtx env uvars litType projType k Γ a Γ') :
    IsDefEq env uvars litType projType Γ'
      (instVar i a k) (instVar i a k) (ty.inst a k) := by
  induction hl generalizing k a Γ' with
  | @zero A Γ₀ =>
    cases hctx with
    | base ha =>
      simp only [instVar_zero, inst_lift]
      exact ha
    | step hctx' =>
      simp only [instVar_lower]
      rw [← lift_instN_lo]
      exact .bvar .zero
  | @succ Γ₀ m tyInner A _ ih =>
    cases hctx with
    | base ha =>
      simp only [instVar_upper, inst_lift]
      exact .bvar ‹_›
    | step hctx' =>
      rw [instVar_succ, ← lift_instN_lo]
      exact (ih hctx').weakening henv hlt hpt

/-! ## General substitution (instN) -/

theorem IsDefEq.instN {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    {Γ : List TExpr} {e₁ e₂ A : TExpr}
    (h : IsDefEq env uvars litType projType Γ e₁ e₂ A)
    {k : Nat} {a : TExpr} {Γ' : List TExpr}
    (hctx : InstCtx env uvars litType projType k Γ a Γ') :
    IsDefEq env uvars litType projType Γ'
      (e₁.inst a k) (e₂.inst a k) (A.inst a k) := by
  induction h generalizing k a Γ' with
  | bvar lookup =>
    simp only [SExpr.inst]
    exact lookup.instN henv hlt hpt hctx
  | symm _ ih => exact .symm (ih hctx)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hctx) (ih2 hctx)
  | sortDF hwf1 hwf2 heq =>
    simp only [SExpr.inst]
    exact .sortDF hwf1 hwf2 heq
  | constDF hc hwf hwf' hlen heq =>
    simp only [SExpr.inst]
    rw [ClosedN.instN_eq ((henv.constClosed _ _ hc).instL _) (Nat.zero_le _)]
    exact .constDF hc hwf hwf' hlen heq
  | appDF _ _ ih_f ih_a =>
    simp only [SExpr.inst]
    rw [inst0_inst_hi]
    exact .appDF (ih_f hctx) (ih_a hctx)
  | lamDF _ _ ih_A ih_body =>
    simp only [SExpr.inst]
    exact .lamDF (ih_A hctx) (ih_body (.step hctx))
  | forallEDF _ _ ih_A ih_body =>
    simp only [SExpr.inst]
    exact .forallEDF (ih_A hctx) (ih_body (.step hctx))
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hctx) (ih2 hctx)
  | beta _ _ ih_body ih_arg =>
    simp only [SExpr.inst]
    rw [inst0_inst_hi, inst0_inst_hi]
    exact .beta (ih_body (.step hctx)) (ih_arg hctx)
  | eta _ ih =>
    simp only [SExpr.inst, instVar_lower]
    rw [← lift_instN_lo]
    exact .eta (ih hctx)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel (ih1 hctx) (ih2 hctx) (ih3 hctx)
  | extra hdf hwf hlen =>
    have ⟨hcl_l, hcl_r, hcl_t⟩ := henv.defeqClosed _ hdf
    rw [(hcl_l.instL _).instN_eq (Nat.zero_le _),
        (hcl_r.instL _).instN_eq (Nat.zero_le _),
        (hcl_t.instL _).instN_eq (Nat.zero_le _)]
    exact .extra hdf hwf hlen
  | letDF _ _ _ ih_ty ih_val ih_body =>
    simp only [SExpr.inst]
    rw [inst0_inst_hi]
    exact .letDF (ih_ty hctx) (ih_val hctx) (ih_body (.step hctx))
  | letZeta _ _ _ ih_ty ih_val ih_body =>
    simp only [SExpr.inst]
    rw [inst0_inst_hi, inst0_inst_hi]
    exact .letZeta (ih_ty hctx) (ih_val hctx) (ih_body (.step hctx))
  | litDF =>
    rw [hlt.instN_eq (Nat.zero_le _)]
    simp only [SExpr.inst]
    exact .litDF
  | projDF _ ih =>
    simp only [SExpr.inst]
    rw [hpt_inst]
    exact .projDF (ih hctx)

/-- Substitution: substitute a well-typed term into a judgment. -/
theorem IsDefEq.substitution {env : SEnv} {uvars : Nat}
    {litType : TExpr} {projType : Nat → Nat → TExpr → TExpr → TExpr}
    (henv : env.WFClosed)
    (hlt : litType.Closed)
    (hpt : ∀ t i s sType n k,
      (projType t i s sType).liftN n k =
      projType t i (s.liftN n k) (sType.liftN n k))
    (hpt_inst : ∀ t i s sType a k,
      (projType t i s sType).inst a k =
      projType t i (s.inst a k) (sType.inst a k))
    {Γ : List TExpr} {e₁ e₂ A B : TExpr}
    (h : IsDefEq env uvars litType projType (A :: Γ) e₁ e₂ B)
    {a : TExpr}
    (ha : HasType env uvars litType projType Γ a A) :
    IsDefEq env uvars litType projType Γ
      (e₁.inst a) (e₂.inst a) (B.inst a) :=
  h.instN henv hlt hpt hpt_inst (.base ha)

end Ix.Theory
