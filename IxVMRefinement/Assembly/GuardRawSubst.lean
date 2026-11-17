import IxVMRefinement.Assembly.GuardRawExact

/-! # Exact raw syntax for capture-avoiding binder substitution

The raw expression keeps its let cells and binder metadata. The semantic reading is retained
existentially because raw head computation does not need a licensed reduction judgement.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll IdxLt)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A completely specified raw expression with a bound on its ambient de Bruijn variables. -/
def RawExprRep (κ : _root_.Address → KKey) (h : Heap F) (k : Nat) (R : KExpr)
    (p : SourceValue F) : Prop :=
  ∃ E, RawTmExact κ 0 (fun _ => default) h k R E p

/-- Enlarging the ambient variable bound preserves both exact readings. -/
theorem RawTmExact.weaken_bound {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {k'}, k ≤ k' → RawTmExact κ 0 Γ h k' R E p := by
  induction rep with
  | bvarLocal cell small inside => intro k' bound; exact .bvarLocal cell small (by omega)
  | bvarFree _ _ _ impossible => omega
  | sort cell level => intro k' _; exact .sort cell level
  | const cell address levels => intro k' _; exact .const cell address levels
  | app cell _ _ left right => intro k' bound; exact .app cell (left bound) (right bound)
  | lam cell _ _ level dom body =>
    intro k' bound; exact .lam cell (dom bound) (body (by omega)) level
  | forallE cell _ _ level dom body =>
    intro k' bound; exact .forallE cell (dom bound) (body (by omega)) level
  | letE cell _ _ _ type value body =>
    intro k' bound; exact .letE cell (type bound) (value bound) (body (by omega))
  | litNat cell limbs canonical => intro k' _; exact .litNat cell limbs canonical
  | litStr cell bytes string => intro k' _; exact .litStr cell bytes string
  | proj cell address _ inner => intro k' bound; exact .proj cell address (inner bound)

theorem RawExprRep.mono {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p : SourceValue F} (represented : RawExprRep κ h k R p)
    (extension : Heap.Extends h h') : RawExprRep κ h' k R p := by
  obtain ⟨E, rep⟩ := represented
  exact ⟨E, rep.mono extension⟩

theorem RawExprRep.weaken {κ : _root_.Address → KKey} {h : Heap F} {k k' : Nat}
    {R : KExpr} {p : SourceValue F} (represented : RawExprRep κ h k R p)
    (bound : k ≤ k') : RawExprRep κ h k' R p := by
  obtain ⟨E, rep⟩ := represented
  exact ⟨E, rep.weaken_bound bound⟩

/-- Heap index bounds apply to all raw syntax, including the type and value of every let. -/
theorem RawTmExact.raw_bounded_of_idx {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {m bound}, IdxAll h (fun n i => i.val < bound + n) m p →
      R.looseBVarsBounded (bound + m) = true := by
  induction rep with
  | bvarLocal cell small inside =>
    intro m bound indices
    obtain ⟨i, equal, below⟩ := SubstAux.idxAll_bvar_inv indices (loadValue_enum_cell cell)
    injection equal with equal
    subst equal
    exact decide_eq_true below
  | bvarFree _ _ _ impossible => omega
  | sort | const | litNat | litStr => intro _ _ _; rfl
  | app cell _ _ left right =>
    intro m bound indices
    obtain ⟨func, arg⟩ := SubstAux.idxAll_app_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨left func, right arg⟩
  | lam cell _ _ _ dom body =>
    intro m bound indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_lam_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | forallE cell _ _ _ dom body =>
    intro m bound indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_forallE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | letE cell _ _ _ type value body =>
    intro m bound indices
    obtain ⟨typeIndices, valueIndices, tail⟩ := SubstAux.idxAll_letE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨type typeIndices, value valueIndices⟩,
      by simpa only [Nat.add_assoc] using body tail⟩
  | proj cell address _ inner =>
    intro m bound indices
    exact inner (SubstAux.idxAll_proj_inv indices (loadValue_enum_cell cell))

end IxVM.Refinement.Decl
