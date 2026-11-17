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

/-- The actual loose-bound scan gives a bound on the retained raw syntax, not only its
let-erased semantic image. -/
theorem RawExprRep.lbr {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_lbr" [p] h r h' calls) :
    h' = h ∧ ∃ (bound : Nat), r = .field (bound : F) ∧ bound ≤ 9223372036854775808 ∧
      R.looseBVarsBounded bound = true := by
  obtain ⟨E, rep⟩ := represented
  obtain ⟨unchanged, scan⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ observed p rfl bounded
  obtain ⟨bound, result, small, _, indices, _⟩ := scan 0 (fun _ => default) k E rep.toTmExact.toTm
  refine ⟨unchanged, bound, result, small, ?_⟩
  simpa only [Nat.add_zero] using rep.raw_bounded_of_idx indices

/-- The actual lifted-variable primitive preserves the exact de Bruijn index. The successful
comparison bounds the input by 2^32; the explicit shift bound prevents field wraparound. -/
theorem raw_lift_bvar_exact {κ : _root_.Address → KKey} {h h' : Heap F}
    {k : Nat} {i shift cutoff : F} {r : SourceValue F} {calls : List (Call F)}
    (small : i.val < 9223372036854775808) (inside : i.val < k)
    (shiftBound : shift.val < 4611686018427387904)
    (observed : ObsFn W "KernelSubst::expr_lift_bvar"
      [.field i, .field shift, .field cutoff] h r h' calls) :
    RawExprRep κ h' (k + shift.val)
      ((.bvar i.val : KExpr).liftLooseBVars shift.val cutoff.val) r := by
  cases Obs.«KernelSubst::expr_lift_bvar».obs observed with
  | n1 m2 childCalls comparison result heap events =>
    obtain ⟨i', cutoff', hi, hc, _, _, verdict, rfl⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hc with hc
    subst hi hc result heap
    have below := SubstAux.ltf_one verdict.symm
    have rep : RawExprRep κ (m2 ++ [.construct kexprEnum "BVar" [.field i]])
        (k + shift.val) (.bvar i.val) (.ptr (.enum kexprEnum) m2.length) :=
      ⟨_, .bvarLocal (by simp) small (by omega)⟩
    simpa [Expr.liftLooseBVars, show ¬ cutoff.val ≤ i.val by omega] using rep
  | n0 m2 childCalls value comparison result heap added events =>
    obtain ⟨i', cutoff', hi, hc, inputBound, _, verdict, rfl⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hc with hc
    subst hi hc result heap
    have above := SubstAux.ltf_zero verdict.symm
    rw [SubstAux.add_ok added]
    have sumValue : (i + shift).val = i.val + shift.val :=
      SubstAux.val_add (by
        have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
        omega)
    have rep : RawExprRep κ (m2 ++ [.construct kexprEnum "BVar" [.field (i + shift)]])
        (k + shift.val) (.bvar (i + shift).val) (.ptr (.enum kexprEnum) m2.length) :=
      ⟨_, .bvarLocal (by simp) (by rw [sumValue]; omega) (by rw [sumValue]; omega)⟩
    simpa [Expr.liftLooseBVars, show cutoff.val ≤ i.val by omega, sumValue] using rep


end IxVM.Refinement.Decl
