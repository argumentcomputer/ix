import IxVMRefinement.Assembly.GuardRawSubst
import IxC.Kernel.Inductives.StructParts

/-! # Actual capture-avoiding substitution of retained raw syntax

The source substitutes open de Bruijn arguments with lifting. Its absence shortcut lowers a
variable window; both paths must match instantiate1Lift, without identifying it with the
closed-argument semantic substitution specification.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll NoIdx)
open Ix.Kernel (Expr)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The actual heap exclusion window excludes the corresponding variable from retained lets
as well as every other part of the raw syntax. -/
theorem RawTmExact.raw_absent_of_idx {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {m j}, IdxAll h (fun n i => i.val < j + n ∨ j + 1 + n ≤ i.val) m p →
      R.hasLooseBVar (j + m) = false := by
  induction rep with
  | bvarLocal cell small inside =>
    intro m j indices
    obtain ⟨i, equal, outside⟩ := SubstAux.idxAll_bvar_inv indices (loadValue_enum_cell cell)
    injection equal with equal
    subst equal
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne]
    omega
  | bvarFree _ _ _ impossible => omega
  | sort | const | litNat | litStr => intro _ _ _; rfl
  | app cell _ _ left right =>
    intro m j indices
    obtain ⟨func, arg⟩ := SubstAux.idxAll_app_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨left func, right arg⟩
  | lam cell _ _ _ dom body =>
    intro m j indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_lam_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | forallE cell _ _ _ dom body =>
    intro m j indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_forallE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | letE cell _ _ _ type value body =>
    intro m j indices
    obtain ⟨typeIndices, valueIndices, tail⟩ := SubstAux.idxAll_letE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨⟨type typeIndices, value valueIndices⟩,
      by simpa only [Nat.add_assoc] using body tail⟩
  | proj cell address _ inner =>
    intro m j indices
    exact inner (SubstAux.idxAll_proj_inv indices (loadValue_enum_cell cell))

/-- The actual occurrence scan produces the raw absence fact used by its lowering branch. -/
theorem RawExprRep.occurs {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {j : F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_has_bvar_at" [p, .field j] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 0 → R.hasLooseBVar j.val = false) := by
  obtain ⟨E, rep⟩ := represented
  obtain ⟨unchanged, binary, absent⟩ :=
    SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ observed p j rfl bounded
  refine ⟨unchanged, binary, fun zero => ?_⟩
  simpa only [Nat.add_zero] using rep.raw_absent_of_idx
    (absent zero 0 (fun _ => default) k E rep.toTmExact.toTm)

/-- When the substituted variable is absent, capture-avoiding substitution is the same
single-slot lowering used by the actual shortcut. -/
theorem instantiate1Lift_of_absent {R V : KExpr} {j : Nat}
    (absent : R.hasLooseBVar j = false) : R.instantiate1Lift V j = R.lowerBVars 1 j := by
  induction R generalizing j with
  | bvar i =>
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at absent
    simp [Expr.instantiate1Lift, Expr.lowerBVars, Ne.symm absent, Nat.add_one, Nat.succ_le_iff]
  | _ => simp_all [Expr.instantiate1Lift, Expr.lowerBVars, Expr.hasLooseBVar, Bool.or_eq_false_iff]

/-- The actual variable substitution primitive lifts an open argument under the consumed
binders and preserves the complete raw result. The retained bound is an upper bound only. -/
theorem raw_inst1_bvar_exact {κ : _root_.Address → KKey} {h h' : Heap F}
    {n : Nat} {R : KExpr} {i depth : F} {arg r : SourceValue F} {calls : List (Call F)}
    (small : i.val < 9223372036854775808) (inside : i.val < n + depth.val + 1)
    (argument : RawExprRep κ h n R arg) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_inst1_bvar"
      [.field i, arg, .field depth] h r h' calls) :
    RawExprRep κ h' (n + depth.val + 1) ((.bvar i.val : KExpr).instantiate1Lift R depth.val) r := by
  match Obs.«KernelSubst::expr_inst1_bvar».obs observed with
  | .n1 (m2 := after) (ev15 := comparison) (he40 := result) (hm39 := heap) .. =>
    obtain ⟨i', depth', hi, hd, _, _, verdict, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged result heap
    have below := SubstAux.ltf_one verdict.symm
    have rep : RawExprRep κ (h ++ [.construct kexprEnum "BVar" [.field i]])
        (n + depth.val + 1) (.bvar i.val) (.ptr (.enum kexprEnum) h.length) :=
      ⟨_, .bvarLocal (by simp) small inside⟩
    simpa [Expr.instantiate1Lift, show i.val ≠ depth.val by omega, show ¬ depth.val < i.val by omega] using rep
  | .n0_n0 (ev15 := comparison) (op74 := subtracted) (ev86 := lifted) (hc110 := events) .. =>
    obtain ⟨i', depth', hi, hd, _, depthBound, _, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged
    have same : i = depth := by
      have equal := SubstAux.sub_ok subtracted
      injection equal with zero
      exact sub_eq_zero.mp zero.symm
    subst i
    have rawLift := argument.lift
      (bounded_sub (fun _ member => by rw [events]; simp [member]) bounded) (by omega) lifted
    simpa only [Expr.instantiate1Lift, ite_true, ZMod.val_zero] using rawLift.weaken (by omega)
  | .n0_other (ev15 := comparison) (op74 := subtracted) (hne111 := different)
      (he119 := result) (hm118 := heap) (op137 := lowered) .. =>
    obtain ⟨i', depth', hi, hd, _, _, verdict, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged result heap
    have above := SubstAux.ltf_zero verdict.symm
    have distinct : i ≠ depth := fun equal => different (by rw [SubstAux.sub_ok subtracted, equal, sub_self])
    have valuesDistinct : i.val ≠ depth.val := fun equal => distinct (ZMod.val_injective _ equal)
    rw [SubstAux.sub_ok lowered]
    have difference : (i - 1).val = i.val - 1 := by
      rw [SubstAux.val_sub (by rw [SubstAux.val_one]; omega), SubstAux.val_one]
    have rep : RawExprRep κ (h ++ [.construct kexprEnum "BVar" [.field (i - 1)]])
        (n + depth.val + 1) (.bvar (i - 1).val) (.ptr (.enum kexprEnum) h.length) :=
      ⟨_, .bvarLocal (by simp) (by rw [difference]; omega) (by rw [difference]; omega)⟩
    simpa [Expr.instantiate1Lift, valuesDistinct, show depth.val < i.val by omega, difference] using rep

end IxVM.Refinement.Decl
