import IxVMRefinement.Core.LoadedExact
import IxVMRefinement.Core.Det

/-! # Uniqueness of exact retained raw heap syntax

Raw exact readings keep let cells and binder metadata. At a fixed keying, ghost context
and variable bounds, one physical pointer has one such raw reading.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels

theorem RawTmExact.raw_det {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {R₁ R₂ E₁ E₂ : KExpr} {p : SourceValue F} (r₁ : RawTmExact κ d Γ h k R₁ E₁ p) (r₂ : RawTmExact κ d Γ h k R₂ E₂ p) :
    R₁ = R₂ := by
  induction r₁ generalizing R₂ E₂ with
  | bvarLocal cell _ hi =>
    cases r₂ with
    | bvarLocal cell' _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; exact rfl
    | bvarFree cell' _ hk _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | sort cell' _ | const cell' _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | bvarFree cell _ hk hd =>
    cases r₂ with
    | bvarLocal cell' _ hi =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; omega
    | bvarFree cell' _ _ _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; exact rfl
    | sort cell' _ | const cell' _ _ | app cell' _ _ | lam cell' _ _ _ | forallE cell' _ _ _
    | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | sort cell rl =>
    cases r₂ with
    | sort cell' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := rl.det rl'; subst this; exact rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | const cell ra rls =>
    cases r₂ with
    | const cell' ra' rls' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      have := rls.det rls'; subst this
      exact rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | app cell _ _ ihf iha =>
    cases r₂ with
    | app cell' rf' ra' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      cases ihf rf'; cases iha ra'; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | lam cell _ _ rl iht ihb =>
    cases r₂ with
    | lam cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      cases iht rt'; cases ihb rb'; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | forallE cell _ _ rl iht ihb =>
    cases r₂ with
    | forallE cell' rt' rb' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := rl.det rl'; subst this
      cases iht rt'; cases ihb rb'; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | letE cell _ _ _ iht ihv ihb =>
    cases r₂ with
    | letE cell' rt' rv' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      cases iht rt'; cases ihv rv'; cases ihb rb'; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litNat cell rl _ =>
    cases r₂ with
    | litNat cell' rl' _ =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := limbsVal_det rl rl'; subst this; exact rfl
    | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litStr cell rb hs =>
    cases r₂ with
    | litStr cell' rb' hs' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := bytes_det rb rb'; subst this
      rw [StrBytes] at hs hs'; rw [hs] at hs'; injection hs' with hs'; subst hs'; exact rfl
    | litNat cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | proj cell ra _ ihe =>
    cases r₂ with
    | proj cell' ra' re' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      cases ihe re'; rfl
    | bvarLocal cell' _ _ | bvarFree cell' _ _ _ | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ _ | forallE cell' _ _ _ | letE cell' _ _ _ | litNat cell' _ _ | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this

/-- Interpret retained raw lets. Free-variable annotations are already semantic annotations
and remain unchanged; all other recursive term positions follow the raw heap constructors. -/
def rawMeaning : KExpr → KExpr
  | .bvar i => .bvar i
  | .fvar i type => .fvar i type
  | .sort u => .sort u
  | .const key levels => .const key levels
  | .app func arg => .app (rawMeaning func) (rawMeaning arg)
  | .lam dom body metadata => .lam (rawMeaning dom) (rawMeaning body) metadata
  | .forallE dom body metadata => .forallE (rawMeaning dom) (rawMeaning body) metadata
  | .letE _ value body _ => instShift (rawMeaning value) 0 (rawMeaning body)
  | .lit value => .lit value
  | .proj key index inner => .proj key index (rawMeaning inner)

/-- The semantic expression is determined by the retained raw expression alone. -/
theorem RawTmExact.meaning {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (represented : RawTmExact κ d Γ h k R E p) : E = rawMeaning R := by
  induction represented with
  | bvarLocal | bvarFree | sort | const | litNat | litStr => rfl
  | app _ _ _ func arg => exact congrArg₂ Ix.Kernel.Expr.app func arg
  | lam _ _ _ _ dom body => simp only [rawMeaning, dom, body]
  | forallE _ _ _ _ dom body => simp only [rawMeaning, dom, body]
  | letE _ _ _ _ _ value body => simp only [rawMeaning, value, body]
  | proj _ _ _ inner => simp only [rawMeaning, inner]

/-- A common exact raw reading gives identical semantic terms even across distinct heaps,
keyings, ghost contexts and local bounds. The raw expression itself carries their common data. -/
theorem RawTmExact.semantic_det {κ κ' : _root_.Address → KKey} {d d' k k' : Nat}
    {Γ Γ' : Nat → KExpr} {h h' : Heap F} {R E E' : KExpr} {p p' : SourceValue F}
    (first : RawTmExact κ d Γ h k R E p) (second : RawTmExact κ' d' Γ' h' k' R E' p') :
    E = E' := first.meaning.trans second.meaning.symm

end IxVM.Refinement.Decl
