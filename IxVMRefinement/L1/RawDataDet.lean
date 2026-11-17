import IxVMRefinement.L1.RawData

/-! # Uniqueness of scope-free reader data at a physical heap pointer -/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

/-- Conversion's wider universe parameter bound is still below the field modulus. -/
theorem RawKLevel.det {h : Heap F} {u v : KLevel} {p : SourceValue F}
    (first : RawKLevel h u p) (second : RawKLevel h v p) : u = v := by
  induction first generalizing v with
  | zero cell =>
    cases second with
    | zero _ => rfl
    | succ other _ | max other _ _ | imax other _ _ | param _ other =>
      have := cell_eq cell other; simp at this
  | succ cell _ ih =>
    cases second with
    | succ other inner =>
      have equal := cell_eq cell other
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at equal
      subst equal
      exact congrArg Ix.Kernel.Level.succ (ih inner)
    | zero other | max other _ _ | imax other _ _ | param _ other =>
      have := cell_eq cell other; simp at this
  | max cell _ _ left right =>
    cases second with
    | max other first second =>
      have equal := cell_eq cell other
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact congrArg₂ Ix.Kernel.Level.max (left first) (right second)
    | zero other | succ other _ | imax other _ _ | param _ other =>
      have := cell_eq cell other; simp at this
  | imax cell _ _ left right =>
    cases second with
    | imax other first second =>
      have equal := cell_eq cell other
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at equal
      obtain ⟨rfl, rfl⟩ := equal
      exact congrArg₂ Ix.Kernel.Level.imax (left first) (right second)
    | zero other | succ other _ | max other _ _ | param _ other =>
      have := cell_eq cell other; simp at this
  | param small cell =>
    cases second with
    | param small' other =>
      have equal := cell_eq cell other
      simp only [Value.construct.injEq, List.cons.injEq, Value.field.injEq, and_true, true_and] at equal
      have indices := congrArg ZMod.val equal
      rw [ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega), ZMod.val_natCast_of_lt (by change _ < 18446744069414584321; omega)] at indices
      cases indices
      rfl
    | zero other | succ other _ | max other _ _ | imax other _ _ =>
      have := cell_eq cell other; simp at this

theorem RawKLevelList.det {h : Heap F} {us vs : List KLevel} {p : SourceValue F}
    (first : RawKLevelList h us p) (second : RawKLevelList h vs p) : us = vs :=
  IxVMRep.repList_det (fun a b => a.det b) first second

theorem RawDataExpr.det {κ : _root_.Address → KKey} {h : Heap F}
    {R₁ R₂ : KExpr} {p : SourceValue F}
    (r₁ : RawDataExpr κ h R₁ p) (r₂ : RawDataExpr κ h R₂ p) : R₁ = R₂ := by
  induction r₁ generalizing R₂ with
  | bvar cell =>
    cases r₂ with
    | bvar cell' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; subst this; rfl
    | sort cell' _ | const cell' _ _ | app cell' _ _ | lam cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | sort cell rl =>
    cases r₂ with
    | sort cell' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := rl.det rl'; subst this; exact rfl
    | bvar cell' | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _
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
    | bvar cell' | sort cell' _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | app cell _ _ ihf iha =>
    cases r₂ with
    | app cell' rf' ra' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl⟩ := this
      cases ihf rf'; cases iha ra'; rfl
    | bvar cell' | sort cell' _ | const cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _
    | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | lam cell _ _ iht ihb =>
    cases r₂ with
    | lam cell' rt' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      cases iht rt'; cases ihb rb'; rfl
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | forallE cell _ _ iht ihb =>
    cases r₂ with
    | forallE cell' rt' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      cases iht rt'; cases ihb rb'; rfl
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | letE cell' _ _ _ | litNat cell' _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | letE cell _ _ _ iht ihv ihb =>
    cases r₂ with
    | letE cell' rt' rv' rb' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      cases iht rt'; cases ihv rv'; cases ihb rb'; rfl
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | litNat cell' _ | litStr cell' _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litNat cell rl =>
    cases r₂ with
    | litNat cell' rl' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := limbsVal_det rl rl'; subst this; exact rfl
    | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | litStr cell rb hs =>
    cases r₂ with
    | litStr cell' rb' hs' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq, and_true,
        true_and] at this; subst this
      have := bytes_det rb rb'; subst this
      rw [StrBytes] at hs hs'; rw [hs] at hs'; injection hs' with hs'; subst hs'; exact rfl
    | litNat cell' _ =>
      have := cell_eq cell cell'; simp at this
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | proj cell' _ _ =>
      have := cell_eq cell cell'; simp at this
  | proj cell ra _ ihe =>
    cases r₂ with
    | proj cell' ra' re' =>
      have := cell_eq cell cell'; simp only [Value.construct.injEq, List.cons.injEq,
        Value.field.injEq, and_true, true_and] at this; obtain ⟨rfl, rfl, rfl⟩ := this
      have := addr_det ra ra'; subst this
      cases ihe re'; rfl
    | bvar cell' | sort cell' _ | const cell' _ _ | app cell' _ _
    | lam cell' _ _ | forallE cell' _ _ | letE cell' _ _ _ | litNat cell' _ | litStr cell' _ _ =>
      have := cell_eq cell cell'; simp at this

end IxVM.Refinement.L1
