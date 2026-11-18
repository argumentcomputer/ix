import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.NativeAliasTeleStable
import IxVMRefinement.Assembly.TypingRecLateMajorKey

/-! # Nonzero alias indices from the actual raw former guard

The telescope test reads raw heap cells. Its successful branch therefore gives a telescope in
the original reader syntax as well as in the semantic reading; raw binder traces preserve
lets and prevent a converse through zeta erasure from entering this argument.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem raw_sort_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p level : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Srt" [level])) :
    ∃ sort, R = .sort sort := by
  cases rep with
  | sort cell represented => exact ⟨_, rfl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell loaded (by decide)).elim

/-- Actual raw telescope cells imply a telescope in the raw exact reading. -/
theorem raw_telescope_of_cells {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ n {h : Heap F} {k : Nat} {R E : KExpr} {p level : SourceValue F},
      RawTmExact κ d Γ h k R E p → TeleShape h n p level →
      ∃ binders sort, R.stripPis n = some (binders, .sort sort)
  | 0, h, k, R, E, p, level, rep, shape => by
    obtain ⟨sort, rfl⟩ := raw_sort_of_load rep shape
    exact ⟨[], sort, rfl⟩
  | n + 1, h, k, R, E, p, level, rep, ⟨dom, body, metaPtr, loaded, tail⟩ => by
    obtain ⟨RD, RB, D, B, sort, rfl, rfl, _, represented, _⟩ := rep.forallE_of_load loaded
    obtain ⟨binders, result, stripped⟩ := raw_telescope_of_cells n represented tail
    exact ⟨(RD, bmeta sort) :: binders, result, by simp [Expr.stripPis, stripped]⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open Ix.Kernel (Expr)

/-- Changing only raw binder metadata preserves telescope shape in the reader direction. -/
theorem RawShape.strip_sort_left : ∀ {n : Nat} {E R : KExpr} {binders} {sort},
    RawShape E R → R.stripPis n = some (binders, .sort sort) →
    ∃ original, E.stripPis n = some (original, .sort sort)
  | 0, E, R, binders, level, shape, stripped => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at stripped
    obtain ⟨rfl, rfl⟩ := stripped
    cases shape
    exact ⟨[], rfl⟩
  | n + 1, E, R, binders, level, shape, stripped => by
    cases shape <;> simp only [Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at stripped
    rename_i D D' B B' binderMeta binderMeta' dom body
    obtain ⟨⟨tail, residual⟩, next, equal⟩ := stripped
    obtain ⟨_, rfl⟩ := Prod.mk.inj equal
    obtain ⟨original, reconstructed⟩ := body.strip_sort_left next
    exact ⟨(D, binderMeta) :: original, by simp [Expr.stripPis, reconstructed]⟩

/-- A checked former whose raw reader syntax is not a telescope must have nonzero indices. -/
theorem alias_indices_of_guard {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {params indices : Nat} {read raw semantic : KExpr}
    {pointer count blockArg index level result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (bound : params + indices < 18446744069414584321)
    (shape : RawShape read raw)
    (represented : Decl.RawTmExact κ 0 Γ h 0 raw semantic pointer)
    (notTelescope : ∀ binders sort, read.piBinders ≠ (binders, .sort sort))
    (observed : ObsFn W "KernelCheck::former_decl_ok"
      [pointer, .field (params : F), .field (indices : F), count, blockArg, index, level]
      h result h' calls) : indices ≠ 0 := by
  match Obs.«KernelCheck::former_decl_ok».obs observed with
  | .n1 (v17 := sum) (op38 := added) (ev15 := telescope) .. =>
    rw [Decl.evalBinOp_add_nat params indices added] at telescope
    obtain ⟨level, cells⟩ := Decl.former_is_tele_one_cells (params + indices) bound telescope
    obtain ⟨binders, sort, stripped⟩ := Decl.raw_telescope_of_cells _ represented cells
    obtain ⟨original, readStrip⟩ := shape.strip_sort_left stripped
    exact (notTelescope original sort (stripPis_sort_piBinders _ _ readStrip).1).elim
  | .other (ev78 := zeroTest) (heq93 := resultEq) .. =>
    subst resultEq
    obtain ⟨isZero, _⟩ := Lib.is_zero_spec zeroTest
    intro zero
    subst indices
    simp at isZero

end IxVM.Refinement.Typing
