import IxVMRefinement.Assembly.GuardRawRep
import IxVMRefinement.Guard.RawLevels
import IxVMRefinement.Decl.NativeFront

/-! # Metadata-preserving exact raw substitution

The structural guard substitutes universe syntax without normalization. Both the retained raw
expression and its semantic reading follow the same literal positional substitution; binder
metadata follows the exact zeroness substitution identity. This is a data specification only.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr Level)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000

private theorem raw_ilp_nil {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) : R.instantiateLevelParams [] [] = R := by
  induction rep with
  | bvarLocal => rfl
  | bvarFree _ _ _ hd => omega
  | sort cell level => simp only [Expr.instantiateLevelParams, SubstAux.level_subst_nil]
  | const cell address levels =>
    simp only [Expr.instantiateLevelParams]
    congr 1
    exact List.map_id' (fun u => SubstAux.level_subst_nil u)
  | app cell _ _ ihf iha => simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam cell _ _ level iht ihb | forallE cell _ _ level iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, SubstAux.bmeta_subst_nil]
  | letE cell _ _ _ iht ihv ihb => simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | litNat | litStr => rfl
  | proj cell address _ ih => simp only [Expr.instantiateLevelParams, ih]

private theorem raw_bmeta_subst (params : List Level) (u : Level) :
    ({ bmeta u with pw := Level.substPW (List.range params.length) params (bmeta u).pw } :
      Ix.Kernel.BinderMeta) = bmeta (Level.subst (List.range params.length) params u) := by
  unfold bmeta
  rw [Level.zeronessOf_subst]

private theorem raw_sort_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p level : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Srt" [level])) :
    ∃ u, R = .sort u ∧ E = .sort u ∧ RepKLevel h u level := by
  cases rep with
  | sort cell represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with same
    subst same
    exact ⟨_, rfl, rfl, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_lam_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p dom body level : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Lam" [dom, body, level])) :
    ∃ RD RB D B u, R = .lam RD RB (bmeta u) ∧ E = .lam D B (bmeta u) ∧
      RawTmExact κ d Γ h k RD D dom ∧ RawTmExact κ d Γ h (k + 1) RB B body ∧
      RepKLevel h u level := by
  cases rep with
  | lam cell domain bodyRep represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, _, rfl, rfl, domain, bodyRep, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_let_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ty val body : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Let" [ty, val, body])) :
    ∃ RT RV RB T V B, R = .letE RT RV RB default ∧ E = instShift V 0 B ∧
      RawTmExact κ d Γ h k RT T ty ∧ RawTmExact κ d Γ h k RV V val ∧
      RawTmExact κ d Γ h (k + 1) RB B body := by
  cases rep with
  | letE cell typeRep valueRep bodyRep =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, _, _, rfl, rfl, typeRep, valueRep, bodyRep⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_proj_view {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ap i inner : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, i, inner])) :
    ∃ a (index : F) RI I, R = .proj (κ (ixAddr a)) index.val RI ∧
      E = .proj (κ (ixAddr a)) index.val I ∧ i = .field index ∧
      Bytes.RepAddressRef addrTy h a ap ∧ RawTmExact κ d Γ h k RI I inner := by
  cases rep with
  | proj cell address represented =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with one fields; injection fields with two fields; injection fields with three
    subst one two three
    exact ⟨_, _, _, _, rfl, rfl, rfl, address, represented⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem raw_leaf_ilp {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F} {fields : List (SourceValue F)}
    (rep : RawTmExact κ 0 Γ h k R E p) (params : List Level)
    (leaf : loadValue h p = .ok (.construct kexprEnum "BVar" fields) ∨
      loadValue h p = .ok (.construct kexprEnum "Lit" fields)) :
    R.instantiateLevelParams (List.range params.length) params = R ∧
      E.instantiateLevelParams (List.range params.length) params = E := by
  cases rep with
  | bvarLocal | litNat | litStr => exact ⟨rfl, rfl⟩
  | bvarFree _ _ _ hd => omega
  | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | proj cell _ _ =>
    rcases leaf with loaded | loaded <;> exact (load_cell_ne cell loaded (by decide)).elim

end IxVM.Refinement.Decl
