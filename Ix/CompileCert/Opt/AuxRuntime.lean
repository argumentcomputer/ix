import Ix.CompileCert.Opt.AuxCore
import Ix.AuxGen.Recursor

/-!
# Exact runtime refinement of auxiliary abstraction and implicit marking

The original arbitrary-HashMap entry point retains its domain and agrees,
including cached output fields, with the total core copy. The same total
lookup-function traversal also supplies the structural-table erasure law.
Implicit marking preserves erased terms without assuming anything about its
Boolean marking helpers. No production lookup table is migrated by these
theorems; freshness and generated-type scope remain separate obligations.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Expr)
open Ix.CompileCert.Conv

/-- Exact raw-result equality, including cached fields, for every old map. -/
theorem batchAbstract_eq_copy (e : Expr) (m : Std.HashMap Name Nat)
    (S d : Nat) : Ix.AuxGen.batchAbstract e m S d = batchAbstractP e m S d := by
  unfold Ix.AuxGen.batchAbstract
  induction e generalizing d with
  | app f a hash ihf iha =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, ihf, iha]
  | lam name ty body info hash iht ihb =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, iht, ihb]
  | forallE name ty body info hash iht ihb =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, iht, ihb]
  | letE name ty value body nd hash iht ihv ihb =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, iht, ihv, ihb]
  | proj name index body hash ih =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, ih]
  | mdata data body hash ih =>
    simp only [Ix.AuxGen.batchAbstractWith, batchAbstractP, ih]
  | _ => rfl

/-- The former named executable-copy obligation has no remaining hypothesis. -/
theorem auxGenCopies : AuxGenCopies := by
  constructor
  funext e m S d
  exact batchAbstract_eq_copy e m S d

theorem er_batchAbstractWith (lookup : Name → Option Nat) (S : Nat) :
    ∀ (e : Expr) (d : Nat), er (Ix.AuxGen.batchAbstractWith lookup e S d) = babs lookup S d (er e) := by
  intro e
  by_cases hS : S = 0
  · subst hS
    intro d
    unfold Ix.AuxGen.batchAbstractWith
    simp only [beq_self_eq_true, ↓reduceIte, babs_zero]
  · have hS' : (S == 0) = false := by simpa using hS
    induction e with
    | fvar n _ =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
      cases lookup n with
      | none => rfl
      | some pos =>
        simp only
        split <;> simp [er]
    | bvar i _ =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
      by_cases hi : d ≤ i
      · have : (i ≥ d) := hi
        simp only [ge_iff_le, hi, ↓reduceIte, er_mkBVar]
      · simp only [ge_iff_le, hi, ↓reduceIte, er]
    | app f a _ ihf iha =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkApp, er, babs, ihf, iha]
    | lam n t b bi _ iht ihb =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkLam, er, babs, iht, ihb]
    | forallE n t b bi _ iht ihb =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkForallE, er, babs, iht, ihb]
    | letE n t v b nd _ iht ihv ihb =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkLetE, er, babs, iht, ihv,
        ihb]
    | proj n i e _ ihe =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkProj, er, babs, ihe]
    | mdata kvs e _ ihe =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er_mkMData, er, ihe]
    | mvar =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | sort =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | const =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | lit =>
      intro d
      simp only [Ix.AuxGen.batchAbstractWith, hS', Bool.false_eq_true, ↓reduceIte, er, babs]

/-- Structural-table consumers inherit the same arbitrary-lookup erasure. -/
theorem er_batchAbstractNames (m : Ix.Compile.Canon.NameTable Nat) (S : Nat)
    (e : Expr) (d : Nat) :
    er (Ix.AuxGen.batchAbstractNames e m S d) = babs m.get? S d (er e) :=
  er_batchAbstractWith m.get? S e d

/-- Implicit marking changes only binder annotations, with no premise about
the opaque Boolean marking helper or the original expression's scope. -/
theorem er_inferImplicit (ty : Expr) (numParams : Nat) :
    er (Ix.AuxGen.inferImplicit ty numParams) = er ty := by
  induction ty generalizing numParams with
  | forallE name dom body info hash _ ih =>
    unfold Ix.AuxGen.inferImplicit
    split
    · rfl
    · change Tm.pi (er dom) (er (Ix.AuxGen.inferImplicit body (numParams - 1))) =
        Tm.pi (er dom) (er body)
      rw [ih]
  | _ => unfold Ix.AuxGen.inferImplicit; split <;> rfl

end Ix.CompileCert.Opt

