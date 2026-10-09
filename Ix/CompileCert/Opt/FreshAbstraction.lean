import Ix.CompileCert.Opt.FreshFVars
import Ix.AuxGen.ExprUtils
import Ix.Environment
import Ix.Compile.Canon.NameTable
import Ix.CompileCert.Canon.GeneratedTables

/-!
Support preservation for the actual total abstraction after input-derived
fresh allocation. This leaf is uncompiled; it does not equate the opaque
partial opening helper with a new copy or discharge the general callback
conversion obligation.
-/

namespace Ix.CompileCert.Opt.FreshFVarsProof

open Ix (Name Expr)
open Ix.AuxGen (FreshFVars batchAbstractWith batchAbstractNames)
open Ix.Compile.Canon (keyName NameTable)

/-- The actual abstraction traversal never creates a free variable. -/
theorem abstraction_occurs_source (lookup : Name → Option Nat) (scope : Nat)
    (e : Expr) (depth : Nat) (key : Lean.Name) :
    Occurs key (batchAbstractWith lookup e scope depth) → Occurs key e := by
  by_cases zero : scope = 0
  · subst scope
    simpa only [batchAbstractWith, beq_self_eq_true, ↓reduceIte] using (id : Occurs key e → Occurs key e)
  have nonzero : (scope == 0) = false := by simpa using zero
  induction e generalizing depth with
  | app f a hash ihf iha =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      change (Occurs key (batchAbstractWith lookup f scope depth) ∨
        Occurs key (batchAbstractWith lookup a scope depth)) → _
      exact Or.imp (ihf depth) (iha depth)
  | lam name ty body info hash iht ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      change (Occurs key (batchAbstractWith lookup ty scope depth) ∨
        Occurs key (batchAbstractWith lookup body scope (depth + 1))) → _
      exact Or.imp (iht depth) (ihb (depth + 1))
  | forallE name ty body info hash iht ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      change (Occurs key (batchAbstractWith lookup ty scope depth) ∨
        Occurs key (batchAbstractWith lookup body scope (depth + 1))) → _
      exact Or.imp (iht depth) (ihb (depth + 1))
  | letE name ty value body nd hash iht ihv ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      change ((Occurs key (batchAbstractWith lookup ty scope depth) ∨
        Occurs key (batchAbstractWith lookup value scope depth)) ∨
        Occurs key (batchAbstractWith lookup body scope (depth + 1))) → _
      exact Or.imp (Or.imp (iht depth) (ihv depth)) (ihb (depth + 1))
  | proj name index body hash ih =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact ih depth
  | mdata data body hash ih =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact ih depth
  | fvar name hash =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      cases lookup name with
      | none => exact id
      | some pos =>
          split
          · exact False.elim
          · exact id
  | bvar index hash =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      split <;> exact False.elim
  | _ =>
      intro occurs
      simpa only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte] using occurs

/-- An unselected structural name keeps every occurrence at any scope/depth.
This lemma's lookup premise is discharged from actual allocation below. -/
theorem abstraction_occurs_iff_of_lookup (lookup : Name → Option Nat) (scope : Nat)
    (key : Lean.Name) (leaves : ∀ name, keyName name = key → lookup name = none)
    (e : Expr) (depth : Nat) :
    Occurs key (batchAbstractWith lookup e scope depth) ↔ Occurs key e := by
  by_cases zero : scope = 0
  · subst scope
    simp only [batchAbstractWith, beq_self_eq_true, ↓reduceIte]
  have nonzero : (scope == 0) = false := by simpa using zero
  induction e generalizing depth with
  | app f a hash ihf iha =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact or_congr (ihf depth) (iha depth)
  | lam name ty body info hash iht ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact or_congr (iht depth) (ihb (depth + 1))
  | forallE name ty body info hash iht ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact or_congr (iht depth) (ihb (depth + 1))
  | letE name ty value body nd hash iht ihv ihb =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact or_congr (or_congr (iht depth) (ihv depth)) (ihb (depth + 1))
  | proj name index body hash ih =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact ih depth
  | mdata data body hash ih =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      exact ih depth
  | fvar name hash =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      cases hit : lookup name with
      | none => exact Iff.rfl
      | some pos =>
          have different : keyName name ≠ key := by
            intro equal
            have absent := leaves name equal
            rw [hit] at absent
            contradiction
          split
          · change False ↔ keyName name = key
            exact ⟨False.elim, different⟩
          · exact Iff.rfl
  | bvar index hash =>
      simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]
      split <;> exact Iff.rfl
  | _ => simp only [batchAbstractWith, nonzero, Bool.false_eq_true, ↓reduceIte]

/-- The exact structural table used by a one-binder abstraction. -/
def singletonTable (name : Name) : NameTable Nat := ({} : NameTable Nat).insert name 0

theorem singletonTable_get (name query : Name) :
    (singletonTable name).get? query =
      if keyName name = keyName query then some 0 else none := by
  unfold singletonTable
  rw [NameTable.get?_insert]
  rfl

theorem singleton_abstraction_occurs (name : Name) (key : Lean.Name)
    (different : keyName name ≠ key) (e : Expr) (scope depth : Nat) :
    Occurs key (batchAbstractNames e (singletonTable name) scope depth) ↔ Occurs key e := by
  apply abstraction_occurs_iff_of_lookup
  intro query same
  have unequal : keyName name ≠ keyName query := fun equal => different (equal.trans same)
  simp only [singletonTable_get, unequal, ↓reduceIte]

/-- A complete support-preservation law for actual abstraction after actual
input-derived allocation. No closedness, freshness or cache-validity premise
is imposed on the caller's expression or initial supply. -/
theorem fresh_abstraction_occurs (s : FreshFVars) (e : Expr)
    (pfx : String) (idx scope depth : Nat) (key : Lean.Name) :
    let chosen := ((s.protectExpr e).fresh pfx idx).1.1
    Occurs key (batchAbstractNames e (singletonTable chosen) scope depth) ↔ Occurs key e := by
  dsimp only
  constructor
  · exact abstraction_occurs_source _ scope e depth key
  · intro occurs
    have different : keyName ((s.protectExpr e).fresh pfx idx).1.1 ≠ key := by
      intro equal
      apply fresh_avoids_expr s e pfx idx
      rw [equal]
      exact occurs
    exact (singleton_abstraction_occurs _ key different e scope depth).2 occurs

/-- A particular existing FVar's complete raw node is retained, including its
cached fields, by the actual structural-table abstraction. -/
theorem fresh_abstraction_fvar (s : FreshFVars) (name : Name) (hash : _root_.Address)
    (pfx : String) (idx scope depth : Nat) :
    let e := Expr.fvar name hash
    let chosen := ((s.protectExpr e).fresh pfx idx).1.1
    batchAbstractNames e (singletonTable chosen) scope depth = e := by
  dsimp only
  have different : keyName ((s.protectExpr (.fvar name hash)).fresh pfx idx).1.1 ≠ keyName name := by
    intro equal
    apply fresh_avoids_expr s (.fvar name hash) pfx idx
    exact equal.symm
  unfold batchAbstractNames batchAbstractWith
  split
  · rfl
  · simp only [singletonTable_get, different, ↓reduceIte]

end Ix.CompileCert.Opt.FreshFVarsProof
