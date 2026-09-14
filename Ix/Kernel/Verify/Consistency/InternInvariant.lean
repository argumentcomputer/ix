/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Expr
import Ix.Kernel.Monad

/-!
# Maintained expression support for interning

The pool includes the initial table and the finitely many candidates a
computation can create. Each insertion preserves key coherence and support;
finite key faithfulness then gives exact anonymous syntax for every result.
Universe interning preserves the same expression invariant.
-/

namespace Ix.Kernel.Consistency

structure ExpressionInternInvariant (pool : KExpr .anon → Prop)
    (table : InternTable .anon) : Prop where
  coherent : table.WF
  supported : ∀ term, table.ExprSupport term → pool term

namespace ExpressionInternInvariant

theorem empty (pool : KExpr .anon → Prop) : ExpressionInternInvariant pool .empty := by
  refine ⟨.empty, ?_⟩
  intro term ⟨key, found⟩
  simp [InternTable.empty] at found

theorem mono {pool larger : KExpr .anon → Prop} {table : InternTable .anon}
    (valid : ExpressionInternInvariant pool table) (included : ∀ term, pool term → larger term) :
    ExpressionInternInvariant larger table :=
  ⟨valid.coherent, fun term found => included term (valid.supported term found)⟩

theorem internExpr {pool : KExpr .anon → Prop} {table : InternTable .anon}
    {candidate : KExpr .anon} (valid : ExpressionInternInvariant pool table)
    (allowed : pool candidate) : ExpressionInternInvariant pool (table.internExpr candidate).2 := by
  refine ⟨valid.coherent.internExpr candidate, ?_⟩
  intro term found
  rcases InternTable.ExprSupport.of_internExpr found with old | rfl
  · exact valid.supported term old
  · exact allowed

theorem internUniv {pool : KExpr .anon → Prop} {table : InternTable .anon}
    (valid : ExpressionInternInvariant pool table) (level : KUniv .anon) :
    ExpressionInternInvariant pool (table.internUniv level).2 := by
  refine ⟨valid.coherent.internUniv level, ?_⟩
  intro term ⟨key, found⟩
  exact valid.supported term ⟨key, by simpa using found⟩

theorem result_eq {pool : KExpr .anon → Prop} {table : InternTable .anon}
    {candidate : KExpr .anon} (valid : ExpressionInternInvariant pool table)
    (faithful : KExpr.KeyCollisionFree pool) (allowed : pool candidate) :
    (table.internExpr candidate).1 = candidate := by
  have result := table.internExpr_eraseMeta valid.coherent (fun {_} left {_} right same =>
    faithful (left.elim (valid.supported _) (fun equal => equal.symm ▸ allowed))
      (right.elim (valid.supported _) (fun equal => equal.symm ▸ allowed)) same)
  simpa only [KExpr.eraseMeta_anon] using result

end ExpressionInternInvariant

def internExprState (before : TcState .anon) (candidate : KExpr .anon) : TcState .anon :=
  {before with env := {before.env with intern := (before.env.intern.internExpr candidate).2}}

theorem intern_eq {pool : KExpr .anon → Prop} {before : TcState .anon}
    {candidate : KExpr .anon} (valid : ExpressionInternInvariant pool before.env.intern)
    (faithful : KExpr.KeyCollisionFree pool) (allowed : pool candidate) :
    TcM.intern candidate before = .ok candidate (internExprState before candidate) := by
  change EStateM.Result.ok (before.env.intern.internExpr candidate).1
    (internExprState before candidate) = _
  rw [valid.result_eq faithful allowed]

def internExprList (table : InternTable .anon) (candidates : List (KExpr .anon)) :
    InternTable .anon :=
  candidates.foldl (fun current candidate => (current.internExpr candidate).2) table

theorem ExpressionInternInvariant.internExprList {pool : KExpr .anon → Prop}
    {table : InternTable .anon} (valid : ExpressionInternInvariant pool table)
    (candidates : List (KExpr .anon)) (allowed : ∀ term ∈ candidates, pool term) :
    ExpressionInternInvariant pool (internExprList table candidates) := by
  induction candidates generalizing table with
  | nil => exact valid
  | cons term rest ih =>
      exact ih (valid.internExpr (allowed term (by simp)))
        (fun term member => allowed term (by simp [member]))

end Ix.Kernel.Consistency
