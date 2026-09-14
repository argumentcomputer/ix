/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.LocalContext

/-!
# Observable local contexts and fresh extensions

Scope restoration preserves the ordered declarations and every index lookup.
Hash-map representation need not be identical after insertion and erasure.
Fresh extensions compose through nested pushes and scope truncation.
-/

namespace Ix.Kernel.LocalContext

private local instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    congr 1
    exact eq_of_beq equal
  rfl {a} := by
    cases a with
    | mk x => show (x == x) = true; exact beq_self_eq_true x

/-- The ordered declarations and every observable index lookup agree.
Physical hash-map representation is deliberately not part of the relation. -/
structure Equiv (left right : LocalContext m) : Prop where
  decls : left.decls = right.decls
  index : ∀ id : FVarId, left.index[id]? = right.index[id]?

namespace Equiv

theorem refl (context : LocalContext m) : Equiv context context := ⟨rfl, fun _ => rfl⟩

theorem symm {left right : LocalContext m} (same : Equiv left right) : Equiv right left :=
  ⟨same.decls.symm, fun id => (same.index id).symm⟩

theorem trans {first second third : LocalContext m}
    (left : Equiv first second) (right : Equiv second third) : Equiv first third :=
  ⟨left.decls.trans right.decls, fun id => (left.index id).trans (right.index id)⟩

theorem size {left right : LocalContext m} (same : Equiv left right) : left.size = right.size :=
  congrArg Array.size same.decls

theorem find? {left right : LocalContext m} (same : Equiv left right) (id : FVarId) :
    left.find? id = right.find? id := by
  simp only [LocalContext.find?, same.index, same.decls]

theorem wf {left right : LocalContext m} (same : Equiv left right) (valid : left.WF) : right.WF := by
  constructor
  intro id position found
  rw [← same.index] at found
  obtain ⟨decl, hit⟩ := valid.sound found
  exact ⟨decl, same.decls ▸ hit⟩

theorem push {left right : LocalContext m} (same : Equiv left right)
    (id : FVarId) (decl : LocalDecl m) : Equiv (left.push id decl) (right.push id decl) := by
  constructor
  · simp only [LocalContext.push, same.decls]
  · intro queried
    simp only [LocalContext.push, Std.HashMap.getElem?_insert, same.decls, same.index]

private theorem truncate_go {left right : LocalContext m} (same : Equiv left right)
    (len fuel : Nat) : Equiv
      (LocalContext.truncate.go len left.decls left.index fuel)
      (LocalContext.truncate.go len right.decls right.index fuel) := by
  induction fuel generalizing left right with
  | zero => exact same
  | succ fuel ih =>
      simp only [LocalContext.truncate.go, same.decls]
      split
      · apply ih (left := ⟨right.decls.pop, left.index.erase right.decls.back!.1⟩)
          (right := ⟨right.decls.pop, right.index.erase right.decls.back!.1⟩)
        exact ⟨rfl, fun id => by simp only [Std.HashMap.getElem?_erase, same.index]⟩
      · exact ⟨rfl, same.index⟩

theorem truncate {left right : LocalContext m} (same : Equiv left right) (len : Nat) :
    Equiv (left.truncate len) (right.truncate len) := by
  unfold LocalContext.truncate
  simpa only [same.decls] using truncate_go same len (left.decls.size - len)

end Equiv

/-- Popping a fresh push restores the old declarations and all old lookups. -/
theorem truncate_push {context : LocalContext m} {id : FVarId}
    (fresh : context.index[id]? = none) (decl : LocalDecl m) :
    Equiv ((context.push id decl).truncate context.size) context := by
  rw [LocalContext.truncate_pred_eval (by simp [LocalContext.push, LocalContext.size])]
  constructor
  · simp [LocalContext.push]
  · intro queried
    simp only [LocalContext.push, Array.back!_push, Std.HashMap.getElem?_erase,
      Std.HashMap.getElem?_insert]
    split
    next equal =>
      have equal : id = queried := eq_of_beq equal
      subst queried
      exact fresh.symm
    next different => rfl

/-- A fresh final push can also be removed while restoring an older scope. -/
theorem truncate_push_le {context : LocalContext m} {id : FVarId} {len : Nat}
    (fresh : context.index[id]? = none) (decl : LocalDecl m) (bound : len ≤ context.size) :
    Equiv ((context.push id decl).truncate len) (context.truncate len) := by
  unfold LocalContext.truncate
  simp only [LocalContext.push, Array.size_push]
  have fuel : context.decls.size + 1 - len = (context.decls.size - len) + 1 := by
    change len ≤ context.decls.size at bound
    omega
  rw [fuel, LocalContext.truncate.go, if_pos (by
    simp only [Array.size_push]
    change len < context.size + 1
    omega)]
  simp only [Array.back!_push, Array.pop_push]
  apply Equiv.truncate_go (left := ⟨context.decls, (context.index.insert id context.decls.size).erase id⟩)
    (right := context)
  refine ⟨rfl, ?_⟩
  intro queried
  simp only [Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
  split
  next equal =>
    have equal : id = queried := eq_of_beq equal
    subst queried
    exact fresh.symm
  next different => rfl

/-- A context is extended only by fresh pushes and by observable context
equivalence. Nested scope cleanup can therefore be composed without exposing
hash-map implementation details. -/
inductive Extension : LocalContext m → LocalContext m → Prop
  | refl (context : LocalContext m) : Extension context context
  | push {before current : LocalContext m} {id : FVarId} (decl : LocalDecl m)
      (previous : Extension before current) (fresh : current.index[id]? = none) :
      Extension before (current.push id decl)
  | equiv {before current after : LocalContext m}
      (previous : Extension before current) (same : Equiv current after) : Extension before after

namespace Extension

theorem trans {before middle after : LocalContext m}
    (first : Extension before middle) (second : Extension middle after) : Extension before after := by
  induction second with
  | refl => exact first
  | push decl _ fresh ih => exact .push decl ih fresh
  | equiv _ same ih => exact .equiv ih same

theorem size_le {before after : LocalContext m} (extended : Extension before after) :
    before.size ≤ after.size := by
  induction extended with
  | refl => exact Nat.le_refl _
  | push decl previous fresh ih =>
      simp only [LocalContext.size, LocalContext.push, Array.size_push] at *
      omega
  | equiv previous same ih => rw [← same.size]; exact ih

theorem restore {before after : LocalContext m} (extended : Extension before after) :
    Equiv (after.truncate before.size) before := by
  induction extended with
  | refl =>
      simpa [LocalContext.truncate, LocalContext.size, LocalContext.truncate.go] using
        Equiv.refl before
  | push decl previous fresh ih => exact (truncate_push_le fresh decl previous.size_le).trans ih
  | equiv previous same ih => exact (same.symm.truncate _).trans ih

end Extension

end Ix.Kernel.LocalContext
