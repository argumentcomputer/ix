/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Lctx
import Std.Data.HashMap.Lemmas

/-!
# Concrete local-context coherence

Every successful index lookup points at a declaration carrying the queried
identifier. These structural facts are shared by the direct set-model proof
and the named translation, without importing either semantic development.
They concern the actual production context, including truncation.
-/

namespace Ix.Kernel

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

/-! The invariant is extensional in the index map. Truncation need not
reconstruct a previous hash-map representation to preserve it. -/

structure LocalContext.WF {m : Mode} (lctx : LocalContext m) : Prop where
  sound : ∀ {fv : FVarId} {i : Nat}, lctx.index[fv]? = some i →
    ∃ d, lctx.decls[i]? = some (fv, d)

protected theorem LocalContext.WF.empty :
    LocalContext.WF ({} : LocalContext m) where
  sound := by simp

protected theorem LocalContext.WF.push {m : Mode}
    {lctx : LocalContext m} {fv : FVarId} {d : LocalDecl m}
    (h : lctx.WF) (hfree : lctx.index[fv]? = none) :
    (lctx.push fv d).WF where
  sound := by
    have _hfree := hfree
    intro queried i hi
    simp only [LocalContext.push] at hi ⊢
    rw [Std.HashMap.getElem?_insert] at hi
    split at hi
    · next heq =>
      cases hi
      have hid : fv = queried := eq_of_beq heq
      subst queried
      refine ⟨d, ?_⟩
      rw [Array.getElem?_push]
      simp
    · obtain ⟨decl, hd⟩ := h.sound hi
      refine ⟨decl, ?_⟩
      rw [Array.getElem?_push, if_neg]
      · exact hd
      · intro hieq
        subst i
        obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hd
        omega

theorem LocalContext.WF.mem_of_index {m : Mode}
    {lctx : LocalContext m} (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) :
    ∃ p ∈ lctx.decls.toList, p.1 = fv := by
  obtain ⟨d, hd⟩ := h.sound hi
  refine ⟨(fv, d), ?_, rfl⟩
  apply List.mem_of_getElem?
  rw [Array.getElem?_toList]
  exact hd

theorem LocalContext.WF.index_lt {m : Mode} {lctx : LocalContext m}
    (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) : i < lctx.decls.size := by
  obtain ⟨d, hd⟩ := h.sound hi
  exact (Array.getElem?_eq_some_iff.mp hd).choose

/-- The index is positionally coherent: a hit points at an entry
    carrying exactly the queried id. -/
theorem LocalContext.WF.getElem?_of_index {m : Mode}
    {lctx : LocalContext m} (h : lctx.WF) {fv : FVarId} {i : Nat}
    (hi : lctx.index[fv]? = some i) :
    ∃ d, lctx.decls[i]? = some (fv, d) :=
  h.sound hi

/-- Truncating a one-entry extension produces the exact declaration-array
prefix and an index whose remaining hits are still sound.  The index is not
claimed equal to any earlier hash-map value. -/
theorem LocalContext.truncate_pred_eval {m : Mode}
    {lctx : LocalContext m} {len : Nat}
    (hsize : lctx.decls.size = len + 1) :
    lctx.truncate len =
      { decls := lctx.decls.pop
        index := lctx.index.erase lctx.decls.back!.1 } := by
  unfold LocalContext.truncate
  simp [hsize, LocalContext.truncate.go]

theorem LocalContext.WF.truncate_pred {m : Mode}
    {lctx : LocalContext m} {len : Nat}
    (h : lctx.WF) (hsize : lctx.decls.size = len + 1) :
    (lctx.truncate len).WF := by
  rw [LocalContext.truncate_pred_eval hsize]
  constructor
  intro fv i hi
  change (lctx.index.erase lctx.decls.back!.1)[fv]? = some i at hi
  rw [Std.HashMap.getElem?_erase] at hi
  split at hi
  · contradiction
  · next hne =>
    obtain ⟨d, hd⟩ := h.sound hi
    by_cases hlt : i < lctx.decls.pop.size
    · refine ⟨d, ?_⟩
      rw [Array.getElem?_pop, if_pos (by simpa using hlt)]
      exact hd
    · have hiOld : i < lctx.decls.size :=
        (Array.getElem?_eq_some_iff.mp hd).choose
      have hiLast : i = lctx.decls.size - 1 := by
        simp only [Array.size_pop] at hlt
        omega
      subst i
      obtain ⟨hiBound, hget⟩ := Array.getElem?_eq_some_iff.mp hd
      have hback : lctx.decls.back! = (fv, d) := by
        simp only [Array.back!]
        rw [getElem!_pos lctx.decls (lctx.decls.size - 1) hiBound]
        exact hget
      exfalso
      rw [hback] at hne
      simp at hne

/-- Unpack the concrete `find?` read into a positional hit. -/
theorem LocalContext.WF.find?_pos {m : Mode} {lctx : LocalContext m}
    (h : lctx.WF) {fv : FVarId} {d : LocalDecl m}
    (hf : lctx.find? fv = some d) :
    ∃ i, i < lctx.decls.size ∧ lctx.decls[i]? = some (fv, d) := by
  match hi : lctx.index[fv]? with
  | none => simp [LocalContext.find?, hi] at hf
  | some i =>
    obtain ⟨d', hd⟩ := h.getElem?_of_index hi
    have hlt := h.index_lt hi
    refine ⟨i, hlt, ?_⟩
    simp [LocalContext.find?, hi, hd] at hf
    rw [hd, hf]

end Ix.Kernel
