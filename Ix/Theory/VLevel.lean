/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Std.Basic

/-!
# Semantic universe levels

`VLevel` gives the implementation-independent meaning of universe levels used
by Theory. Its equivalence relation is extensional equality under every
valuation, so it deliberately forgets representation identity and sharing.
-/

namespace Ix.Theory

inductive VLevel where
  | zero  : VLevel
  | succ  : VLevel → VLevel
  | max   : VLevel → VLevel → VLevel
  | imax  : VLevel → VLevel → VLevel
  | param : Nat → VLevel
deriving DecidableEq, Hashable

namespace VLevel

/-- The natural-number semantics of universe `imax`. -/
def natIMax (a b : Nat) : Nat := if b = 0 then 0 else Nat.max a b

instance : Inhabited VLevel := ⟨.zero⟩

variable (n : Nat) in
def WF : VLevel → Prop
  | .zero => True
  | .succ l => l.WF
  | .max l₁ l₂ => l₁.WF ∧ l₂.WF
  | .imax l₁ l₂ => l₁.WF ∧ l₂.WF
  | .param i => i < n

instance decidable_WF : ∀ {l}, Decidable (WF n l)
  | .zero => instDecidableTrue
  | .succ l => @decidable_WF _ l
  | .max .. | .imax .. => @instDecidableAnd _ _ decidable_WF decidable_WF
  | .param _ => Nat.decLt ..

variable (ls : List Nat) in
def eval : VLevel → Nat
  | .zero => 0
  | .succ l => l.eval + 1
  | .max l₁ l₂ => l₁.eval.max l₂.eval
  | .imax l₁ l₂ => natIMax l₁.eval l₂.eval
  | .param i => ls.getD i 0

protected def LE (a b : VLevel) : Prop := ∀ ls, a.eval ls ≤ b.eval ls

instance : LE VLevel := ⟨VLevel.LE⟩

theorem le_refl (a : VLevel) : a ≤ a := fun _ => Nat.le_refl _

protected def Equiv (a b : VLevel) : Prop := a.eval = b.eval

instance : HasEquiv VLevel := ⟨VLevel.Equiv⟩

theorem equiv_def {a b : VLevel} : a ≈ b ↔ ∀ ls, a.eval ls = b.eval ls := funext_iff

theorem le_antisymm_iff {a b : VLevel} : a ≈ b ↔ a ≤ b ∧ b ≤ a :=
  equiv_def.trans <| (forall_congr' fun _ => Nat.le_antisymm_iff).trans forall_and

theorem succ_congr {a b : VLevel} (h : a ≈ b) : succ a ≈ succ b := by
  simpa [equiv_def, eval] using h

theorem imax_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : imax a₁ a₂ ≈ imax b₁ b₂ := by
  simp_all [equiv_def, eval]

theorem imax_self : imax a a ≈ a := by
  simp [equiv_def, eval, natIMax, eq_comm (b := 0)]

variable (ls : List VLevel) in
def inst : VLevel → VLevel
  | .zero => .zero
  | .succ l => .succ l.inst
  | .max l₁ l₂ => .max l₁.inst l₂.inst
  | .imax l₁ l₂ => .imax l₁.inst l₂.inst
  | .param i => ls.getD i .zero

theorem inst_inst {l : VLevel} : (l.inst ls).inst ls' = l.inst (ls.map (inst ls')) := by
  induction l <;> simp [inst, *, List.getD_eq_getElem?_getD, List.getElem?_map]
  case param n => cases ls[n]? <;> simp [inst]

def params (n : Nat) : List VLevel := (List.range n).map .param

@[simp] theorem params_length {n : Nat} : (params n).length = n := by simp [params]

theorem params_wf {n : Nat} : ∀ ⦃l⦄, l ∈ params n → l.WF n := by simp [params, WF]

theorem inst_id {l : VLevel} (h : l.WF u) : l.inst (params u) = l := by
  induction l <;> simp_all [params, inst, WF, List.getD_eq_getElem?_getD]

theorem inst_map_id (h : ls.length = n) : (params n).map (inst ls) = ls := by
  subst n; simp [params]; apply List.ext_get (by simp)
  intro i _ _; simp [inst]; rw [List.getElem?_eq_getElem]; rfl

theorem eval_inst {l : VLevel} : (l.inst ls).eval ns = l.eval (ls.map (eval ns)) := by
  induction l <;> simp [eval, inst, *, List.getD_eq_getElem?_getD]
  case param n => cases ls[n]? <;> simp [eval]

theorem WF.inst {l : VLevel} (H : ∀ l ∈ ls, l.WF n) : (l.inst ls).WF n := by
  induction l with
  | zero => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | param i =>
    simp [VLevel.inst, List.getD_eq_getElem?_getD]
    cases e : ls[i]? with
    | none => trivial
    | some => exact H _ (List.mem_of_getElem? e)

theorem inst_congr {l : VLevel} (h1 : l ≈ l') (h2 : List.Forall₂ (·≈·) ls ls') :
    l.inst ls ≈ l'.inst ls' := by
  simp [equiv_def, eval_inst, ← equiv_def.1 h1]
  intro ns; congr 1
  induction h2 with
  | nil => rfl
  | cons h2 => simp [*, equiv_def.1 h2]

theorem inst_congr_l {l : VLevel} (h1 : l ≈ l') : l.inst ls ≈ l'.inst ls :=
  inst_congr h1 <| Ix.Theory.List.Forall₂.rfl fun _ _ => rfl
