/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Checked

namespace Ix.Theory.Certified.Natural

open Model Model.SetTheory Model.SetTheory.Tower Model.InductiveCodes Ordinary

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

def zeroConstructor : Constructor β := ⟨[], [], []⟩
def succConstructor : Constructor β := ⟨[], [⟨[], []⟩], []⟩
def shape : Shape β := ⟨0, [], [], .succ .zero, [zeroConstructor, succConstructor]⟩

variable (constants : Assignment β V)

theorem zero_positions :
    shape.positions constants [] (fun _ => empty) (inj 0 (pt : V)) = empty := by
  apply eq_empty
  intro p hp
  obtain ⟨i, field, _, hi, _, _⟩ := Shape.mem_positions
    (shape := shape) (constants := constants) (levels := []) (env := fun _ => empty)
    (show (shape : Shape β).constructors[0]? = some zeroConstructor from rfl)
    (xs := []) rfl hp
  simp [zeroConstructor] at hi

theorem succ_positions :
    shape.positions constants [] (fun _ => empty) (inj 1 (pt : V)) = sing (inj 0 pt) := by
  apply ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, field, ys, hi, hys, rfl⟩ := Shape.mem_positions
      (shape := shape) (constants := constants) (levels := []) (env := fun _ => empty)
      (show (shape : Shape β).constructors[1]? = some succConstructor from rfl)
      (xs := []) rfl hp
    have he : i = 0 := by
      have hb := (List.getElem?_eq_some_iff.mp hi).1
      simp only [succConstructor, List.length_singleton] at hb
      omega
    subst i
    cases Option.some.inj hi
    cases ys with
    | nil => exact mem_sing.mpr rfl
    | cons _ _ => exact hys.elim
  · intro hp
    cases mem_sing.mp hp
    exact Shape.inj_mem_positions (shape := shape) (constants := constants) (levels := []) (env := fun _ => empty)
      (show (shape : Shape β).constructors[1]? = some succConstructor from rfl)
      (show (succConstructor : Constructor β).recursive[0]? = some ⟨[], []⟩ from rfl)
      (xs := []) (ys := []) rfl trivial

theorem zero_value :
    shape.constructorValue constants [] (fun _ => empty) zeroConstructor 0 [] [] = (Numeral.value 0 : V) := by
  have hg : shape.branches constants [] (fun _ => empty) zeroConstructor 0 [] [] = (empty : V) := by
    rw [Shape.branches, mkTower, zero_positions]
    apply eq_empty
    intro p hp
    obtain ⟨x, hx, _⟩ := mem_graph.mp hp
    exact not_mem_empty x hx
  rw [Shape.constructorValue, hg]
  rfl

theorem succ_value (n : V) :
    shape.constructorValue constants [] (fun _ => empty) succConstructor 1 [] [n] = Numeral.succ n := by
  have hg : shape.branches constants [] (fun _ => empty) succConstructor 1 [] [n] =
      graph (fun _ => n) (sing (inj 0 pt)) := by
    rw [Shape.branches, mkTower, succ_positions]
    apply graph_congr
    intro p hp
    cases mem_sing.mp hp
    simp only [Shape.branchBody, tag_inj, succConstructor, List.getElem?_cons_zero,
      List.getD_cons_zero, List.length_nil, projList, Telescope.applyN]
  rw [Shape.constructorValue, hg]
  rfl

variable {constants} {entries : Environment β} {store : Store β} {source : β}

/-- Every literal is a member of the exact carrier built for zero/successor.
This is proved by natural-number induction, not supplied as a certificate. -/
theorem value_mem (h : CheckedShape.{u,v} entries store source shape)
    (hM : Realizes constants entries) (n : Nat) :
    Numeral.value n ∈ˢ shape.familyValue constants [] := by
  induction n with
  | zero =>
    have hm := Shape.constructorValue_mem h hM (Context.valid_nil constants [] (fun _ => empty))
      (show (shape : Shape β).constructors[0]? = some zeroConstructor from rfl)
      (xs := []) (fs := []) (by trivial) (by trivial)
    rw [zero_value] at hm
    exact hm
  | succ n ih =>
    have hm := Shape.constructorValue_mem h hM (Context.valid_nil constants [] (fun _ => empty))
      (show (shape : Shape β).constructors[1]? = some succConstructor from rfl)
      (xs := []) (fs := [Numeral.value n]) (by trivial) (show _ ∧ True from ⟨ih, trivial⟩)
    rw [succ_value] at hm
    exact hm

theorem meaning (h : CheckedShape.{u,v} entries store source shape)
    {reading : Assignment β V} (hr : ConstructorReading entries shape source constants reading)
    (hM : Realizes constants entries) :
    NaturalMeaning reading (.member source 0) (.ctor source 0 0) (.ctor source 0 1) := by
  constructor
  · intro n
    rw [hr.family [] rfl]
    exact value_mem h hM n
  · rw [hr.constructor [] rfl 0 zeroConstructor rfl]
    exact zero_value constants
  · intro n
    rw [hr.constructor [] rfl 1 succConstructor rfl]
    have he := Shape.constructorClosedValue_apply h hM
      (show (shape : Shape β).constructors[1]? = some succConstructor from rfl)
      (levels := []) (ps := []) (xs := []) (fs := [Numeral.value n]) (by trivial) (by trivial)
      (show _ ∧ True from ⟨value_mem h hM n, trivial⟩)
    simpa only [Telescope.applyN, Telescope.extend, List.nil_append, succ_value, Numeral.value] using he

end Ix.Theory.Certified.Natural
