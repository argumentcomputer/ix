/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Natural/Value.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store is removed and `meaning` takes the successor's function
membership (`NaturalMeaning.succApp`) as a hypothesis proved in `Publish`.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Checked

namespace Ix.Kernel.Certified.Natural

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

variable {constants} {entries : Environment β} {source : β}

/-- Every literal is a member of the exact carrier built for zero/successor.
This is proved by natural-number induction, not supplied as a certificate. -/
theorem value_mem (h : CheckedShape.{u,v} entries source shape)
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

/-- Structural induction on the constructed carrier rules out additional
elements. Its zero node has no branches and its successor node has exactly
one branch, whose value is a numeral by the induction hypothesis. -/
theorem value_complete (h : CheckedShape.{u,v} entries source shape)
    (hM : Realizes constants entries) {x : V}
    (member : x ∈ˢ shape.familyValue constants []) : ∃ n, x = Numeral.value n := by
  have valid := Context.valid_nil constants [] (fun _ => empty)
  have formed := Shape.container_wf h hM valid
  have all := IndexedContainer.induction formed (fun _ value => ∃ n, value = Numeral.value n)
  apply all ?_ (pt : V) ?_ x member
  · intro index _ tag tagMember branches branchesMember ih
    obtain ⟨j, ctor, xs, selected, fits, rfl⟩ := Shape.mem_allShapes (mem_sep.mp tagMember).1
    have bound : j < 2 := by
      simpa only [shape, List.length_cons, List.length_nil] using
        (List.getElem?_eq_some_iff.mp selected).1
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · cases Option.some.inj selected
      have emptyArgs : xs = [] := List.eq_nil_of_length_eq_zero (FitsS.length_eq fits)
      subst xs
      change branches ∈ˢ piSet (shape.positions constants [] (fun _ => empty) (inj 0 pt)) _ at branchesMember
      rw [zero_positions] at branchesMember
      have emptyBranches : branches = empty := by
        rw [← eq_graph_app_of_mem_piSet branchesMember]
        apply eq_empty
        intro p hp
        obtain ⟨a, ha, _⟩ := mem_graph.mp hp
        exact not_mem_empty a ha
      exact ⟨0, by change spair (inj 0 pt) branches = _; rw [emptyBranches]; rfl⟩
    · cases Option.some.inj selected
      have emptyArgs : xs = [] := List.eq_nil_of_length_eq_zero (FitsS.length_eq fits)
      subst xs
      change branches ∈ˢ piSet (shape.positions constants [] (fun _ => empty) (inj 1 pt)) _ at branchesMember
      rw [succ_positions] at branchesMember
      have position : inj 0 pt ∈ˢ (shape.container constants [] (fun _ => empty)).positions (inj 1 pt) := by
        change inj 0 pt ∈ˢ shape.positions constants [] (fun _ => empty) (inj 1 pt)
        rw [succ_positions]
        exact mem_sing.mpr rfl
      obtain ⟨n, value⟩ := ih (inj 0 pt) position
      have branchEq : branches = graph (fun _ => Numeral.value n) (sing (inj 0 pt)) := by
        rw [← eq_graph_app_of_mem_piSet branchesMember]
        apply graph_congr
        intro p hp
        cases mem_sing.mp hp
        exact value
      exact ⟨n + 1, by change spair (inj 1 pt) branches = _; rw [branchEq]; rfl⟩
  · exact pt_mem_unitSet

theorem meaning (h : CheckedShape.{u,v} entries source shape)
    {reading : Assignment β V} (hr : ConstructorReading entries shape source constants reading)
    (hM : Realizes constants entries)
    (hsucc : ∀ n, ∃ (v : Nat) (A : V) (B : V → V), reading (.ctor source 0 1) [] ∈ˢ SetModel.piR v A B ∧
      Numeral.value n ∈ˢ A ∧ ∀ x, x ∈ˢ A → B x ∈ˢ univ v) :
    NaturalMeaning reading (.member source 0) (.ctor source 0 0) (.ctor source 0 1) := by
  constructor
  · intro n
    rw [hr.family [] rfl]
    exact value_mem h hM n
  · intro x member
    rw [hr.family [] rfl] at member
    exact value_complete h hM member
  · rw [hr.constructor [] rfl 0 zeroConstructor rfl]
    exact zero_value constants
  · intro n
    rw [hr.constructor [] rfl 1 succConstructor rfl]
    have he := Shape.constructorClosedValue_apply h hM
      (show (shape : Shape β).constructors[1]? = some succConstructor from rfl)
      (levels := []) (ps := []) (xs := []) (fs := [Numeral.value n]) (by trivial) (by trivial)
      (show _ ∧ True from ⟨value_mem h hM n, trivial⟩)
    simpa only [Telescope.applyN, Telescope.extend, List.nil_append, succ_value, Numeral.value] using he
  · exact hsucc

end Ix.Kernel.Certified.Natural
