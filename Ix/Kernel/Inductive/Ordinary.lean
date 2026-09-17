/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Certified.Ordinary.Checked
import Ix.Kernel.Certified.Ordinary.Read

/-! # Installing an ordinary inductive block

Connects the ordinary-inductive route (`Ix.Kernel.Certified.Ordinary`) to the
checked environment: the entries an accepted block publishes, the equality of
the list-based environment with the route's published environment, and the
installation with its model extension (`StepClaim`). -/

namespace Ix.Kernel

open Model Certified Certified.Ordinary Inductive

universe u v

variable {β : Type u} [DecidableEq β]

namespace Certified.Ordinary.Shape

/-- The constructor entries of a block, positionally. -/
def constructorList (shape : Shape β) (source : β) : List (ConstRef β × ConstantEntry β) :=
  shape.constructors.zipIdx.map fun (ctor, i) => (.ctor source 0 i, shape.constructorEntry source ctor)

/-- The entries a block installs, newest first, with the family entry supplied. -/
def installedWith (shape : Shape β) (source : β) (mode : ElimMode) (fam : ConstantEntry β) :
    List (ConstRef β × ConstantEntry β) :=
  (.member source 1, shape.publishedRecursorEntry source mode) ::
    shape.constructorList source ++ [(.member source 0, fam)]

/-- The entries an accepted ordinary block installs, newest first. -/
def installed (shape : Shape β) (source : β) (mode : ElimMode) :
    List (ConstRef β × ConstantEntry β) :=
  shape.installedWith source mode shape.familyEntry

theorem find?_constructorList_member (shape : Shape β) (source b : β) (j : Nat) :
    (shape.constructorList source).find? (fun e => e.1 == ConstRef.member b j) = none := by
  apply List.find?_eq_none.mpr
  intro e he
  obtain ⟨⟨ctor, i⟩, -, rfl⟩ := List.mem_map.mp he
  simp

theorem find?_zipIdx_ctor (shape : Shape β) (source b : β) (j i : Nat) :
    ∀ (cs : List (Constructor β)) (off : Nat),
      ((cs.zipIdx off).map fun (ctor, k) => (ConstRef.ctor source 0 k, shape.constructorEntry source ctor)).find?
          (fun e => e.1 == ConstRef.ctor b j i) =
        if b = source ∧ j = 0 ∧ off ≤ i then
          (cs[i - off]?).map fun ctor => (ConstRef.ctor source 0 i, shape.constructorEntry source ctor)
        else none
  | [], off => by
    simp only [List.zipIdx_nil, List.map_nil, List.find?_nil, List.getElem?_nil, Option.map_none]
    split <;> rfl
  | c :: cs, off => by
    rw [List.zipIdx_cons, List.map_cons, List.find?_cons]
    by_cases hb : b = source ∧ j = 0 ∧ off = i
    · obtain ⟨rfl, rfl, rfl⟩ := hb
      simp
    · have hne : (ConstRef.ctor source 0 off == ConstRef.ctor b j i) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq, ConstRef.ctor.injEq]
        intro h
        exact hb ⟨h.1.symm, h.2.1.symm, h.2.2⟩
      simp only [hne]
      rw [find?_zipIdx_ctor shape source b j i cs (off + 1)]
      by_cases hc : b = source ∧ j = 0 ∧ off ≤ i
      · obtain ⟨rfl, rfl, hle⟩ := hc
        have hlt : off < i := by
          rcases Nat.lt_or_eq_of_le hle with h | h
          · exact h
          · exact absurd ⟨rfl, rfl, h⟩ hb
        have hi : i - off = (i - (off + 1)) + 1 := by omega
        simp [show off + 1 ≤ i from hlt, hle, hi]
      · have hc' : ¬ (b = source ∧ j = 0 ∧ off + 1 ≤ i) := fun h => hc ⟨h.1, h.2.1, by omega⟩
        simp [hc, hc']

theorem find?_constructorList_ctor (shape : Shape β) (source b : β) (j i : Nat) :
    (shape.constructorList source).find? (fun e => e.1 == ConstRef.ctor b j i) =
      if b = source ∧ j = 0 then
        (shape.constructors[i]?).map fun ctor => (ConstRef.ctor source 0 i, shape.constructorEntry source ctor)
      else none := by
  rw [constructorList, find?_zipIdx_ctor shape source b j i shape.constructors 0]
  simp

/-- The list-based environment after installation, for any family entry. -/
theorem toEnvironment_installedWith (env : Env β) (shape : Shape β) (source : β) (mode : ElimMode)
    (fam : ConstantEntry β) :
    (env.pushList (shape.installedWith source mode fam)).toEnvironment =
      ((env.toEnvironment.insert (.member source 0) fam).overlay (shape.constructorEntries source)).insert
        (.member source 1) (shape.publishedRecursorEntry source mode) := by
  funext q
  rw [Env.toEnvironment_pushList]
  simp only [installedWith, List.find?_cons, List.find?_append]
  unfold Environment.insert Environment.overlay
  cases q with
  | member b j =>
    rw [find?_constructorList_member]
    by_cases h1 : ConstRef.member b j = ConstRef.member source 1
    · cases h1
      simp
    · have h1' : (ConstRef.member source 1 == ConstRef.member b j) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm h1)
      simp only [h1', Option.none_or, constructorEntries, List.find?_nil, if_neg h1]
      by_cases h0 : ConstRef.member b j = ConstRef.member source 0
      · cases h0
        simp
      · have h0' : (ConstRef.member source 0 == ConstRef.member b j) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm h0)
        simp [h0', h0]
  | ctor b j i =>
    have h1 : (ConstRef.member source 1 == ConstRef.ctor b j i) = false := by simp
    have h0 : (ConstRef.member source 0 == ConstRef.ctor b j i) = false := by simp
    have hm1 : ConstRef.ctor b j i ≠ ConstRef.member source 1 := by simp
    have hm0 : ConstRef.ctor b j i ≠ ConstRef.member source 0 := by simp
    simp only [h1, h0, if_neg hm1, if_neg hm0, find?_constructorList_ctor,
      List.find?_nil]
    cases j with
    | zero =>
      by_cases hb : b = source
      · subst hb
        simp only [constructorEntries, true_and, if_true]
        cases shape.constructors[i]? <;> simp
      · simp [constructorEntries, hb]
    | succ j => simp [constructorEntries]

/-- The list-based environment after installation is the route's published
environment. -/
theorem toEnvironment_installed (env : Env β) (shape : Shape β) (source : β) (mode : ElimMode) :
    (env.pushList (shape.installed source mode)).toEnvironment =
      shape.publishedEnvironment env.toEnvironment source mode := by
  unfold publishedEnvironment constructorEnvironment familyEnvironment
  exact toEnvironment_installedWith env shape source mode shape.familyEntry

end Certified.Ordinary.Shape

/-- Install a checked ordinary block with its model extension. -/
def installOrdinary (env : Env β) (source : β) (shape : Shape β) (mode : ElimMode)
    (h : CheckedBlock.{u,v} env.toEnvironment source shape mode) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  ⟨env.pushList (shape.installed source mode), fun V _ m => by
    refine ⟨⟨shape.recursorAssignment m.constants source mode, ?_, ?_⟩⟩
    · rw [Shape.toEnvironment_installed]
      exact Shape.publishedAssignment_realizes h m.wf m.constants m.realizes
    · rw [Shape.toEnvironment_installed]
      exact Shape.publishedEnvironment_wf h m.wf⟩

end Ix.Kernel
