/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Fidelity
import Ix.Kernel.Certified.Ordinary.Stage
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
def installedWith (shape : Shape β) (source : β) (mode : ElimMode) (fam : ConstantEntry β)
    (recursor : ConstRef β := .member source 1) :
    List (ConstRef β × ConstantEntry β) :=
  (recursor, shape.publishedRecursorEntry source mode recursor) ::
    shape.constructorList source ++ [(.member source 0, fam)]

/-- The entries an accepted ordinary block installs, newest first. -/
def installed (shape : Shape β) (source : β) (mode : ElimMode)
    (recursor : ConstRef β := .member source 1) :
    List (ConstRef β × ConstantEntry β) :=
  shape.installedWith source mode shape.familyEntry recursor

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

theorem toEnvironment_constructorsWith (env : Env β) (shape : Shape β) (source : β)
    (fam : ConstantEntry β) :
    (env.pushList (shape.constructorList source ++ [(.member source 0, fam)])).toEnvironment =
      (env.toEnvironment.insert (.member source 0) fam).overlay (shape.constructorEntries source) := by
  funext q
  rw [Env.toEnvironment_pushList]
  simp only [List.find?_append]
  unfold Environment.insert Environment.overlay
  cases q with
  | member b j =>
    rw [find?_constructorList_member]
    simp only [Option.none_or, constructorEntries]
    by_cases h0 : ConstRef.member b j = ConstRef.member source 0
    · cases h0; simp
    · have h0' : (ConstRef.member source 0 == ConstRef.member b j) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm h0)
      simp [h0', h0]
  | ctor b j i =>
    rw [find?_constructorList_ctor]
    cases j with
    | zero =>
      by_cases hb : b = source
      · subst hb
        cases hc : shape.constructors[i]? <;> simp [constructorEntries, hc]
      · simp [constructorEntries, hb]
    | succ j => simp [constructorEntries]

/-- The list-based environment after installation, for any family entry. -/
theorem toEnvironment_installedWith (env : Env β) (shape : Shape β) (source : β) (mode : ElimMode)
    (fam : ConstantEntry β) (recursor : ConstRef β := .member source 1) :
    (env.pushList (shape.installedWith source mode fam recursor)).toEnvironment =
      ((env.toEnvironment.insert (.member source 0) fam).overlay (shape.constructorEntries source)).insert
        recursor (shape.publishedRecursorEntry source mode recursor) := by
  funext q
  rw [Env.toEnvironment_pushList]
  simp only [installedWith, List.find?_cons, List.find?_append]
  unfold Environment.insert Environment.overlay
  by_cases hr : q = recursor
  · subst q; simp
  · have hr' : (recursor == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm hr)
    simp only [hr', ite_eq_right hr]
    cases q with
    | member b j =>
      rw [find?_constructorList_member]
      simp only [Option.none_or, constructorEntries, List.find?_nil]
      by_cases h0 : ConstRef.member b j = ConstRef.member source 0
      · cases h0; simp
      · have h0' : (ConstRef.member source 0 == ConstRef.member b j) = false :=
          beq_eq_false_iff_ne.mpr (Ne.symm h0)
        simp [h0', h0]
    | ctor b j i =>
      simp only [show (ConstRef.member source 0 == ConstRef.ctor b j i) = false from by simp,
        show ConstRef.ctor b j i ≠ ConstRef.member source 0 from by simp,
        ite_false, find?_constructorList_ctor, List.find?_nil]
      cases j with
      | zero =>
        by_cases hb : b = source
        · subst hb
          simp only [constructorEntries, true_and, ite_true]
          cases shape.constructors[i]? <;> simp
        · simp [constructorEntries, hb]
      | succ j => simp [constructorEntries]

/-- The list-based environment after installation is the route's published environment. -/
theorem toEnvironment_installed (env : Env β) (shape : Shape β) (source : β) (mode : ElimMode)
    (recursor : ConstRef β := .member source 1) :
    (env.pushList (shape.installed source mode recursor)).toEnvironment =
      shape.publishedEnvironment env.toEnvironment source mode recursor := by
  unfold publishedEnvironment constructorEnvironment familyEnvironment
  exact toEnvironment_installedWith env shape source mode shape.familyEntry recursor

/-- The generated block's supplied members and constructors are installed at
their exact positions. Specializations may add facts to the family entry. -/
theorem installedWith_fidelity (env : Env β) (shape : Shape β) (source : β)
    (mode : ElimMode) (k : Bool) (fam : ConstantEntry β)
    (hf : (shape.source source).TypeBodyReads fam) :
    (Block.mk [shape.source source, shape.recursorSource source mode k]).Installed source
      (env.pushList (shape.installedWith source mode fam)).toEnvironment := by
  apply Block.installed_pair
  · refine ⟨⟨fam, ?_, hf⟩, ?_⟩
    · rw [toEnvironment_installedWith]
      simp [Environment.insert, Environment.overlay, constructorEntries]
    · intro j ctor hc
      change (shape.constructors.map (fun c => c.source shape source))[j]? = some ctor at hc
      cases hj : shape.constructors[j]? with
      | none => simp [List.getElem?_map, hj] at hc
      | some c =>
        simp only [List.getElem?_map, hj, Option.map_some, Option.some.injEq] at hc
        subst ctor
        refine ⟨shape.constructorEntry source c, ?_, rfl, rfl, rfl⟩
        rw [toEnvironment_installedWith]
        simp [Environment.insert, Environment.overlay, constructorEntries, hj]
  · refine ⟨⟨shape.publishedRecursorEntry source mode, ?_, rfl, rfl, rfl⟩, trivial⟩
    rw [toEnvironment_installedWith]
    exact Environment.insert_same ..

/-- Fidelity at independent family and recursor references. Freshness proves
that publishing the recursor preserves the family and every constructor. -/
theorem installedWith_members (env : Env β) (shape : Shape β) (source : β)
    (mode : ElimMode) (k : Bool) (fam : ConstantEntry β) (recursor : ConstRef β)
    (hf : (shape.source source).TypeBodyReads fam)
    (hR : RecursorFormation.{u,v} env.toEnvironment shape source mode recursor) :
    (shape.source source).Installed source 0
        (env.pushList (shape.installedWith source mode fam recursor)).toEnvironment ∧
      ∃ entry, (env.pushList (shape.installedWith source mode fam recursor)).toEnvironment recursor =
        some entry ∧ (shape.recursorSource source mode k recursor).TypeBodyReads entry := by
  constructor
  · refine ⟨⟨fam, ?_, hf⟩, ?_⟩
    · rw [toEnvironment_installedWith (recursor := recursor)]
      simp [Environment.insert, Environment.overlay, constructorEntries, Ne.symm hR.ne_family]
    · intro j ctor hc
      change (shape.constructors.map (fun c => c.source shape source))[j]? = some ctor at hc
      cases hj : shape.constructors[j]? with
      | none => simp [List.getElem?_map, hj] at hc
      | some c =>
        simp only [List.getElem?_map, hj, Option.map_some, Option.some.injEq] at hc
        subst ctor
        refine ⟨shape.constructorEntry source c, ?_, rfl, rfl, rfl⟩
        rw [toEnvironment_installedWith (recursor := recursor)]
        simp [Environment.insert, Environment.overlay, constructorEntries, hj,
          Ne.symm (hR.ne_constructor hj)]
  · refine ⟨shape.publishedRecursorEntry source mode recursor, ?_, rfl, rfl, rfl⟩
    rw [toEnvironment_installedWith (recursor := recursor)]
    exact Environment.insert_same ..

/-- Entries for either stage; family facts are independent of recursor presence. -/
def stagedInstalledWith (shape : Shape β) (source : β) (stage : Stage β) (fam : ConstantEntry β) :
    List (ConstRef β × ConstantEntry β) :=
  match stage with
  | .family => shape.constructorList source ++ [(.member source 0, fam)]
  | .recursor mode reference => shape.installedWith source mode fam reference

theorem toEnvironment_stagedInstalledWith (env : Env β) (shape : Shape β) (source : β)
    (stage : Stage β) (fam : ConstantEntry β) (h : stage.Checked.{u,v} env.toEnvironment source shape) :
    (env.pushList (shape.stagedInstalledWith source stage fam)).toEnvironment =
      (stage.environment shape env.toEnvironment source).insert (.member source 0) fam := by
  cases stage with
  | family =>
    rw [stagedInstalledWith, toEnvironment_constructorsWith]
    funext q
    cases q <;> simp [Stage.environment, constructorEnvironment, familyEnvironment,
      Environment.insert, Environment.overlay, constructorEntries]
    split <;> simp_all
  | recursor mode reference =>
    rw [stagedInstalledWith, toEnvironment_installedWith (recursor := reference)]
    funext q
    simp only [Stage.environment, publishedEnvironment, constructorEnvironment,
      familyEnvironment, Environment.insert, Environment.overlay]
    by_cases h0 : q = ConstRef.member source 0
    · subst q
      simp [constructorEntries, Ne.symm h.recursorChecked.ne_family]
    · by_cases hr : q = reference
      · subst q; simp [h.recursorChecked.ne_family]
      · simp [h0, hr]

theorem stagedInstalledWith_family (env : Env β) (shape : Shape β) (source : β)
    (stage : Stage β) (fam : ConstantEntry β) (h : stage.Checked.{u,v} env.toEnvironment source shape)
    (hf : (shape.source source).TypeBodyReads fam) :
    (shape.source source).Installed source 0
      (env.pushList (shape.stagedInstalledWith source stage fam)).toEnvironment := by
  rw [toEnvironment_stagedInstalledWith env shape source stage fam h]
  refine ⟨⟨fam, Environment.insert_same .., hf⟩, ?_⟩
  intro j ctor hc
  change (shape.constructors.map (fun c => c.source shape source))[j]? = some ctor at hc
  cases hj : shape.constructors[j]? with
  | none => simp [List.getElem?_map, hj] at hc
  | some c =>
    simp only [List.getElem?_map, hj, Option.map_some, Option.some.injEq] at hc
    subst ctor
    refine ⟨shape.constructorEntry source c, ?_, rfl, rfl, rfl⟩
    simpa [Environment.insert] using Stage.constructor_lookup h hj

end Certified.Ordinary.Shape

/-- Install a checked ordinary block with its model extension. -/
def installOrdinary (env : Env β) (source : β) (shape : Shape β) (mode : ElimMode) {recursor : ConstRef β}
    (h : CheckedBlock.{u,v} env.toEnvironment source shape mode recursor) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  ⟨env.pushList (shape.installed source mode recursor), ⟨fun V _ m => by
    refine ⟨⟨shape.recursorAssignment m.constants source mode recursor, ?_, ?_⟩⟩
    · rw [Shape.toEnvironment_installed (recursor := recursor)]
      exact Shape.publishedAssignment_realizes h m.wf m.constants m.realizes
    · rw [Shape.toEnvironment_installed (recursor := recursor)]
      exact Shape.publishedEnvironment_wf h m.wf,
    by
      intro r entry hr
      rw [Shape.toEnvironment_installed (recursor := recursor)]
      exact Shape.publishedEnvironment_old h hr⟩⟩

theorem installOrdinary_fidelity (env : Env β) (source : β) (shape : Shape β)
    (mode : ElimMode) (h : CheckedBlock.{u,v} env.toEnvironment source shape mode) (k : Bool) :
    (Block.mk [shape.source source, shape.recursorSource source mode k]).Installed source
      (installOrdinary env source shape mode h).val.toEnvironment :=
  shape.installedWith_fidelity env source mode k shape.familyEntry ⟨rfl, rfl, rfl⟩

theorem installOrdinary_members (env : Env β) (source : β) (shape : Shape β)
    (mode : ElimMode) {recursor : ConstRef β}
    (h : CheckedBlock.{u,v} env.toEnvironment source shape mode recursor) (k : Bool) :
    (shape.source source).Installed source 0 (installOrdinary env source shape mode h).val.toEnvironment ∧
      ∃ entry, (installOrdinary env source shape mode h).val.toEnvironment recursor = some entry ∧
        (shape.recursorSource source mode k recursor).TypeBodyReads entry :=
  shape.installedWith_members env source mode k shape.familyEntry recursor ⟨rfl, rfl, rfl⟩ h.recursorChecked

/-- Admit a family and its constructors without generating or checking an
absent recursor. -/
def installFamily (env : Env β) (source : β) (shape : Shape β)
    (h : (Stage.family : Stage β).Checked.{u,v} env.toEnvironment source shape) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  ⟨env.pushList (shape.stagedInstalledWith source .family shape.familyEntry),
    ⟨fun V _ m => by
      refine ⟨⟨shape.constructorAssignment m.constants source, ?_, ?_⟩⟩
      · rw [Shape.stagedInstalledWith, Shape.toEnvironment_constructorsWith]
        exact Shape.constructorAssignment_realizes h.1 m.wf h.2 m.constants m.realizes
      · rw [Shape.stagedInstalledWith, Shape.toEnvironment_constructorsWith]
        exact Shape.constructorEnvironment_wf h.1 m.wf h.2,
      by
        intro r entry hr
        rw [Shape.stagedInstalledWith, Shape.toEnvironment_constructorsWith]
        exact Stage.environment_old h hr⟩⟩

theorem installFamily_fidelity (env : Env β) (source : β) (shape : Shape β)
    (h : (Stage.family : Stage β).Checked.{u,v} env.toEnvironment source shape) :
    (shape.source source).Installed source 0 (installFamily env source shape h).val.toEnvironment :=
  shape.stagedInstalledWith_family env source .family shape.familyEntry h ⟨rfl, rfl, rfl⟩

end Ix.Kernel
