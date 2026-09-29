/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.Checked

/-! # Family admission with an optional supplied recursor

An inductive family and its constructors have their own model construction.
A recursor adds its elimination checks and computation equations only when
the input supplies one. Both stages expose the same constructor reading to
the Nat and structure fact proofs, so those facts do not require a recursor.
-/

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Inductive
universe u v
variable {β : Type u} [DecidableEq β]

inductive Stage (β : Type u) where
  | family
  | recursor (mode : ElimMode) (reference : ConstRef β)

def Stage.environment (stage : Stage β) (shape : Shape β) (entries : Environment β)
    (source : β) : Environment β :=
  match stage with
  | .family => shape.constructorEnvironment entries source
  | .recursor mode reference => shape.publishedEnvironment entries source mode reference

def Stage.Checked (stage : Stage β) (entries : Environment β) (source : β) (shape : Shape β) : Prop :=
  match stage with
  | .family => CheckedShape.{u,v} entries source shape ∧ shape.ConstructorFormation.{u,v} entries source
  | .recursor mode reference => CheckedBlock.{u,v} entries source shape mode reference

def Stage.check (fuel : Nat) (stage : Stage β) (entries : Environment β) (source : β)
    (shape : Shape β) : Search (CheckedClaim.{u} (stage.Checked.{u,v} entries source shape)) :=
  match stage with
  | .family => do
    let shapeChecked ← checkShape.{u,v} fuel entries source shape
    let constructors ← shape.checkConstructorTypes.{u,v} fuel entries source shape.constructors
    return ⟨shapeChecked.down, constructors.down⟩
  | .recursor mode reference => checkBlock.{u,v} fuel entries source shape mode reference

namespace Stage

variable {stage : Stage β} {entries : Environment β} {source : β} {shape : Shape β}

theorem Checked.shapeChecked (h : stage.Checked.{u,v} entries source shape) :
    CheckedShape.{u,v} entries source shape := by
  cases stage with
  | family => exact h.1
  | recursor _ _ => exact h.shapeChecked

theorem environment_wf (h : stage.Checked.{u,v} entries source shape) (hE : entries.WF) :
    (stage.environment shape entries source).WF := by
  cases stage with
  | family => exact Shape.constructorEnvironment_wf h.1 hE h.2
  | recursor _ _ => exact Shape.publishedEnvironment_wf h hE

theorem environment_old (h : stage.Checked.{u,v} entries source shape)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : entries r = some entry) :
    stage.environment shape entries source r = some entry := by
  cases stage with
  | family =>
    exact Environment.overlay_old (Shape.constructorEntries_fresh h.1)
      (Environment.insert_old (h.1.fresh _ (List.mem_cons_self ..)) hr)
  | recursor _ _ => exact Shape.publishedEnvironment_old h hr

theorem family_lookup (h : stage.Checked.{u,v} entries source shape) :
    stage.environment shape entries source (.member source 0) = some shape.familyEntry := by
  cases stage with
  | family =>
    simp [environment, Shape.constructorEnvironment, Shape.familyEnvironment,
      Environment.overlay, Shape.constructorEntries]
  | recursor _ _ =>
    apply Environment.insert_old h.recursorChecked.fresh
    simp [Shape.constructorEnvironment, Shape.familyEnvironment,
      Environment.overlay, Shape.constructorEntries]

theorem constructor_lookup (h : stage.Checked.{u,v} entries source shape)
    {i : Nat} {ctor : Constructor β} (hc : shape.constructors[i]? = some ctor) :
    stage.environment shape entries source (.ctor source 0 i) = some (shape.constructorEntry source ctor) := by
  cases stage with
  | family => simp [environment, Shape.constructorEnvironment, Environment.overlay, Shape.constructorEntries, hc]
  | recursor _ _ =>
    apply Environment.insert_old h.recursorChecked.fresh
    simp [Shape.constructorEnvironment, Environment.overlay, Shape.constructorEntries, hc]

variable {V : Type v} [SetTheory V]

noncomputable def assignment (stage : Stage β) (shape : Shape β) (constants : Assignment β V)
    (source : β) : Assignment β V :=
  match stage with
  | .family => shape.constructorAssignment constants source
  | .recursor mode reference => shape.recursorAssignment constants source mode reference

theorem assignment_reading (h : stage.Checked.{u,v} entries source shape) (constants : Assignment β V) :
    ConstructorReading entries shape source constants (stage.assignment shape constants source) := by
  cases stage with
  | family => exact Shape.constructorAssignment_reading h.1 constants
  | recursor _ _ => exact (Shape.recursorAssignment_reading h.shapeChecked h.recursorChecked constants).toConstructorReading

theorem assignment_realizes (h : stage.Checked.{u,v} entries source shape) (hE : entries.WF)
    (constants : Assignment β V) (hM : Realizes constants entries) :
    Realizes (stage.assignment shape constants source) (stage.environment shape entries source) := by
  cases stage with
  | family => exact Shape.constructorAssignment_realizes h.1 hE h.2 constants hM
  | recursor _ _ => exact Shape.publishedAssignment_realizes h hE constants hM

end Stage
end Ix.Kernel.Certified.Ordinary
