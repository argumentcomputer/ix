/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Inductive.Ordinary
import Ix.Kernel.Certified.Natural.Publish

/-! # Installing the natural numbers

A block whose shape is exactly zero and successor is installed as an
ordinary block whose family entry carries the `natural` fact
(`Ix.Kernel.Certified.Natural`), which types literals at the family and
converts them with the constructors. -/

namespace Ix.Kernel

open Model Certified Certified.Ordinary Inductive

universe u v

variable {β : Type u} [DecidableEq β]

namespace Certified.Natural

/-- The entries the block installs, newest first. -/
def installed (source : β) (mode : ElimMode) : List (ConstRef β × ConstantEntry β) :=
  (shape : Shape β).installedWith source mode (entry source)

theorem toEnvironment_installed (env : Env β) (source : β) (mode : ElimMode) :
    (env.pushList (installed source mode)).toEnvironment = environment env.toEnvironment source mode := by
  rw [installed, Shape.toEnvironment_installedWith]
  funext q
  simp only [environment, Shape.publishedEnvironment, Shape.constructorEnvironment,
    Shape.familyEnvironment, Environment.insert, Environment.overlay]
  by_cases h0 : q = ConstRef.member source 0
  · subst h0
    simp [Shape.constructorEntries]
  · by_cases h1 : q = ConstRef.member source 1
    · subst h1
      simp
    · simp [h0, h1]

end Certified.Natural

/-- Install a checked natural-number block with its model extension. -/
def installNatural (env : Env β) (source : β) (mode : ElimMode)
    (h : Natural.Checked.{u,v} env.toEnvironment source mode) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  ⟨env.pushList (Natural.installed source mode), fun V _ m => by
    refine ⟨⟨(Natural.shape : Shape β).recursorAssignment m.constants source mode, ?_, ?_⟩⟩
    · rw [Natural.toEnvironment_installed]
      exact Natural.assignment_realizes h m.wf m.constants m.realizes
    · rw [Natural.toEnvironment_installed]
      exact Natural.environment_wf h m.wf⟩

end Ix.Kernel
