/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Inductive.Ordinary
import Ix.Kernel.Certified.Structure.Publish
import Ix.Kernel.Certified.Structure.Read

/-! # Installing a structure

A structure is an ordinary block whose family entry is published with the
projection facts, the eta and iota equations, their typed endpoints, and
the arities (`Ix.Kernel.Certified.Structure`). Installation reuses the
ordinary entry list with that family entry. -/

namespace Ix.Kernel

open Model Certified Certified.Ordinary Certified.Structure Inductive

universe u v

variable {β : Type u} [DecidableEq β]

namespace Certified.Structure.Description

/-- The entries an accepted structure installs, newest first. -/
def installed (d : Description β) (source : β) (mode : ElimMode) :
    List (ConstRef β × ConstantEntry β) :=
  d.ordinary.installedWith source mode (d.publishedEntry source)

theorem toEnvironment_installed (env : Env β) (d : Description β) (source : β) (mode : ElimMode) :
    (env.pushList (d.installed source mode)).toEnvironment =
      d.publishedEnvironment env.toEnvironment source mode := by
  rw [installed, Shape.toEnvironment_installedWith]
  funext q
  simp only [publishedEnvironment, Shape.publishedEnvironment, Shape.constructorEnvironment,
    Shape.familyEnvironment, Environment.insert, Environment.overlay]
  by_cases h0 : q = ConstRef.member source 0
  · subst h0
    simp [Shape.constructorEntries]
  · by_cases h1 : q = ConstRef.member source 1
    · subst h1
      simp
    · simp [h0, h1]

end Certified.Structure.Description

/-- Install a checked structure with its model extension. -/
def installStructure (env : Env β) (source : β) (d : Description β) (mode : ElimMode)
    (h : Checked.{u,v} env.toEnvironment d source mode) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  ⟨env.pushList (d.installed source mode), fun V _ m => by
    refine ⟨⟨d.ordinary.recursorAssignment m.constants source mode, ?_, ?_⟩⟩
    · rw [Description.toEnvironment_installed]
      exact d.publishedAssignment_realizes h m.wf m.constants m.realizes
    · rw [Description.toEnvironment_installed]
      exact d.publishedEnvironment_wf h m.wf⟩

end Ix.Kernel
