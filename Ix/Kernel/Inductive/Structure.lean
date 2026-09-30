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

/-- Publish family facts over either checked admission stage. -/
def installed (d : Description β) (source : β) (stage : Stage β) : List (ConstRef β × ConstantEntry β) :=
  d.ordinary.stagedInstalledWith source stage (d.publishedEntry source)

theorem toEnvironment_installed (env : Env β) (d : Description β) (source : β) (stage : Stage β)
    (h : Checked.{u,v} env.toEnvironment d source stage) :
    (env.pushList (d.installed source stage)).toEnvironment =
      d.publishedEnvironment env.toEnvironment source stage :=
  Shape.toEnvironment_stagedInstalledWith env d.ordinary source stage (d.publishedEntry source) h.facts.block

end Certified.Structure.Description

/-- Install the checked family facts, whether or not a recursor was supplied. -/
def installStructureStage (env : Env β) (source : β) (d : Description β) (stage : Stage β)
    (h : Checked.{u,v} env.toEnvironment d source stage) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  ⟨env.pushList (d.installed source stage), ⟨fun V _ m => by
    refine ⟨⟨stage.assignment d.ordinary m.constants source, ?_, ?_⟩⟩
    · rw [Description.toEnvironment_installed env d source stage h]
      exact d.publishedAssignment_realizes h m.wf m.constants m.realizes
    · rw [Description.toEnvironment_installed env d source stage h]
      exact d.publishedEnvironment_wf h m.wf,
    by
      intro r entry hr
      rw [Description.toEnvironment_installed env d source stage h]
      exact d.publishedEnvironment_old h hr⟩⟩

theorem installStructureStage_family (env : Env β) (source : β) (d : Description β) (stage : Stage β)
    (h : Checked.{u,v} env.toEnvironment d source stage) :
    (d.ordinary.source source).Installed source 0
      (installStructureStage env source d stage h).val.toEnvironment :=
  Shape.stagedInstalledWith_family env d.ordinary source stage (d.publishedEntry source) h.facts.block ⟨rfl, rfl, rfl⟩

/-- Compatibility entry point for the stage with a supplied recursor. -/
def installStructure (env : Env β) (source : β) (d : Description β) (mode : ElimMode) {recursor : ConstRef β}
    (h : Checked.{u,v} env.toEnvironment d source (.recursor mode recursor)) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  installStructureStage env source d (.recursor mode recursor) h

theorem installStructure_fidelity (env : Env β) (source : β) (d : Description β) (mode : ElimMode)
    (h : Checked.{u,v} env.toEnvironment d source (.recursor mode (.member source 1))) (k : Bool) :
    (Block.mk [d.ordinary.source source, d.ordinary.recursorSource source mode k]).Installed source
      (installStructure env source d mode h).val.toEnvironment :=
  Shape.installedWith_fidelity env d.ordinary source mode k (d.publishedEntry source) ⟨rfl, rfl, rfl⟩

theorem installStructure_members (env : Env β) (source : β) (d : Description β) (mode : ElimMode)
    {recursor : ConstRef β}
    (h : Checked.{u,v} env.toEnvironment d source (.recursor mode recursor)) (k : Bool) :
    (d.ordinary.source source).Installed source 0
        (installStructure env source d mode h).val.toEnvironment ∧
      ∃ entry, (installStructure env source d mode h).val.toEnvironment recursor = some entry ∧
        (d.ordinary.recursorSource source mode k recursor).TypeBodyReads entry :=
  Shape.installedWith_members env d.ordinary source mode k (d.publishedEntry source) recursor
    ⟨rfl, rfl, rfl⟩ h.facts.block.recursorChecked

end Ix.Kernel
