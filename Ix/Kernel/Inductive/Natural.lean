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

/-- Publish family facts over either checked admission stage. -/
def installed (source : β) (stage : Stage β) : List (ConstRef β × ConstantEntry β) :=
  (shape : Shape β).stagedInstalledWith source stage (entry source)

theorem toEnvironment_installed (env : Env β) (source : β) (stage : Stage β)
    (h : Natural.Checked.{u,v} env.toEnvironment source stage) :
    (env.pushList (installed source stage)).toEnvironment =
      environment env.toEnvironment source stage :=
  Shape.toEnvironment_stagedInstalledWith env (shape : Shape β) source stage (entry source) h.block

end Certified.Natural

/-- Install the checked family facts, whether or not a recursor was supplied. -/
def installNaturalStage (env : Env β) (source : β) (stage : Stage β)
    (h : Natural.Checked.{u,v} env.toEnvironment source stage) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  ⟨env.pushList (Natural.installed source stage), ⟨fun V _ m => by
    refine ⟨⟨stage.assignment (Natural.shape : Shape β) m.constants source, ?_, ?_⟩⟩
    · rw [Natural.toEnvironment_installed env source stage h]
      exact Natural.assignment_realizes h m.wf m.constants m.realizes
    · rw [Natural.toEnvironment_installed env source stage h]
      exact Natural.environment_wf h m.wf,
    by
      intro r entry hr
      rw [Natural.toEnvironment_installed env source stage h]
      exact Natural.environment_old h hr⟩⟩

theorem installNaturalStage_family (env : Env β) (source : β) (stage : Stage β)
    (h : Natural.Checked.{u,v} env.toEnvironment source stage) :
    ((Natural.shape : Shape β).source source).Installed source 0
      (installNaturalStage env source stage h).val.toEnvironment :=
  Shape.stagedInstalledWith_family env (Natural.shape : Shape β) source stage (Natural.entry source) h.block ⟨rfl, rfl, rfl⟩

/-- Compatibility entry point for the stage with a supplied recursor. -/
def installNatural (env : Env β) (source : β) (mode : ElimMode) {recursor : ConstRef β}
    (h : Natural.Checked.{u,v} env.toEnvironment source (.recursor mode recursor)) :
    { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  installNaturalStage env source (.recursor mode recursor) h

theorem installNatural_fidelity (env : Env β) (source : β) (mode : ElimMode)
    (h : Natural.Checked.{u,v} env.toEnvironment source (.recursor mode (.member source 1))) (k : Bool) :
    (Block.mk [(Natural.shape : Shape β).source source, (Natural.shape : Shape β).recursorSource source mode k]).Installed source
      (installNatural env source mode h).val.toEnvironment :=
  Shape.installedWith_fidelity env (Natural.shape : Shape β) source mode k (Natural.entry source) ⟨rfl, rfl, rfl⟩

theorem installNatural_members (env : Env β) (source : β) (mode : ElimMode)
    {recursor : ConstRef β}
    (h : Natural.Checked.{u,v} env.toEnvironment source (.recursor mode recursor)) (k : Bool) :
    ((Natural.shape : Shape β).source source).Installed source 0
        (installNatural env source mode h).val.toEnvironment ∧
      ∃ entry, (installNatural env source mode h).val.toEnvironment recursor = some entry ∧
        ((Natural.shape : Shape β).recursorSource source mode k recursor).Reads entry :=
  Shape.installedWith_members env (Natural.shape : Shape β) source mode k (Natural.entry source) recursor
    ⟨rfl, rfl, rfl⟩ h.block.recursorChecked

end Ix.Kernel
