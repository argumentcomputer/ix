/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/RecursorValue.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `checkMode` takes the shape.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Ordinary.RecursorReading

namespace Ix.Kernel.Certified.Ordinary

open Model Model.SetTheory Model.SetTheory.Tower Model.SetModel Inductive

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

def ModeEvidence (entries : Environment β) (shape : Shape β) : ElimMode → Prop
  | .small => True
  | .large => LargeEvidence.{u,v} entries shape

def checkMode [DecidableEq β] (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (mode : ElimMode) : Option (CheckedClaim.{u} (ModeEvidence.{u,v} entries shape mode)) :=
  match mode with
  | .small => some ⟨trivial⟩
  | .large => checkLarge fuel entries shape

namespace Shape

noncomputable def recursorAt (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (mode : ElimMode) (m : V) (minors : List V) : V := by
  classical
  exact match mode with
  | .small => pt
  | .large =>
    if hD : (shape.container constants (mode.sourceArgs levels) env).WF
        (shape.level.eval (mode.sourceArgs levels)) then
      if hlarge : (shape.container constants (mode.sourceArgs levels) env).LargeElim
          (shape.level.eval (mode.sourceArgs levels)) then
        shape.largeValue constants (mode.sourceArgs levels) env (mode.motiveLevel.eval levels) m minors hD hlarge
      else pt
    else pt

theorem recursorAt_large (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (m : V) (minors : List V)
    (hD : (shape.container constants (ElimMode.large.sourceArgs levels) env).WF
      (shape.level.eval (ElimMode.large.sourceArgs levels)))
    (hlarge : (shape.container constants (ElimMode.large.sourceArgs levels) env).LargeElim
      (shape.level.eval (ElimMode.large.sourceArgs levels))) :
    shape.recursorAt constants levels env .large m minors =
      shape.largeValue constants (ElimMode.large.sourceArgs levels) env
        (ElimMode.large.motiveLevel.eval levels) m minors hD hlarge := by
  simp only [recursorAt, dif_pos hD, dif_pos hlarge]

theorem recursorSet_zero (shape : Shape β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (m : V) :
    shape.recursorSet constants levels env 0 m ∈ˢ (univZero : V) :=
  Telescope.piN_zero_mem _ (fun _ _ => piR_zero_mem_univZero)

variable {entries : Environment β} {shape : Shape β} {source : β}
  {constants : Assignment β V} {levels : List Nat} {env : Nat → V} {mode : ElimMode}

theorem recursorAt_mem (h : CheckedShape.{u,v} entries source shape)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hΓ : shape.parameterContext.Valid constants (mode.sourceArgs levels) env)
    {m : V} {minors : List V}
    (hm : m ∈ˢ shape.motiveSet constants (mode.sourceArgs levels) env (mode.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (mode.sourceArgs levels) env (mode.motiveLevel.eval levels) m minors) :
    shape.recursorAt constants levels env mode m minors ∈ˢ
      shape.recursorSet constants (mode.sourceArgs levels) env (mode.motiveLevel.eval levels) m := by
  cases mode with
  | small => exact pt_mem_smallRecursorSet h hM hΓ hm hminors
  | large =>
    rw [recursorAt_large _ _ _ _ _ _ (container_wf h hM hΓ) (container_large hmode hM hΓ)]
    exact largeValue_mem h hM hΓ hm hminors _ _

noncomputable def closedRecursorValue (shape : Shape β) (constants : Assignment β V)
    (levels : List Nat) (mode : ElimMode) : V :=
  let ls := mode.sourceArgs levels
  let v := mode.motiveLevel.eval levels
  Telescope.curry v (Telescope.interpret constants ls (fun _ => empty) shape.parameters) fun ps =>
    lamR v (shape.motiveSet constants ls (Telescope.extend (fun _ => empty) ps) v) fun m =>
      Telescope.curry v (Telescope.simple (shape.minorTypes constants ls (Telescope.extend (fun _ => empty) ps) v m))
        (fun minors => shape.recursorAt constants levels (Telescope.extend (fun _ => empty) ps) mode m minors)

theorem closedRecursorValue_mem (h : CheckedShape.{u,v} entries source shape)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries) :
    shape.closedRecursorValue constants levels mode ∈ˢ shape.closedRecursorSet constants levels mode := by
  apply Telescope.curry_mem
  intro ps hps
  apply lamR_mem
  intro m hm
  apply Telescope.curry_mem
  intro minors hminors
  exact recursorAt_mem h hmode hM
    (h.parameters.valid constants hM (mode.sourceArgs levels)
      (Context.valid_nil constants (mode.sourceArgs levels) (fun _ => empty)) hps) hm hminors

theorem closedRecursorValue_mem_source (h : CheckedShape.{u,v} entries source shape)
    {reading : Assignment β V} (hr : ConstructorReading entries shape source constants reading)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries)
    (hn : levels.length = mode.recUvars shape.universes) :
    shape.closedRecursorValue constants levels mode ∈ˢ
      interp reading levels (fun _ => empty) (shape.recursorType source mode) := by
  rw [recursorType_interp h hr hM hn]
  exact closedRecursorValue_mem h hmode hM

theorem closedRecursorValue_apply (h : CheckedShape.{u,v} entries source shape)
    (hmode : ModeEvidence.{u,v} entries shape mode) (hM : Realizes constants entries) {ps : List V}
    (hps : FitsS (Telescope.interpret constants (mode.sourceArgs levels) (fun _ => empty) shape.parameters) ps)
    {m : V} {minors : List V}
    (hm : m ∈ˢ shape.motiveSet constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels))
    (hminors : shape.MinorValuesFit constants (mode.sourceArgs levels) (Telescope.extend (fun _ => empty) ps)
      (mode.motiveLevel.eval levels) m minors) :
    Telescope.applyN (shape.closedRecursorValue constants levels mode) (ps ++ [m] ++ minors) =
      shape.recursorAt constants levels (Telescope.extend (fun _ => empty) ps) mode m minors := by
  have hbody (ps : List V) hps m hm minors hminors := recursorAt_mem h hmode hM
    (h.parameters.valid constants hM (mode.sourceArgs levels) (xs := ps)
      (Context.valid_nil constants (mode.sourceArgs levels) (fun _ => empty)) hps)
    (m := m) hm (minors := minors) hminors
  have hminor ps hps m hm := Telescope.curry_mem (w := mode.motiveLevel.eval levels) _ (hbody ps hps m hm)
  have hmotive ps hps := lamR_mem (v := mode.motiveLevel.eval levels) (hminor ps hps)
  rw [closedRecursorValue, Telescope.applyN_append, Telescope.applyN_append,
    Telescope.applyN_curry _ hps hmotive (fun hv _ _ => by
      rw [hv]
      exact piR_zero_mem_univZero)]
  change Telescope.applyN (app (lamR _ _ _) m) minors = _
  rw [app_lamR hm (hminor ps hps) (fun hv _ _ => by
    rw [hv]
    apply Telescope.piN_zero_mem
    intro _ _
    exact recursorSet_zero _ _ _ _ _)]
  exact Telescope.applyN_curry _ hminors (hbody ps hps m hm) (fun hv _ _ => by
    rw [hv]
    exact recursorSet_zero _ _ _ _ _)

end Shape
end Ix.Kernel.Certified.Ordinary
