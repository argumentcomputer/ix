/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Environment
import Ix.Kernel.Model.Extension

/-! # The checked environment and its models

`Env β` is the environment the kernel builds: installed entries in
installation order, keyed by `ConstRef β`. The semantic model reads it through
`Env.toEnvironment`, the `Model.Environment β` view (a partial function from
references to entries). `β` is the reference type; the public API fixes it to
`Address`, where an address is an opaque key: the kernel never hashes.

Installation order is the host-supplied dependency order. The checker rejects
a reference to an entry that is not yet installed and rejects a duplicate
reference, so acceptance needs neither an acyclicity proof nor a collision
assumption about addresses.

A `Model V env` is an assignment realizing every installed entry together
with the syntactic well-formedness of the environment (`Environment.WF`),
which the checker's decidable scope and reference checks establish and the
model extension of a definition consumes. -/

namespace Ix.Kernel

open Model Model.SetTheory

universe u v

/-- The checked environment: entries in installation order, newest first. -/
structure Env (β : Type u) where
  entries : List (ConstRef β × Model.ConstantEntry β)

namespace Env

variable {β : Type u} [DecidableEq β]

/-- The empty environment, the starting point of the closed check. -/
def empty : Env β := ⟨[]⟩

/-- Look up an installed entry. Installation rejects duplicate references, so
the first match is the only match. -/
def lookup (env : Env β) (r : ConstRef β) : Option (Model.ConstantEntry β) :=
  (env.entries.find? fun e => e.1 == r).map (·.2)

/-- The semantic view of the environment read by the model. -/
def toEnvironment (env : Env β) : Model.Environment β := env.lookup

/-- Install an entry. -/
def push (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) : Env β :=
  { env with entries := (r, entry) :: env.entries }

@[simp] theorem lookup_empty (r : ConstRef β) : (empty : Env β).lookup r = none := rfl

@[simp] theorem toEnvironment_empty (r : ConstRef β) :
    (empty : Env β).toEnvironment r = none := rfl

theorem toEnvironment_push (env : Env β) (r : ConstRef β) (entry : Model.ConstantEntry β) :
    (env.push r entry).toEnvironment = env.toEnvironment.insert r entry := by
  funext q
  by_cases h : q = r
  · subst h
    simp [toEnvironment, lookup, push, Environment.insert]
  · have : (r == q) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp [toEnvironment, lookup, push, Environment.insert, this, h]

end Env

variable {β : Type u} [DecidableEq β]

/-- A model of a checked environment in the set theory `V`: one assignment of
a set to every reference at every universe instance under which every
installed entry is realized (`Model.Realizes`): its type is well denoted, the
constant is a member of what its type denotes, its body if any denotes the
constant, and its published equations and facts hold. The environment is
also syntactically well formed. -/
structure Model (V : Type v) [SetTheory V] (env : Env β) where
  constants : Assignment β V
  realizes : Realizes constants env.toEnvironment
  wf : env.toEnvironment.WF

/-- The empty environment has a model in every set theory. -/
noncomputable def Model.emptyEnv (V : Type v) [SetTheory V] : Model V (Env.empty : Env β) where
  constants := fun _ _ => SetTheory.empty
  realizes :=
    { typeValid := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      member := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      bodyValid := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      bodyValue := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      equationValue := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      factMeaning := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h }
  wf :=
    { typeScope := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      bodyScope := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      typeReferences := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      bodyReferences := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      equationScope := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      equationReferences := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      factScope := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h
      factReferences := fun _ _ h => by rw [Env.toEnvironment_empty] at h; cases h }

/-- One accepted step extends every model of the input environment. -/
def StepClaim (env env' : Env β) : Prop :=
  ∀ (V : Type v) [SetTheory V], Model.{u,v} V env → Nonempty (Model.{u,v} V env')

theorem StepClaim.refl (env : Env β) : StepClaim.{u,v} env env := fun _ _ m => ⟨m⟩

theorem StepClaim.trans {a b c : Env β} (h₁ : StepClaim.{u,v} a b) (h₂ : StepClaim.{u,v} b c) :
    StepClaim.{u,v} a c := fun V _ m => (h₁ V m).elim fun m' => h₂ V m'

end Ix.Kernel

namespace Ix.Kernel.Env

variable {β : Type u} [DecidableEq β]

/-- Install several entries at once; the list is newest first. -/
def pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β)) : Env β :=
  { env with entries := rs ++ env.entries }

theorem lookup_pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β))
    (q : ConstRef β) :
    (env.pushList rs).lookup q =
      match rs.find? (fun e => e.1 == q) with
      | some e => some e.2
      | none => env.lookup q := by
  simp only [lookup, pushList, List.find?_append]
  cases rs.find? (fun e => e.1 == q) <;> simp [Option.or]

theorem toEnvironment_pushList (env : Env β) (rs : List (ConstRef β × Model.ConstantEntry β))
    (q : ConstRef β) :
    (env.pushList rs).toEnvironment q =
      match rs.find? (fun e => e.1 == q) with
      | some e => some e.2
      | none => env.toEnvironment q := lookup_pushList env rs q

end Ix.Kernel.Env

namespace Ix.Kernel.Env

variable {β : Type u} [DecidableEq β]

