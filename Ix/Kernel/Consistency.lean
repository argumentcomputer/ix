/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Check
import Ix.Kernel.Model.Interpret

/-! # The public theorems

Every environment the kernel accepts has a model in every set theory, and no
accepted constant inhabits a type that denotes the empty set. The statements
are fixed here at milestone K0 and preserved by every later milestone: no
theorem below is removed, weakened, or given a new hypothesis.

* `checkDecls_has_model`: the conditional form. Checking declarations against
  an environment that already has a model yields an environment with a model.
* `check_has_model`: the closed form. The closed check constructs its starting
  model itself.
* `no_proof_of_False`: an installed entry whose type denotes the empty set in
  every model of its environment cannot exist. A constructor-free inductive
  (Lean's `False` or `Empty`) is one instance once inductives are supported;
  the hypothesis is semantic so that no pinned constant is needed.

The set theory `SetTheory V` is the standing hypothesis of the argument, not a
hypothesis about the input; the separate `Models/SetTheory` package supplies
an instance under an explicit large-cardinal assumption. -/

namespace Ix.Kernel

open Model Model.SetTheory

universe u v

variable {β : Type u} [DecidableEq β]

/-- A model of a checked environment in the set theory `V`: one assignment of
a set to every reference at every universe instance under which every
installed entry is realized (`Model.Realizes`): its type is well denoted, the
constant is a member of what its type denotes, its body if any denotes the
constant, and its published equations and facts hold. -/
structure Model (V : Type v) [SetTheory V] (env : Env β) where
  constants : Assignment β V
  realizes : Realizes constants env.toEnvironment

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

/-- `A`, a type with `universes` universe parameters, denotes the empty set in
every model of `env`, at every universe instance and valuation. -/
def Env.EmptyType (env : Env β) (universes : Nat) (A : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (m : Model V env) (levels : List Nat),
    levels.length = universes → ∀ valuation : Nat → V,
      interp m.constants levels valuation A = SetTheory.empty

omit [DecidableEq β] in
/-- At K0 the fold accepts only the empty list. -/
theorem checkDecls_ok {cfg : Config} {env env' : Env β} {decls : List (Decl β)}
    (h : checkDecls cfg env decls = .ok env') : decls = [] ∧ env' = env := by
  cases decls with
  | nil => exact ⟨rfl, (Except.ok.inj h).symm⟩
  | cons d ds =>
    have : checkDecls cfg env (d :: ds) =
        .error (.declined "no declaration form is supported yet") := rfl
    rw [this] at h
    cases h

/-- Checking against an environment that already has a model yields an
environment with a model. -/
theorem checkDecls_has_model (V : Type v) [SetTheory V] {cfg : Config}
    {env env' : Env β} {decls : List (Decl β)} (m : Model V env)
    (h : checkDecls cfg env decls = .ok env') : Nonempty (Model V env') := by
  obtain ⟨-, rfl⟩ := checkDecls_ok h
  exact ⟨m⟩

/-- The closed check constructs a model of everything it accepts. -/
theorem check_has_model (V : Type v) [SetTheory V] {cfg : Config}
    {decls : List (Decl β)} {env : Env β} (h : check cfg decls = .ok env) :
    Nonempty (Model V env) :=
  checkDecls_has_model V (Model.emptyEnv V) h

/-- No accepted constant inhabits an empty type. -/
theorem no_proof_of_False (V : Type v) [SetTheory V] {cfg : Config}
    {decls : List (Decl β)} {env : Env β} (h : check cfg decls = .ok env)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : env.toEnvironment r = some entry)
    (hA : env.EmptyType.{u,v} entry.universes entry.type) : False := by
  obtain ⟨m⟩ := check_has_model V h
  have hmem := m.realizes.member r entry hr (List.replicate entry.universes 0)
    (by simp) (fun _ => SetTheory.empty)
  rw [hA V m _ (by simp) _] at hmem
  exact not_mem_empty _ hmem

end Ix.Kernel
