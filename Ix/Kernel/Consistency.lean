/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Check
import Ix.Kernel.Model.Interpret

/-! # The public theorems

Every environment the kernel accepts has a model in every set theory, and no
accepted constant inhabits a type that denotes the empty set. The statements
were fixed at milestone K0 and are preserved by every later milestone: no
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

/-- `A`, a type with `universes` universe parameters, denotes the empty set in
every model of `env`, at every universe instance and valuation. -/
def Env.EmptyType (env : Env β) (universes : Nat) (A : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (m : Model V env) (levels : List Nat),
    levels.length = universes → ∀ valuation : Nat → V,
      interp m.constants levels valuation A = SetTheory.empty

omit [DecidableEq β] in
theorem Except.map_eq_ok {ε α γ : Type _} {f : α → γ} {x : Except ε α} {y : γ}
    (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => simp [Except.map] at h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- An accepted fold carries its model extension. -/
theorem checkDecls_step {cfg : Config} {env env' : Env β} {decls : List (Decl β)}
    (h : checkDecls.{u,v} cfg env decls = .ok env') : StepClaim.{u,v} env env' := by
  obtain ⟨⟨e, claim⟩, -, rfl⟩ := Except.map_eq_ok h
  exact claim

/-- Checking against an environment that already has a model yields an
environment with a model. -/
theorem checkDecls_has_model (V : Type v) [SetTheory V] {cfg : Config}
    {env env' : Env β} {decls : List (Decl β)} (m : Model V env)
    (h : checkDecls.{u,v} cfg env decls = .ok env') : Nonempty (Model V env') :=
  checkDecls_step h V m

/-- The closed check constructs a model of everything it accepts. -/
theorem check_has_model (V : Type v) [SetTheory V] {cfg : Config}
    {decls : List (Decl β)} {env : Env β} (h : check.{u,v} cfg decls = .ok env) :
    Nonempty (Model V env) :=
  checkDecls_has_model V (Model.emptyEnv V) h

/-- No accepted constant inhabits an empty type. -/
theorem no_proof_of_False (V : Type v) [SetTheory V] {cfg : Config}
    {decls : List (Decl β)} {env : Env β} (h : check.{u,v} cfg decls = .ok env)
    {r : ConstRef β} {entry : ConstantEntry β} (hr : env.toEnvironment r = some entry)
    (hA : env.EmptyType.{u,v} entry.universes entry.type) : False := by
  obtain ⟨m⟩ := check_has_model V h
  have hmem := m.realizes.member r entry hr (List.replicate entry.universes 0)
    (by simp) (fun _ => SetTheory.empty)
  rw [hA V m _ (by simp) _] at hmem
  exact not_mem_empty _ hmem

end Ix.Kernel
