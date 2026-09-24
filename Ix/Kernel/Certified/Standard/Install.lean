/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Standard.Checked
import Ix.Kernel.Env

/-! # Installing the standard axioms

`propext` and `Classical.choice` are admitted at their exact types over the
admitted `Eq`, `Iff`, and `Nonempty` interfaces, and realized by the point and
by a choice function respectively. -/

namespace Ix.Kernel.Certified.Standard

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Install a checked standard axiom at its reference. -/
def install (env : Env β) (ref : ConstRef β) (spec : Spec β)
    (h : Checked.{u,v} env.toEnvironment ref spec) : { env' : Env β // StepClaim.{u,v} env env' } :=
  ⟨env.push ref spec.entry, fun V _ m => by
    refine ⟨⟨assignment m.constants ref spec, ?_, ?_⟩⟩
    · rw [Env.toEnvironment_push]
      exact assignment_realizes h m.wf m.constants m.realizes
    · rw [Env.toEnvironment_push]
      exact environment_wf h m.wf⟩

/-- The references a standard axiom's type mentions, in order of first occurrence. -/
def occurrences (t : VExpr β) : List (ConstRef β) := t.refs.eraseDups

/-- The spec of `propext` over the equality family `eq` and the `iff` family,
each at member 0 of its block with the constructor and the eliminator where
the ordinary route puts them. -/
def propextSpec : ConstRef β → ConstRef β → Option (Spec β)
  | .member beq 0, .member biff 0 =>
    some (.propext (.member beq 0) (.ctor beq 0 0) (.member beq 1) (.member biff 0) (.ctor biff 0 0) (.member biff 1))
  | _, _ => none

/-- The spec of `Classical.choice` over the `nonempty` family. -/
def choiceSpec : ConstRef β → Option (Spec β)
  | .member b 0 => some (.choice (.member b 0) (.ctor b 0 0) (.member b 1))
  | _ => none

end Ix.Kernel.Certified.Standard
