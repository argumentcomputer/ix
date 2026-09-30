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
    (h : Checked.{u,v} env.toEnvironment ref spec) : { env' : Env β // AdmissionClaim.{u,v} env env' } :=
  ⟨env.push ref spec.entry, ⟨fun V _ m => by
    refine ⟨⟨assignment m.constants ref spec, ?_, ?_⟩⟩
    · rw [Env.toEnvironment_push]
      exact assignment_realizes h m.wf m.constants m.realizes
    · rw [Env.toEnvironment_push]
      exact environment_wf h m.wf, env.preserves_push ref spec.entry h.fresh⟩⟩

/-- The references a standard axiom's type mentions, in order of first occurrence. -/
def occurrences (t : VExpr β) : List (ConstRef β) := t.refs.eraseDups

/-- The spec of `propext` over the equality family `eq` and the `iff` family,
each at member 0 of its block with its constructor. Each eliminator is the
installed entry with that family's eliminator interface: Ixon stores a
recursor as its own record, so its reference is found, not assumed. When none
is found, the paired fixture position is used and `Spec.Prerequisites`
reports the mismatch. -/
def propextSpec (env : Env β) : ConstRef β → ConstRef β → Option (Spec β)
  | .member beq 0, .member biff 0 =>
    let eqRec := (env.findRef fun r =>
      decide (Basis.Equality.Interface env.toEnvironment (.member beq 0) (.ctor beq 0 0) r)).getD
        (.member beq 1)
    let iffRec := (env.findRef fun r =>
      decide (Basis.Iff.Interface env.toEnvironment (.member biff 0) (.ctor biff 0 0) r)).getD
        (.member biff 1)
    some (.propext (.member beq 0) (.ctor beq 0 0) eqRec (.member biff 0) (.ctor biff 0 0) iffRec)
  | _, _ => none

/-- The spec of `Classical.choice` over the `nonempty` family, with its found
eliminator. -/
def choiceSpec (env : Env β) : ConstRef β → Option (Spec β)
  | .member b 0 =>
    let recursor := (env.findRef fun r =>
      decide (Basis.Nonempty.Interface env.toEnvironment (.member b 0) (.ctor b 0 0) r)).getD
        (.member b 1)
    some (.choice (.member b 0) (.ctor b 0 0) recursor)
  | _ => none

end Ix.Kernel.Certified.Standard
