/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts
import IxSetTheoryModel.Carneiro

/-!
# Checked dependency boundary of the concrete set model

The traversal reads declaration types, bodies, and constructor fields directly.
It does not depend on imported axiom summaries or the kernel's named calculus.
-/

namespace IxSetTheoryModel.Audit

open Lean Elab Command

private def directConstants (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ match info with
  | .thmInfo value => value.value.getUsedConstants
  | .defnInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

private partial def closure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env rest seen
    else match env.checked.get.find? name with
    | some info => closure env ((directConstants info).toList ++ rest) (seen.insert name)
    | none => closure env rest (seen.insert name)

run_cmd do
  let env ← getEnv
  let root := ``carneiro_implies_ix
  let dependencies := closure env [root]
  let actual := dependencies.toList.toArray.filter fun name =>
    match env.checked.get.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    throwError m!"set-theory model axiom boundary changed:\n{actual.qsort Name.lt}"
  logInfo "Set-theory model full dependency audit passed: standard Lean axioms only"

end IxSetTheoryModel.Audit
