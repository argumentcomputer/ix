/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts

/-! # Exact axiom checks for the kernel's public roots

Adapted from the `jcb/ix-kernel-consistency` branch's
`Ix.Kernel.Verify.Audit.AxiomAudit`. The traversal follows checked types,
bodies, and inductive constructor types directly, so it sees dependencies that
imported axiom summaries can omit. The checked sets use resolved declaration
names; both missing and additional axioms fail, so a namespace migration
cannot silently widen a recorded boundary.

`#guard_kernel_axioms root [axioms]` fails elaboration unless the transitive
axiom set of `root` is exactly the listed one. The negative controls at the
end of this module exercise both rejection directions. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

/-- Constants referenced directly by a declaration's checked type, body, and
constructor list. -/
def directConstants : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

structure State where
  visited : NameSet := {}
  names : Array Name := #[]
  /-- Declarations that reference `sorryAx` directly. -/
  origins : Array Name := #[]
  axioms : Array Name := #[]

structure Node where
  isAxiom : Bool := false
  dependencies : Array Name := #[]

/-- Direct dependencies may be reused across roots in one fixed environment.
Reachability and axiom sets are computed afresh for each root. -/
abbrev Cache := NameMap Node

abbrev M := ReaderT Environment (StateM (State × Cache))

partial def visit (name : Name) : M Unit := do
  let (state, cache) ← get
  unless state.visited.contains name do
    let env ← read
    let (node, cache) := match cache.find? name with
      | some node => (node, cache)
      | none =>
        let node : Node := match env.checked.get.find? name with
          | some info =>
            { isAxiom := (info matches .axiomInfo _)
              dependencies := directConstants info }
          | none => {}
        (node, cache.insert name node)
    let state := { state with
      visited := state.visited.insert name
      names := state.names.push name
      axioms := if node.isAxiom then state.axioms.push name else state.axioms
      origins := if name != ``sorryAx && node.dependencies.contains ``sorryAx then
        state.origins.push name else state.origins }
    set (state, cache)
    node.dependencies.forM visit

def collectCached (env : Environment) (root : Name) (cache : Cache) : State × Cache :=
  ((visit root).run env).run ({}, cache) |>.2

/-- The transitive closure of `root` with its axioms and direct `sorryAx` users. -/
def collect (env : Environment) (root : Name) : State :=
  (collectCached env root {}).1

/-- Fail unless `root` exists and its axiom set is exactly `expected`. -/
def checkAxioms (root : Name) (expected : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    throwError m!"required root is missing: {root}"
  let actual := (collect env root).axioms
  unless actual.qsort Name.lt == expected.qsort Name.lt do
    let missing := expected.filter (!actual.contains ·)
    let additional := actual.filter (!expected.contains ·)
    throwError m!"axiom boundary changed for {root}\n\
      expected but absent: {missing}\nactual but unlisted: {additional}"

syntax (name := guardKernelAxioms) "#guard_kernel_axioms " ident " [" ident,* "]" : command

elab_rules : command
  | `(#guard_kernel_axioms $root:ident [$axioms:ident,*]) => do
    let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
    let expected ← axioms.getElems.mapM fun axiomSyntax =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo axiomSyntax
    checkAxioms rootName expected

end Ix.Kernel.Audit

/-! ## Controls

Successful exact checks in both directions, a constructor that depends on its
whole inductive definition, cache reuse across roots, and the two rejection
directions. -/

#guard_kernel_axioms Eq.refl []
#guard_kernel_axioms propext [propext]

private inductive AuditFixture : Prop where
  | plain
  | withAxiom (proof : propext (Iff.rfl : True ↔ True) = rfl)

#guard_kernel_axioms AuditFixture.plain [propext]

run_cmd do
  let env ← getEnv
  let (first, cache) := Ix.Kernel.Audit.collectCached env ``AuditFixture.plain {}
  let (independent, cache) := Ix.Kernel.Audit.collectCached env ``Eq.refl cache
  let (sibling, _) := Ix.Kernel.Audit.collectCached env ``AuditFixture.withAxiom cache
  unless first.axioms == #[``propext] && independent.axioms.isEmpty &&
      sibling.axioms == #[``propext] do
    throwError "cached axiom traversal changed a root's dependency boundary"

/--
error: axiom boundary changed for propext
expected but absent: []
actual but unlisted: [propext]
-/
#guard_msgs (whitespace := lax) in
#guard_kernel_axioms propext []

/--
error: axiom boundary changed for Eq.refl
expected but absent: [propext]
actual but unlisted: []
-/
#guard_msgs (whitespace := lax) in
#guard_kernel_axioms Eq.refl [propext]

/-- error: required root is missing: Ix.Kernel.Audit.doesNotExist -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkAxioms `Ix.Kernel.Audit.doesNotExist #[]
