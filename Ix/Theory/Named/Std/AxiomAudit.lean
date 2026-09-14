/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
# Exact axiom checks for named-specification proofs

The checked sets use resolved declaration names, independent of pretty-print
width and dependency traversal order. Both missing and additional axioms fail
the check; a namespace migration cannot silently widen the recorded boundary.
-/

open Lean Elab Command

namespace Ix.Theory.Named.AxiomAudit

/-- Traverse checked declarations directly. Imported axiom summaries can
omit dependencies of mutually recursive declaration groups. -/
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
  origins : Array Name := #[]
  axioms : Array Name := #[]

structure Node where
  isAxiom : Bool := false
  dependencies : Array Name := #[]

/-- Direct dependencies may be reused across roots in one fixed environment.
Reachability and axiom sets are always computed afresh for each root. -/
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

def collect (env : Environment) (root : Name) : State :=
  (collectCached env root {}).1

end Ix.Theory.Named.AxiomAudit

syntax (name := guardNamedAxioms)
  "#guard_named_axioms " ident " [" ident,* "]" : command

elab_rules : command
  | `(#guard_named_axioms $root:ident [$axioms:ident,*]) => do
    let rootName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
    let expected ← axioms.getElems.mapM fun axiomSyntax =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo axiomSyntax
    let actual := (Ix.Theory.Named.AxiomAudit.collect (← getEnv) rootName).axioms
    unless actual.qsort Name.lt == expected.qsort Name.lt do
      let missing := expected.filter (!actual.contains ·)
      let additional := actual.filter (!expected.contains ·)
      throwError m!"axiom boundary changed for {rootName}\n\
        expected but absent: {missing}\nactual but unlisted: {additional}"

-- Exercise both rejection directions as well as successful exact checks.
#guard_named_axioms Eq.refl []
#guard_named_axioms propext [propext]

-- A constructor depends on its full inductive definition, including siblings.
private inductive AuditFixture : Prop where
  | plain
  | withAxiom (proof : propext (Iff.rfl : True ↔ True) = rfl)

#guard_named_axioms AuditFixture.plain [propext]

run_cmd do
  let env ← getEnv
  let (first, cache) := Ix.Theory.Named.AxiomAudit.collectCached env
    ``AuditFixture.plain {}
  let (independent, cache) := Ix.Theory.Named.AxiomAudit.collectCached env ``Eq.refl cache
  let (sibling, _) := Ix.Theory.Named.AxiomAudit.collectCached env
    ``AuditFixture.withAxiom cache
  unless first.axioms == #[``propext] && independent.axioms.isEmpty &&
      sibling.axioms == #[``propext] do
    throwError "cached axiom traversal changed a root's dependency boundary"

/--
error: axiom boundary changed for propext
expected but absent: []
actual but unlisted: [propext]
-/
#guard_msgs (whitespace := lax) in
#guard_named_axioms propext []

/--
error: axiom boundary changed for Eq.refl
expected but absent: [propext]
actual but unlisted: []
-/
#guard_msgs (whitespace := lax) in
#guard_named_axioms Eq.refl [propext]
