/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean

/-! Checked declaration traversal for the certified host adapters. Runtime
workers and foreign interfaces are inventoried separately from proof axioms. -/

open Lean Lean.Elab Command

namespace Ix.Certified.AuditSupport

private def constants (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ match info with
  | .thmInfo value => value.value.getUsedConstants
  | .defnInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

private partial def closure (env : Environment) (runtime : Bool) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env runtime rest seen
    else match env.checked.get.find? name with
    | none => closure env runtime rest (seen.insert name)
    | some info =>
      let extras := if runtime then Id.run do
        let mut names := #[]
        let worker := Lean.Compiler.mkUnsafeRecName name
        if (env.checked.get.find? worker).isSome then names := names.push worker
        if let some other := Lean.Compiler.getImplementedBy? env name then
          names := names.push other
        if let some other := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
          names := names.push other.toDeclName
        return names
      else #[]
      closure env runtime ((constants info ++ extras).toList ++ rest) (seen.insert name)

private def projectConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx =>
    let moduleName := env.allImportedModuleNames[idx.toNat]!
    (`Ix).isPrefixOf moduleName || (`Blake3).isPrefixOf moduleName

/-- Include constructor types and full checked bodies instead of relying on
imported axiom summaries. Both added and removed assumptions require review. -/
def checkAxioms (env : Environment) (root : Name) (expected : Array Name) :
    CommandElabM (Array Name) := do
  let mut actual := #[]
  for name in closure env false [root] do
    let some info := env.checked.get.find? name
      | throwError "certified adapter has an unavailable checked dependency: {name}"
    if info.isAxiom then actual := actual.push name
  let sorted := actual.qsort Name.lt
  unless sorted == expected.qsort Name.lt do
    throwError "certified axiom boundary changed for {root}: expected {expected.qsort Name.lt}, actual {sorted}"
  return sorted

private def expectedAxioms (root : Name) : Array Name :=
  if #[`Ix.Certified.readLevel_value, `Ix.Certified.treeLeaves_join].contains root then
    #[``propext]
  else if #[`Ix.Certified.readSignature?, `Ix.Certified.constantBytes?,
      `Ix.Certified.resolveReference_iff, `Ix.Certified.readExpr_sound,
      `Ix.Certified.ExprReading.unique, `Ix.Certified.readExpr_fuel_independent,
      `Ix.Certified.readBlock_sourceHeader, `Ix.Certified.readStore_sourceHeader,
      `Ix.Certified.readSignature_sound, `Ix.Theory.Certificate.Modeled.witness?,
      `Ix.Theory.Certificate.sourceGroup?, `Ix.Theory.Certificate.proofWitness?,
      `Ix.Certified.modelCandidate?, `Ix.Certified.modelCandidates?].contains root then
    #[``propext, ``Quot.sound]
  else #[``propext, ``Classical.choice, ``Quot.sound]

def distinct (names : Array Name) : Array Name :=
  names.foldl (fun result name => if result.contains name then result else result.push name) #[]

/-- Freeze theorem types, premise definitions, and transitive execution
dependencies. This does not establish correctness of native execution. -/
def report (label : String) (roots premises : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    let some info := env.checked.get.find? root
      | throwError "certified audit: missing root {root}"
    let axioms ← checkAxioms env root (expectedAxioms root)
    liftTermElabM do logInfo m!"ROOT {root}\n{← Meta.ppExpr info.type}\nAXIOMS {axioms}"
  for name in premises do
    let some info := env.checked.get.find? name
      | throwError "certified audit: missing premise {name}"
    liftTermElabM do
      logInfo m!"PREMISE {name}\n{← Meta.ppExpr info.type}"
      if let .defnInfo value := info then logInfo m!"DEFINITION\n{← Meta.ppExpr value.value}"
  let logical := closure env false roots.toList
  let reachable := (closure env true roots.toList).toList.mergeSort (fun a b => a.toString < b.toString)
  let mut workers : Array Name := #[]
  let mut externs : Array Name := #[]
  let mut replacements : Array (Name × Name) := #[]
  for name in reachable do
    let some info := env.checked.get.find? name
      | throwError "certified adapter has an unavailable checked runtime dependency: {name}"
    if projectConstant env name then
      if let some parent := Lean.Compiler.isUnsafeRecName? name then
        match env.checked.get.find? parent with
        | some (.defnInfo original) =>
          unless original.safety == .safe do
            throwError "certified recursion worker source is not safe: {name}"
        | _ => throwError "certified recursion worker has no safe source definition: {name}"
        workers := workers.push name
      if Lean.isExtern env name then externs := externs.push name
      if let some other := Lean.Compiler.getImplementedBy? env name then
        replacements := replacements.push (name, other)
      if let some other := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
        replacements := replacements.push (name, other.toDeclName)
      if let .defnInfo definition := info then
        unless definition.safety == .safe || (Lean.Compiler.isUnsafeRecName? name).isSome do
          throwError "certified adapter has an unreviewed unsafe runtime: {name}"
      if let .opaqueInfo definition := info then
        if definition.isUnsafe then throwError "certified adapter has an unsafe opaque runtime: {name}"
      if Lean.Elab.ComputedFields.computedFieldAttr.hasTag env name then
        throwError "certified adapter has an unreviewed computed field: {name}"
  unless externs == #[`Blake3.Rust.hasherFinalize, `Blake3.Rust.hasherInit,
      `Blake3.Rust.hasherInitDeriveKey, `Blake3.Rust.hasherInitKeyed,
      `Blake3.Rust.hasherUpdate] do
    throwError "certified runtime extern inventory changed: {externs}"
  unless replacements.isEmpty do
    throwError "certified runtime replacements changed: {replacements}"
  for name in externs do
    let some info := env.checked.get.find? name
      | throwError "certified runtime extern is missing: {name}"
    liftTermElabM do logInfo m!"RUNTIME EXTERN {name}\n{← Meta.ppExpr info.type}"
  for name in workers.qsort Name.lt do
    let some (.defnInfo value) := env.checked.get.find? name
      | throwError "certified recursion worker is missing: {name}"
    liftTermElabM do
      logInfo m!"RECURSION WORKER {name}\n{← Meta.ppExpr value.type}\nIMPLEMENTATION\n{← Meta.ppExpr value.value}"
  logInfo m!"{label} ROOTS {roots.size}; LOGICAL DECLARATIONS {logical.size}; WITH RUNTIME {reachable.length}"
  logInfo m!"RUNTIME EXTERNS {externs}\nRECURSION WORKERS {workers.size}"
  logInfo "All inventoried recursion workers have safe logical sources; no partial opaque source or executable replacement is permitted. Runtime diagnostics cover Ix and Blake3 modules, including private constants. Lean/Std execution and the BLAKE3 foreign interface remain external runtime boundaries."
  logInfo "These host-adapter roots establish semantic claims under the enforced profile and explicit model premises. They do not establish full production-checker refinement or Aiur compiler/AIR soundness."

private inductive ConstructorAuditFixture where
  | plain
  | withProof (proof : propext (Iff.refl True) = rfl)

run_cmd do
  let _ ← checkAxioms (← getEnv) ``ConstructorAuditFixture.plain #[``propext]
  let _ ← checkAxioms (← getEnv) ``Eq.refl #[]

/-- error: certified axiom boundary changed for Eq.refl: expected [propext], actual [] -/
#guard_msgs in
run_cmd do
  let _ ← checkAxioms (← getEnv) ``Eq.refl #[``propext]

/-- error: certified axiom boundary changed for propext: expected [], actual [propext] -/
#guard_msgs in
run_cmd do
  let _ ← checkAxioms (← getEnv) ``propext #[]

end Ix.Certified.AuditSupport
