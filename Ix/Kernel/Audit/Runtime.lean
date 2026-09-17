/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ExternAttr

/-! # Runtime closure of the public operations

The mathematical theorem is about the Lean functions; execution replaces some
of them. This audit walks the constants reachable from the public operations
through definition bodies, `implemented_by` targets, and `csimp` replacements,
and reports every replaced or unchecked constant it reaches: `@[extern]`
symbols, `implemented_by` redirections (which is how `partial` definitions
execute), and `unsafe` declarations. Replacements that belong to Lean's own
runtime (modules under the allowed prefixes) are inherited execution
foundations; any other one fails the audit. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

structure RuntimeReport where
  visited : Array Name := #[]
  externs : Array Name := #[]
  implementedBy : Array (Name × Name) := #[]
  unsafes : Array Name := #[]
  csimp : Array (Name × Name) := #[]

/-- Constants reachable through execution from `roots`. -/
partial def runtimeClosure (env : Environment) (roots : Array Name) : RuntimeReport :=
  go roots {} {}
where
  go (todo : Array Name) (seen : NameSet) (report : RuntimeReport) : RuntimeReport :=
    match todo.back? with
    | none => report
    | some name =>
      let todo := todo.pop
      if seen.contains name then go todo seen report else
      let seen := seen.insert name
      let report := { report with visited := report.visited.push name }
      match env.find? name with
      | none => go todo seen report
      | some info =>
        let extern := isExtern env name
        let report := if extern then { report with externs := report.externs.push name } else report
        let report := if info.isUnsafe then { report with unsafes := report.unsafes.push name } else report
        let (todo, report) := match Compiler.getImplementedBy? env name with
          | some target =>
            (todo.push target, { report with implementedBy := report.implementedBy.push (name, target) })
          | none => (todo, report)
        let (todo, report) := match (Compiler.CSimp.ext.getState env).map.find? name with
          | some entry => (todo.push entry.toDeclName, { report with csimp := report.csimp.push (name, entry.toDeclName) })
          | none => (todo, report)
        let todo := if extern then todo else
          match info with
          | .defnInfo v => todo ++ v.value.getUsedConstants
          | .opaqueInfo v => todo ++ v.value.getUsedConstants
          | _ => todo
        go todo seen report

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Fail if any replaced or unchecked constant reached from `roots` lives
outside the allowed module prefixes. -/
def checkRuntime (roots : Array Name) (prefixes : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do throwError m!"required root is missing: {root}"
  let report := runtimeClosure env roots
  let inherited (name : Name) : Bool :=
    match moduleOf env name with
    | some module => prefixes.any (·.isPrefixOf module)
    | none => false
  let flagged := (report.externs ++ report.implementedBy.map (·.1) ++ report.unsafes ++
      report.csimp.map (·.1)) |>.filter (!inherited ·) |>.qsort Name.lt
  unless flagged.isEmpty do
    throwError m!"project-level execution replacements reached from {roots}:\n{flagged}"
  logInfo m!"runtime closure of {roots}: {report.visited.size} constants; inherited externs \
    {report.externs.size}, implemented_by {report.implementedBy.size}, unsafe \
    {report.unsafes.size}, csimp {report.csimp.size}"

end Ix.Kernel.Audit

/-! ## Controls -/

namespace Ix.Kernel.Audit.RuntimeControls

def plainSquare (n : Nat) : Nat := n * n

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``plainSquare] #[`Init]

@[extern "ix_kernel_audit_control"]
opaque projectExtern (n : Nat) : Nat

def usesProjectExtern (n : Nat) : Nat := projectExtern n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesProjectExtern]:
[Ix.Kernel.Audit.RuntimeControls.projectExtern] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesProjectExtern] #[`Init]

unsafe def projectUnsafe (n : Nat) : Nat := n

@[implemented_by projectUnsafe]
def usesImplementedBy (n : Nat) : Nat := n

/-- error: project-level execution replacements reached from [Ix.Kernel.Audit.RuntimeControls.usesImplementedBy]:
[Ix.Kernel.Audit.RuntimeControls.projectUnsafe, Ix.Kernel.Audit.RuntimeControls.usesImplementedBy] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime #[``usesImplementedBy] #[`Init]

end Ix.Kernel.Audit.RuntimeControls
