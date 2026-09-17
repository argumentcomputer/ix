/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.EmitUtil

/-! # Runtime closure of the public operations

The theorems are about the Lean functions; execution runs their compiled
code. This audit walks the compiled code reachable from the public
operations: the IR the code generator emits, after proofs and types are
erased and `csimp` and `implemented_by` replacements are applied. It reports
every constant it reaches that execution treats specially: `@[extern]`
symbols, `implemented_by` redirections (which is how `partial` definitions
execute), and `unsafe` declarations. Replacements that belong to Lean's own
runtime (modules under the allowed prefixes) are inherited execution
foundations; any other one fails the audit. Every audited root must have
compiled code, so the audit cannot pass vacuously. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

structure RuntimeReport where
  /-- Compiled functions reached, roots included. -/
  visited : Array Name := #[]
  externs : Array Name := #[]
  implementedBy : Array (Name × Name) := #[]
  unsafes : Array Name := #[]
  csimp : Array (Name × Name) := #[]
  /-- Names reached that have no compiled code. -/
  uncompiled : Array Name := #[]

/-- Compiled code reachable through execution from `roots`. -/
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
      let report := if (env.find? name).any (·.isUnsafe) then
        { report with unsafes := report.unsafes.push name } else report
      let (todo, report) := match Compiler.getImplementedBy? env name with
        | some target =>
          (todo.push target, { report with implementedBy := report.implementedBy.push (name, target) })
        | none => (todo, report)
      let (todo, report) := match (Compiler.CSimp.ext.getState env).map.find? name with
        | some entry =>
          (todo.push entry.toDeclName, { report with csimp := report.csimp.push (name, entry.toDeclName) })
        | none => (todo, report)
      match IR.findEnvDecl env name with
      | none => go todo seen { report with uncompiled := report.uncompiled.push name }
      | some decl =>
        let report := { report with visited := report.visited.push name }
        match decl with
        | .extern .. => go todo seen { report with externs := report.externs.push name }
        | .fdecl .. => go (todo ++ IR.collectUsedDecls env [decl]) seen report

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Fail if any replaced or unchecked constant reached from `roots` lives
outside the allowed module prefixes, or a root has no compiled code. -/
def checkRuntime (roots : Array Name) (prefixes : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  for root in roots do
    unless env.contains root do throwError m!"required root is missing: {root}"
    unless (IR.findEnvDecl env root).isSome || (Compiler.getImplementedBy? env root).isSome do
      throwError m!"root has no compiled code: {root}"
  let report := runtimeClosure env roots
  let inherited (name : Name) : Bool :=
    match moduleOf env name with
    | some module => prefixes.any (·.isPrefixOf module)
    | none => false
  let flagged := (report.externs ++ report.implementedBy.map (·.1) ++ report.unsafes ++
      report.csimp.map (·.1)) |>.filter (!inherited ·) |>.qsort Name.lt
  unless flagged.isEmpty do
    throwError m!"project-level execution replacements reached from {roots}:\n{flagged}"
  logInfo m!"runtime closure of {roots}: {report.visited.size} compiled functions; inherited \
    externs {report.externs.size}, implemented_by {report.implementedBy.size}, unsafe \
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

/-- A proof-only constant has no compiled code and cannot be audited. -/
theorem noCode : True := trivial

/-- error: root has no compiled code: Ix.Kernel.Audit.RuntimeControls.noCode -/
#guard_msgs in
run_cmd Ix.Kernel.Audit.checkRuntime #[``noCode] #[`Init]

end Ix.Kernel.Audit.RuntimeControls
