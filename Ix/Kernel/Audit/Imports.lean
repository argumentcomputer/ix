/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean.Elab.Command

/-! # Import allowlist for the certified closure

The transitive imports of the kernel's root modules must stay inside an
explicit allowlist of module prefixes. The graph is rebuilt from the module
headers of the current environment (`Environment.header`), so the check sees
`import`, `public import`, and `import all` alike. A `lean_lib` does not
enforce layering; this does, and the controls at the end fail on a
deliberately forbidden module. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

/-- Direct imports of every module in the environment. -/
def importGraph (env : Environment) : NameMap (Array Name) := Id.run do
  let mut graph : NameMap (Array Name) := {}
  for name in env.header.moduleNames, data in env.header.moduleData do
    graph := graph.insert name (data.imports.map (·.module))
  return graph

/-- Modules reachable from `roots` by imports, including the roots. -/
partial def importClosure (graph : NameMap (Array Name)) (roots : Array Name) : Array Name :=
  go roots {} #[]
where
  go (todo : Array Name) (seen : NameSet) (acc : Array Name) : Array Name :=
    match todo.back? with
    | none => acc
    | some name =>
      let todo := todo.pop
      if seen.contains name then go todo seen acc else
        let next := (graph.find? name).getD #[]
        go (todo ++ next) (seen.insert name) (acc.push name)

def allowed (prefixes : Array Name) (module : Name) : Bool :=
  prefixes.any (·.isPrefixOf module)

/-- Fail unless every module in the import closure of `roots` lies under one
of `prefixes`, and every root is present. -/
def checkImports (roots : Array Name) (prefixes : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let graph := importGraph env
  for root in roots do
    unless graph.contains root do throwError m!"required root module is missing: {root}"
  let closure := importClosure graph roots
  let offenders := closure.filter (!allowed prefixes ·) |>.qsort Name.lt
  unless offenders.isEmpty do
    throwError m!"forbidden modules in the certified import closure:\n{offenders}"
  logInfo m!"import closure of {roots}: {closure.size} modules, all under {prefixes}"

end Ix.Kernel.Audit

/-! ## Controls -/

/-- info: import closure of [Init.Prelude]: 1 modules, all under [Init] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkImports #[`Init.Prelude] #[`Init]

/-- error: forbidden modules in the certified import closure:
[Init.Prelude] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkImports #[`Init.Prelude] #[`Std]

/-- error: required root module is missing: Ix.Kernel.Audit.NoSuchModule -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel.Audit.NoSuchModule] #[`Ix]
