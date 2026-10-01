import Lean.Elab.Command

/-! # Import allowlist for the certified closure

The transitive imports of the kernel's root modules must stay inside an
explicit allowlist of module prefixes. The graph is rebuilt from the module
headers of the current environment (`Environment.header`), so the check sees
`import`, `public import`, `meta import`, and `import all` alike. A
`lean_lib` does not enforce layering; this does, and the controls at the end
fail on a deliberately forbidden module.

One ruling refines the closure: a `meta import` made by
a module under `ElaborationImports.importers` is elaboration-time only. The
modules reached only through such edges form the elaboration closure, which
is checked against `ElaborationImports.allowed` instead. This is how
`Ix.Kernel.BasisGen` uses `Lean`: everywhere
else `Lean` stays forbidden. -/

open Lean Elab Command

namespace Ix.Kernel.Audit

/-- Direct imports of every module in the environment. -/
def importGraph (env : Environment) : NameMap (Array Name) := Id.run do
  let mut graph : NameMap (Array Name) := {}
  for name in env.header.moduleNames, data in env.header.moduleData do
    graph := graph.insert name (data.imports.map (·.module))
  return graph

/-- Direct imports of every module, with their kind. -/
def importEdges (env : Environment) : NameMap (Array Import) := Id.run do
  let mut graph : NameMap (Array Import) := {}
  for name in env.header.moduleNames, data in env.header.moduleData do
    graph := graph.insert name data.imports
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

/-- Elaboration-time import edges: a `meta import` by a module under one of
`importers` leads into the elaboration closure, whose modules must lie under
`allowed` (or the ordinary prefixes). -/
structure ElaborationImports where
  importers : Array Name := #[]
  allowed : Array Name := #[]

/-- The runtime closure (every edge except elaboration-time ones) and the
modules reached only through elaboration-time edges. -/
def splitClosure (graph : NameMap (Array Import)) (elaboration : ElaborationImports)
    (roots : Array Name) : Array Name × Array Name :=
  let elaborationEdge (importer : Name) (edge : Import) : Bool :=
    edge.isMeta && allowed elaboration.importers importer
  let runtime := importClosure
    (graph.foldl (init := {}) fun acc name edges =>
      acc.insert name ((edges.filter (!elaborationEdge name ·)).map (·.module)))
    roots
  let entries := runtime.foldl (init := #[]) fun acc name =>
    acc ++ (((graph.find? name).getD #[]).filter (elaborationEdge name ·)).map (·.module)
  let below := importClosure (graph.foldl (init := {}) fun acc name edges =>
    acc.insert name (edges.map (·.module))) entries
  (runtime, below.filter (!runtime.contains ·))

/-- Fail unless every module in the runtime import closure of `roots` lies
under one of `prefixes`, every module reached only through an
elaboration-time edge lies under `elaboration.allowed` or `prefixes`, and
every root is present. -/
def checkImportsWith (roots : Array Name) (prefixes : Array Name)
    (elaboration : ElaborationImports) : CommandElabM Unit := do
  let env ← getEnv
  let graph := importEdges env
  for root in roots do
    unless graph.contains root do throwError m!"required root module is missing: {root}"
  let (runtime, below) := splitClosure graph elaboration roots
  let offenders := runtime.filter (!allowed prefixes ·) |>.qsort Name.lt
  unless offenders.isEmpty do
    throwError m!"forbidden modules in the certified import closure:\n{offenders}"
  let elaborationOffenders := below.filter (fun module =>
    !allowed prefixes module && !allowed elaboration.allowed module) |>.qsort Name.lt
  unless elaborationOffenders.isEmpty do
    throwError m!"forbidden modules below the elaboration-time imports:\n{elaborationOffenders}"
  let elaborationSummary := if below.isEmpty then "" else
    s!"; {below.size} more at elaboration time, all under {prefixes ++ elaboration.allowed}"
  logInfo m!"import closure of {roots}: {runtime.size} modules, all under {prefixes}{elaborationSummary}"

/-- `checkImportsWith` with no elaboration-time edges. -/
def checkImports (roots : Array Name) (prefixes : Array Name) : CommandElabM Unit :=
  checkImportsWith roots prefixes {}

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

/-! The elaboration-time split, on a synthetic graph: `A.Gen` meta-imports
`L.Elab`, which imports `L.Core`; `A.Main` imports `A.Gen` and `B`, and `B`
meta-imports `L.Other`. Only `A.Gen` is an elaboration-time importer, so
`L.Elab` and `L.Core` are elaboration time and `L.Other` is not. -/

namespace Ix.Kernel.Audit.ImportControls

open Lean

def graph : NameMap (Array Import) :=
  ({} : NameMap (Array Import))
    |>.insert `A.Main #[{ module := `A.Gen }, { module := `B }]
    |>.insert `A.Gen #[{ module := `L.Elab, isMeta := true }]
    |>.insert `B #[{ module := `L.Other, isMeta := true }]
    |>.insert `L.Elab #[{ module := `L.Core }]
    |>.insert `L.Core #[]
    |>.insert `L.Other #[]

def sorted (names : Array Name) : List String := ((names.map toString).qsort (· < ·)).toList

def split (graph : NameMap (Array Import)) (importers : Array Name) : List String × List String :=
  let (runtime, below) := Ix.Kernel.Audit.splitClosure graph { importers } #[`A.Main]
  (sorted runtime, sorted below)

#guard split graph #[`A.Gen] == (["A.Gen", "A.Main", "B", "L.Other"], ["L.Core", "L.Elab"])
-- Without the ruling every module is in the runtime closure.
#guard split graph #[] == (["A.Gen", "A.Main", "B", "L.Core", "L.Elab", "L.Other"], [])
-- A module reached both ways belongs to the runtime closure.
#guard split (graph.insert `B #[{ module := `L.Core }]) #[`A.Gen] ==
  (["A.Gen", "A.Main", "B", "L.Core"], ["L.Elab"])
-- A non-meta import by an elaboration-time importer is an ordinary edge.
#guard split (graph.insert `A.Gen #[{ module := `L.Elab }]) #[`A.Gen] ==
  (["A.Gen", "A.Main", "B", "L.Core", "L.Elab", "L.Other"], [])

end Ix.Kernel.Audit.ImportControls
