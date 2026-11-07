import Lean

/-!
# Axiom sweep over the Aiur package

`Aiur.Audit` freezes the statements and axioms of the headline theorems by
name. This sweep covers every declaration of the package: it imports every
module file under the package directory (`Aiur.lean` and `Aiur/**`, found by
walking the directory, so a new module is covered without editing anything)
and fails if any declaration depends, directly or transitively, on an axiom
other than `propext`, `Classical.choice` and `Quot.sound` — `sorryAx`, a custom
`axiom`, or `Lean.ofReduceBool` from `native_decide` alike.

Run it after `lake build aiur/Aiur`, which builds every module of the package:

```sh
lake build aiur/axiom_sweep
lake env Aiur/.lake/build/bin/axiom_sweep Aiur
```
-/

open Lean

namespace Aiur.AxiomSweep

/-- The axioms an Aiur declaration may depend on. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The module names of the `.lean` files of the package at `root`: `Aiur.lean`
and everything under `Aiur/`. -/
def packageModules (root : System.FilePath) : IO (Array Name) := do
  let mut modules := #[`Aiur]
  for file in ← (root / "Aiur").walkDir do
    if file.extension != some "lean" then continue
    let some relative := (file.withExtension "").toString.dropPrefix? (root.toString ++ "/")
      | throw (IO.userError s!"{file} is not under {root}")
    modules := modules.push <|
      (System.FilePath.mk relative.toString).components.foldl .str .anonymous
  return modules.qsort Name.lt

/-- The axioms `c` depends on, directly or transitively. One cache serves the
whole sweep, so every constant's closure is walked once. As in Lean's
`collectAxioms`, a constant in progress counts as axiom-free when a cycle
(an inductive type and its constructors) reaches it again. -/
partial def axiomsOf (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (c : Name) : IO (Array Name) := do
  if let some axioms := (← cache.get)[c]? then return axioms
  cache.modify (·.insert c #[])
  let some info := env.find? c | return #[]
  let (exprs, more) : Array Expr × List Name := match info with
    | .axiomInfo v => (#[v.type], [])
    | .defnInfo v => (#[v.type, v.value], [])
    | .thmInfo v => (#[v.type, v.value], [])
    | .opaqueInfo v => (#[v.type, v.value], [])
    | .quotInfo _ => (#[], [])
    | .ctorInfo v => (#[v.type], [])
    | .recInfo v => (#[v.type], [])
    | .inductInfo v => (#[v.type], v.ctors)
  let mut result : Array Name := if info matches .axiomInfo _ then #[c] else #[]
  for dependency in exprs.flatMap (·.getUsedConstants) ++ more.toArray do
    for a in ← axiomsOf env cache dependency do
      unless result.contains a do result := result.push a
  cache.modify (·.insert c result)
  return result

/-- Every declaration of a module under `Aiur` whose axioms leave the standard
three, with those extra axioms. -/
def offenders (env : Environment) : IO (Nat × Array (Name × Name × Array Name)) := do
  let env := env.setExporting false
  let cache ← IO.mkRef {}
  let moduleNames := env.allImportedModuleNames
  let mut scanned := 0
  let mut found := #[]
  for (name, _) in env.constants.map₁.toList do
    let some index := env.getModuleIdxFor? name | continue
    let module := moduleNames[index.toNat]!
    unless (`Aiur).isPrefixOf module do continue
    scanned := scanned + 1
    let extra := (← axiomsOf env cache name).filter (!standardAxioms.contains ·)
    unless extra.isEmpty do found := found.push (module, name, extra)
  return (scanned, found.qsort fun a b => Name.lt a.2.1 b.2.1)

end Aiur.AxiomSweep

open Aiur.AxiomSweep in
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "."
  unless ← (root / "Aiur.lean").pathExists do
    IO.eprintln s!"usage: axiom_sweep <Aiur package directory>; {root} has no Aiur.lean"
    return 2
  initSearchPath (← findSysroot)
  let modules ← packageModules root
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
  let (scanned, found) ← offenders env
  if found.isEmpty then
    IO.println s!"Aiur axiom sweep OK: {scanned} declarations in {modules.size} modules use only \
      {standardAxioms.toList}"
    return 0
  IO.eprintln s!"Aiur axiom sweep: {found.size} declaration(s) depend on non-standard axioms:"
  for (module, name, extra) in found do
    IO.eprintln s!"  {module} :: {name} uses {extra.toList}"
  return 1
