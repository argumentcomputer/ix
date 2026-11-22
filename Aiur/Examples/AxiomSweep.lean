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

/-- Tarjan SCC state for exact transitive axiom collection over cyclic
constant graphs (inductives + constructors, mutual definitions). Cache entries
are finalized ONLY when an entire SCC completes, so non-root SCC members are
never poisoned with `#[]`. -/
structure TarjanState where
  cache : Std.HashMap Name (Array Name) := {}
  nextIndex : Nat := 0
  index : Std.HashMap Name Nat := {}
  lowlink : Std.HashMap Name Nat := {}
  stack : Array Name := #[]
  onStack : Std.HashSet Name := {}
  localAxioms : Std.HashMap Name (Array Name) := {}

def mergeAxioms (acc src : Array Name) : Array Name :=
  src.foldl (init := acc) fun acc a => if acc.contains a then acc else acc.push a

/-- Compute transitive axioms for `c` over an abstract dependency graph using
Tarjan's SCC condensation so every member of a cycle shares the full SCC union. -/
partial def collectAxiomsSCC (directAxiom : Name → Option Name) (depsOf : Name → Array Name)
    (stRef : IO.Ref TarjanState) (c : Name) : IO (Array Name) := do
  if let some axioms := (← stRef.get).cache[c]? then
    return axioms
  dfs c
  return (← stRef.get).cache.getD c #[]
where
  dfs (v : Name) : IO Unit := do
    if (← stRef.get).cache.contains v then return
    let idx ← stRef.modifyGet fun st =>
      let idx := st.nextIndex
      (idx, { st with
        nextIndex := idx + 1
        index := st.index.insert v idx
        lowlink := st.lowlink.insert v idx
        stack := st.stack.push v
        onStack := st.onStack.insert v })
    let mut acc : Array Name := match directAxiom v with
      | some a => #[a]
      | none => #[]
    for w in depsOf v do
      let st ← stRef.get
      if let some cached := st.cache[w]? then
        acc := mergeAxioms acc cached
      else if !st.index.contains w then
        dfs w
        let st' ← stRef.get
        if let some cached := st'.cache[w]? then
          acc := mergeAxioms acc cached
        else
          let lowV := st'.lowlink.getD v idx
          let lowW := st'.lowlink.getD w idx
          if lowW < lowV then
            stRef.modify fun s => { s with lowlink := s.lowlink.insert v lowW }
      else if st.onStack.contains w then
        let lowV := st.lowlink.getD v idx
        let idxW := st.index.getD w idx
        if idxW < lowV then
          stRef.modify fun s => { s with lowlink := s.lowlink.insert v idxW }
    stRef.modify fun s => { s with localAxioms := s.localAxioms.insert v acc }
    let st ← stRef.get
    if st.lowlink.getD v idx == idx then
      -- `v` is the root of a completed SCC: pop every member and union all axioms.
      let mut members : Array Name := #[]
      let mut sccAxioms : Array Name := #[]
      let mut stack := st.stack
      let mut onStack := st.onStack
      let mut localAxioms := st.localAxioms
      while h : stack.size > 0 do
        let w := stack.back
        stack := stack.pop
        onStack := onStack.erase w
        members := members.push w
        if let some loc := localAxioms[w]? then
          sccAxioms := mergeAxioms sccAxioms loc
          localAxioms := localAxioms.erase w
        if w == v then break
      let mut cache := st.cache
      for w in members do
        cache := cache.insert w sccAxioms
      stRef.set { st with stack, onStack, localAxioms, cache }

def envDirectAxiom (env : Environment) (c : Name) : Option Name :=
  match env.find? c with
  | some (.axiomInfo _) => some c
  | _ => none

def envDepsOf (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some info =>
    let (exprs, more) : Array Expr × List Name := match info with
      | .axiomInfo v => (#[v.type], [])
      | .defnInfo v => (#[v.type, v.value], v.all)
      | .thmInfo v => (#[v.type, v.value], v.all)
      | .opaqueInfo v => (#[v.type, v.value], v.all)
      | .quotInfo v => (#[v.type], [])
      | .ctorInfo v => (#[v.type], [v.induct])
      | .recInfo v =>
        (#[v.type] ++ v.rules.toArray.map (·.rhs), v.all ++ v.rules.map (·.ctor))
      | .inductInfo v => (#[v.type], v.all ++ v.ctors)
    exprs.flatMap (·.getUsedConstants) ++ more.toArray

/-- The axioms `c` depends on, directly or transitively. Uses Tarjan SCC
condensation so cyclic constant graphs (inductives + constructors, mutual
definitions) propagate axioms to every member of the cycle without cache
poisoning. -/
def axiomsOf (env : Environment) (stRef : IO.Ref TarjanState) (c : Name) : IO (Array Name) :=
  collectAxiomsSCC (envDirectAxiom env) (envDepsOf env) stRef c

/-- Self-test for M19: entering an inductive `Evil` before its clean ctor
`Evil.good` and axiom-bearing ctor `Evil.bad` must propagate `badAxiom` to
`Evil.good` and its downstream callers without `#[]` cache poisoning. -/
def sccSelfTest : IO Unit := do
  let direct : Name → Option Name := fun n => if n == `badAxiom then some `badAxiom else none
  let deps : Name → Array Name := fun
    | `Evil => #[`Evil, `Evil.good, `Evil.bad]
    | `Evil.good => #[`Evil]
    | `Evil.bad => #[`badAxiom, `Evil]
    | `usesGood => #[`Evil.good]
    | _ => #[]
  let stRef ← IO.mkRef ({} : TarjanState)
  let evilAx ← collectAxiomsSCC direct deps stRef `Evil
  let goodAx ← collectAxiomsSCC direct deps stRef `Evil.good
  let callerAx ← collectAxiomsSCC direct deps stRef `usesGood
  unless evilAx == #[`badAxiom] && goodAx == #[`badAxiom] && callerAx == #[`badAxiom] do
    throw (IO.userError s!"SCC axiom sweep self-test failed: Evil={evilAx}, Evil.good={goodAx}, usesGood={callerAx}")

/-- Every declaration of a module under `Aiur` whose axioms leave the standard
three, with those extra axioms. -/
def offenders (env : Environment) : IO (Nat × Array (Name × Name × Array Name)) := do
  sccSelfTest
  let env := env.setExporting false
  let stRef ← IO.mkRef ({} : TarjanState)
  let moduleNames := env.allImportedModuleNames
  let mut scanned := 0
  let mut found := #[]
  for (name, _) in env.constants.map₁.toList do
    let some index := env.getModuleIdxFor? name | continue
    let module := moduleNames[index.toNat]!
    unless (`Aiur).isPrefixOf module do continue
    scanned := scanned + 1
    let extra := (← axiomsOf env stRef name).filter (!standardAxioms.contains ·)
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
