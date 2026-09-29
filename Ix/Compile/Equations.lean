/-
  Unfolding equations for compiled closures.

  Lean's code generator never compiles kernel recursion (`brecOn`, `WellFounded.fix`);
  it compiles an unchecked `_unsafe_rec` twin. A certified consumer instead compiles
  the right-hand side of the kernel-checked unfolding theorem `f.eq_def`, which states
  `f xs = body` with direct recursive calls. Lean realizes these theorems lazily, so a
  closure export must realize them before computing its dependency closure.
-/
module
public import Lean.Meta.Eqns
public import Ix.EnvScope

public section

namespace Ix.Compile.Equations

open Lean Meta

/-- A recursive definition and its realized unfolding theorem. -/
structure Association where
  definition : Lean.Name
  equation : Lean.Name
  deriving Inhabited, Repr, BEq

/-- Realize `f.eq_def` for every recursive definition among `names`: structural,
well-founded (including `WellFounded.Nat.fix` fuel encodings), mutual and
`partial_fixpoint` definitions. Non-recursive definitions produce nothing.
Definitions whose equation generation throws are returned with the message, so
a caller can report them instead of silently dropping them. -/
def realize (env : Lean.Environment) (names : List Lean.Name)
    : IO (Lean.Environment × Array Association × Array (Lean.Name × String)) := do
  let ctx : Core.Context := { fileName := "<ix-equations>", fileMap := default, maxHeartbeats := 0 }
  let action : MetaM (Array Association × Array (Lean.Name × String)) := do
    let mut found := #[]
    let mut failed := #[]
    for name in names do
      let some (.defnInfo _) := (← getEnv).find? name | continue
      try
        if let some equation ← getUnfoldEqnFor? name then
          found := found.push { definition := name, equation }
      catch error =>
        failed := failed.push (name, ← error.toMessageData.toString)
    return (found, failed)
  let ((found, failed), state) ← (action.run' {} {}).toIO ctx { env }
  return (state.env, found, failed)

/-- Close `seeds` over dependencies and over the unfolding theorems of every
recursive definition reached, until no new theorem appears. The equations' own
dependencies (matchers, and definitions their statements mention) join the
closure, and their recursive definitions are processed in turn. -/
partial def close (env : Lean.Environment) (seeds : List Lean.Name)
    : IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association × Array (Lean.Name × String)) :=
  loop env seeds {} #[] #[]
where
  loop (env : Lean.Environment) (seeds : List Lean.Name) (visited : Lean.NameSet)
      (found : Array Association) (failed : Array (Lean.Name × String)) :
      IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association × Array (Lean.Name × String)) := do
    let closed := Ix.EnvScope.collectDeps env seeds
    let pending := closed.filterMap fun (name, _) =>
      if visited.contains name then none else some name
    if pending.isEmpty then
      return (env, closed, found, failed)
    let (env, newFound, newFailed) ← realize env pending
    let visited := pending.foldl (·.insert ·) visited
    let equations := newFound.toList.map (·.equation)
    loop env (seeds ++ equations) visited (found ++ newFound) (failed ++ newFailed)

/-- The association records as JSON, sorted by definition name. -/
def toJson (found : Array Association) (failed : Array (Lean.Name × String)) : Lean.Json :=
  let found := found.qsort (fun a b => a.definition.toString < b.definition.toString)
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ix/compile-equations/1"),
    ("equations", Lean.Json.arr <| found.map fun a => Lean.Json.mkObj [
      ("definition", Lean.Json.str a.definition.toString),
      ("equation", Lean.Json.str a.equation.toString)]),
    ("failures", Lean.Json.arr <| failed.map fun (name, message) => Lean.Json.mkObj [
      ("definition", Lean.Json.str name.toString), ("message", Lean.Json.str message)])]

end Ix.Compile.Equations
