/-
  Unfolding equations for compiled closures (`ix compile --equations`).

  Lean's code generator never compiles kernel recursion (`brecOn`,
  `WellFounded.fix`); it compiles an unchecked `_unsafe_rec` twin. A consumer
  that compiles from the kernel-checked terms instead compiles the right-hand
  side of the unfolding theorem `f.eq_def`, which states `f xs = body` with
  direct recursive calls. Lean realizes these theorems on demand, so an export
  must realize them before it computes its closure: once realized, each
  theorem is in the environment and its dependencies (matchers, splitters, the
  definitions its statement mentions) join the selected closure.
-/
module
public import Lean.Meta.Eqns
public import Ix.EnvScope
-- The structural, well-founded and `partial_fixpoint` equation generators
-- register themselves with `Lean.Meta.getUnfoldEqnFor?` when this module's
-- initializers run; without them it finds no unfolding theorem.
import Lean.Elab.PreDefinition

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
`partial_fixpoint` definitions. Non-recursive definitions and constants that are
not definitions produce nothing. A definition whose equation generation throws
is returned with the message, so that a caller reports it instead of dropping
it. -/
def realize (env : Lean.Environment) (names : List Lean.Name) :
    IO (Lean.Environment × Array Association × Array (Lean.Name × String)) := do
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

/-- Close `seeds` as a selected input (`Ix.EnvScope.collectSelectedDeps`, the
closure `ix compile --consts` compiles) and over the unfolding theorems of every
recursive definition it reaches, until no new theorem appears. The theorems'
own dependencies join the closure, and the recursive definitions among them
are processed in turn. Returns the environment with the realized theorems, the
closed constant list, the associations and the failures, each definition
visited once. -/
partial def close (env : Lean.Environment) (seeds : List Lean.Name) :
    IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association ×
      Array (Lean.Name × String)) :=
  loop env seeds {} #[] #[]
where
  loop (env : Lean.Environment) (seeds : List Lean.Name) (visited : Lean.NameSet)
      (found : Array Association) (failed : Array (Lean.Name × String)) :
      IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association ×
        Array (Lean.Name × String)) := do
    let closed := Ix.EnvScope.collectSelectedDeps env seeds
    let pending := closed.filterMap fun (name, _) =>
      if visited.contains name then none else some name
    if pending.isEmpty then
      return (env, closed, found, failed)
    let (env, newFound, newFailed) ← realize env pending
    let visited := pending.foldl (·.insert ·) visited
    let equations := newFound.toList.map (·.equation)
    loop env (seeds ++ equations) visited (found ++ newFound) (failed ++ newFailed)

/-- The associations as JSON (`ix/compile-equations/1`): the format name, the
associations sorted by the definition's name, and the failures in the order
they were met. -/
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

end
