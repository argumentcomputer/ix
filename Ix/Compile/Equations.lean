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
public import Ix.Compile.SourceContract.Registry

public section

namespace Ix.Compile.Equations

open Lean Meta

/-- A header input contract of a definition, carried onto the same position of
its unfolding equation's statement (R1 amendment). -/
structure CarriedContract where
  position : Nat
  binder : Lean.Name
  uses : Ixon.Uses
  value : Ixon.ValueContract
  deriving Inhabited, Repr, BEq

/-- A recursive definition and its realized unfolding theorem. -/
structure Association where
  definition : Lean.Name
  equation : Lean.Name
  /-- The definition's header input contracts that the equation's statement
  carries, by telescope position. -/
  contracts : Array CarriedContract := #[]
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

/-- The non-default input contracts of a declaration's type telescope, from its
registered or marked source contract. -/
def headerContracts (env : Lean.Environment) (info : Lean.ConstantInfo) :
    Except Ix.Compile.SourceContractError (Array CarriedContract) := do
  let input ← Ix.Compile.compileInputFromEnv env [(info.name, info)]
  let some contract := input.contracts[0]? | return #[]
  let resolved ← contract.resolve info
  let types := Ix.Compile.sourceTelescope info .type
  let mut carried := #[]
  for i in [:types.size] do
    let (site, binder) := types[i]!
    if let some b := resolved.binders.find? (·.site == site) then
      if b.uses != .many || b.value != .shared then
        carried := carried.push { position := i, binder, uses := b.uses, value := b.value }
  return carried

/-- Carry each definition's header input contracts onto its unfolding
equation (R1 amendment): the statement's binder at the same telescope position,
and the matching lambda of the proof, are registered with the same input
contract, so that transport writes them into the exported theorem. Result
contracts are not carried: the statement's arrows end in an equality, not in
the definition's result. Contracts written inside the body already reach the
statement. An equation whose telescope does not match is left unchanged and
reported. -/
def carryContracts (env : Lean.Environment) (found : Array Association) :
    Lean.Environment × Array Association × Array (Lean.Name × String) := Id.run do
  let mut env := env
  let mut result := #[]
  let mut failed := #[]
  for a in found do
    let (some definition, some equation) := (env.find? a.definition, env.find? a.equation)
      | result := result.push a
        continue
    match headerContracts env definition with
    | .error error =>
      failed := failed.push (a.definition, s!"contracts not carried: {error}")
      result := result.push a
    | .ok carried =>
      if carried.isEmpty then
        result := result.push a
        continue
      let requests := carried.map fun c =>
        ({ binder := .position c.position, uses := c.uses, value := c.value } : Ix.Compile.TelescopeContract)
      let registered : Except Ix.Compile.SourceContractError Lean.Environment := do
        let header ← Ix.Compile.SourceContract.ofTelescope equation requests
        let existing ← if Ix.Compile.sourceHasAnnotations equation then
            pure (← Ix.Compile.SourceContract.fromAnnotations equation).binders
          else pure #[]
        let binders := existing ++ header.binders.filter fun b => !existing.any (·.site == b.site)
        Ix.Compile.registerSourceContract env { source := equation, binders }
      match registered with
      | .ok next =>
        env := next
        result := result.push { a with contracts := carried }
      | .error error =>
        failed := failed.push (a.definition, s!"contracts not carried: {error}")
        result := result.push a
  return (env, result, failed)

private def usesName : Ixon.Uses → String
  | .erased => "erased" | .linear => "linear" | .affine => "affine" | .many => "many"

/-- The association records as JSON, sorted by definition name. -/
def toJson (found : Array Association) (failed : Array (Lean.Name × String)) : Lean.Json :=
  let found := found.qsort (fun a b => a.definition.toString < b.definition.toString)
  let contract (c : CarriedContract) := Lean.Json.mkObj [
    ("position", Lean.toJson c.position), ("binder", Lean.Json.str c.binder.toString),
    ("uses", Lean.Json.str (usesName c.uses)),
    ("owned", Lean.Json.str (if c.value.owned == .unique then "unique" else "shared")),
    ("locality", Lean.Json.str (if c.value.locality == .local then "local" else "unrestricted"))]
  Lean.Json.mkObj [
    ("format", Lean.Json.str "ix/compile-equations/1"),
    ("equations", Lean.Json.arr <| found.map fun a => Lean.Json.mkObj <| [
      ("definition", Lean.Json.str a.definition.toString),
      ("equation", Lean.Json.str a.equation.toString)] ++
      (if a.contracts.isEmpty then [] else [("contracts", Lean.Json.arr (a.contracts.map contract))])),
    ("failures", Lean.Json.arr <| failed.map fun (name, message) => Lean.Json.mkObj [
      ("definition", Lean.Json.str name.toString), ("message", Lean.Json.str message)])]

end Ix.Compile.Equations
