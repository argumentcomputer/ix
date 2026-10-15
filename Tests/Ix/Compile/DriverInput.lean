import LSpec
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver

/-! The compile drivers' input checks and keys: a condensation with a block
that has no reference set is refused by both drivers
(`Ix.CompileM.missingBlockRefs?`) instead of being scheduled as if it had no
dependencies; a block is named by its least member and an address by its
least alias (`canonicalKey`, `insertCanonicalAlias`), whatever the order.
A cross-SCC subset whose compile fails fails its block in both drivers,
recorded by name (`CompileEnv.ungrounded`), never dropped. -/

namespace Tests.Ix.Compile.DriverInput

open LSpec
open _root_.Ix (Name)

private def missing : Name := Name.fromLeanName `DriverInput.missing
private def present : Name := Name.fromLeanName `DriverInput.present

/-- Two singleton blocks; only `present` has a reference set. -/
private def blocks : _root_.Ix.CondensedBlocks :=
  { lowLinks := ({} : _root_.Ix.Map Name Name).insert missing missing |>.insert present present
    blocks := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name))
      |>.insert missing (({} : _root_.Ix.Set Name).insert missing)
      |>.insert present (({} : _root_.Ix.Set Name).insert present)
    blockRefs := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name)).insert present {} }

private def expected : String := "block DriverInput.missing has no condensation reference set"

/-- Three aliases at one address, in every insertion order. -/
private def aliases : List Name :=
  [`DriverInput.a, `DriverInput.b, `DriverInput.c].map Name.fromLeanName

private def permutations : List (List Name) := match aliases with
  | [a, b, c] => [[a, b, c], [a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]]
  | _ => []

private def least : Name := aliases.foldl (init := aliases.head!) fun k n =>
  if _root_.Ix.nameCompare n k == .lt then n else k

/-! ### A failed cross-SCC subset

The prerequisite pre-compile registers the block of the aux-gen seed `True`
(the inductive, with its constructor's projection) before the scheduler
runs. A further block holds the constructor `True.intro`, which that
pre-compile registered, and a constant whose compile fails (`bad`, whose value
is a constant the environment lacks): it takes the promotion path, and `bad`
is the unresolved subset, compiled on its own. Its failure fails the
promotion of the whole block in both drivers (`finishAuxPromotion`): both
members are recorded with it, by name, and neither is published; `True`'s
own block is unaffected. The condensation is crafted; on a real one the
subset is the unresolved remainder of a block whose key an earlier block
registered. -/

/-- `True`'s closure, canonicalized. -/
private def trueEnv (leanEnv : Lean.Environment) : _root_.Ix.Environment :=
  let consts := (_root_.Ix.EnvScope.collectDeps leanEnv [``True]).toArray
  { consts := (_root_.Ix.CanonM.canonChunk consts).foldl (fun m (n, c) => m.insert n c) {} }

/-- A definition whose value is a constant the environment lacks. -/
private def badConst (bad : Name) : _root_.Ix.ConstantInfo :=
  .defnInfo
    { cnst := { name := bad, levelParams := #[], type := _root_.Ix.Expr.mkSort _root_.Ix.Level.mkZero }
      value := _root_.Ix.Expr.mkConst (Name.fromLeanName `DriverInput.absent) #[]
      hints := .opaque, safety := .safe, all := #[bad] }

/-- `True`'s closure plus `bad`, and the condensation of the closure with
`True.intro` moved out of `True`'s block into the block `{True.intro, bad}`,
keyed by `True.intro` (`bad` is chosen to follow it, `Ix.nameCompare`). -/
private def crossInput (leanEnv : Lean.Environment) :
    Option (_root_.Ix.Environment × _root_.Ix.CondensedBlocks × Name × Name × Name) := do
  let env := trueEnv leanEnv
  let blocks := _root_.Ix.CondenseM.run (_root_.Ix.GraphM.envSerial env)
  let trueName := Name.fromLeanName ``True
  let resolved := Name.fromLeanName ``True.intro
  let rep ← blocks.lowLinks.get? trueName
  let members ← blocks.blocks.get? rep
  guard (members.contains resolved)
  let bad ← (List.range 64).map (fun i => Name.fromLeanName (.num `DriverInput.bad i))
    |>.find? fun b => _root_.Ix.nameCompare resolved b == .lt
  let env := { env with consts := env.consts.insert bad (badConst bad) }
  let blocks := { blocks with
    lowLinks := blocks.lowLinks.insert bad bad |>.insert resolved bad
    blocks := blocks.blocks.insert rep (members.erase resolved)
      |>.insert bad (({} : _root_.Ix.Set Name).insert resolved |>.insert bad)
    blockRefs := blocks.blockRefs.insert bad {} }
  return (env, blocks, trueName, resolved, bad)

/-- `none` when a driver's result records exactly `resolved` and `bad` as
failures, publishes neither, and publishes `owner`; otherwise what it did
instead. -/
private def crossVerdict (label : String) (owner resolved bad : Name)
    (result : Except String (Ixon.Env × Nat × _root_.Ix.CompileM.CompileEnv)) : Option String :=
  match result with
  | .error e => some s!"{label}: {e}"
  | .ok (ixe, _, cenv) =>
    let failed := (cenv.ungrounded.toArray.map (·.1.pretty)).qsort (· < ·) |>.toList
    let expected := (#[resolved.pretty, bad.pretty].qsort (· < ·)).toList
    if failed != expected then some s!"{label}: failures {failed}, expected {expected}"
    else if ixe.named.contains resolved || ixe.named.contains bad then
      some s!"{label}: a withdrawn member is published"
    else if !ixe.named.contains owner then some s!"{label}: {owner.pretty} is not published"
    else none

def suite : List TestSeq := [
  test "the reverse index keeps the least alias whatever the insertion order"
    (permutations.all fun order =>
      (order.foldl (init := ({} : Std.HashMap Address Name)) fun m n =>
        _root_.Ix.CompileM.insertCanonicalAlias m default n).get? default == some least),
  test "a block is keyed by its least member whatever the iteration order"
    (permutations.all fun order =>
      _root_.Ix.CompileM.canonicalKey Name.mkAnon order.toArray == least),
  test "missingBlockRefs? names the block without references"
    (_root_.Ix.CompileM.missingBlockRefs? blocks == some expected),
  test "missingBlockRefs? accepts a complete condensation"
    (_root_.Ix.CompileM.missingBlockRefs?
      { blocks with blockRefs := blocks.blockRefs.insert missing {} } == none),
  test "the sequential driver refuses a block without references"
    (show Bool from match _root_.Ix.CompileM.compileEnvAux { consts := {} } blocks with
      | .error why => why == expected
      | .ok _ => false),
  .individualIO "the parallel driver refuses a block without references" none (do
    let result ← _root_.Ix.CompileM.compileEnvParallelAux { consts := {} } blocks
      (numWorkers := 1)
    let ok := match result with
      | .error why => why == expected
      | .ok _ => false
    return (ok, if ok then 1 else 0, 1,

      if ok then none else some "the parallel driver did not refuse the condensation")) .done,
  .individualIO "a failed cross-SCC subset fails its block by name, in both drivers" none (do
    let leanEnv ← get_env!
    let some (env, blocks, owner, resolved, bad) := crossInput leanEnv
      | return (false, 0, 1, some "could not craft the cross-SCC input")
    let seq := crossVerdict "sequential driver" owner resolved bad
      (_root_.Ix.CompileM.compileEnvAux env blocks)
    let par := crossVerdict "wave driver" owner resolved bad
      (← _root_.Ix.CompileM.compileEnvParallelAux env blocks (numWorkers := 2))
    let errors := [seq, par].filterMap id
    let ok := errors.isEmpty
    return (ok, if ok then 1 else 0, 1, if ok then none else some (", ".intercalate errors))) .done]

end Tests.Ix.Compile.DriverInput
