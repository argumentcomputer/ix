import Ix.Compile.ReadyQueue

/-! Native scale fixtures for publication across singleton dependency waves
and planning a block with many distinct parents. Fixture construction is
outside the measured interval. No wall-clock threshold is used: run doubling
sizes on the same native build to inspect growth.

The chain is `axiom p0 : Prop; def p1 : Prop := p0; ...`, represented directly
as source constants. The fan-in fixture exercises only dependency planning.
Arguments: `chain COUNT [WORKERS]` or `plan PARENTS`.
-/

namespace ReadyScale

open Ix.CompileM Ix.Compile.ReadyQueue

private def singleton (name : Ix.Name) : Ix.Set Ix.Name :=
  ({} : Ix.Set Ix.Name).insert name

private def names (count : Nat) : Array Ix.Name :=
  (Array.range count).map fun i => Ix.Name.mkStr Ix.Name.mkAnon s!"p{i}"

private def chain (count : Nat) : Ix.Environment × Ix.CondensedBlocks := Id.run do
  let keys := names count
  let mut source : Ix.Environment := { consts := {} }
  let mut blocks : Ix.CondensedBlocks := { lowLinks := {}, blocks := {}, blockRefs := {} }
  for i in [:count] do
    let name := keys[i]!
    let cnst : Ix.ConstantVal := { name, type := .mkSort .mkZero, levelParams := #[] }
    let declaration : Ix.ConstantInfo := if i == 0 then .axiomInfo { cnst, isUnsafe := false }
      else .defnInfo {
        cnst, value := .mkConst keys[i-1]! #[], safety := .safe
        all := #[name], hints := .abbrev }
    source := { source with consts := source.consts.insert name declaration }
    blocks := {
      lowLinks := blocks.lowLinks.insert name name
      blocks := blocks.blocks.insert name (singleton name)
      blockRefs := blocks.blockRefs.insert name (if i == 0 then {} else singleton keys[i-1]!) }
  return (source, blocks)

private def fanIn (count : Nat) : Ix.CondensedBlocks := Id.run do
  let keys := names (count + 1)
  let mut blocks : Ix.CondensedBlocks := { lowLinks := {}, blocks := {}, blockRefs := {} }
  let mut dependencies : Ix.Set Ix.Name := {}
  for i in [:count + 1] do
    let name := keys[i]!
    blocks := {
      lowLinks := blocks.lowLinks.insert name name
      blocks := blocks.blocks.insert name (singleton name)
      blockRefs := blocks.blockRefs.insert name {} }
    if i < count then dependencies := dependencies.insert name
  return { blocks with blockRefs := blocks.blockRefs.insert keys[count]! dependencies }

private def measureChain (count workers : Nat) : IO Unit := do
  let (source, blocks) ← IO.lazyPure fun _ => chain count
  let schedule ← IO.lazyPure fun _ => FoldSchedule.of blocks
  let initial := FoldState.init (CompileEnv.new source) blocks schedule
  let start ← IO.monoMsNow
  let (result, metrics) ← Ix.Compile.ReadyQueue.run { workers } blocks schedule
    foldWaveTasks false (count + 1) initial
  let elapsed := (← IO.monoMsNow) - start
  let final ← IO.ofExcept result.val
  unless final.acc.cenv.ungrounded.isEmpty && final.acc.cenv.nameToNamed.size == count &&
      final.waves == count && metrics.started == metrics.completed + metrics.drained do
    throw (IO.userError "chain did not publish every declaration and consume its workers")
  IO.println s!"chain count={count} workers={workers} ms={elapsed} reused={metrics.reused} fallbacks={metrics.fallbackRequests}"

private def measurePlan (count : Nat) : IO Unit := do
  let blocks ← IO.lazyPure fun _ => fanIn count
  let schedule ← IO.lazyPure fun _ => FoldSchedule.of blocks
  let initial := FoldState.init (CompileEnv.new { consts := {} }) blocks schedule
  let start ← IO.monoMsNow
  let plan ← IO.lazyPure fun _ => makePlan blocks schedule initial
  let elapsed := (← IO.monoMsNow) - start
  unless plan.descriptors.size == count + 1 &&
      plan.descriptors.any (fun descriptor => descriptor.parents.size == count) do
    throw (IO.userError "fan-in plan lost blocks or parents")
  IO.println s!"plan parents={count} ms={elapsed} descriptors={plan.descriptors.size}"

def run (args : List String) : IO UInt32 := do
  match args with
  | ["chain", count] => measureChain count.toNat! 4
  | ["chain", count, workers] => measureChain count.toNat! workers.toNat!
  | ["plan", count] => measurePlan count.toNat!
  | _ => throw (IO.userError "expected chain COUNT [WORKERS] or plan PARENTS")
  return 0

end ReadyScale

def main (args : List String) : IO UInt32 := ReadyScale.run args
