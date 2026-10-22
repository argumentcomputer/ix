import Ix.Check

/-! Native phase timings for the production LegacyIxVM compiler and Nat.add_comm.
Run `lake exe bench-aiur-compile [stages] [bytecode] [compile-only]`.
The default times the unmodified compiler. `stages` expands that same pipeline
to locate its costs. Parsing/elaboration happened when the executable was built;
module initialization (including LegacyIxVM merge/prune) precedes `main`.
-/

open LegacyAiur

@[noinline] private def timePure (label : String)
    (action : Unit → Except String α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← IO.ofExcept (action ())
  let elapsed := (← IO.monoNanosNow) - start
  IO.eprintln s!"Phase {label}: {elapsed / 1000}us"
  return result

@[noinline] private def timeIO (label : String) (action : IO α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  IO.eprintln s!"Phase {label}: {elapsed / 1000}us"
  return result

-- Keep the input as a function argument so Lean cannot lift compilation into
-- a closed value initialized before its timer.
@[noinline] private def compileTimed (t : Source.Toplevel) (stages : Bool) :
    IO CompiledToplevel := timeIO "compiler total" do
  unless stages do
    return ← timePure "compileWithGroups" fun _ =>
      t.compileWithGroups LegacyIxVM.functionGroups
  let t ← timePure "inline" fun _ => t.inlineCalls
  let typed ← timePure "check and simplify" fun _ =>
    t.checkAndSimplify.mapError toString
  let concrete ← timePure "concretize" fun _ =>
    typed.concretize.mapError toString
  let (raw, preNameMap) ← timePure "lower and layout" fun _ => concrete.toBytecode
  let (dedup, remap) ← timePure "deduplicate" fun _ => .ok raw.deduplicate
  let compiled ← timePure "finalize" fun _ => do
    let needs := dedup.needsCircuit
    let bytecode : Bytecode.Toplevel := { dedup with
      functions := dedup.functions.mapIdx fun i f =>
        { f with constrained := needs[i]! } }
    let nameMap := preNameMap.fold
      (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
      fun acc name idx => acc.insert name (remap idx)
    let reverseMap := nameMap.fold
      (init := (∅ : Std.HashMap Bytecode.FunIdx String))
      fun acc global idx => if acc.contains idx then acc
        else acc.insert idx (toString global)
    let bytecode := { bytecode with
      circuits := bytecode.singletonCircuits fun i =>
        reverseMap[i]?.getD s!"<fn {i}>" }
    return CompiledToplevel.mk t bytecode nameMap
  timePure "group functions" fun _ =>
    if functionGroupsDisabled then .ok compiled
    else compiled.groupFunctions LegacyIxVM.functionGroups

def main (args : List String) : IO Unit := do
  let start ← IO.monoNanosNow
  let toplevel ← IO.ofExcept (LegacyIxVM.ixVM.mapError toString)
  let compiled ← compileTimed toplevel (args.contains "stages")
  IO.println s!"Functions: {compiled.bytecode.functions.size}; function circuits: {compiled.bytecode.circuits.size}"
  unless args.contains "compile-only" do
    let env ← timeIO "load Lean environment" get_env!
    let ixonEnv ← timeIO "compile Nat.add_comm environment" <|
      LegacyIxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
    let addr ← LegacyIxVM.ClaimHarness.lookupAddr ixonEnv ``Nat.add_comm
    let handle ← timeIO "serialize and load Ixon environment" do
      let bytes ← IO.ofExcept (Ixon.serEnv ixonEnv)
      IO.ofExcept (EnvHandle.fromBytes bytes)
    let funIdx := compiled.getFuncIdx `verify_claim |>.get!
    let useBytecode := args.contains "bytecode"
    let (_, _, counts) ← timePure
        (if useBytecode then "bytecode check (including witness)"
          else "selected legacy runner (including witness)") fun _ =>
      compiled.bytecode.checkAddrWithEnv funIdx handle addr.hash useBytecode
    let shapes ← timePure "Rust system build and circuit shapes" fun _ =>
      .ok (circuitShapes compiled.bytecode defaultCommitmentParameters defaultFriParameters)
    let stats ← timePure "compute statistics" fun _ =>
      .ok (computeStats compiled counts shapes)
    printStats stats
  IO.eprintln s!"Phase main total: {((← IO.monoNanosNow) - start) / 1000}us"
