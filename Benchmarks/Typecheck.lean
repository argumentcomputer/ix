import Ix.Meta
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Benchmark.Bench

open BgroupM

/-! `lake exe bench-typecheck [<Module>] <Const>` STARK-proves
    `Ix.Claim.check name none`. `<Module>` defaults to `Init + Std`,
    auto-built via `lake build` if missing. Examples:

        lake exe bench-typecheck Nat.add_comm
        lake exe bench-typecheck Tests.Ix.Kernel.TutorialDefs basicDef
-/

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
  capHeight := 0
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def parseName (s : String) : Lean.Name :=
  s.splitOn "." |>.foldl (init := .anonymous) Lean.Name.mkStr

def main (args : List String) : IO UInt32 := do
  let (modules, nameArg) ← match args with
    | [n]    => pure (#[`Init, `Std], n)
    | [m, n] => pure (#[parseName m], n)
    | _      => IO.eprintln "usage: bench-typecheck [<Module>] <Const>"; return 1
  let name := parseName nameArg
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `verify_claim
    | throw (IO.userError "verify_claim entrypoint missing")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  let env ← try getCompileEnv modules catch _ => do
    modules.forM fun m => discard <| IO.Process.run { cmd := "lake", args := #["build", toString m] }
    getCompileEnv modules
  if !env.constants.contains name then IO.eprintln s!"{name} not found"; return 1
  let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv name env
  let target ← IxVM.ClaimHarness.lookupAddr ixonEnv name
  -- `assumptions = none` = full transitive typecheck.
  let witness ← IO.ofExcept <| IxVM.ClaimHarness.buildClaimWitness ixonEnv
    (Ix.Claim.check target none)
  let _ ← bgroup "Kernel typechecking" { oneShot := true } do
    throughput (.Elements ixonEnv.consts.size.toUInt64 "consts")
    bench s!"check {name}"
      (aiurSystem.prove friParameters funIdx witness.input)
      witness.inputIOBuffer
  return 0
