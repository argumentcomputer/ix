import Ix.Meta
import Ix.IxVM
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Benchmark.Bench

open BgroupM

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

def main : IO Unit := do
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `verify_claim
    | throw (IO.userError "verify_claim entrypoint missing")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  let env ← get_env!
  let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
  let target ← IxVM.ClaimHarness.lookupAddr ixonEnv ``Nat.add_comm
  -- `assumptions = none` = full transitive typecheck.
  let witness ← IO.ofExcept <| IxVM.ClaimHarness.buildClaimWitness ixonEnv
    (Ix.Claim.check target none)

  let _ ← bgroup "Kernel typechecking" { oneShot := true } do
    throughput (.Elements ixonEnv.consts.size.toUInt64 "consts")
    bench "check Nat.add_comm"
      (aiurSystem.prove friParameters funIdx witness.input)
      witness.inputIOBuffer
  return
