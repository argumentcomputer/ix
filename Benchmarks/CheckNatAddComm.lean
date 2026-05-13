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
  let some funIdx := compiled.getFuncIdx `kernel_check_test
    | throw (IO.userError "Aiur function not found")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  let env ← get_env!
  let ixonEnv ← IxVM.CheckHarness.loadIxonEnv ``Nat.add_comm env
  let ioBuffer := IxVM.CheckHarness.buildKernelCheckIOBuffer ixonEnv
  let targetAddrBytes := IxVM.CheckHarness.kernelCheckTarget ``Nat.add_comm ixonEnv
  -- check_deps=1 here: bench full transitive checking.
  let input := targetAddrBytes.push 1

  let _ ← bgroup "Kernel typechecking" { oneShot := true } do
    throughput (.Elements ixonEnv.consts.size.toUInt64 "consts")
    bench "check Nat.add_comm"
      (aiurSystem.prove friParameters funIdx input)
      ioBuffer
  return
