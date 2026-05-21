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
  let some funIdx := compiled.getFuncIdx `ixon_serde_blake3_bench
    | throw (IO.userError "Aiur function not found")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  let env ← get_env!
  let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
  let (ioBuffer, n) := IxVM.ClaimHarness.buildSerdeIOBuffer ixonEnv

  let _ ← bgroup "IxVM benchmarks" { oneShot := true } do
    throughput (.Elements n.toUInt64 "consts")
    bench "serde/blake3 Nat.add_comm"
      (aiurSystem.prove friParameters funIdx #[.ofNat n])
      ioBuffer
  return
