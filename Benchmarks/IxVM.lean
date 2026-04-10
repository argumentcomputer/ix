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

def main (args : List String) : IO Unit := do
  setBenchArgs args
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `ixon_serde_blake3_bench
    | throw (IO.userError "Aiur function not found")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters

  let env ← get_env!
  let natAddCommName := ``Nat.add_comm
  let constList := Lean.collectDependencies natAddCommName env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv
  let ixonConsts := ixonEnv.consts.valuesIter
  let (ioBuffer, n) := ixonConsts.fold (init := (default, 0)) fun (ioBuffer, i) c =>
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    (ioBuffer.extend #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)

  let _ ← bgroup "IxVM benchmarks" { oneShot := true } do
    throughput (.Elements n.toUInt64 "consts")
    bench "serde/blake3 Nat.add_comm"
      (aiurSystem.prove friParameters funIdx #[.ofNat n])
      ioBuffer
  return
