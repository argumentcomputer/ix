import Ix.Meta
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def main : IO Unit := do
  let .ok toplevel := IxVM.ixVM
    | throw (IO.userError "Merging failed")
  let some funIdx := toplevel.getFuncIdx `ixon_serde_blake3_bench
    | throw (IO.userError "Aiur function not found")
  let .ok decls := toplevel.checkAndSimplify
    | throw (IO.userError "Simplification failed")
  let .ok bytecode := decls.compile
    | throw (IO.userError "Compilation failed")
  let aiurSystem := Aiur.AiurSystem.build bytecode commitmentParameters

  let env ← get_env!
  let natAddCommName := ``Nat.add_comm
  let constList := Lean.collectDependencies natAddCommName env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv
  let ixonConsts := ixonEnv.consts.valuesIter
  let (ioBuffer, n) := ixonConsts.fold (init := (default, 0)) fun (ioBuffer, i) c =>
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    (ioBuffer.extend #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)

  let _report ← oneShotBench "IxVM benchmarks"
    (bench "serde/blake3 Nat.add_comm"
      (aiurSystem.prove friParameters funIdx #[.ofNat n])
      ioBuffer)
    { oneShot := true }
  return
