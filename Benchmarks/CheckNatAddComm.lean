import Ix.Meta
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

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
  let some funIdx := toplevel.getFuncIdx `kernel_check_test
    | throw (IO.userError "Aiur function not found")
  let .ok decls := toplevel.checkAndSimplify
    | throw (IO.userError "Simplification failed")
  let .ok bytecode := decls.compile
    | throw (IO.userError "Compilation failed")
  let aiurSystem := Aiur.AiurSystem.build bytecode commitmentParameters

  let env ← get_env!
  let constList := Lean.collectDependencies ``Nat.add_comm env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv

  let mut ioBuffer : Aiur.IOBuffer := default

  -- Store ALL constants (including muts blocks) by Blake3 hash
  for (addr, c) in ixonEnv.consts do
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend key (bytes.data.map .ofUInt8)

  -- Store each blob:
  -- 1. Raw bytes under prefixed key [1] ++ blake3_hash (for on-demand verified loading)
  -- 2. Empty sentinel under plain blake3_hash (so io_get_info returns len=0, marking as blob)
  for (addr, rawBytes) in ixonEnv.blobs do
    let hashKey : Array Aiur.G := addr.hash.data.map .ofUInt8
    let prefixedKey : Array Aiur.G := #[1] ++ hashKey
    ioBuffer := ioBuffer.extend prefixedKey (rawBytes.data.map fun b => .ofNat b.toNat)
    ioBuffer := ioBuffer.extend hashKey #[]

  -- Get the blake3 address of Nat.add_comm as the target
  let targetAddr := match ixonEnv.getAddr? (Ix.Name.fromLeanName ``Nat.add_comm) with
    | some addr => addr
    | none => panic! "Nat.add_comm not found in Ixon environment"
  let targetAddrBytes : Array Aiur.G := targetAddr.hash.data.map .ofUInt8

  let _report ← oneShotBench "Kernel typechecking"
    (bench "check Nat.add_comm"
      (aiurSystem.prove friParameters funIdx targetAddrBytes)
      ioBuffer)
    { oneShot := true }
  return
