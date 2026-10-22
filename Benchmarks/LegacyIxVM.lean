import Ix.Meta
import LegacyIxVM
import LegacyIxVM.Toplevel
import LegacyAiur.Protocol
import LegacyAiur.Compiler
import Ix.Benchmark.Bench

open BgroupM

def commitmentParameters : LegacyAiur.CommitmentParameters := {
  logBlowup := 2
  capHeight := 0
}

def friParameters : LegacyAiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

def main : IO Unit := do
  -- `ixon_serde_blake3_bench` is a bench-only entrypoint, present only in
  -- the FULL toplevel (production prunes it), so this prove goes through
  -- the generic interpreter — the codegen'd kernel mirrors the pruned
  -- toplevel and has no code (or index) for bench entries.
  let .ok toplevel := LegacyIxVM.ixVMFull
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `ixon_serde_blake3_bench
    | throw (IO.userError "LegacyAiur function not found")
  let aiurSystem := LegacyAiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters

  let env ← get_env!
  let ixonEnv ← LegacyIxVM.ClaimHarness.loadIxonEnv ``Nat.add_comm env
  let (ioBuffer, n) := LegacyIxVM.ClaimHarness.buildSerdeIOBuffer ixonEnv

  let _ ← bgroup "LegacyIxVM benchmarks" { oneShot := true } do
    throughput (.Elements n.toUInt64 "consts")
    bench "serde/blake3 Nat.add_comm"
      (aiurSystem.prove funIdx #[.ofNat n])
      ioBuffer
  return
