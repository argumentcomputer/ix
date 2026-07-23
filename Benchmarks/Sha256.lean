import Ix.IxVM.Core
import Ix.IxVM.ByteStream
import Ix.IxVM.Sha256
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Benchmark.Bench

open BgroupM

abbrev dataSizes := #[64, 128, 256, 512, 1024, 2048]
abbrev numHashesPerProof := #[1, 2, 4, 8, 16, 32]

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 2
  capHeight := 0
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

def mergedToplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let tl ← IxVM.core.merge IxVM.byteStream
  tl.merge IxVM.sha256

def sha256Bench : IO $ Array BenchReport := do
  let .ok toplevel := mergedToplevel
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `sha256_bench
    | throw (IO.userError "Aiur function not found")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters
  bgroup "prove sha256" { oneShot := true, avgThroughput := true, report := true } do
    for dataSize in dataSizes do
      for numHashes in numHashesPerProof do
        let ioBuffer := Array.range numHashes |>.foldl
          (init := default)
          fun ioBuffer idx =>
            let data := Array.range dataSize |>.map
              -- Add `idx` so every preimage is different and avoids memoization.
              fun i => Aiur.G.ofUInt8 (i + idx).toUInt8
            ioBuffer.extend 0 #[.ofNat idx] data
        throughput (.ElementsAndBytes numHashes.toUInt64 (dataSize * numHashes).toUInt64 "hashes")
        bench s!"dataSize={dataSize} numHashes={numHashes}"
          (aiurSystem.prove funIdx #[Aiur.G.ofNat numHashes]) ioBuffer

def main : IO Unit := do
  let _ ← sha256Bench
  return
