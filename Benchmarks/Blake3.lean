import Ix.IxVM.Core
import Ix.IxVM.ByteStream
import Ix.IxVM.Blake3
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Benchmark.Bench

open BgroupM

abbrev dataSizes := #[64, 128, 256, 512, 1024, 2048]
abbrev numHashesPerProof := #[1, 2, 4, 8, 16, 32]

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

def mergedToplevel : Except Aiur.Global Aiur.Toplevel := do
  let tl ← IxVM.core.merge IxVM.byteStream
  tl.merge IxVM.blake3

def blake3Bench : IO $ Array BenchReport := do
  let .ok toplevel := mergedToplevel
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx `blake3_bench
    | throw (IO.userError "Aiur function not found")
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  bgroup "prove blake3" { oneShot := true, avgThroughput := true, report := true } do
    for dataSize in dataSizes do
      for numHashes in numHashesPerProof do
        let ioBuffer := Array.range numHashes |>.foldl
          (init := default)
          fun ioBuffer idx =>
            let data := Array.range dataSize |>.map
              -- Add `idx` so every preimage is different and avoids memoization.
              fun i => Aiur.G.ofUInt8 (i + idx).toUInt8
            let ioKeyInfo := ⟨ioBuffer.data.size, dataSize⟩
            { ioBuffer with
                data := ioBuffer.data ++ data
                map := ioBuffer.map.insert #[.ofNat idx] ioKeyInfo }
        throughput (.ElementsAndBytes numHashes.toUInt64 (dataSize * numHashes).toUInt64 "hashes")
        bench s!"dataSize={dataSize} numHashes={numHashes}"
          (aiurSystem.prove friParameters funIdx #[Aiur.G.ofNat numHashes]) ioBuffer

def main (args : List String) : IO Unit := do
  setBenchArgs args
  let _ ← blake3Bench
  return
