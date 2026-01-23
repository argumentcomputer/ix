import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

abbrev dataSizes := #[64, 128, 256, 512, 1024, 2048, 4096, 8192]
abbrev numHashesPerProof := #[32, 64, 128, 256, 512]

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def blake3Bench : IO $ Array BenchReport := do
  let .ok ixVM := IxVM.ixVM
    | throw (IO.userError "IxVM merging failed")
  let some funIdx := ixVM.getFuncIdx `blake3_bench
    | throw (IO.userError "Aiur function not found")
  let .ok decls := ixVM.checkAndSimplify
    | throw (IO.userError "Simplification failed")
  let aiurSystem := Aiur.AiurSystem.build decls.compile commitmentParameters

  let mut benches := Array.emptyWithCapacity $ dataSizes.size * numHashesPerProof.size
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
      benches := benches.push <| bench s!"dataSize={dataSize} numHashes={numHashes}" (aiurSystem.prove friParameters funIdx #[Aiur.G.ofNat numHashes]) ioBuffer
  bgroup "prove blake3" benches.toList { oneShot := true }

def parseFunction (words : List String) (param : String): Option String :=
  words.find? (·.startsWith param) |> .map (·.stripPrefix param)

def main : IO Unit := do
  let result ← blake3Bench

  let mut sumWeights := 0.0
  let mut weightedSum := 0.0
  for report in result do
    let words := report.function.splitOn
    let dataSize := (parseFunction words "dataSize=").get!.toNat!
    let numHashes := (parseFunction words "numHashes=").get!.toNat!
    let sizeFloat := (dataSize * numHashes).toFloat
    let throughput := sizeFloat / (report.newBench.getTime.toSeconds )
    weightedSum := weightedSum + sizeFloat * throughput
    sumWeights := sumWeights + sizeFloat
  let avgThroughput := weightedSum / sumWeights
  println! "Average throughput: {avgThroughput.toUSize} bytes/s"
