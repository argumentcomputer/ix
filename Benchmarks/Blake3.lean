import Ix.IxVM.ByteStream
import Ix.IxVM.Blake3
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol
import Ix.Benchmark.Bench

abbrev dataSizes := #[64, 128, 256, 512, 1024, 2048]
abbrev numHashesPerProof := #[1, 2, 4, 8, 16, 32]

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
  let .ok toplevel := IxVM.byteStream.merge IxVM.blake3
    | throw (IO.userError "Merging failed")
  let some funIdx := toplevel.getFuncIdx `blake3_bench
    | throw (IO.userError "Aiur function not found")
  let .ok decls := toplevel.checkAndSimplify
    | throw (IO.userError "Simplification failed")
  let .ok bytecode := decls.compile
    | throw (IO.userError "Compilation failed")
  let aiurSystem := Aiur.AiurSystem.build bytecode commitmentParameters

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
  words.find? (·.startsWith param) |> .map (·.dropPrefix param |>.toString)

def main : IO Unit := do
  let result ← blake3Bench
  let mut sumWeights := 0.0
  let mut weightedSum := 0.0
  for report in result do
    let words := report.function.splitOn
    let .some dataSizeStr := parseFunction words "dataSize="
      | throw $ IO.userError s!"Missing dataSize in: {report.function}"
    let .some dataSize := dataSizeStr.toNat?
      | throw $ IO.userError s!"Invalid dataSize: {dataSizeStr}"
    let .some numHashesStr := parseFunction words "numHashes="
      | throw $ IO.userError s!"Missing numHashes in: {report.function}"
    let .some numHashes := numHashesStr.toNat?
      | throw $ IO.userError s!"Invalid numHashes: {numHashesStr}"
    let sizeFloat := (dataSize * numHashes).toFloat
    let throughput := sizeFloat / (report.newBench.getTime.toSeconds )
    weightedSum := weightedSum + sizeFloat * throughput
    sumWeights := sumWeights + sizeFloat
  let avgThroughput := weightedSum / sumWeights
  println! "Average throughput: {avgThroughput.toUSize} bytes/s"
