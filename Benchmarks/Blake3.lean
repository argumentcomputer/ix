import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol

abbrev dataSizes := #[64, 128, 256, 512, 1024, 2048]
abbrev numHashesPerProof := #[1, 2, 4, 8, 16, 32]

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  proofOfWorkBits := 20
}

def runBenches (aiurSystem : Aiur.AiurSystem) (funIdx : Nat) :
    IO $ Array (Nat × Float) := do
  let mut results := Array.emptyWithCapacity $ dataSizes.size * numHashesPerProof.size
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
      IO.print s!"Proving for dataSize={dataSize}, numHashes={numHashes} "
      let startMs ← IO.monoMsNow
      let (claim, proof, _) := aiurSystem.prove friParameters funIdx
        #[Aiur.G.ofNat numHashes] ioBuffer
      let finishedMs ← IO.monoMsNow
      let elapsedMs := finishedMs - startMs
      let elapsed := elapsedMs.toFloat / 1000.0
      IO.print s!"{elapsed}s "
      let verified := aiurSystem.verify friParameters claim proof |>.isOk
      if verified then println! "✓" else println! "✕"
      results := results.push (dataSize * numHashes, elapsed)
  pure results

def main (_args : List String) : IO Unit := do
  let some funIdx := ixVM.getFuncIdx `blake3_bench
    | println! "Aiur function not found"; return
  let .ok decls := ixVM.checkAndSimplify
    | println! "Simplification failed"; return
  let aiurSystem := Aiur.AiurSystem.build decls.compile commitmentParameters
  let results ← runBenches aiurSystem funIdx

  let mut sumWeights := 0.0
  let mut weightedSum := 0.0
  for (size, time) in results do
    let sizeFloat := size.toFloat
    let throughput := sizeFloat / time
    weightedSum := weightedSum + sizeFloat * throughput
    sumWeights := sumWeights + sizeFloat
  let avgThroughput := weightedSum / sumWeights
  println! s!"Average throughput: {avgThroughput.toUSize} bytes/s"
