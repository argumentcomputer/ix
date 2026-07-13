import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.Benchmark.Bench

/-!
Shared harness for the hash-proving benchmarks (`bench-blake3`,
`bench-sha256` and `bench-keccak`).

Each benchmark case proves `numHashes` hashes of `dataSize` bytes in a single
Aiur proof and reports proving throughput in bytes/s. Before the timed runs,
the harness executes the largest workload once (execution only, no proving)
and prints the circuit statistics — per-circuit width, height and FFT cost,
plus the total circuit width — so width regressions show up in the benchmark
output.
-/

open BgroupM

namespace HashBench

/-- Sizes in bytes of each hashed message. The largest case proves 4 hashes
of 128 KiB — 512 KiB per proof — which sits on the sustained bytes/s plateau
(reached at ~128 KiB per proof) while keeping a full grid run fast enough to
iterate on. -/
def dataSizes : Array Nat := #[4096, 32768, 131072]

/-- Number of hashes proven in a single proof. -/
def numHashesPerProof : Array Nat := #[1, 4]

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

/-- Builds an `IOBuffer` with `numHashes` streams of `dataSize` bytes each.

The bytes are non-periodic pseudorandom (LCG), seeded per hash: a
`(i + idx) % 256` pattern repeats every 256 bytes, which memoizes repeated
sub-computations across blocks and understates honest proving cost. -/
def mkIOBuffer (dataSize numHashes : Nat) : Aiur.IOBuffer :=
  Array.range numHashes |>.foldl (init := default) fun ioBuffer idx =>
    let data := Array.range dataSize |>.map fun i =>
      Aiur.G.ofUInt8 (((i + idx * dataSize) * 1103515245 + 12345) >>> 16).toUInt8
    ioBuffer.extend 0 #[.ofNat idx] data

def run (groupName : String) (funcName : Lean.Name)
    (toplevel : Except Aiur.Global Aiur.Source.Toplevel) : IO (Array BenchReport) := do
  let .ok toplevel := toplevel
    | throw (IO.userError "Merging failed")
  let .ok compiled := toplevel.compile
    | throw (IO.userError "Compilation failed")
  let some funIdx := compiled.getFuncIdx funcName
    | throw (IO.userError "Aiur function not found")
  let maxDataSize := dataSizes.foldl Nat.max 0
  let maxNumHashes := numHashesPerProof.foldl Nat.max 0
  match compiled.bytecode.execute funIdx #[.ofNat maxNumHashes]
      (mkIOBuffer maxDataSize maxNumHashes) with
  | .error e => throw (IO.userError s!"Execution failed: {e}")
  | .ok (_, _, queryCounts) =>
    IO.println s!"Circuit statistics at dataSize={maxDataSize} numHashes={maxNumHashes}:"
    Aiur.printStats (Aiur.computeStats compiled queryCounts)
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters friParameters
  bgroup groupName { oneShot := true, avgThroughput := true, report := true } do
    for dataSize in dataSizes do
      for numHashes in numHashesPerProof do
        let ioBuffer := mkIOBuffer dataSize numHashes
        throughput (.ElementsAndBytes numHashes.toUInt64 (dataSize * numHashes).toUInt64 "hashes")
        bench s!"dataSize={dataSize} numHashes={numHashes}"
          (aiurSystem.prove funIdx #[Aiur.G.ofNat numHashes]) ioBuffer

end HashBench
