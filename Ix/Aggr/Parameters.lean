module
public import Ix.MultiStark.Wire

public section
namespace Aggr

/-- Commitment and FRI parameters for aggregation proofs. -/
structure RecursionParameters where
  commitment : Aiur.CommitmentParameters
  fri : Aiur.FriParameters

/-- Compatibility default for aggregate recursion proofs. -/
def defaultRecursionParameters : RecursionParameters := {
  commitment := Aiur.defaultCommitmentParameters
  fri := Aiur.defaultFriParameters
}

/-- Stable 40-byte serialization used as the `fri_params_ser` component of the
aggregate cache key: five `u64` little-endian fields in verifying-key
order. -/
def RecursionParameters.cacheFriBytes (parameters : RecursionParameters) : ByteArray :=
  let fri := parameters.fri
  ⟨MultiStark.u64le fri.logFinalPolyLen ++ MultiStark.u64le fri.maxLogArity ++
    MultiStark.u64le fri.numQueries ++ MultiStark.u64le fri.commitProofOfWorkBits ++
    MultiStark.u64le fri.queryProofOfWorkBits⟩

def defaultStructuralAbove : Nat := 0

def aggregateGiB : Nat := 1024 * 1024 * 1024

/-- Linux `MemTotal` parser kept separate so the 92% default has a pure seam. -/
def aggregateMemTotalBytes (contents : String) : Option Nat :=
  (contents.splitOn "\n").findSome? fun line =>
    if line.startsWith "MemTotal:" then
      ((line.splitOn " ").filter (· != "") |>.drop 1).head?.bind fun kib =>
        kib.toNat?.map (· * 1024)
    else none

def defaultAggregateRamBudgetBytes : IO Nat := do
  let contents ← try IO.FS.readFile "/proc/meminfo" catch _ => pure ""
  return match aggregateMemTotalBytes contents with
    | some total => total / 100 * 92
    | none => 16 * aggregateGiB

end Aggr
end
