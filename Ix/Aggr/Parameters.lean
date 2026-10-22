module
public import LegacyMultiStark.Wire

public section
namespace Aggr

/-! ## Recursion proof parameters

LegacyIxVM proofs and aggregate recursion proofs deliberately have separate host
configuration, even while both configurations retain today's canonical values.
Keeping the recursion pair here gives aggregation and aggregate verification a
single construction path; a later policy change cannot silently update only one
side.
-/

/-- Commitment and FRI parameters for aggregation proofs. These parameters are
already bound by `AiurSystem.vkBytes`; this structure is host configuration, not
an additional circuit public input. -/
structure RecursionParameters where
  commitment : LegacyAiur.CommitmentParameters
  fri : LegacyAiur.FriParameters

/-- Compatibility default for aggregate recursion proofs. Policy changes (for
example, reducing the query count) must be explicit updates to this value and
must not change the canonical LegacyIxVM proof parameters. -/
def defaultRecursionParameters : RecursionParameters := {
  commitment := LegacyAiur.defaultCommitmentParameters
  fri := LegacyAiur.defaultFriParameters
}

/-- Stable 40-byte serialization used as the `fri_params_ser` component of the
aggregate cache key: five `u64` little-endian fields in verifying-key
order. Commitment parameters need no separate cache-key component because a
change to them changes the recursion-vk digest that the key also contains. -/
def RecursionParameters.cacheFriBytes (parameters : RecursionParameters) : ByteArray :=
  let fri := parameters.fri
  ⟨LegacyMultiStark.u64le fri.logFinalPolyLen ++ LegacyMultiStark.u64le fri.maxLogArity ++
    LegacyMultiStark.u64le fri.numQueries ++ LegacyMultiStark.u64le fri.commitProofOfWorkBits ++
    LegacyMultiStark.u64le fri.queryProofOfWorkBits⟩

/-- Build a recursion proving/verifying system through the shared aggregate
parameter path. Both `AggregateCmd` and `VerifyCmd` use this helper. -/
def buildRecursionSystem (bytecode : LegacyAiur.Bytecode.Toplevel)
    (parameters : RecursionParameters) : LegacyAiur.AiurSystem :=
  LegacyAiur.AiurSystem.build bytecode parameters.commitment parameters.fri


def defaultStructuralAbove : Nat := 4096

def aggregateGiB : Nat := 1024 * 1024 * 1024

/-- Linux `MemTotal` parser kept separate so the 92% default has a pure seam.
The fallback only affects non-Linux hosts; admit-when-alone still guarantees
progress without pretending the fallback is a calibrated capacity. -/
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
