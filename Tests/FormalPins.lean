import Ix.Cli.FormalAggregate

/-! `formal-aiur-tests pins [ROOT]`: acceptance against the pinned verifying
keys and entry indices (`tools/formal-aiur.keys`), and, given the aggregate
root proof `ROOT` (an `IXAGGR2` proof file or store address; a direct IxVM
proof is refused), the identity blob.

- Keys other than the pinned ones are rejected before any proof is checked,
  and so are the pinned keys under entry indices other than the pinned ones
  (an artifact whose function table names another function of the pinned
  circuits).
- The root verifies under the identity blob built from the pins.
- It fails under every forged blob: either key digest or entry index
  changed. -/

namespace FormalPins
open Ix.Cli Ix.Cli.FormalAiur

/-- The pinned keys and entry indices of the selected programs are accepted;
other keys and other entry indices are rejected. Returns the aggregation
system and the pinned identity blob. -/
def checkAcceptance : IO (Ix.FormalProver.System × ByteArray) := do
  let registry ← Ix.FormalProver.Registry.new
  -- The packages `IX_AIUR_ARTIFACT` and `IX_AGGR_ARTIFACT` name, or the
  -- checkout's cached ones.
  let #[ixvmSelected, aggrSelected] ← selectAll default registry #[.ixvm, .aggregation]
    | throw (IO.userError "expected the IxVM and aggregation programs")
  let ixvmSystem ← ixvmSelected.system
  let aggrSystem ← aggrSelected.system
  let ixvm ← FormalAggregate.identity ixvmSystem false
  let aggr ← FormalAggregate.identity aggrSystem true
  let allowed ← FormalKeys.pinnedAllowed ixvm.key ixvm.index aggr.key aggr.index
  IO.println s!"pinned keys accepted: ixvm {FormalKeys.keyDigest ixvm.key} entry {ixvm.index}, \
    aggregation {FormalKeys.keyDigest aggr.key} entry {aggr.index}"
  for (label, ixvmKey, aggrKey) in
      [("the aggregation key as IxVM's", aggr.key, aggr.key),
       ("the IxVM key as aggregation's", ixvm.key, ixvm.key)] do
    match ← (FormalKeys.pinnedAllowed ixvmKey ixvm.index aggrKey aggr.index).toBaseIO with
    | .ok _ => throw (IO.userError s!"{label} was accepted")
    | .error e => IO.println s!"rejected {label}: {e}"
  for (label, ixvmIndex, aggrIndex) in
      [("another IxVM entry index", ixvm.index + 1, aggr.index),
       ("another aggregation entry index", ixvm.index, aggr.index + 1)] do
    match ← (FormalKeys.pinnedAllowed ixvm.key ixvmIndex aggr.key aggrIndex).toBaseIO with
    | .ok _ => throw (IO.userError s!"{label} was accepted")
    | .error e => IO.println s!"rejected {label}: {e}"
  return (aggrSystem, allowed)

/-- `ROOT` must be an aggregate root (`IXAGGR2`): the identity blob is what an
aggregate proof commits to. A direct IxVM proof (`IXAIUR2`, as `ix prove` without
`--aggregate` writes) commits to none; `ix verify` checks it against the pinned
key, and `formal-aiur-tests pins` without `ROOT` runs the acceptance checks. The
root is read before the acceptance checks, which derive both verifying keys. -/
def run (root : String) : IO Unit := do
  let wrapper ← readProofFileOrStore root
  let raw ← do
    try FormalAggregate.rawProof .aggr wrapper.proof
    catch e => throw (IO.userError s!"formal-aiur-tests pins ROOT takes an aggregate root proof \
      (IXAGGR2); {root}: {e}. For a direct IxVM proof run `formal-aiur-tests pins` without ROOT")
  let (aggrSystem, allowed) ← checkAcceptance
  let claim := Ix.Claim.ser wrapper.claim
  let verifies (blob : ByteArray) : IO Bool := do
    let input := (Aggr.pubInput blob claim).map (·.val)
    match ← (aggrSystem.verify "MultiStark::ix_aggr" input raw).toBaseIO with
    | .ok _ => pure true
    | .error _ => pure false
  unless ← verifies allowed do
    throw (IO.userError "the root does not verify under the pinned identity blob")
  IO.println "the root verifies under the pinned identity blob"
  for (label, offset) in [("IxVM key digest", 0), ("IxVM entry index", 32),
      ("aggregation key digest", 40), ("aggregation entry index", 72)] do
    let forged := allowed.set! offset (allowed.get! offset ^^^ 1)
    if ← verifies forged then
      throw (IO.userError s!"the root verifies under a forged {label}")
    IO.println s!"rejected under a forged {label}"

end FormalPins
