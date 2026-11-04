import Ix.Cli.FormalAggregate

/-! `formal-aiur-tests pins ROOT`: acceptance against the pinned verifying
keys (`tools/formal-aiur.keys`), for the aggregate root proof `ROOT` (a
proof file or store address).

- Keys other than the pinned ones are rejected before any proof is checked.
- The root verifies under the identity blob built from the pins.
- It fails under every forged blob: either key digest or entry index
  changed. -/

namespace FormalPins
open Ix.Cli Ix.Cli.FormalAiur

def run (root : String) : IO Unit := do
  let registry ← Ix.FormalProver.Registry.new
  let #[ixvmSelected, aggrSelected] ← compiledPrograms registry
      #[ixvmProgram, aggregationProgram] (checkExecutors := false)
    | throw (IO.userError "expected the IxVM and aggregation programs")
  let ixvmSystem ← ixvmSelected.system
  let aggrSystem ← aggrSelected.system
  let ixvm ← FormalAggregate.identity ixvmSystem false
  let aggr ← FormalAggregate.identity aggrSystem true
  let allowed ← FormalKeys.pinnedAllowed ixvm.key ixvm.index aggr.key aggr.index
  IO.println s!"pinned keys accepted: ixvm {FormalKeys.keyDigest ixvm.key}, \
    aggregation {FormalKeys.keyDigest aggr.key}"
  for (label, ixvmKey, aggrKey) in
      [("the aggregation key as IxVM's", aggr.key, aggr.key),
       ("the IxVM key as aggregation's", ixvm.key, ixvm.key)] do
    match ← (FormalKeys.pinnedAllowed ixvmKey ixvm.index aggrKey aggr.index).toBaseIO with
    | .ok _ => throw (IO.userError s!"{label} was accepted")
    | .error e => IO.println s!"rejected {label}: {e}"
  let wrapper ← readProofFileOrStore root
  let raw ← FormalAggregate.rawProof .aggr wrapper.proof
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
