module

public import Tests.Ix.RoleGeneration
public import Ix.RoleBinding.ArtifactTiered

namespace Tests.Ix.RolePacking

open Ixon
open _root_.Ix.RoleBinding.Artifact

@[extern "rs_test_pack_env_modes"]
private opaque packModes : @& ByteArray → @& ByteArray → IO (Array ByteArray)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def verify (source : Env) (root : Address) : IO Unit := do
  let limits := _root_.Ix.Resource.typingLimits
  let before ← IO.ofExcept ((prepareRecords source limits).mapError toString)
  let original := _root_.Ix.Kernel.Admission.streamContext Address.admissionHash
    before.prepared.table before.prepared.pre before.constants before.prepared.blobs before.prepared.hints.lookup
  let bytes ← IO.ofExcept (serEnv source)
  let packages ← packModes bytes root.hash
  ensure (packages.size == 3 && packages[0]? == packages[1]?) "full and streaming packages differ"
  for (bytes, mode) in packages.zipIdx do
    let packed ← IO.ofExcept (deEnv bytes)
    ensure (packed.main == some root && packed.roleBinding == source.roleBinding)
      "packing changed main or the actual binding"
    ensure (packed.consts.toList.all fun (a, c) => (source.consts[a]?).any (·.rawBytes == c.rawBytes))
      "packing changed carried constant bytes"
    if mode == 2 then
      ensure (packed.named.isEmpty && packed.names.size ≤ 1 &&
        packed.names.toList.all (fun (_, name) => match name with | .anonymous _ => true | _ => false) &&
        packed.comms.isEmpty)
        "anonymous packing retained names or commitments"
    let after ← IO.ofExcept ((prepareRecords packed limits).mapError toString)
    let context := _root_.Ix.Kernel.Admission.streamContext Address.admissionHash
      after.prepared.table after.prepared.pre after.constants after.prepared.blobs after.prepared.hints.lookup
    for (a, c) in after.constants do
      if let .muts ms := c.info then
        if ms.any (fun | .indc _ => true | _ => false) then
          let some old := original.index.blocks[a]? | throw (IO.userError "original recursor context missing")
          let some actual := context.index.blocks[a]? | throw (IO.userError "packed recursor context missing")
          ensure (old.order == actual.order && old.recs == actual.recs)
            "packing changed the actual reader's selected recursors"
    if after.hasTier then
      let receipt ← IO.ofExcept ((checkTiered packed limits).mapError toString)
      ensure (!receipt.logical.consts.isEmpty && receipt.prepared.records.length == packed.consts.size)
        "packed tier receipt did not cover the complete actual batch"
    else
      let receipt ← IO.ofExcept ((check packed limits).mapError toString)
      ensure (!receipt.target.consts.isEmpty && receipt.prepared.records.length == packed.consts.size)
        "packed logical receipt did not cover the complete actual batch"
    IO.println s!"bound pack mode {mode}: {source.consts.size} → {packed.consts.size} records; exact binding and actual consumer passed"

private def checks : IO Nat := do
  let (source, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some root := generated.table.addressOf? .natDiv | throw (IO.userError "fixture has no Nat.div")
  verify source root
  -- A missing binding stays a legacy transport possibility, never a bound
  -- certificate. No defaults are supplied to the actual consumer.
  ensure (!(check { source with roleBinding := none } _root_.Ix.Resource.typingLimits).isOk)
    "missing binding acquired a certified artifact result"
  -- A canonical wire table with a different specification version is still
  -- transportable. Packing success must not stand in for semantic admission.
  let wrongTable := { generated.table with version := generated.table.version + 1 }
  let wrongBytes := wrongTable.toBytes
  let wrong := { source with roleBinding := some ⟨Address.admissionHash wrongBytes, wrongBytes⟩ }
  let packages ← packModes (← IO.ofExcept (serEnv wrong)) root.hash
  ensure (packages.size == 3) "semantic-refusal control missed a pruner"
  for bytes in packages do
    let packed ← IO.ofExcept (deEnv bytes)
    ensure (packed.roleBinding == wrong.roleBinding) "packing normalized a wrong-version binding"
    ensure (match check packed _root_.Ix.Resource.typingLimits with
      | .error (.binding _) => true | _ => false) "wire-valid binding bypassed semantic admission"
  let some (proof, _) := generated.evidence[0]? | throw (IO.userError "fixture has no proof")
  ensure (source.consts.contains proof) "missing-proof control is vacuous"
  let missing := { source with consts := source.consts.erase proof }
  let rejected ← try
      let _ ← packModes (← IO.ofExcept (serEnv missing)) root.hash
      pure false
    catch e => pure (e.toString.contains "binding support: missing constant")
  ensure rejected "generated artifact's missing proof was not refused by packing"
  -- Optional preserved real-compiler capture for the full integration gate.
  if let some path ← IO.getEnv "IX_ROLE_PACK_CAPTURE" then
    let captured ← IO.ofExcept (deEnv (← IO.FS.readBinFile path))
    let name := _root_.Ix.Name.fromLeanName `artifactQuotient
    let some named := captured.named[name]? | throw (IO.userError "captured producer root is absent")
    verify captured named.addr
    return 6
  return 3

public def units : LSpec.TestSeq :=
  .individualIO "bound packing: all production pruners preserve actual reader/consumer support" none (do
    let count ← checks
    return (true, count, 0, none)) .done

end Tests.Ix.RolePacking
