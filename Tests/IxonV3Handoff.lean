module

public import Tests.Ix.ResourceAddressed
public import Ix.Resource.Claim

public section

namespace Tests.IxonV3Handoff

/-- A complete anonymous environment and its native resource admission claim.
The rejected fixture differs only in the escaping result contract. -/
def artifacts : Except String (Array (String × ByteArray)) := do
  let (base, unit) := Tests.ResourceAddressed.unitEnv
  let (accepted, _) := Tests.ResourceAddressed.store base
    (Tests.ResourceAddressed.identity unit)
  let (rejected, _) := Tests.ResourceAddressed.store base
    (Tests.ResourceAddressed.identity unit Tests.ResourceAddressed.linearLocal .shared)
  let profile : Ix.Resource.Profile := {}
  let claim ← Ix.Resource.makeClaim accepted profile
  if (Ix.Resource.validate rejected profile).toOption.isSome then
    throw "handoff: local escape fixture must be rejected"
  let profileAddress ← profile.address
  let files := #[
    ("accepted.ixe", ← Ixon.serEnv accepted),
    ("rejected-local-escape.ixe", ← Ixon.serEnv rejected),
    ("profile.bin", profile.bytes),
    ("accepted.claim", Ix.Claim.ser claim) ]
  let manifest := Lean.Json.mkObj [
    ("schema", .str "ixon-v3-handoff-1"),
    ("objectFormat", .str "ixon-v3"),
    ("validator", .str Ix.Resource.validatorId),
    ("subject", .str (toString accepted.merkleRoot.get!)),
    ("profile", .str (toString profileAddress)),
    ("claim", .str (toString (Ix.Claim.commit claim))),
    ("files", Lean.Json.mkObj (files.toList.map fun (name, bytes) =>
      (name, .str (toString (Address.blake3 bytes))))),
    ("ixvmResourceProof", .bool false) ]
  return files.push ("manifest.json", (manifest.pretty ++ "\n").toUTF8)

def writeArtifacts (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name, bytes) in ← IO.ofExcept artifacts do
    IO.FS.writeBinFile (directory / name) bytes

def check (directory : System.FilePath) : IO Unit := do
  for (name, bytes) in ← IO.ofExcept artifacts do
    unless (← IO.FS.readBinFile (directory / name)) == bytes do
      throw <| IO.userError s!"handoff fixture differs: {name}"

end Tests.IxonV3Handoff

end
