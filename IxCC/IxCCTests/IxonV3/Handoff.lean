import IxCC.Ixon.V3.Source
import IxCC.Tools.Check

namespace IxCCTests.IxonV3

open IxCC.Ixon IxCC.Ixon.V3

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError message)

def handoff (root : System.FilePath) : IO Nat := do
  let directory := root / "handoff"
  let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (directory / "manifest.json")))
  let string := fun (key : String) => IO.ofExcept (manifest.getObjValAs? String key)
  let files ← IO.ofExcept (manifest.getObjVal? "files")
  for name in #["accepted.ixe", "rejected-local-escape.ixe", "profile.bin", "accepted.claim"] do
    let expected ← IO.ofExcept (files.getObjValAs? String name)
    require ((Address.blake3 (← IO.FS.readBinFile (directory / name))).toHex == expected)
      s!"handoff fixture hash differs: {name}"
  let bytes ← IO.FS.readBinFile (directory / "accepted.ixe")
  let profile ← IO.FS.readBinFile (directory / "profile.bin")
  let claimBytes ← IO.FS.readBinFile (directory / "accepted.claim")
  let input ← IO.ofExcept (admitResources bytes profile)
  require (input.env.root.toHex == (← string "subject")) "handoff subject differs"
  require (input.resolved.profileAddress.toHex == (← string "profile")) "handoff profile differs"
  require (input.profile.bytes == profile) "profile did not reencode exactly"
  IO.ofExcept (input.checkClaimBinding claimBytes)
  let claim ← IO.ofExcept (ResourceClaim.decode claimBytes)
  require (claim.bytes == claimBytes) "resource claim did not reencode exactly"
  require ((Address.blake3 claimBytes).toHex == (← string "claim")) "claim digest differs"
  let rejected ← IO.FS.readBinFile (directory / "rejected-local-escape.ixe")
  let rejectedEnv ← IO.ofExcept (decodeAnonymousEnv rejected)
  require (rejectedEnv.root != input.env.root) "changed contract retained the old subject"
  let failure := admitResources rejected profile
  require (failure.toOption.isNone) "accepted local escape"
  match failure with
  | .error error => require ((error.splitOn "unrestrictedEscape").length > 1) s!"wrong local-escape rejection: {error}"
  | .ok _ => pure ()
  require ((input.checkClaimBinding { claim with subject := rejectedEnv.root }.bytes).toOption.isNone)
    "accepted wrong claim subject"
  require ((input.checkClaimBinding { claim with profile := input.env.root }.bytes).toOption.isNone)
    "accepted wrong claim profile"
  require ((decodeAnonymousEnv (bytes.set! 0 0xE3)).toOption.isNone) "accepted v3 environment"
  require ((decodeAnonymousEnv (bytes.set! 1 (bytes[1]! ^^^ 1))).toOption.isNone) "accepted corrupt root"
  require ((decodeAnonymousEnv bytes (bytes.size - 1)).toOption.isNone) "ignored environment byte budget"
  require ((decodeAnonymousEnv (bytes.set! 180 (bytes[180]! ^^^ 1))).toOption.isNone) "accepted corrupt object"
  let raised := { input.profile with limits := { depth := 256, steps := 500000 } }
  let raisedInput ← IO.ofExcept (admitResources bytes raised.bytes)
  require (raisedInput.env.root == input.env.root && raisedInput.profile.bytes == raised.bytes)
    "500k admission changed the source or profile"
  require (raisedInput.resolved.profileAddress == Address.blake3 raised.bytes &&
      raisedInput.resolved.profileAddress != input.resolved.profileAddress)
    "500k profile did not receive its own address"
  match raisedInput.checkClaimBinding claimBytes with
  | .error error =>
    require (error == "ixon-v3: claim profile mismatch")
      s!"wrong old-profile claim rejection: {error}"
  | .ok _ => throw (IO.userError "accepted the old claim under the 500k profile")
  match admitResources rejected raised.bytes with
  | .error error =>
    require ((error.splitOn "unrestrictedEscape").length > 1)
      s!"wrong 500k local-escape rejection: {error}"
  | .ok _ => throw (IO.userError "accepted local escape under the 500k profile")
  let excessiveLimits : Array (String × Resource.Limits) := #[
    ("original depth", { depth := 257, steps := 100000 }),
    ("raised depth", { depth := 257, steps := 500000 }),
    ("steps", { depth := 256, steps := 500001 })]
  for (label, limits) in excessiveLimits do
    let excessive := { input.profile with limits }
    match admitResources bytes excessive.bytes with
    | .error error =>
      require (error == "ixon-v3: profile exceeds consumer checker budget")
        s!"wrong consumer {label} budget rejection: {error}"
    | .ok _ => throw (IO.userError s!"ignored consumer {label} checker budget")
  let mut assertions := 25
  for count in [:(bytes.size - input.env.metadata.size)] do
    require ((decodeAnonymousEnv (bytes.extract 0 count)).toOption.isNone) "accepted truncated anonymous environment"
    assertions := assertions + 1
  for count in [:claimBytes.size] do
    require ((ResourceClaim.decode (claimBytes.extract 0 count)).toOption.isNone) "accepted truncated claim"
    assertions := assertions + 1
  for count in [:profile.size] do
    require ((Resource.Profile.ofBytes (profile.extract 0 count)).toOption.isNone) "accepted truncated profile"
    assertions := assertions + 1
  for bad in #[claimBytes.push 0, claimBytes.set! 2 2, claimBytes.set! 3 1, claimBytes.set! 0 0xF6] do
    require ((ResourceClaim.decode bad).toOption.isNone) "accepted malformed or differently scoped claim"
    assertions := assertions + 1
  require ((Resource.Profile.ofBytes (profile.push 0)).toOption.isNone) "accepted trailing profile byte"
  require ((Resource.Profile.ofBytes (profile.set! 0 0)).toOption.isNone) "accepted wrong profile domain"
  for line in (← IO.FS.readFile (root / "addressed.tsv")).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [name, address, encoded] := line.splitOn "\t"
      | throw (IO.userError "invalid addressed fixture row")
    let raw ← IO.ofExcept (IxCC.Tools.Check.unhex encoded)
    require ((Address.blake3 raw).toHex == address) s!"addressed fixture hash differs: {name}"
    if name == "profile" then
      let decoded ← IO.ofExcept (Resource.Profile.ofBytes raw)
      require (decoded.bytes == raw) "addressed profile differs"
    else
      let decoded ← IO.ofExcept (decodeConstant raw)
      require (constantBytes decoded.value == raw) s!"addressed constant differs: {name}"
    assertions := assertions + 2
  for line in (← IO.FS.readFile (root / "claims.tsv")).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [name, address, encoded] := line.splitOn "\t"
      | throw (IO.userError "invalid claim fixture row")
    let raw ← IO.ofExcept (IxCC.Tools.Check.unhex encoded)
    require ((Address.blake3 raw).toHex == address) s!"claim fixture hash differs: {name}"
    if name == "resource" then
      let decoded ← IO.ofExcept (ResourceClaim.decode raw)
      require (decoded.bytes == raw) "resource claim fixture differs"
    else
      require ((ResourceClaim.decode raw).toOption.isNone) s!"accepted non-resource claim {name}"
    assertions := assertions + 2
  return assertions + 2

end IxCCTests.IxonV3
