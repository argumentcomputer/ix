module

public import Ix.Resource.Claim
public import Tests.Ix.ResourceAddressed
public import Tests.Ix.Claim

public section

namespace Tests.ClaimsV3

def fixtures : Array (String × Ix.Claim) :=
  let a := Address.blake3 "a".toUTF8
  let b := Address.blake3 "b".toUTF8
  let asm := some (Address.blake3 "asm".toUTF8)
  #[ ("eval", .eval a b asm), ("check", .check a none),
     ("check_env", .checkEnv a asm), ("reveal", .reveal a (.axio none none none)),
     ("contains", .contains a b), ("catalog", .catalog a b asm),
     ("resource", .resource a b) ]

def fixtureText : String := Id.run do
  let mut text := "# Ixon v3 claims: name, BLAKE3, canonical bytes\n"
  for (name, claim) in fixtures do
    text := text ++ s!"{name}\t{Ix.Claim.commit claim}\t{hexOfBytes (Ix.Claim.ser claim)}\n"
  return text

def run : IO Unit := do
  let expected ← IO.FS.readFile "Tests/Fixtures/ixon-v3/claims.tsv"
  unless expected == fixtureText do throw <| IO.userError "v3 claim fixture bytes differ"
  for (_, claim) in fixtures do
    let bytes := Ix.Claim.ser claim
    unless (Ix.Claim.de bytes).toOption == some claim do throw <| IO.userError "v3 claim roundtrip"
    for n in [:bytes.size] do
      unless (Ix.Claim.de (bytes.extract 0 n)).toOption.isNone do
        throw <| IO.userError "truncated v3 claim accepted"
    unless (Ix.Claim.de (bytes.push 0)).toOption.isNone do throw <| IO.userError "trailing v3 claim accepted"
    let header := if Ix.Claim.variantOf claim >= 8 then 2 else 1
    unless (Ix.Claim.de (bytes.set! header 2)).toOption.isNone do throw <| IO.userError "legacy claim version accepted"
    unless (Ix.Claim.de (bytes.set! (header + 1) 255)).toOption.isNone do throw <| IO.userError "wrong validator accepted"
    let proof : Ixon.Proof := { claim, proof := ⟨#[1, 2, 3]⟩ }
    let proofBytes := Ixon.Proof.ser proof
    let decoded ← IO.ofExcept (Ixon.Proof.de proofBytes)
    unless decoded.claim == claim && decoded.proof == proof.proof do throw <| IO.userError "v3 proof roundtrip"
    unless (Ixon.Proof.de (proofBytes.push 0)).toOption.isNone do throw <| IO.userError "trailing proof bytes accepted"
  let (base, unit) := Tests.ResourceAddressed.unitEnv
  let (env, _) := Tests.ResourceAddressed.store base (Tests.ResourceAddressed.identity unit)
  let profile : Ix.Resource.Profile := {}
  let claim ← IO.ofExcept (Ix.Resource.makeClaim env profile)
  let _ ← IO.ofExcept (Ix.Resource.checkClaim env profile claim)
  Tests.ResourceAddressed.check "resource claim rejects erased validator"
    (Ix.Resource.checkClaim env profile (.checkEnv env.merkleRoot.get! none)) false
  Tests.ResourceAddressed.check "resource claim binds the entire subject"
    (Ix.Resource.checkClaim base profile claim) false
  Tests.ResourceAddressed.check "resource claim binds limits"
    (Ix.Resource.checkClaim env { profile with limits := { steps := 100001 } } claim) false
  let result ← LSpec.lspecIO (.ofList [("v3 claims", Tests.Claim.suite)]) []
  unless result == 0 do throw <| IO.userError "existing claim tests failed"
  IO.println "V3 claims: fixtures, strict envelopes, proof wrappers, subjects, and profiles passed"

end Tests.ClaimsV3

end
