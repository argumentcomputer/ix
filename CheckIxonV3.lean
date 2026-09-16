import Compilatrix.Ixon.V3

open Compilatrix.Ixon.V3

private def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    for _ in [:limit + 1] do
      let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then return bytes
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError "input file exceeds the byte budget")
    throw (IO.userError "input file exceeds the byte budget")

def main (args : List String) : IO UInt32 := do
  try
    let (envFile, profileFile, claimFile) ← match args with
      | [envFile, profileFile] => pure (envFile, profileFile, none)
      | [envFile, profileFile, claimFile] => pure (envFile, profileFile, some claimFile)
      | _ => throw (IO.userError "usage: check-ixon-v3 ENV.ixe PROFILE.bin [RESOURCE.claim]")
    let input ← IO.ofExcept (admitResources (← readBounded envFile (16 * 1024 * 1024))
      (← readBounded profileFile (1024 * 1024)))
    if let some path := claimFile then
      IO.ofExcept (input.checkClaimBinding (← readBounded path 68))
    IO.println s!"ixon-v3 resource-admitted: subject={input.env.root} profile={input.resolved.profileAddress} declarations={input.resolved.program.declarations.size}"
    IO.println "Erased typing and IxVM resource proofs are not checked by this command."
    return 0
  catch error =>
    IO.eprintln s!"ixon-v3 rejected: {error}"
    return 1
