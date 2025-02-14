import Ix.Ixon.Serialize
import Ix.Prove
import Apps.ZKVoting.Common

def main (args : List String) : IO UInt32 := do
  let mut votes := #[]
  for commStr in args do
    match Commitment.ofString commStr with
    | none => IO.eprintln s!"Couldn't parse {commStr} as a commitment"; return 1
    | some (comm : Vote) => votes := votes.push comm
  let proofBytes ← IO.FS.readBinFile proofPath
  match Ixon.Serialize.get proofBytes with
  | .error err => IO.eprintln s!"Proof deserialization error: {err}"; return 1
  | .ok (_proof : Proof) =>
    -- TODO: print the resulting vote counts in the claim
    -- TODO: assert that every vote in `votes` is in the proof claim
    -- TODO: verify proof
    return 0
