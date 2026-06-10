import Ix.Claim

/-- NOT IMPLEMENTED. A verifier stub that exits 0 unconditionally is worse
    than none at all — anything scripted against it silently treats every
    proof as valid — so it fails loudly until real verification (parse
    commitments, deserialize the proof, check every vote is in the claim,
    run the STARK verifier) lands. -/
def main (_args : List String) : IO UInt32 := do
--  TODO
--  let mut votes := #[]
--  for commStr in args do
--    match Commitment.ofString commStr with
--    | none => IO.eprintln s!"Couldn't parse {commStr} as a commitment"; return 1
--    | some (comm : Vote) => votes := votes.push comm
--  let proofBytes ← IO.FS.readBinFile proofPath
--  match Ixon.Serialize.get proofBytes with
--  | .error err => IO.eprintln s!"Proof deserialization error: {err}"; return 1
--  | .ok (_proof : Proof) =>
--    -- TODO: print the resulting vote counts in the claim
--    -- TODO: assert that every vote in `votes` is in the proof claim
--    -- TODO: verify proof
    IO.eprintln "error: ZKVoting verifier is not implemented; refusing to report success"
    return 1
