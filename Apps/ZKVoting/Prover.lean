import Ix
import Apps.ZKVoting.ProverInit
import Apps.ZKVoting.Common

partial def collectVotes : IO $ List Vote :=
  gatherVotesLoop [] initSecret (0 : UInt64)
where
  gatherVotesLoop votes secret count := do
    let input := (← (← IO.getStdin).getLine).trim
    let voteAbe ← commitIO secret Candidate.abe
    let voteBam ← commitIO secret Candidate.bam
    let voteCot ← commitIO secret Candidate.cot
    IO.println s!"a: Abe | {voteAbe}"
    IO.println s!"b: Bam | {voteBam}"
    IO.println s!"b: Cot | {voteCot}"
    IO.println "_: End voting"
    let vote ← match input with
      | "a" => pure voteAbe | "b" => pure voteBam | "c" => pure voteCot
      | _ => return votes
    let secret' := (← commitIO secret count).adr
    IO.println vote
    gatherVotesLoop (vote :: votes) secret' (count + 1)

structure VoteCounts where
  abe : UInt64
  bam : UInt64
  cot : UInt64

def VoteCounts.new : VoteCounts :=
  ⟨0, 0, 0⟩

def countVotes (votes : List Vote) : VoteCounts :=
  votes.foldl (init := .new) fun counts vote =>
    match (reveal vote : Candidate) with
    | .abe => { counts with abe := counts.abe + 1 }
    | .bam => { counts with bam := counts.bam + 1 }
    | .cot => { counts with cot := counts.cot + 1 }

def main : IO UInt32 := do
  let votes ← collectVotes
  let claimAdr := ix_adr countVotes votes
  match ← prove claimAdr with
  | .ok proof => IO.FS.writeBinFile proofPath $ Ixon.Serialize.put proof; return 0
  | .error err => IO.eprintln $ toString err; return 1
