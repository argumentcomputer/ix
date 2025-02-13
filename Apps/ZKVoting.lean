import Ix

inductive Candidate
  | abe | bam | cot
  deriving Inhabited

def initSecret : Address :=
  ⟨⟨#[42, 101, 255]⟩⟩

abbrev Vote := Commitment Candidate

partial def gatherVotes : IO $ List Vote := do
  IO.println "a: Abe\nb: Bam\nc: Cot\n_: End voting"
  gatherVotesLoop ([] : List Vote) initSecret
where
  gatherVotesLoop votes secret := do
    let input := (← (← IO.getStdin).getLine).trim
    let candidate ← match input with
      | "a" => pure .abe | "b" => pure .bam | "c" => pure .cot
      | _ => return votes
    let vote := commit secret candidate
    let secret' := commit secret secret |>.adr
    -- TODO: commitments should be properly formatted
    IO.println vote.adr.adr
    gatherVotesLoop (vote :: votes) secret'

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

#ix hash countVotes as countVotesAdr
#ix hash VoteCounts as VoteCountsAdr

def main : IO UInt32 := do
  let _votes ← gatherVotes
  let votesExpr := sorry -- How to get it from `votes`?
  let _claimConst := Ixon.Const.defn {
    lvls := 0,
    type := .cnst VoteCountsAdr [],
    value := .apps (.cnst countVotesAdr []) [votesExpr], -- `countVotes votes`
    part := false,
  }
  let claimAdr := default -- Get from hashing the bytes of `claimConst`
  match ← proveM claimAdr with
  | .ok _proof => -- `proof` would be published online
    -- TODO: print claim and verify proof
    return 0
  | .error err => IO.eprintln $ toString err; return 1
