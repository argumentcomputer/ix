import Ix
import Apps.ZKVoting.ProverInit
import Apps.ZKVoting.Common

open Lean

partial def collectVotes (env : Environment) : IO $ List Vote :=
  collectVotesLoop [] initSecret (0 : UInt64)
where
  collectVotesLoop votes secret count := do
    let input := (← (← IO.getStdin).getLine).trim
    let consts := env.constants
    let voteAbe ← mkCommit secret Candidate.abe consts
    let voteBam ← mkCommit secret Candidate.bam consts
    let voteCot ← mkCommit secret Candidate.cot consts
    IO.println s!"a: Abe | {voteAbe}"
    IO.println s!"b: Bam | {voteBam}"
    IO.println s!"b: Cot | {voteCot}"
    IO.println "_: End voting"
    let vote ← match input with
      | "a" => pure voteAbe | "b" => pure voteBam | "c" => pure voteCot
      | _ => return votes
    let secret' := (← mkCommit secret count consts).adr
    IO.println vote
    collectVotesLoop (vote :: votes) secret' (count + 1)

structure VoteCounts where
  abe : UInt64
  bam : UInt64
  cot : UInt64
  deriving ToExpr

def countVotes : List Vote → VoteCounts
  | [] => ⟨0, 0, 0⟩
  | vote :: votes =>
    let counts := countVotes votes
    match (reveal vote : Candidate) with
    | .abe => { counts with abe := counts.abe + 1 }
    | .bam => { counts with bam := counts.bam + 1 }
    | .cot => { counts with cot := counts.cot + 1 }

def main : IO UInt32 := do
  let env ← get_env!
  let votes ← collectVotes env
  let .defnInfo countVotesDefn ← runCore (getConstInfo ``countVotes) env
    | unreachable!
  let claimValue := .app countVotesDefn.value (toExpr votes)
  let claimType ← runMeta (Meta.inferType claimValue) env
  let claimAdr := computeIxAddress (mkAnonDefInfoRaw claimType claimValue) env.constants
  match ← prove claimAdr with
  | .ok proof => IO.FS.writeBinFile proofPath $ Ixon.Serialize.put proof; return 0
  | .error err => IO.eprintln $ toString err; return 1
