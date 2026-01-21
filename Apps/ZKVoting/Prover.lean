import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileMOld
import Batteries

inductive Candidate
   | alice | bob | charlie
   deriving Inhabited, Lean.ToExpr, Repr, BEq, Ord

structure Result where
  aliceVotes: Nat
  bobVotes: Nat
  charlieVotes: Nat
deriving Repr, Lean.ToExpr

def privateVotes : List Candidate := 
  [.alice, .alice, .bob]

def runElection (votes: List Candidate) : Result :=
  votes.foldr tally ⟨0,0,0⟩
    where
      tally (comm: Candidate) (res: Result): Result :=
      match comm, res with
      | .alice, ⟨a, b, c⟩ => ⟨a+1, b, c⟩
      | .bob, ⟨a, b, c⟩ => ⟨a, b+1, c⟩
      | .charlie, ⟨a, b, c⟩ => ⟨a, b, c+1⟩

open Ix.Compile

def main : IO UInt32 := do
  let mut env : Lean.Environment := <- get_env!
  -- simulate getting the votes from somewhere
  let votes : List Candidate <- pure privateVotes
  let mut as : List Lean.Name := []
  -- the type of each vote to commit
  let voteType := Lean.toTypeExpr Candidate
  -- loop over the votes
  for v in votes do
    -- add each vote to our environment as a commitment
    let (lvls, typ, val) <- runMeta (metaMakeDef v) env
    let ((addr, _), stt) <- (commitDef lvls typ val).runIO env
    env := stt.env
    as := (Address.toUniqueName addr)::as
    IO.println s!"vote: {repr v}, commitment: {addr}"
  -- build a Lean list of our commitments as the argument to runElection
  let arg : Lean.Expr <- runMeta (metaMakeList voteType as) env
  let (lvls, input, output, type, sort) <-
    runMeta (metaMakeEvalClaim ``runElection [arg]) env
  let inputPretty <- runMeta (Lean.Meta.ppExpr input) env
  let outputPretty <- runMeta (Lean.Meta.ppExpr output) env
  let typePretty <- runMeta (Lean.Meta.ppExpr type) env
  IO.println s!"claim: {inputPretty}"
  IO.println s!"  ~> {outputPretty}"
  IO.println s!"  : {typePretty}"
  IO.println s!"  @ {repr lvls}"
  let ((claim,_,_,_), _stt') <- 
    (evalClaim lvls input output type sort true).runIO env
  IO.println s!"{claim}"
  -- Ix.prove claim stt
  return 0

