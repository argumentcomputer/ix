import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM

inductive Candidate
   | alice | bob | charlie
   deriving Inhabited, Lean.ToExpr, Repr

inductive Result
| winner : Candidate -> Result
| tie : List Candidate -> Result
deriving Repr, Lean.ToExpr

def privateVotes : List Candidate := 
  [.alice, .alice, .bob]

def runElection (votes: List Candidate) : Result :=
  let (a, b, c) := votes.foldr tally (0,0,0)
  if a > b && a > c
  then .winner .alice
  else if b > a && b > c
  then .winner .bob
  else if c > a && c > b
  then .winner .charlie
  else if a == b && b == c
  then .tie [.alice, .bob, .charlie]
  else if a == b
  then .tie [.alice, .bob]
  else if a == c
  then .tie [.alice, .charlie]
  else .tie [.bob, .charlie]
    where
      tally (comm: Candidate) (acc: (Nat × Nat × Nat)): (Nat × Nat × Nat) :=
      match comm, acc with
      | .alice, (a, b, c) => (a+1, b, c)
      | .bob, (a, b, c) => (a, b+1, c)
      | .charlie, (a, b, c) => (a, b, c+1)

open Ix.Compile

def main : IO UInt32 := do
  let mut stt : CompileState := .init (<- get_env!)
  -- simulate getting the votes from somewhere
  let votes : List Candidate <- pure [.alice, .alice, .bob]
  let mut as : List Lean.Name := []
  -- default maxHeartBeats
  let ticks : USize := 200000
  -- the type of each vote to commit
  let voteType := Lean.toTypeExpr Candidate
  -- loop over the votes
  for v in votes do
    -- add each vote to our environment as a commitment
    let (lvls, typ, val) <- runMeta (metaMakeDef v) stt.env
    let ((addr, _), stt') <- (commitDef lvls typ val).runIO' ticks stt
    stt := stt'
    as := (Address.toUniqueName addr)::as
    IO.println s!"vote: {repr v}, commitment: {addr}"
  -- build a Lean list of our commitments as the argument to runElection
  let arg : Lean.Expr <- runMeta (metaMakeList voteType as) stt.env
  let (lvls, input, output, type, sort) <-
    runMeta (metaMakeEvalClaim ``runElection [arg]) stt.env
  let inputPretty <- runMeta (Lean.Meta.ppExpr input) stt.env
  let outputPretty <- runMeta (Lean.Meta.ppExpr output) stt.env
  let typePretty <- runMeta (Lean.Meta.ppExpr type) stt.env
  IO.println s!"claim: {inputPretty}"
  IO.println s!"  ~> {outputPretty}"
  IO.println s!"  : {typePretty}"
  IO.println s!"  @ {repr lvls}"
  let ((claim,_,_,_), _stt') <-
     (evalClaim lvls input output type sort true).runIO' ticks stt
  IO.println s!"{claim}"
  -- Ix.prove claim stt
  return 0

