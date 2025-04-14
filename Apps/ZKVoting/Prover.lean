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

def main : IO UInt32 := do
  let mut stt : Ix.Compile.CompileState := .init (<- get_env!)
  -- simulate getting the votes from somewhere
  let votes : List Candidate <- pure [.alice, .alice, .bob]
  let mut as : List Lean.Name := []
  -- default maxHeartBeats
  let ticks : USize := 200000
  -- the type of each vote to commit
  let voteType := Lean.toTypeExpr Candidate
  -- loop over the votes
  for v in votes do
    let voteExpr := Lean.toExpr v
    -- add each vote to our environment as a commitment
    let ((addr, _), stt') <-
      (Ix.Compile.addCommitment [] voteType voteExpr).runIO' ticks stt
    stt := stt'
    -- collect each commitment addresses as names
    as := (Address.toUniqueName addr)::as
  IO.println s!"{repr as}"
  -- identify our function
  let func := ``runElection
  -- build a Lean list of our commitments as the argument to runElection
  let arg : Lean.Expr <- runMeta (metaMkList voteType as) stt.env
  let argType <- runMeta (Lean.Meta.inferType arg) stt.env
  -- inputs to commit to the type of the output
  let type := Lean.toTypeExpr Result
  let sort <- runMeta (Lean.Meta.inferType type) stt.env
  -- evaluate the output (both methods should be the same)
  let output := Lean.toExpr (runElection votes)
  IO.println s!"output1 {repr output}"
  let output' <- runMeta (Lean.Meta.reduce (.app (Lean.mkConst func) arg)) stt.env
  IO.println s!"output2 {repr output'}"
  -- build the evaluation claim
  let ((claim,_,_,_), _stt') <-
     (Ix.Compile.evalClaimWithArgs func [(arg, argType)] output type sort [] true).runIO' ticks stt
  IO.println s!"{claim}"
  -- Ix.prove claim stt
  return 0

