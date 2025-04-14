import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM

namespace ZKVoting

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


--def claim (argT: Type) (argVal: argT) : Ix.IxM Claim := do
--  let func <- Ix.IxM.byName `ZKVoting.runElection
--  let type <- Ix.IxM.byName `ZKVoting.Result
--  let argm <- Ix.IxM.byName `ZKVoting.privateVotes >>= Ix.IxM.commit
--  let main <- Ix.IxM.mkMain type func [argm]
--  let output <- Ix.IxM.evaluate type main
--  return Claim.mk main output type

--def addr : Ix.Comm Nat := Ix.Comm.mk (toString (Address.blake3 ⟨#[]⟩))
--def unAddr (a: Ix.Comm Nat) : String := a.value
--
--#eval Lean.toExpr [Candidate.alice]
-- .app (.app (.const `List.cons) (.const `.alice)) (.const `List.nil)
-- .app (.app (.const `List.cons) (.const `<comm-hash>)) (.const `List.nil)
-- ixon
-- def vote1 := .alice
-- .apps (.cnst <List.cons-hash>) [.cnst `<vote1-comm-hash>, .cnst <List.nil-hash>]
--def spliceComm : Lean.Expr

--def main : IO Proof := do
--  let env <- get_env!
--  let votes : List Candidate <- pure [.alice, .alice, .bob]
--  let args := [
--    (Lean.toExpr $ Ix.Compile.Comm.mk <$> votes, Lean.toTypeExpr (Ix.Compile.Comm Candidate))
--  ]
--  let func := `ZKVoting.runElection
--  let type := Lean.toTypeExpr ZKVoting.Result
--  let sort := Lean.Expr.sort (.succ .zero)
--  let output := Lean.toExpr (runElection votes)
--  let (claim, stt) <-
--    (Ix.Compile.evalClaimWithArgs func args output type sort [] true).runIO' env
--  --let 
--  return default
--
--end ZKVoting
