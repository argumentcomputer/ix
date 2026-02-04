import Ix.Claim
import Ix.Commit
import Ix.Address
import Ix.Meta
import Ix.CompileM
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

def main : IO UInt32 := do
  let mut env : Lean.Environment ← get_env!

  -- 1. Full compilation via Rust
  let phases ← Ix.CompileM.rsCompilePhases env
  let mut compileEnv := Ix.Commit.mkCompileEnv phases

  -- simulate getting the votes from somewhere
  let votes : List Candidate ← pure privateVotes
  let mut as : List Lean.Name := []
  -- the type of each vote to commit
  let voteType := Lean.toTypeExpr Candidate
  -- loop over the votes
  for v in votes do
    -- add each vote to our environment as a commitment
    let (lvls, typ, val) ← runMeta (metaMakeDef v) env
    let (commitAddr, env', compileEnv') ← Ix.Commit.commitDef compileEnv env lvls typ val
    env := env'
    compileEnv := compileEnv'
    as := (Address.toUniqueName commitAddr)::as
    IO.println s!"vote: {repr v}, commitment: {commitAddr}"
  -- build a Lean list of our commitments as the argument to runElection
  let arg : Lean.Expr ← runMeta (metaMakeList voteType as) env
  let (lvls, input, output, type, _sort) ←
    runMeta (metaMakeEvalClaim ``runElection [arg]) env
  let claim ← IO.ofExcept <| Ix.Commit.evalClaim compileEnv lvls input output type
  IO.println s!"{claim}"
  return 0
