import Blake3
import Ix.Address
import Ix.Ixon
import Ix.Ixon.Serialize
import Ix.Meta
import Ix.CanonM
import Batteries.Data.RBMap
import Lean
import Ix.Prove

open Batteries (RBMap)

namespace Ix

inductive IxError
| todo

instance : ToString IxError where
  toString p := s!"todo"

--instance : ToString Proof where
--  toString p := s!"<#{p.inp} ~> #{p.out} : #{p.typ}>"

--inductive IxVMOp where
--| commit (payload secret comm: Address) : IxVMOp
--| reveal (payload secret comm: Address) : IxVMOp

structure IxMEnv where
  names : RBMap Lean.Name (Address × Address) compare
  consts: RBMap Address Ixon.Const compare
  secret: Address

structure IxMState where
  comms : RBMap Address Ixon.Comm compare
  -- transcript : List IxVMOp
  main : Option (Address × Ixon.Const)
  deriving Inhabited

abbrev IxM := ReaderT IxMEnv $ ExceptT IxError $ StateT IxMState Id

def IxM.run (env: Lean.Environment) (secret: Lean.Name) (ixm: IxM Claim)
  : IO (Claim × IxMState × IxMEnv) := do
  let stt <- IO.ofExcept (<- Ix.CanonM.canonicalizeEnv env)
  let (secret, _) := stt.names.find! secret
  let env := IxMEnv.mk stt.names stt.store secret
  let (res, stt) := Id.run (StateT.run (ReaderT.run ixm env) default)
  let claim <- IO.ofExcept res
  return (claim, stt, env)

def IxM.commit (payload: Address): IxM Address := do
  let secret <- (·.secret) <$> read
  let comm := Ixon.Comm.mk secret payload
  let addr := Address.blake3 (Ixon.Serialize.put (Ixon.Const.comm comm))
  modify (fun stt => { stt with 
    comms := stt.comms.insert addr comm 
    -- transcript := (.commit payload secret addr)::stt.transcript
  })
  return addr

def IxM.byName (name: Lean.Name) : IxM Address := do
  let env <- read
  match env.names.find? name with
  | .none => throw .todo
  | .some (addr, _) => return addr

def IxM.reveal (comm: Address) : IxM Address := do
  let stt <- get
  match stt.comms.find? comm with
  | .some c => return c.payload
  | .none => throw .todo

def IxM.secret (comm: Address) : IxM Address := do
  let stt <- get
  match stt.comms.find? comm with
  | .some c => return c.secret
  | .none => throw .todo

def IxM.mkMainConst (type func: Address) (args: List Address): Ixon.Const :=
  match args with
  | [] =>
    Ixon.Const.defn {
      lvls := 0,
      type := Ixon.Expr.cnst type [],
      value := Ixon.Expr.cnst func [],
      part := .true,
    }
  | a::as => 
    let as':= as.map (fun a => Ixon.Expr.cnst a [])
    Ixon.Const.defn {
      lvls := 0,
      type := Ixon.Expr.cnst type [],
      value := Ixon.Expr.apps (Ixon.Expr.cnst func []) (Ixon.Expr.cnst a []) as' ,
      part := .true,
    }

def IxM.mkMain (type func: Address) (args: List Address): IxM Address := do
  let mainConst := IxM.mkMainConst type func args
  let bytes := Ixon.Serialize.put mainConst
  let addr := Address.blake3 bytes
  modify (fun stt => { stt with main := .some (addr, mainConst) })
  return addr

def IxM.evaluate (type input: Address) : IxM Address := sorry

def IxM.prove (claim : Claim) (stt: IxMState) (env: IxMEnv) : IO Proof :=
  sorry

end Ix

namespace ZKVoting

def secret : Nat := 42

inductive Candidate
   | alice | bob | charlie
   deriving Inhabited, Lean.ToExpr, Repr

inductive Result
| winner : Candidate -> Result
| tie : List Candidate -> Result
deriving Repr

def privateVotes : List Candidate := [.alice, .alice, .bob]

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
      tally : Candidate -> (Nat × Nat × Nat) -> (Nat × Nat × Nat)
      | .alice, (a, b, c) => (a+1, b, c)
      | .bob, (a, b, c) => (a, b+1, c)
      | .charlie, (a, b, c) => (a, b, c+1)

def claim : Ix.IxM Claim := do
  let func <- Ix.IxM.byName `ZKVoting.runElection
  let type <- Ix.IxM.byName `ZKVoting.Result
  let argm <- Ix.IxM.byName `ZKVoting.privateVotes >>= Ix.IxM.commit
  let main <- Ix.IxM.mkMain type func [argm]
  let output <- Ix.IxM.evaluate type main
  return Claim.mk main output type

def main : IO Proof := do
  let env <- get_env!
  let (claim, stt, env) <- Ix.IxM.run env `ZKVoting.secret claim
  Ix.IxM.prove claim stt env

end ZKVoting

-- IxVM
-- ingress : Address -> Ptr
-- eval    : Ptr -> Ptr
-- check   : Ptr -> Ptr -> Bool
-- commit  : Ptr -> Ptr -> Comm
-- reveal  : Comm -> Ptr
-- egress  : Ptr -> Address

-- IxM
-- eval    : Address -> Address
-- check   : Address -> Bool
-- commit  : Address -> Address -> Comm
-- reveal  : Comm -> Address

