import Ix.Common
import Ix.Address
import Ix.Prove
import Lean.Declaration
import Ix.Ixon.Serialize
import Ix.Ixon.Metadata
import Ix.Ixon.Expr

namespace Ixon

structure Quotient where
  lvls : Nat
  type : Expr
  kind : Lean.QuotKind
  deriving BEq, Repr

structure Axiom where
  lvls : Nat
  type : Expr
  deriving BEq, Repr

structure Definition where
  lvls : Nat
  type : Expr
  mode : Ix.DefMode
  value : Expr
  part : Bool
  deriving BEq, Repr

structure Constructor where
  lvls : Nat
  type : Expr
  cidx : Nat
  params : Nat
  fields : Nat
  deriving BEq, Repr

structure RecursorRule where
  fields : Nat
  rhs : Expr
  deriving BEq, Repr

structure Recursor where
  lvls : Nat
  type : Expr
  params : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  rules : List RecursorRule
  k : Bool
  deriving BEq, Repr

structure Inductive where
  lvls : Nat
  type : Expr
  params : Nat
  indices : Nat
  ctors : List Constructor
  recrs : List Recursor
  nested : Nat
  recr : Bool
  refl : Bool
  deriving BEq, Repr

structure InductiveProj where
  block : Address
  idx : Nat
  deriving BEq, Repr

structure ConstructorProj where
  block : Address
  idx : Nat
  cidx : Nat
  deriving BEq, Repr

structure RecursorProj where
  block : Address
  idx : Nat
  ridx : Nat
  deriving BEq, Repr

structure DefinitionProj where
  block : Address
  idx : Nat
  deriving BEq, Repr

structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr

inductive Const where
  -- 0xC0
  | defn : Definition -> Const
  -- 0xC1
  | axio : Axiom -> Const
  -- 0xC2
  | quot : Quotient -> Const
  -- 0xC3
  | ctorProj : ConstructorProj -> Const
  -- 0xC4
  | recrProj : RecursorProj -> Const
  -- 0xC5
  | indcProj : InductiveProj -> Const
  -- 0xC6
  | defnProj : DefinitionProj -> Const
  -- 0xC7
  | mutDef : List Definition -> Const
  -- 0xC8
  | mutInd : List Inductive -> Const
  -- 0xC9
  | meta   : Metadata -> Const
  -- 0xCA
  | proof : Proof -> Const
  -- 0xCC
  | comm: Comm -> Const
  deriving BEq, Repr, Inhabited

def putConst : Const → PutM
| .defn x => putUInt8 0xC0 *> putDefn x
| .axio x => putUInt8 0xC1 *> putNatl x.lvls *> putExpr x.type
| .quot x => putUInt8 0xC2 *> putNatl x.lvls *> putExpr x.type *> putQuotKind x.kind
| .ctorProj x => putUInt8 0xC3 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.cidx
| .recrProj x => putUInt8 0xC4 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.ridx
| .indcProj x => putUInt8 0xC5 *> putBytes x.block.hash *> putNatl x.idx
| .defnProj x => putUInt8 0xC6 *> putBytes x.block.hash *> putNatl x.idx
| .mutDef xs => putUInt8 0xC7 *> putArray putDefn xs
| .mutInd xs => putUInt8 0xC8 *> putArray putIndc xs
| .meta m => putUInt8 0xC9 *> putMetadata m
| .proof p => putUInt8 0xCA *> putProof p
| .comm c => putUInt8 0xCC *> putComm c
  where
    putDefn (x: Definition) := do
      putNatl x.lvls
      putExpr x.type
      putDefMode x.mode
      putExpr x.value
      putBool x.part
    putRecrRule (x: RecursorRule) : PutM := putNatl x.fields *> putExpr x.rhs
    putCtor (x: Constructor) : PutM := do
      putNatl x.lvls
      putExpr x.type
      putNatl x.cidx
      putNatl x.params
      putNatl x.fields
    putRecr (x: Recursor) : PutM := do
      putNatl x.lvls
      putExpr x.type
      putNatl x.params
      putNatl x.indices
      putNatl x.motives
      putNatl x.minors
      putArray putRecrRule x.rules
      putBool x.k
    putIndc (x: Inductive) : PutM := do
      putNatl x.lvls
      putExpr x.type
      putNatl x.params
      putNatl x.indices
      putArray putCtor x.ctors
      putArray putRecr x.recrs
      putNatl x.nested
      putBools [x.recr, x.refl]
    putProof (p: Proof) : PutM :=
      match p.claim with
      | .checks lvls type value => do
        putUInt8 0
        putBytes lvls.hash
        putBytes type.hash
        putBytes value.hash
        putByteArray p.bin
      | .evals lvls inp out type => do
        putUInt8 1
        putBytes lvls.hash
        putBytes inp.hash
        putBytes out.hash
        putBytes type.hash
        putByteArray p.bin
    putComm (c: Comm) : PutM :=
      putBytes c.secret.hash *> putBytes c.payload.hash

def getConst : GetM Const := do
  let tag ← getUInt8
  match tag with
  | 0xC0 => .defn <$> getDefn
  | 0xC1 => .axio <$> (.mk <$> getNatl <*> getExpr)
  | 0xC2 => .quot <$> (.mk <$> getNatl <*> getExpr <*> getQuotKind)
  | 0xC3 => .ctorProj <$> (.mk <$> getAddr <*> getNatl <*> getNatl)
  | 0xC4 => .recrProj <$> (.mk <$> getAddr <*> getNatl <*> getNatl)
  | 0xC5 => .indcProj <$> (.mk <$> getAddr <*> getNatl)
  | 0xC6 => .defnProj <$> (.mk <$> getAddr <*> getNatl)
  | 0xC7 => .mutDef <$> getArray getDefn
  | 0xC8 => .mutInd <$> getArray getIndc
  | 0xC9 => .meta <$> getMetadata
  | 0xCA => .proof <$> getProof
  | 0xCC => .comm <$> getComm
  | e => throw s!"expected Const tag, got {e}"
  where
    getDefn : GetM Definition := do
      let lvls <- getNatl
      let type <- getExpr
      let mode <- getDefMode
      let value <- getExpr
      let part <- getBool
      return ⟨lvls, type, mode, value, part⟩
    getCtor : GetM Constructor := do
      let lvls <- getNatl
      let type <- getExpr
      let cidx <- getNatl
      let params <- getNatl
      let fields <- getNatl
      return ⟨lvls, type, cidx, params, fields⟩
    getRecrRule : GetM RecursorRule := RecursorRule.mk <$> getNatl <*> getExpr
    getRecr : GetM Recursor := do
      let lvls <- getNatl
      let type <- getExpr
      let params <- getNatl
      let indices <- getNatl
      let motives <- getNatl
      let minors <- getNatl
      let rules <- getArray getRecrRule
      let k <- getBool
      return ⟨lvls, type, params, indices, motives, minors, rules, k⟩
    getIndc : GetM Inductive := do
      let lvls <- getNatl
      let type <- getExpr
      let params <- getNatl
      let indices <- getNatl
      let ctors <- getArray getCtor
      let recrs <- getArray getRecr
      let nested <- getNatl
      let (recr, refl) <- match ← getBools 2 with
        | [x, y] => pure (x, y)
        | _ => throw s!"unreachable"
      return ⟨lvls, type, params, indices, ctors, recrs, nested, recr, refl⟩
    getAddr : GetM Address := .mk <$> getBytes 32
    getProof : GetM Proof := do
      match (<- getUInt8) with
      | 0 => do
        let claim <- .checks <$> getAddr <*> getAddr <*> getAddr
        let proof <- getByteArray
        return ⟨claim, proof⟩
      | 1 => do
        let claim <- .evals <$> getAddr <*> getAddr <*> getAddr <*> getAddr
        let proof <- getByteArray
        return ⟨claim, proof⟩
      | e => throw s!"expect proof variant tag, got {e}"
    getComm : GetM Comm :=
      .mk <$> getAddr <*> getAddr

instance : Serialize Const where
  put := runPut ∘ putConst
  get := runGet getConst

end Ixon
