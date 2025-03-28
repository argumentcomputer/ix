import Ix.Address
import Ix.Prove
import Lean.Declaration
import Ix.Ixon.Serialize
import Ix.Ixon.Metadata
import Ix.Ixon.Expr

namespace Ixon

deriving instance BEq for Lean.QuotKind

deriving instance Repr for Lean.QuotKind

structure Quotient where
  lvls : Nat
  type : Expr
  kind : Lean.QuotKind
  deriving BEq, Repr

structure Axiom where
  lvls  : Nat
  type  : Expr
  deriving BEq, Repr

structure Theorem where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving BEq, Repr

structure Opaque where
  lvls  : Nat
  type  : Expr
  value : Expr
  deriving BEq, Repr

structure Definition where
  lvls  : Nat
  type  : Expr
  value : Expr
  part  : Bool
  deriving BEq, Repr

structure Constructor where
  lvls   : Nat
  type   : Expr
  idx    : Nat
  params : Nat
  fields : Nat
  deriving BEq, Repr

structure RecursorRule where
  fields : Nat
  rhs    : Expr
  deriving BEq, Repr

structure Recursor where
  lvls     : Nat
  type     : Expr
  params   : Nat
  indices  : Nat
  motives  : Nat
  minors   : Nat
  rules    : List RecursorRule
  isK      : Bool
  internal : Bool
  deriving BEq, Repr

structure Inductive where
  lvls    : Nat
  type    : Expr
  params  : Nat
  indices : Nat
  ctors   : List Constructor
  recrs   : List Recursor
  recr    : Bool
  refl    : Bool
  struct  : Bool
  unit    : Bool
  deriving BEq, Repr

structure InductiveProj where
  block : Address
  idx   : Nat
  deriving BEq, Repr

structure ConstructorProj where
  block : Address
  idx   : Nat
  cidx  : Nat
  deriving BEq, Repr

structure RecursorProj where
  block : Address
  idx   : Nat
  ridx  : Nat
  deriving BEq, Repr

structure DefinitionProj where
  block : Address
  idx   : Nat
  deriving BEq, Repr

structure Comm where
  secret: Address
  payload: Address
  deriving BEq, Repr

inductive Const where
  -- 0xC0
  | axio : Axiom -> Const
  -- 0xC1
  | theo : Theorem -> Const
  -- 0xC2
  | opaq : Opaque -> Const
  -- 0xC3
  | defn : Definition -> Const
  -- 0xC4
  | quot : Quotient -> Const
  -- 0xC5
  | ctorProj : ConstructorProj -> Const
  -- 0xC6
  | recrProj : RecursorProj -> Const
  -- 0xC7
  | indcProj : InductiveProj -> Const
  -- 0xC8
  | defnProj : DefinitionProj -> Const
  -- 0xC9
  | mutDef : List Definition -> Const
  -- 0xCA
  | mutInd : List Inductive -> Const
  -- 0xCB
  | meta   : Metadata -> Const
  -- 0xCC
  | proof : Proof -> Const
  | comm: Comm -> Const
  deriving BEq, Repr, Inhabited

def putConst : Const → PutM
| .axio x => putUInt8 0xC0 *> putNatl x.lvls *> putExpr x.type
| .theo x => putUInt8 0xC1 *> putNatl x.lvls *> putExpr x.type *> putExpr x.value
| .opaq x => putUInt8 0xC2 *> putNatl x.lvls *> putExpr x.type *> putExpr x.value
| .defn x => putUInt8 0xC3 *> putDefn x
| .quot x => putUInt8 0xC4 *> putNatl x.lvls *> putExpr x.type *> putQuotKind x.kind
| .ctorProj x => putUInt8 0xC5 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.cidx
| .recrProj x => putUInt8 0xC6 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.ridx
| .indcProj x => putUInt8 0xC7 *> putBytes x.block.hash *> putNatl x.idx
| .defnProj x => putUInt8 0xC8 *> putBytes x.block.hash *> putNatl x.idx
| .mutDef xs => putUInt8 0xC9 *> putArray (putDefn <$> xs)
| .mutInd xs => putUInt8 0xCA *> putArray (putIndc <$> xs)
| .meta m => putUInt8 0xCB *> putMetadata m
| .proof p => putUInt8 0xCC *> putProof p
| .comm c => putUInt8 0xCD *> putComm c
  where
    putDefn (x: Definition) :=
      putNatl x.lvls *> putExpr x.type *> putExpr x.value *> putBool x.part
    putRecrRule (x: RecursorRule) : PutM := putNatl x.fields *> putExpr x.rhs
    putCtor (x: Constructor) : PutM :=
      putNatl x.lvls *> putExpr x.type
        *> putNatl x.idx *> putNatl x.params *> putNatl x.fields
    putRecr (x: Recursor) : PutM :=
      putNatl x.lvls *> putExpr x.type
        *> putNatl x.params *> putNatl x.indices *> putNatl x.motives
        *> putNatl x.minors *> putArray (putRecrRule <$> x.rules)
        *> putBools [x.isK, x.internal]
    putIndc (x: Inductive) : PutM :=
      putNatl x.lvls *> putExpr x.type
        *> putNatl x.params *> putNatl x.indices
        *> putArray (putCtor <$> x.ctors) *> putArray (putRecr <$> x.recrs)
        *> putBools [x.recr, x.refl, x.struct, x.unit]
    putProof (p: Proof) : PutM :=
      putBytes p.claim.inp.hash
      *> putBytes p.claim.out.hash
      *> putBytes p.claim.typ.hash
      *> putByteArray p.bin
    putComm (c: Comm) : PutM :=
      putBytes c.secret.hash *> putBytes c.payload.hash

def getConst : GetM Const := do
  let tag ← getUInt8
  match tag with
  | 0xC0 => .axio <$> (.mk <$> getNatl <*> getExpr)
  | 0xC1 => .theo <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC2 => .opaq <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC3 => .defn <$> getDefn
  | 0xC4 => .quot <$> (.mk <$> getNatl <*> getExpr <*> getQuotKind)
  | 0xC5 => .ctorProj <$> (.mk <$> getAddr <*> getNatl <*> getNatl)
  | 0xC6 => .recrProj <$> (.mk <$> getAddr <*> getNatl <*> getNatl)
  | 0xC7 => .indcProj <$> (.mk <$> getAddr <*> getNatl)
  | 0xC8 => .defnProj <$> (.mk <$> getAddr <*> getNatl)
  | 0xC9 => .mutDef <$> getArray getDefn
  | 0xCA => .mutInd <$> getArray getIndc
  | 0xCB => .meta <$> getMetadata
  | 0xCC => .proof <$> getProof
  | 0xCD => .comm <$> getComm
  | e => throw s!"expected Const tag, got {e}"
  where
    getDefn : GetM Definition :=
      .mk <$> getNatl <*> getExpr <*> getExpr <*> getBool
    getCtor : GetM Constructor :=
      .mk <$> getNatl <*> getExpr <*> getNatl <*> getNatl <*> getNatl
    getRecrRule : GetM RecursorRule := 
      RecursorRule.mk <$> getNatl <*> getExpr
    getRecr : GetM Recursor := do
      let f ← Recursor.mk <$> getNatl <*> getExpr <*> getNatl
        <*> getNatl <*> getNatl <*> getNatl <*> getArray getRecrRule
      match ← getBools 2 with
      | [x, y] => return f x y
      | _ => throw s!"unreachable"
    getIndc : GetM Inductive := do
      let f ← Inductive.mk <$> getNatl <*> getExpr <*> getNatl <*> getNatl
        <*> getArray getCtor <*> getArray getRecr
      match ← getBools 4 with
      | [w, x, y, z] => return f w x y z
      | _ => throw s!"unreachable"
    getAddr : GetM Address := .mk <$> getBytes 32
    getProof : GetM Proof :=
      .mk <$> (.mk <$> getAddr <*> getAddr <*> getAddr) <*> getByteArray
    getComm : GetM Comm :=
      .mk <$> getAddr <*> getAddr

instance : Serialize Const where
  put := runPut ∘ putConst
  get := runGet getConst

end Ixon
