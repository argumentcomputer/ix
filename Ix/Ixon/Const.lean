import Ix.Address
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
  --| ctor : Constructor -> Const
  ---- 0xC6
  --| recr : Recursor -> Const
  ---- 0xC7
  --| indc : Inductive -> Const
  -- 0xC8
  | ctorProj : ConstructorProj -> Const
  -- 0xC9
  | recrProj : RecursorProj -> Const
  -- 0xCA
  | indcProj : InductiveProj -> Const
  -- 0xCB
  | defnProj : DefinitionProj -> Const
  -- 0xCC
  | mutDef : List Definition -> Const
  -- 0xCD
  | mutInd : List Inductive -> Const
  -- 0xCE
  | meta   : Metadata -> Const
  deriving BEq, Repr, Inhabited

def putDefn (x: Definition) : PutM :=
  putUInt8 0xC3 *>

  putNatl x.lvls *> putExpr x.type *> putExpr x.value *> putBool x.part

def putConst : Const → PutM
| .axio x => putUInt8 0xC0 *> putNatl x.lvls *> putExpr x.type
| .theo x => putUInt8 0xC1 *> putNatl x.lvls *> putExpr x.type *> putExpr x.value
| .opaq x => putUInt8 0xC2 *> putNatl x.lvls *> putExpr x.type *> putExpr x.value
| .defn x => putUInt8 0xC3 *> putDefn x
| .quot x => putUInt8 0xC4 *> putNatl x.lvls *> putExpr x.type *> putQuotKind x.kind
--| .ctor x => putUInt8 0xC5 *> putCtor x
--| .recr x => putUInt8 0xC6 *> putRecr x
--| .indc x => putUInt8 0xC7 *> putIndc x
| .ctorProj x => putUInt8 0xC8 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.cidx
| .recrProj x => putUInt8 0xC9 *> putBytes x.block.hash *> putNatl x.idx *> putNatl x.ridx
| .indcProj x => putUInt8 0xCA *> putBytes x.block.hash *> putNatl x.idx
| .defnProj x => putUInt8 0xCB *> putBytes x.block.hash *> putNatl x.idx
| .mutDef xs => putUInt8 0xCC *> putArray (putDefn <$> xs)
| .mutInd xs => putUInt8 0xCD *> putArray (putIndc <$> xs)
| .meta m => putUInt8 0xCE *> putMetadata m
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

def getDefn : GetM Definition := .mk <$> getNatl <*> getExpr <*> getExpr <*> getBool

def getConst : GetM Const := do
  let tag ← getUInt8
  match tag with
  | 0xC0 => .axio <$> (.mk <$> getNatl <*> getExpr)
  | 0xC1 => .theo <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC2 => .opaq <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC3 => .defn <$> getDefn
  | 0xC4 => .quot <$> (.mk <$> getNatl <*> getExpr <*> getQuotKind)
 -- | 0xC5 => .ctor <$> getCtor
 -- | 0xC6 => .recr <$> getRecr
 -- | 0xC7 => .indc <$> getIndc
  | 0xC8 => .ctorProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl <*> getNatl)
  | 0xC9 => .recrProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl <*> getNatl)
  | 0xCA => .indcProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl)
  | 0xCB => .defnProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl)
  | 0xCC => .mutDef <$> getArray getDefn
  | 0xCD => .mutInd <$> getArray getIndc
  | 0xCE => .meta <$> getMetadata
  | e => throw s!"expected Const tag, got {e}"
  where
    getCtor := .mk <$> getNatl <*> getExpr <*> getNatl <*> getNatl <*> getNatl
    getRecrRule := RecursorRule.mk <$> getNatl <*> getExpr
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

instance : Serialize Const where
  put := runPut ∘ putConst
  get := runGet getConst

end Ixon
