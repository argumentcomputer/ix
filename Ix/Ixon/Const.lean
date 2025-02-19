import Ix.Address
import Lean.Declaration
import Ix.Ixon.Serialize
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

structure MetaNode where
  name : Option Lean.Name
  link : Option Address
  deriving BEq, Repr

structure Metadata where
  meta: List MetaNode
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
  | ctor : Constructor -> Const
  -- 0xC6
  | recr : Recursor -> Const
  -- 0xC7
  | indc : Inductive -> Const
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
  deriving BEq, Repr

def putNatl (x: Nat) : PutM := putExpr (.natl x)
def getNatl : GetM Nat := do
  match (← getExpr) with
  | .natl n => return n
  | x => throw s!"expected Expr.Nat, got {repr x}"

def putArray (xs : List PutM) := do
  putExprTag 0xB (UInt64.ofNat xs.length)
  List.forM xs id

def getArray (getM: GetM A) : GetM (List A) := do
  let tagByte ← getUInt8
  let tag := UInt8.shiftRight tagByte 4
  let small := UInt8.land tagByte 0b111
  let isLarge := (UInt8.land tagByte 0b1000 != 0)
  match tag with
  | 0xB => do
    let len <- UInt64.toNat <$> getExprTag isLarge small
    List.mapM (λ _ => getM) (List.range len) 
  | e => throw s!"expected Array with tag 0xB, got {e}"

def putQuotKind : Lean.QuotKind → PutM
| .type => putUInt8 0
| .ctor => putUInt8 1
| .lift => putUInt8 2
| .ind => putUInt8 3

def getQuotKind : GetM Lean.QuotKind := do
  match (← getUInt8) with
  | 0 => return .type
  | 1 => return .ctor
  | 2 => return .lift
  | 3 => return .ind
  | e => throw s!"expected QuotKind encoding between 0 and 3, got {e}"

inductive NamePart where
| str (s: String)
| num (n: Nat)

def nameToParts: Lean.Name → List NamePart
| .anonymous => []
| .str n s => NamePart.str s :: nameToParts n
| .num n i => NamePart.num i :: nameToParts n

def nameFromParts: List NamePart → Lean.Name
| [] => .anonymous
| (.str n)::ns => .str (nameFromParts ns) n
| (.num i)::ns => .num (nameFromParts ns) i

def putNamePart : NamePart → PutM
| .str s => putExpr (.strl s)
| .num i => putExpr (.natl i)

def getNamePart : GetM NamePart := do
  match (← getExpr) with
  | .strl s => return (.str s)
  | .natl s => return (.num s)
  | e => throw s!"expected NamePart from .strl or .natl, got {repr e}"

def putName (n: Lean.Name): PutM := putArray (putNamePart <$> (nameToParts n))
def getName: GetM Lean.Name := nameFromParts <$> getArray getNamePart

def putOption (putM: A -> PutM): Option A → PutM
| .none => putArray []
| .some x => putArray [putM x]

def getOption [Repr A] (getM: GetM A): GetM (Option A) := do
  match ← getArray getM with
  | [] => return .none
  | [x] => return .some x
  | e => throw s!"Expected Option, got {repr e}"

def putMetaNode: MetaNode → PutM
| ⟨n, a⟩ => putArray [putOption putName n, putOption (putBytes ·.hash) a]

def getMetaNode: GetM MetaNode := do
  let tagByte ← getUInt8
  let tag := UInt8.shiftRight tagByte 4
  let small := UInt8.land tagByte 0b111
  let isLarge := (UInt8.land tagByte 0b1000 != 0)
  match tag with
  | 0xB => do
    let _ ← UInt64.toNat <$> getExprTag isLarge small
    let n ← getOption getName
    let a ← getOption (Address.mk <$> getBytes 32)
    return MetaNode.mk n a
  | e => throw s!"expected metanode Array with tag 0xB, got {e}"

def putConst : Const → PutM
| .axio x => putTag 0xC0 x.lvls x.type
| .theo x => putTag 0xC1 x.lvls x.type *> putExpr x.value
| .opaq x => putTag 0xC2 x.lvls x.type *> putExpr x.value
| .defn x => putDefn x
| .quot x => putTag 0xC4 x.lvls x.type *> putQuotKind x.kind
| .ctor x => putCtor x
| .recr x => putRecr x
| .indc x => putIndc x
| .ctorProj x => putProj 0xC8 x.block *> putNatl x.idx *> putNatl x.cidx
| .recrProj x => putProj 0xC9 x.block *> putNatl x.idx *> putNatl x.ridx
| .indcProj x => putProj 0xCA x.block *> putNatl x.idx
| .defnProj x => putProj 0xCB x.block *> putNatl x.idx
| .mutDef xs => putUInt8 0xCC *> putArray (putDefn <$> xs)
| .mutInd xs => putUInt8 0xCD *> putArray (putIndc <$> xs)
| .meta m => putUInt8 0xCE *> putArray (putMetaNode <$> m.meta)
  where
    putTag (tag: UInt8) (lvls : Nat) (type: Expr) : PutM :=
      putUInt8 tag *> putNatl lvls *> putExpr type
    putProj (tag: UInt8) (a: Address) : PutM := putUInt8 tag *> putBytes a.hash
    putRecrRule (x: RecursorRule) : PutM := putNatl x.fields *> putExpr x.rhs
    putDefn (x: Definition) : PutM := 
      putTag 0xC3 x.lvls x.type *> putExpr x.value *> putBool x.part
    putCtor (x: Constructor) : PutM :=
      putTag 0xC5 x.lvls x.type
        *> putNatl x.idx *> putNatl x.params *> putNatl x.fields
    putRecr (x: Recursor) : PutM :=
      putTag 0xC6 x.lvls x.type
        *> putNatl x.params *> putNatl x.indices *> putNatl x.motives
        *> putNatl x.minors *> putArray (putRecrRule <$> x.rules)
        *> putBools [x.isK, x.internal]
    putIndc (x: Inductive) : PutM :=
      putTag 0xC7 x.lvls x.type
        *> putNatl x.params *> putNatl x.indices
        *> putArray (putCtor <$> x.ctors) *> putArray (putRecr <$> x.recrs)
        *> putBools [x.recr, x.refl, x.struct, x.unit]

def getConst : GetM Const := do
  let tag ← getUInt8
  match tag with
  | 0xC0 => .axio <$> (.mk <$> getNatl <*> getExpr)
  | 0xC1 => .theo <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC2 => .opaq <$> (.mk <$> getNatl <*> getExpr <*> getExpr)
  | 0xC3 => .defn <$> getDefn
  | 0xC4 => .quot <$> (.mk <$> getNatl <*> getExpr <*> getQuotKind)
  | 0xC5 => .ctor <$> getCtor
  | 0xC6 => .recr <$> getRecr
  | 0xC7 => .indc <$> getIndc
  | 0xC8 => .ctorProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl <*> getNatl)
  | 0xC9 => .recrProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl <*> getNatl)
  | 0xCA => .indcProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl)
  | 0xCB => .defnProj <$> (.mk <$> (.mk <$> getBytes 32) <*> getNatl)
  | 0xCC => .mutDef <$> getArray getDefn
  | 0xCD => .mutInd <$> getArray getIndc
  | 0xCE => .meta <$> (.mk <$> getArray getMetaNode)
  | e => throw s!"expected Const tag, got {e}"
  where
    getDefn := .mk <$> getNatl <*> getExpr <*> getExpr <*> getBool
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
