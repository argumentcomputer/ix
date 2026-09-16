import Compilatrix.Ixon.Const
import Compilatrix.Ixon.V3.Expr

/-! V3 declaration headers are unchanged; their expression fields carry
complete v3 contracts. Raw v3 identities do not use the legacy v2 compressor. -/

namespace Compilatrix.Ixon.V3

structure Definition where
  kind : DefKind
  safety : DefinitionSafety
  lvls : UInt64
  typ : Expr
  value : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

structure RecursorRule where
  fields : UInt64
  rhs : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

structure Recursor where
  k : Bool
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  motives : UInt64
  minors : UInt64
  typ : Expr
  rules : Array RecursorRule
  deriving BEq, DecidableEq, Repr, Inhabited

structure Axiom where
  isUnsafe : Bool
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Quotient where
  kind : QuotKind
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Constructor where
  isUnsafe : Bool
  lvls : UInt64
  cidx : UInt64
  params : UInt64
  fields : UInt64
  typ : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

structure Inductive where
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, DecidableEq, Repr, Inhabited

structure InductiveProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure ConstructorProj where
  idx : UInt64
  cidx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure RecursorProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure DefinitionProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

inductive MutConst where
  | defn : Definition → MutConst
  | indc : Inductive → MutConst
  | recr : Recursor → MutConst
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ConstantInfo where
  | defn : Definition → ConstantInfo
  | recr : Recursor → ConstantInfo
  | axio : Axiom → ConstantInfo
  | quot : Quotient → ConstantInfo
  | cPrj : ConstructorProj → ConstantInfo
  | rPrj : RecursorProj → ConstantInfo
  | iPrj : InductiveProj → ConstantInfo
  | dPrj : DefinitionProj → ConstantInfo
  | muts : Array MutConst → ConstantInfo
  deriving BEq, Repr, Inhabited

namespace ConstantInfo

def CONST_DEFN : UInt64 := 0
def CONST_RECR : UInt64 := 1
def CONST_AXIO : UInt64 := 2
def CONST_QUOT : UInt64 := 3
def CONST_CPRJ : UInt64 := 4
def CONST_RPRJ : UInt64 := 5
def CONST_IPRJ : UInt64 := 6
def CONST_DPRJ : UInt64 := 7

end ConstantInfo

/-- Recover the member table used when a constant is entered as its own
evaluation/checking frame. Standalone definitions and recursors behave as
singleton blocks; projections, axioms, quotients, and inductive projections
have no local `recur` members.

This belongs to the constant layer because both the evaluator and the usage
checker interpret the same serialized `ConstantInfo` shape. -/
def selfMutsOf : ConstantInfo → Array MutConst
  | .muts members => members
  | .defn definition => #[.defn definition]
  | .recr recursor => #[.recr recursor]
  | _ => #[]

/-- A top-level constant with sharing, refs, and univs tables. -/
structure Constant where
  info : ConstantInfo
  sharing : Array Expr
  refs : Array Address
  univs : Array Univ
  deriving BEq, Repr, Inhabited

namespace Constant

def FLAG_MUTS : UInt8 := 0xC
def FLAG : UInt8 := 0xD

end Constant

/-! ## Embedded expression enumeration

This is the authoritative body order consumed by the sharing-table checker.
It covers every expression in a constant payload; projections contain none. -/

def Definition.exprs (d : Definition) : List Expr := [d.typ, d.value]

def Recursor.exprs (r : Recursor) : List Expr :=
  r.typ :: r.rules.toList.map (·.rhs)

def Axiom.exprs (a : Axiom) : List Expr := [a.typ]

def Quotient.exprs (q : Quotient) : List Expr := [q.typ]

def Constructor.exprs (c : Constructor) : List Expr := [c.typ]

def Inductive.exprs (i : Inductive) : List Expr :=
  i.typ :: i.ctors.toList.flatMap Constructor.exprs

def MutConst.exprs : MutConst → List Expr
  | .defn d => d.exprs
  | .indc i => i.exprs
  | .recr r => r.exprs

def ConstantInfo.exprs : ConstantInfo → List Expr
  | .defn d => d.exprs
  | .recr r => r.exprs
  | .axio a => a.exprs
  | .quot q => q.exprs
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => []
  | .muts ms => ms.toList.flatMap MutConst.exprs

def definitionBytes (d : Definition) : ByteArray :=
  u8Bytes (definitionModeByte d.kind d.safety) ++
    tag0Bytes ⟨d.lvls⟩ ++ exprBytes d.typ ++ exprBytes d.value

def recursorRuleBytes (r : RecursorRule) : ByteArray :=
  tag0Bytes ⟨r.fields⟩ ++ exprBytes r.rhs

def recursorBytes (r : Recursor) : ByteArray :=
  u8Bytes (recursorModeByte r.k r.isUnsafe) ++
    tag0Bytes ⟨r.lvls⟩ ++ tag0Bytes ⟨r.params⟩ ++
    tag0Bytes ⟨r.indices⟩ ++ tag0Bytes ⟨r.motives⟩ ++
    tag0Bytes ⟨r.minors⟩ ++ exprBytes r.typ ++
    countedArrayBytes recursorRuleBytes r.rules

def axiomBytes (a : Axiom) : ByteArray :=
  boolBytes a.isUnsafe ++
    tag0Bytes ⟨a.lvls⟩ ++ exprBytes a.typ

def quotientBytes (q : Quotient) : ByteArray :=
  u8Bytes q.kind.toBits ++ tag0Bytes ⟨q.lvls⟩ ++ exprBytes q.typ

def constructorBytes (c : Constructor) : ByteArray :=
  boolBytes c.isUnsafe ++
    tag0Bytes ⟨c.lvls⟩ ++ tag0Bytes ⟨c.cidx⟩ ++
    tag0Bytes ⟨c.params⟩ ++ tag0Bytes ⟨c.fields⟩ ++ exprBytes c.typ

def inductiveBytes (i : Inductive) : ByteArray :=
  boolBytes i.isUnsafe ++
    tag0Bytes ⟨i.lvls⟩ ++ tag0Bytes ⟨i.params⟩ ++
    tag0Bytes ⟨i.indices⟩ ++ exprBytes i.typ ++
    countedArrayBytes constructorBytes i.ctors

def inductiveProjBytes (p : InductiveProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def constructorProjBytes (p : ConstructorProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ tag0Bytes ⟨p.cidx⟩ ++ p.block.hash

def recursorProjBytes (p : RecursorProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def definitionProjBytes (p : DefinitionProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def mutConstPayloadBytes : MutConst → ByteArray
  | .defn d => definitionBytes d
  | .indc i => inductiveBytes i
  | .recr r => recursorBytes r

def mutConstTag : MutConst → UInt8
  | .defn _ => 0
  | .indc _ => 1
  | .recr _ => 2

def mutConstBytes (m : MutConst) : ByteArray :=
  u8Bytes (mutConstTag m) ++ mutConstPayloadBytes m

def constantInfoTag : ConstantInfo → Tag4
  | .defn _ => ⟨Constant.FLAG, ConstantInfo.CONST_DEFN⟩
  | .recr _ => ⟨Constant.FLAG, ConstantInfo.CONST_RECR⟩
  | .axio _ => ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  | .quot _ => ⟨Constant.FLAG, ConstantInfo.CONST_QUOT⟩
  | .cPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_CPRJ⟩
  | .rPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_RPRJ⟩
  | .iPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_IPRJ⟩
  | .dPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_DPRJ⟩
  | .muts ms => ⟨Constant.FLAG_MUTS, ms.size.toUInt64⟩

def constantInfoPayloadBytes : ConstantInfo → ByteArray
  | .defn d => definitionBytes d
  | .recr r => recursorBytes r
  | .axio a => axiomBytes a
  | .quot q => quotientBytes q
  | .cPrj p => constructorProjBytes p
  | .rPrj p => recursorProjBytes p
  | .iPrj p => inductiveProjBytes p
  | .dPrj p => definitionProjBytes p
  | .muts ms => encodedArrayBytes mutConstBytes ms

def constantInfoBytes (info : ConstantInfo) : ByteArray :=
  tag4Bytes (constantInfoTag info) ++ constantInfoPayloadBytes info

def constantTablesBytes (c : Constant) : ByteArray :=
  countedArrayBytes exprBytes c.sharing ++
    countedArrayBytes (fun a : Address => a.hash) c.refs ++
    countedArrayBytes univBytes c.univs

def constantBytes (c : Constant) : ByteArray :=
  constantInfoBytes c.info ++ constantTablesBytes c

def putConstantInfo (info : ConstantInfo) : PutM Unit := putBytes (constantInfoBytes info)
def putConstant (c : Constant) : PutM Unit := putBytes (constantBytes c)

end Compilatrix.Ixon.V3
