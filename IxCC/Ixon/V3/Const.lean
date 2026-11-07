import IxCC.Ixon.Kinds
import IxCC.Ixon.Address
import IxCC.Ixon.Univ
import IxCC.Ixon.V3.Expr

/-! Ixon declarations with contract-carrying expression fields (the data model
introduced by Ixon v3 and kept by v4); their canonical bytes are the v4
encoding of `IxCC.Ixon.V3.Wire`. -/

namespace IxCC.Ixon.V3

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

end IxCC.Ixon.V3
