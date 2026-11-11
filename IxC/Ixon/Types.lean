module
public import IxC.Address.Core
public import IxC.Ixon.Types.Kinds
public import IxC.Ixon.Types.Contract

/-! # Pure Ixon data

The anonymous production data types, with the same names and fields as
`Ix.Ixon`, independent of codecs, compiler metadata, and hashing backends.
Projection defaults stay in the host module because `Inhabited Address`
uses the host hash function. Addresses here are opaque keys.
-/

public section

namespace Ixon

/-! ## Universe Levels -/

/-- Universe levels for Lean's type system. -/
inductive Univ where
  | zero : Univ
  | succ : Univ → Univ
  | max : Univ → Univ → Univ
  | imax : Univ → Univ → Univ
  | var : UInt64 → Univ
  deriving BEq, Repr, Inhabited, Hashable

namespace Univ
  def FLAG_ZERO_SUCC : UInt8 := 0
  def FLAG_MAX : UInt8 := 1
  def FLAG_IMAX : UInt8 := 2
  def FLAG_VAR : UInt8 := 3
end Univ

/-! ## Expressions -/

/-- Expression in the Ixon format.
    Alpha-invariant representation of Lean expressions.
    Names are stripped, binder info is stored in metadata. -/
inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : BinderContract → Expr → Expr → Expr
  | all : BinderContract → ValueContract → Expr → Expr → Expr
  | letE : LetContract → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, Repr, Inhabited, Hashable

namespace Expr
  def FLAG_SORT : UInt8 := 0x0
  def FLAG_VAR : UInt8 := 0x1
  def FLAG_REF : UInt8 := 0x2
  def FLAG_REC : UInt8 := 0x3
  def FLAG_PRJ : UInt8 := 0x4
  def FLAG_STR : UInt8 := 0x5
  def FLAG_NAT : UInt8 := 0x6
  def FLAG_APP : UInt8 := 0x7
  def FLAG_LAM : UInt8 := 0x8
  def FLAG_ALL : UInt8 := 0x9
  def FLAG_LET : UInt8 := 0xA
  def FLAG_SHARE : UInt8 := 0xB

  /-- Embed an ordinary Lean lambda in Ixon. -/
  def leanLam (ty body : Expr) : Expr := .lam .many ty body

  /-- Embed an ordinary Lean forall in Ixon. -/
  def leanAll (ty body : Expr) : Expr := .all .many .shared ty body

  /-- Embed an ordinary Lean let with default contracts. -/
  def leanLet (nonDep : Bool) (ty val body : Expr) : Expr :=
    .letE (.lean nonDep) ty val body

  /-- The ordinary Lean fragment uses explicit default contracts. -/
  def leanFragment : Expr → Bool
    | .lam contract ty body =>
      contract == BinderContract.many && leanFragment ty && leanFragment body
    | .all contract result ty body =>
      contract == BinderContract.many && result == ValueContract.shared &&
        leanFragment ty && leanFragment body
    | .app fn arg => leanFragment fn && leanFragment arg
    | .prj _ _ val => leanFragment val
    | .letE contract ty val body =>
      contract.kind == .value && contract.binder == BinderContract.many &&
        leanFragment ty && leanFragment val && leanFragment body
    | _ => true
end Expr

/-! ## Constant Types -/

-- Declaration tags are shared with the host through Types.Kinds.

open Ix (DefKind DefinitionSafety QuotKind)

structure Definition where
  kind : DefKind
  safety : DefinitionSafety
  lvls : UInt64
  typ : Expr
  value : Expr
  deriving BEq, Repr, Inhabited

structure RecursorRule where
  fields : UInt64
  rhs : Expr
  deriving BEq, Repr, Inhabited

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
  deriving BEq, Repr, Inhabited

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
  deriving BEq, Repr, Inhabited

structure Inductive where
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, Repr, Inhabited

/-! ## Projection Types -/

structure InductiveProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Hashable

structure ConstructorProj where
  idx : UInt64
  cidx : UInt64
  block : Address
  deriving BEq, Repr, Hashable

structure RecursorProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Hashable

structure DefinitionProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Hashable

/-! ## Constant Info -/

inductive MutConst where
  | defn : Definition → MutConst
  | indc : Inductive → MutConst
  | recr : Recursor → MutConst
  deriving BEq, Repr, Inhabited

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

/-! ## Binder data

The binder-data section of a record: the zero-ness of the codomain sort of
every `lam` and `all` binder, as IxC's `PropWhen` (`never`, or "zero exactly
when all of the parameters are zero"). The section is part of the record's
bytes, so the record's address covers it.

A block holds the data of one expression: a root (`shared = false`, `index`
the root's number, `variant = 0`) or a sharing entry (`shared = true`, `index`
the entry's index, `variant` one of its variants). Its nodes follow the
expression's numbered nodes in pre-order: every `lam` and `all`, and every
`share` whose entry has a binder (`BinderNode.share` names the entry's
variant there). A record without binders has no block. -/

/-- One numbered node of a binder-data block. -/
inductive BinderNode where
  /-- A binder whose codomain sort is never zero (wire tag 0). -/
  | never : BinderNode
  /-- A binder whose codomain sort is always zero (`ifAllZero []`, wire tag 1). -/
  | zero : BinderNode
  /-- A binder whose codomain sort is zero exactly when every universe
  parameter in `params` is (wire tag 2). Canonical: nonempty and strictly
  ascending. -/
  | ifAllZero : Array UInt64 → BinderNode
  /-- A share site whose entry has a binder: the entry at variant `v` (wire tag 3). -/
  | share : UInt64 → BinderNode
  /-- A binder whose datum the compiler could not decide (wire tag 4).
  Readers accept it; a checker that needs the datum rejects it. -/
  | undecided : BinderNode
  deriving BEq, Repr, Inhabited, Hashable

namespace BinderNode
  def TAG_NEVER : UInt8 := 0
  def TAG_ZERO : UInt8 := 1
  def TAG_IF_ALL_ZERO : UInt8 := 2
  def TAG_SHARE : UInt8 := 3
  def TAG_UNDECIDED : UInt8 := 4
end BinderNode

/-- The binder data of one expression of a record (one variant of it, for a
sharing entry). -/
structure BinderBlock where
  /-- `false` for a root expression, `true` for a sharing entry (wire byte 0 or 1). -/
  shared : Bool
  /-- The root's number, or the sharing entry's index. -/
  index : UInt64
  /-- The variant: 0 for a root. -/
  variant : UInt64
  nodes : Array BinderNode
  deriving BEq, Repr, Inhabited, Hashable

/-- A top-level constant with sharing, refs, and univs tables, and its
binder-data section (blocks sorted by `(shared, index, variant)`). -/
structure Constant where
  info : ConstantInfo
  sharing : Array Expr
  refs : Array Address
  univs : Array Univ
  binders : Array BinderBlock := #[]
  deriving BEq, Repr, Inhabited

namespace Constant
  def FLAG_MUTS : UInt8 := 0xC
  def FLAG : UInt8 := 0xD
end Constant

end Ixon

end
