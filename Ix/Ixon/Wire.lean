/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0

Extracted from Ix/Compile/Verify/Catalog.lean and Codec.lean at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f.
-/

module
public import Ix.Ixon.Codec

public section

/-! Structural wire representability, without compiler or source-language
semantics. These predicates describe lossless counts and address widths;
they do not assert canonical table order, typing, or authenticated hashes. -/

namespace Ixon

namespace Univ

/-- Compressed successor-chain counts fit the v2 wire. Explicit universe
variables already have the format's UInt64 bound. -/
def wireWF : Ixon.Univ → Prop
  | .zero => True
  | u@(.succ inner) => u.succCountNat < UInt64.size ∧ wireWF inner
  | .max left right => wireWF left ∧ wireWF right
  | .imax left right => wireWF left ∧ wireWF right
  | .var _ => True

end Univ

namespace Expr

def appCount : Ixon.Expr → Nat
  | .app fn _ => fn.appCount + 1
  | _ => 0

def lamCount : Ixon.Expr → Nat
  | .lam _ _ body => body.lamCount + 1
  | _ => 0

def allCount : Ixon.Expr → Nat
  | .all _ _ _ body => body.allCount + 1
  | _ => 0

/-- Every structural count emitted through a `UInt64` is representable. -/
def wireWF : Ixon.Expr → Prop
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => True
  | .ref _ idxs | .recur _ idxs => idxs.size < UInt64.size
  | .prj _ _ value => value.wireWF
  | .app fn arg =>
    fn.wireWF ∧ arg.wireWF ∧ fn.appCount + 1 < UInt64.size
  | .lam _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.lamCount + 1 < UInt64.size
  | .all _ _ ty body =>
    ty.wireWF ∧ body.wireWF ∧ body.allCount + 1 < UInt64.size
  | .letE _ ty value body => ty.wireWF ∧ value.wireWF ∧ body.wireWF

end Expr

def Definition.exprs (definition : Definition) : List Expr :=
  [definition.typ, definition.value]

def Recursor.exprs (recursor : Recursor) : List Expr :=
  recursor.typ :: recursor.rules.toList.map (·.rhs)

def Axiom.exprs (axiomInfo : Axiom) : List Expr := [axiomInfo.typ]

def Quotient.exprs (quotient : Quotient) : List Expr := [quotient.typ]

def Constructor.exprs (constructor : Constructor) : List Expr :=
  [constructor.typ]

def Inductive.exprs (indInfo : Inductive) : List Expr :=
  indInfo.typ :: indInfo.ctors.toList.flatMap Constructor.exprs

def MutConst.exprs : MutConst → List Expr
  | .defn definition => definition.exprs
  | .indc indInfo => indInfo.exprs
  | .recr recursor => recursor.exprs

def ConstantInfo.exprs : ConstantInfo → List Expr
  | .defn definition => definition.exprs
  | .recr recursor => recursor.exprs
  | .axio axiomInfo => axiomInfo.exprs
  | .quot quotient => quotient.exprs
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => []
  | .muts members => members.toList.flatMap MutConst.exprs

def Definition.wireWF (definition : Definition) : Prop :=
  definition.typ.wireWF ∧ definition.value.wireWF

def RecursorRule.wireWF (rule : RecursorRule) : Prop := rule.rhs.wireWF

def Recursor.wireWF (recursor : Recursor) : Prop :=
  recursor.typ.wireWF ∧
  recursor.rules.size < UInt64.size ∧
  ∀ rule ∈ recursor.rules, rule.wireWF

def Axiom.wireWF (axiomInfo : Axiom) : Prop := axiomInfo.typ.wireWF

def Quotient.wireWF (quotient : Quotient) : Prop := quotient.typ.wireWF

def Constructor.wireWF (constructor : Constructor) : Prop :=
  constructor.typ.wireWF

def Inductive.wireWF (indInfo : Inductive) : Prop :=
  indInfo.typ.wireWF ∧
  indInfo.ctors.size < UInt64.size ∧
  ∀ constructor ∈ indInfo.ctors, constructor.wireWF

def MutConst.wireWF : MutConst → Prop
  | .defn definition => definition.wireWF
  | .indc indInfo => indInfo.wireWF
  | .recr recursor => recursor.wireWF

def ConstantInfo.wireWF : ConstantInfo → Prop
  | .defn definition => definition.wireWF
  | .recr recursor => recursor.wireWF
  | .axio axiomInfo => axiomInfo.wireWF
  | .quot quotient => quotient.wireWF
  | .cPrj projection => projection.block.hash.size = 32
  | .rPrj projection => projection.block.hash.size = 32
  | .iPrj projection => projection.block.hash.size = 32
  | .dPrj projection => projection.block.hash.size = 32
  | .muts members =>
    members.size < UInt64.size ∧ ∀ member ∈ members, member.wireWF

/-- Complete production-codec domain for a constant: every serialized count is
representable, every expression and universe payload has a lossless telescope
count, and every address payload contains the 32 bytes consumed by the reader. -/
def Constant.wireWF (constant : Constant) : Prop :=
  constant.info.wireWF ∧
  constant.sharing.size < UInt64.size ∧
  (∀ expr ∈ constant.sharing, expr.wireWF) ∧
  constant.refs.size < UInt64.size ∧
  (∀ ref ∈ constant.refs, ref.hash.size = 32) ∧
  constant.univs.size < UInt64.size ∧
  (∀ univ ∈ constant.univs,
    Univ.wireWF univ)

end Ixon
