module
public import IxC.Ixon.Types

public section

namespace Ixon

/-- Structural storage units: one per expression constructor and one per
universe-index slot in a reference. This is not a heap-byte measurement.
The parser does not compute it; the byte-consumption proof bounds it without
an additional traversal of decoded terms. -/
def Expr.resourceSize : Expr → Nat
  | .sort _ | .var _ | .str _ | .nat _ | .share _ => 1
  | .ref _ levels | .recur _ levels => 1 + levels.size
  | .prj _ _ value => value.resourceSize + 1
  | .app fn arg => fn.resourceSize + arg.resourceSize + 1
  | .lam type body | .all type body => type.resourceSize + body.resourceSize + 1
  | .letE _ _ type value body => type.resourceSize + value.resourceSize + body.resourceSize + 1

def Definition.resourceSize (value : Definition) : Nat :=
  1 + value.typ.resourceSize + value.value.resourceSize

def RecursorRule.resourceSize (value : RecursorRule) : Nat := 1 + value.rhs.resourceSize

def Recursor.resourceSize (value : Recursor) : Nat :=
  1 + value.typ.resourceSize + (value.rules.toList.map RecursorRule.resourceSize).sum

def Axiom.resourceSize (value : Axiom) : Nat := 1 + value.typ.resourceSize
def Quotient.resourceSize (value : Quotient) : Nat := 1 + value.typ.resourceSize
def Constructor.resourceSize (value : Constructor) : Nat := 1 + value.typ.resourceSize

def Inductive.resourceSize (value : Inductive) : Nat :=
  1 + value.typ.resourceSize + (value.ctors.toList.map Constructor.resourceSize).sum

def MutConst.resourceSize : MutConst → Nat
  | .defn value => value.resourceSize + 1
  | .indc value => value.resourceSize + 1
  | .recr value => value.resourceSize + 1

def ConstantInfo.resourceSize : ConstantInfo → Nat
  | .defn value => value.resourceSize + 1
  | .recr value => value.resourceSize + 1
  | .axio value => value.resourceSize + 1
  | .quot value => value.resourceSize + 1
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => 1
  | .muts members => 1 + (members.toList.map MutConst.resourceSize).sum

def BinderNode.resourceSize : BinderNode → Nat
  | .ifAllZero params _ => 1 + params.size
  | _ => 1

def BinderBlock.resourceSize (value : BinderBlock) : Nat :=
  1 + (value.nodes.toList.map BinderNode.resourceSize).sum

/-- Constant/declaration/expression constructors and variable-size table
slots. Scalar metadata and fixed-width addresses are represented by their
containing record or slot. Each universe contributes its table slot here;
expanded universe trees have the separate `Bounded.univNodes` budget. Binder data
count one unit per block, node and parameter. -/
def Constant.resourceSize (value : Constant) : Nat :=
  1 + value.info.resourceSize + (value.sharing.toList.map Expr.resourceSize).sum +
    value.refs.size + value.univs.size + (value.binders.toList.map BinderBlock.resourceSize).sum

end Ixon
