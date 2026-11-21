import IxVMRefinement.FamilyAlias.Check

/-! # The rule copy, from the advice statement

The alias at an `iota` key of the family record is a copy of the advice theorem of the rule. A
producer on the circuit's side has the advice statement: the theorem record's type, read with its
level parameters at positions, over the advice keys. This module states the copy as a function
of that statement (`ruleCopyOfAdvice`):

* the statement's level parameters are renamed back from positions (`invPosOf`);
* every binder domain of its telescope, the equation's type and its right side are kept, over the
  advice keys;
* the head of the left side becomes the recursor's model key at the recursor's own level
  parameters;
* the major premise of a canonical rule gets the constructor's model key as its head
  (`plainMajor`); the major premise of a nested rule keeps its head and gets the rule's pins,
  renamed by the block renaming, as its parameters (`nestedMajor`).

No inverse of the advice renaming is used, so two members may share an advice constant. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Expr Key Level LevelParam auxKey)

set_option linter.unusedVariables false

/-- The copy's equation: the head of the left side and its major premise replaced. -/
def copyEquation (headKey : KKey) (lps : List LevelParam) (major : KExpr → KExpr)
    (body : KExpr) : KExpr :=
  match body with
  | .app (.app (.app eq alpha) lhs) rhs =>
    .app (.app (.app eq alpha)
      (Expr.mkAppN (.const headKey (lps.map .param))
        (lhs.getAppArgs.dropLast ++ [major (lhs.getAppArgs.getLastD (.bvar 0))]))) rhs
  | e => e

/-- The copy of a statement: its telescope kept, its equation by `copyEquation`. -/
def copyStatement (headKey : KKey) (lps : List LevelParam) (major : KExpr → KExpr) :
    KExpr → KExpr
  | .forallE ty body mb => .forallE ty (copyStatement headKey lps major body) mb
  | e => copyEquation headKey lps major e

/-- A canonical rule's major premise: the constructor's model key at the head. -/
def plainMajor (ctorKey : KKey) (m : KExpr) : KExpr :=
  match m.getAppFn with
  | .const _ us => Expr.mkAppN (.const ctorKey us) m.getAppArgs
  | _ => m

/-- A nested rule's major premise: the rule's pins, lifted over the `cnF` field binders and
renamed by the block renaming, as the constructor's parameters. -/
def nestedMajor (f : KKey → KKey) (cnF : Nat) (pins : List KExpr) (m : KExpr) : KExpr :=
  Expr.mkAppN m.getAppFn
    ((pins.map fun p => (p.liftLooseBVars cnF 0).renameConsts f) ++
      m.getAppArgs.drop pins.length)

/-- **The rule copy of recursor `recKey`, from the advice statement** `adviceType` (level
parameters at positions), at the recursor's level parameters `lps`. -/
def ruleCopyOfAdvice (lps : List LevelParam) (recKey : KKey) (major : KExpr → KExpr)
    (adviceType : KExpr) : KExpr :=
  copyStatement (auxKey recKey .model) lps major (invPosOf lps adviceType)

end IxVM.Refinement.Decl.FamilyAlias
