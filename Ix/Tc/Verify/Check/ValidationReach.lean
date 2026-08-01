import Ix.Tc.Verify.Check.Scoped
import Ix.Tc.Verify.Support

/-!
# Finite syntax support for well-scopedness validation

The production validators memoize by content address.  Their soundness
therefore needs collision freedom on exactly the finite syntax they may
visit, rather than a global injectivity axiom.  This module names that
syntax: expression descendants and the universe descendants embedded in
sort and constant nodes.

The reach relations contain no validation or typing fact.  `Coverage` only
connects their finite footprints to an existing `RunSupport`, whose separate
`CollisionFree` field is consumed by the operational proof.
-/

namespace Ix.Tc

namespace KUniv

/-- Direct worklist children in the production validator's LIFO order. -/
def validationChildren : KUniv .anon → List (KUniv .anon)
  | .succ child _ => [child]
  | .max left right _ | .imax left right _ => [right, left]
  | .zero _ | .param .. => []

/-- Reflexive structural descent through a universe expression. -/
inductive ValidationReach : KUniv .anon → KUniv .anon → Prop
  | refl (u : KUniv .anon) : ValidationReach u u
  | succ {u child : KUniv .anon} {addr : Address} :
    ValidationReach u child →
    ValidationReach (.succ u addr) child
  | maxLeft {left right child : KUniv .anon} {addr : Address} :
    ValidationReach left child →
    ValidationReach (.max left right addr) child
  | maxRight {left right child : KUniv .anon} {addr : Address} :
    ValidationReach right child →
    ValidationReach (.max left right addr) child
  | imaxLeft {left right child : KUniv .anon} {addr : Address} :
    ValidationReach left child →
    ValidationReach (.imax left right addr) child
  | imaxRight {left right child : KUniv .anon} {addr : Address} :
    ValidationReach right child →
    ValidationReach (.imax left right addr) child

namespace ValidationReach

/-- Structural validation reach composes. -/
theorem trans {root middle child : KUniv .anon}
    (hroot : ValidationReach root middle)
    (hmiddle : ValidationReach middle child) :
    ValidationReach root child := by
  induction hroot with
  | refl => exact hmiddle
  | succ _ ih => exact .succ (ih hmiddle)
  | maxLeft _ ih => exact .maxLeft (ih hmiddle)
  | maxRight _ ih => exact .maxRight (ih hmiddle)
  | imaxLeft _ ih => exact .imaxLeft (ih hmiddle)
  | imaxRight _ ih => exact .imaxRight (ih hmiddle)

/-- A direct validator child is structurally reachable. -/
theorem child {parent child : KUniv .anon}
    (hchild : child ∈ parent.validationChildren) :
    ValidationReach parent child := by
  cases parent with
  | zero => simp [validationChildren] at hchild
  | succ parent addr =>
      simp only [validationChildren, List.mem_singleton] at hchild
      subst child
      exact .succ (.refl _)
  | max left right addr =>
      simp [validationChildren] at hchild
      rcases hchild with rfl | rfl
      · exact .maxRight (.refl _)
      · exact .maxLeft (.refl _)
  | imax left right addr =>
      simp [validationChildren] at hchild
      rcases hchild with rfl | rfl
      · exact .imaxRight (.refl _)
      · exact .imaxLeft (.refl _)
  | param => simp [validationChildren] at hchild

end ValidationReach

/-- The local guard checked when a universe node is first inserted into the
memo set.  Composite nodes have no local obligation; their children are
represented by the validation frontier. -/
def ValidationLocal (bound : Nat) : KUniv .anon → Prop
  | .param idx _ _ => idx.toNat < bound
  | _ => True

/-- A finite run support covers a universe domain, and that domain is closed
under exactly the child edges followed by the validator. -/
structure ValidationDomain (support : RunSupport)
    (domain : KUniv .anon → Prop) : Prop where
  covered : ∀ ⦃level⦄, domain level → support.univ level
  child : ∀ ⦃parent child⦄, domain parent →
    child ∈ parent.validationChildren → domain child

/-- Local guard validity at every reachable node implies full universe
scoping. -/
theorem scoped_of_validationLocal
    {root : KUniv .anon} {bound : Nat}
    (hall : ∀ ⦃u⦄, ValidationReach root u → u.ValidationLocal bound) :
    root.Scoped bound := by
  induction root with
  | zero => trivial
  | succ child addr ih =>
      apply ih
      intro u hu
      exact hall (.succ hu)
  | max left right addr ihLeft ihRight =>
      exact ⟨ihLeft (fun _ h => hall (.maxLeft h)),
        ihRight (fun _ h => hall (.maxRight h))⟩
  | imax left right addr ihLeft ihRight =>
      exact ⟨ihLeft (fun _ h => hall (.imaxLeft h)),
        ihRight (fun _ h => hall (.imaxRight h))⟩
  | param idx name addr => exact hall (.refl _)

end KUniv

namespace KExpr

/-- Direct expression worklist children, including the exact depth attached
by the production validator. -/
def validationChildrenAt (depth : UInt64) :
    KExpr .anon → List (KExpr .anon × UInt64)
  | .app fn arg _ => [(arg, depth), (fn, depth)]
  | .lam _ _ type body _ | .all _ _ type body _ =>
      [(body, depth + 1), (type, depth)]
  | .letE _ type value body _ _ =>
      [(body, depth + 1), (value, depth), (type, depth)]
  | .prj _ _ value _ => [(value, depth)]
  | _ => []

/-- Universe roots passed directly to `validateUnivParamsSeen` at one
expression node. -/
def validationUnivRoots : KExpr .anon → List (KUniv .anon)
  | .sort level _ => [level]
  | .const _ levels _ => levels.toList
  | _ => []

/-- Reflexive structural descent through expression children.  Universes
are tracked by the separate `ValidationUnivReach` relation below. -/
inductive ValidationReach : KExpr .anon → KExpr .anon → Prop
  | refl (e : KExpr .anon) : ValidationReach e e
  | appFn {fn arg child : KExpr .anon} {info : ExprInfo .anon} :
    ValidationReach fn child →
    ValidationReach (.app fn arg info) child
  | appArg {fn arg child : KExpr .anon} {info : ExprInfo .anon} :
    ValidationReach arg child →
    ValidationReach (.app fn arg info) child
  | lamType {type body child : KExpr .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationReach type child →
    ValidationReach (.lam name bi type body info) child
  | lamBody {type body child : KExpr .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationReach body child →
    ValidationReach (.lam name bi type body info) child
  | allType {type body child : KExpr .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationReach type child →
    ValidationReach (.all name bi type body info) child
  | allBody {type body child : KExpr .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationReach body child →
    ValidationReach (.all name bi type body info) child
  | letType {type value body child : KExpr .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationReach type child →
    ValidationReach (.letE name type value body nonDep info) child
  | letValue {type value body child : KExpr .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationReach value child →
    ValidationReach (.letE name type value body nonDep info) child
  | letBody {type value body child : KExpr .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationReach body child →
    ValidationReach (.letE name type value body nonDep info) child
  | projectionValue {value child : KExpr .anon} {id : KId .anon}
      {field : UInt64} {info : ExprInfo .anon} :
    ValidationReach value child →
    ValidationReach (.prj id field value info) child

namespace ValidationReach

/-- Expression validation reach composes. -/
theorem trans {root middle child : KExpr .anon}
    (hroot : ValidationReach root middle)
    (hmiddle : ValidationReach middle child) :
    ValidationReach root child := by
  induction hroot with
  | refl => exact hmiddle
  | appFn _ ih => exact .appFn (ih hmiddle)
  | appArg _ ih => exact .appArg (ih hmiddle)
  | lamType _ ih => exact .lamType (ih hmiddle)
  | lamBody _ ih => exact .lamBody (ih hmiddle)
  | allType _ ih => exact .allType (ih hmiddle)
  | allBody _ ih => exact .allBody (ih hmiddle)
  | letType _ ih => exact .letType (ih hmiddle)
  | letValue _ ih => exact .letValue (ih hmiddle)
  | letBody _ ih => exact .letBody (ih hmiddle)
  | projectionValue _ ih => exact .projectionValue (ih hmiddle)

/-- A direct expression-validator work item is structurally reachable. -/
theorem childAt {parent child : KExpr .anon} {parentDepth childDepth : UInt64}
    (hchild : (child, childDepth) ∈
      parent.validationChildrenAt parentDepth) :
    ValidationReach parent child := by
  cases parent with
  | var | fvar | sort | const | nat | str =>
      simp [validationChildrenAt] at hchild
  | app fn arg info =>
      simp [validationChildrenAt] at hchild
      rcases hchild with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .appArg (.refl _)
      · exact .appFn (.refl _)
  | lam name bi type body info =>
      simp [validationChildrenAt] at hchild
      rcases hchild with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .lamBody (.refl _)
      · exact .lamType (.refl _)
  | all name bi type body info =>
      simp [validationChildrenAt] at hchild
      rcases hchild with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .allBody (.refl _)
      · exact .allType (.refl _)
  | letE name type value body nonDep info =>
      simp [validationChildrenAt] at hchild
      rcases hchild with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .letBody (.refl _)
      · exact .letValue (.refl _)
      · exact .letType (.refl _)
  | prj id field value info =>
      simp only [validationChildrenAt, List.mem_singleton, Prod.mk.injEq]
        at hchild
      rcases hchild with ⟨rfl, rfl⟩
      exact .projectionValue (.refl _)

end ValidationReach

/-- Universe nodes reachable from an expression, including every structural
descendant of each sort level or constant universe argument. -/
inductive ValidationUnivReach : KExpr .anon → KUniv .anon → Prop
  | sort {root child : KUniv .anon} {info : ExprInfo .anon} :
    KUniv.ValidationReach root child →
    ValidationUnivReach (.sort root info) child
  | const {levels : Array (KUniv .anon)} {root child : KUniv .anon}
      {id : KId .anon} {info : ExprInfo .anon} :
    root ∈ levels →
    KUniv.ValidationReach root child →
    ValidationUnivReach (.const id levels info) child
  | appFn {fn arg : KExpr .anon} {level : KUniv .anon}
      {info : ExprInfo .anon} :
    ValidationUnivReach fn level →
    ValidationUnivReach (.app fn arg info) level
  | appArg {fn arg : KExpr .anon} {level : KUniv .anon}
      {info : ExprInfo .anon} :
    ValidationUnivReach arg level →
    ValidationUnivReach (.app fn arg info) level
  | lamType {type body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationUnivReach type level →
    ValidationUnivReach (.lam name bi type body info) level
  | lamBody {type body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationUnivReach body level →
    ValidationUnivReach (.lam name bi type body info) level
  | allType {type body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationUnivReach type level →
    ValidationUnivReach (.all name bi type body info) level
  | allBody {type body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {info : ExprInfo .anon} :
    ValidationUnivReach body level →
    ValidationUnivReach (.all name bi type body info) level
  | letType {type value body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationUnivReach type level →
    ValidationUnivReach (.letE name type value body nonDep info) level
  | letValue {type value body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationUnivReach value level →
    ValidationUnivReach (.letE name type value body nonDep info) level
  | letBody {type value body : KExpr .anon} {level : KUniv .anon}
      {name : Mode.anon.F Name} {nonDep : Bool}
      {info : ExprInfo .anon} :
    ValidationUnivReach body level →
    ValidationUnivReach (.letE name type value body nonDep info) level
  | projectionValue {value : KExpr .anon} {level : KUniv .anon}
      {id : KId .anon} {field : UInt64} {info : ExprInfo .anon} :
    ValidationUnivReach value level →
    ValidationUnivReach (.prj id field value info) level

namespace ValidationUnivReach

/-- Universe reach remains inside the expression footprint when descending
further through a universe node. -/
theorem trans {root : KExpr .anon} {level child : KUniv .anon}
    (hlevel : ValidationUnivReach root level)
    (hchild : KUniv.ValidationReach level child) :
    ValidationUnivReach root child := by
  induction hlevel with
  | sort hreach => exact .sort (hreach.trans hchild)
  | const hmem hreach => exact .const hmem (hreach.trans hchild)
  | appFn _ ih => exact .appFn (ih hchild)
  | appArg _ ih => exact .appArg (ih hchild)
  | lamType _ ih => exact .lamType (ih hchild)
  | lamBody _ ih => exact .lamBody (ih hchild)
  | allType _ ih => exact .allType (ih hchild)
  | allBody _ ih => exact .allBody (ih hchild)
  | letType _ ih => exact .letType (ih hchild)
  | letValue _ ih => exact .letValue (ih hchild)
  | letBody _ ih => exact .letBody (ih hchild)
  | projectionValue _ ih => exact .projectionValue (ih hchild)

end ValidationUnivReach

namespace ValidationReach

/-- Universe reach lifts through an expression-reach path. -/
theorem validationUniv
    {root nested : KExpr .anon} {level : KUniv .anon}
    (hroot : ValidationReach root nested)
    (hnested : ValidationUnivReach nested level) :
    ValidationUnivReach root level := by
  induction hroot with
  | refl => exact hnested
  | appFn _ ih => exact .appFn (ih hnested)
  | appArg _ ih => exact .appArg (ih hnested)
  | lamType _ ih => exact .lamType (ih hnested)
  | lamBody _ ih => exact .lamBody (ih hnested)
  | allType _ ih => exact .allType (ih hnested)
  | allBody _ ih => exact .allBody (ih hnested)
  | letType _ ih => exact .letType (ih hnested)
  | letValue _ ih => exact .letValue (ih hnested)
  | letBody _ ih => exact .letBody (ih hnested)
  | projectionValue _ ih => exact .projectionValue (ih hnested)

/-- A direct universe root at a reachable expression node belongs to the
root expression's universe footprint. -/
theorem univRoot
    {root nested : KExpr .anon} {level : KUniv .anon}
    (hroot : ValidationReach root nested)
    (hlevel : level ∈ nested.validationUnivRoots) :
    ValidationUnivReach root level := by
  apply hroot.validationUniv
  cases nested with
  | var | fvar | app | lam | all | letE | prj | nat | str =>
      simp [validationUnivRoots] at hlevel
  | sort level info =>
      simp only [validationUnivRoots, List.mem_singleton] at hlevel
      subst level
      exact .sort (.refl _)
  | const id levels info =>
      exact .const (by simpa [validationUnivRoots] using hlevel) (.refl _)

end ValidationReach

/-- The local expression guard checked when a `(node, depth)` key is first
inserted into the memo set. -/
def ValidationLocal (depth : UInt64) : KExpr .anon → Prop
  | .var idx _ _ => idx < depth
  | _ => True

/-- A finite run support covers the exact syntax footprint of one expression
validation. -/
structure ValidationCoverage (support : RunSupport)
    (root : KExpr .anon) : Prop where
  expr : ∀ ⦃candidate⦄, ValidationReach root candidate → support candidate
  univ : ∀ ⦃level⦄, ValidationUnivReach root level → support.univ level

namespace ValidationCoverage

theorem root {support : RunSupport} {root : KExpr .anon}
    (h : ValidationCoverage support root) : support root :=
  h.expr (.refl root)

/-- The universes embedded in an expression validation form a child-closed
domain covered by the same finite run support. -/
theorem univDomain {support : RunSupport} {root : KExpr .anon}
    (h : ValidationCoverage support root) :
    KUniv.ValidationDomain support (ValidationUnivReach root) where
  covered := h.univ
  child := fun {_ _} hparent hchild =>
    hparent.trans (.child hchild)

end ValidationCoverage

end KExpr

end Ix.Tc
