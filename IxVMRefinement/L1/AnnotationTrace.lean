import IxVMRefinement.L1.BinderTree
import IxVMRefinement.L1.BinderFlag

/-! # Serialized annotation traces

The trace lists binder levels in the expanded expression's traversal order. Shared expressions
select their own serialized node block; ordinary child expressions consume no nodes when their
structural binder flag is zero.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The pure node-consumption operation performed by annotated conversion. -/
def binderPlanStep (tree : BinderTreeData) (sharing : List Ixon.Expr) (bound : Nat)
    (expr : Ixon.Expr) (nodes : List Ixon.BinderNode) :
    Option (List Core.KLevel × List Ixon.BinderNode) :=
  match expr with
  | .lam dom body | .all dom body => do
    let node :: rest := nodes | none
    let (domPlan, afterDom) ← if needsBinderAt sharing bound dom then
      binderPlanStep tree sharing bound dom rest else some ([], rest)
    let (bodyPlan, afterBody) ← if needsBinderAt sharing bound body then
      binderPlanStep tree sharing bound body afterDom else some ([], afterDom)
    return (binderLevel node :: (domPlan ++ bodyPlan), afterBody)
  | .app func arg => do
    let (funcPlan, afterFunc) ← if needsBinderAt sharing bound func then
      binderPlanStep tree sharing bound func nodes else some ([], nodes)
    let (argPlan, afterArg) ← if needsBinderAt sharing bound arg then
      binderPlanStep tree sharing bound arg afterFunc else some ([], afterFunc)
    return (funcPlan ++ argPlan, afterArg)
  | .letE _ _ ty value body => do
    let (typePlan, afterType) ← if needsBinderAt sharing bound ty then
      binderPlanStep tree sharing bound ty nodes else some ([], nodes)
    let (valuePlan, afterValue) ← if needsBinderAt sharing bound value then
      binderPlanStep tree sharing bound value afterType else some ([], afterType)
    let (bodyPlan, afterBody) ← if needsBinderAt sharing bound body then
      binderPlanStep tree sharing bound body afterValue else some ([], afterValue)
    return ((typePlan ++ valuePlan) ++ bodyPlan, afterBody)
  | .prj _ _ inner => binderPlanStep tree sharing bound inner nodes
  | .share index => do
    if hindex : index.toNat < bound then
      let body ← sharing[index.toNat]?
      let .share variant :: rest := nodes | none
      let entryNodes ← tree.lookup (1, (index.toNat : F), (variant.toNat : F))
      let (plan, afterEntry) ← binderPlanStep tree sharing index.toNat body entryNodes
      match afterEntry with
      | [] => return (plan, rest)
      | _ => none
    else none
  | _ => none
termination_by (bound, sizeOf expr)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Root conversion uses either no annotation block, or the complete root block at variant0. -/
def binderRootPlan (tree : BinderTreeData) (sharing : List Ixon.Expr) (root : F)
    (expr : Ixon.Expr) : Option (List Core.KLevel) := do
  if needsBinderAt sharing 4294967295 expr then
    let nodes ← tree.lookup (0, root, 0)
    let (plan, remaining) ← binderPlanStep tree sharing 4294967295 expr nodes
    match remaining with
    | [] => return plan
    | _ => none
  else return []

/-- The exact binder levels carried by a heap expression, before its lets are expanded. -/
inductive HeapBinderLevels (h : Heap F) : SourceValue F → List Core.KLevel → Prop where
  | bvar {addr : Nat} {index : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "BVar" [index])) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) []
  | sort {addr : Nat} {level : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Srt" [level])) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) []
  | const {addr : Nat} {name levels : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Const" [name, levels])) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) []
  | lit {addr : Nat} {value : SourceValue F}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Lit" [value])) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) []
  | app {addr : Nat} {func arg : SourceValue F} {funcPlan argPlan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.kexprEnum "App" [func, arg]))
      (function : HeapBinderLevels h func funcPlan) (argument : HeapBinderLevels h arg argPlan) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) (funcPlan ++ argPlan)
  | lam {addr : Nat} {dom body level : SourceValue F} {u : Core.KLevel}
      {domPlan bodyPlan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Lam" [dom, body, level]))
      (levelRep : KernelLevels.RepKLevel h u level)
      (domain : HeapBinderLevels h dom domPlan) (range : HeapBinderLevels h body bodyPlan) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) (u :: (domPlan ++ bodyPlan))
  | forallE {addr : Nat} {dom body level : SourceValue F} {u : Core.KLevel}
      {domPlan bodyPlan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Forall" [dom, body, level]))
      (levelRep : KernelLevels.RepKLevel h u level)
      (domain : HeapBinderLevels h dom domPlan) (range : HeapBinderLevels h body bodyPlan) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) (u :: (domPlan ++ bodyPlan))
  | letE {addr : Nat} {ty value body : SourceValue F} {typePlan valuePlan bodyPlan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Let" [ty, value, body]))
      (type : HeapBinderLevels h ty typePlan) (value : HeapBinderLevels h value valuePlan)
      (body : HeapBinderLevels h body bodyPlan) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) ((typePlan ++ valuePlan) ++ bodyPlan)
  | proj {addr : Nat} {name index inner : SourceValue F} {plan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.kexprEnum "Proj" [name, index, inner]))
      (value : HeapBinderLevels h inner plan) :
      HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan

theorem HeapBinderLevels.mono {h h' : Heap F} {ptr : SourceValue F} {plan : List Core.KLevel}
    (extended : Heap.Extends h h') (levels : HeapBinderLevels h ptr plan) :
    HeapBinderLevels h' ptr plan := by
  induction levels with
  | bvar cell => exact .bvar (extended.getElem?_eq cell)
  | sort cell => exact .sort (extended.getElem?_eq cell)
  | const cell => exact .const (extended.getElem?_eq cell)
  | lit cell => exact .lit (extended.getElem?_eq cell)
  | app cell _ _ func arg => exact .app (extended.getElem?_eq cell) func arg
  | lam cell level _ _ dom body => exact .lam (extended.getElem?_eq cell) (level.mono extended) dom body
  | forallE cell level _ _ dom body => exact .forallE (extended.getElem?_eq cell) (level.mono extended) dom body
  | letE cell _ _ _ ty value body => exact .letE (extended.getElem?_eq cell) ty value body
  | proj cell _ value => exact .proj (extended.getElem?_eq cell) value

end IxVM.Refinement.L1
