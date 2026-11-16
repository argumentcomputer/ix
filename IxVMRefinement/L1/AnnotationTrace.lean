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
    if _hindex : index.toNat < bound then
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

theorem binderPlanStep_app {tree : BinderTreeData} {sharing : List Ixon.Expr} {bound : Nat}
    {func arg : Ixon.Expr} {nodes middle remaining : List Ixon.BinderNode}
    {funcPlan argPlan : List Core.KLevel}
    (function : (if needsBinderAt sharing bound func then binderPlanStep tree sharing bound func nodes
      else some ([], nodes)) = some (funcPlan, middle))
    (argument : (if needsBinderAt sharing bound arg then binderPlanStep tree sharing bound arg middle
      else some ([], middle)) = some (argPlan, remaining)) :
    binderPlanStep tree sharing bound (.app func arg) nodes = some (funcPlan ++ argPlan, remaining) := by
  split at function <;> split at argument <;> simp_all [binderPlanStep]

theorem binderPlanStep_lam {tree : BinderTreeData} {sharing : List Ixon.Expr} {bound : Nat}
    {dom body : Ixon.Expr} {node : Ixon.BinderNode} {nodes middle remaining : List Ixon.BinderNode}
    {domPlan bodyPlan : List Core.KLevel}
    (domain : (if needsBinderAt sharing bound dom then binderPlanStep tree sharing bound dom nodes
      else some ([], nodes)) = some (domPlan, middle))
    (range : (if needsBinderAt sharing bound body then binderPlanStep tree sharing bound body middle
      else some ([], middle)) = some (bodyPlan, remaining)) :
    binderPlanStep tree sharing bound (.lam dom body) (node :: nodes) =
      some (binderLevel node :: (domPlan ++ bodyPlan), remaining) := by
  split at domain <;> split at range <;> simp_all [binderPlanStep]

theorem binderPlanStep_all {tree : BinderTreeData} {sharing : List Ixon.Expr} {bound : Nat}
    {dom body : Ixon.Expr} {node : Ixon.BinderNode} {nodes middle remaining : List Ixon.BinderNode}
    {domPlan bodyPlan : List Core.KLevel}
    (domain : (if needsBinderAt sharing bound dom then binderPlanStep tree sharing bound dom nodes
      else some ([], nodes)) = some (domPlan, middle))
    (range : (if needsBinderAt sharing bound body then binderPlanStep tree sharing bound body middle
      else some ([], middle)) = some (bodyPlan, remaining)) :
    binderPlanStep tree sharing bound (.all dom body) (node :: nodes) =
      some (binderLevel node :: (domPlan ++ bodyPlan), remaining) := by
  split at domain <;> split at range <;> simp_all [binderPlanStep]

theorem binderPlanStep_let {tree : BinderTreeData} {sharing : List Ixon.Expr} {bound : Nat}
    {nondependent : Bool} {mode : Ixon.LetMode} {ty value body : Ixon.Expr}
    {nodes afterType afterValue remaining : List Ixon.BinderNode}
    {typePlan valuePlan bodyPlan : List Core.KLevel}
    (type : (if needsBinderAt sharing bound ty then binderPlanStep tree sharing bound ty nodes
      else some ([], nodes)) = some (typePlan, afterType))
    (value : (if needsBinderAt sharing bound value then binderPlanStep tree sharing bound value afterType
      else some ([], afterType)) = some (valuePlan, afterValue))
    (body : (if needsBinderAt sharing bound body then binderPlanStep tree sharing bound body afterValue
      else some ([], afterValue)) = some (bodyPlan, remaining)) :
    binderPlanStep tree sharing bound (.letE nondependent mode ty value body) nodes =
      some ((typePlan ++ valuePlan) ++ bodyPlan, remaining) := by
  split at type <;> split at value <;> split at body <;> simp_all [binderPlanStep]

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

/-- A heap leaf contributes no binder annotations. -/
theorem HeapBinderLevels.leaf_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {ctor : String} {fields : List (SourceValue F)}
    (leaf : ctor = "BVar" ∨ ctor = "Srt" ∨ ctor = "Const" ∨ ctor = "Lit")
    (cell : h[addr]? = some (.construct Core.kexprEnum ctor fields))
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) : plan = [] := by
  rcases leaf with rfl | rfl | rfl | rfl
  all_goals cases levels <;> simp_all

theorem HeapBinderLevels.app_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {func arg : SourceValue F}
    (cell : h[addr]? = some (.construct Core.kexprEnum "App" [func, arg]))
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) :
    ∃ funcPlan argPlan, plan = funcPlan ++ argPlan ∧
      HeapBinderLevels h func funcPlan ∧ HeapBinderLevels h arg argPlan := by
  cases levels with
  | app observed function argument =>
    have fields := Option.some.inj (cell.symm.trans observed)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
    obtain ⟨rfl, rfl⟩ := fields
    exact ⟨_, _, rfl, function, argument⟩
  | bvar observed | sort observed | const observed | lit observed
  | lam observed _ _ _ | forallE observed _ _ _ | letE observed _ _ _ | proj observed _ =>
    rw [cell] at observed
    simp at observed

theorem HeapBinderLevels.lam_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {dom body levelPtr : SourceValue F} {level : Core.KLevel}
    (cell : h[addr]? = some (.construct Core.kexprEnum "Lam" [dom, body, levelPtr]))
    (levelRep : KernelLevels.RepKLevel h level levelPtr)
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) :
    ∃ domPlan bodyPlan, plan = level :: (domPlan ++ bodyPlan) ∧
      HeapBinderLevels h dom domPlan ∧ HeapBinderLevels h body bodyPlan := by
  cases levels with
  | lam observed actual domain range =>
    have fields := Option.some.inj (cell.symm.trans observed)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
    obtain ⟨rfl, rfl, rfl⟩ := fields
    have same := actual.det levelRep
    cases same
    exact ⟨_, _, rfl, domain, range⟩
  | bvar observed | sort observed | const observed | lit observed | app observed _ _
  | forallE observed _ _ _ | letE observed _ _ _ | proj observed _ =>
    rw [cell] at observed
    simp at observed

theorem HeapBinderLevels.forall_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {dom body levelPtr : SourceValue F} {level : Core.KLevel}
    (cell : h[addr]? = some (.construct Core.kexprEnum "Forall" [dom, body, levelPtr]))
    (levelRep : KernelLevels.RepKLevel h level levelPtr)
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) :
    ∃ domPlan bodyPlan, plan = level :: (domPlan ++ bodyPlan) ∧
      HeapBinderLevels h dom domPlan ∧ HeapBinderLevels h body bodyPlan := by
  cases levels with
  | forallE observed actual domain range =>
    have fields := Option.some.inj (cell.symm.trans observed)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
    obtain ⟨rfl, rfl, rfl⟩ := fields
    have same := actual.det levelRep
    cases same
    exact ⟨_, _, rfl, domain, range⟩
  | bvar observed | sort observed | const observed | lit observed | app observed _ _
  | lam observed _ _ _ | letE observed _ _ _ | proj observed _ =>
    rw [cell] at observed
    simp at observed

theorem HeapBinderLevels.let_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {ty value body : SourceValue F}
    (cell : h[addr]? = some (.construct Core.kexprEnum "Let" [ty, value, body]))
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) :
    ∃ typePlan valuePlan bodyPlan, plan = (typePlan ++ valuePlan) ++ bodyPlan ∧
      HeapBinderLevels h ty typePlan ∧ HeapBinderLevels h value valuePlan ∧
      HeapBinderLevels h body bodyPlan := by
  cases levels with
  | letE observed type value body =>
    have fields := Option.some.inj (cell.symm.trans observed)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
    obtain ⟨rfl, rfl, rfl⟩ := fields
    exact ⟨_, _, _, rfl, type, value, body⟩
  | bvar observed | sort observed | const observed | lit observed | app observed _ _
  | lam observed _ _ _ | forallE observed _ _ _ | proj observed _ =>
    rw [cell] at observed
    simp at observed

theorem HeapBinderLevels.proj_inv {h : Heap F} {addr : Nat} {plan : List Core.KLevel}
    {name index inner : SourceValue F}
    (cell : h[addr]? = some (.construct Core.kexprEnum "Proj" [name, index, inner]))
    (levels : HeapBinderLevels h (.ptr (.enum Core.kexprEnum) addr) plan) :
    HeapBinderLevels h inner plan := by
  cases levels with
  | proj observed value =>
    have fields := Option.some.inj (cell.symm.trans observed)
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at fields
    obtain ⟨rfl, rfl, rfl⟩ := fields
    exact value
  | bvar observed | sort observed | const observed | lit observed | app observed _ _
  | lam observed _ _ _ | forallE observed _ _ _ | letE observed _ _ _ =>
    rw [cell] at observed
    simp at observed

/-- Apply a positional binder trace to the reader expression. The metadata mapping permits
both range parameters and inverse positional naming. Let components are traversed before
zeta expansion, matching conversion's annotation order. -/
def applyBinderTrace (metadata : Core.KLevel → Ix.Kernel.BinderMeta) :
    Core.KExpr → List Core.KLevel → Option (Core.KExpr × List Core.KLevel)
  | .bvar index, levels => some (.bvar index, levels)
  | .fvar index ty, levels => do
    let (ty', remaining) ← applyBinderTrace metadata ty levels
    return (.fvar index ty', remaining)
  | .sort level, levels => some (.sort level, levels)
  | .const name args, levels => some (.const name args, levels)
  | .lit value, levels => some (.lit value, levels)
  | .app func arg, levels => do
    let (func', afterFunc) ← applyBinderTrace metadata func levels
    let (arg', afterArg) ← applyBinderTrace metadata arg afterFunc
    return (.app func' arg', afterArg)
  | .lam dom body _, levels => do
    let level :: remaining := levels | none
    let (dom', afterDom) ← applyBinderTrace metadata dom remaining
    let (body', afterBody) ← applyBinderTrace metadata body afterDom
    return (.lam dom' body' (metadata level), afterBody)
  | .forallE dom body _, levels => do
    let level :: remaining := levels | none
    let (dom', afterDom) ← applyBinderTrace metadata dom remaining
    let (body', afterBody) ← applyBinderTrace metadata body afterDom
    return (.forallE dom' body' (metadata level), afterBody)
  | .letE ty value body _, levels => do
    let (_, afterType) ← applyBinderTrace metadata ty levels
    let (value', afterValue) ← applyBinderTrace metadata value afterType
    let (body', afterBody) ← applyBinderTrace metadata body afterValue
    return (body'.instantiate1Lift value' 0, afterBody)
  | .proj name index inner, levels => do
    let (inner', remaining) ← applyBinderTrace metadata inner levels
    return (.proj name index inner', remaining)

/-- Applying one fixed trace cannot choose different annotations. -/
theorem applyBinderTrace_unique {metadata : Core.KLevel → Ix.Kernel.BinderMeta}
    {expr left right : Core.KExpr} {levels leftRest rightRest : List Core.KLevel}
    (first : applyBinderTrace metadata expr levels = some (left, leftRest))
    (second : applyBinderTrace metadata expr levels = some (right, rightRest)) :
    left = right ∧ leftRest = rightRest :=
  Prod.mk.inj (Option.some.inj (first.symm.trans second))

end IxVM.Refinement.L1
