/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler.CallOrder
import Ix.Aiur.Semantics.AIR

/-! Every constrained request in local AIR execution occurs in the
syntactic call collector used by the checked component certificate. The
certificate supplies endpoint bounds, component order and call rank modes. -/

namespace Aiur.Bytecode

def Op.constrainedCalls : Op → List FunIdx
  | .call function _ _ false => [function]
  | _ => []

private theorem opFold_calls (ops : List Op) (acc : Array FunIdx) :
    (ops.foldl (fun acc op => match op with
      | .call function _ _ false => acc.push function | _ => acc) acc).toList =
      acc.toList ++ ops.flatMap Op.constrainedCalls := by
  induction ops generalizing acc with
  | nil => simp
  | cons op ops ih =>
    simp only [List.foldl_cons, ih, List.flatMap_cons]
    cases op <;> try rfl
    rename_i function indices size unconstrained
    cases unconstrained <;> simp [Op.constrainedCalls, Array.toList_push, List.append_assoc]

theorem Block.collect_calls (block : Block) :
    block.collectConstrainedCallees.toList =
      block.ops.toList.flatMap Op.constrainedCalls ++ block.ctrl.collectConstrainedCallees.toList := by
  rw [Block.collectConstrainedCallees]
  simp only [Array.toList_append, ← Array.foldl_toList]
  exact congrArg (· ++ block.ctrl.collectConstrainedCallees.toList) (opFold_calls block.ops.toList #[])

private theorem branchFold_calls (items : List (G × Block)) (acc : Array FunIdx) :
    (items.foldl (fun acc pair => acc ++ pair.2.collectConstrainedCallees) acc).toList =
      acc.toList ++ items.flatMap (fun pair => pair.2.collectConstrainedCallees.toList) := by
  induction items generalizing acc with
  | nil => simp
  | cons pair items ih => simp [List.foldl_cons, ih, List.append_assoc]

private theorem branchArray_calls (branches : Array (G × Block)) :
    (branches.attach.foldl (fun acc pair => acc ++ pair.val.2.collectConstrainedCallees) #[]).toList =
      branches.toList.flatMap (fun pair => pair.2.collectConstrainedCallees.toList) := by
  rw [← Array.foldl_toList]
  have mapped := List.foldl_map (f := fun (pair : { x // x ∈ branches }) => pair.val)
    (g := fun (acc : Array FunIdx) pair => acc ++ pair.2.collectConstrainedCallees)
    (l := branches.attach.toList) (init := #[])
  rw [← mapped]
  have values : branches.attach.toList.map (fun pair => pair.val) = branches.toList := by
    rw [Array.toList_attach, List.attachWith_map_subtype_val]
  rw [values, branchFold_calls]
  rfl

def branchCalls (branches : Array (G × Block)) (fallback : Option Block) : List FunIdx :=
  branches.toList.flatMap (fun pair => pair.2.collectConstrainedCallees.toList) ++
    fallback.toList.flatMap (fun block => block.collectConstrainedCallees.toList)

theorem Ctrl.collect_match (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).collectConstrainedCallees.toList = branchCalls branches fallback := by
  rw [Ctrl.collectConstrainedCallees.eq_def]
  cases fallback <;> simp [branchCalls]
  all_goals simpa only [Array.size_attach] using branchArray_calls branches

theorem Ctrl.collect_continue (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block)
    (size aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback size aux lookups continuation).collectConstrainedCallees.toList =
      branchCalls branches fallback ++ continuation.collectConstrainedCallees.toList := by
  rw [Ctrl.collectConstrainedCallees.eq_def]
  cases fallback <;> simp [branchCalls, List.append_assoc]
  all_goals simpa only [Array.size_attach] using branchArray_calls branches

namespace AIR

theorem Step.calls_collected {memory : Memory} {op : Op} {values outputs : Array G} {calls : List Call}
    (execution : Step memory op values outputs calls) : ∀ child ∈ calls, child.function ∈ op.constrainedCalls := by
  intro child member
  cases execution with
  | primitive _ => cases member
  | call _ _ => simp only [List.mem_singleton.mp member, Op.constrainedCalls, List.mem_singleton]
  | store _ _ => cases member
  | load _ _ _ => cases member

theorem RunOps.calls_collected {memory : Memory} {ops : List Op} {values outputs : Array G} {calls : List Call}
    (execution : RunOps memory ops values outputs calls) :
    ∀ child ∈ calls, child.function ∈ ops.flatMap Op.constrainedCalls := by
  induction execution with
  | nil => intro child member; cases member
  | @cons op ops values intermediate firstCalls outputs restCalls first rest ih =>
    intro child member
    simp only [List.flatMap_cons]
    rcases List.mem_append.mp member with head | tail
    · exact List.mem_append_left _ (first.calls_collected child head)
    · exact List.mem_append_right _ (ih child tail)

theorem SelectArm.calls_collected {scrutinee : G} {branches : Array (G × Block)}
    {fallback : Option Block} {arm : Block} (selected : SelectArm scrutinee branches fallback arm) :
    arm.collectConstrainedCallees.toList ⊆ branchCalls branches fallback := by
  intro child member
  cases selected with
  | case present =>
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, present, member⟩)
  | fallback present _ =>
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨arm, by simp [present], member⟩)

theorem RunBlock.calls_collected {memory : Memory} {block : Block} {values : Array G}
    {outcome : Outcome} {calls : List Call} (execution : RunBlock memory block values outcome calls) :
    ∀ child ∈ calls, child.function ∈ block.collectConstrainedCallees.toList := by
  induction execution using RunBlock.rec
    (motive_2 := fun ctrl _ _ calls _ => ∀ child ∈ calls, child.function ∈ ctrl.collectConstrainedCallees.toList) with
  | block operations control ih =>
    intro child member
    rw [Block.collect_calls]
    rcases List.mem_append.mp member with first | last
    · exact List.mem_append_left _ (operations.calls_collected child first)
    · exact List.mem_append_right _ (ih child last)
  | returned _ child member => cases member
  | yielded _ child member => cases member
  | «match» value selected branch ih child member =>
    rw [Ctrl.collect_match]
    exact selected.calls_collected (ih child member)
  | matchContinueReturn value selected branch ih child member =>
    rw [Ctrl.collect_continue]
    exact List.mem_append_left _ (selected.calls_collected (ih child member))
  | matchContinueYield value selected branch outputSize continued ihBranch ihCont child member =>
    rw [Ctrl.collect_continue]
    rcases List.mem_append.mp member with first | last
    · exact List.mem_append_left _ (selected.calls_collected (ihBranch child first))
    · exact List.mem_append_right _ (ihCont child last)

end AIR

theorem Toplevel.validCallComponents_size {program : Toplevel}
    (valid : program.validCallComponents = true) : program.callComponents.size = program.functions.size := by
  simp only [Toplevel.validCallComponents, Bool.and_eq_true, beq_iff_eq] at valid
  exact valid.1.1

theorem Toplevel.validCallComponents_order {program : Toplevel}
    (valid : program.validCallComponents = true) {index : Nat} {component : CallComponent}
    (present : program.callComponents[index]? = some component) : component.order < program.functions.size := by
  simp only [Toplevel.validCallComponents, Bool.and_eq_true] at valid
  have bounds := valid.1.2
  exact decide_eq_true_eq.mp (Array.all_eq_true'.mp bounds component (Array.mem_of_getElem? present))

def Toplevel.ComponentEdge (program : Toplevel) (parent child : FunIdx) : Prop :=
  ∃ parentComponent childComponent,
    program.callComponents[parent]? = some parentComponent ∧
    program.callComponents[child]? = some childComponent ∧ parentComponent.permits childComponent = true

theorem Toplevel.validCallComponents_edge {program : Toplevel}
    (valid : program.validCallComponents = true) {parent child : FunIdx} {function : Function}
    (present : program.functions[parent]? = some function) (constrained : function.constrained = true)
    (called : child ∈ function.body.collectConstrainedCallees.toList) : program.ComponentEdge parent child := by
  simp only [Toplevel.validCallComponents, Bool.and_eq_true] at valid
  have functions := valid.2
  obtain ⟨bound, rfl⟩ := Array.getElem?_eq_some_iff.mp present
  have atParent := Array.all_eq_true'.mp functions _
    (Array.getElem_mem (xs := program.functions.mapIdx fun i f => !f.constrained ||
      f.body.collectConstrainedCallees.all (fun j => match program.callComponents[i]?, program.callComponents[j]? with
        | some parent, some child => parent.permits child | _, _ => false))
      (i := parent) (by simpa only [Array.size_mapIdx] using bound))
  simp only [Array.getElem_mapIdx, constrained, Bool.not_true, Bool.false_or, id_eq] at atParent
  have edge := Array.all_eq_true'.mp atParent child (Array.mem_toList_iff.mp called)
  unfold Toplevel.ComponentEdge
  cases parentComponent : program.callComponents[parent]? <;>
    cases childComponent : program.callComponents[child]? <;>
    simp only [parentComponent, childComponent, Bool.false_eq_true] at edge
  exact ⟨_, _, rfl, rfl, edge⟩

theorem AIR.RunFunction.calls_components {program : Toplevel} {memory : AIR.Memory}
    {request : AIR.Call} {calls : List AIR.Call} (execution : AIR.RunFunction program memory request calls)
    (valid : program.validCallComponents = true) {function : Function}
    (present : program.functions[request.function]? = some function) (constrained : function.constrained = true) :
    ∀ child ∈ calls, program.ComponentEdge request.function child.function := by
  cases execution with
  | function selected arity body =>
    have same := Option.some.inj (selected.symm.trans present)
    subst function
    intro child called
    exact Toplevel.validCallComponents_edge valid selected constrained (body.calls_collected child called)

theorem Toplevel.callRanksFor_read {program : Toplevel} {parent child : FunIdx}
    {parentComponent childComponent : CallComponent}
    (parentPresent : program.callComponents[parent]? = some parentComponent)
    (childPresent : program.callComponents[child]? = some childComponent) :
    (program.callRanksFor parent)[child]? = some
      (if parentComponent.order == childComponent.order then .ordered
        else if childComponent.ranked then .bound else .zero) := by
  simp only [Toplevel.callRanksFor, Array.getElem?_map, childPresent, Option.map_some]
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, parentPresent]
  rfl

theorem CallComponent.permits_same {parent child : CallComponent}
    (permitted : parent.permits child = true) (same : parent.order = child.order) :
    parent.ranked = true ∧ child.ranked = true := by
  simpa only [CallComponent.permits, same, Nat.lt_irrefl, decide_false, Bool.false_or,
    BEq.rfl, Bool.true_and, Bool.and_eq_true] using permitted

theorem CallComponent.permits_other {parent child : CallComponent}
    (permitted : parent.permits child = true) (different : parent.order ≠ child.order) :
    parent.order < child.order := by
  simpa only [CallComponent.permits, beq_eq_false_iff_ne.mpr different, Bool.false_and,
    Bool.or_false, decide_eq_true_eq] using permitted

theorem Toplevel.ComponentEdge.ordered {program : Toplevel} {parent child : FunIdx}
    (edge : program.ComponentEdge parent child) {parentComponent childComponent : CallComponent}
    (parentPresent : program.callComponents[parent]? = some parentComponent)
    (childPresent : program.callComponents[child]? = some childComponent)
    (same : parentComponent.order = childComponent.order) :
    parentComponent.ranked = true ∧ childComponent.ranked = true ∧
      (program.callRanksFor parent)[child]? = some .ordered := by
  obtain ⟨a, b, parentRead, childRead, permitted⟩ := edge
  have sameParent := Option.some.inj (parentRead.symm.trans parentPresent)
  have sameChild := Option.some.inj (childRead.symm.trans childPresent)
  subst a b
  obtain ⟨parentRanked, childRanked⟩ := CallComponent.permits_same permitted same
  refine ⟨parentRanked, childRanked, ?_⟩
  simpa only [same, BEq.rfl, if_true] using Toplevel.callRanksFor_read parentPresent childPresent

theorem Toplevel.ComponentEdge.cross {program : Toplevel} {parent child : FunIdx}
    (edge : program.ComponentEdge parent child) {parentComponent childComponent : CallComponent}
    (parentPresent : program.callComponents[parent]? = some parentComponent)
    (childPresent : program.callComponents[child]? = some childComponent)
    (different : parentComponent.order ≠ childComponent.order) :
    parentComponent.order < childComponent.order ∧
      (program.callRanksFor parent)[child]? = some (if childComponent.ranked then .bound else .zero) := by
  obtain ⟨a, b, parentRead, childRead, permitted⟩ := edge
  have sameParent := Option.some.inj (parentRead.symm.trans parentPresent)
  have sameChild := Option.some.inj (childRead.symm.trans childPresent)
  subst a b
  refine ⟨CallComponent.permits_other permitted different, ?_⟩
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, if_false] using
    Toplevel.callRanksFor_read parentPresent childPresent

def Toplevel.componentFor (program : Toplevel) (function : FunIdx) : CallComponent :=
  program.callComponents[function]?.getD default

theorem Toplevel.componentFor_read {program : Toplevel} {function : FunIdx} {component : CallComponent}
    (present : program.callComponents[function]? = some component) : program.componentFor function = component := by
  simp only [Toplevel.componentFor, present, Option.getD_some]

theorem Toplevel.ComponentEdge.permits {program : Toplevel} {parent child : FunIdx}
    (edge : program.ComponentEdge parent child) :
    (program.componentFor parent).permits (program.componentFor child) = true := by
  obtain ⟨a, b, parentRead, childRead, permitted⟩ := edge
  simpa only [Toplevel.componentFor_read parentRead, Toplevel.componentFor_read childRead] using permitted

theorem Toplevel.ComponentEdge.rankMode {program : Toplevel} {parent child : FunIdx}
    (edge : program.ComponentEdge parent child)
    (same : (program.componentFor parent).order = (program.componentFor child).order) :
    (program.callRanksFor parent)[child]?.getD .ordered = .ordered := by
  obtain ⟨a, b, parentRead, childRead, _⟩ := edge
  simp only [Toplevel.componentFor_read parentRead, Toplevel.componentFor_read childRead] at same
  rw [Toplevel.callRanksFor_read parentRead childRead]
  simp only [same, BEq.rfl, if_true, Option.getD_some]

theorem Toplevel.validCallComponents_component_order {program : Toplevel}
    (valid : program.validCallComponents = true) {index : FunIdx} {function : Function}
    (present : program.functions[index]? = some function) :
    (program.componentFor index).order < program.functions.size := by
  have bound : index < program.callComponents.size := by
    rw [Toplevel.validCallComponents_size valid]
    exact (Array.getElem?_eq_some_iff.mp present).1
  have read := Array.getElem?_eq_getElem bound
  rw [Toplevel.componentFor_read read]
  exact Toplevel.validCallComponents_order valid read

end Aiur.Bytecode
