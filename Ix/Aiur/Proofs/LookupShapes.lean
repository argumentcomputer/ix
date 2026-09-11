/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.LookupShapes
import Ix.Aiur.Semantics.AIR
import Ix.Aiur.BoundVerifier
import Ix.Aiur.Proofs.CallOrder

/-! A checked return-arity validator implies the output size of every AIR
execution, including early returns and match continuations. -/

namespace Aiur.Bytecode

theorem returnsHaveSize_match (size : Nat) (index : ValIdx) (branches : Array (G × Block))
    (fallback : Option Block) :
    (Ctrl.match index branches fallback).returnsHaveSize size = true ↔
      (∀ pair ∈ branches.toList, pair.2.returnsHaveSize size = true) ∧
        (∀ block, fallback = some block → block.returnsHaveSize size = true) := by
  rw [Ctrl.returnsHaveSize.eq_def]
  simp only [Bool.and_eq_true, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> simp

theorem returnsHaveSize_matchContinue (size : Nat) (index : ValIdx)
    (branches : Array (G × Block)) (fallback : Option Block)
    (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).returnsHaveSize size = true ↔
      (∀ pair ∈ branches.toList, pair.2.returnsHaveSize size = true) ∧
        (∀ block, fallback = some block → block.returnsHaveSize size = true) ∧
        continuation.returnsHaveSize size = true := by
  rw [Ctrl.returnsHaveSize.eq_def]
  simp only [Bool.and_eq_true, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> simp

namespace AIR

/-- A function query uses the input and return boundaries of its selected
callee. Returnless functions satisfy the last check vacuously; they still
need a finite execution before they can provide a return. -/
def Call.LookupShape (program : Toplevel) (request : Call) : Prop :=
  ∃ callee, program.functions[request.function]? = some callee ∧
    callee.constrained = true ∧ callee.layout.inputSize = request.inputs.size ∧
    callee.body.returnsHaveSize request.outputs.size = true

theorem list_mapM_some_length (f : α → Option β) (inputs : List α) (outputs : List β)
    (result : inputs.mapM f = some outputs) : outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at result
           subst outputs; rfl
  | cons input inputs ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at result
    cases head : f input with
    | none => simp only [head, reduceCtorEq] at result
    | some output =>
      cases tail : inputs.mapM f with
      | none => simp only [head, tail, reduceCtorEq] at result
      | some rest =>
        simp only [head, tail, Option.some.injEq] at result
        subst outputs
        simp only [List.length_cons, ih rest tail]

theorem readValues_size {values : Array G} {indices : Array ValIdx} {outputs : Array G}
    (read : readValues values indices = some outputs) : outputs.size = indices.size := by
  have listResult := congrArg (Functor.map Array.toList) read
  rw [readValues, Array.toList_mapM] at listResult
  have sizes := list_mapM_some_length (fun index => values[index]?) indices.toList outputs.toList listResult
  simpa only [Array.length_toList] using sizes

theorem SelectArm.returnsHaveSize {scrutinee : G} {branches : Array (G × Block)}
    {fallback : Option Block} {arm : Block} (selected : SelectArm scrutinee branches fallback arm)
    (size : Nat) (casesValid : ∀ pair ∈ branches.toList, pair.2.returnsHaveSize size = true)
    (fallbackValid : ∀ block, fallback = some block → block.returnsHaveSize size = true) :
    arm.returnsHaveSize size = true := by
  cases selected with
  | case member => exact casesValid _ member
  | fallback present unmatched => exact fallbackValid _ present

def Outcome.ReturnSize (outcome : Outcome) (size : Nat) : Prop :=
  match outcome with
  | .returned outputs => outputs.size = size
  | .yielded _ => True

theorem RunBlock.return_size {memory : Memory} {block : Block} {values : Array G}
    {outcome : Outcome} {calls : List Call} (execution : RunBlock memory block values outcome calls)
    (size : Nat) (valid : block.returnsHaveSize size = true) : outcome.ReturnSize size := by
  revert valid
  induction execution using RunBlock.rec
    (motive_2 := fun ctrl _ outcome _ _ => ctrl.returnsHaveSize size = true → outcome.ReturnSize size) with
  | block operations control ih =>
    intro valid
    apply ih
    simpa only [Block.returnsHaveSize] using valid
  | returned result valid =>
    rw [Ctrl.returnsHaveSize] at valid
    have sized : _ = size := beq_iff_eq.mp valid
    exact (readValues_size result).trans sized
  | yielded result valid => exact True.intro
  | «match» value selected branch ih valid =>
    obtain ⟨casesValid, fallbackValid⟩ := (returnsHaveSize_match _ _ _ _).mp valid
    exact ih (selected.returnsHaveSize size casesValid fallbackValid)
  | matchContinueReturn value selected branch ih valid =>
    obtain ⟨casesValid, fallbackValid, _⟩ := (returnsHaveSize_matchContinue _ _ _ _ _ _ _ _).mp valid
    exact ih (selected.returnsHaveSize size casesValid fallbackValid)
  | matchContinueYield value selected branch outputSize continued ihBranch ihCont valid =>
    obtain ⟨_, _, contValid⟩ := (returnsHaveSize_matchContinue _ _ _ _ _ _ _ _).mp valid
    exact ihCont contValid

theorem RunFunction.return_size {program : Toplevel} {memory : Memory}
    {request : Call} {calls : List Call} (execution : RunFunction program memory request calls)
    {callee : Function} (present : program.functions[request.function]? = some callee)
    (size : Nat) (valid : callee.body.returnsHaveSize size = true) : request.outputs.size = size := by
  cases execution with
  | function selected arity body =>
    have same := Option.some.inj (selected.symm.trans present)
    subst callee
    exact body.return_size size valid

theorem Step.calls_lookupShape {program : Toplevel} {memory : Memory} {op : Op}
    {values outputs : Array G} {calls : List Call} (execution : Step memory op values outputs calls)
    (valid : op.lookupShape program = true) : ∀ request ∈ calls, request.LookupShape program := by
  intro request member
  cases execution with
  | primitive evaluated => cases member
  | call arguments outputSize =>
    have same := List.mem_singleton.mp member
    subst request
    simp only [Op.lookupShape] at valid
    split at valid
    · cases valid
    · rename_i callee present
      obtain ⟨constrained, inputSize, returnSize⟩ :=
        (show _ ∧ _ ∧ _ from by simpa only [Bool.and_eq_true, beq_iff_eq] using valid)
      refine ⟨callee, present, constrained, ?_, ?_⟩
      · exact inputSize.trans (readValues_size arguments).symm
      · simpa only [outputSize] using returnSize
  | store arguments stored => cases member
  | load address width loaded => cases member

theorem RunOps.calls_lookupShape {program : Toplevel} {memory : Memory} {ops : List Op}
    {values outputs : Array G} {calls : List Call} (execution : RunOps memory ops values outputs calls)
    (valid : ∀ op ∈ ops, op.lookupShape program = true) :
    ∀ request ∈ calls, request.LookupShape program := by
  induction execution with
  | nil => intro request member; cases member
  | @cons op ops values intermediate firstCalls finalValues restCalls first rest ih =>
    intro request member
    rcases List.mem_append.mp member with firstMember | restMember
    · exact first.calls_lookupShape (valid op List.mem_cons_self) request firstMember
    · exact ih (fun op member => valid op (List.mem_cons_of_mem _ member)) request restMember

end AIR

theorem lookupShapes_match (program : Toplevel) (yieldSize : Option Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block) :
    (Ctrl.match index branches fallback).lookupShapes program yieldSize = true ↔
      (∀ pair ∈ branches.toList, pair.2.lookupShapes program yieldSize = true) ∧
        (∀ block, fallback = some block → block.lookupShapes program yieldSize = true) := by
  rw [Ctrl.lookupShapes.eq_def]
  simp only [Bool.and_eq_true, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> simp

theorem lookupShapes_matchContinue (program : Toplevel) (yieldSize : Option Nat)
    (index : ValIdx) (branches : Array (G × Block)) (fallback : Option Block)
    (outputs aux lookups : Nat) (continuation : Block) :
    (Ctrl.matchContinue index branches fallback outputs aux lookups continuation).lookupShapes program yieldSize = true ↔
      (∀ pair ∈ branches.toList, pair.2.lookupShapes program (some outputs) = true) ∧
        (∀ block, fallback = some block → block.lookupShapes program (some outputs) = true) ∧
        continuation.lookupShapes program yieldSize = true := by
  rw [Ctrl.lookupShapes.eq_def]
  simp only [Bool.and_eq_true, Array.all_eq_true',
    Array.mem_attach, forall_const, Subtype.forall]
  cases fallback <;> simp

namespace AIR

theorem SelectArm.lookupShapes {scrutinee : G} {branches : Array (G × Block)}
    {fallback : Option Block} {arm : Block} (selected : SelectArm scrutinee branches fallback arm)
    (program : Toplevel) (yieldSize : Option Nat)
    (casesValid : ∀ pair ∈ branches.toList, pair.2.lookupShapes program yieldSize = true)
    (fallbackValid : ∀ block, fallback = some block → block.lookupShapes program yieldSize = true) :
    arm.lookupShapes program yieldSize = true := by
  cases selected with
  | case member => exact casesValid _ member
  | fallback present unmatched => exact fallbackValid _ present

theorem RunBlock.calls_lookupShape {program : Toplevel} {memory : Memory} {block : Block}
    {values : Array G} {outcome : Outcome} {calls : List Call}
    (execution : RunBlock memory block values outcome calls)
    (yieldSize : Option Nat) (valid : block.lookupShapes program yieldSize = true) :
    ∀ request ∈ calls, request.LookupShape program := by
  revert yieldSize valid
  induction execution using RunBlock.rec
    (motive_2 := fun ctrl _ _ calls _ => ∀ yieldSize,
      ctrl.lookupShapes program yieldSize = true →
        ∀ request ∈ calls, request.LookupShape program) with
  | block operations control ih =>
    intro yieldSize valid request member
    obtain ⟨opsValid, ctrlValid⟩ := (show _ ∧ _ from by
      simpa only [Block.lookupShapes, Bool.and_eq_true] using valid)
    rcases List.mem_append.mp member with first | last
    · apply operations.calls_lookupShape _ request first
      simpa only [Array.all_eq_true', Array.mem_def] using opsValid
    · exact ih yieldSize ctrlValid request last
  | returned result yieldSize valid request member => cases member
  | yielded result yieldSize valid request member => cases member
  | «match» value selected branch ih yieldSize valid request member =>
    obtain ⟨casesValid, fallbackValid⟩ := (lookupShapes_match _ _ _ _ _).mp valid
    exact ih yieldSize (selected.lookupShapes program yieldSize casesValid fallbackValid) request member
  | matchContinueReturn value selected branch ih yieldSize valid request member =>
    obtain ⟨casesValid, fallbackValid, _⟩ := (lookupShapes_matchContinue _ _ _ _ _ _ _ _ _).mp valid
    exact ih _ (selected.lookupShapes program _ casesValid fallbackValid) request member
  | matchContinueYield value selected branch outputSize continued ihBranch ihCont yieldSize valid request member =>
    obtain ⟨casesValid, fallbackValid, contValid⟩ := (lookupShapes_matchContinue _ _ _ _ _ _ _ _ _).mp valid
    rcases List.mem_append.mp member with first | last
    · exact ihBranch _ (selected.lookupShapes program _ casesValid fallbackValid) request first
    · exact ihCont yieldSize contValid request last

theorem RunFunction.calls_lookupShape {program : Toplevel} {memory : Memory}
    {request : Call} {calls : List Call} (execution : RunFunction program memory request calls)
    (valid : program.validateLookupShapes = true)
    {callee : Function} (present : program.functions[request.function]? = some callee)
    (constrained : callee.constrained = true) :
    ∀ child ∈ calls, child.LookupShape program := by
  simp only [Toplevel.validateLookupShapes, Bool.and_eq_true] at valid
  have functionsValid := valid.2.2
  have member : callee ∈ program.functions := Array.mem_of_getElem? present
  have bodyValid := Array.all_eq_true'.mp functionsValid callee member
  simp only [constrained, Bool.not_true, Bool.false_or] at bodyValid
  cases execution with
  | function selected arity body =>
    have same := Option.some.inj (selected.symm.trans present)
    subst callee
    exact body.calls_lookupShape none bodyValid

end AIR
end Aiur.Bytecode

namespace Aiur.BoundVerifier

theorem Backend.air_return_size {selection : Selection} (backend : Backend selection)
    {memory : Bytecode.AIR.Memory} {request : Bytecode.AIR.Call}
    {calls : List Bytecode.AIR.Call}
    (execution : Bytecode.AIR.RunFunction backend.compiled.bytecode memory request calls)
    (selected : request.function = selection.function) :
    request.outputs.size = selection.success.size := by
  apply execution.return_size (callee := backend.entry) _ _ backend.returnArity
  simpa only [selected] using backend.present

theorem Backend.claim_shape {selection : Selection} (backend : Backend selection)
    (input : Array G) (arity : input.size = selection.inputSize) :
    backend.compiled.bytecode.validClaimShape
      (buildClaim selection.function input selection.success) = true := by
  simp only [Bytecode.Toplevel.validClaimShape, buildClaim, Array.toList_append,
    List.cons_append, List.nil_append, G.n_ofNat,
    Nat.mod_eq_of_lt backend.functionRange, backend.present, backend.publicEntry,
    backend.constrained, functionChannel, Bool.true_and, Bool.and_true, List.length_append,
    Array.length_toList, backend.arity, arity, Nat.add_sub_cancel_left, backend.returnArity]
  exact decide_eq_true (by omega)

end Aiur.BoundVerifier
