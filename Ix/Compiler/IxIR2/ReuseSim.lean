import Ix.Compiler.IxIR1.EvalIso
import Ix.Compiler.IxIR2.Reuse

/-!
# Semantic seam for dynamic shared reuse

This module connects the concrete IxIR₂ hot-reset stores to the exact
ownership and live-heap isomorphism developed for IxIR₁ heaps.  The local
theorem is deliberately independent of a particular CFG: physical
reservation/reuse is related to logical shallow-free/fresh-allocation for an
arbitrary shared constructor replacement and arbitrary surrounding roots.
-/

namespace Ix.Compiler.IxIR2.ReuseSim

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.IxIR2.Reuse
  (Shape translateRegister? translateAtom? translateAtoms? branchValues)

/-! ## Operand-translation semantics -/

/-- Runtime value files agree at every register mapping accepted by the reuse
planner.  Registers deliberately rejected by `translateRegister?` need no
target counterpart. -/
def ValuesRel (shape : Shape) (source target : Array RVal) : Prop :=
  ∀ sourceId targetId,
    translateRegister? shape sourceId = some targetId →
    source[sourceId]? = target[targetId]?

/-- Every successful register translation is either the distinguished
allocation-result mapping at both file ends, or lies strictly before both
ends. -/
theorem translateRegister?_range {shape : Shape} {sourceId targetId : Nat}
    (sourceBound : shape.source < shape.parameterCount)
    (translated : translateRegister? shape sourceId = some targetId) :
    (sourceId = shape.parameterCount + 2 * shape.fieldCount ∧
      targetId = shape.fieldCount + (shape.parameterCount - 1)) ∨
    (sourceId < shape.parameterCount + 2 * shape.fieldCount ∧
      targetId < shape.fieldCount + (shape.parameterCount - 1)) := by
  have parameterPositive : 0 < shape.parameterCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le shape.source) sourceBound
  unfold translateRegister? at translated
  split at translated
  · have sourceParameter : sourceId < shape.parameterCount := by assumption
    split at translated
    · cases translated
    · split at translated
      · simp only [Option.some.injEq] at translated
        subst targetId
        have beforeSource : sourceId < shape.source := by assumption
        have targetBound : sourceId < shape.parameterCount - 1 :=
          Nat.lt_of_lt_of_le beforeSource
            (Nat.le_sub_one_of_lt sourceBound)
        right
        constructor
        · omega
        · exact Nat.add_lt_add_left targetBound shape.fieldCount
      · simp only [Option.some.injEq] at translated
        subst targetId
        have notBefore : ¬sourceId < shape.source := by assumption
        have notSourceBool : ¬(sourceId == shape.source) = true := by
          assumption
        have sourceNe : sourceId ≠ shape.source := by
          intro same
          subst sourceId
          exact notSourceBool (by simp)
        have sourceLt : shape.source < sourceId :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt notBefore) sourceNe.symm
        have oneLe : 1 ≤ sourceId :=
          Nat.succ_le_iff.mpr
            (Nat.lt_of_le_of_lt (Nat.zero_le shape.source) sourceLt)
        have targetBound : sourceId - 1 < shape.parameterCount - 1 :=
          Nat.sub_lt_sub_right oneLe sourceParameter
        right
        constructor
        · omega
        · exact Nat.add_lt_add_left targetBound shape.fieldCount
  · split at translated
    · cases translated
    · split at translated
      · have retainedEnd :
            sourceId < shape.parameterCount + 2 * shape.fieldCount := by
          assumption
        have retainedStart :
            ¬sourceId < shape.parameterCount + shape.fieldCount := by
          assumption
        simp only [Option.some.injEq] at translated
        subst targetId
        right
        constructor
        · exact retainedEnd
        · have start : shape.parameterCount + shape.fieldCount ≤ sourceId :=
            Nat.le_of_not_gt retainedStart
          have fieldIndex : sourceId -
              (shape.parameterCount + shape.fieldCount) <
                shape.fieldCount := by
            apply (Nat.sub_lt_iff_lt_add start).2
            rw [Nat.two_mul] at retainedEnd
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              retainedEnd
          exact Nat.lt_of_lt_of_le fieldIndex
            (Nat.le_add_right shape.fieldCount (shape.parameterCount - 1))
      · split at translated
        · have sourceEq : sourceId =
              shape.parameterCount + 2 * shape.fieldCount :=
            beq_iff_eq.mp (by assumption)
          simp only [Option.some.injEq] at translated
          subst targetId
          exact Or.inl ⟨sourceEq, rfl⟩
        · cases translated

/-- Appending the same freshly allocated value to both register files extends
the relation across the planner's distinguished result-register mapping. -/
theorem ValuesRel.pushResult {shape : Shape} {source target : Array RVal}
    {result : RVal} (related : ValuesRel shape source target)
    (sourceSize : source.size =
      shape.parameterCount + 2 * shape.fieldCount)
    (targetSize : target.size =
      shape.fieldCount + (shape.parameterCount - 1))
    (sourceBound : shape.source < shape.parameterCount) :
    ValuesRel shape (source.push result) (target.push result) := by
  intro sourceId targetId translated
  rcases translateRegister?_range sourceBound translated with
    ⟨sourceEnd, targetEnd⟩ | ⟨sourceBefore, targetBefore⟩
  · subst sourceId
    subst targetId
    rw [← sourceSize, ← targetSize]
    simp
  · have sourceNe : sourceId ≠ source.size := by
      rw [sourceSize]
      exact Nat.ne_of_lt sourceBefore
    have targetNe : targetId ≠ target.size := by
      rw [targetSize]
      exact Nat.ne_of_lt targetBefore
    simpa [Array.getElem?_push, sourceNe, targetNe] using
      related sourceId targetId translated

/-- Runtime register file after the recognized baseline fetch/retain prefix. -/
def baselinePrefixValues (parameters fields : Array RVal) : Array RVal :=
  parameters ++ fields ++ fields

/-- Runtime register file entering either generated credit helper: reset fields
first, followed by the original parameters with the consumed source removed. -/
def helperEntryValues (source : ValueId) (parameters fields : Array RVal) :
    Array RVal :=
  fields ++ (parameters.toList.eraseIdx source).toArray

/-- The planner's register translation exactly relates the concrete baseline
prefix file to the concrete helper-entry file.  This includes the not-yet-
allocated result register: both sides are out of bounds at its mapped index. -/
theorem valuesRel_helperEntry {shape : Shape}
    {parameters fields : Array RVal}
    (parameterCount : parameters.size = shape.parameterCount)
    (fieldCount : fields.size = shape.fieldCount)
    (sourceBound : shape.source < shape.parameterCount) :
    ValuesRel shape (baselinePrefixValues parameters fields)
      (helperEntryValues shape.source parameters fields) := by
  intro sourceId targetId translated
  unfold translateRegister? at translated
  split at translated
  · have sourceParameter : sourceId < shape.parameterCount := by assumption
    split at translated
    · cases translated
    · have notSourceBool : ¬(sourceId == shape.source) = true := by assumption
      split at translated
      · have beforeSource : sourceId < shape.source := by assumption
        simp only [Option.some.injEq] at translated
        subst targetId
        simp [baselinePrefixValues, helperEntryValues,
          Array.getElem?_append, parameterCount, fieldCount,
          List.getElem?_eraseIdx, sourceParameter, beforeSource]
      · have notBeforeSource : ¬sourceId < shape.source := by assumption
        have sourceNe : sourceId ≠ shape.source := by
          intro same
          subst sourceId
          exact notSourceBool (by simp)
        have sourceLt : shape.source < sourceId :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt notBeforeSource) sourceNe.symm
        simp only [Option.some.injEq] at translated
        subst targetId
        have eraseSide : ¬sourceId - 1 < shape.source := by
          rw [← Nat.pred_eq_sub_one]
          exact Nat.not_lt_of_ge (Nat.le_pred_of_lt sourceLt)
        have oneLe : 1 ≤ sourceId :=
          Nat.succ_le_iff.mpr
            (Nat.lt_of_le_of_lt (Nat.zero_le shape.source) sourceLt)
        have indexEq : sourceId - 1 + 1 = sourceId :=
          Nat.sub_add_cancel oneLe
        simp [baselinePrefixValues, helperEntryValues,
          Array.getElem?_append, parameterCount, fieldCount,
          List.getElem?_eraseIdx, sourceParameter, eraseSide, indexEq]
  · have afterParameters : ¬sourceId < shape.parameterCount := by assumption
    split at translated
    · cases translated
    · have afterFetched :
          ¬sourceId < shape.parameterCount + shape.fieldCount := by
        assumption
      split at translated
      · have beforeRetainedEnd :
            sourceId < shape.parameterCount + 2 * shape.fieldCount := by
          assumption
        simp only [Option.some.injEq] at translated
        subst targetId
        have retainedStart :
            shape.parameterCount + shape.fieldCount ≤ sourceId :=
          Nat.le_of_not_gt afterFetched
        have fieldIndexShape :
            sourceId - (shape.parameterCount + shape.fieldCount) <
              shape.fieldCount := by
          apply (Nat.sub_lt_iff_lt_add retainedStart).2
          rw [Nat.two_mul] at beforeRetainedEnd
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            beforeRetainedEnd
        have sourceMiddle :
            ¬sourceId - shape.parameterCount < shape.fieldCount := by
          intro middle
          have parameterLe : shape.parameterCount ≤ sourceId :=
            Nat.le_trans (Nat.le_add_right _ _) retainedStart
          have upper := (Nat.sub_lt_iff_lt_add parameterLe).1 middle
          omega
        have indexEq :
            sourceId - shape.parameterCount - shape.fieldCount =
              sourceId - (shape.parameterCount + shape.fieldCount) :=
          (Nat.sub_add_eq sourceId shape.parameterCount
            shape.fieldCount).symm
        simp [baselinePrefixValues, helperEntryValues,
          Array.getElem?_append, parameterCount, fieldCount,
          afterParameters, sourceMiddle, fieldIndexShape, indexEq]
      · split at translated
        · have sourceEq : sourceId =
              shape.parameterCount + 2 * shape.fieldCount :=
            beq_iff_eq.mp (by assumption)
          simp only [Option.some.injEq] at translated
          subst targetId
          subst sourceId
          have sourceNone :
              (baselinePrefixValues parameters fields)[
                shape.parameterCount + 2 * shape.fieldCount]? = none := by
            apply Array.getElem?_eq_none_iff.mpr
            simp [baselinePrefixValues, parameterCount, fieldCount,
              Nat.two_mul]
          have targetNone :
              (helperEntryValues shape.source parameters fields)[
                shape.fieldCount + (shape.parameterCount - 1)]? = none := by
            apply Array.getElem?_eq_none_iff.mpr
            simp [helperEntryValues, List.length_eraseIdx, parameterCount,
              fieldCount, sourceBound]
          rw [sourceNone, targetNone]
        · cases translated

/-- After both allocation instructions append the same result value, the
canonical baseline/helper register files remain related for tail operands. -/
theorem valuesRel_afterAllocation {shape : Shape}
    {parameters fields : Array RVal} {result : RVal}
    (parameterCount : parameters.size = shape.parameterCount)
    (fieldCount : fields.size = shape.fieldCount)
    (sourceBound : shape.source < shape.parameterCount) :
    ValuesRel shape
      ((baselinePrefixValues parameters fields).push result)
      ((helperEntryValues shape.source parameters fields).push result) := by
  apply ValuesRel.pushResult
    (valuesRel_helperEntry parameterCount fieldCount sourceBound)
  · simp [baselinePrefixValues, parameterCount, fieldCount, Nat.two_mul]
  · simp [helperEntryValues, List.length_eraseIdx, parameterCount,
      fieldCount, sourceBound]
  · exact sourceBound

/-- The concrete helper-entry value vector has exactly the ABI length emitted
for either helper block. -/
theorem helperEntryValues_size {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {parameters fields : Array RVal}
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount) :
    (helperEntryValues site.shape.source parameters fields).size =
      site.candidate.helperValueParams.size := by
  rw [site.candidateVectors.1]
  simp [helperEntryValues, List.length_eraseIdx, parameterCount, fieldCount,
    site.fits.parameterCount]

private theorem eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (values : List α) (index : Nat),
      (values.map f).eraseIdx index = (values.eraseIdx index).map f := by
  intro values
  induction values with
  | nil => intro index; cases index <;> rfl
  | cons value values ih =>
      intro index
      cases index with
      | zero => rfl
      | succ index =>
          simp only [List.map_cons, List.eraseIdx_cons_succ]
          rw [ih]

private theorem filter_range_ne_eq_eraseIdx (count source : Nat)
    (bound : source < count) :
    (List.range count).filter (fun value => value != source) =
      (List.range count).eraseIdx source := by
  induction count generalizing source with
  | zero => omega
  | succ count ih =>
      cases source with
      | zero =>
          rw [show count + 1 = Nat.succ count by omega,
            List.range_succ_eq_map]
          simp only [List.filter_cons, List.filter_map, List.eraseIdx_zero,
            List.tail_cons]
          have keepAll :
              List.filter ((fun value => value != 0) ∘ Nat.succ)
                  (List.range count) = List.range count := by
            apply List.filter_eq_self.mpr
            intro value member
            simp [Function.comp_apply]
          rw [keepAll]
          simp
      | succ source =>
          have tailBound : source < count := by omega
          rw [show count + 1 = Nat.succ count by omega,
            List.range_succ_eq_map]
          simp only [List.filter_cons, bne_iff_ne, ne_eq,
            Nat.zero_ne_add_one, not_false_eq_true, ↓reduceIte,
            List.filter_map, List.eraseIdx_cons_succ]
          rw [eraseIdx_map]
          have predicate :
              ((fun value => value != source + 1) ∘ Nat.succ) =
                (fun value => value != source) := by
            funext value
            simp [Function.comp_apply]
          rw [predicate]
          rw [ih source tailBound]

private theorem mapM_eq_ok_of_getElem {ε α β : Type}
    (f : α → Except ε β) :
    ∀ (input : List α) (output : List β),
      input.length = output.length →
      (∀ (index : Nat) (source : α) (target : β),
        input[index]? = some source →
        output[index]? = some target →
        f source = .ok target) →
      input.mapM f = .ok output := by
  intro input
  induction input with
  | nil =>
      intro output lengths pointwise
      cases output with
      | nil => rfl
      | cons target output => simp at lengths
  | cons source input ih =>
      intro output lengths pointwise
      cases output with
      | nil => simp at lengths
      | cons target output =>
          have head := pointwise 0 source target (by rfl) (by rfl)
          have tailPointwise : ∀ (index : Nat) (tailSource : α)
              (tailTarget : β),
              input[index]? = some tailSource →
              output[index]? = some tailTarget →
              f tailSource = .ok tailTarget := by
            intro index tailSource tailTarget sourceAt targetAt
            exact pointwise (index + 1) tailSource tailTarget
              (by simpa using sourceAt) (by simpa using targetAt)
          simp only [List.length_cons] at lengths
          simp [List.mapM_cons, head, ih output (Nat.succ.inj lengths)
            tailPointwise]
          rfl

private theorem resolveFold_of_mapM {values : Array RVal} :
    ∀ {atoms : List Atom} {output : List RVal},
      atoms.mapM (resolveAtom values) = .ok output →
      ∀ initial : Array RVal,
        atoms.foldlM (fun current atom => do
          return current.push (← resolveAtom values atom)) initial =
            .ok (initial ++ output.toArray) := by
  intro atoms
  induction atoms with
  | nil =>
      intro output resolved initial
      change Except.ok [] = Except.ok output at resolved
      injection resolved with outputEq
      subst output
      simp [List.foldlM_nil, pure, Except.pure]
  | cons atom atoms ih =>
      intro output resolved initial
      cases headAt : resolveAtom values atom with
      | error error =>
          simp [List.mapM_cons, headAt, bind, Except.bind] at resolved
      | ok value =>
          cases tailAt : atoms.mapM (resolveAtom values) with
          | error error =>
              simp [List.mapM_cons, headAt, tailAt, bind, Except.bind] at resolved
          | ok tail =>
              simp [List.mapM_cons, headAt, tailAt, bind, Except.bind,
                pure, Except.pure] at resolved
              subst output
              rw [List.foldlM_cons]
              simp only [headAt, bind, Except.bind, pure, Except.pure]
              change atoms.foldlM (fun current atom => do
                return current.push (← resolveAtom values atom))
                  (initial.push value) =
                    .ok (initial ++ (value :: tail).toArray)
              rw [ih tailAt]
              congr 1
              apply Array.ext'
              simp

private theorem resolveAtoms_of_mapM {values : Array RVal}
    {atoms : Array Atom} {output : List RVal}
    (resolved : atoms.toList.mapM (resolveAtom values) = .ok output) :
    resolveAtoms values atoms = .ok output.toArray := by
  unfold resolveAtoms
  rw [← Array.foldlM_toList]
  simpa using resolveFold_of_mapM resolved #[]

private theorem resolveAtom_reg_of_getElem {values : Array RVal}
    {index : Nat} {value : RVal}
    (found : values[index]? = some value) :
    resolveAtom values (.reg index) = .ok value := by
  simp [resolveAtom, found]

/-- The generated branch operand vector resolves to exactly the canonical
helper-entry register file.  This is the runtime half of the reset-to-helper
CFG transfer and holds for any constructor arity and source parameter slot. -/
theorem branchValues_resolve {shape : Shape}
    {parameters fields : Array RVal}
    (parameterCount : parameters.size = shape.parameterCount)
    (fieldCount : fields.size = shape.fieldCount)
    (sourceBound : shape.source < shape.parameterCount) :
    resolveAtoms (parameters ++ fields) (branchValues shape) =
      .ok (helperEntryValues shape.source parameters fields) := by
  let fieldAtoms : List Atom :=
    (List.range shape.fieldCount).map fun field =>
      .reg (shape.parameterCount + field)
  let parameterAtoms : List Atom :=
    ((List.range shape.parameterCount).filter fun value =>
      value != shape.source).map fun value => .reg value
  have fieldsMapped :
      fieldAtoms.mapM (resolveAtom (parameters ++ fields)) =
        .ok fields.toList := by
    apply mapM_eq_ok_of_getElem
    · simp [fieldAtoms, fieldCount]
    · intro index atom value atomAt valueAt
      have indexBound : index < shape.fieldCount := by
        have := (List.getElem?_eq_some_iff.mp atomAt).choose
        simpa [fieldAtoms] using this
      simp only [fieldAtoms, List.getElem?_map,
        List.getElem?_range indexBound, Option.map_some,
        Option.some.injEq] at atomAt
      subst atom
      have fieldAt : fields[index]? = some value := by
        simpa only [Array.getElem?_toList] using valueAt
      have afterParameters :
          ¬shape.parameterCount + index < parameters.size := by
        rw [parameterCount]
        omega
      have indexEq : shape.parameterCount + index - parameters.size =
          index := by
        rw [parameterCount]
        omega
      apply resolveAtom_reg_of_getElem
      rw [Array.getElem?_append, if_neg afterParameters, indexEq]
      exact fieldAt
  have parametersMapped :
      parameterAtoms.mapM (resolveAtom (parameters ++ fields)) =
        .ok (parameters.toList.eraseIdx shape.source) := by
    unfold parameterAtoms
    rw [filter_range_ne_eq_eraseIdx _ _ sourceBound]
    apply mapM_eq_ok_of_getElem
    · simp [List.length_eraseIdx, sourceBound, parameterCount]
    · intro index atom value atomAt valueAt
      have erasedBound :
          index < (parameters.toList.eraseIdx shape.source).length :=
        (List.getElem?_eq_some_iff.mp valueAt).choose
      rw [List.getElem?_map, List.getElem?_eraseIdx] at atomAt
      rw [List.getElem?_eraseIdx] at valueAt
      split at atomAt <;> split at valueAt
      · rename_i beforeSource _
        have rangeBound : index < shape.parameterCount :=
          Nat.lt_trans beforeSource sourceBound
        rw [List.getElem?_range rangeBound] at atomAt
        simp only [Option.map_some, Option.some.injEq] at atomAt
        subst atom
        have parameterAt : parameters[index]? = some value := by
          simpa only [Array.getElem?_toList] using valueAt
        have parameterIndex : index < parameters.size := by
          rw [parameterCount]
          exact rangeBound
        apply resolveAtom_reg_of_getElem
        rw [Array.getElem?_append, if_pos parameterIndex]
        exact parameterAt
      · rename_i beforeSource notBeforeSource
        omega
      · rename_i notBeforeSource beforeSource
        omega
      · rename_i notBeforeSource _
        have rangeBound : index + 1 < shape.parameterCount := by
          simp [List.length_eraseIdx, sourceBound, parameterCount] at erasedBound
          omega
        rw [List.getElem?_range rangeBound] at atomAt
        simp only [Option.map_some, Option.some.injEq] at atomAt
        subst atom
        have parameterAt : parameters[index + 1]? = some value := by
          simpa only [Array.getElem?_toList] using valueAt
        have parameterIndex : index + 1 < parameters.size := by
          rw [parameterCount]
          exact rangeBound
        apply resolveAtom_reg_of_getElem
        rw [Array.getElem?_append, if_pos parameterIndex]
        exact parameterAt
  have mapped :
      (fieldAtoms ++ parameterAtoms).mapM
          (resolveAtom (parameters ++ fields)) =
        .ok (fields.toList ++ parameters.toList.eraseIdx shape.source) := by
    simp [List.mapM_append, fieldsMapped, parametersMapped, bind,
      Except.bind, pure, Except.pure]
  have resolved := resolveAtoms_of_mapM mapped
  have atomsEq : (fieldAtoms ++ parameterAtoms).toArray =
      branchValues shape := by
    simp [branchValues, fieldAtoms, parameterAtoms]
  have outputEq :
      (fields.toList ++ parameters.toList.eraseIdx shape.source).toArray =
        helperEntryValues shape.source parameters fields := by
    apply Array.ext'
    simp [helperEntryValues]
  change resolveAtoms (parameters ++ fields)
      (fieldAtoms ++ parameterAtoms).toArray =
        .ok (fields.toList ++
          parameters.toList.eraseIdx shape.source).toArray at resolved
  rw [atomsEq, outputEq] at resolved
  exact resolved

/-- A reset successor transfers its one linear credit and the canonical
branch value vector into either generated helper block. -/
theorem helperEdgeTransfer {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {frame : Frame} {target : BlockId} {capability : CreditCap}
    {credit : Credit} {parameters fields : Array RVal}
    (frameValues : frame.values = parameters ++ fields)
    (frameCredits : frame.credits = #[some credit])
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (blockAt : frame.definition.blocks[target]? =
      some (Reuse.creditBlock site.candidate capability)) :
    EdgeTransfer frame
      { target
        values := site.candidate.resetValues
        credits := #[0] }
      #[]
      { frame with
        block := target
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some credit] } := by
  let after : Frame :=
    { frame with credits := frame.credits.setIfInBounds 0 none }
  have creditAt : frame.credits[0]? = some (some credit) := by
    simp [frameCredits]
  have taken : CreditTake frame 0 after credit := by
    simpa [after] using CreditTake.of_lookup
      (CreditLookup.of_getElem creditAt)
  have takenMany : CreditTakeMany frame #[0] after #[credit] :=
    CreditTakeMany.single taken
  have afterCredits : after.credits = #[none] := by
    simp [after, frameCredits, Array.setIfInBounds]
  have cleared : NoLiveCredits after := by
    simp [NoLiveCredits, afterCredits]
  have resolved : resolveAtoms frame.values site.candidate.resetValues =
      .ok (helperEntryValues site.shape.source parameters fields) := by
    rw [frameValues, site.candidateVectors.2]
    exact branchValues_resolve parameterCount fieldCount site.fits.sourceBound
  have transferred := EdgeTransfer.of_parts
    (frame := frame) (after := after)
    (edge := { target, values := site.candidate.resetValues, credits := #[0] })
    (implicitValues := #[])
    (values := helperEntryValues site.shape.source parameters fields)
    (credits := #[credit])
    (block := Reuse.creditBlock site.candidate capability)
    resolved takenMany cleared blockAt
    (by simpa [Reuse.creditBlock] using
      helperEntryValues_size site parameterCount fieldCount)
    (by simp [Reuse.creditBlock])
  simpa [after] using transferred

/-- A unit-refcount logical reset and its present-credit branch reach the
required helper in exactly two machine steps.  All operand reordering and
linear credit transfer are discharged from the accepted site. -/
theorem hotLogicalControlPrefix {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields : Array RVal} {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (resolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (unitRC : box.rc = 1) :
    Steps context .logical 2 machine
      { machine with
        store := ((machine.store.tickResetAttempt).kill location).tickHotReset
        control := .running
          { definition
            block := hotId
            pc := 0
            values := helperEntryValues site.shape.source parameters fields
            credits := #[some
              { layout := sourceSchema.layout
                presence := .present none }] }
          stack } := by
  let initial : Frame :=
    { definition
      block := resetId
      pc := 0
      values := parameters
      credits := #[] }
  let credit : Credit :=
    { layout := sourceSchema.layout, presence := .present none }
  let middle : Frame :=
    { initial with
      pc := 1
      values := parameters ++ fields
      credits := #[some credit] }
  let target : Frame :=
    { definition
      block := hotId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  have resetStep : Step context .logical machine
      { machine with
        store := ((machine.store.tickResetAttempt).kill location).tickHotReset
        control := .running middle stack } := by
    have step := Step.resetSharedLogicalHot
      (context := context) (machine := machine)
      (frame := initial) (stack := stack)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (target := .reg site.shape.source)
      (cid := site.shape.sourceConstructor)
      (schema := sourceSchema) (location := location) (box := box)
      (fields := fields)
      (by simpa [initial] using control) resetAt
      (by simp [initial, site.resetBlock_eq])
      (by simp [initial, site.resetBlock_eq]) schemaAt
      (by simpa [initial] using resolved) viewed unitRC
    simpa [initial, middle, credit] using step
  have transferred : EdgeTransfer middle
      { target := hotId
        values := site.candidate.resetValues
        credits := #[0] }
      #[] target := by
    simpa [middle, target, credit] using
      helperEdgeTransfer site (frame := middle) (target := hotId)
        (capability := .required site.candidate.layout) (credit := credit)
        (parameters := parameters) (fields := fields)
        (by simp [middle]) (by simp [middle]) parameterCount
        fieldCount (by simpa [middle, initial] using hotAt)
  have branchStep : Step context .logical
      { machine with
        store := ((machine.store.tickResetAttempt).kill location).tickHotReset
        control := .running middle stack }
      { machine with
        store := ((machine.store.tickResetAttempt).kill location).tickHotReset
        control := .running target stack } := by
    apply Step.branchCreditPresent
      (frame := middle) (target := target)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (creditId := 0)
      (credit := credit)
      (someEdge :=
        { target := hotId
          values := site.candidate.resetValues
          credits := #[0] })
      (noneEdge :=
        { target := coldId
          values := site.candidate.resetValues
          credits := #[0] })
    · rfl
    · simpa [middle, initial] using resetAt
    · simp [middle, Reuse.resetBlock]
    · rfl
    · apply CreditLookup.of_getElem
      simp [middle, credit]
    · rfl
    · exact transferred
  have first := resetStep.toSteps (by simpa [initial] using control)
  have second := branchStep.toSteps (by rfl)
  simpa [target, credit] using first.trans second

/-- The physical unit-refcount arm reaches the same required helper/value
file in two steps while its credit carries the reserved source location. -/
theorem hotPhysicalControlPrefix {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields : Array RVal} {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (resolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (unitRC : box.rc = 1) :
    Steps context .physical 2 machine
      { machine with
        store :=
          ((machine.store.tickResetAttempt).reserve location).tickHotReset
        control := .running
          { definition
            block := hotId
            pc := 0
            values := helperEntryValues site.shape.source parameters fields
            credits := #[some
              { layout := sourceSchema.layout
                presence := .present (some location) }] }
          stack } := by
  let initial : Frame :=
    { definition
      block := resetId
      pc := 0
      values := parameters
      credits := #[] }
  let credit : Credit :=
    { layout := sourceSchema.layout, presence := .present (some location) }
  let middle : Frame :=
    { initial with
      pc := 1
      values := parameters ++ fields
      credits := #[some credit] }
  let target : Frame :=
    { definition
      block := hotId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  have resetStep : Step context .physical machine
      { machine with
        store :=
          ((machine.store.tickResetAttempt).reserve location).tickHotReset
        control := .running middle stack } := by
    have step := Step.resetSharedPhysicalHot
      (context := context) (machine := machine)
      (frame := initial) (stack := stack)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (target := .reg site.shape.source)
      (cid := site.shape.sourceConstructor)
      (schema := sourceSchema) (location := location) (box := box)
      (fields := fields)
      (by simpa [initial] using control) resetAt
      (by simp [initial, site.resetBlock_eq])
      (by simp [initial, site.resetBlock_eq]) schemaAt
      (by simpa [initial] using resolved) viewed unitRC
    simpa [initial, middle, credit] using step
  have transferred : EdgeTransfer middle
      { target := hotId
        values := site.candidate.resetValues
        credits := #[0] }
      #[] target := by
    simpa [middle, target, credit] using
      helperEdgeTransfer site (frame := middle) (target := hotId)
        (capability := .required site.candidate.layout) (credit := credit)
        (parameters := parameters) (fields := fields)
        (by simp [middle]) (by simp [middle]) parameterCount
        fieldCount (by simpa [middle, initial] using hotAt)
  have branchStep : Step context .physical
      { machine with
        store :=
          ((machine.store.tickResetAttempt).reserve location).tickHotReset
        control := .running middle stack }
      { machine with
        store :=
          ((machine.store.tickResetAttempt).reserve location).tickHotReset
        control := .running target stack } := by
    apply Step.branchCreditPresent
      (frame := middle) (target := target)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (creditId := 0)
      (credit := credit)
      (someEdge :=
        { target := hotId
          values := site.candidate.resetValues
          credits := #[0] })
      (noneEdge :=
        { target := coldId
          values := site.candidate.resetValues
          credits := #[0] })
    · rfl
    · simpa [middle, initial] using resetAt
    · simp [middle, Reuse.resetBlock]
    · rfl
    · apply CreditLookup.of_getElem
      simp [middle, credit]
    · rfl
    · exact transferred
  have first := resetStep.toSteps (by simpa [initial] using control)
  have second := branchStep.toSteps (by rfl)
  simpa [target, credit] using first.trans second

/-- The multiply-referenced reset arm reaches the optional-credit helper in
two steps under either interpretation.  The evaluator's exact retained store
is threaded unchanged through the CFG branch. -/
theorem coldControlPrefix {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {resetId hotId coldId : BlockId}
    {parameters fields : Array RVal} {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema : CtorSchema} {machine : Machine} {store : Store}
    {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (coldAt : definition.blocks[coldId]? = some
      (Reuse.creditBlock site.candidate
        (.optional site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (resolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (shared : 1 < box.rc)
    (retained : RetainSharedMany
      ((((machine.store.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      fields store) :
    Steps context interpretation 2 machine
      { machine with
        store
        control := .running
          { definition
            block := coldId
            pc := 0
            values := helperEntryValues site.shape.source parameters fields
            credits := #[some
              { layout := sourceSchema.layout
                presence := .absent }] }
          stack } := by
  let initial : Frame :=
    { definition
      block := resetId
      pc := 0
      values := parameters
      credits := #[] }
  let credit : Credit :=
    { layout := sourceSchema.layout, presence := .absent }
  let middle : Frame :=
    { initial with
      pc := 1
      values := parameters ++ fields
      credits := #[some credit] }
  let target : Frame :=
    { definition
      block := coldId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  have resetStep : Step context interpretation machine
      { machine with store, control := .running middle stack } := by
    have step := Step.resetSharedCold
      (context := context) (interpretation := interpretation)
      (machine := machine) (frame := initial) (stack := stack)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (target := .reg site.shape.source)
      (cid := site.shape.sourceConstructor)
      (schema := sourceSchema) (location := location) (box := box)
      (fields := fields) (store := store)
      (by simpa [initial] using control) resetAt
      (by simp [initial, site.resetBlock_eq])
      (by simp [initial, site.resetBlock_eq]) schemaAt
      (by simpa [initial] using resolved) viewed shared retained
    simpa [initial, middle, credit] using step
  have transferred : EdgeTransfer middle
      { target := coldId
        values := site.candidate.resetValues
        credits := #[0] }
      #[] target := by
    simpa [middle, target, credit] using
      helperEdgeTransfer site (frame := middle) (target := coldId)
        (capability := .optional site.candidate.layout) (credit := credit)
        (parameters := parameters) (fields := fields)
        (by simp [middle]) (by simp [middle]) parameterCount
        fieldCount (by simpa [middle, initial] using coldAt)
  have branchStep : Step context interpretation
      { machine with store, control := .running middle stack }
      { machine with store, control := .running target stack } := by
    apply Step.branchCreditAbsent
      (frame := middle) (target := target)
      (block := Reuse.resetBlock site.candidate hotId coldId)
      (creditId := 0)
      (credit := credit)
      (someEdge :=
        { target := hotId
          values := site.candidate.resetValues
          credits := #[0] })
      (noneEdge :=
        { target := coldId
          values := site.candidate.resetValues
          credits := #[0] })
    · rfl
    · simpa [middle, initial] using resetAt
    · simp [middle, Reuse.resetBlock]
    · rfl
    · apply CreditLookup.of_getElem
      simp [middle, credit]
    · rfl
    · exact transferred
  have first := resetStep.toSteps (by simpa [initial] using control)
  have second := branchStep.toSteps (by rfl)
  simpa [target, credit] using first.trans second

/-- Successful resolution of a translated atom returns the same runtime
value.  The premise is intentionally success-directed: missing source and
target registers carry register-specific diagnostic strings. -/
theorem resolveAtom_translate {shape : Shape} {source target : Array RVal}
    {atom translated : Atom} {value : RVal}
    (related : ValuesRel shape source target)
    (translation : translateAtom? shape atom = some translated)
    (resolved : resolveAtom source atom = .ok value) :
    resolveAtom target translated = .ok value := by
  cases atom with
  | reg sourceId =>
      cases translatedAt : translateRegister? shape sourceId with
      | none => simp [translateAtom?, translatedAt] at translation
      | some targetId =>
          simp [translateAtom?, translatedAt] at translation
          subst translated
          cases sourceAt : source[sourceId]? with
          | none => simp [resolveAtom, sourceAt] at resolved
          | some actual =>
              simp [resolveAtom, sourceAt] at resolved
              subst actual
              have targetAt := related sourceId targetId translatedAt
              rw [sourceAt] at targetAt
              have targetAt' : target[targetId]? = some value := targetAt.symm
              simp [resolveAtom, targetAt']
  | lit literal =>
      simp [translateAtom?] at translation
      subst translated
      simpa [resolveAtom] using resolved
  | erased =>
      simp [translateAtom?] at translation
      subst translated
      simpa [resolveAtom] using resolved

private theorem resolveList_translate {shape : Shape}
    {source target : Array RVal} (related : ValuesRel shape source target) :
    ∀ {atoms translated : List Atom},
      atoms.mapM (translateAtom? shape) = some translated →
      ∀ (initial result : Array RVal),
        atoms.foldlM (fun output atom => do
            return output.push (← resolveAtom source atom)) initial =
              .ok result →
        translated.foldlM (fun output atom => do
            return output.push (← resolveAtom target atom)) initial =
              .ok result := by
  intro atoms
  induction atoms with
  | nil =>
      intro translated translation initial result resolved
      simp at translation
      subst translated
      simpa using resolved
  | cons atom atoms ih =>
      intro translated translation initial result resolved
      cases atomAt : translateAtom? shape atom with
      | none => simp [List.mapM_cons, atomAt] at translation
      | some translatedAtom =>
          cases tailAt : atoms.mapM (translateAtom? shape) with
          | none => simp [List.mapM_cons, atomAt, tailAt] at translation
          | some translatedAtoms =>
              simp [List.mapM_cons, atomAt, tailAt] at translation
              subst translated
              rw [List.foldlM_cons]
              rw [List.foldlM_cons] at resolved
              cases sourceResolved : resolveAtom source atom with
              | error error =>
                  simp only [sourceResolved, bind, Except.bind] at resolved
                  cases resolved
              | ok value =>
                  simp only [sourceResolved, bind, Except.bind] at resolved
                  have targetResolved :
                      resolveAtom target translatedAtom = .ok value :=
                    resolveAtom_translate related atomAt sourceResolved
                  rw [targetResolved]
                  simp only [bind, Except.bind]
                  apply ih tailAt (initial.push value) result
                  exact resolved

/-- Successful batch resolution is preserved by the planner's accepted atom
translation, with both sides producing the identical value vector. -/
theorem resolveAtoms_translate {shape : Shape}
    {source target : Array RVal} (related : ValuesRel shape source target)
    {atoms translated : Array Atom} {values : Array RVal}
    (translation : translateAtoms? shape atoms = some translated)
    (resolved : resolveAtoms source atoms = .ok values) :
    resolveAtoms target translated = .ok values := by
  unfold translateAtoms? at translation
  cases mappedAt : atoms.toList.mapM (translateAtom? shape) with
  | none => simp [mappedAt] at translation
  | some translatedAtoms =>
      simp [mappedAt] at translation
      subst translated
      unfold resolveAtoms at resolved ⊢
      rw [← Array.foldlM_toList]
      apply resolveList_translate related mappedAt #[] values
      simpa only [Array.foldlM_toList] using resolved

/-- The accepted-site trace turns successful baseline allocation-operand
resolution into the exact helper-block operand resolution. -/
theorem resolveAllocationArguments {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {source target values : Array RVal}
    (related : ValuesRel site.shape source target)
    (resolved : resolveAtoms source site.shape.allocationArguments =
      .ok values) :
    resolveAtoms target site.candidate.allocationArguments = .ok values :=
  resolveAtoms_translate related site.allocationArgumentsFound resolved

/-- The same accepted-site mapping preserves the tail-call argument vector
after baseline and helper allocation states have been related. -/
theorem resolveTailArguments {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {source target values : Array RVal}
    (related : ValuesRel site.shape source target)
    (resolved : resolveAtoms source site.shape.tailArguments = .ok values) :
    resolveAtoms target site.candidate.tailArguments = .ok values :=
  resolveAtoms_translate related site.tailArgumentsFound resolved

/-- Accepted validator schemas are also the evaluator schemas whenever the
enclosing execution context carries the checked schema table. -/
theorem evalRuntimeSchemas {limits : Validate.Limits}
    {validation : Validate.Context} {block : Block}
    (site : Reuse.Site limits validation block) {context : Eval.Context}
    (schemas : context.schemas = validation.schemas) :
    ∃ sourceSchema allocationSchema,
      context.schemas .shared site.shape.sourceConstructor =
        some sourceSchema ∧
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema ∧
      sourceSchema.fields =
        Array.replicate site.shape.fieldCount .shared ∧
      allocationSchema.fields = sourceSchema.fields ∧
      site.candidate.layout = sourceSchema.layout ∧
      site.candidate.layout = allocationSchema.layout := by
  rw [schemas]
  exact site.runtimeSchemas

private theorem blocks_nonempty_of_getElem {blocks : Array Block}
    {index : Nat} {block : Block} (found : blocks[index]? = some block) :
    blocks.isEmpty = false := by
  apply Bool.eq_false_iff.mpr
  intro empty
  have blocksEmpty : blocks = #[] := Array.isEmpty_iff.mp empty
  subst blocks
  simp at found

/-- A baseline register remains observable to an accepted rewrite exactly when
the recognized allocation or recursive tail call reads it. The reset block may
forward additional ABI slots, but helper-local liveness is allowed to forget
those values immediately. -/
def PlannerValueRelevant (shape : Shape) (sourceId : ValueId) : Prop :=
  .reg sourceId ∈ shape.allocationArguments.toList ∨
    .reg sourceId ∈ shape.tailArguments.toList

def PlannerAtomRelevant (shape : Shape) : Atom → Prop
  | .reg sourceId => PlannerValueRelevant shape sourceId
  | .lit _ | .erased => True

/-- Observable register values selected by the planner agree modulo a location
relation. The implication form is sufficient for operand resolution and
permits both dead forwarded parameters and the distinguished, not-yet-allocated
result mapping to be out of bounds. -/
def TranslatedValuesIso (shape : Shape) (locRel : Nat → Nat → Prop)
    (source target : Array RVal) : Prop :=
  ∀ sourceId targetId sourceValue,
    PlannerValueRelevant shape sourceId →
    translateRegister? shape sourceId = some targetId →
    source[sourceId]? = some sourceValue →
    ∃ targetValue,
      target[targetId]? = some targetValue ∧
      IxIR1.Sim.RValIso locRel sourceValue targetValue

/-- A location value is represented by one of the surrounding semantic
roots. Scalars require no heap-root witness. -/
def PlannerValueInRoots (roots : List IxIR1.Sim.Root) : RVal → Prop
  | .loc location =>
      ∃ world, (⟨world, .loc location⟩ : IxIR1.Sim.Root) ∈ roots
  | .lit _ | .erased => True

/-- Every observable source register that the reuse planner preserves has
the root support needed by physical address replacement. The consumed source
register, discarded fetch temporaries, dead forwarded parameters, and scalar
values are deliberately outside the heap-root obligation. -/
def MappedValuesInRoots (shape : Shape) (values : Array RVal)
    (roots : List IxIR1.Sim.Root) : Prop :=
  ∀ sourceId targetId sourceValue,
    PlannerValueRelevant shape sourceId →
    translateRegister? shape sourceId = some targetId →
    values[sourceId]? = some sourceValue →
    PlannerValueInRoots roots sourceValue

/-- Root-level self-relatedness discharges self-relatedness for every
planner-preserved register. -/
theorem MappedValuesInRoots.selfRelated {shape : Shape}
    {values : Array RVal} {roots : List IxIR1.Sim.Root}
    {locRel : Nat → Nat → Prop}
    (mapped : MappedValuesInRoots shape values roots)
    (rootsRelated : ∀ root ∈ roots,
      IxIR1.Sim.RValIso locRel root.value root.value) :
    ∀ sourceId targetId sourceValue,
      PlannerValueRelevant shape sourceId →
      translateRegister? shape sourceId = some targetId →
      values[sourceId]? = some sourceValue →
      IxIR1.Sim.RValIso locRel sourceValue sourceValue := by
  intro sourceId targetId sourceValue relevant translated sourceAt
  have supported :=
    mapped sourceId targetId sourceValue relevant translated sourceAt
  cases sourceValue with
  | loc location =>
      obtain ⟨world, member⟩ := supported
      exact rootsRelated ⟨world, .loc location⟩ member
  | lit literal => exact .lit
  | erased => exact .erased

/-- Exact planner register agreement lifts to location-renaming agreement
when each live source value is self-related. -/
theorem ValuesRel.toTranslatedValuesIso {shape : Shape}
    {source target : Array RVal} {locRel : Nat → Nat → Prop}
    (related : ValuesRel shape source target)
    (selfRelated : ∀ (sourceId targetId : Nat) (sourceValue : RVal),
      PlannerValueRelevant shape sourceId →
      translateRegister? shape sourceId = some targetId →
      source[sourceId]? = some sourceValue →
      IxIR1.Sim.RValIso locRel sourceValue sourceValue) :
    TranslatedValuesIso shape locRel source target := by
  intro sourceId targetId sourceValue relevant translated sourceAt
  have targetAt := related sourceId targetId translated
  rw [sourceAt] at targetAt
  exact ⟨sourceValue, targetAt.symm,
    selfRelated sourceId targetId sourceValue relevant translated sourceAt⟩

private theorem rvalsIso_append {locRel : Nat → Nat → Prop}
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso locRel left right)
    {leftValue rightValue : RVal}
    (valueRelated : IxIR1.Sim.RValIso locRel leftValue rightValue) :
    IxIR1.Sim.RValsIso locRel
      (left ++ [leftValue]) (right ++ [rightValue]) := by
  induction related with
  | nil => exact .cons valueRelated .nil
  | cons head tail ih => exact .cons head ih

/-- Appending a common suffix preserves an identity-location value relation. -/
private theorem rvalsIso_append_refl
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso (fun l r => l = r) left right)
    (suffix : List RVal) :
    IxIR1.Sim.RValsIso (fun l r => l = r)
      (left ++ suffix) (right ++ suffix) := by
  induction related with
  | nil => simpa using IxIR1.Sim.RValsIso.refl suffix
  | cons head tail ih => exact .cons head ih

private theorem rvalsIso_length_eq {locRel : Nat → Nat → Prop}
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso locRel left right) :
    left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem rvalsIso_symm {locRel : Nat → Nat → Prop}
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso locRel left right) :
    IxIR1.Sim.RValsIso (fun rightLocation leftLocation =>
      locRel leftLocation rightLocation) right left := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.symm ih

private theorem rvalsIso_append_pair {locRel : Nat → Nat → Prop}
    {left₁ right₁ left₂ right₂ : List RVal}
    (first : IxIR1.Sim.RValsIso locRel left₁ right₁)
    (second : IxIR1.Sim.RValsIso locRel left₂ right₂) :
    IxIR1.Sim.RValsIso locRel (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Pointwise enlargement of a runtime-location relation preserves related
value vectors.  This local public-proof helper is used when corresponding
fresh allocations extend an existing allocation history. -/
private theorem rvalsIso_mono_rel {oldRel newRel : Nat → Nat → Prop}
    (lift : ∀ {left right}, oldRel left right → newRel left right) :
    ∀ {left right : List RVal},
      IxIR1.Sim.RValsIso oldRel left right →
        IxIR1.Sim.RValsIso newRel left right
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (head.mono lift) (rvalsIso_mono_rel lift tail)

private theorem rvalsIso_array_extract {locRel : Nat → Nat → Prop}
    {left right : Array RVal}
    (related : IxIR1.Sim.RValsIso locRel left.toList right.toList)
    (start stop : Nat) :
    IxIR1.Sim.RValsIso locRel
      (left.extract start stop).toList (right.extract start stop).toList := by
  simpa [List.extract_eq_take_drop] using
    (related.drop start).take (stop - start)

private theorem rvalsIso_transport_avoiding_right
    {oldRel newRel : Nat → Nat → Prop} {removed : Nat}
    (lift : ∀ {leftLocation rightLocation},
      oldRel leftLocation rightLocation →
      rightLocation ≠ removed →
      newRel leftLocation rightLocation)
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso oldRel left right)
    (avoids : ∀ value ∈ right, value ≠ .loc removed) :
    IxIR1.Sim.RValsIso newRel left right := by
  induction related with
  | nil => exact .nil
  | @cons leftValue rightValue lefts rights head tail ih =>
      have headAvoids : rightValue ≠ .loc removed :=
        avoids rightValue (by simp)
      have tailAvoids : ∀ value ∈ rights, value ≠ .loc removed := by
        intro value member
        exact avoids value (by simp [member])
      refine .cons ?_ (ih tailAvoids)
      cases head with
      | loc locationRelated =>
          apply IxIR1.Sim.RValIso.loc
          apply lift locationRelated
          intro same
          apply headAvoids
          cases same
          rfl
      | lit => exact .lit
      | erased => exact .erased

private theorem rvalsIso_getElem? {locRel : Nat → Nat → Prop}
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso locRel left right)
    {index : Nat} {leftValue : RVal}
    (found : left[index]? = some leftValue) :
    ∃ rightValue,
      right[index]? = some rightValue ∧
        IxIR1.Sim.RValIso locRel leftValue rightValue := by
  induction related generalizing index leftValue with
  | nil => simp at found
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst leftValue
          exact ⟨rightHead, by simp, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact ih found

private theorem rvalsIso_array_getElem? {locRel : Nat → Nat → Prop}
    {left right : Array RVal}
    (related : IxIR1.Sim.RValsIso locRel left.toList right.toList)
    {index : Nat} {leftValue : RVal}
    (found : left[index]? = some leftValue) :
    ∃ rightValue,
      right[index]? = some rightValue ∧
        IxIR1.Sim.RValIso locRel leftValue rightValue := by
  have listFound : left.toList[index]? = some leftValue := by
    simpa using found
  obtain ⟨rightValue, rightFound, valueRelated⟩ :=
    rvalsIso_getElem? related listFound
  exact ⟨rightValue, by simpa using rightFound, valueRelated⟩

/-- Resolving the same atom in pointwise-related register files produces
related runtime values. -/
theorem resolveAtom_iso {locRel : Nat → Nat → Prop}
    {left right : Array RVal}
    (related : IxIR1.Sim.RValsIso locRel left.toList right.toList)
    {atom : Atom} {leftValue : RVal}
    (resolved : resolveAtom left atom = .ok leftValue) :
    ∃ rightValue,
      resolveAtom right atom = .ok rightValue ∧
        IxIR1.Sim.RValIso locRel leftValue rightValue := by
  cases atom with
  | reg index =>
      cases found : left[index]? with
      | none => simp [resolveAtom, found] at resolved
      | some actual =>
          simp [resolveAtom, found] at resolved
          subst actual
          obtain ⟨rightValue, rightFound, valueRelated⟩ :=
            rvalsIso_array_getElem? related found
          exact ⟨rightValue, by simp [resolveAtom, rightFound], valueRelated⟩
  | lit literal =>
      simp [resolveAtom] at resolved
      subst leftValue
      exact ⟨.lit literal, by simp [resolveAtom], .lit⟩
  | erased =>
      simp [resolveAtom] at resolved
      subst leftValue
      exact ⟨.erased, by simp [resolveAtom], .erased⟩

private theorem resolveList_iso {locRel : Nat → Nat → Prop}
    {left right : Array RVal}
    (related : IxIR1.Sim.RValsIso locRel left.toList right.toList) :
    ∀ {atoms : List Atom} {leftInitial leftResult : Array RVal},
      atoms.foldlM (fun output atom => do
          return output.push (← resolveAtom left atom)) leftInitial =
        .ok leftResult →
      ∀ {rightInitial : Array RVal},
        IxIR1.Sim.RValsIso locRel leftInitial.toList rightInitial.toList →
        ∃ rightResult,
          atoms.foldlM (fun output atom => do
              return output.push (← resolveAtom right atom)) rightInitial =
            .ok rightResult ∧
          IxIR1.Sim.RValsIso locRel leftResult.toList
            rightResult.toList := by
  intro atoms
  induction atoms with
  | nil =>
      intro leftInitial leftResult resolved rightInitial initialRelated
      change (Except.ok leftInitial : Except Error (Array RVal)) =
        .ok leftResult at resolved
      have same : leftInitial = leftResult := Except.ok.inj resolved
      subst leftResult
      exact ⟨rightInitial, rfl, initialRelated⟩
  | cons atom atoms ih =>
      intro leftInitial leftResult resolved rightInitial initialRelated
      rw [List.foldlM_cons] at resolved
      cases leftResolved : resolveAtom left atom with
      | error error =>
          simp only [leftResolved, bind, Except.bind] at resolved
          cases resolved
      | ok leftValue =>
          simp only [leftResolved, bind, Except.bind] at resolved
          obtain ⟨rightValue, rightResolved, valueRelated⟩ :=
            resolveAtom_iso related leftResolved
          have pushedRelated : IxIR1.Sim.RValsIso locRel
              (leftInitial.push leftValue).toList
              (rightInitial.push rightValue).toList := by
            simpa using rvalsIso_append initialRelated valueRelated
          obtain ⟨rightResult, rightRun, resultRelated⟩ :=
            ih resolved pushedRelated
          refine ⟨rightResult, ?_, resultRelated⟩
          rw [List.foldlM_cons, rightResolved]
          exact rightRun

/-- Batch resolution of an unchanged atom vector is equivariant under any
pointwise runtime-location relation. -/
theorem resolveAtoms_iso {locRel : Nat → Nat → Prop}
    {left right leftValues : Array RVal}
    (related : IxIR1.Sim.RValsIso locRel left.toList right.toList)
    {atoms : Array Atom}
    (resolved : resolveAtoms left atoms = .ok leftValues) :
    ∃ rightValues,
      resolveAtoms right atoms = .ok rightValues ∧
        IxIR1.Sim.RValsIso locRel leftValues.toList rightValues.toList := by
  unfold resolveAtoms at resolved ⊢
  rw [← Array.foldlM_toList]
  apply resolveList_iso related
    (by simpa only [Array.foldlM_toList] using resolved)
  exact .nil

/-- Appending related result values extends the planner's translated register
relation across its distinguished result-register mapping. -/
theorem TranslatedValuesIso.pushResult {shape : Shape}
    {source target : Array RVal} {locRel : Nat → Nat → Prop}
    {sourceResult targetResult : RVal}
    (related : TranslatedValuesIso shape locRel source target)
    (resultRelated : IxIR1.Sim.RValIso locRel sourceResult targetResult)
    (sourceSize : source.size =
      shape.parameterCount + 2 * shape.fieldCount)
    (targetSize : target.size =
      shape.fieldCount + (shape.parameterCount - 1))
    (sourceBound : shape.source < shape.parameterCount) :
    TranslatedValuesIso shape locRel
      (source.push sourceResult) (target.push targetResult) := by
  intro sourceId targetId sourceValue relevant translated sourceAt
  rcases translateRegister?_range sourceBound translated with
    ⟨sourceEnd, targetEnd⟩ | ⟨sourceBefore, targetBefore⟩
  · subst sourceId
    subst targetId
    rw [← sourceSize] at sourceAt
    simp at sourceAt
    subst sourceValue
    refine ⟨targetResult, ?_, resultRelated⟩
    rw [← targetSize]
    simp
  · have sourceNe : sourceId ≠ source.size := by
      rw [sourceSize]
      exact Nat.ne_of_lt sourceBefore
    have targetNe : targetId ≠ target.size := by
      rw [targetSize]
      exact Nat.ne_of_lt targetBefore
    have sourceAtOld : source[sourceId]? = some sourceValue := by
      simpa [Array.getElem?_push, sourceNe] using sourceAt
    obtain ⟨targetValue, targetAt, valueRelated⟩ :=
      related sourceId targetId sourceValue relevant translated sourceAtOld
    refine ⟨targetValue, ?_, valueRelated⟩
    simpa [Array.getElem?_push, targetNe] using targetAt

/-- Resolving one translated atom preserves its runtime value modulo the
chosen location relation. -/
theorem resolveAtom_translate_iso {shape : Shape}
    {locRel : Nat → Nat → Prop} {source target : Array RVal}
    (related : TranslatedValuesIso shape locRel source target)
    {atom translated : Atom} {sourceValue : RVal}
    (relevant : PlannerAtomRelevant shape atom)
    (translation : translateAtom? shape atom = some translated)
    (resolved : resolveAtom source atom = .ok sourceValue) :
    ∃ targetValue,
      resolveAtom target translated = .ok targetValue ∧
      IxIR1.Sim.RValIso locRel sourceValue targetValue := by
  cases atom with
  | reg sourceId =>
      cases translatedAt : translateRegister? shape sourceId with
      | none => simp [translateAtom?, translatedAt] at translation
      | some targetId =>
          simp [translateAtom?, translatedAt] at translation
          subst translated
          cases sourceAt : source[sourceId]? with
          | none => simp [resolveAtom, sourceAt] at resolved
          | some actual =>
              simp [resolveAtom, sourceAt] at resolved
              subst actual
              obtain ⟨targetValue, targetAt, valueRelated⟩ :=
                related sourceId targetId sourceValue relevant translatedAt
                  sourceAt
              exact
                ⟨targetValue, by simp [resolveAtom, targetAt], valueRelated⟩
  | lit literal =>
      simp [translateAtom?] at translation
      subst translated
      simp [resolveAtom] at resolved
      subst sourceValue
      exact ⟨.lit literal, by simp [resolveAtom], .lit⟩
  | erased =>
      simp [translateAtom?] at translation
      subst translated
      simp [resolveAtom] at resolved
      subst sourceValue
      exact ⟨.erased, by simp [resolveAtom], .erased⟩

private theorem resolveList_translate_iso {shape : Shape}
    {locRel : Nat → Nat → Prop} {source target : Array RVal}
    (related : TranslatedValuesIso shape locRel source target) :
    ∀ {atoms translated : List Atom},
      (∀ atom ∈ atoms, PlannerAtomRelevant shape atom) →
      atoms.mapM (translateAtom? shape) = some translated →
      ∀ {sourceInitial sourceResult : Array RVal},
        atoms.foldlM (fun output atom => do
            return output.push (← resolveAtom source atom)) sourceInitial =
              .ok sourceResult →
        ∀ {targetInitial : Array RVal},
          IxIR1.Sim.RValsIso locRel sourceInitial.toList
            targetInitial.toList →
          ∃ targetResult,
            translated.foldlM (fun output atom => do
                return output.push (← resolveAtom target atom)) targetInitial =
              .ok targetResult ∧
            IxIR1.Sim.RValsIso locRel sourceResult.toList
              targetResult.toList := by
  intro atoms
  induction atoms with
  | nil =>
      intro translated _relevant translation sourceInitial sourceResult resolved
        targetInitial initialRelated
      simp at translation
      subst translated
      change (Except.ok sourceInitial : Except Error (Array RVal)) =
        .ok sourceResult at resolved
      have sourceEq : sourceInitial = sourceResult := Except.ok.inj resolved
      subst sourceResult
      exact ⟨targetInitial, rfl, initialRelated⟩
  | cons atom atoms ih =>
      intro translated relevant translation sourceInitial sourceResult resolved
        targetInitial initialRelated
      cases atomAt : translateAtom? shape atom with
      | none => simp [List.mapM_cons, atomAt] at translation
      | some translatedAtom =>
          cases tailAt : atoms.mapM (translateAtom? shape) with
          | none => simp [List.mapM_cons, atomAt, tailAt] at translation
          | some translatedAtoms =>
              simp [List.mapM_cons, atomAt, tailAt] at translation
              subst translated
              rw [List.foldlM_cons] at resolved
              cases sourceResolved : resolveAtom source atom with
              | error error =>
                  simp only [sourceResolved, bind, Except.bind] at resolved
                  cases resolved
              | ok sourceValue =>
                  simp only [sourceResolved, bind, Except.bind] at resolved
                  obtain ⟨targetValue, targetResolved, valueRelated⟩ :=
                    resolveAtom_translate_iso related
                      (relevant atom (by simp)) atomAt sourceResolved
                  have pushedRelated : IxIR1.Sim.RValsIso locRel
                      (sourceInitial.push sourceValue).toList
                      (targetInitial.push targetValue).toList := by
                    simpa using rvalsIso_append initialRelated valueRelated
                  obtain ⟨targetResult, targetRun, resultRelated⟩ :=
                    ih (fun tailAtom member =>
                      relevant tailAtom (by simp [member])) tailAt resolved
                      pushedRelated
                  refine ⟨targetResult, ?_, resultRelated⟩
                  rw [List.foldlM_cons, targetResolved]
                  change translatedAtoms.foldlM (fun output atom => do
                      return output.push (← resolveAtom target atom))
                    (targetInitial.push targetValue) = .ok targetResult
                  exact targetRun

/-- Batch operand resolution commutes with the planner translation modulo an
arbitrary runtime-location relation. -/
theorem resolveAtoms_translate_iso {shape : Shape}
    {locRel : Nat → Nat → Prop} {source target : Array RVal}
    (related : TranslatedValuesIso shape locRel source target)
    {atoms translated : Array Atom} {sourceValues : Array RVal}
    (relevant : ∀ atom ∈ atoms.toList,
      PlannerAtomRelevant shape atom)
    (translation : translateAtoms? shape atoms = some translated)
    (resolved : resolveAtoms source atoms = .ok sourceValues) :
    ∃ targetValues,
      resolveAtoms target translated = .ok targetValues ∧
      IxIR1.Sim.RValsIso locRel sourceValues.toList targetValues.toList := by
  unfold translateAtoms? at translation
  cases mappedAt : atoms.toList.mapM (translateAtom? shape) with
  | none => simp [mappedAt] at translation
  | some translatedAtoms =>
      simp [mappedAt] at translation
      subst translated
      unfold resolveAtoms at resolved ⊢
      rw [← Array.foldlM_toList]
      apply resolveList_translate_iso related relevant mappedAt
        (by simpa only [Array.foldlM_toList] using resolved)
      exact .nil

/-- Accepted allocation operands resolve on the helper side to values related
to the baseline operands by the chosen location relation. -/
theorem resolveAllocationArguments_iso {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {locRel : Nat → Nat → Prop} {source target sourceValues : Array RVal}
    (related : TranslatedValuesIso site.shape locRel source target)
    (resolved : resolveAtoms source site.shape.allocationArguments =
      .ok sourceValues) :
    ∃ targetValues,
      resolveAtoms target site.candidate.allocationArguments =
        .ok targetValues ∧
      IxIR1.Sim.RValsIso locRel sourceValues.toList targetValues.toList :=
  resolveAtoms_translate_iso related (by
    intro atom member
    cases atom with
    | reg sourceId => exact .inl member
    | lit | erased => trivial) site.allocationArgumentsFound resolved

/-- Accepted tail operands resolve on the helper side to values related to
the baseline operands by the chosen location relation. -/
theorem resolveTailArguments_iso {limits : Validate.Limits}
    {context : Validate.Context} {block : Block}
    (site : Reuse.Site limits context block)
    {locRel : Nat → Nat → Prop} {source target sourceValues : Array RVal}
    (related : TranslatedValuesIso site.shape locRel source target)
    (resolved : resolveAtoms source site.shape.tailArguments =
      .ok sourceValues) :
    ∃ targetValues,
      resolveAtoms target site.candidate.tailArguments = .ok targetValues ∧
      IxIR1.Sim.RValsIso locRel sourceValues.toList targetValues.toList :=
  resolveAtoms_translate_iso related (by
    intro atom member
    cases atom with
    | reg sourceId => exact .inr member
    | lit | erased => trivial) site.tailArgumentsFound resolved

/-- The concrete canonical baseline/helper entry files are related modulo any
location relation that self-relates the surviving baseline values. -/
theorem translatedValuesIso_helperEntry {shape : Shape}
    {parameters fields : Array RVal} {locRel : Nat → Nat → Prop}
    (parameterCount : parameters.size = shape.parameterCount)
    (fieldCount : fields.size = shape.fieldCount)
    (sourceBound : shape.source < shape.parameterCount)
    (selfRelated : ∀ (sourceId targetId : Nat) (sourceValue : RVal),
      PlannerValueRelevant shape sourceId →
      translateRegister? shape sourceId = some targetId →
      (baselinePrefixValues parameters fields)[sourceId]? =
        some sourceValue →
      IxIR1.Sim.RValIso locRel sourceValue sourceValue) :
    TranslatedValuesIso shape locRel
      (baselinePrefixValues parameters fields)
      (helperEntryValues shape.source parameters fields) :=
  (valuesRel_helperEntry parameterCount fieldCount sourceBound).toTranslatedValuesIso
    selfRelated

/-- Appending two related allocation results to the canonical baseline and
helper files yields the location-renaming relation required by tail operand
resolution. -/
theorem translatedValuesIso_afterAllocation {shape : Shape}
    {parameters fields : Array RVal} {locRel : Nat → Nat → Prop}
    {sourceResult targetResult : RVal}
    (parameterCount : parameters.size = shape.parameterCount)
    (fieldCount : fields.size = shape.fieldCount)
    (sourceBound : shape.source < shape.parameterCount)
    (selfRelated : ∀ (sourceId targetId : Nat) (sourceValue : RVal),
      PlannerValueRelevant shape sourceId →
      translateRegister? shape sourceId = some targetId →
      (baselinePrefixValues parameters fields)[sourceId]? =
        some sourceValue →
      IxIR1.Sim.RValIso locRel sourceValue sourceValue)
    (resultRelated :
      IxIR1.Sim.RValIso locRel sourceResult targetResult) :
    TranslatedValuesIso shape locRel
      ((baselinePrefixValues parameters fields).push sourceResult)
      ((helperEntryValues shape.source parameters fields).push
        targetResult) := by
  apply TranslatedValuesIso.pushResult
    (translatedValuesIso_helperEntry parameterCount fieldCount sourceBound
      selfRelated) resultRelated
  · simp [baselinePrefixValues, parameterCount, fieldCount, Nat.two_mul]
  · simp [helperEntryValues, List.length_eraseIdx, parameterCount,
      fieldCount, sourceBound]
  · exact sourceBound

/-- An absent optional credit performs fresh allocation and then the helper's
self tail call in exactly two steps.  Allocation and tail operand resolution
are transported from the recognized baseline register files. -/
theorem absentHelperControl {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {helperId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation}
    (helperAt : definition.blocks[helperId]? = some
      (Reuse.creditBlock site.candidate
        (.optional site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (layout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := helperId
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some
          { layout := site.candidate.layout
            presence := .absent }] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds machine.store allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (machine.store.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let allocation := machine.store.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context interpretation 2 machine
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
  dsimp only
  let credit : Credit :=
    { layout := site.candidate.layout, presence := .absent }
  let initial : Frame :=
    { definition
      block := helperId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  let advanced : Frame :=
    { initial with pc := 1, credits := #[none] }
  let allocation := machine.store.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let afterAllocation : Frame :=
    { advanced with
      values := (helperEntryValues site.shape.source parameters fields).push
        (.loc allocation.2) }
  have helperResolved : resolveAtoms initial.values
      site.candidate.allocationArguments = .ok newFields := by
    apply resolveAllocationArguments site
      (valuesRel_helperEntry parameterCount fieldCount site.fits.sourceBound)
    simpa [initial] using allocationResolved
  have creditAt : ({ initial with pc := initial.pc + 1 } : Frame).credits[0]? =
      some (some credit) := by
    simp [initial, credit]
  have taken : CreditTake { initial with pc := initial.pc + 1 } 0
      advanced credit := by
    have := CreditTake.of_lookup (CreditLookup.of_getElem creditAt)
    simpa [initial, advanced, Array.setIfInBounds] using this
  have allocationStep : Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running afterAllocation stack } := by
    have step := Step.allocWithAbsent
      (context := context) (interpretation := interpretation)
      (machine := machine) (frame := initial) (next := advanced)
      (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.optional site.candidate.layout))
      (creditId := 0) (credit := credit) (world := .shared)
      (cid := site.shape.allocationConstructor)
      (arguments := site.candidate.allocationArguments)
      (schema := allocationSchema) (values := newFields)
      (by simpa [initial] using control) helperAt
      (by simp [initial, site.creditBlock_eq])
      (by simp [initial, site.creditBlock_eq]) schemaAt helperResolved
      fieldWorlds taken layout rfl
    simpa [allocation, afterAllocation, advanced, initial, credit] using step
  have helperTailResolved : resolveAtoms afterAllocation.values
      site.candidate.tailArguments = .ok callValues := by
    apply resolveTailArguments site
      (valuesRel_afterAllocation parameterCount fieldCount
        site.fits.sourceBound)
    simpa [afterAllocation, advanced, initial, allocation] using tailResolved
  have noCredits : NoLiveCredits afterAllocation := by
    simp [NoLiveCredits, afterAllocation, advanced]
  have tailStep : Step context interpretation
      { machine with
        store := allocation.1
        control := .running afterAllocation stack }
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
    apply Step.tailCallSelfCleared
      (frame := afterAllocation) (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.optional site.candidate.layout))
      (arguments := site.candidate.tailArguments) (values := callValues)
    · rfl
    · simpa [afterAllocation, advanced, initial] using helperAt
    · simp [afterAllocation, advanced, Reuse.creditBlock]
    · rfl
    · exact noCredits
    · exact helperTailResolved
    · simpa [afterAllocation, advanced, initial] using arity
    · simpa [afterAllocation, advanced, initial] using nonempty
  have first := allocationStep.toSteps (by simpa [initial] using control)
  have second := tailStep.toSteps (by rfl)
  simpa [allocation] using first.trans second

/-- A present logical credit records a reuse opportunity, performs the same
fresh semantic allocation as the baseline, and then enters the recursive
self call in exactly two steps. -/
theorem logicalPresentHelperControl {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function} {helperId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation}
    (helperAt : definition.blocks[helperId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (layout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := helperId
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some
          { layout := site.candidate.layout
            presence := .present none }] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds machine.store allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (machine.store.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let allocation := machine.store.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context .logical 2 machine
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
  dsimp only
  let credit : Credit :=
    { layout := site.candidate.layout, presence := .present none }
  let initial : Frame :=
    { definition
      block := helperId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  let advanced : Frame :=
    { initial with pc := 1, credits := #[none] }
  let allocation := machine.store.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let afterAllocation : Frame :=
    { advanced with
      values := (helperEntryValues site.shape.source parameters fields).push
        (.loc allocation.2) }
  have helperResolved : resolveAtoms initial.values
      site.candidate.allocationArguments = .ok newFields := by
    apply resolveAllocationArguments site
      (valuesRel_helperEntry parameterCount fieldCount site.fits.sourceBound)
    simpa [initial] using allocationResolved
  have creditAt : ({ initial with pc := initial.pc + 1 } : Frame).credits[0]? =
      some (some credit) := by
    simp [initial, credit]
  have taken : CreditTake { initial with pc := initial.pc + 1 } 0
      advanced credit := by
    have := CreditTake.of_lookup (CreditLookup.of_getElem creditAt)
    simpa [initial, advanced, Array.setIfInBounds] using this
  have allocationStep : Step context .logical machine
      { machine with
        store := allocation.1
        control := .running afterAllocation stack } := by
    have step := Step.allocWithLogical
      (context := context) (machine := machine) (frame := initial)
      (next := advanced) (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.required site.candidate.layout))
      (creditId := 0) (credit := credit) (world := .shared)
      (cid := site.shape.allocationConstructor)
      (arguments := site.candidate.allocationArguments)
      (schema := allocationSchema) (values := newFields)
      (by simpa [initial] using control) helperAt
      (by simp [initial, site.creditBlock_eq])
      (by simp [initial, site.creditBlock_eq]) schemaAt helperResolved
      fieldWorlds taken layout rfl
    simpa [allocation, afterAllocation, advanced, initial, credit] using step
  have helperTailResolved : resolveAtoms afterAllocation.values
      site.candidate.tailArguments = .ok callValues := by
    apply resolveTailArguments site
      (valuesRel_afterAllocation parameterCount fieldCount
        site.fits.sourceBound)
    simpa [afterAllocation, advanced, initial, allocation] using tailResolved
  have noCredits : NoLiveCredits afterAllocation := by
    simp [NoLiveCredits, afterAllocation, advanced]
  have tailStep : Step context .logical
      { machine with
        store := allocation.1
        control := .running afterAllocation stack }
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
    apply Step.tailCallSelfCleared
      (frame := afterAllocation) (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.required site.candidate.layout))
      (arguments := site.candidate.tailArguments) (values := callValues)
    · rfl
    · simpa [afterAllocation, advanced, initial] using helperAt
    · simp [afterAllocation, advanced, Reuse.creditBlock]
    · rfl
    · exact noCredits
    · exact helperTailResolved
    · simpa [afterAllocation, advanced, initial] using arity
    · simpa [afterAllocation, advanced, initial] using nonempty
  have first := allocationStep.toSteps (by simpa [initial] using control)
  have second := tailStep.toSteps (by rfl)
  simpa [allocation] using first.trans second

/-- The accepted logical hot arm reaches its recursive self call in four
genuine steps: reset, credit branch, fresh allocation, and tail call. -/
theorem hotLogicalAcceptedControl {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (unitRC : box.rc = 1)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds
      (((machine.store.tickResetAttempt).kill location).tickHotReset)
      allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc ((((machine.store.tickResetAttempt).kill location).tickHotReset
          ).allocNode .shared
            (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let resetStore :=
      ((machine.store.tickResetAttempt).kill location).tickHotReset
    let allocation := resetStore.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context .logical 4 machine
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
  dsimp only
  let resetStore :=
    ((machine.store.tickResetAttempt).kill location).tickHotReset
  let helperMachine : Machine :=
    { machine with
      store := resetStore
      control := .running
        { definition
          block := hotId
          pc := 0
          values := helperEntryValues site.shape.source parameters fields
          credits := #[some
            { layout := site.candidate.layout
              presence := .present none }] }
        stack }
  let allocation := resetStore.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have prefixSteps : Steps context .logical 2 machine helperMachine := by
    simpa [helperMachine, resetStore, sourceLayout] using
      hotLogicalControlPrefix site resetAt hotAt sourceSchemaAt control
        parameterCount fieldCount sourceResolved viewed unitRC
  have helperSteps : Steps context .logical 2 helperMachine
      { helperMachine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
    simpa [helperMachine, allocation, resetStore] using
      logicalPresentHelperControl site (machine := helperMachine) hotAt
        allocationSchemaAt allocationLayout (by rfl) parameterCount fieldCount
        allocationResolved (by simpa [helperMachine, resetStore] using
          fieldWorlds)
        (by simpa [helperMachine, allocation, resetStore] using tailResolved)
        arity nonempty
  simpa [helperMachine, allocation, resetStore] using
    prefixSteps.trans helperSteps

/-- The accepted cold arm reaches its recursive self call in four genuine
steps under either credit interpretation. -/
theorem coldAcceptedControl {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {resetId hotId coldId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema allocationSchema : CtorSchema} {machine : Machine}
    {resetStore : Store} {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (coldAt : definition.blocks[coldId]? = some
      (Reuse.creditBlock site.candidate
        (.optional site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (shared : 1 < box.rc)
    (retained : RetainSharedMany
      ((((machine.store.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      fields resetStore)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds resetStore allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (resetStore.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let allocation := resetStore.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context interpretation 4 machine
      { machine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
  dsimp only
  let helperMachine : Machine :=
    { machine with
      store := resetStore
      control := .running
        { definition
          block := coldId
          pc := 0
          values := helperEntryValues site.shape.source parameters fields
          credits := #[some
            { layout := site.candidate.layout
              presence := .absent }] }
        stack }
  let allocation := resetStore.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have prefixSteps : Steps context interpretation 2 machine helperMachine := by
    simpa [helperMachine, sourceLayout] using
      coldControlPrefix site resetAt coldAt sourceSchemaAt control
        parameterCount fieldCount sourceResolved viewed shared retained
  have helperSteps : Steps context interpretation 2 helperMachine
      { helperMachine with
        store := allocation.1
        control := .running { definition, values := callValues } stack } := by
    simpa [helperMachine, allocation] using
      absentHelperControl site (machine := helperMachine) coldAt
        allocationSchemaAt allocationLayout (by rfl) parameterCount fieldCount
        allocationResolved (by simpa [helperMachine] using fieldWorlds)
        (by simpa [helperMachine, allocation] using tailResolved)
        arity nonempty
  simpa [helperMachine, allocation] using prefixSteps.trans helperSteps

/-- A present physical credit rewrites the reserved source slot and then
enters the recursive self call in exactly two steps.  Unlike the logical
theorem, the tail operands are stated in the physical register file: relating
its reused location to the baseline's fresh location is the heap-isomorphism
obligation of the surrounding simulation. -/
theorem physicalPresentHelperControl {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function} {helperId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation} {location : Nat} {store : Store}
    (helperAt : definition.blocks[helperId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (layout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := helperId
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some
          { layout := site.candidate.layout
            presence := .present (some location) }] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds machine.store allocationSchema newFields)
    (reused : machine.store.reuseReservation location .shared
      (.ctorN site.shape.allocationConstructor newFields)
      allocationSchema.fields.size = .ok store)
    (tailResolved : resolveAtoms
      ((helperEntryValues site.shape.source parameters fields).push
        (.loc location))
      site.candidate.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Steps context .physical 2 machine
      { machine with
        store
        control := .running { definition, values := callValues } stack } := by
  let credit : Credit :=
    { layout := site.candidate.layout,
      presence := .present (some location) }
  let initial : Frame :=
    { definition
      block := helperId
      pc := 0
      values := helperEntryValues site.shape.source parameters fields
      credits := #[some credit] }
  let advanced : Frame :=
    { initial with pc := 1, credits := #[none] }
  let afterAllocation : Frame :=
    { advanced with
      values := (helperEntryValues site.shape.source parameters fields).push
        (.loc location) }
  have helperResolved : resolveAtoms initial.values
      site.candidate.allocationArguments = .ok newFields := by
    apply resolveAllocationArguments site
      (valuesRel_helperEntry parameterCount fieldCount site.fits.sourceBound)
    simpa [initial] using allocationResolved
  have creditAt : ({ initial with pc := initial.pc + 1 } : Frame).credits[0]? =
      some (some credit) := by
    simp [initial, credit]
  have taken : CreditTake { initial with pc := initial.pc + 1 } 0
      advanced credit := by
    have := CreditTake.of_lookup (CreditLookup.of_getElem creditAt)
    simpa [initial, advanced, Array.setIfInBounds] using this
  have allocationStep : Step context .physical machine
      { machine with
        store
        control := .running afterAllocation stack } := by
    have step := Step.allocWithPhysical
      (context := context) (machine := machine) (frame := initial)
      (next := advanced) (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.required site.candidate.layout))
      (creditId := 0) (credit := credit) (world := .shared)
      (cid := site.shape.allocationConstructor)
      (arguments := site.candidate.allocationArguments)
      (schema := allocationSchema) (values := newFields)
      (location := location) (store := store)
      (by simpa [initial] using control) helperAt
      (by simp [initial, site.creditBlock_eq])
      (by simp [initial, site.creditBlock_eq]) schemaAt helperResolved
      fieldWorlds taken layout rfl reused
    simpa [afterAllocation, advanced, initial, credit] using step
  have noCredits : NoLiveCredits afterAllocation := by
    simp [NoLiveCredits, afterAllocation, advanced]
  have tailStep : Step context .physical
      { machine with
        store
        control := .running afterAllocation stack }
      { machine with
        store
        control := .running { definition, values := callValues } stack } := by
    apply Step.tailCallSelfCleared
      (frame := afterAllocation) (stack := stack)
      (block := Reuse.creditBlock site.candidate
        (.required site.candidate.layout))
      (arguments := site.candidate.tailArguments) (values := callValues)
    · rfl
    · simpa [afterAllocation, advanced, initial] using helperAt
    · simp [afterAllocation, advanced, Reuse.creditBlock]
    · rfl
    · exact noCredits
    · simpa [afterAllocation, advanced, initial] using tailResolved
    · simpa [afterAllocation, advanced, initial] using arity
    · simpa [afterAllocation, advanced, initial] using nonempty
  have first := allocationStep.toSteps (by simpa [initial] using control)
  have second := tailStep.toSteps (by rfl)
  simpa using first.trans second

/-- Physical helper execution transported from baseline tail resolution.
The recursive argument vectors are related by the post-reuse heap
isomorphism rather than equated. -/
theorem physicalPresentHelperControlIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function} {helperId : BlockId}
    {parameters fields newFields baselineCallValues : Array RVal}
    {allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation} {location baselineLocation : Nat}
    {store : Store} {baselineHeap : IxIR1.Store}
    (helperAt : definition.blocks[helperId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (layout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := helperId
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some
          { layout := site.candidate.layout
            presence := .present (some location) }] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds machine.store allocationSchema newFields)
    (reused : machine.store.reuseReservation location .shared
      (.ctorN site.shape.allocationConstructor newFields)
      allocationSchema.fields.size = .ok store)
    (iso : IxIR1.Sim.HeapIso store.heap baselineHeap)
    (selfRelated : ∀ (sourceId targetId : Nat) (sourceValue : RVal),
      PlannerValueRelevant site.shape sourceId →
      translateRegister? site.shape sourceId = some targetId →
      (baselinePrefixValues parameters fields)[sourceId]? =
        some sourceValue →
      IxIR1.Sim.RValIso (fun baseline physical =>
        iso.locRel physical baseline) sourceValue sourceValue)
    (resultRelated : iso.locRel location baselineLocation)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc baselineLocation))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    ∃ physicalCallValues,
      Steps context .physical 2 machine
        { machine with
          store
          control := .running
            { definition, values := physicalCallValues } stack } ∧
      IxIR1.Sim.RValsIso (fun baseline physical =>
        iso.locRel physical baseline)
        baselineCallValues.toList physicalCallValues.toList := by
  have registerRelation : TranslatedValuesIso site.shape
      (fun baseline physical => iso.locRel physical baseline)
      ((baselinePrefixValues parameters fields).push
        (.loc baselineLocation))
      ((helperEntryValues site.shape.source parameters fields).push
        (.loc location)) :=
    translatedValuesIso_afterAllocation parameterCount fieldCount
      site.fits.sourceBound selfRelated (.loc resultRelated)
  obtain ⟨physicalCallValues, physicalTailResolved, callsRelated⟩ :=
    resolveTailArguments_iso site registerRelation tailResolved
  have sizeEq : baselineCallValues.size = physicalCallValues.size := by
    simpa using rvalsIso_length_eq callsRelated
  have physicalArity : physicalCallValues.size =
      definition.signature.params.size := sizeEq.symm.trans arity
  refine ⟨physicalCallValues, ?_, callsRelated⟩
  exact physicalPresentHelperControl site helperAt schemaAt layout control
    parameterCount fieldCount allocationResolved fieldWorlds reused
    physicalTailResolved physicalArity nonempty

/-- Physical helper execution from an arbitrary translated baseline register
file.  Unlike `physicalPresentHelperControlIso`, this interface does not
require the preserved operands to be literally equal on both sides, so it can
consume a location relation inherited from an earlier physical reuse. -/
theorem physicalPresentHelperControlTranslated {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function} {helperId : BlockId}
    {parameters fields newFields baselineTailValues baselineCallValues :
      Array RVal}
    {allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation} {location : Nat}
    {store : Store} {locRel : Nat → Nat → Prop}
    (helperAt : definition.blocks[helperId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (layout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := helperId
        pc := 0
        values := helperEntryValues site.shape.source parameters fields
        credits := #[some
          { layout := site.candidate.layout
            presence := .present (some location) }] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds machine.store allocationSchema newFields)
    (reused : machine.store.reuseReservation location .shared
      (.ctorN site.shape.allocationConstructor newFields)
      allocationSchema.fields.size = .ok store)
    (registerRelation : TranslatedValuesIso site.shape locRel
      baselineTailValues
      ((helperEntryValues site.shape.source parameters fields).push
        (.loc location)))
    (tailResolved : resolveAtoms baselineTailValues
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    ∃ physicalCallValues,
      Steps context .physical 2 machine
        { machine with
          store
          control := .running
            { definition, values := physicalCallValues } stack } ∧
      IxIR1.Sim.RValsIso locRel baselineCallValues.toList
        physicalCallValues.toList := by
  obtain ⟨physicalCallValues, physicalTailResolved, callsRelated⟩ :=
    resolveTailArguments_iso site registerRelation tailResolved
  have sizeEq : baselineCallValues.size = physicalCallValues.size := by
    simpa using rvalsIso_length_eq callsRelated
  have physicalArity : physicalCallValues.size =
      definition.signature.params.size := sizeEq.symm.trans arity
  refine ⟨physicalCallValues, ?_, callsRelated⟩
  exact physicalPresentHelperControl site helperAt schemaAt layout control
    parameterCount fieldCount allocationResolved fieldWorlds reused
    physicalTailResolved physicalArity nonempty

/-- The accepted physical hot arm reaches a recursively related call in four
genuine target steps: reset, credit branch, reserved-slot allocation, and
self tail call. -/
theorem hotPhysicalAcceptedControlIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields newFields baselineCallValues : Array RVal}
    {location baselineLocation : Nat} {box : IxIR1.NodeBox}
    {sourceSchema allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation} {store : Store}
    {baselineHeap : IxIR1.Store}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (unitRC : box.rc = 1)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds
      (((machine.store.tickResetAttempt).reserve location).tickHotReset)
      allocationSchema newFields)
    (reused : Eval.Store.reuseReservation
      (((machine.store.tickResetAttempt).reserve location).tickHotReset)
      location .shared
      (.ctorN site.shape.allocationConstructor newFields)
      allocationSchema.fields.size = Except.ok store)
    (iso : IxIR1.Sim.HeapIso store.heap baselineHeap)
    (selfRelated : ∀ (sourceId targetId : Nat) (sourceValue : RVal),
      PlannerValueRelevant site.shape sourceId →
      translateRegister? site.shape sourceId = some targetId →
      (baselinePrefixValues parameters fields)[sourceId]? =
        some sourceValue →
      IxIR1.Sim.RValIso (fun baseline physical =>
        iso.locRel physical baseline) sourceValue sourceValue)
    (resultRelated : iso.locRel location baselineLocation)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc baselineLocation))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    ∃ physicalCallValues,
      Steps context .physical 4 machine
        { machine with
          store
          control := .running
            { definition, values := physicalCallValues } stack } ∧
      IxIR1.Sim.RValsIso (fun baseline physical =>
        iso.locRel physical baseline)
        baselineCallValues.toList physicalCallValues.toList := by
  let helperMachine : Machine :=
    { machine with
      store := ((machine.store.tickResetAttempt).reserve location).tickHotReset
      control := .running
        { definition
          block := hotId
          pc := 0
          values := helperEntryValues site.shape.source parameters fields
          credits := #[some
            { layout := site.candidate.layout
              presence := .present (some location) }] }
        stack }
  have prefixSteps : Steps context .physical 2 machine helperMachine := by
    simpa [helperMachine, sourceLayout] using
      hotPhysicalControlPrefix site resetAt hotAt sourceSchemaAt control
        parameterCount fieldCount sourceResolved viewed unitRC
  obtain ⟨physicalCallValues, helperSteps, callsRelated⟩ :=
    physicalPresentHelperControlIso site
      (machine := helperMachine) (store := store)
      (baselineHeap := baselineHeap) hotAt allocationSchemaAt
      allocationLayout (by rfl) parameterCount fieldCount
      allocationResolved (by simpa [helperMachine] using fieldWorlds)
      (by simpa [helperMachine] using reused) iso selfRelated resultRelated
      tailResolved arity nonempty
  refine ⟨physicalCallValues, ?_, callsRelated⟩
  simpa [helperMachine] using prefixSteps.trans helperSteps

/-- Four-step physical accepted execution from an arbitrary translated
baseline tail register file.  This is the control half of composing physical
reuse with an already-isomorphic input state. -/
theorem hotPhysicalAcceptedControlTranslated {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields newFields baselineTailValues baselineCallValues :
      Array RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema allocationSchema : CtorSchema} {machine : Machine}
    {stack : List Continuation} {store : Store}
    {locRel : Nat → Nat → Prop}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (unitRC : box.rc = 1)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds
      (((machine.store.tickResetAttempt).reserve location).tickHotReset)
      allocationSchema newFields)
    (reused : Eval.Store.reuseReservation
      (((machine.store.tickResetAttempt).reserve location).tickHotReset)
      location .shared
      (.ctorN site.shape.allocationConstructor newFields)
      allocationSchema.fields.size = Except.ok store)
    (registerRelation : TranslatedValuesIso site.shape locRel
      baselineTailValues
      ((helperEntryValues site.shape.source parameters fields).push
        (.loc location)))
    (tailResolved : resolveAtoms baselineTailValues
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    ∃ physicalCallValues,
      Steps context .physical 4 machine
        { machine with
          store
          control := .running
            { definition, values := physicalCallValues } stack } ∧
      IxIR1.Sim.RValsIso locRel baselineCallValues.toList
        physicalCallValues.toList := by
  let helperMachine : Machine :=
    { machine with
      store := ((machine.store.tickResetAttempt).reserve location).tickHotReset
      control := .running
        { definition
          block := hotId
          pc := 0
          values := helperEntryValues site.shape.source parameters fields
          credits := #[some
            { layout := site.candidate.layout
              presence := .present (some location) }] }
        stack }
  have prefixSteps : Steps context .physical 2 machine helperMachine := by
    simpa [helperMachine, sourceLayout] using
      hotPhysicalControlPrefix site resetAt hotAt sourceSchemaAt control
        parameterCount fieldCount sourceResolved viewed unitRC
  obtain ⟨physicalCallValues, helperSteps, callsRelated⟩ :=
    physicalPresentHelperControlTranslated site
      (machine := helperMachine) (store := store) hotAt allocationSchemaAt
      allocationLayout (by rfl) parameterCount fieldCount allocationResolved
      (by simpa [helperMachine] using fieldWorlds)
      (by simpa [helperMachine] using reused) registerRelation tailResolved
      arity nonempty
  refine ⟨physicalCallValues, ?_, callsRelated⟩
  simpa [helperMachine] using prefixSteps.trans helperSteps

/-! ## Recognized baseline-block control -/

/-- Values after fetching the first `count` constructor fields. -/
def fetchedPrefixValues (parameters fields : Array RVal) (count : Nat) :
    Array RVal :=
  parameters ++ (fields.toList.take count).toArray

private theorem fetchedPrefixValues_succ {parameters fields : Array RVal}
    {count : Nat} (bound : count < fields.size) :
    (fetchedPrefixValues parameters fields count).push fields[count] =
      fetchedPrefixValues parameters fields (count + 1) := by
  apply Array.toList_inj.mp
  simp only [fetchedPrefixValues, Array.toList_push, Array.toList_append]
  rw [← List.take_append_getElem (l := fields.toList)
    (i := count) (by simpa using bound)]
  simp [List.append_assoc]

/-- Execute all recognized fetches from an accepted baseline block. -/
theorem fetchPrefixControl {limits : Validate.Limits}
    {validation : Validate.Context} {block : Block}
    (site : Reuse.Site limits validation block)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {blockId : BlockId}
    {parameters fields : Array RVal} {location : Nat}
    {box : IxIR1.NodeBox} {machine : Machine}
    {stack : List Continuation}
    (blockAt : definition.blocks[blockId]? = some block)
    (control : machine.control = .running
      { definition
        block := blockId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN site.shape.sourceConstructor fields) :
    Steps context interpretation site.shape.fieldCount machine
      { machine with
        control := .running
          { definition
            block := blockId
            pc := site.shape.fieldCount
            values := parameters ++ fields
            credits := #[] }
          stack } := by
  have loop : ∀ count, count ≤ site.shape.fieldCount →
      Steps context interpretation count machine
        { machine with
          control := .running
            { definition
              block := blockId
              pc := count
              values := fetchedPrefixValues parameters fields count
              credits := #[] }
            stack } := by
    intro count countLe
    induction count with
    | zero =>
        simpa [fetchedPrefixValues, ← control] using Steps.refl machine
    | succ count ih =>
        have countBound : count < site.shape.fieldCount := by omega
        have prefixSteps := ih (by omega)
        let before : Machine :=
          { machine with
            control := .running
              { definition
                block := blockId
                pc := count
                values := fetchedPrefixValues parameters fields count
                credits := #[] }
              stack }
        have instructionAt := site.fits.fetches count countBound
        obtain ⟨pcBound, instruction⟩ :=
          Array.getElem?_eq_some_iff.mp instructionAt
        have resolved : resolveAtom
            (fetchedPrefixValues parameters fields count)
            (.reg site.shape.source) = .ok (.loc location) := by
          simpa [fetchedPrefixValues, resolveAtom,
            Array.getElem?_append, parameterCount,
            site.fits.sourceBound] using sourceResolved
        have fieldBound : count < fields.size := by
          simpa [fieldCount] using countBound
        have fieldAt : fields[count]? = some fields[count] :=
          Array.getElem?_eq_some_iff.mpr ⟨fieldBound, rfl⟩
        have step : Step context interpretation before
            { before with
              control := .running
                { definition
                  block := blockId
                  pc := count + 1
                  values := fetchedPrefixValues parameters fields (count + 1)
                  credits := #[] }
                stack } := by
          have fetched := Step.fetch
            (context := context) (interpretation := interpretation)
            (machine := before)
            (frame :=
              { definition
                block := blockId
                pc := count
                values := fetchedPrefixValues parameters fields count
                credits := #[] })
            (stack := stack) (block := block)
            (atom := .reg site.shape.source)
            (cid := site.shape.sourceConstructor) (field := count)
            (location := location) (box := box) (fields := fields)
            (value := fields[count]) rfl blockAt pcBound instruction resolved
            (by simpa [before] using boxAt) node fieldAt
          simpa [fetchedPrefixValues_succ fieldBound] using fetched
        have one := step.toSteps (by rfl)
        simpa [before, Nat.succ_eq_add_one] using prefixSteps.trans one
  have result := loop site.shape.fieldCount (Nat.le_refl _)
  have allFields : (fields.toList.take site.shape.fieldCount).toArray =
      fields := by
    rw [← fieldCount]
    change (fields.toList.take fields.toList.length).toArray = fields
    rw [List.take_length]
  simpa [fetchedPrefixValues, allFields] using result

private theorem retainedPrefix_push {parameters fields : Array RVal}
    (processed : List RVal) (value : RVal) :
    (parameters ++ fields ++ processed.toArray).push value =
      parameters ++ fields ++ (processed ++ [value]).toArray := by
  apply Array.toList_inj.mp
  simp

private theorem retainSuffixControl {limits : Validate.Limits}
    {validation : Validate.Context} {block : Block}
    (site : Reuse.Site limits validation block)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {blockId : BlockId}
    {parameters fields : Array RVal} {processed remaining : List RVal}
    {startStore finalStore : Store} {heapFuel : Nat}
    {stack : List Continuation}
    (blockAt : definition.blocks[blockId]? = some block)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (split : fields.toList = processed ++ remaining)
    (retained : RetainSharedMany startStore remaining.toArray finalStore) :
    Steps context interpretation remaining.length
      { store := startStore
        heapFuel
        control := .running
          { definition
            block := blockId
            pc := site.shape.fieldCount + processed.length
            values := parameters ++ fields ++ processed.toArray
            credits := #[] }
          stack }
      { store := finalStore
        heapFuel
        control := .running
          { definition
            block := blockId
            pc := site.shape.fieldCount + (processed ++ remaining).length
            values := parameters ++ fields ++
              (processed ++ remaining).toArray
            credits := #[] }
          stack } := by
  induction remaining generalizing processed startStore with
  | nil =>
      change (.ok startStore : Except Error Store) = .ok finalStore at retained
      have storeEq := Except.ok.inj retained
      subst finalStore
      simpa using (Steps.refl
        ({ store := startStore
           heapFuel
           control := .running
             { definition
               block := blockId
               pc := site.shape.fieldCount + processed.length
               values := parameters ++ fields ++ processed.toArray
               credits := #[] }
             stack } : Machine))
  | cons value remaining ih =>
      obtain ⟨middle, headRetained, tailRetained⟩ :=
        RetainSharedMany.cons_inv retained
      have fieldIndexBound : processed.length < site.shape.fieldCount := by
        have lengths := congrArg List.length split
        simp only [List.length_append, List.length_cons] at lengths
        have fieldsLength : fields.toList.length = site.shape.fieldCount := by
          simp [fieldCount]
        omega
      have fieldAt : fields[processed.length]? = some value := by
        rw [Array.getElem?_eq_some_iff]
        refine ⟨?_, ?_⟩
        · simpa [fieldCount] using fieldIndexBound
        · have listAt : fields.toList[processed.length]? = some value := by
            rw [split, List.getElem?_append_right (Nat.le_refl _)]
            simp
          exact Option.some.inj
            ((List.getElem?_eq_getElem (l := fields.toList)
              (i := processed.length) (by simpa [fieldCount] using
                fieldIndexBound)).symm.trans listAt)
      have fieldEq : fields[processed.length] = value :=
        (Array.getElem?_eq_some_iff.mp fieldAt).2
      have resolved : resolveAtom
          (parameters ++ fields ++ processed.toArray)
          (.reg (site.shape.parameterCount + processed.length)) =
          .ok value := by
        simp [resolveAtom, Array.getElem?_append, parameterCount,
          fieldCount, fieldIndexBound, fieldEq,
          show ¬site.shape.parameterCount + processed.length <
            site.shape.parameterCount by omega]
      have instructionAt := site.fits.retains processed.length fieldIndexBound
      obtain ⟨pcBound, instruction⟩ :=
        Array.getElem?_eq_some_iff.mp instructionAt
      let before : Machine :=
        { store := startStore
          heapFuel
          control := .running
            { definition
              block := blockId
              pc := site.shape.fieldCount + processed.length
              values := parameters ++ fields ++ processed.toArray
              credits := #[] }
            stack }
      let afterHead : Machine :=
        { store := middle
          heapFuel
          control := .running
            { definition
              block := blockId
              pc := site.shape.fieldCount + (processed ++ [value]).length
              values := parameters ++ fields ++
                (processed ++ [value]).toArray
              credits := #[] }
            stack }
      have headStep : Step context interpretation before afterHead := by
        have step := Step.retainShared
          (context := context) (interpretation := interpretation)
          (machine := before)
          (frame :=
            { definition
              block := blockId
              pc := site.shape.fieldCount + processed.length
              values := parameters ++ fields ++ processed.toArray
              credits := #[] })
          (stack := stack) (block := block)
          (atom := .reg (site.shape.parameterCount + processed.length))
          (value := value) (store := middle) rfl blockAt pcBound instruction
          resolved headRetained
        simpa [before, afterHead, retainedPrefix_push, List.length_append,
          Nat.add_assoc] using step
      have tailSteps := ih (processed := processed ++ [value])
        (startStore := middle) (by simpa [List.append_assoc] using split)
        tailRetained
      have one := headStep.toSteps (by rfl)
      simpa [before, afterHead, List.append_assoc, Nat.add_comm] using
        one.trans tailSteps

/-- Execute every recognized retain after all fields have been fetched. -/
theorem retainPrefixControl {limits : Validate.Limits}
    {validation : Validate.Context} {block : Block}
    (site : Reuse.Site limits validation block)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {blockId : BlockId}
    {parameters fields : Array RVal} {store retainedStore : Store}
    {heapFuel : Nat} {stack : List Continuation}
    (blockAt : definition.blocks[blockId]? = some block)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (retained : RetainSharedMany store fields retainedStore) :
    Steps context interpretation site.shape.fieldCount
      { store
        heapFuel
        control := .running
          { definition
            block := blockId
            pc := site.shape.fieldCount
            values := parameters ++ fields
            credits := #[] }
          stack }
      { store := retainedStore
        heapFuel
        control := .running
          { definition
            block := blockId
            pc := 2 * site.shape.fieldCount
            values := baselinePrefixValues parameters fields
            credits := #[] }
          stack } := by
  have steps := retainSuffixControl site
    (context := context) (interpretation := interpretation)
    (definition := definition) (blockId := blockId)
    (parameters := parameters) (fields := fields)
    (processed := []) (remaining := fields.toList)
    (startStore := store) (finalStore := retainedStore)
    (heapFuel := heapFuel) (stack := stack) blockAt parameterCount
    fieldCount (by simp) (by simpa using retained)
  simpa [baselinePrefixValues, fieldCount, Nat.two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using steps

/-- Execute the entire arbitrary-arity baseline block recognized at an
accepted reuse site. -/
theorem baselineAcceptedControl {limits : Validate.Limits}
    {validation : Validate.Context} {block : Block}
    (site : Reuse.Site limits validation block)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {blockId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {location : Nat} {box : IxIR1.NodeBox} {machine : Machine}
    {retainedStore releasedStore : Store} {remaining : Nat}
    {allocationSchema : CtorSchema} {stack : List Continuation}
    (blockAt : definition.blocks[blockId]? = some block)
    (control : machine.control = .running
      { definition
        block := blockId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN site.shape.sourceConstructor fields)
    (retained : RetainSharedMany machine.store fields retainedStore)
    (released : releaseShared machine.heapFuel retainedStore (.loc location) =
      .ok (releasedStore, remaining))
    (schemaAt : context.schemas .shared site.shape.allocationConstructor =
      some allocationSchema)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds releasedStore allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (releasedStore.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let allocation := releasedStore.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context interpretation (2 * site.shape.fieldCount + 3) machine
      { store := allocation.1
        heapFuel := remaining
        control := .running { definition, values := callValues } stack } := by
  dsimp only
  let afterFetches : Machine :=
    { machine with
      control := .running
        { definition
          block := blockId
          pc := site.shape.fieldCount
          values := parameters ++ fields
          credits := #[] }
        stack }
  let afterRetains : Machine :=
    { store := retainedStore
      heapFuel := machine.heapFuel
      control := .running
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount
          values := baselinePrefixValues parameters fields
          credits := #[] }
        stack }
  let afterRelease : Machine :=
    { store := releasedStore
      heapFuel := remaining
      control := .running
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount + 1
          values := baselinePrefixValues parameters fields
          credits := #[] }
        stack }
  let allocation := releasedStore.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let afterAllocation : Machine :=
    { store := allocation.1
      heapFuel := remaining
      control := .running
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount + 2
          values := (baselinePrefixValues parameters fields).push
            (.loc allocation.2)
          credits := #[] }
        stack }
  have fetches : Steps context interpretation site.shape.fieldCount machine
      afterFetches := by
    simpa [afterFetches] using
      fetchPrefixControl site blockAt control parameterCount fieldCount
        sourceResolved boxAt node
  have retains : Steps context interpretation site.shape.fieldCount
      afterFetches afterRetains := by
    simpa [afterFetches, afterRetains] using
      retainPrefixControl site (context := context)
        (interpretation := interpretation) (definition := definition)
        (blockId := blockId) (parameters := parameters) (fields := fields)
        (store := machine.store) (retainedStore := retainedStore)
        (heapFuel := machine.heapFuel) (stack := stack) blockAt parameterCount
        fieldCount retained
  have prefixSteps : Steps context interpretation (2 * site.shape.fieldCount)
      machine afterRetains := by
    simpa [Nat.two_mul] using fetches.trans retains
  have sourceResolvedAfter : resolveAtom
      (baselinePrefixValues parameters fields) (.reg site.shape.source) =
      .ok (.loc location) := by
    simpa [baselinePrefixValues, resolveAtom, Array.getElem?_append,
      parameterCount, site.fits.sourceBound] using sourceResolved
  have releaseAt := site.fits.release
  rw [site.fits.releasePosition] at releaseAt
  obtain ⟨releasePc, releaseInstruction⟩ :=
    Array.getElem?_eq_some_iff.mp releaseAt
  have releaseStep : Step context interpretation afterRetains afterRelease := by
    have step := Step.releaseShared
      (context := context) (interpretation := interpretation)
      (machine := afterRetains)
      (frame :=
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount
          values := baselinePrefixValues parameters fields
          credits := #[] })
      (stack := stack) (block := block)
      (atom := .reg site.shape.source) (value := .loc location)
      (store := releasedStore) (heapFuel := remaining) rfl blockAt releasePc
      releaseInstruction sourceResolvedAfter (by simpa [afterRetains] using
        released)
    simpa [afterRetains, afterRelease] using step
  have allocationAt := site.fits.allocation
  rw [site.fits.releasePosition] at allocationAt
  obtain ⟨allocationPc, allocationInstruction⟩ :=
    Array.getElem?_eq_some_iff.mp allocationAt
  have allocationStep : Step context interpretation afterRelease
      afterAllocation := by
    have step := Step.alloc
      (context := context) (interpretation := interpretation)
      (machine := afterRelease)
      (frame :=
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount + 1
          values := baselinePrefixValues parameters fields
          credits := #[] })
      (stack := stack) (block := block) (world := .shared)
      (cid := site.shape.allocationConstructor)
      (arguments := site.shape.allocationArguments)
      (schema := allocationSchema) (values := newFields) rfl blockAt
      allocationPc allocationInstruction schemaAt allocationResolved
      (by simpa [afterRelease] using fieldWorlds)
    simpa [afterRelease, afterAllocation, allocation] using step
  have tailStep : Step context interpretation afterAllocation
      { store := allocation.1
        heapFuel := remaining
        control := .running { definition, values := callValues } stack } := by
    apply Step.tailCallSelf
      (frame :=
        { definition
          block := blockId
          pc := 2 * site.shape.fieldCount + 2
          values := (baselinePrefixValues parameters fields).push
            (.loc allocation.2)
          credits := #[] })
      (stack := stack) (block := block)
      (arguments := site.shape.tailArguments) (values := callValues)
    · rfl
    · simpa [afterAllocation] using blockAt
    · exact site.fits.instructionCount.symm
    · exact site.fits.terminator
    · rfl
    · simpa [allocation] using tailResolved
    · exact arity
    · exact nonempty
  have releaseOne := releaseStep.toSteps (by rfl)
  have allocationOne := allocationStep.toSteps (by rfl)
  have tailOne := tailStep.toSteps (by rfl)
  simpa [allocation] using
    ((prefixSteps.trans releaseOne).trans allocationOne).trans tailOne

/-! ## Concrete hot-path stores -/

/-- Store produced by the logical unit-refcount arm of `resetShared`. -/
def logicalHotResetStore (store : Store) (location : Nat) : Store :=
  ((store.tickResetAttempt).kill location).tickHotReset

/-- Store produced by the physical unit-refcount arm of `resetShared`. -/
def physicalHotResetStore (store : Store) (location : Nat) : Store :=
  ((store.tickResetAttempt).reserve location).tickHotReset

/-- Logical consumption of a present credit allocates the replacement at a
fresh location. -/
def logicalHotReuseStore (store : Store) (location : Nat)
    (node : IxIR1.Node) : Store × Nat :=
  (logicalHotResetStore store location).allocNode .shared node

/-- Physical consumption of a present credit revives the reserved source
slot. -/
def physicalHotReuseStore (store : Store) (location : Nat)
    (node : IxIR1.Node) (payloadUnits : Nat) : Except Error Store :=
  (physicalHotResetStore store location).reuseReservation location .shared
    node payloadUnits

/-! ## Baseline shared-release algebra -/

/-- The store update performed when a shared release sees more than one
owner.  Keeping this operation explicit lets the cold-reset proof commute a
parent decrement with the batch of field retains. -/
def baselineDecrementStore (store : Store) (location : Nat)
    (box : IxIR1.NodeBox) : Store :=
  store.rcTick.setBox location { box with rc := box.rc - 1 }

/-- The successful location branch of one shared retain. -/
def incrementSharedStore (store : Store) (location : Nat)
    (box : IxIR1.NodeBox) : Store :=
  (store.setBox location { box with rc := box.rc + 1 }).rcTick

@[simp] theorem baselineDecrementStore_heap (store : Store)
    (location : Nat) (box : IxIR1.NodeBox) :
    (baselineDecrementStore store location box).heap =
      IxIR1.Sim.decRcStore store.heap location box := by
  rfl

@[simp] theorem incrementSharedStore_heap (store : Store)
    (location : Nat) (box : IxIR1.NodeBox) :
    (incrementSharedStore store location box).heap =
      IxIR1.Sim.incRcStore store.heap location box := by
  rfl

theorem get?_baselineDecrementStore_same {store : Store} {location : Nat}
    {box : IxIR1.NodeBox} (hget : store.get? location = some box) :
    (baselineDecrementStore store location box).get? location =
      some { box with rc := box.rc - 1 } := by
  exact IxIR1.Sim.get?_decRcStore_same hget

theorem get?_baselineDecrementStore_other {store : Store}
    {location other : Nat} {box otherBox : IxIR1.NodeBox}
    (hne : location ≠ other) (hlive : store.get? location = some box)
    (hget : store.get? other = some otherBox) :
    (baselineDecrementStore store location box).get? other =
      some otherBox := by
  exact IxIR1.Sim.get?_decRcStore_other hne hlive hget

theorem get?_incrementSharedStore_same {store : Store} {location : Nat}
    {box : IxIR1.NodeBox} (hget : store.get? location = some box) :
    (incrementSharedStore store location box).get? location =
      some { box with rc := box.rc + 1 } := by
  exact IxIR1.Sim.get?_incRcStore_same hget

theorem get?_incrementSharedStore_other {store : Store}
    {location other : Nat} {box otherBox : IxIR1.NodeBox}
    (hne : location ≠ other) (hlive : store.get? location = some box)
    (hget : store.get? other = some otherBox) :
    (incrementSharedStore store location box).get? other = some otherBox := by
  exact IxIR1.Sim.get?_incRcStore_other hne hlive hget

theorem get?_of_incrementSharedStore_other {store : Store}
    {location other : Nat} {box otherBox : IxIR1.NodeBox}
    (hne : location ≠ other) (hlive : store.get? location = some box)
    (hget : (incrementSharedStore store location box).get? other =
      some otherBox) :
    store.get? other = some otherBox := by
  exact IxIR1.Sim.get?_of_incRcStore_other hne hlive hget

private theorem increment_increment_other (store : Store)
    (first second : Nat) (firstBox secondBox : IxIR1.NodeBox)
    (hne : first ≠ second) :
    incrementSharedStore
        (incrementSharedStore store first firstBox) second secondBox =
      incrementSharedStore
        (incrementSharedStore store second secondBox) first firstBox := by
  cases store with
  | mk heap resetAttempts hotResets coldResets reusedPayloadUnits peakLiveNodes =>
      cases heap with
      | mk nodes allocs reuses frees rcops =>
          simp only [incrementSharedStore, Eval.Store.rcTick,
            Eval.Store.setBox, IxIR1.Store.rcTick, IxIR1.Store.setBox,
            Array.set!_eq_setIfInBounds]
          congr 2
          exact Array.setIfInBounds_comm _ _ hne

private theorem decrement_increment_other (store : Store)
    (target child : Nat) (targetBox childBox : IxIR1.NodeBox)
    (hne : child ≠ target) :
    baselineDecrementStore
        (incrementSharedStore store child childBox) target targetBox =
      incrementSharedStore
        (baselineDecrementStore store target targetBox) child childBox := by
  cases store with
  | mk heap resetAttempts hotResets coldResets reusedPayloadUnits peakLiveNodes =>
      cases heap with
      | mk nodes allocs reuses frees rcops =>
          simp only [baselineDecrementStore, incrementSharedStore,
            Eval.Store.rcTick, Eval.Store.setBox, IxIR1.Store.rcTick,
            IxIR1.Store.setBox, Array.set!_eq_setIfInBounds]
          congr 2
          exact Array.setIfInBounds_comm _ _ hne

private theorem decrement_increment_same (store : Store) (target rc : Nat)
    (node : IxIR1.Node) (hmany : 1 < rc) :
    baselineDecrementStore
        (incrementSharedStore store target ⟨.shared, rc, node⟩) target
        ⟨.shared, rc + 1, node⟩ =
      incrementSharedStore
        (baselineDecrementStore store target ⟨.shared, rc, node⟩) target
        ⟨.shared, rc - 1, node⟩ := by
  cases store with
  | mk heap resetAttempts hotResets coldResets reusedPayloadUnits peakLiveNodes =>
      cases heap with
      | mk nodes allocs reuses frees rcops =>
          simp only [baselineDecrementStore, incrementSharedStore,
            Eval.Store.rcTick, Eval.Store.setBox, IxIR1.Store.rcTick,
            IxIR1.Store.setBox, Array.set!_eq_setIfInBounds,
            Array.setIfInBounds_setIfInBounds]
          have hsub : rc - 1 + 1 = rc := Nat.sub_add_cancel (by omega)
          simp [hsub]

/-- Successful shared retains commute.  Besides supporting the hot-prefix
cancellation proof, this records that the compiler may retain projected
fields in any order without changing the resulting store. -/
theorem retainShared_commute {store afterFirst final : Store}
    {first second : RVal}
    (firstRun : retainShared store first = .ok afterFirst)
    (secondRun : retainShared afterFirst second = .ok final) :
    ∃ afterSecond,
      retainShared store second = .ok afterSecond ∧
      retainShared afterSecond first = .ok final := by
  cases first with
  | lit literal =>
      have storeEq : store = afterFirst := by
        simpa [retainShared] using firstRun
      subst afterFirst
      exact ⟨final, secondRun, by simp [retainShared]⟩
  | erased =>
      have storeEq : store = afterFirst := by
        simpa [retainShared] using firstRun
      subst afterFirst
      exact ⟨final, secondRun, by simp [retainShared]⟩
  | loc firstLocation =>
      cases firstAt : store.get? firstLocation with
      | none => simp [retainShared, firstAt] at firstRun
      | some firstBox =>
          cases firstBox with
          | mk firstWorld firstRc firstNode =>
              cases firstWorld with
              | unique => simp [retainShared, firstAt] at firstRun
              | shared =>
                  have afterFirstEq :
                      incrementSharedStore store firstLocation
                        ⟨.shared, firstRc, firstNode⟩ = afterFirst := by
                    simpa [retainShared, firstAt, incrementSharedStore] using
                      firstRun
                  subst afterFirst
                  cases second with
                  | lit literal =>
                      have finalEq :
                          incrementSharedStore store firstLocation
                            ⟨.shared, firstRc, firstNode⟩ = final := by
                        simpa [retainShared] using secondRun
                      subst final
                      exact ⟨store, by simp [retainShared], firstRun⟩
                  | erased =>
                      have finalEq :
                          incrementSharedStore store firstLocation
                            ⟨.shared, firstRc, firstNode⟩ = final := by
                        simpa [retainShared] using secondRun
                      subst final
                      exact ⟨store, by simp [retainShared], firstRun⟩
                  | loc secondLocation =>
                      by_cases same : firstLocation = secondLocation
                      · subst secondLocation
                        exact ⟨incrementSharedStore store firstLocation
                            ⟨.shared, firstRc, firstNode⟩,
                          firstRun, secondRun⟩
                      · cases secondAt :
                            (incrementSharedStore store firstLocation
                              ⟨.shared, firstRc, firstNode⟩).get?
                                secondLocation with
                        | none => simp [retainShared, secondAt] at secondRun
                        | some secondBox =>
                            cases secondBox with
                            | mk secondWorld secondRc secondNode =>
                                cases secondWorld with
                                | unique =>
                                    simp [retainShared, secondAt] at secondRun
                                | shared =>
                                    have finalEq :
                                        incrementSharedStore
                                            (incrementSharedStore store
                                              firstLocation
                                              ⟨.shared, firstRc, firstNode⟩)
                                            secondLocation
                                            ⟨.shared, secondRc, secondNode⟩ =
                                          final := by
                                      simp only [retainShared] at secondRun
                                      rw [secondAt] at secondRun
                                      simpa [incrementSharedStore] using secondRun
                                    subst final
                                    have secondOriginal :=
                                      get?_of_incrementSharedStore_other same
                                        firstAt secondAt
                                    let afterSecond :=
                                      incrementSharedStore store secondLocation
                                        ⟨.shared, secondRc, secondNode⟩
                                    have runSecond :
                                        retainShared store (.loc secondLocation) =
                                          .ok afterSecond := by
                                      simp [retainShared, secondOriginal,
                                        afterSecond, incrementSharedStore]
                                    have firstAfterSecond :=
                                      get?_incrementSharedStore_other
                                        (Ne.symm same) secondOriginal firstAt
                                    refine ⟨afterSecond, runSecond, ?_⟩
                                    have runFirst :
                                        retainShared afterSecond
                                            (.loc firstLocation) =
                                          .ok (incrementSharedStore afterSecond
                                            firstLocation
                                            ⟨.shared, firstRc, firstNode⟩) := by
                                      simp only [retainShared]
                                      rw [firstAfterSecond]
                                      rfl
                                    rw [runFirst]
                                    exact congrArg Except.ok
                                      (increment_increment_other store
                                        firstLocation secondLocation
                                        ⟨.shared, firstRc, firstNode⟩
                                        ⟨.shared, secondRc, secondNode⟩
                                        same).symm

/-- Rotate the first retain of a successful batch to the end.  This is the
algebraic normalization used by the hot proof to place one retain directly
beside the matching release. -/
theorem RetainSharedMany.rotate_head {store target : Store}
    {head : RVal} {tail : List RVal}
    (run : RetainSharedMany store (head :: tail).toArray target) :
    ∃ middle,
      RetainSharedMany store tail.toArray middle ∧
      retainShared middle head = .ok target := by
  induction tail generalizing store target head with
  | nil =>
      obtain ⟨afterHead, headRun, emptyRun⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      change (.ok afterHead : Except Error Store) = .ok target at emptyRun
      injection emptyRun with targetEq
      subst target
      exact ⟨store, RetainSharedMany.empty _, headRun⟩
  | cons second rest ih =>
      obtain ⟨afterHead, headRun, tailRun⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      obtain ⟨afterBoth, secondRun, restRun⟩ :=
        Eval.RetainSharedMany.cons_inv (run := tailRun)
      obtain ⟨afterSecond, secondFirst, headSecond⟩ :=
        retainShared_commute headRun secondRun
      have rotatedInput :
          RetainSharedMany afterSecond (head :: rest).toArray target :=
        RetainSharedMany.cons headSecond restRun
      obtain ⟨middle, restFirst, headLast⟩ := ih rotatedInput
      exact ⟨middle, RetainSharedMany.cons secondFirst restFirst, headLast⟩

/-- Retaining a value other than `target` leaves the target box exactly
unchanged. -/
theorem retainShared_preserves_box {store retained : Store}
    {target : Nat} {targetBox : IxIR1.NodeBox} {value : RVal}
    (targetAt : store.get? target = some targetBox)
    (different : value ≠ .loc target)
    (run : retainShared store value = .ok retained) :
    retained.get? target = some targetBox := by
  cases value with
  | lit literal =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      exact targetAt
  | erased =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      exact targetAt
  | loc location =>
      have locationNe : location ≠ target := by
        intro same
        subst location
        exact different rfl
      cases valueAt : store.get? location with
      | none => simp [retainShared, valueAt] at run
      | some valueBox =>
          cases valueBox with
          | mk world rc node =>
              cases world with
              | unique => simp [retainShared, valueAt] at run
              | shared =>
                  have retainedEq :
                      incrementSharedStore store location
                        ⟨.shared, rc, node⟩ = retained := by
                    simpa [retainShared, valueAt, incrementSharedStore] using run
                  subst retained
                  exact get?_incrementSharedStore_other locationNe valueAt
                    targetAt

/-- A batch of retains leaves an unrelated box exactly unchanged. -/
theorem RetainSharedMany.preserves_box {store retained : Store}
    {target : Nat} {targetBox : IxIR1.NodeBox} {values : List RVal}
    (targetAt : store.get? target = some targetBox)
    (different : ∀ value ∈ values, value ≠ .loc target)
    (run : RetainSharedMany store values.toArray retained) :
    retained.get? target = some targetBox := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact targetAt
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      have middleAt := retainShared_preserves_box targetAt
        (different value (by simp)) head
      exact ih middleAt (fun candidate member =>
        different candidate (by simp [member])) tail

private theorem kill_increment_other (store : Store) (target child : Nat)
    (box : IxIR1.NodeBox) (hne : child ≠ target) :
    (incrementSharedStore store child box).kill target =
      incrementSharedStore (store.kill target) child box := by
  cases store with
  | mk heap resetAttempts hotResets coldResets reusedPayloadUnits peakLiveNodes =>
      cases heap with
      | mk nodes allocs reuses frees rcops =>
          simp only [incrementSharedStore, Eval.Store.kill,
            Eval.Store.setBox, Eval.Store.rcTick, IxIR1.Store.kill,
            IxIR1.Store.setBox, IxIR1.Store.rcTick,
            Array.set!_eq_setIfInBounds]
          congr 2
          exact Array.setIfInBounds_comm _ _ hne

/-- A retain of a non-parent value commutes with killing the parent. -/
theorem retainShared_kill_commute {store retained : Store}
    {target : Nat} {targetBox : IxIR1.NodeBox} {value : RVal}
    (targetAt : store.get? target = some targetBox)
    (different : value ≠ .loc target)
    (run : retainShared store value = .ok retained) :
    retainShared (store.kill target) value = .ok (retained.kill target) := by
  cases value with
  | lit literal =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | erased =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | loc location =>
      have locationNe : location ≠ target := by
        intro same
        subst location
        exact different rfl
      cases valueAt : store.get? location with
      | none => simp [retainShared, valueAt] at run
      | some valueBox =>
          cases valueBox with
          | mk world rc node =>
              cases world with
              | unique => simp [retainShared, valueAt] at run
              | shared =>
                  have retainedEq :
                      incrementSharedStore store location
                        ⟨.shared, rc, node⟩ = retained := by
                    simpa [retainShared, valueAt, incrementSharedStore] using run
                  subst retained
                  have valueAfterKill : (store.kill target).get? location =
                      some ⟨.shared, rc, node⟩ :=
                    IxIR1.Sim.get?_kill_other (Ne.symm locationNe) targetAt
                      valueAt
                  rw [show retainShared (store.kill target) (.loc location) =
                      .ok (incrementSharedStore (store.kill target) location
                        ⟨.shared, rc, node⟩) by
                    simp [retainShared, valueAfterKill, incrementSharedStore]]
                  exact congrArg Except.ok
                    (kill_increment_other store target location
                      ⟨.shared, rc, node⟩ locationNe).symm

/-- Batch field retention commutes with killing an unrelated parent. -/
theorem RetainSharedMany.kill_commute {store retained : Store}
    {target : Nat} {targetBox : IxIR1.NodeBox} {values : List RVal}
    (targetAt : store.get? target = some targetBox)
    (different : ∀ value ∈ values, value ≠ .loc target)
    (run : RetainSharedMany store values.toArray retained) :
    RetainSharedMany (store.kill target) values.toArray
      (retained.kill target) := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact RetainSharedMany.empty _
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      have valueDifferent := different value (by simp)
      have headKilled := retainShared_kill_commute targetAt valueDifferent head
      have middleAt := retainShared_preserves_box targetAt valueDifferent head
      have tailKilled := ih middleAt (fun candidate member =>
        different candidate (by simp [member])) tail
      exact RetainSharedMany.cons headKilled tailKilled

/-- One successful field retain commutes with the non-final decrement of a
shared parent.  The result also exposes the parent's updated box so the
statement can be iterated when a field aliases the parent. -/
theorem retainShared_decrement_commute {store retained : Store}
    {target rc : Nat} {node : IxIR1.Node} {value : RVal}
    (hget : store.get? target = some ⟨.shared, rc, node⟩)
    (hmany : 1 < rc)
    (hretain : retainShared store value = .ok retained) :
    ∃ retainedRc,
      retained.get? target = some ⟨.shared, retainedRc, node⟩ ∧
      1 < retainedRc ∧
      retainShared
          (baselineDecrementStore store target ⟨.shared, rc, node⟩)
          value =
        .ok (baselineDecrementStore retained target
          ⟨.shared, retainedRc, node⟩) := by
  cases value with
  | lit literal =>
      simp [retainShared] at hretain
      subst retained
      exact ⟨rc, hget, hmany, rfl⟩
  | erased =>
      simp [retainShared] at hretain
      subst retained
      exact ⟨rc, hget, hmany, rfl⟩
  | loc child =>
      cases hchild : store.get? child with
      | none => simp [retainShared, hchild] at hretain
      | some childBox =>
          cases childBox with
          | mk childWorld childRc childNode =>
              cases childWorld with
              | unique => simp [retainShared, hchild] at hretain
              | shared =>
                  have retainedEq :
                      incrementSharedStore store child
                          ⟨.shared, childRc, childNode⟩ = retained := by
                    simpa [retainShared, hchild, incrementSharedStore] using
                      hretain
                  subst retained
                  by_cases heq : child = target
                  · subst child
                    have boxEq :
                        (⟨.shared, childRc, childNode⟩ : IxIR1.NodeBox) =
                          ⟨.shared, rc, node⟩ :=
                      Option.some.inj (hchild.symm.trans hget)
                    cases boxEq
                    refine ⟨rc + 1,
                      get?_incrementSharedStore_same hget,
                      by omega, ?_⟩
                    have decremented := get?_baselineDecrementStore_same hget
                    rw [show retainShared
                        (baselineDecrementStore store target
                          ⟨.shared, rc, node⟩) (.loc target) =
                        .ok (incrementSharedStore
                          (baselineDecrementStore store target
                            ⟨.shared, rc, node⟩) target
                          ⟨.shared, rc - 1, node⟩) by
                      simp [retainShared, decremented, incrementSharedStore]]
                    exact congrArg Except.ok
                      (decrement_increment_same store target rc node hmany).symm
                  · refine ⟨rc,
                      get?_incrementSharedStore_other heq hchild hget,
                      hmany, ?_⟩
                    have childAfter := get?_baselineDecrementStore_other
                      (Ne.symm heq) hget hchild
                    rw [show retainShared
                        (baselineDecrementStore store target
                          ⟨.shared, rc, node⟩) (.loc child) =
                        .ok (incrementSharedStore
                          (baselineDecrementStore store target
                            ⟨.shared, rc, node⟩) child
                          ⟨.shared, childRc, childNode⟩) by
                      simp [retainShared, childAfter, incrementSharedStore]]
                    exact congrArg Except.ok
                      (decrement_increment_other store target child
                        ⟨.shared, rc, node⟩
                        ⟨.shared, childRc, childNode⟩ heq).symm

/-- A whole successful field-retain prefix commutes with a non-final parent
decrement.  The theorem permits repeated fields and even a parent-valued
field; the updated parent box is threaded explicitly through the induction. -/
theorem RetainSharedMany.decrement_commute {store retained : Store}
    {target rc : Nat} {node : IxIR1.Node} {values : List RVal}
    (hget : store.get? target = some ⟨.shared, rc, node⟩)
    (hmany : 1 < rc)
    (run : RetainSharedMany store values.toArray retained) :
    ∃ retainedRc,
      retained.get? target = some ⟨.shared, retainedRc, node⟩ ∧
      1 < retainedRc ∧
      RetainSharedMany
        (baselineDecrementStore store target ⟨.shared, rc, node⟩)
        values.toArray
        (baselineDecrementStore retained target
          ⟨.shared, retainedRc, node⟩) := by
  induction values generalizing store retained rc node with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact ⟨rc, hget, hmany, RetainSharedMany.empty _⟩
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      obtain ⟨middleRc, middleAt, middleMany, headCommutes⟩ :=
        retainShared_decrement_commute hget hmany head
      obtain ⟨retainedRc, retainedAt, retainedMany, tailCommutes⟩ :=
        ih middleAt middleMany tail
      exact ⟨retainedRc, retainedAt, retainedMany,
        RetainSharedMany.cons headCommutes tailCommutes⟩

/-- Reset-attempt accounting commutes with a successful shared retain. -/
theorem retainShared_tickResetAttempt {store retained : Store}
    {value : RVal} (run : retainShared store value = .ok retained) :
    retainShared store.tickResetAttempt value =
      .ok retained.tickResetAttempt := by
  cases value with
  | lit literal =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | erased =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | loc location =>
      cases hget : store.get? location with
      | none => simp [retainShared, hget] at run
      | some box =>
          cases box with
          | mk world rc node =>
              cases world with
              | unique => simp [retainShared, hget] at run
              | shared =>
                  have retainedEq :
                      incrementSharedStore store location
                        ⟨.shared, rc, node⟩ = retained := by
                    simpa [retainShared, hget, incrementSharedStore] using run
                  subst retained
                  have heapGet : store.heap.get? location =
                      some ⟨.shared, rc, node⟩ := hget
                  simp [retainShared, heapGet, incrementSharedStore,
                    Eval.Store.tickResetAttempt, Eval.Store.get?,
                    Eval.Store.setBox, Eval.Store.rcTick]

/-- Cold-reset accounting commutes with a successful shared retain. -/
theorem retainShared_tickColdReset {store retained : Store}
    {value : RVal} (run : retainShared store value = .ok retained) :
    retainShared store.tickColdReset value =
      .ok retained.tickColdReset := by
  cases value with
  | lit literal =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | erased =>
      have storeEq : store = retained := by
        simpa [retainShared] using run
      subst retained
      rfl
  | loc location =>
      cases hget : store.get? location with
      | none => simp [retainShared, hget] at run
      | some box =>
          cases box with
          | mk world rc node =>
              cases world with
              | unique => simp [retainShared, hget] at run
              | shared =>
                  have retainedEq :
                      incrementSharedStore store location
                        ⟨.shared, rc, node⟩ = retained := by
                    simpa [retainShared, hget, incrementSharedStore] using run
                  subst retained
                  have heapGet : store.heap.get? location =
                      some ⟨.shared, rc, node⟩ := hget
                  simp [retainShared, heapGet, incrementSharedStore,
                    Eval.Store.tickColdReset, Eval.Store.get?,
                    Eval.Store.setBox, Eval.Store.rcTick]

/-- Batch field retention is insensitive to when reset-attempt accounting is
recorded. -/
theorem RetainSharedMany.tickResetAttempt {store retained : Store}
    {values : List RVal}
    (run : RetainSharedMany store values.toArray retained) :
    RetainSharedMany store.tickResetAttempt values.toArray
      retained.tickResetAttempt := by
  induction values generalizing store retained with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact RetainSharedMany.empty _
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      exact RetainSharedMany.cons
        (retainShared_tickResetAttempt head) (ih tail)

/-- Batch field retention is insensitive to when cold-reset accounting is
recorded. -/
theorem RetainSharedMany.tickColdReset {store retained : Store}
    {values : List RVal}
    (run : RetainSharedMany store values.toArray retained) :
    RetainSharedMany store.tickColdReset values.toArray
      retained.tickColdReset := by
  induction values generalizing store retained with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact RetainSharedMany.empty _
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      exact RetainSharedMany.cons
        (retainShared_tickColdReset head) (ih tail)

/-! ## Counter-insensitive heap congruence -/

/-- Exact semantic heap state, deliberately forgetting allocation/reset cost
counters.  Unlike `HeapIso`, this relation keeps location identities fixed;
it is the right intermediate relation for cancellation of baseline RC
traffic. -/
structure HeapContentsEq (left right : Store) : Prop where
  nodes : left.heap.nodes = right.heap.nodes

namespace HeapContentsEq

theorem refl (store : Store) : HeapContentsEq store store := ⟨rfl⟩

theorem symm {left right : Store} (h : HeapContentsEq left right) :
    HeapContentsEq right left := ⟨h.nodes.symm⟩

theorem trans {first second third : Store}
    (h₁ : HeapContentsEq first second) (h₂ : HeapContentsEq second third) :
    HeapContentsEq first third := ⟨h₁.nodes.trans h₂.nodes⟩

theorem get?_eq {left right : Store} (h : HeapContentsEq left right)
    (location : Nat) : left.get? location = right.get? location := by
  simp [Eval.Store.get?, IxIR1.Store.get?, h.nodes]

/-- Exact heap contents make dynamic ownership-world checks identical at a
fixed runtime value. -/
theorem rvalHasWorld_eq {left right : Store} (h : HeapContentsEq left right)
    (world : Owned) (value : RVal) :
    RVal.hasWorld left world value = RVal.hasWorld right world value := by
  cases value with
  | loc location =>
      simp [RVal.hasWorld, h.get?_eq location]
  | lit literal => rfl
  | erased => rfl

/-- Field validation transports across counter-insensitive exact heap
contents without a second executable checker premise. -/
theorem fieldWorlds {left right : Store} (h : HeapContentsEq left right)
    {schema : CtorSchema} {values : Array RVal}
    (worlds : FieldWorlds left schema values) :
    FieldWorlds right schema values :=
  FieldWorlds.congrStore
    (fun world value => h.rvalHasWorld_eq world value) worlds

theorem fieldWorlds_iff {left right : Store} (h : HeapContentsEq left right)
    {schema : CtorSchema} {values : Array RVal} :
    FieldWorlds left schema values ↔ FieldWorlds right schema values :=
  ⟨h.fieldWorlds, h.symm.fieldWorlds⟩

/-- Constructor views are preserved at fixed locations. -/
theorem constructorView {left right : Store} (h : HeapContentsEq left right)
    {location : Nat} {world : Owned} {cid : CtorId}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (viewed : ConstructorView left location world cid box fields) :
    ConstructorView right location world cid box fields :=
  ConstructorView.congrStore (h.get?_eq location) viewed

/-- One successful shared retain is congruent under exact semantic heap
contents, including its refcount update. -/
theorem retainShared {left right leftOut : Store}
    (h : HeapContentsEq left right) {value : RVal}
    (run : Eval.retainShared left value = .ok leftOut) :
    ∃ rightOut,
      Eval.retainShared right value = .ok rightOut ∧
      HeapContentsEq leftOut rightOut := by
  cases value with
  | lit literal =>
      have leftEq : left = leftOut := by
        simpa [Eval.retainShared] using run
      subst leftOut
      exact ⟨right, by simp [Eval.retainShared], h⟩
  | erased =>
      have leftEq : left = leftOut := by
        simpa [Eval.retainShared] using run
      subst leftOut
      exact ⟨right, by simp [Eval.retainShared], h⟩
  | loc location =>
      cases leftAt : left.get? location with
      | none => simp [Eval.retainShared, leftAt] at run
      | some box =>
          have rightAt : right.get? location = some box := by
            rw [← h.get?_eq location]
            exact leftAt
          cases box with
          | mk boxWorld rc node =>
              cases boxWorld with
              | unique => simp [Eval.retainShared, leftAt] at run
              | shared =>
                  have leftOutEq :
                      (left.setBox location
                        ⟨.shared, rc + 1, node⟩).rcTick = leftOut := by
                    simpa [Eval.retainShared, leftAt] using run
                  subst leftOut
                  refine ⟨(right.setBox location
                    ⟨.shared, rc + 1, node⟩).rcTick, ?_, ?_⟩
                  · simp [Eval.retainShared, rightAt]
                  · constructor
                    simp [Eval.Store.setBox, Eval.Store.rcTick,
                      IxIR1.Store.setBox, IxIR1.Store.rcTick, h.nodes]

/-- Batch shared retain is congruent under exact semantic heap contents. -/
theorem retainSharedMany {left right leftOut : Store}
    (h : HeapContentsEq left right) {values : Array RVal}
    (run : RetainSharedMany left values leftOut) :
    ∃ rightOut,
      RetainSharedMany right values rightOut ∧
      HeapContentsEq leftOut rightOut := by
  have loop : ∀ (entries : List RVal) {left right leftOut : Store},
      HeapContentsEq left right →
      RetainSharedMany left entries.toArray leftOut →
      ∃ rightOut,
        RetainSharedMany right entries.toArray rightOut ∧
        HeapContentsEq leftOut rightOut := by
    intro entries
    induction entries with
    | nil =>
        intro left right leftOut contents retained
        change (.ok left : Except Error Store) = .ok leftOut at retained
        injection retained with leftEq
        subst leftOut
        exact ⟨right, rfl, contents⟩
    | cons head tail ih =>
        intro left right leftOut contents retained
        obtain ⟨leftMiddle, headRun, tailRun⟩ :=
          Eval.RetainSharedMany.cons_inv (run := retained)
        obtain ⟨rightMiddle, rightHead, middleContents⟩ :=
          contents.retainShared headRun
        obtain ⟨rightOut, rightTail, finalContents⟩ :=
          ih middleContents tailRun
        exact ⟨rightOut,
          Eval.RetainSharedMany.cons rightHead rightTail, finalContents⟩
  have normalized :
      RetainSharedMany left values.toList.toArray leftOut := by
    simpa using run
  obtain ⟨rightOut, rightRun, contents⟩ :=
    loop values.toList h normalized
  exact ⟨rightOut, by simpa using rightRun, contents⟩

theorem rcTick {left right : Store} (h : HeapContentsEq left right) :
    HeapContentsEq left.rcTick right.rcTick := by
  exact ⟨h.nodes⟩

theorem setBox {left right : Store} (h : HeapContentsEq left right)
    (location : Nat) (box : IxIR1.NodeBox) :
    HeapContentsEq (left.setBox location box) (right.setBox location box) := by
  constructor
  simp [Eval.Store.setBox, IxIR1.Store.setBox, h.nodes]

theorem kill {left right : Store} (h : HeapContentsEq left right)
    (location : Nat) :
    HeapContentsEq (left.kill location) (right.kill location) := by
  constructor
  simp [Eval.Store.kill, IxIR1.Store.kill, h.nodes]

theorem reserve {left right : Store} (h : HeapContentsEq left right)
    (location : Nat) :
    HeapContentsEq (left.reserve location) (right.reserve location) := by
  constructor
  simp [Eval.Store.reserve, h.nodes]

theorem tickResetAttempt {left right : Store}
    (h : HeapContentsEq left right) :
    HeapContentsEq left.tickResetAttempt right.tickResetAttempt :=
  ⟨h.nodes⟩

theorem tickHotReset {left right : Store} (h : HeapContentsEq left right) :
    HeapContentsEq left.tickHotReset right.tickHotReset :=
  ⟨h.nodes⟩

theorem tickColdReset {left right : Store} (h : HeapContentsEq left right) :
    HeapContentsEq left.tickColdReset right.tickColdReset :=
  ⟨h.nodes⟩

/-- Releasing the same reserved slot succeeds congruently in exact-content
stores; only observational free counters may differ. -/
theorem releaseReservation {left right leftOut : Store}
    (h : HeapContentsEq left right) {location : Nat}
    (run : left.releaseReservation location = .ok leftOut) :
    ∃ rightOut,
      right.releaseReservation location = .ok rightOut ∧
      HeapContentsEq leftOut rightOut := by
  cases found : left.heap.nodes[location]? with
  | none =>
      simp [Eval.Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box =>
          simp [Eval.Store.releaseReservation, found] at run
      | none =>
          have rightAt : right.heap.nodes[location]? = some none := by
            rw [← h.nodes]
            exact found
          have leftOutEq :
              { left with
                heap := { left.heap with frees := left.heap.frees + 1 } } =
                leftOut := by
            simpa [Eval.Store.releaseReservation, found] using run
          subst leftOut
          refine ⟨
            { right with
              heap := { right.heap with frees := right.heap.frees + 1 } },
            ?_, ⟨h.nodes⟩⟩
          simp [Eval.Store.releaseReservation, rightAt]

/-- Reusing the same reserved slot with the same payload is congruent under
exact heap contents. -/
theorem reuseReservation {left right leftOut : Store}
    (h : HeapContentsEq left right) {location : Nat} {world : Owned}
    {node : IxIR1.Node} {payloadUnits : Nat}
    (run : left.reuseReservation location world node payloadUnits =
      .ok leftOut) :
    ∃ rightOut,
      right.reuseReservation location world node payloadUnits = .ok rightOut ∧
      HeapContentsEq leftOut rightOut := by
  cases found : left.heap.nodes[location]? with
  | none =>
      simp [Eval.Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box =>
          simp [Eval.Store.reuseReservation, found] at run
      | none =>
          have rightAt : right.heap.nodes[location]? = some none := by
            rw [← h.nodes]
            exact found
          cases rightRun :
              right.reuseReservation location world node payloadUnits with
          | error error =>
              simp [Eval.Store.reuseReservation, rightAt] at rightRun
          | ok rightOut =>
              refine ⟨rightOut, rfl, ?_⟩
              have leftNodes := congrArg
                (fun result : Except Error Store =>
                  result.map (fun output => output.heap.nodes)) run
              have rightNodes := congrArg
                (fun result : Except Error Store =>
                  result.map (fun output => output.heap.nodes)) rightRun
              have leftNodes' :
                  left.heap.nodes.setIfInBounds location
                      (some { world, rc := 1, node }) =
                    leftOut.heap.nodes := by
                simpa [Eval.Store.reuseReservation, found, Except.map]
                  using leftNodes
              have rightNodes' :
                  right.heap.nodes.setIfInBounds location
                      (some { world, rc := 1, node }) =
                    rightOut.heap.nodes := by
                simpa [Eval.Store.reuseReservation, rightAt, Except.map]
                  using rightNodes
              constructor
              exact leftNodes'.symm.trans
                ((congrArg
                  (fun nodes => nodes.setIfInBounds location
                    (some { world, rc := 1, node })) h.nodes).trans
                  rightNodes')

theorem allocNode {left right : Store} (h : HeapContentsEq left right)
    (world : Owned) (node : IxIR1.Node) :
    HeapContentsEq (left.allocNode world node).1
      (right.allocNode world node).1 := by
  constructor
  simp [Eval.Store.allocNode, IxIR1.Store.allocNode, h.nodes]

theorem allocNode_location {left right : Store}
    (h : HeapContentsEq left right) (world : Owned) (node : IxIR1.Node) :
    (left.allocNode world node).2 = (right.allocNode world node).2 := by
  simp [Eval.Store.allocNode, IxIR1.Store.allocNode, h.nodes]

theorem hasWorld {left right : Store} (h : HeapContentsEq left right)
    {world : Owned} {value : RVal}
    (live : IxIR1.Sim.HasWorld left.heap world value) :
    IxIR1.Sim.HasWorld right.heap world value := by
  cases value with
  | lit literal => trivial
  | erased => trivial
  | loc location =>
      obtain ⟨box, boxAt, boxWorld⟩ := live
      refine ⟨box, ?_, boxWorld⟩
      change right.get? location = some box
      rw [← h.get?_eq location]
      exact boxAt

/-- Exact node-array equality transports exact ownership without changing
the root list. -/
theorem rootOwnership {left right : Store} (h : HeapContentsEq left right)
    {roots : List IxIR1.Sim.Root}
    (owned : IxIR1.Sim.RootOwnership left.heap roots) :
    IxIR1.Sim.RootOwnership right.heap roots := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root member
    exact h.hasWorld (owned.roots_world root member)
  · intro location box boxAt child member
    have leftAt : left.heap.get? location = some box := by
      change left.get? location = some box
      rw [h.get?_eq location]
      exact boxAt
    exact h.hasWorld (owned.edges_world leftAt child member)
  · intro location box address arity arguments boxAt node
    have leftAt : left.heap.get? location = some box := by
      change left.get? location = some box
      rw [h.get?_eq location]
      exact boxAt
    exact owned.pap_shared leftAt node
  · intro location box boxAt
    have leftAt : left.heap.get? location = some box := by
      change left.get? location = some box
      rw [h.get?_eq location]
      exact boxAt
    simpa [IxIR1.Sim.incoming, IxIR1.Sim.edgeLocations, h.nodes] using
      owned.counts leftAt

/-- Fixed-location heap contents induce a live-heap isomorphism; cost
counters and dead-slot metadata remain unobservable. -/
def toHeapIso {left right : Store} (h : HeapContentsEq left right)
    (closed : IxIR1.Sim.StoreClosed left.heap) :
    IxIR1.Sim.HeapIso left.heap right.heap :=
  let identity := IxIR1.Sim.HeapIso.refl left.heap closed
  { locRel := identity.locRel
    left_unique := identity.left_unique
    right_unique := identity.right_unique
    left_total := identity.left_total
    right_total := by
      intro location box rightAt
      have leftAt : left.heap.get? location = some box := by
        change left.get? location = some box
        rw [h.get?_eq location]
        exact rightAt
      exact identity.right_total leftAt
    related_live := by
      intro leftLocation rightLocation related
      obtain ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩ :=
        identity.related_live related
      have rightAt' : right.heap.get? rightLocation = some rightBox := by
        change right.get? rightLocation = some rightBox
        rw [← h.get?_eq rightLocation]
        exact rightAt
      exact ⟨leftBox, rightBox, leftAt, rightAt', boxes⟩ }

theorem toHeapIso_rel_self {left right : Store}
    (h : HeapContentsEq left right)
    (closed : IxIR1.Sim.StoreClosed left.heap) {location : Nat}
    {box : IxIR1.NodeBox} (live : left.get? location = some box) :
    (h.toHeapIso closed).locRel location location := by
  change location = location ∧ ∃ box, left.heap.get? location = some box
  exact ⟨rfl, box, live⟩

end HeapContentsEq

/-- A live-heap isomorphism is a valid initial allocation-history
isomorphism.  It simply has no dead/dead rows yet; later reclamation steps
may retain those rows so stale, unreachable register slots remain related. -/
def heapIsoToHistory {left right : IxIR1.Store}
    (iso : IxIR1.Sim.HeapIso left right) :
    IxIR1.Sim.HeapHistoryIso left right where
  locRel := iso.locRel
  left_unique := iso.left_unique
  right_unique := iso.right_unique
  left_bound := by
    intro leftLocation rightLocation related
    obtain ⟨leftBox, _rightBox, leftAt, _rightAt, _boxes⟩ :=
      iso.related_live related
    exact (Array.getElem?_eq_some_iff.mp
      (IxIR1.Sim.nodes_get?_of_get? leftAt)).1
  right_bound := by
    intro leftLocation rightLocation related
    obtain ⟨_leftBox, rightBox, _leftAt, rightAt, _boxes⟩ :=
      iso.related_live related
    exact (Array.getElem?_eq_some_iff.mp
      (IxIR1.Sim.nodes_get?_of_get? rightAt)).1
  left_total := iso.left_total
  right_total := iso.right_total
  related := by
    intro leftLocation rightLocation related
    exact .inr (iso.related_live related)

private theorem nodeIso_ctor_left {locRel : Nat → Nat → Prop}
    {cid : CtorId} {leftFields : Array RVal} {rightNode : IxIR1.Node}
    (related : IxIR1.Sim.NodeIso locRel (.ctorN cid leftFields) rightNode) :
    ∃ rightFields : Array RVal,
      rightNode = .ctorN cid rightFields ∧
        IxIR1.Sim.RValsIso locRel leftFields.toList rightFields.toList := by
  cases related with
  | ctor fields => exact ⟨_, rfl, fields⟩

private theorem nodeIso_pap_left {locRel : Nat → Nat → Prop}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {leftArguments : Array RVal} {rightNode : IxIR1.Node}
    (related : IxIR1.Sim.NodeIso locRel
      (.papN address arity leftArguments) rightNode) :
    ∃ rightArguments : Array RVal,
      rightNode = .papN address arity rightArguments ∧
        IxIR1.Sim.RValsIso locRel
          leftArguments.toList rightArguments.toList := by
  cases related with
  | pap arguments => exact ⟨_, rfl, arguments⟩

/-! ## Removing a related hot-reset source -/

private theorem rvalsIso_restrict_left {locRel : Nat → Nat → Prop}
    {left right : List RVal} {removed : Nat}
    (related : IxIR1.Sim.RValsIso locRel left right)
    (avoids : ∀ value ∈ left, value ≠ .loc removed) :
    IxIR1.Sim.RValsIso
      (fun leftLocation rightLocation =>
        locRel leftLocation rightLocation ∧ leftLocation ≠ removed)
      left right := by
  induction related with
  | nil => exact .nil
  | @cons leftValue rightValue lefts rights head tail ih =>
      have headAvoids : leftValue ≠ .loc removed :=
        avoids leftValue (by simp)
      have tailAvoids : ∀ value ∈ lefts, value ≠ .loc removed := by
        intro value member
        exact avoids value (by simp [member])
      refine .cons ?_ (ih tailAvoids)
      cases head with
      | loc locationRelated =>
          apply IxIR1.Sim.RValIso.loc
          refine ⟨locationRelated, ?_⟩
          intro same
          apply headAvoids
          cases same
          rfl
      | lit => exact .lit
      | erased => exact .erased

private theorem rvalsIso_right_avoids_of_left
    {leftStore rightStore : IxIR1.Store}
    (iso : IxIR1.Sim.HeapIso rightStore leftStore)
    {leftRemoved rightRemoved : Nat}
    (removedRelated : iso.locRel rightRemoved leftRemoved)
    {left right : List RVal}
    (related : IxIR1.Sim.RValsIso
      (fun leftLocation rightLocation =>
        iso.locRel rightLocation leftLocation) left right)
    (leftAvoids : ∀ value ∈ left, value ≠ .loc leftRemoved) :
    ∀ value ∈ right, value ≠ .loc rightRemoved := by
  induction related with
  | nil => simp
  | @cons leftValue rightValue lefts rights head tail ih =>
      have headAvoids : leftValue ≠ .loc leftRemoved :=
        leftAvoids leftValue (by simp)
      have tailAvoids : ∀ value ∈ lefts, value ≠ .loc leftRemoved := by
        intro value member
        exact leftAvoids value (by simp [member])
      intro value member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · cases head with
        | loc locationRelated =>
            intro same
            cases same
            have leftSame := iso.left_unique locationRelated removedRelated
            apply headAvoids
            cases leftSame
            rfl
        | lit => intro impossible; cases impossible
        | erased => intro impossible; cases impossible
      · exact ih tailAvoids value member

private theorem nodeIso_restrict_left {locRel : Nat → Nat → Prop}
    {left right : IxIR1.Node} {removed : Nat}
    (related : IxIR1.Sim.NodeIso locRel left right)
    (avoids : ∀ value ∈ IxIR1.Sim.nodeChildren left,
      value ≠ .loc removed) :
    IxIR1.Sim.NodeIso
      (fun leftLocation rightLocation =>
        locRel leftLocation rightLocation ∧ leftLocation ≠ removed)
      left right := by
  cases related with
  | ctor values =>
      apply IxIR1.Sim.NodeIso.ctor
      apply rvalsIso_restrict_left values
      simpa [IxIR1.Sim.nodeChildren] using avoids
  | pap values =>
      apply IxIR1.Sim.NodeIso.pap
      apply rvalsIso_restrict_left values
      simpa [IxIR1.Sim.nodeChildren] using avoids

/-- Removing two related unit-refcount shared nodes preserves the existing
live-heap bijection on every surviving location. Exact ownership on the left
excludes hidden incoming heap edges to the consumed node, which is precisely
what permits the location pair to be removed from the relation. -/
def heapIsoKillShared {left right : IxIR1.Store}
    (iso : IxIR1.Sim.HeapIso left right)
    {leftLocation rightLocation : Nat}
    {leftNode rightNode : IxIR1.Node} {leftRest : List IxIR1.Sim.Root}
    (locations : iso.locRel leftLocation rightLocation)
    (leftAt : left.get? leftLocation =
      some ⟨.shared, 1, leftNode⟩)
    (rightAt : right.get? rightLocation =
      some ⟨.shared, 1, rightNode⟩)
    (leftOwned : IxIR1.Sim.RootOwnership left
      (⟨.shared, .loc leftLocation⟩ :: leftRest)) :
    IxIR1.Sim.HeapIso (left.kill leftLocation)
      (right.kill rightLocation) := by
  let kept : Nat → Nat → Prop := fun leftCandidate rightCandidate =>
    iso.locRel leftCandidate rightCandidate ∧
      leftCandidate ≠ leftLocation
  refine
    { locRel := kept
      left_unique := ?_
      right_unique := ?_
      left_total := ?_
      right_total := ?_
      related_live := ?_ }
  · intro leftCandidate right₁ right₂ first second
    exact iso.left_unique first.1 second.1
  · intro left₁ left₂ rightCandidate first second
    exact iso.right_unique first.1 second.1
  · intro leftCandidate box live
    have different : leftLocation ≠ leftCandidate := by
      intro same
      subst leftCandidate
      rw [IxIR1.Sim.get?_kill_same leftAt] at live
      contradiction
    have original : left.get? leftCandidate = some box :=
      IxIR1.Sim.get?_of_kill_other different leftAt live
    obtain ⟨rightCandidate, related⟩ := iso.left_total original
    exact ⟨rightCandidate, related, Ne.symm different⟩
  · intro rightCandidate box live
    have different : rightLocation ≠ rightCandidate := by
      intro same
      subst rightCandidate
      rw [IxIR1.Sim.get?_kill_same rightAt] at live
      contradiction
    have original : right.get? rightCandidate = some box :=
      IxIR1.Sim.get?_of_kill_other different rightAt live
    obtain ⟨leftCandidate, related⟩ := iso.right_total original
    have leftDifferent : leftCandidate ≠ leftLocation := by
      intro same
      subst leftCandidate
      exact different (iso.left_unique locations related)
    exact ⟨leftCandidate, related, leftDifferent⟩
  · intro leftCandidate rightCandidate related
    obtain ⟨leftBox, rightBox, leftLive, rightLive, boxes⟩ :=
      iso.related_live related.1
    have rightDifferent : rightLocation ≠ rightCandidate := by
      intro same
      subst rightCandidate
      exact related.2 (iso.right_unique related.1 locations)
    have leftKilled : (left.kill leftLocation).get? leftCandidate =
        some leftBox :=
      IxIR1.Sim.get?_kill_other (Ne.symm related.2) leftAt leftLive
    have rightKilled : (right.kill rightLocation).get? rightCandidate =
        some rightBox :=
      IxIR1.Sim.get?_kill_other rightDifferent rightAt rightLive
    refine ⟨leftBox, rightBox, leftKilled, rightKilled,
      boxes.world, boxes.rc, ?_⟩
    apply nodeIso_restrict_left boxes.node
    intro child member
    exact leftOwned.sole_child_ne leftAt leftLive member

/-- The restricted post-kill relation contains every old related pair whose
left endpoint is not the consumed source location. -/
theorem heapIsoKillShared_rel {left right : IxIR1.Store}
    (iso : IxIR1.Sim.HeapIso left right)
    {leftLocation rightLocation : Nat}
    {leftNode rightNode : IxIR1.Node} {leftRest : List IxIR1.Sim.Root}
    (locations : iso.locRel leftLocation rightLocation)
    (leftAt : left.get? leftLocation =
      some ⟨.shared, 1, leftNode⟩)
    (rightAt : right.get? rightLocation =
      some ⟨.shared, 1, rightNode⟩)
    (leftOwned : IxIR1.Sim.RootOwnership left
      (⟨.shared, .loc leftLocation⟩ :: leftRest))
    {leftCandidate rightCandidate : Nat}
    (related : iso.locRel leftCandidate rightCandidate)
    (different : leftCandidate ≠ leftLocation) :
    (heapIsoKillShared iso locations leftAt rightAt leftOwned).locRel
      leftCandidate rightCandidate := by
  exact ⟨related, different⟩

/-! ## Field worlds under live-heap isomorphism -/

/-- Related runtime values have the same dynamic ownership observation under
an allocation-history isomorphism.  A historical dead/dead pair reports
`false` on both sides. -/
theorem heapHistoryIso_rvalHasWorld_eq {left right : Store}
    (iso : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftValue rightValue : RVal}
    (related : IxIR1.Sim.RValIso iso.locRel leftValue rightValue)
    (world : Owned) :
    RVal.hasWorld left world leftValue =
      RVal.hasWorld right world rightValue := by
  cases related with
  | loc locationRelated =>
      rcases iso.related locationRelated with dead | live
      · simp [RVal.hasWorld, Eval.Store.get?, dead.1, dead.2]
      · obtain ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩ := live
        simp [RVal.hasWorld, Eval.Store.get?, leftAt, rightAt, boxes.world]
  | lit => rfl
  | erased => rfl

theorem heapHistoryIso_fieldValuesWorldEq {left right : Store}
    (iso : IxIR1.Sim.HeapHistoryIso left.heap right.heap) :
    ∀ {leftValues rightValues : List RVal},
      IxIR1.Sim.RValsIso iso.locRel leftValues rightValues →
      FieldValuesWorldEq left right leftValues rightValues
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (fun world => heapHistoryIso_rvalHasWorld_eq iso head world)
        (heapHistoryIso_fieldValuesWorldEq iso tail)

/-- Constructor inspection transports across corresponding live locations,
returning the related target box and field vector. -/
theorem constructorView_historyIso {left right : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftLocation rightLocation : Nat}
    (locations : heap.locRel leftLocation rightLocation)
    {world : Owned} {cid : CtorId} {leftBox : IxIR1.NodeBox}
    {leftFields : Array RVal}
    (viewed : ConstructorView left leftLocation world cid leftBox leftFields) :
    ∃ (rightBox : IxIR1.NodeBox) (rightFields : Array RVal),
      right.get? rightLocation = some rightBox ∧
        ConstructorView right rightLocation world cid rightBox rightFields ∧
        IxIR1.Sim.NodeBoxIso heap.locRel leftBox rightBox ∧
        IxIR1.Sim.RValsIso heap.locRel
          leftFields.toList rightFields.toList := by
  obtain ⟨leftAt, leftWorld, leftNode⟩ := viewed.parts
  obtain ⟨rightBox, rightAt, boxes⟩ := heap.boxes locations (by
    change left.heap.get? leftLocation = some leftBox
    exact leftAt)
  have nodes : IxIR1.Sim.NodeIso heap.locRel
      (.ctorN cid leftFields) rightBox.node := by
    simpa only [← leftNode] using boxes.node
  obtain ⟨rightFields, rightNode, fields⟩ := nodeIso_ctor_left nodes
  have rightWorld : rightBox.world = world :=
    boxes.world.symm.trans leftWorld
  have rightViewed : ConstructorView right rightLocation world cid rightBox
      rightFields := ConstructorView.of_box rightAt rightWorld rightNode
  exact ⟨rightBox, rightFields, rightAt, rightViewed, boxes, fields⟩

/-- An in-bounds location whose live-node lookup is empty is an actual dead
slot, rather than an out-of-bounds address. -/
private theorem reservedSlot_of_bound {heap : IxIR1.Store} {location : Nat}
    (bound : location < heap.nodes.size)
    (dead : heap.get? location = none) :
    heap.nodes[location]? = some none := by
  obtain ⟨slot, slotAt⟩ : ∃ slot, heap.nodes[location]? = some slot := by
    refine ⟨heap.nodes[location], ?_⟩
    exact Array.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
  cases slot with
  | none => exact slotAt
  | some box =>
      have live : heap.get? location = some box := by
        simp [IxIR1.Store.get?, slotAt]
      rw [dead] at live
      contradiction

/-- Reserving corresponding live locations preserves allocation history.
The IxIR₂ reservation does not count a free, so only its node-array effect
is compared with the history-level kill operation. -/
def reserve_historyIso {left right : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftLocation rightLocation : Nat}
    (locations : heap.locRel leftLocation rightLocation)
    {leftBox rightBox : IxIR1.NodeBox}
    (leftAt : left.get? leftLocation = some leftBox)
    (rightAt : right.get? rightLocation = some rightBox) :
    IxIR1.Sim.HeapHistoryIso
      (left.reserve leftLocation).heap
      (right.reserve rightLocation).heap := by
  let killed := heap.kill locations leftAt rightAt
  exact killed.nodesEq
    (by
      simp [Eval.Store.reserve, IxIR1.Store.kill,
        Array.set!_eq_setIfInBounds])
    (by
      simp [Eval.Store.reserve, IxIR1.Store.kill,
        Array.set!_eq_setIfInBounds])

/-- Releasing corresponding physical reservations succeeds on both sides and
does not change their allocation-history relation. -/
theorem releaseReservation_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftLocation rightLocation : Nat}
    (locations : heap.locRel leftLocation rightLocation)
    (run : left.releaseReservation leftLocation = .ok leftOut) :
    ∃ rightOut,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        right.releaseReservation rightLocation = .ok rightOut ∧
          outputHeap.locRel = heap.locRel := by
  cases found : left.heap.nodes[leftLocation]? with
  | none =>
      simp [Eval.Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box =>
          simp [Eval.Store.releaseReservation, found] at run
      | none =>
          have leftDead : left.heap.get? leftLocation = none := by
            simp [IxIR1.Store.get?, found]
          have rightDead : right.heap.get? rightLocation = none := by
            rcases heap.related locations with dead | live
            · exact dead.2
            · obtain ⟨leftBox, rightBox, leftLive, _, _⟩ := live
              rw [leftDead] at leftLive
              contradiction
          have rightReserved : right.heap.nodes[rightLocation]? = some none :=
            reservedSlot_of_bound (heap.right_bound locations) rightDead
          have leftOutEq :
              { left with
                heap := { left.heap with frees := left.heap.frees + 1 } } =
                leftOut := by
            simpa [Eval.Store.releaseReservation, found] using run
          subst leftOut
          let rightOut : Store :=
            { right with
              heap := { right.heap with frees := right.heap.frees + 1 } }
          let outputHeap := heap.nodesEq (nextLeft :=
            { left.heap with frees := left.heap.frees + 1 })
            (nextRight :=
              { right.heap with frees := right.heap.frees + 1 }) rfl rfl
          refine ⟨rightOut, outputHeap, ?_, rfl⟩
          simp [rightOut, Eval.Store.releaseReservation, rightReserved]

/-- Reusing corresponding physical reservations with related payload nodes
revives their dead history row.  The two concrete locations may differ. -/
theorem reuseReservation_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftLocation rightLocation : Nat}
    (locations : heap.locRel leftLocation rightLocation)
    {world : Owned} {leftNode rightNode : IxIR1.Node}
    (nodes : IxIR1.Sim.NodeIso heap.locRel leftNode rightNode)
    {payloadUnits : Nat}
    (run : left.reuseReservation leftLocation world leftNode payloadUnits =
      .ok leftOut) :
    ∃ rightOut,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        right.reuseReservation rightLocation world rightNode payloadUnits =
            .ok rightOut ∧
          outputHeap.locRel = heap.locRel := by
  cases found : left.heap.nodes[leftLocation]? with
  | none =>
      simp [Eval.Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box =>
          simp [Eval.Store.reuseReservation, found] at run
      | none =>
          have leftDead : left.heap.get? leftLocation = none := by
            simp [IxIR1.Store.get?, found]
          have rightDead : right.heap.get? rightLocation = none := by
            rcases heap.related locations with dead | live
            · exact dead.2
            · obtain ⟨leftBox, rightBox, leftLive, _, _⟩ := live
              rw [leftDead] at leftLive
              contradiction
          have rightReserved : right.heap.nodes[rightLocation]? = some none :=
            reservedSlot_of_bound (heap.right_bound locations) rightDead
          cases targetRun : right.reuseReservation rightLocation world
              rightNode payloadUnits with
          | error error =>
              simp [Eval.Store.reuseReservation, rightReserved] at targetRun
          | ok rightOut =>
              have leftNodes := congrArg
                (fun result : Except Error Store =>
                  result.map (fun output => output.heap.nodes)) run
              have rightNodes := congrArg
                (fun result : Except Error Store =>
                  result.map (fun output => output.heap.nodes)) targetRun
              have leftNodes' :
                  left.heap.nodes.setIfInBounds leftLocation
                      (some { world, rc := 1, node := leftNode }) =
                    leftOut.heap.nodes := by
                simpa [Eval.Store.reuseReservation, found, Except.map]
                  using leftNodes
              have rightNodes' :
                  right.heap.nodes.setIfInBounds rightLocation
                      (some { world, rc := 1, node := rightNode }) =
                    rightOut.heap.nodes := by
                simpa [Eval.Store.reuseReservation, rightReserved, Except.map]
                  using rightNodes
              let revived := heap.revive locations leftDead rightDead
                (show IxIR1.Sim.NodeBoxIso heap.locRel
                    ⟨world, 1, leftNode⟩ ⟨world, 1, rightNode⟩ from
                  ⟨rfl, rfl, nodes⟩)
              let outputHeap := revived.nodesEq
                (by
                  simpa [IxIR1.Store.setBox,
                    Array.set!_eq_setIfInBounds] using leftNodes'.symm)
                (by
                  simpa [IxIR1.Store.setBox,
                    Array.set!_eq_setIfInBounds] using rightNodes'.symm)
              exact ⟨rightOut, outputHeap, rfl, rfl⟩

/-- One shared retain is equivariant under allocation history.  Its output
history keeps every entry relation, including any pre-existing dead rows. -/
theorem retainShared_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftValue rightValue : RVal}
    (value : IxIR1.Sim.RValIso heap.locRel leftValue rightValue)
    (run : retainShared left leftValue = .ok leftOut) :
    ∃ rightOut,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        retainShared right rightValue = .ok rightOut ∧
          outputHeap.locRel = heap.locRel := by
  cases value with
  | lit =>
      simp [retainShared] at run
      subst leftOut
      exact ⟨right, heap, rfl, rfl⟩
  | erased =>
      simp [retainShared] at run
      subst leftOut
      exact ⟨right, heap, rfl, rfl⟩
  | @loc leftLocation rightLocation related =>
      cases leftAt : left.get? leftLocation with
      | none => simp [retainShared, leftAt] at run
      | some leftBox =>
          obtain ⟨rightBox, rightAt, boxes⟩ := heap.boxes related (by
            change left.heap.get? leftLocation = some leftBox
            exact leftAt)
          cases leftBox with
          | mk leftWorld leftRc leftNode =>
              cases leftWorld with
              | unique => simp [retainShared, leftAt] at run
              | shared =>
                  have rightWorld : rightBox.world = .shared := by
                    exact boxes.world.symm
                  simp [retainShared, leftAt] at run
                  subst leftOut
                  let rightOut :=
                    (right.setBox rightLocation
                      { rightBox with rc := rightBox.rc + 1 }).rcTick
                  have rightAtStore : right.get? rightLocation =
                      some rightBox := by
                    exact rightAt
                  have rightRun : retainShared right (.loc rightLocation) =
                      .ok rightOut := by
                    simp [retainShared, rightAtStore, rightWorld, rightOut]
                  let setHistory := heap.setBox related
                    (by
                      change left.heap.get? leftLocation =
                        some ⟨.shared, leftRc, leftNode⟩
                      exact leftAt)
                    rightAt
                    (show IxIR1.Sim.NodeBoxIso heap.locRel
                        { (⟨.shared, leftRc, leftNode⟩ : IxIR1.NodeBox) with
                          rc := leftRc + 1 }
                        { rightBox with rc := rightBox.rc + 1 } from
                      ⟨boxes.world, congrArg (fun rc => rc + 1) boxes.rc,
                        boxes.node⟩)
                  let outputHistory := setHistory.rcTick
                  exact ⟨rightOut, outputHistory, rightRun, rfl⟩

private theorem retainSharedMany_historyIso_rel
    {rel : Nat → Nat → Prop} {leftValues rightValues : List RVal}
    (values : IxIR1.Sim.RValsIso rel leftValues rightValues) :
    ∀ {left right leftOut : Store}
      (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap),
      heap.locRel = rel →
      RetainSharedMany left leftValues.toArray leftOut →
      ∃ rightOut,
        ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
          RetainSharedMany right rightValues.toArray rightOut ∧
            outputHeap.locRel = rel := by
  induction values with
  | nil =>
      intro left right leftOut heap heapRelation run
      have leftEmpty : RetainSharedMany left #[] left :=
        RetainSharedMany.empty left
      have leftOutEq : leftOut = left := by
        unfold RetainSharedMany at run leftEmpty
        exact Except.ok.inj (run.symm.trans leftEmpty)
      subst leftOut
      exact ⟨right, heap, RetainSharedMany.empty right, heapRelation⟩
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      intro left right leftOut heap heapRelation run
      obtain ⟨leftMiddle, leftHeadRun, leftTailRun⟩ := run.cons_inv
      have headRelated : IxIR1.Sim.RValIso heap.locRel
          leftHead rightHead := by
        rw [heapRelation]
        exact head
      obtain ⟨rightMiddle, middleHeap, rightHeadRun, middleRelation⟩ :=
        retainShared_historyIso heap headRelated leftHeadRun
      obtain ⟨rightOut, outputHeap, rightTailRun, outputRelation⟩ :=
        ih middleHeap (middleRelation.trans heapRelation) leftTailRun
      refine ⟨rightOut, outputHeap,
        RetainSharedMany.cons rightHeadRun rightTailRun, outputRelation⟩

/-- Batch shared retain preserves the allocation-history relation while
allowing each side to update the corresponding concrete locations. -/
theorem retainSharedMany_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftValues rightValues : List RVal}
    (values : IxIR1.Sim.RValsIso heap.locRel leftValues rightValues)
    (run : RetainSharedMany left leftValues.toArray leftOut) :
    ∃ rightOut,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        RetainSharedMany right rightValues.toArray rightOut ∧
          outputHeap.locRel = heap.locRel :=
  retainSharedMany_historyIso_rel values heap rfl run

/-- Deep shared release is equivariant at a common traversal-fuel index.
Corresponding kills retain dead/dead history rows, and corresponding
decrements preserve the same location relation. -/
theorem releaseSharedWork_historyIso_sameFuel :
    ∀ {fuel : Nat} {left right leftOut : Store}
      {leftValues rightValues : List RVal} {remaining : Nat}
      (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap),
      IxIR1.Sim.RValsIso heap.locRel leftValues rightValues →
      releaseSharedWork fuel left leftValues = .ok (leftOut, remaining) →
      ∃ rightOut,
        ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
          releaseSharedWork fuel right rightValues =
              .ok (rightOut, remaining) ∧
            outputHeap.locRel = heap.locRel := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right leftOut leftValues rightValues remaining heap values run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (left, 0) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, heap, rfl, rfl⟩
      | cons head tail => simp [releaseSharedWork] at run
  | succ fuel ih =>
      intro left right leftOut leftValues rightValues remaining heap values run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (left, fuel + 1) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, heap, rfl, rfl⟩
      | @cons leftValue rightValue leftRest rightRest head tail =>
          cases head with
          | lit =>
              simp only [releaseSharedWork] at run ⊢
              exact ih heap tail run
          | erased =>
              simp only [releaseSharedWork] at run ⊢
              exact ih heap tail run
          | @loc leftLocation rightLocation locations =>
              cases leftAt : left.get? leftLocation with
              | none => simp [releaseSharedWork, leftAt] at run
              | some leftBox =>
                  obtain ⟨rightBox, rightAt, boxes⟩ :=
                    heap.boxes locations (by
                      change left.heap.get? leftLocation = some leftBox
                      exact leftAt)
                  cases leftBox with
                  | mk leftWorld leftRc leftNode =>
                      cases leftWorld with
                      | unique => simp [releaseSharedWork, leftAt] at run
                      | shared =>
                          cases rightBox with
                          | mk rightWorld rightRc rightNode =>
                              have worldEq := boxes.world
                              have rcEq := boxes.rc
                              simp only at worldEq rcEq
                              subst rightWorld
                              subst rightRc
                              have rightAtStore : right.get? rightLocation =
                                  some ⟨.shared, leftRc, rightNode⟩ := by
                                exact rightAt
                              have nodes : IxIR1.Sim.NodeIso heap.locRel
                                  leftNode rightNode := boxes.node
                              by_cases zero : leftRc = 0
                              · subst leftRc
                                simp [releaseSharedWork, leftAt] at run
                              · by_cases unit : leftRc = 1
                                · subst leftRc
                                  cases leftNode with
                                  | ctorN cid leftFields =>
                                      obtain ⟨rightFields, rightNodeEq,
                                          fieldsRelated⟩ :=
                                        nodeIso_ctor_left nodes
                                      let nextHeap :=
                                        (heap.rcTick).kill locations
                                          (by
                                            change left.heap.rcTick.get?
                                              leftLocation = some
                                                ⟨.shared, 1,
                                                  .ctorN cid leftFields⟩
                                            exact leftAt)
                                          (by
                                            change right.heap.rcTick.get?
                                              rightLocation = some
                                                ⟨.shared, 1, rightNode⟩
                                            exact rightAt)
                                      have nextValues : IxIR1.Sim.RValsIso
                                          nextHeap.locRel
                                          (leftFields.toList ++ leftRest)
                                          (rightFields.toList ++ rightRest) :=
                                        fieldsRelated.append tail
                                      simp [releaseSharedWork, leftAt,
                                        rightAtStore, rightNodeEq] at run ⊢
                                      obtain ⟨rightOut, outputHeap, rightRun,
                                          outputRelation⟩ := ih
                                        (left := left.rcTick.kill leftLocation)
                                        (right := right.rcTick.kill
                                          rightLocation)
                                        nextHeap nextValues run
                                      refine ⟨rightOut, rightRun, outputHeap, ?_⟩
                                      exact outputRelation.trans (by rfl)
                                  | papN address arity leftArguments =>
                                      obtain ⟨rightArguments, rightNodeEq,
                                          argumentsRelated⟩ :=
                                        nodeIso_pap_left nodes
                                      let nextHeap :=
                                        (heap.rcTick).kill locations
                                          (by
                                            change left.heap.rcTick.get?
                                              leftLocation = some
                                                ⟨.shared, 1, .papN address
                                                  arity leftArguments⟩
                                            exact leftAt)
                                          (by
                                            change right.heap.rcTick.get?
                                              rightLocation = some
                                                ⟨.shared, 1, rightNode⟩
                                            exact rightAt)
                                      have nextValues : IxIR1.Sim.RValsIso
                                          nextHeap.locRel
                                          (leftArguments.toList ++ leftRest)
                                          (rightArguments.toList ++
                                            rightRest) :=
                                        argumentsRelated.append tail
                                      simp [releaseSharedWork, leftAt,
                                        rightAtStore, rightNodeEq] at run ⊢
                                      obtain ⟨rightOut, outputHeap, rightRun,
                                          outputRelation⟩ := ih
                                        (left := left.rcTick.kill leftLocation)
                                        (right := right.rcTick.kill
                                          rightLocation)
                                        nextHeap nextValues run
                                      refine ⟨rightOut, rightRun, outputHeap, ?_⟩
                                      exact outputRelation.trans (by rfl)
                                · have nonzero : (leftRc == 0) = false :=
                                    beq_eq_false_iff_ne.mpr zero
                                  have nonunit : (leftRc == 1) = false :=
                                    beq_eq_false_iff_ne.mpr unit
                                  let nextHeap :=
                                    (heap.rcTick).setBox locations
                                      (by
                                        change left.heap.rcTick.get?
                                          leftLocation = some
                                            ⟨.shared, leftRc, leftNode⟩
                                        exact leftAt)
                                      (by
                                        change right.heap.rcTick.get?
                                          rightLocation = some
                                            ⟨.shared, leftRc, rightNode⟩
                                        exact rightAt)
                                      (show IxIR1.Sim.NodeBoxIso heap.locRel
                                          ⟨.shared, leftRc - 1, leftNode⟩
                                          ⟨.shared, leftRc - 1, rightNode⟩
                                        from ⟨rfl, rfl, nodes⟩)
                                  simp [releaseSharedWork, leftAt,
                                    rightAtStore, nonzero, nonunit] at run ⊢
                                  obtain ⟨rightOut, outputHeap, rightRun,
                                      outputRelation⟩ := ih
                                    (left := left.rcTick.setBox leftLocation
                                      ⟨.shared, leftRc - 1, leftNode⟩)
                                    (right := right.rcTick.setBox rightLocation
                                      ⟨.shared, leftRc - 1, rightNode⟩)
                                    nextHeap tail run
                                  refine ⟨rightOut, rightRun, outputHeap, ?_⟩
                                  exact outputRelation.trans (by rfl)

/-- Deep unique destruction is allocation-history equivariant at a common
fuel index. -/
theorem dropUniqueWork_historyIso_sameFuel :
    ∀ {fuel : Nat} {left right leftOut : Store}
      {leftValues rightValues : List RVal} {remaining : Nat}
      (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap),
      IxIR1.Sim.RValsIso heap.locRel leftValues rightValues →
      dropUniqueWork fuel left leftValues = .ok (leftOut, remaining) →
      ∃ rightOut,
        ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
          dropUniqueWork fuel right rightValues =
              .ok (rightOut, remaining) ∧
            outputHeap.locRel = heap.locRel := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right leftOut leftValues rightValues remaining heap values run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (left, 0) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, heap, rfl, rfl⟩
      | cons head tail => simp [dropUniqueWork] at run
  | succ fuel ih =>
      intro left right leftOut leftValues rightValues remaining heap values run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (left, fuel + 1) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, heap, rfl, rfl⟩
      | @cons leftValue rightValue leftRest rightRest head tail =>
          cases head with
          | lit =>
              simp only [dropUniqueWork] at run ⊢
              exact ih heap tail run
          | erased =>
              simp only [dropUniqueWork] at run ⊢
              exact ih heap tail run
          | @loc leftLocation rightLocation locations =>
              cases leftAt : left.get? leftLocation with
              | none => simp [dropUniqueWork, leftAt] at run
              | some leftBox =>
                  obtain ⟨rightBox, rightAt, boxes⟩ :=
                    heap.boxes locations (by
                      change left.heap.get? leftLocation = some leftBox
                      exact leftAt)
                  cases leftBox with
                  | mk leftWorld leftRc leftNode =>
                      cases leftWorld with
                      | shared => simp [dropUniqueWork, leftAt] at run
                      | unique =>
                          cases rightBox with
                          | mk rightWorld rightRc rightNode =>
                              have worldEq := boxes.world
                              have rcEq := boxes.rc
                              simp only at worldEq rcEq
                              subst rightWorld
                              subst rightRc
                              have rightAtStore : right.get? rightLocation =
                                  some ⟨.unique, leftRc, rightNode⟩ := by
                                exact rightAt
                              have nodes : IxIR1.Sim.NodeIso heap.locRel
                                  leftNode rightNode := boxes.node
                              cases leftNode with
                              | papN address arity arguments =>
                                  simp [dropUniqueWork, leftAt] at run
                              | ctorN cid leftFields =>
                                  obtain ⟨rightFields, rightNodeEq,
                                      fieldsRelated⟩ := nodeIso_ctor_left nodes
                                  let nextHeap := heap.kill locations
                                    (by
                                      change left.heap.get? leftLocation = some
                                        ⟨.unique, leftRc,
                                          .ctorN cid leftFields⟩
                                      exact leftAt)
                                    (by
                                      change right.heap.get? rightLocation =
                                        some ⟨.unique, leftRc, rightNode⟩
                                      exact rightAt)
                                  have nextValues : IxIR1.Sim.RValsIso
                                      nextHeap.locRel
                                      (leftFields.toList ++ leftRest)
                                      (rightFields.toList ++ rightRest) :=
                                    fieldsRelated.append tail
                                  simp [dropUniqueWork, leftAt, rightAtStore,
                                    rightNodeEq] at run ⊢
                                  obtain ⟨rightOut, outputHeap, rightRun,
                                      outputRelation⟩ := ih
                                    (left := left.kill leftLocation)
                                    (right := right.kill rightLocation)
                                    nextHeap nextValues run
                                  refine ⟨rightOut, rightRun, outputHeap, ?_⟩
                                  exact outputRelation.trans (by rfl)

/-- Related runtime values report the same dynamic ownership world in
isomorphic evaluator heaps. -/
theorem heapIso_rvalHasWorld_eq {left right : Store}
    (iso : IxIR1.Sim.HeapIso left.heap right.heap)
    {leftValue rightValue : RVal}
    (related : IxIR1.Sim.RValIso iso.locRel leftValue rightValue)
    (world : Owned) :
    RVal.hasWorld left world leftValue =
      RVal.hasWorld right world rightValue := by
  cases related with
  | loc locationRelated =>
      obtain ⟨leftBox, rightBox, leftAt, rightAt, boxes⟩ :=
        iso.related_live locationRelated
      simp [RVal.hasWorld, Eval.Store.get?, leftAt, rightAt, boxes.world]
  | lit => rfl
  | erased => rfl

/-- Uniform constructor-field validation transports pointwise across a live
heap isomorphism and its related value vector. -/
theorem heapIso_fieldWorlds_of_replicate {left right : Store}
    (iso : IxIR1.Sim.HeapIso left.heap right.heap)
    {schema : CtorSchema} {leftValues rightValues : Array RVal}
    {world : Owned} {count : Nat}
    (schemaFields : schema.fields = Array.replicate count world)
    (related : IxIR1.Sim.RValsIso iso.locRel
      leftValues.toList rightValues.toList)
    (fieldWorlds : FieldWorlds left schema leftValues) :
    FieldWorlds right schema rightValues := by
  obtain ⟨leftCount, leftWorlds⟩ :=
    fieldWorlds.to_replicate schemaFields
  have valueCounts : leftValues.size = rightValues.size := by
    simpa using rvalsIso_length_eq related
  have rightCount : rightValues.size = count :=
    valueCounts.symm.trans leftCount
  have transfer : ∀ {lefts rights : List RVal},
      IxIR1.Sim.RValsIso iso.locRel lefts rights →
      (∀ value ∈ lefts, RVal.hasWorld left world value = true) →
      ∀ value ∈ rights, RVal.hasWorld right world value = true := by
    intro lefts rights valuesRelated
    induction valuesRelated with
    | nil => simp
    | @cons leftValue rightValue lefts rights head tail ih =>
        intro sourceWorlds value member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rw [← heapIso_rvalHasWorld_eq iso head world]
          exact sourceWorlds leftValue (by simp)
        · apply ih
          · intro sourceValue sourceMember
            exact sourceWorlds sourceValue (by simp [sourceMember])
          · exact member
  exact FieldWorlds.of_replicate schemaFields rightCount
    (transfer related leftWorlds)

/-- Values accepted by a uniform field schema cannot name a missing heap
location.  This is the local freshness fact used when restricting an existing
heap bijection after a hot reset consumes its source node. -/
theorem FieldWorlds.avoidsMissing {store : Store} {schema : CtorSchema}
    {values : Array RVal} {world : Owned} {count location : Nat}
    (schemaFields : schema.fields = Array.replicate count world)
    (worlds : FieldWorlds store schema values)
    (missing : store.get? location = none) :
    ∀ value ∈ values.toList, value ≠ .loc location := by
  obtain ⟨_count, valuesWorld⟩ := worlds.to_replicate schemaFields
  intro value member
  have valueWorld := valuesWorld value member
  cases value with
  | loc actual =>
      intro same
      cases same
      simp [RVal.hasWorld, missing] at valueWorld
  | lit literal => intro impossible; cases impossible
  | erased => intro impossible; cases impossible

/-- A scalar, or a live shared location with a positive refcount.  This is
the local safety fact needed to show that releasing a freshly retained field
takes the non-final branch. -/
def SharedPositive (store : Store) : RVal → Prop
  | .loc location =>
      ∃ rc node, store.get? location = some ⟨.shared, rc, node⟩ ∧ 0 < rc
  | .lit _ | .erased => True

/-- Every field edge of an exactly owned shared node points to a positive
shared value (or is scalar). -/
theorem sharedChild_positive {store : Store} {parent parentRc : Nat}
    {node : IxIR1.Node} {roots : List IxIR1.Sim.Root} {child : RVal}
    (parentAt : store.get? parent =
      some ⟨.shared, parentRc, node⟩)
    (owned : IxIR1.Sim.RootOwnership store.heap roots)
    (member : child ∈ IxIR1.Sim.nodeChildren node) :
    SharedPositive store child := by
  cases child with
  | lit literal => trivial
  | erased => trivial
  | loc childLocation =>
      have childWorld := owned.edges_world parentAt (.loc childLocation) member
      obtain ⟨childBox, childAt, childBoxWorld⟩ := childWorld
      cases childBox with
      | mk world rc childNode =>
          change world = .shared at childBoxWorld
          subst world
          have count := owned.counts childAt
          change rc = IxIR1.Sim.incoming store.heap roots childLocation at count
          have edge : childLocation ∈ IxIR1.Sim.edgeLocations store.heap :=
            IxIR1.Sim.child_location_mem_edgeLocations parentAt member
          have positiveIncoming :
              0 < IxIR1.Sim.incoming store.heap roots childLocation := by
            rw [IxIR1.Sim.incoming, List.count_pos_iff]
            exact List.mem_append_right _ edge
          exact ⟨rc, childNode, childAt, by omega⟩

/-- Killing a different live slot preserves positivity. -/
theorem SharedPositive.kill {store : Store} {value : RVal}
    {target : Nat} {targetBox : IxIR1.NodeBox}
    (positive : SharedPositive store value)
    (targetAt : store.get? target = some targetBox)
    (different : value ≠ .loc target) :
    SharedPositive (store.kill target) value := by
  cases value with
  | lit literal => trivial
  | erased => trivial
  | loc location =>
      obtain ⟨rc, node, valueAt, rcPositive⟩ := positive
      have targetNe : target ≠ location := by
        intro same
        subst location
        exact different rfl
      exact ⟨rc, node,
        IxIR1.Sim.get?_kill_other targetNe targetAt valueAt, rcPositive⟩

/-- Retaining any value preserves positivity of every already-positive shared
value. -/
theorem SharedPositive.retain {store retained : Store}
    {preserved changed : RVal}
    (positive : SharedPositive store preserved)
    (run : retainShared store changed = .ok retained) :
    SharedPositive retained preserved := by
  cases preserved with
  | lit literal => trivial
  | erased => trivial
  | loc protectedLocation =>
      obtain ⟨protectedRc, protectedNode, protectedAt, protectedPositive⟩ :=
        positive
      cases changed with
      | lit literal =>
          have storeEq : store = retained := by
            simpa [retainShared] using run
          subst retained
          exact ⟨protectedRc, protectedNode, protectedAt, protectedPositive⟩
      | erased =>
          have storeEq : store = retained := by
            simpa [retainShared] using run
          subst retained
          exact ⟨protectedRc, protectedNode, protectedAt, protectedPositive⟩
      | loc changedLocation =>
          cases changedAt : store.get? changedLocation with
          | none => simp [retainShared, changedAt] at run
          | some changedBox =>
              cases changedBox with
              | mk changedWorld changedRc changedNode =>
                  cases changedWorld with
                  | unique => simp [retainShared, changedAt] at run
                  | shared =>
                      have retainedEq :
                          incrementSharedStore store changedLocation
                            ⟨.shared, changedRc, changedNode⟩ = retained := by
                        simpa [retainShared, changedAt, incrementSharedStore]
                          using run
                      subst retained
                      by_cases same : changedLocation = protectedLocation
                      · subst changedLocation
                        have boxEq :
                            (⟨.shared, changedRc, changedNode⟩ :
                              IxIR1.NodeBox) =
                              ⟨.shared, protectedRc, protectedNode⟩ :=
                          Option.some.inj (changedAt.symm.trans protectedAt)
                        cases boxEq
                        exact ⟨protectedRc + 1, protectedNode,
                          get?_incrementSharedStore_same protectedAt, by omega⟩
                      · exact ⟨protectedRc, protectedNode,
                          get?_incrementSharedStore_other same changedAt
                            protectedAt,
                          protectedPositive⟩

/-- A successful batch of retains preserves positivity of every previously
positive shared value. -/
theorem RetainSharedMany.preserve_positive {store retained : Store}
    {values : List RVal} {preserved : RVal}
    (run : RetainSharedMany store values.toArray retained)
    (positive : SharedPositive store preserved) :
    SharedPositive retained preserved := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except Error Store) = .ok retained at run
      injection run with storeEq
      subst retained
      exact positive
  | cons value values ih =>
      obtain ⟨middle, head, tail⟩ :=
        Eval.RetainSharedMany.cons_inv (run := run)
      exact ih tail (positive.retain head)

private theorem setIfInBounds_existing {entries : Array (Option IxIR1.NodeBox)}
    {location : Nat} {box : IxIR1.NodeBox}
    (found : entries[location]? = some (some box)) :
    entries.setIfInBounds location (some box) = entries := by
  apply Array.ext_getElem?
  intro other
  by_cases same : location = other
  · subst other
    obtain ⟨bound, atLocation⟩ := Array.getElem?_eq_some_iff.mp found
    simp [bound, atLocation]
  · simp [same]

/-- Releasing a just-retained positive shared value cancels its refcount
increment in the semantic heap, even when the release starts from a store
whose accounting counters differ.  The remaining work list and heap-fuel
suffix are exposed unchanged. -/
theorem releaseRetainedHead {base retained releaseStart : Store}
    {value : RVal} {rest : List RVal} {heapFuel : Nat}
    (positive : SharedPositive base value)
    (retainedRun : retainShared base value = .ok retained)
    (contents : HeapContentsEq releaseStart retained) :
    ∃ afterHead,
      releaseSharedWork (heapFuel + 1) releaseStart (value :: rest) =
        releaseSharedWork heapFuel afterHead rest ∧
      HeapContentsEq afterHead base := by
  cases value with
  | lit literal =>
      have baseEq : base = retained := by
        simpa [retainShared] using retainedRun
      subst retained
      exact ⟨releaseStart, rfl, contents⟩
  | erased =>
      have baseEq : base = retained := by
        simpa [retainShared] using retainedRun
      subst retained
      exact ⟨releaseStart, rfl, contents⟩
  | loc location =>
      obtain ⟨rc, node, baseAt, rcPositive⟩ := positive
      have retainedEq :
          incrementSharedStore base location ⟨.shared, rc, node⟩ =
            retained := by
        simpa [retainShared, baseAt, incrementSharedStore] using retainedRun
      subst retained
      have retainedAt := get?_incrementSharedStore_same baseAt
      have releaseAt : releaseStart.get? location =
          some ⟨.shared, rc + 1, node⟩ := by
        rw [contents.get?_eq location]
        exact retainedAt
      let afterHead := baselineDecrementStore releaseStart location
        ⟨.shared, rc + 1, node⟩
      refine ⟨afterHead, ?_, ?_⟩
      · have nonzero : (rc + 1 == 0) = false :=
          beq_eq_false_iff_ne.mpr (by omega)
        have nonunit : (rc + 1 == 1) = false :=
          beq_eq_false_iff_ne.mpr (by omega)
        simp [releaseSharedWork, releaseAt, nonzero, nonunit,
          afterHead, baselineDecrementStore]
      · constructor
        have baseNodesAt : base.heap.nodes[location]? =
            some (some ⟨.shared, rc, node⟩) :=
          IxIR1.Sim.nodes_get?_of_get? baseAt
        have restored := setIfInBounds_existing baseNodesAt
        simpa [afterHead, baselineDecrementStore, incrementSharedStore,
          Eval.Store.setBox, Eval.Store.rcTick, IxIR1.Store.setBox,
          IxIR1.Store.rcTick, Array.set!_eq_setIfInBounds, contents.nodes]
          using restored

/-- Retaining a vector of positive shared fields and subsequently releasing
the same vector restores the exact node array.  The release may start from a
counter-different store, which is needed after the parent's hot shallow
free. -/
theorem retainedFields_release_roundtrip :
    ∀ {base retained releaseStart output : Store} {values : List RVal}
      {heapFuel remaining : Nat},
      (∀ value ∈ values, SharedPositive base value) →
      RetainSharedMany base values.toArray retained →
      HeapContentsEq releaseStart retained →
      releaseSharedWork heapFuel releaseStart values =
        .ok (output, remaining) →
      HeapContentsEq output base := by
  intro base retained releaseStart output values
  induction values generalizing base retained releaseStart output with
  | nil =>
      intro heapFuel remaining _ retainedRun contents releaseRun
      change (.ok base : Except Error Store) = .ok retained at retainedRun
      injection retainedRun with retainedEq
      subst retained
      have releaseEq :
          (.ok (releaseStart, heapFuel) : Except Error (Store × Nat)) =
            .ok (output, remaining) := by
        cases heapFuel <;> simpa [releaseSharedWork] using releaseRun
      have pairEq : (releaseStart, heapFuel) = (output, remaining) :=
        Except.ok.inj releaseEq
      cases pairEq
      exact contents
  | cons head tail ih =>
      intro heapFuel remaining positives retainedRun contents releaseRun
      cases heapFuel with
      | zero => simp [releaseSharedWork] at releaseRun
      | succ heapFuel =>
          obtain ⟨middle, tailRetained, headRetained⟩ :=
            RetainSharedMany.rotate_head retainedRun
          have headPositive : SharedPositive base head :=
            positives head (by simp)
          have headPositiveMiddle : SharedPositive middle head :=
            RetainSharedMany.preserve_positive tailRetained headPositive
          obtain ⟨afterHead, releaseHead, afterHeadContents⟩ :=
            releaseRetainedHead headPositiveMiddle headRetained contents
          rw [releaseHead] at releaseRun
          apply ih
          · intro value member
            exact positives value (by simp [member])
          · exact tailRetained
          · exact afterHeadContents
          · exact releaseRun

/-- The compiler-emitted hot baseline prefix—retain every projected field,
then deep-release the unit-refcount parent—has exactly the same node array as
the logical hot reset's shallow parent kill.

The premise is the baseline evaluator's successful release equation.  The
proof derives its child-work suffix, cancels every retain/release pair, and
uses exact ownership to rule out a self-field pointing back to the unit
parent. -/
theorem hotPrefix_contents {store baselineRetained output : Store}
    {target : Nat} {cid : CtorId} {fields : Array RVal}
    {fieldFuel remaining : Nat} {ambient : List IxIR1.Sim.Root}
    (targetAt : store.get? target =
      some ⟨.shared, 1, .ctorN cid fields⟩)
    (owned : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc target⟩ :: ambient))
    (retained : RetainSharedMany store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc target) = .ok (output, remaining)) :
    HeapContentsEq output (logicalHotResetStore store target) := by
  have different : ∀ value ∈ fields.toList, value ≠ .loc target := by
    intro value member
    apply owned.sole_child_ne targetAt targetAt
    simpa [IxIR1.Sim.nodeChildren] using member
  have retainedList :
      RetainSharedMany store fields.toList.toArray baselineRetained := by
    simpa using retained
  have retainedTarget : baselineRetained.get? target =
      some ⟨.shared, 1, .ctorN cid fields⟩ :=
    RetainSharedMany.preserves_box targetAt different retainedList
  have childRelease :
      releaseSharedWork fieldFuel
          (baselineRetained.rcTick.kill target) fields.toList =
        .ok (output, remaining) := by
    unfold releaseShared at released
    simpa [releaseSharedWork, retainedTarget] using released
  have retainedAfterKill :
      RetainSharedMany (store.kill target) fields.toList.toArray
        (baselineRetained.kill target) :=
    RetainSharedMany.kill_commute targetAt different retainedList
  have positives : ∀ value ∈ fields.toList,
      SharedPositive (store.kill target) value := by
    intro value member
    exact (sharedChild_positive targetAt owned
      (by simpa [IxIR1.Sim.nodeChildren] using member)).kill targetAt
        (different value member)
  have releaseStartContents :
      HeapContentsEq (baselineRetained.rcTick.kill target)
        (baselineRetained.kill target) := ⟨rfl⟩
  have restored : HeapContentsEq output (store.kill target) :=
    retainedFields_release_roundtrip positives retainedAfterKill
      releaseStartContents childRelease
  exact restored.trans ⟨rfl⟩

/-- Deep shared release is congruent under exact node-array equality.  It
therefore cannot observe the reset and RC accounting differences intentionally
forgotten by `HeapContentsEq`. -/
theorem releaseSharedWork_contents_congr :
    ∀ {fuel : Nat} {left right : Store} {values : List RVal}
      {leftOut : Store} {remaining : Nat},
      HeapContentsEq left right →
      releaseSharedWork fuel left values = .ok (leftOut, remaining) →
      ∃ rightOut,
        releaseSharedWork fuel right values = .ok (rightOut, remaining) ∧
        HeapContentsEq leftOut rightOut := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right values leftOut remaining heaps run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (left, 0) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, rfl, heaps⟩
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      intro left right values leftOut remaining heaps run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (left, fuel + 1) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, rfl, heaps⟩
      | cons value rest =>
          cases value with
          | lit literal =>
              simp only [releaseSharedWork] at run ⊢
              exact ih heaps run
          | erased =>
              simp only [releaseSharedWork] at run ⊢
              exact ih heaps run
          | loc location =>
              have lookup := heaps.get?_eq location
              cases leftAt : left.get? location with
              | none => simp [releaseSharedWork, leftAt] at run
              | some box =>
                  have rightAt : right.get? location = some box := by
                    rw [← lookup]
                    exact leftAt
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | unique =>
                          simp [releaseSharedWork, leftAt] at run
                      | shared =>
                          by_cases zero : rc = 0
                          · subst rc
                            simp [releaseSharedWork, leftAt] at run
                          · by_cases unit : rc = 1
                            · subst rc
                              simp [releaseSharedWork, leftAt, rightAt]
                                at run ⊢
                              exact ih (heaps.rcTick.kill location) run
                            · have nonzero : (rc == 0) = false :=
                                beq_eq_false_iff_ne.mpr zero
                              have nonunit : (rc == 1) = false :=
                                beq_eq_false_iff_ne.mpr unit
                              simp [releaseSharedWork, leftAt, rightAt,
                                nonzero, nonunit] at run ⊢
                              exact ih
                                ((heaps.rcTick).setBox location
                                  ⟨.shared, rc - 1, node⟩) run

/-- The public single-value release operation inherits exact-content
congruence from its work-list implementation. -/
theorem HeapContentsEq.releaseShared {left right leftOut : Store}
    (heaps : HeapContentsEq left right) {fuel remaining : Nat}
    {value : RVal}
    (run : releaseShared fuel left value = .ok (leftOut, remaining)) :
    ∃ rightOut,
      releaseShared fuel right value = .ok (rightOut, remaining) ∧
      HeapContentsEq leftOut rightOut := by
  unfold Eval.releaseShared at run ⊢
  exact releaseSharedWork_contents_congr heaps run

/-- Extra heap fuel is preserved as extra remainder by a successful shared
release traversal. -/
theorem releaseSharedWork_addFuel :
    ∀ {fuel : Nat} {store output : Store} {values : List RVal}
      {remaining : Nat} (extra : Nat),
      releaseSharedWork fuel store values = .ok (output, remaining) →
      releaseSharedWork (fuel + extra) store values =
        .ok (output, remaining + extra) := by
  intro fuel
  induction fuel with
  | zero =>
      intro store output values remaining extra run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (store, 0) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          rfl
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      intro store output values remaining extra run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run ⊢
          have pairEq : (store, fuel + 1) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          rfl
      | cons value rest =>
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
          cases value with
          | lit literal =>
              simp only [releaseSharedWork] at run ⊢
              exact ih extra run
          | erased =>
              simp only [releaseSharedWork] at run ⊢
              exact ih extra run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | unique => simp [releaseSharedWork, found] at run
                      | shared =>
                          by_cases zero : rc = 0
                          · subst rc
                            simp [releaseSharedWork, found] at run
                          · by_cases unit : rc = 1
                            · subst rc
                              simp [releaseSharedWork, found] at run ⊢
                              exact ih extra run
                            · have nonzero : (rc == 0) = false :=
                                beq_eq_false_iff_ne.mpr zero
                              have nonunit : (rc == 1) = false :=
                                beq_eq_false_iff_ne.mpr unit
                              simp [releaseSharedWork, found, nonzero,
                                nonunit] at run ⊢
                              exact ih extra run

/-- Deep shared release with extra target fuel preserves fuel dominance; the
additional target budget remains as an equal additive suffix. -/
theorem releaseSharedWork_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftFuel rightFuel remaining : Nat}
    {leftValues rightValues : List RVal}
    (fuel : leftFuel ≤ rightFuel)
    (values : IxIR1.Sim.RValsIso heap.locRel leftValues rightValues)
    (run : releaseSharedWork leftFuel left leftValues =
      .ok (leftOut, remaining)) :
    ∃ rightOut rightRemaining,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        releaseSharedWork rightFuel right rightValues =
            .ok (rightOut, rightRemaining) ∧
          remaining ≤ rightRemaining ∧
          outputHeap.locRel = heap.locRel := by
  obtain ⟨rightOut, outputHeap, sameFuelRun, outputRelation⟩ :=
    releaseSharedWork_historyIso_sameFuel heap values run
  let extra := rightFuel - leftFuel
  have extended := releaseSharedWork_addFuel extra sameFuelRun
  have fuelEq : leftFuel + extra = rightFuel := Nat.add_sub_of_le fuel
  refine ⟨rightOut, remaining + extra, outputHeap, ?_,
    Nat.le_add_right remaining extra, outputRelation⟩
  simpa [fuelEq] using extended

/-- A successful shared release cannot increase its heap-fuel remainder. -/
theorem releaseSharedWork_remaining_le :
    ∀ {fuel : Nat} {store output : Store} {values : List RVal}
      {remaining : Nat},
      releaseSharedWork fuel store values = .ok (output, remaining) →
      remaining ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro store output values remaining run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run
          have pairEq : (store, 0) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact Nat.le_refl 0
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      intro store output values remaining run
      cases values with
      | nil =>
          simp only [releaseSharedWork] at run
          have pairEq : (store, fuel + 1) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact Nat.le_refl _
      | cons value rest =>
          have finish : remaining ≤ fuel → remaining ≤ fuel + 1 :=
            Nat.le_succ_of_le
          cases value with
          | lit literal =>
              simp only [releaseSharedWork] at run
              exact finish (ih run)
          | erased =>
              simp only [releaseSharedWork] at run
              exact finish (ih run)
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | unique => simp [releaseSharedWork, found] at run
                      | shared =>
                          by_cases zero : rc = 0
                          · subst rc
                            simp [releaseSharedWork, found] at run
                          · by_cases unit : rc = 1
                            · subst rc
                              simp [releaseSharedWork, found] at run
                              exact finish (ih run)
                            · have nonzero : (rc == 0) = false :=
                                beq_eq_false_iff_ne.mpr zero
                              have nonunit : (rc == 1) = false :=
                                beq_eq_false_iff_ne.mpr unit
                              simp [releaseSharedWork, found, nonzero,
                                nonunit] at run
                              exact finish (ih run)

/-- Batch shared release transports across exact heap contents while allowing
the rewritten machine to start with additional traversal fuel. -/
theorem HeapContentsEq.releaseSharedWork_of_le {left right leftOut : Store}
    (heaps : HeapContentsEq left right)
    {baselineFuel rewrittenFuel remaining : Nat} {values : List RVal}
    (fuel : baselineFuel ≤ rewrittenFuel)
    (run : releaseSharedWork baselineFuel left values =
      .ok (leftOut, remaining)) :
    ∃ rightOut rightRemaining,
      releaseSharedWork rewrittenFuel right values =
        .ok (rightOut, rightRemaining) ∧
      HeapContentsEq leftOut rightOut ∧
      remaining ≤ rightRemaining := by
  obtain ⟨rightOut, sameFuelRun, outputHeaps⟩ :=
    releaseSharedWork_contents_congr heaps run
  let extra := rewrittenFuel - baselineFuel
  have extended := releaseSharedWork_addFuel extra sameFuelRun
  have fuelEq : baselineFuel + extra = rewrittenFuel := by
    exact Nat.add_sub_of_le fuel
  refine ⟨rightOut, remaining + extra, ?_, outputHeaps,
    Nat.le_add_right remaining extra⟩
  simpa [fuelEq] using extended

theorem releaseShared_remaining_le {fuel remaining : Nat}
    {store output : Store} {value : RVal}
    (run : Eval.releaseShared fuel store value = .ok (output, remaining)) :
    remaining ≤ fuel := by
  unfold Eval.releaseShared at run
  exact releaseSharedWork_remaining_le run

theorem releaseShared_addFuel {fuel remaining : Nat}
    {store output : Store} {value : RVal} (extra : Nat)
    (run : Eval.releaseShared fuel store value = .ok (output, remaining)) :
    Eval.releaseShared (fuel + extra) store value =
      .ok (output, remaining + extra) := by
  unfold Eval.releaseShared at run ⊢
  exact releaseSharedWork_addFuel extra run

/-- Exact-content release simulation permits the rewritten machine to carry
additional heap fuel, as it does after replacing deep release by reset. -/
theorem HeapContentsEq.releaseShared_of_le {left right leftOut : Store}
    (heaps : HeapContentsEq left right)
    {baselineFuel rewrittenFuel remaining : Nat} {value : RVal}
    (fuel : baselineFuel ≤ rewrittenFuel)
    (run : Eval.releaseShared baselineFuel left value =
      .ok (leftOut, remaining)) :
    ∃ rightOut rightRemaining,
      Eval.releaseShared rewrittenFuel right value =
        .ok (rightOut, rightRemaining) ∧
      HeapContentsEq leftOut rightOut ∧
      remaining ≤ rightRemaining := by
  obtain ⟨rightOut, sameFuelRun, outputHeaps⟩ :=
    heaps.releaseShared run
  let extra := rewrittenFuel - baselineFuel
  have extended := releaseShared_addFuel extra sameFuelRun
  have fuelEq : baselineFuel + extra = rewrittenFuel := by
    exact Nat.add_sub_of_le fuel
  refine ⟨rightOut, remaining + extra, ?_, outputHeaps,
    Nat.le_add_right remaining extra⟩
  simpa [fuelEq] using extended

/-- Deep unique destruction is likewise insensitive to accounting counters
when the semantic node arrays agree. -/
theorem dropUniqueWork_contents_congr :
    ∀ {fuel : Nat} {left right : Store} {values : List RVal}
      {leftOut : Store} {remaining : Nat},
      HeapContentsEq left right →
      dropUniqueWork fuel left values = .ok (leftOut, remaining) →
      ∃ rightOut,
        dropUniqueWork fuel right values = .ok (rightOut, remaining) ∧
        HeapContentsEq leftOut rightOut := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right values leftOut remaining heaps run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (left, 0) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, rfl, heaps⟩
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      intro left right values leftOut remaining heaps run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (left, fuel + 1) = (leftOut, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact ⟨right, rfl, heaps⟩
      | cons value rest =>
          cases value with
          | lit literal =>
              simp only [dropUniqueWork] at run ⊢
              exact ih heaps run
          | erased =>
              simp only [dropUniqueWork] at run ⊢
              exact ih heaps run
          | loc location =>
              have lookup := heaps.get?_eq location
              cases leftAt : left.get? location with
              | none => simp [dropUniqueWork, leftAt] at run
              | some box =>
                  have rightAt : right.get? location = some box := by
                    rw [← lookup]
                    exact leftAt
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | shared => simp [dropUniqueWork, leftAt] at run
                      | unique =>
                          cases node with
                          | papN address arity arguments =>
                              simp [dropUniqueWork, leftAt] at run
                          | ctorN cid fields =>
                              simp [dropUniqueWork, leftAt, rightAt] at run ⊢
                              exact ih (heaps.kill location) run

/-- The public single-value unique drop inherits exact-content congruence. -/
theorem HeapContentsEq.dropUnique {left right leftOut : Store}
    (heaps : HeapContentsEq left right) {fuel remaining : Nat}
    {value : RVal}
    (run : Eval.dropUnique fuel left value = .ok (leftOut, remaining)) :
    ∃ rightOut,
      Eval.dropUnique fuel right value = .ok (rightOut, remaining) ∧
      HeapContentsEq leftOut rightOut := by
  unfold Eval.dropUnique at run ⊢
  exact dropUniqueWork_contents_congr heaps run

/-- Extra heap fuel is preserved as extra remainder by successful unique
destruction. -/
theorem dropUniqueWork_addFuel :
    ∀ {fuel : Nat} {store output : Store} {values : List RVal}
      {remaining : Nat} (extra : Nat),
      dropUniqueWork fuel store values = .ok (output, remaining) →
      dropUniqueWork (fuel + extra) store values =
        .ok (output, remaining + extra) := by
  intro fuel
  induction fuel with
  | zero =>
      intro store output values remaining extra run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (store, 0) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          rfl
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      intro store output values remaining extra run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run ⊢
          have pairEq : (store, fuel + 1) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          rfl
      | cons value rest =>
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
          cases value with
          | lit literal =>
              simp only [dropUniqueWork] at run ⊢
              exact ih extra run
          | erased =>
              simp only [dropUniqueWork] at run ⊢
              exact ih extra run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | shared => simp [dropUniqueWork, found] at run
                      | unique =>
                          cases node with
                          | papN address arity arguments =>
                              simp [dropUniqueWork, found] at run
                          | ctorN cid fields =>
                              simp [dropUniqueWork, found] at run ⊢
                              exact ih extra run

/-- Unique destruction with extra target fuel preserves the history relation
and leaves the extra budget as an additive suffix. -/
theorem dropUniqueWork_historyIso {left right leftOut : Store}
    (heap : IxIR1.Sim.HeapHistoryIso left.heap right.heap)
    {leftFuel rightFuel remaining : Nat}
    {leftValues rightValues : List RVal}
    (fuel : leftFuel ≤ rightFuel)
    (values : IxIR1.Sim.RValsIso heap.locRel leftValues rightValues)
    (run : dropUniqueWork leftFuel left leftValues =
      .ok (leftOut, remaining)) :
    ∃ rightOut rightRemaining,
      ∃ outputHeap : IxIR1.Sim.HeapHistoryIso leftOut.heap rightOut.heap,
        dropUniqueWork rightFuel right rightValues =
            .ok (rightOut, rightRemaining) ∧
          remaining ≤ rightRemaining ∧
          outputHeap.locRel = heap.locRel := by
  obtain ⟨rightOut, outputHeap, sameFuelRun, outputRelation⟩ :=
    dropUniqueWork_historyIso_sameFuel heap values run
  let extra := rightFuel - leftFuel
  have extended := dropUniqueWork_addFuel extra sameFuelRun
  have fuelEq : leftFuel + extra = rightFuel := Nat.add_sub_of_le fuel
  refine ⟨rightOut, remaining + extra, outputHeap, ?_,
    Nat.le_add_right remaining extra, outputRelation⟩
  simpa [fuelEq] using extended

theorem dropUniqueWork_remaining_le :
    ∀ {fuel : Nat} {store output : Store} {values : List RVal}
      {remaining : Nat},
      dropUniqueWork fuel store values = .ok (output, remaining) →
      remaining ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro store output values remaining run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run
          have pairEq : (store, 0) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact Nat.le_refl 0
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      intro store output values remaining run
      cases values with
      | nil =>
          simp only [dropUniqueWork] at run
          have pairEq : (store, fuel + 1) = (output, remaining) :=
            Except.ok.inj run
          cases pairEq
          exact Nat.le_refl _
      | cons value rest =>
          have finish : remaining ≤ fuel → remaining ≤ fuel + 1 :=
            Nat.le_succ_of_le
          cases value with
          | lit literal =>
              simp only [dropUniqueWork] at run
              exact finish (ih run)
          | erased =>
              simp only [dropUniqueWork] at run
              exact finish (ih run)
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  cases box with
                  | mk world rc node =>
                      cases world with
                      | shared => simp [dropUniqueWork, found] at run
                      | unique =>
                          cases node with
                          | papN address arity arguments =>
                              simp [dropUniqueWork, found] at run
                          | ctorN cid fields =>
                              simp [dropUniqueWork, found] at run
                              exact finish (ih run)

theorem dropUnique_addFuel {fuel remaining : Nat}
    {store output : Store} {value : RVal} (extra : Nat)
    (run : Eval.dropUnique fuel store value = .ok (output, remaining)) :
    Eval.dropUnique (fuel + extra) store value =
      .ok (output, remaining + extra) := by
  unfold Eval.dropUnique at run ⊢
  exact dropUniqueWork_addFuel extra run

theorem HeapContentsEq.dropUnique_of_le {left right leftOut : Store}
    (heaps : HeapContentsEq left right)
    {baselineFuel rewrittenFuel remaining : Nat} {value : RVal}
    (fuel : baselineFuel ≤ rewrittenFuel)
    (run : Eval.dropUnique baselineFuel left value =
      .ok (leftOut, remaining)) :
    ∃ rightOut rightRemaining,
      Eval.dropUnique rewrittenFuel right value =
        .ok (rightOut, rightRemaining) ∧
      HeapContentsEq leftOut rightOut ∧
      remaining ≤ rightRemaining := by
  obtain ⟨rightOut, sameFuelRun, outputHeaps⟩ := heaps.dropUnique run
  let extra := rewrittenFuel - baselineFuel
  have extended := dropUnique_addFuel extra sameFuelRun
  have fuelEq : baselineFuel + extra = rewrittenFuel := by
    exact Nat.add_sub_of_le fuel
  refine ⟨rightOut, remaining + extra, ?_, outputHeaps,
    Nat.le_add_right remaining extra⟩
  simpa [fuelEq] using extended

/-- The store at which the executable cold reset begins retaining projected
fields. -/
def coldResetStartStore (store : Store) (location : Nat)
    (box : IxIR1.NodeBox) : Store :=
  ((((store.tickResetAttempt).setBox location
    { box with rc := box.rc - 1 }).rcTick).tickColdReset)

theorem coldResetStartStore_eq (store : Store) (location : Nat)
    (box : IxIR1.NodeBox) :
    coldResetStartStore store location box =
      (baselineDecrementStore store location box).tickResetAttempt.tickColdReset := by
  cases store with
  | mk heap resetAttempts hotResets coldResets reusedPayloadUnits peakLiveNodes =>
      cases heap with
      | mk nodes allocs reuses frees rcops =>
          rfl

/-- The compiler's baseline cold prefix and `resetShared`'s cold operation
produce the same semantic heap.  More precisely, from the baseline batch of
field retains this theorem constructs both the subsequent non-final parent
release and the exact batch retain required by the reset evaluator.  Their
stores differ only by reset-observation counters, so their heap components
are definitionally equal.

No distinctness premise is needed: repeated fields and a field that aliases
the parent are covered by `RetainSharedMany.decrement_commute`. -/
theorem coldPrefix_commutes {store baselineRetained : Store}
    {target rc : Nat} {cid : CtorId} {fields : Array RVal}
    {heapFuel : Nat}
    (hget : store.get? target =
      some ⟨.shared, rc, .ctorN cid fields⟩)
    (hmany : 1 < rc)
    (retained : RetainSharedMany store fields baselineRetained) :
    ∃ retainedRc,
      baselineRetained.get? target =
        some ⟨.shared, retainedRc, .ctorN cid fields⟩ ∧
      releaseShared (heapFuel + 1) baselineRetained (.loc target) =
        .ok (baselineDecrementStore baselineRetained target
          ⟨.shared, retainedRc, .ctorN cid fields⟩, heapFuel) ∧
      RetainSharedMany
        (coldResetStartStore store target
          ⟨.shared, rc, .ctorN cid fields⟩)
        fields
        ((baselineDecrementStore baselineRetained target
          ⟨.shared, retainedRc, .ctorN cid fields⟩).tickResetAttempt.tickColdReset) ∧
      (baselineDecrementStore baselineRetained target
          ⟨.shared, retainedRc, .ctorN cid fields⟩).heap =
        ((baselineDecrementStore baselineRetained target
          ⟨.shared, retainedRc, .ctorN cid fields⟩).tickResetAttempt.tickColdReset).heap := by
  have retainedList :
      RetainSharedMany store fields.toList.toArray baselineRetained := by
    simpa using retained
  obtain ⟨retainedRc, retainedAt, retainedMany, commuted⟩ :=
    RetainSharedMany.decrement_commute hget hmany retainedList
  have released :
      releaseShared (heapFuel + 1) baselineRetained (.loc target) =
        .ok (baselineDecrementStore baselineRetained target
          ⟨.shared, retainedRc, .ctorN cid fields⟩, heapFuel) := by
    simp [releaseShared, releaseSharedWork, retainedAt,
      baselineDecrementStore,
      show (retainedRc == 0) = false by
        exact beq_eq_false_iff_ne.mpr (by omega),
      show (retainedRc == 1) = false by
        exact beq_eq_false_iff_ne.mpr (by omega)]
  have resetAttemptRetained :=
    RetainSharedMany.tickResetAttempt commuted
  have resetRetained :=
    RetainSharedMany.tickColdReset resetAttemptRetained
  rw [← coldResetStartStore_eq] at resetRetained
  simpa using ⟨retainedRc, retainedAt, released, resetRetained, rfl⟩

/-- A non-final shared release performs exactly one refcount decrement and
spends exactly one unit of heap fuel. -/
theorem releaseShared_nonfinal {store : Store} {location rc : Nat}
    {node : IxIR1.Node} {heapFuel : Nat}
    (hget : store.get? location = some ⟨.shared, rc, node⟩)
    (hmany : 1 < rc) :
    releaseShared (heapFuel + 1) store (.loc location) =
      .ok (baselineDecrementStore store location
        ⟨.shared, rc, node⟩, heapFuel) := by
  simp [releaseShared, releaseSharedWork, hget, baselineDecrementStore,
    show (rc == 0) = false by exact beq_eq_false_iff_ne.mpr (by omega),
    show (rc == 1) = false by exact beq_eq_false_iff_ne.mpr (by omega)]

@[simp] theorem logicalHotResetStore_heap (store : Store) (location : Nat) :
    (logicalHotResetStore store location).heap = store.heap.kill location :=
  rfl

@[simp] theorem physicalHotResetStore_nodes (store : Store)
    (location : Nat) :
    (physicalHotResetStore store location).heap.nodes =
      store.heap.nodes.setIfInBounds location none :=
  rfl

@[simp] theorem logicalHotReuseStore_heap (store : Store) (location : Nat)
    (node : IxIR1.Node) :
    (logicalHotReuseStore store location node).1.heap =
      ((store.heap.kill location).allocNode .shared node).1 :=
  rfl

@[simp] theorem logicalHotReuseStore_location (store : Store)
    (location : Nat) (node : IxIR1.Node) :
    (logicalHotReuseStore store location node).2 =
      ((store.heap.kill location).allocNode .shared node).2 :=
  rfl

/-- A live source slot becomes the empty in-bounds reservation expected by
the physical credit. -/
theorem physicalHotResetStore_reserved {store : Store} {location : Nat}
    {box : IxIR1.NodeBox} (hget : store.get? location = some box) :
    (physicalHotResetStore store location).heap.nodes[location]? =
      some none := by
  have hnodes : store.heap.nodes[location]? = some (some box) :=
    IxIR1.Sim.nodes_get?_of_get? hget
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnodes
  simp [physicalHotResetStore, Eval.Store.tickResetAttempt,
    Eval.Store.tickHotReset, Eval.Store.reserve,
    hlt]

/-- Successful concrete physical credit consumption has exactly the IxIR₁
shared in-place-reuse heap.  IxIR₂-only reset and payload counters remain
outside that semantic heap equation. -/
theorem physicalHotReuseStore_ok {store : Store} {location : Nat}
    {oldBox : IxIR1.NodeBox} (node : IxIR1.Node) (payloadUnits : Nat)
    (hget : store.get? location = some oldBox) :
    ∃ result,
      physicalHotReuseStore store location node payloadUnits = .ok result ∧
      result.heap =
        IxIR1.Sim.reuseSharedNodeStore store.heap location node := by
  unfold physicalHotReuseStore Eval.Store.reuseReservation
  rw [physicalHotResetStore_reserved hget]
  refine ⟨_, rfl, ?_⟩
  rw [IxIR1.Sim.reuseSharedNodeStore_eq_direct]
  simp [physicalHotResetStore, Eval.Store.tickResetAttempt,
    Eval.Store.tickHotReset, Eval.Store.reserve,
    IxIR1.Store.setBox, Array.set!_eq_setIfInBounds]

/-! ## Hot shared-reuse soundness -/

/-- Concrete physical hot reuse and concrete logical hot reuse preserve exact
ownership and are related by a live-location bijection.  The reused physical
slot corresponds to the logical allocator's fresh append location; every
other live location corresponds to itself.

This is the heap-algebra leaf needed by the block simulation.  Its
`List.Perm` premise is the compositional ownership interface for arbitrary
field and tail-argument permutations recovered by the checked planner. -/
theorem hotReuse_sound {store : Store} {target : Nat}
    {oldNode newNode : IxIR1.Node} {before after : List IxIR1.Sim.Root}
    (payloadUnits : Nat)
    (hget : store.get? target = some ⟨.shared, 1, oldNode⟩)
    (hown : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc target⟩ :: before))
    (hpartition :
      (IxIR1.Sim.rootsFor .shared (IxIR1.Sim.nodeChildren oldNode) ++
          before).Perm
        (IxIR1.Sim.rootsFor .shared (IxIR1.Sim.nodeChildren newNode) ++
          after))
    (hworld : IxIR1.Sim.NodeWorld .shared newNode) :
    ∃ physical,
      physicalHotReuseStore store target newNode payloadUnits = .ok physical ∧
      ∃ iso : IxIR1.Sim.HeapIso physical.heap
          (logicalHotReuseStore store target newNode).1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc target⟩ :: after) ∧
        IxIR1.Sim.RootOwnership
            (logicalHotReuseStore store target newNode).1.heap
            (⟨.shared,
              .loc (logicalHotReuseStore store target newNode).2⟩ :: after) ∧
        iso.locRel target (logicalHotReuseStore store target newNode).2 := by
  obtain ⟨physical, reused, physicalHeap⟩ :=
    physicalHotReuseStore_ok newNode payloadUnits hget
  obtain ⟨iso, physicalOwned, logicalOwned, resultRelated⟩ :=
    IxIR1.Sim.reuse_shared_sound hget hown hpartition hworld
  refine ⟨physical, reused, ?_⟩
  rw [physicalHeap]
  exact ⟨iso, physicalOwned, logicalOwned, resultRelated⟩

/-- Concrete hot reuse additionally self-relates every surviving external
root.  This is the value-transport interface needed when the recursive
continuation retains locations other than the replaced result. -/
theorem hotReuse_sound_with_survivors {store : Store} {target : Nat}
    {oldNode newNode : IxIR1.Node} {before after : List IxIR1.Sim.Root}
    (payloadUnits : Nat)
    (hget : store.get? target = some ⟨.shared, 1, oldNode⟩)
    (hown : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc target⟩ :: before))
    (hpartition :
      (IxIR1.Sim.rootsFor .shared (IxIR1.Sim.nodeChildren oldNode) ++
          before).Perm
        (IxIR1.Sim.rootsFor .shared (IxIR1.Sim.nodeChildren newNode) ++
          after))
    (hworld : IxIR1.Sim.NodeWorld .shared newNode) :
    ∃ physical,
      physicalHotReuseStore store target newNode payloadUnits = .ok physical ∧
      ∃ iso : IxIR1.Sim.HeapIso physical.heap
          (logicalHotReuseStore store target newNode).1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc target⟩ :: after) ∧
        IxIR1.Sim.RootOwnership
            (logicalHotReuseStore store target newNode).1.heap
            (⟨.shared,
              .loc (logicalHotReuseStore store target newNode).2⟩ :: after) ∧
        iso.locRel target (logicalHotReuseStore store target newNode).2 ∧
        ∀ root ∈ after,
          IxIR1.Sim.RValIso iso.locRel root.value root.value := by
  obtain ⟨physical, reused, physicalHeap⟩ :=
    physicalHotReuseStore_ok newNode payloadUnits hget
  obtain ⟨iso, physicalOwned, logicalOwned, resultRelated,
      survivorsRelated⟩ :=
    IxIR1.Sim.reuse_shared_sound_with_survivors hget hown hpartition hworld
  refine ⟨physical, reused, ?_⟩
  rw [physicalHeap]
  exact ⟨iso, physicalOwned, logicalOwned, resultRelated,
    survivorsRelated⟩

/-- End-to-end hot-prefix leaf for the insertion proof.  Starting from the
actual successful baseline retain/release prefix, ordinary fresh allocation
is related to physical reset/reuse by a live-location bijection.  Thus this
theorem combines the previously separate baseline-prefix cancellation and
physical/logical reuse leaves at the first point where the rewritten block
can rejoin its tail call. -/
theorem hotPrefixReuse_sound {store baselineRetained baselineReleased : Store}
    {target : Nat} {oldCid newCid : CtorId}
    {fields newFields : Array RVal} {fieldFuel remaining : Nat}
    {before after : List IxIR1.Sim.Root}
    (payloadUnits : Nat)
    (targetAt : store.get? target =
      some ⟨.shared, 1, .ctorN oldCid fields⟩)
    (owned : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc target⟩ :: before))
    (retained : RetainSharedMany store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc target) = .ok (baselineReleased, remaining))
    (partition :
      (IxIR1.Sim.rootsFor .shared fields.toList ++ before).Perm
        (IxIR1.Sim.rootsFor .shared newFields.toList ++ after))
    (newWorld : IxIR1.Sim.NodeWorld .shared (.ctorN newCid newFields)) :
    let baselineAllocation :=
      baselineReleased.allocNode .shared (.ctorN newCid newFields)
    ∃ physical,
      physicalHotReuseStore store target (.ctorN newCid newFields)
          payloadUnits = .ok physical ∧
      ∃ iso : IxIR1.Sim.HeapIso physical.heap baselineAllocation.1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc target⟩ :: after) ∧
        IxIR1.Sim.RootOwnership baselineAllocation.1.heap
            (⟨.shared, .loc baselineAllocation.2⟩ :: after) ∧
        iso.locRel target baselineAllocation.2 := by
  dsimp only
  have prefixContents :
      HeapContentsEq baselineReleased (logicalHotResetStore store target) :=
    hotPrefix_contents targetAt owned retained released
  have allocationContents :
      HeapContentsEq
        (baselineReleased.allocNode .shared (.ctorN newCid newFields)).1
        (logicalHotReuseStore store target
          (.ctorN newCid newFields)).1 := by
    simpa [logicalHotReuseStore] using
      prefixContents.allocNode .shared (.ctorN newCid newFields)
  have allocationLocation :
      (baselineReleased.allocNode .shared (.ctorN newCid newFields)).2 =
        (logicalHotReuseStore store target
          (.ctorN newCid newFields)).2 := by
    simpa [logicalHotReuseStore] using
      prefixContents.allocNode_location .shared (.ctorN newCid newFields)
  obtain ⟨physical, reused, logicalIso, physicalOwned, logicalOwned,
      resultRelated⟩ :=
    hotReuse_sound (store := store) (target := target)
      (oldNode := .ctorN oldCid fields)
      (newNode := .ctorN newCid newFields)
      (before := before) (after := after) payloadUnits targetAt owned
      partition newWorld
  have baselineOwned :
      IxIR1.Sim.RootOwnership
        (baselineReleased.allocNode .shared
          (.ctorN newCid newFields)).1.heap
        (⟨.shared,
          .loc (baselineReleased.allocNode .shared
            (.ctorN newCid newFields)).2⟩ :: after) := by
    apply allocationContents.symm.rootOwnership
    rw [allocationLocation]
    exact logicalOwned
  have logicalClosed : IxIR1.Sim.StoreClosed
      (logicalHotReuseStore store target
        (.ctorN newCid newFields)).1.heap :=
    IxIR1.Sim.RootOwnership.storeClosed logicalOwned
  let logicalToBaseline := allocationContents.symm.toHeapIso logicalClosed
  let iso := logicalIso.trans logicalToBaseline
  have logicalResultLive := logicalOwned.roots_world
    (⟨.shared,
      .loc (logicalHotReuseStore store target
        (.ctorN newCid newFields)).2⟩ : IxIR1.Sim.Root) (by simp)
  obtain ⟨logicalResultBox, logicalResultAt, _⟩ := logicalResultLive
  have logicalToBaselineResult :
      logicalToBaseline.locRel
        (logicalHotReuseStore store target (.ctorN newCid newFields)).2
        (baselineReleased.allocNode .shared
          (.ctorN newCid newFields)).2 := by
    have selfRelated := allocationContents.symm.toHeapIso_rel_self
      logicalClosed logicalResultAt
    rw [allocationLocation]
    exact selfRelated
  refine ⟨physical, reused, iso, physicalOwned, baselineOwned, ?_⟩
  exact ⟨_, resultRelated, logicalToBaselineResult⟩

/-- The complete hot-prefix theorem additionally transports every surviving
external root through the composed physical-to-baseline heap isomorphism.
The reused result maps to the fresh baseline allocation, while all other
continuation roots remain self-related. -/
theorem hotPrefixReuse_sound_with_survivors
    {store baselineRetained baselineReleased : Store}
    {target : Nat} {oldCid newCid : CtorId}
    {fields newFields : Array RVal} {fieldFuel remaining : Nat}
    {before after : List IxIR1.Sim.Root}
    (payloadUnits : Nat)
    (targetAt : store.get? target =
      some ⟨.shared, 1, .ctorN oldCid fields⟩)
    (owned : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc target⟩ :: before))
    (retained : RetainSharedMany store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc target) = .ok (baselineReleased, remaining))
    (partition :
      (IxIR1.Sim.rootsFor .shared fields.toList ++ before).Perm
        (IxIR1.Sim.rootsFor .shared newFields.toList ++ after))
    (newWorld : IxIR1.Sim.NodeWorld .shared (.ctorN newCid newFields)) :
    let baselineAllocation :=
      baselineReleased.allocNode .shared (.ctorN newCid newFields)
    ∃ physical,
      physicalHotReuseStore store target (.ctorN newCid newFields)
          payloadUnits = .ok physical ∧
      ∃ iso : IxIR1.Sim.HeapIso physical.heap baselineAllocation.1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc target⟩ :: after) ∧
        IxIR1.Sim.RootOwnership baselineAllocation.1.heap
            (⟨.shared, .loc baselineAllocation.2⟩ :: after) ∧
        iso.locRel target baselineAllocation.2 ∧
        ∀ root ∈ after,
          IxIR1.Sim.RValIso iso.locRel root.value root.value := by
  dsimp only
  have prefixContents :
      HeapContentsEq baselineReleased (logicalHotResetStore store target) :=
    hotPrefix_contents targetAt owned retained released
  have allocationContents :
      HeapContentsEq
        (baselineReleased.allocNode .shared (.ctorN newCid newFields)).1
        (logicalHotReuseStore store target
          (.ctorN newCid newFields)).1 := by
    simpa [logicalHotReuseStore] using
      prefixContents.allocNode .shared (.ctorN newCid newFields)
  have allocationLocation :
      (baselineReleased.allocNode .shared (.ctorN newCid newFields)).2 =
        (logicalHotReuseStore store target
          (.ctorN newCid newFields)).2 := by
    simpa [logicalHotReuseStore] using
      prefixContents.allocNode_location .shared (.ctorN newCid newFields)
  obtain ⟨physical, reused, logicalIso, physicalOwned, logicalOwned,
      resultRelated, survivorsRelated⟩ :=
    hotReuse_sound_with_survivors (store := store) (target := target)
      (oldNode := .ctorN oldCid fields)
      (newNode := .ctorN newCid newFields)
      (before := before) (after := after) payloadUnits targetAt owned
      partition newWorld
  have baselineOwned :
      IxIR1.Sim.RootOwnership
        (baselineReleased.allocNode .shared
          (.ctorN newCid newFields)).1.heap
        (⟨.shared,
          .loc (baselineReleased.allocNode .shared
            (.ctorN newCid newFields)).2⟩ :: after) := by
    apply allocationContents.symm.rootOwnership
    rw [allocationLocation]
    exact logicalOwned
  have logicalClosed : IxIR1.Sim.StoreClosed
      (logicalHotReuseStore store target
        (.ctorN newCid newFields)).1.heap :=
    IxIR1.Sim.RootOwnership.storeClosed logicalOwned
  let logicalToBaseline := allocationContents.symm.toHeapIso logicalClosed
  let iso := logicalIso.trans logicalToBaseline
  have logicalResultLive := logicalOwned.roots_world
    (⟨.shared,
      .loc (logicalHotReuseStore store target
        (.ctorN newCid newFields)).2⟩ : IxIR1.Sim.Root) (by simp)
  obtain ⟨logicalResultBox, logicalResultAt, _⟩ := logicalResultLive
  have logicalToBaselineResult :
      logicalToBaseline.locRel
        (logicalHotReuseStore store target (.ctorN newCid newFields)).2
        (baselineReleased.allocNode .shared
          (.ctorN newCid newFields)).2 := by
    have selfRelated := allocationContents.symm.toHeapIso_rel_self
      logicalClosed logicalResultAt
    rw [allocationLocation]
    exact selfRelated
  refine ⟨physical, reused, iso, physicalOwned, baselineOwned,
    ⟨_, resultRelated, logicalToBaselineResult⟩, ?_⟩
  intro root member
  have logicalSelf := survivorsRelated root member
  have logicalToBaselineSelf : IxIR1.Sim.RValIso
      logicalToBaseline.locRel root.value root.value := by
    cases root with
    | mk world value =>
        cases value with
        | lit literal => exact .lit
        | erased => exact .erased
        | loc location =>
            obtain ⟨box, live, _⟩ := logicalOwned.roots_world
              ⟨world, .loc location⟩ (by simp [member])
            exact .loc (allocationContents.symm.toHeapIso_rel_self
              logicalClosed live)
  exact logicalSelf.trans logicalToBaselineSelf

/-- Physical hot reuse composes with an already-existing target-to-baseline
heap bijection.  The consumed location pair is removed, corresponding fresh
allocations extend the restricted relation, and physical in-place reuse is
then composed on the target side.  Every old related pair except the consumed
one remains related by the resulting bijection. -/
theorem hotPrefixReuse_sound_under_iso
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineLocation rewrittenLocation : Nat}
    {oldCid newCid : CtorId}
    {baselineFields rewrittenFields baselineNewFields rewrittenNewFields :
      Array RVal}
    {fieldFuel remaining : Nat}
    {baselineBefore baselineAfter rewrittenBefore rewrittenAfter :
      List IxIR1.Sim.Root}
    (payloadUnits : Nat)
    (inputIso : IxIR1.Sim.HeapIso rewrittenStore.heap baselineStore.heap)
    (locations : inputIso.locRel rewrittenLocation baselineLocation)
    (baselineAt : baselineStore.get? baselineLocation = some
      ⟨.shared, 1, .ctorN oldCid baselineFields⟩)
    (rewrittenAt : rewrittenStore.get? rewrittenLocation = some
      ⟨.shared, 1, .ctorN oldCid rewrittenFields⟩)
    (baselineOwned : IxIR1.Sim.RootOwnership baselineStore.heap
      (⟨.shared, .loc baselineLocation⟩ :: baselineBefore))
    (rewrittenOwned : IxIR1.Sim.RootOwnership rewrittenStore.heap
      (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenBefore))
    (retained : RetainSharedMany baselineStore baselineFields
      baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc baselineLocation) = .ok (baselineReleased, remaining))
    (baselinePartition :
      (IxIR1.Sim.rootsFor .shared baselineFields.toList ++
          baselineBefore).Perm
        (IxIR1.Sim.rootsFor .shared baselineNewFields.toList ++
          baselineAfter))
    (rewrittenPartition :
      (IxIR1.Sim.rootsFor .shared rewrittenFields.toList ++
          rewrittenBefore).Perm
        (IxIR1.Sim.rootsFor .shared rewrittenNewFields.toList ++
          rewrittenAfter))
    (newFieldsRelated : IxIR1.Sim.RValsIso
      (fun rewrittenCandidate baselineCandidate =>
        inputIso.locRel rewrittenCandidate baselineCandidate ∧
          rewrittenCandidate ≠ rewrittenLocation)
      rewrittenNewFields.toList baselineNewFields.toList) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN newCid baselineNewFields)
    ∃ physical,
      physicalHotReuseStore rewrittenStore rewrittenLocation
          (.ctorN newCid rewrittenNewFields) payloadUnits = .ok physical ∧
      ∃ outputIso : IxIR1.Sim.HeapIso physical.heap
          baselineAllocation.1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenAfter) ∧
        IxIR1.Sim.RootOwnership baselineAllocation.1.heap
            (⟨.shared, .loc baselineAllocation.2⟩ :: baselineAfter) ∧
        outputIso.locRel rewrittenLocation baselineAllocation.2 ∧
        ∀ {rewrittenCandidate baselineCandidate : Nat},
          inputIso.locRel rewrittenCandidate baselineCandidate →
          rewrittenCandidate ≠ rewrittenLocation →
          outputIso.locRel rewrittenCandidate baselineCandidate := by
  dsimp only
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN newCid baselineNewFields)
  let baselineLogicalAllocation :=
    logicalHotReuseStore baselineStore baselineLocation
      (.ctorN newCid baselineNewFields)
  let rewrittenLogicalAllocation :=
    logicalHotReuseStore rewrittenStore rewrittenLocation
      (.ctorN newCid rewrittenNewFields)
  have prefixContents : HeapContentsEq baselineReleased
      (logicalHotResetStore baselineStore baselineLocation) :=
    hotPrefix_contents baselineAt baselineOwned retained released
  have allocationContents : HeapContentsEq baselineAllocation.1
      baselineLogicalAllocation.1 := by
    simpa [baselineAllocation, baselineLogicalAllocation,
      logicalHotReuseStore] using
      prefixContents.allocNode .shared (.ctorN newCid baselineNewFields)
  have allocationLocation : baselineAllocation.2 =
      baselineLogicalAllocation.2 := by
    simpa [baselineAllocation, baselineLogicalAllocation,
      logicalHotReuseStore] using
      prefixContents.allocNode_location .shared
        (.ctorN newCid baselineNewFields)
  obtain ⟨_baselinePhysical, _baselineReused, _baselineIso,
      _baselinePhysicalOwned, baselineAllocationOwned, _baselineResult⟩ :=
    hotPrefixReuse_sound
      (store := baselineStore) (baselineRetained := baselineRetained)
      (baselineReleased := baselineReleased) (target := baselineLocation)
      (oldCid := oldCid) (newCid := newCid) (fields := baselineFields)
      (newFields := baselineNewFields) (fieldFuel := fieldFuel)
      (remaining := remaining) (before := baselineBefore)
      (after := baselineAfter) payloadUnits baselineAt baselineOwned retained
      released baselinePartition trivial
  have baselineLogicalOwned : IxIR1.Sim.RootOwnership
      baselineLogicalAllocation.1.heap
      (⟨.shared, .loc baselineLogicalAllocation.2⟩ :: baselineAfter) := by
    rw [← allocationLocation]
    exact allocationContents.rootOwnership
      (by simpa [baselineAllocation] using baselineAllocationOwned)
  have baselineLogicalClosed : IxIR1.Sim.StoreClosed
      baselineLogicalAllocation.1.heap :=
    IxIR1.Sim.RootOwnership.storeClosed baselineLogicalOwned
  let baselineExactIso :=
    allocationContents.symm.toHeapIso baselineLogicalClosed
  obtain ⟨physical, reused, physicalHeap⟩ :=
    physicalHotReuseStore_ok (.ctorN newCid rewrittenNewFields) payloadUnits
      rewrittenAt
  have rewrittenPhysicalOwnedRaw : IxIR1.Sim.RootOwnership
      (IxIR1.Sim.reuseSharedNodeStore rewrittenStore.heap rewrittenLocation
        (.ctorN newCid rewrittenNewFields))
      (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenAfter) :=
    rewrittenOwned.reuseSharedNode rewrittenAt rewrittenPartition trivial
  let killedIso := heapIsoKillShared inputIso locations rewrittenAt baselineAt
    rewrittenOwned
  have newNodesRelated : IxIR1.Sim.NodeIso killedIso.locRel
      (.ctorN newCid rewrittenNewFields) (.ctorN newCid baselineNewFields) := by
    apply IxIR1.Sim.NodeIso.ctor
    change IxIR1.Sim.RValsIso
      (fun rewrittenCandidate baselineCandidate =>
        inputIso.locRel rewrittenCandidate baselineCandidate ∧
          rewrittenCandidate ≠ rewrittenLocation)
      rewrittenNewFields.toList baselineNewFields.toList
    exact newFieldsRelated
  let crossRaw : IxIR1.Sim.HeapIso
      ((rewrittenStore.heap.kill rewrittenLocation).allocNode .shared
        (.ctorN newCid rewrittenNewFields)).1
      ((baselineStore.heap.kill baselineLocation).allocNode .shared
        (.ctorN newCid baselineNewFields)).1 :=
    killedIso.alloc (world := .shared) newNodesRelated
  let localRaw := IxIR1.Sim.HeapIso.reuseShared rewrittenAt
    rewrittenPhysicalOwnedRaw
  let outputIso := (localRaw.trans crossRaw).trans baselineExactIso
  have localResultRaw : localRaw.locRel rewrittenLocation
      ((rewrittenStore.heap.kill rewrittenLocation).allocNode .shared
        (.ctorN newCid rewrittenNewFields)).2 := by
    change IxIR1.Sim.reuseRel rewrittenStore.heap rewrittenLocation
      rewrittenLocation
      ((rewrittenStore.heap.kill rewrittenLocation).allocNode .shared
        (.ctorN newCid rewrittenNewFields)).2
    exact .inl ⟨rfl, by simp [IxIR1.Store.kill, IxIR1.Store.allocNode]⟩
  have crossResultRaw : crossRaw.locRel
      ((rewrittenStore.heap.kill rewrittenLocation).allocNode .shared
        (.ctorN newCid rewrittenNewFields)).2
      ((baselineStore.heap.kill baselineLocation).allocNode .shared
        (.ctorN newCid baselineNewFields)).2 := by
    exact .inl ⟨rfl, rfl⟩
  have baselineLogicalResultAt : baselineLogicalAllocation.1.get?
      baselineLogicalAllocation.2 =
        some ⟨.shared, 1, .ctorN newCid baselineNewFields⟩ := by
    exact IxIR1.Sim.HeapIso.get?_allocNode_new
      (logicalHotResetStore baselineStore baselineLocation).heap .shared
      (.ctorN newCid baselineNewFields)
  have exactResultSelf : baselineExactIso.locRel
      baselineLogicalAllocation.2 baselineLogicalAllocation.2 := by
    exact allocationContents.symm.toHeapIso_rel_self baselineLogicalClosed
      baselineLogicalResultAt
  have exactResult : baselineExactIso.locRel
      baselineLogicalAllocation.2 baselineAllocation.2 := by
    rw [allocationLocation]
    exact exactResultSelf
  have outputResult : outputIso.locRel rewrittenLocation
      baselineAllocation.2 := by
    exact ⟨baselineLogicalAllocation.2,
      ⟨rewrittenLogicalAllocation.2, localResultRaw, crossResultRaw⟩,
      exactResult⟩
  refine ⟨physical, reused, ?_⟩
  rw [physicalHeap]
  refine ⟨outputIso, rewrittenPhysicalOwnedRaw,
    by simpa [baselineAllocation] using baselineAllocationOwned,
    outputResult, ?_⟩
  intro rewrittenCandidate baselineCandidate related different
  obtain ⟨rewrittenBox, baselineBox, rewrittenLive, baselineLive, _boxes⟩ :=
    inputIso.related_live related
  have localSelfRaw : localRaw.locRel rewrittenCandidate
      rewrittenCandidate := by
    change IxIR1.Sim.reuseRel rewrittenStore.heap rewrittenLocation
      rewrittenCandidate rewrittenCandidate
    exact .inr ⟨rfl, different, rewrittenBox, rewrittenLive⟩
  have killedRelated : killedIso.locRel rewrittenCandidate
      baselineCandidate :=
    heapIsoKillShared_rel inputIso locations rewrittenAt baselineAt
      rewrittenOwned related different
  have crossOldRaw : crossRaw.locRel rewrittenCandidate
      baselineCandidate :=
    .inr killedRelated
  have baselineDifferent : baselineLocation ≠ baselineCandidate := by
    intro same
    subst baselineCandidate
    exact different (inputIso.right_unique related locations)
  have baselineKilledLive :
      (baselineStore.heap.kill baselineLocation).get? baselineCandidate =
        some baselineBox :=
    IxIR1.Sim.get?_kill_other baselineDifferent baselineAt baselineLive
  have baselineLogicalLive : baselineLogicalAllocation.1.get?
      baselineCandidate = some baselineBox := by
    exact IxIR1.Sim.HeapIso.get?_allocNode_old
      (world := .shared) (node := .ctorN newCid baselineNewFields)
      baselineKilledLive
  have exactOld : baselineExactIso.locRel baselineCandidate
      baselineCandidate :=
    allocationContents.symm.toHeapIso_rel_self baselineLogicalClosed
      baselineLogicalLive
  exact ⟨baselineCandidate,
    ⟨rewrittenCandidate, localSelfRaw, crossOldRaw⟩, exactOld⟩

/-- The complete accepted logical hot rewrite agrees with the concrete
baseline retain/release/allocation prefix and reaches the same recursive
argument vector. -/
theorem hotLogicalAcceptedPrefix {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {location : Nat} {sourceSchema allocationSchema : CtorSchema}
    {machine : Machine} {baselineRetained baselineReleased : Store}
    {stack : List Continuation} {fieldFuel remaining : Nat}
    {ambient : List IxIR1.Sim.Root}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (targetAt : machine.store.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (owned : IxIR1.Sim.RootOwnership machine.store.heap
      (⟨.shared, .loc location⟩ :: ambient))
    (retained : RetainSharedMany machine.store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds baselineReleased allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    let logicalAllocation :=
      (logicalHotResetStore machine.store location).allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
    Steps context .logical 4 machine
        { machine with
          store := logicalAllocation.1
          control := .running { definition, values := callValues } stack } ∧
      HeapContentsEq baselineAllocation.1 logicalAllocation.1 ∧
      baselineAllocation.2 = logicalAllocation.2 := by
  dsimp only
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let logicalAllocation :=
    (logicalHotResetStore machine.store location).allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
  have prefixContents : HeapContentsEq baselineReleased
      (logicalHotResetStore machine.store location) :=
    hotPrefix_contents targetAt owned retained released
  have allocationContents :
      HeapContentsEq baselineAllocation.1 logicalAllocation.1 := by
    simpa [baselineAllocation, logicalAllocation] using
      prefixContents.allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have allocationLocation :
      baselineAllocation.2 = logicalAllocation.2 := by
    simpa [baselineAllocation, logicalAllocation] using
      prefixContents.allocNode_location .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have logicalFieldWorlds : FieldWorlds
      (logicalHotResetStore machine.store location)
      allocationSchema newFields :=
    prefixContents.fieldWorlds fieldWorlds
  have logicalTailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc logicalAllocation.2))
      site.shape.tailArguments = .ok callValues := by
    rw [← allocationLocation]
    simpa [baselineAllocation] using tailResolved
  have viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩ fields :=
    ConstructorView.of_box targetAt rfl rfl
  have execution : Steps context .logical 4 machine
      { machine with
        store := logicalAllocation.1
        control := .running { definition, values := callValues } stack } := by
    simpa [logicalAllocation, logicalHotResetStore] using
      hotLogicalAcceptedControl site resetAt hotAt sourceSchemaAt
        allocationSchemaAt sourceLayout allocationLayout control
        parameterCount fieldCount sourceResolved viewed rfl
        allocationResolved
        (by simpa [logicalHotResetStore] using logicalFieldWorlds)
        (by simpa [logicalAllocation, logicalHotResetStore] using
          logicalTailResolved)
        arity nonempty
  exact ⟨execution, allocationContents, allocationLocation⟩

/-- The complete accepted cold rewrite reaches the same recursive argument
vector as any baseline prefix with equal semantic heap contents. -/
theorem coldAcceptedPrefix {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {interpretation : Interpretation}
    {definition : Function} {resetId hotId coldId : BlockId}
    {parameters fields newFields callValues : Array RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {sourceSchema allocationSchema : CtorSchema} {machine : Machine}
    {resetStore baselineReleased : Store} {stack : List Continuation}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (coldAt : definition.blocks[coldId]? = some
      (Reuse.creditBlock site.candidate
        (.optional site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor box fields)
    (shared : 1 < box.rc)
    (retained : RetainSharedMany
      ((((machine.store.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      fields resetStore)
    (contents : HeapContentsEq baselineReleased resetStore)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds baselineReleased allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    let resetAllocation := resetStore.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps context interpretation 4 machine
        { machine with
          store := resetAllocation.1
          control := .running { definition, values := callValues } stack } ∧
      HeapContentsEq baselineAllocation.1 resetAllocation.1 ∧
      baselineAllocation.2 = resetAllocation.2 := by
  dsimp only
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let resetAllocation := resetStore.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have allocationContents :
      HeapContentsEq baselineAllocation.1 resetAllocation.1 := by
    simpa [baselineAllocation, resetAllocation] using
      contents.allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have allocationLocation :
      baselineAllocation.2 = resetAllocation.2 := by
    simpa [baselineAllocation, resetAllocation] using
      contents.allocNode_location .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have resetTailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc resetAllocation.2))
      site.shape.tailArguments = .ok callValues := by
    rw [← allocationLocation]
    simpa [baselineAllocation] using tailResolved
  have resetFieldWorlds :
      FieldWorlds resetStore allocationSchema newFields :=
    contents.fieldWorlds fieldWorlds
  have execution : Steps context interpretation 4 machine
      { machine with
        store := resetAllocation.1
        control := .running { definition, values := callValues } stack } := by
    simpa [resetAllocation] using
      coldAcceptedControl site resetAt coldAt sourceSchemaAt
        allocationSchemaAt sourceLayout allocationLayout control
        parameterCount fieldCount sourceResolved viewed shared retained
        allocationResolved resetFieldWorlds
        (by simpa [resetAllocation] using resetTailResolved) arity nonempty
  exact ⟨execution, allocationContents, allocationLocation⟩

/-- The complete physical hot rewrite at one accepted site, from reset-block
entry through a recursive call whose argument vector is related to the
baseline call by the resulting heap isomorphism. -/
theorem hotPhysicalAcceptedPrefixIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceBlock : Block}
    (site : Reuse.Site limits validation sourceBlock)
    {context : Eval.Context} {definition : Function}
    {resetId hotId coldId : BlockId}
    {parameters fields newFields baselineCallValues : Array RVal}
    {location : Nat} {sourceSchema allocationSchema : CtorSchema}
    {machine : Machine} {baselineRetained baselineReleased : Store}
    {stack : List Continuation} {fieldFuel remaining : Nat}
    {before after : List IxIR1.Sim.Root}
    (resetAt : definition.blocks[resetId]? =
      some (Reuse.resetBlock site.candidate hotId coldId))
    (hotAt : definition.blocks[hotId]? = some
      (Reuse.creditBlock site.candidate
        (.required site.candidate.layout)))
    (sourceSchemaAt : context.schemas .shared site.shape.sourceConstructor =
      some sourceSchema)
    (allocationSchemaAt :
      context.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (sourceLayout : site.candidate.layout = sourceSchema.layout)
    (allocationLayout : site.candidate.layout = allocationSchema.layout)
    (control : machine.control = .running
      { definition
        block := resetId
        pc := 0
        values := parameters
        credits := #[] } stack)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (targetAt : machine.store.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (retained : RetainSharedMany machine.store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (owned : IxIR1.Sim.RootOwnership machine.store.heap
      (⟨.shared, .loc location⟩ :: before))
    (partition :
      (IxIR1.Sim.rootsFor .shared fields.toList ++ before).Perm
        (IxIR1.Sim.rootsFor .shared newFields.toList ++ after))
    (newWorld : IxIR1.Sim.NodeWorld .shared
      (.ctorN site.shape.allocationConstructor newFields))
    (mapped : MappedValuesInRoots site.shape
      (baselinePrefixValues parameters fields) after)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (fieldWorlds : FieldWorlds
      (((machine.store.tickResetAttempt).reserve location).tickHotReset)
      allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    ∃ physical,
      physicalHotReuseStore machine.store location
        (.ctorN site.shape.allocationConstructor newFields)
        allocationSchema.fields.size = .ok physical ∧
      ∃ iso : IxIR1.Sim.HeapIso physical.heap baselineAllocation.1.heap,
        IxIR1.Sim.RootOwnership physical.heap
            (⟨.shared, .loc location⟩ :: after) ∧
        IxIR1.Sim.RootOwnership baselineAllocation.1.heap
            (⟨.shared, .loc baselineAllocation.2⟩ :: after) ∧
        iso.locRel location baselineAllocation.2 ∧
        ∃ physicalCallValues,
          Steps context .physical 4 machine
            { machine with
              store := physical
              control := .running
                { definition, values := physicalCallValues } stack } ∧
          IxIR1.Sim.RValsIso (fun baseline physicalLocation =>
            iso.locRel physicalLocation baseline)
            baselineCallValues.toList physicalCallValues.toList := by
  dsimp only
  obtain ⟨physical, reused, iso, physicalOwned, baselineOwned,
      resultRelated, survivorsRelated⟩ :=
    hotPrefixReuse_sound_with_survivors
      (store := machine.store)
      (baselineRetained := baselineRetained)
      (baselineReleased := baselineReleased)
      (target := location)
      (oldCid := site.shape.sourceConstructor)
      (newCid := site.shape.allocationConstructor)
      (fields := fields) (newFields := newFields)
      (fieldFuel := fieldFuel) (remaining := remaining)
      (before := before) (after := after)
      allocationSchema.fields.size targetAt owned retained released partition
      newWorld
  have rootsReverse : ∀ root ∈ after,
      IxIR1.Sim.RValIso
        (fun baseline physicalLocation => iso.locRel physicalLocation baseline)
        root.value root.value := by
    intro root member
    exact (survivorsRelated root member).symm
  have selfRelated := mapped.selfRelated rootsReverse
  have viewed : ConstructorView machine.store location .shared
      site.shape.sourceConstructor
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩ fields :=
    ConstructorView.of_box targetAt rfl rfl
  obtain ⟨physicalCallValues, execution, callsRelated⟩ :=
    hotPhysicalAcceptedControlIso site resetAt hotAt sourceSchemaAt
      allocationSchemaAt sourceLayout allocationLayout control parameterCount
      fieldCount sourceResolved viewed rfl allocationResolved fieldWorlds
      (by simpa [physicalHotReuseStore, physicalHotResetStore] using reused)
      iso selfRelated resultRelated tailResolved arity nonempty
  exact ⟨physical, reused, iso, physicalOwned, baselineOwned, resultRelated,
    physicalCallValues, execution, callsRelated⟩

/-! ## Accepted function-rewrite simulations -/

/-- At an accepted function-rewrite decision, the original baseline block and
the logical hot replacement both reach the same recursive argument vector.
The theorem obtains every CFG lookup and both constructor layouts from the
proof-carrying rewrite rather than requiring callers to restate them. -/
theorem acceptedHotLogicalSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {store baselineRetained baselineReleased : Store}
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel remaining : Nat}
    {baselineStack rewrittenStack : List Continuation}
    {ambient : List IxIR1.Sim.Root} {allocationSchema : CtorSchema}
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (targetAt : store.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (owned : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc location⟩ :: ambient))
    (retained : RetainSharedMany store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    let logicalAllocation :=
      (logicalHotResetStore store location).allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
    Steps baselineContext .logical (2 * site.shape.fieldCount + 3)
        baselineMachine
        { store := baselineAllocation.1
          heapFuel := remaining
          control := .running
            { definition := source, values := callValues } baselineStack } ∧
      Steps rewrittenContext .logical 4 rewrittenMachine
        { rewrittenMachine with
          store := logicalAllocation.1
          control := .running
            { definition := rewrite.definition, values := callValues }
              rewrittenStack } ∧
      HeapContentsEq baselineAllocation.1 logicalAllocation.1 ∧
      baselineAllocation.2 = logicalAllocation.2 := by
  dsimp only
  obtain ⟨sourceAt, resetAt, hotAt, _coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  let baselineMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := parameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := rewrite.definition
          block := index
          values := parameters
          credits := #[] }
        rewrittenStack }
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let logicalAllocation :=
    (logicalHotResetStore store location).allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have targetNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have targetArity :
      callValues.size = rewrite.definition.signature.params.size := by
    simpa using arity
  have baselineControl : baselineMachine.control = .running
      { definition := source
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      baselineStack := by
    rfl
  have rewrittenControl : rewrittenMachine.control = .running
      { definition := rewrite.definition
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      rewrittenStack := by
    rfl
  have baselineExecution : Steps baselineContext .logical
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := callValues } baselineStack } := by
    simpa [baselineMachine, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := .logical)
        (definition := source) (blockId := index)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := remaining)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt baselineControl parameterCount fieldCount sourceResolved
        targetAt rfl retained released allocationSchemaAt allocationResolved
        baselineFieldWorlds tailResolved arity sourceNonempty
  obtain ⟨logicalExecution, contents, allocationLocation⟩ :=
    hotLogicalAcceptedPrefix site
      (context := rewrittenContext) (definition := rewrite.definition)
      (resetId := index) (hotId := source.blocks.size + helperOffset)
      (coldId := source.blocks.size + helperOffset + 1)
      (parameters := parameters) (fields := fields)
      (newFields := newFields) (callValues := callValues)
      (location := location) (sourceSchema := sourceSchema)
      (allocationSchema := allocationSchema) (machine := rewrittenMachine)
      (baselineRetained := baselineRetained)
      (baselineReleased := baselineReleased) (stack := rewrittenStack)
      (fieldFuel := fieldFuel) (remaining := remaining) (ambient := ambient)
      resetAt hotAt rewrittenSourceSchemaAt rewrittenAllocationSchemaAt
      sourceLayout
      allocationLayout rewrittenControl parameterCount fieldCount
      sourceResolved targetAt owned retained released allocationResolved
      baselineFieldWorlds tailResolved targetArity targetNonempty
  exact ⟨baselineExecution,
    by simpa [rewrittenMachine, logicalAllocation] using logicalExecution,
    by simpa [baselineAllocation, logicalAllocation] using contents,
    by simpa [baselineAllocation, logicalAllocation] using
      allocationLocation⟩

/-- At an accepted decision whose source has more than one shared owner, the
baseline retain/release prefix and the rewritten cold reset commute.  Thus
both actual CFGs reach the same call arguments and heaps with identical live
contents, although reset-observation counters may differ. -/
theorem acceptedColdSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {store baselineRetained : Store}
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel rc retainedRc : Nat}
    {baselineStack rewrittenStack : List Continuation}
    {allocationSchema : CtorSchema}
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (targetAt : store.get? location = some
      ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩)
    (shared : 1 < rc)
    (retained : RetainSharedMany store fields baselineRetained)
    (retainedAt : baselineRetained.get? location = some
      ⟨.shared, retainedRc, .ctorN site.shape.sourceConstructor fields⟩)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds : FieldWorlds
      (baselineDecrementStore baselineRetained location
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩)
      allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc ((baselineDecrementStore baselineRetained location
          ⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor fields⟩).allocNode .shared
              (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    let baselineReleased := baselineDecrementStore baselineRetained location
      ⟨.shared, retainedRc, .ctorN site.shape.sourceConstructor fields⟩
    let resetStore := baselineReleased.tickResetAttempt.tickColdReset
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    let resetAllocation := resetStore.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps baselineContext interpretation (2 * site.shape.fieldCount + 3)
        baselineMachine
        { store := baselineAllocation.1
          heapFuel := fieldFuel
          control := .running
            { definition := source, values := callValues } baselineStack } ∧
      Steps rewrittenContext interpretation 4 rewrittenMachine
        { rewrittenMachine with
          store := resetAllocation.1
          control := .running
            { definition := rewrite.definition, values := callValues }
              rewrittenStack } ∧
      HeapContentsEq baselineAllocation.1 resetAllocation.1 ∧
      baselineAllocation.2 = resetAllocation.2 := by
  dsimp only
  obtain ⟨sourceAt, resetAt, _hotAt, coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  obtain ⟨actualRetainedRc, actualRetainedAt, released,
      resetRetained, heapsEqual⟩ :=
    coldPrefix_commutes (heapFuel := fieldFuel) targetAt shared retained
  have retainedBoxesEqual :
      (⟨.shared, actualRetainedRc,
          .ctorN site.shape.sourceConstructor fields⟩ : IxIR1.NodeBox) =
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩ :=
    Option.some.inj (actualRetainedAt.symm.trans retainedAt)
  have retainedRcEqual : actualRetainedRc = retainedRc := by
    cases retainedBoxesEqual
    rfl
  subst actualRetainedRc
  let baselineMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := parameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := rewrite.definition
          block := index
          values := parameters
          credits := #[] }
        rewrittenStack }
  let baselineReleased := baselineDecrementStore baselineRetained location
    ⟨.shared, retainedRc, .ctorN site.shape.sourceConstructor fields⟩
  let resetStore := baselineReleased.tickResetAttempt.tickColdReset
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let resetAllocation := resetStore.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have targetNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have targetArity :
      callValues.size = rewrite.definition.signature.params.size := by
    simpa using arity
  have baselineControl : baselineMachine.control = .running
      { definition := source
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      baselineStack := by
    rfl
  have rewrittenControl : rewrittenMachine.control = .running
      { definition := rewrite.definition
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      rewrittenStack := by
    rfl
  have contents : HeapContentsEq baselineReleased resetStore := by
    refine ⟨?_⟩
    simpa [baselineReleased, resetStore] using
      congrArg IxIR1.Store.nodes heapsEqual
  have viewed : ConstructorView rewrittenMachine.store location .shared
      site.shape.sourceConstructor
      ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩ fields :=
    ConstructorView.of_box targetAt rfl rfl
  have baselineExecution : Steps baselineContext interpretation
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := fieldFuel
        control := .running
          { definition := source, values := callValues } baselineStack } := by
    simpa [baselineMachine, baselineReleased, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := interpretation)
        (definition := source) (blockId := index)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := fieldFuel)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt baselineControl parameterCount fieldCount sourceResolved
        targetAt rfl retained (by simpa [baselineReleased] using released)
        allocationSchemaAt allocationResolved
        (by simpa [baselineReleased] using baselineFieldWorlds)
        (by simpa [baselineReleased] using tailResolved) arity
        sourceNonempty
  obtain ⟨coldExecution, allocationContents, allocationLocation⟩ :=
    coldAcceptedPrefix site
      (context := rewrittenContext) (interpretation := interpretation)
      (definition := rewrite.definition) (resetId := index)
      (hotId := source.blocks.size + helperOffset)
      (coldId := source.blocks.size + helperOffset + 1)
      (parameters := parameters) (fields := fields)
      (newFields := newFields) (callValues := callValues)
      (location := location)
      (box := ⟨.shared, rc,
        .ctorN site.shape.sourceConstructor fields⟩)
      (sourceSchema := sourceSchema) (allocationSchema := allocationSchema)
      (machine := rewrittenMachine) (resetStore := resetStore)
      (baselineReleased := baselineReleased) (stack := rewrittenStack)
      resetAt coldAt rewrittenSourceSchemaAt rewrittenAllocationSchemaAt
      sourceLayout
      allocationLayout rewrittenControl parameterCount fieldCount
      sourceResolved viewed shared
      (by simpa [coldResetStartStore, resetStore, baselineReleased] using
        resetRetained)
      contents allocationResolved
      (by simpa [baselineReleased] using baselineFieldWorlds)
      (by simpa [baselineReleased] using tailResolved) targetArity
      targetNonempty
  exact ⟨baselineExecution,
    by simpa [rewrittenMachine, resetStore, baselineReleased,
      resetAllocation] using coldExecution,
    by simpa [baselineAllocation, resetAllocation, baselineReleased,
      resetStore] using
      allocationContents,
    by simpa [baselineAllocation, resetAllocation, baselineReleased,
      resetStore] using
      allocationLocation⟩

/-- At an accepted unit-refcount decision, the original baseline block and
the physical hot replacement both execute to recursive calls.  The resulting
heaps and argument vectors are related by the concrete reuse location
bijection, so this statement does not assume that fresh allocation happened
to choose the reused address. -/
theorem acceptedHotPhysicalSimulationIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {store baselineRetained baselineReleased : Store}
    {parameters fields newFields baselineCallValues : Array RVal}
    {location fieldFuel remaining : Nat}
    {baselineStack rewrittenStack : List Continuation}
    {before after : List IxIR1.Sim.Root}
    {allocationSchema : CtorSchema}
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (targetAt : store.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (retained : RetainSharedMany store fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (owned : IxIR1.Sim.RootOwnership store.heap
      (⟨.shared, .loc location⟩ :: before))
    (partition :
      (IxIR1.Sim.rootsFor .shared fields.toList ++ before).Perm
        (IxIR1.Sim.rootsFor .shared newFields.toList ++ after))
    (newWorld : IxIR1.Sim.NodeWorld .shared
      (.ctorN site.shape.allocationConstructor newFields))
    (mapped : MappedValuesInRoots site.shape
      (baselinePrefixValues parameters fields) after)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema newFields)
    (physicalFieldWorlds : FieldWorlds
      (physicalHotResetStore store location) allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store
        heapFuel := fieldFuel + 1
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    Steps baselineContext .physical (2 * site.shape.fieldCount + 3)
        baselineMachine
        { store := baselineAllocation.1
          heapFuel := remaining
          control := .running
            { definition := source, values := baselineCallValues }
              baselineStack } ∧
      ∃ physical,
        physicalHotReuseStore store location
            (.ctorN site.shape.allocationConstructor newFields)
            allocationSchema.fields.size = .ok physical ∧
        ∃ iso : IxIR1.Sim.HeapIso physical.heap baselineAllocation.1.heap,
          IxIR1.Sim.RootOwnership physical.heap
              (⟨.shared, .loc location⟩ :: after) ∧
          IxIR1.Sim.RootOwnership baselineAllocation.1.heap
              (⟨.shared, .loc baselineAllocation.2⟩ :: after) ∧
          iso.locRel location baselineAllocation.2 ∧
          ∃ physicalCallValues,
            Steps rewrittenContext .physical 4 rewrittenMachine
              { rewrittenMachine with
                store := physical
                control := .running
                  { definition := rewrite.definition
                    values := physicalCallValues }
                  rewrittenStack } ∧
            IxIR1.Sim.RValsIso (fun baseline physicalLocation =>
              iso.locRel physicalLocation baseline)
              baselineCallValues.toList physicalCallValues.toList := by
  dsimp only
  obtain ⟨sourceAt, resetAt, hotAt, _coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  let baselineMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := parameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store
      heapFuel := fieldFuel + 1
      control := .running
        { definition := rewrite.definition
          block := index
          values := parameters
          credits := #[] }
        rewrittenStack }
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have targetNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have targetArity : baselineCallValues.size =
      rewrite.definition.signature.params.size := by
    simpa using arity
  have baselineControl : baselineMachine.control = .running
      { definition := source
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      baselineStack := by
    rfl
  have rewrittenControl : rewrittenMachine.control = .running
      { definition := rewrite.definition
        block := index
        pc := 0
        values := parameters
        credits := #[] }
      rewrittenStack := by
    rfl
  have baselineExecution : Steps baselineContext .physical
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := baselineCallValues }
            baselineStack } := by
    simpa [baselineMachine, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := .physical)
        (definition := source) (blockId := index)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := baselineCallValues)
        (location := location) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := remaining)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt baselineControl parameterCount fieldCount sourceResolved
        targetAt rfl retained released allocationSchemaAt allocationResolved
        baselineFieldWorlds tailResolved arity sourceNonempty
  obtain ⟨physical, reused, iso, physicalOwned, baselineOwned,
      resultRelated, physicalCallValues, physicalExecution, callsRelated⟩ :=
    hotPhysicalAcceptedPrefixIso site
      (context := rewrittenContext) (definition := rewrite.definition)
      (resetId := index) (hotId := source.blocks.size + helperOffset)
      (coldId := source.blocks.size + helperOffset + 1)
      (parameters := parameters) (fields := fields)
      (newFields := newFields) (baselineCallValues := baselineCallValues)
      (location := location) (sourceSchema := sourceSchema)
      (allocationSchema := allocationSchema) (machine := rewrittenMachine)
      (baselineRetained := baselineRetained)
      (baselineReleased := baselineReleased) (stack := rewrittenStack)
      (fieldFuel := fieldFuel) (remaining := remaining)
      (before := before) (after := after)
      resetAt hotAt rewrittenSourceSchemaAt rewrittenAllocationSchemaAt
      sourceLayout
      allocationLayout rewrittenControl parameterCount fieldCount
      sourceResolved targetAt retained released owned partition newWorld mapped
      allocationResolved physicalFieldWorlds tailResolved targetArity
      targetNonempty
  exact ⟨baselineExecution, physical, reused, iso,
    by simpa [baselineAllocation] using physicalOwned,
    by simpa [baselineAllocation] using baselineOwned,
    by simpa [baselineAllocation] using resultRelated,
    physicalCallValues,
    by simpa [rewrittenMachine] using physicalExecution,
    callsRelated⟩

/-! ## Stable whole-program relation -/

/-- Credits in two executions agree modulo the same location relation as
ordinary runtime values.  Logical reservations carry no address; physical
reservations carry corresponding (possibly numerically different) dead heap
slots. -/
inductive StableCreditIso (locRel : Nat → Nat → Prop) :
    Option Credit → Option Credit → Prop where
  | consumed : StableCreditIso locRel none none
  | absent (layout : LayoutId) : StableCreditIso locRel
      (some { layout, presence := .absent })
      (some { layout, presence := .absent })
  | logical (layout : LayoutId) : StableCreditIso locRel
      (some { layout, presence := .present none })
      (some { layout, presence := .present none })
  | physical {layout : LayoutId} {baselineLocation rewrittenLocation : Nat}
      (location : locRel baselineLocation rewrittenLocation) :
      StableCreditIso locRel
        (some { layout, presence := .present (some baselineLocation) })
        (some { layout, presence := .present (some rewrittenLocation) })

/-- Pointwise credit-file isomorphism. -/
inductive StableCreditsIso (locRel : Nat → Nat → Prop) :
    List (Option Credit) → List (Option Credit) → Prop where
  | nil : StableCreditsIso locRel [] []
  | cons {baseline rewritten : Option Credit}
      {baselineTail rewrittenTail : List (Option Credit)}
      (head : StableCreditIso locRel baseline rewritten)
      (tail : StableCreditsIso locRel baselineTail rewrittenTail) :
      StableCreditsIso locRel (baseline :: baselineTail)
        (rewritten :: rewrittenTail)

namespace StableCreditIso

theorem mono {oldRel newRel : Nat → Nat → Prop}
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation)
    {baseline rewritten : Option Credit}
    (credit : StableCreditIso oldRel baseline rewritten) :
    StableCreditIso newRel baseline rewritten := by
  cases credit with
  | consumed => exact .consumed
  | absent layout => exact .absent layout
  | logical layout => exact .logical layout
  | physical location => exact .physical (lift location)

theorem refl : ∀ credit : Option Credit,
    StableCreditIso (fun left right => left = right) credit credit
  | none => .consumed
  | some ⟨layout, .absent⟩ => .absent layout
  | some ⟨layout, .present none⟩ => .logical layout
  | some ⟨_layout, .present (some _location)⟩ => .physical rfl

theorem eq_of_location_eq {baseline rewritten : Option Credit}
    (credit : StableCreditIso (fun left right => left = right)
      baseline rewritten) : baseline = rewritten := by
  cases credit with
  | consumed => rfl
  | absent layout => rfl
  | logical layout => rfl
  | physical location => cases location; rfl

theorem isSome_eq {locRel : Nat → Nat → Prop}
    {baseline rewritten : Option Credit}
    (credit : StableCreditIso locRel baseline rewritten) :
    baseline.isSome = rewritten.isSome := by
  cases credit <;> rfl

theorem present_parts {locRel : Nat → Nat → Prop}
    {baseline rewritten : Credit}
    (credit : StableCreditIso locRel (some baseline) (some rewritten)) :
    baseline.layout = rewritten.layout ∧
      baseline.isPresent = rewritten.isPresent := by
  cases credit with
  | absent layout => exact ⟨rfl, rfl⟩
  | logical layout => exact ⟨rfl, rfl⟩
  | physical location => exact ⟨rfl, rfl⟩

theorem absent_parts {locRel : Nat → Nat → Prop}
    {baseline rewritten : Credit}
    (credit : StableCreditIso locRel (some baseline) (some rewritten))
    (absent : baseline.presence = .absent) :
    baseline.layout = rewritten.layout ∧
      rewritten.presence = .absent := by
  cases credit <;> simp_all

theorem logical_parts {locRel : Nat → Nat → Prop}
    {baseline rewritten : Credit}
    (credit : StableCreditIso locRel (some baseline) (some rewritten))
    (logical : baseline.presence = .present none) :
    baseline.layout = rewritten.layout ∧
      rewritten.presence = .present none := by
  cases credit <;> simp_all

theorem physical_parts {locRel : Nat → Nat → Prop}
    {baseline rewritten : Credit} {baselineLocation : Nat}
    (credit : StableCreditIso locRel (some baseline) (some rewritten))
    (physical : baseline.presence = .present (some baselineLocation)) :
    ∃ rewrittenLocation,
      baseline.layout = rewritten.layout ∧
        rewritten.presence = .present (some rewrittenLocation) ∧
        locRel baselineLocation rewrittenLocation := by
  cases credit <;> simp_all

end StableCreditIso

namespace StableCreditsIso

theorem mono {oldRel newRel : Nat → Nat → Prop}
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation) :
    ∀ {baseline rewritten : List (Option Credit)},
      StableCreditsIso oldRel baseline rewritten →
      StableCreditsIso newRel baseline rewritten
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (head.mono lift) (mono lift tail)

theorem refl : ∀ credits : List (Option Credit),
    StableCreditsIso (fun left right => left = right) credits credits
  | [] => .nil
  | credit :: rest => .cons (StableCreditIso.refl credit) (refl rest)

theorem eq_of_location_eq {baseline rewritten : List (Option Credit)}
    (credits : StableCreditsIso (fun left right => left = right)
      baseline rewritten) : baseline = rewritten := by
  induction credits with
  | nil => rfl
  | cons head tail ih => rw [head.eq_of_location_eq, ih]

theorem length_eq {locRel : Nat → Nat → Prop}
    {baseline rewritten : List (Option Credit)}
    (credits : StableCreditsIso locRel baseline rewritten) :
    baseline.length = rewritten.length := by
  induction credits with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append {locRel : Nat → Nat → Prop}
    {baseline₁ rewritten₁ baseline₂ rewritten₂ : List (Option Credit)}
    (first : StableCreditsIso locRel baseline₁ rewritten₁)
    (second : StableCreditsIso locRel baseline₂ rewritten₂) :
    StableCreditsIso locRel (baseline₁ ++ baseline₂)
      (rewritten₁ ++ rewritten₂) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem get? {locRel : Nat → Nat → Prop}
    {baseline rewritten : List (Option Credit)}
    (credits : StableCreditsIso locRel baseline rewritten)
    {index : Nat} {baselineCredit : Option Credit}
    (found : baseline[index]? = some baselineCredit) :
    ∃ rewrittenCredit,
      rewritten[index]? = some rewrittenCredit ∧
        StableCreditIso locRel baselineCredit rewrittenCredit := by
  induction credits generalizing index baselineCredit with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at found ⊢
          cases found
          exact ⟨_, rfl, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at found ⊢
          exact ih found

theorem set_none {locRel : Nat → Nat → Prop} :
    ∀ {baseline rewritten : List (Option Credit)},
      StableCreditsIso locRel baseline rewritten →
      ∀ index,
        StableCreditsIso locRel (baseline.set index none)
          (rewritten.set index none)
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons _head tail, 0 => .cons .consumed tail
  | _ :: _, _ :: _, .cons head tail, index + 1 =>
      .cons head (set_none tail index)

theorem array_set_none {locRel : Nat → Nat → Prop}
    {baseline rewritten : Array (Option Credit)}
    (credits : StableCreditsIso locRel baseline.toList rewritten.toList)
    (index : Nat) :
    StableCreditsIso locRel
      (baseline.setIfInBounds index none).toList
      (rewritten.setIfInBounds index none).toList := by
  simpa [Array.toList_setIfInBounds] using credits.set_none index

theorem any_isSome_eq {locRel : Nat → Nat → Prop}
    {baseline rewritten : List (Option Credit)}
    (credits : StableCreditsIso locRel baseline rewritten) :
    baseline.any Option.isSome = rewritten.any Option.isSome := by
  induction credits with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.any_cons, head.isSome_eq, ih]

end StableCreditsIso

/-- A physical credit does not reserve the distinguished location.  Logical,
absent, and consumed credits contain no concrete heap address. -/
def CreditAvoidsLocation (location : Nat) : Option Credit → Prop
  | some { presence := .present (some reserved), .. } => reserved ≠ location
  | _ => True

def CreditsAvoidLocation (location : Nat) : List (Option Credit) → Prop
  | [] => True
  | credit :: rest =>
      CreditAvoidsLocation location credit ∧ CreditsAvoidLocation location rest

theorem StableCreditIso.transportRelation
    {oldRel newRel : Nat → Nat → Prop} {removed : Nat}
    {baseline rewritten : Option Credit}
    (credit : StableCreditIso oldRel baseline rewritten)
    (avoids : CreditAvoidsLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableCreditIso newRel baseline rewritten := by
  cases credit with
  | consumed => exact .consumed
  | absent layout => exact .absent layout
  | logical layout => exact .logical layout
  | physical location => exact .physical (lift location avoids)

theorem StableCreditsIso.transportRelation
    {oldRel newRel : Nat → Nat → Prop} {removed : Nat}
    {baseline rewritten : List (Option Credit)}
    (credits : StableCreditsIso oldRel baseline rewritten)
    (avoids : CreditsAvoidLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableCreditsIso newRel baseline rewritten := by
  induction credits with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (head.transportRelation avoids.1 lift)
        (ih avoids.2)

/-- A source frame and its rewritten counterpart occupy the same control
position and carry pointwise related runtime values.  Stable boundaries have
pointwise related credit files; the generated reset/helper diamond is treated
as the four-step macro transition proved above. -/
structure StableFrameIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    (locRel : Nat → Nat → Prop) (baseline rewritten : Frame) : Prop where
  baselineDefinition : baseline.definition = source
  rewrittenDefinition : rewritten.definition = rewrite.definition
  block : baseline.block = rewritten.block
  pc : baseline.pc = rewritten.pc
  values : IxIR1.Sim.RValsIso locRel
    baseline.values.toList rewritten.values.toList
  credits : StableCreditsIso locRel
    baseline.credits.toList rewritten.credits.toList

/-- Existentially select the retained function rewrite governing a stable
frame pair.  Direct-call lookup in `Reuse.Trace` constructs exactly this
witness for callees. -/
inductive StableFrameRel (limits : Validate.Limits)
    (validation : Validate.Context) (locRel : Nat → Nat → Prop) :
    Frame → Frame → Prop where
  | rewritten {source : Function}
      (rewrite : Reuse.FunctionRewrite limits validation source)
      {baseline rewritten : Frame}
      (frame : StableFrameIso rewrite locRel baseline rewritten) :
      StableFrameRel limits validation locRel baseline rewritten

inductive StableContinuationIso (limits : Validate.Limits)
    (validation : Validate.Context) (locRel : Nat → Nat → Prop) :
    Continuation → Continuation → Prop where
  | resume {baseline rewritten : Frame}
      (frame : StableFrameRel limits validation locRel baseline rewritten) :
      StableContinuationIso limits validation locRel
        (.resume baseline) (.resume rewritten)
  | applyMore {baselineArguments rewrittenArguments : Array RVal}
      {baseline rewritten : Frame}
      (arguments : IxIR1.Sim.RValsIso locRel
        baselineArguments.toList rewrittenArguments.toList)
      (frame : StableFrameRel limits validation locRel baseline rewritten) :
      StableContinuationIso limits validation locRel
        (.applyMore baselineArguments baseline)
        (.applyMore rewrittenArguments rewritten)

inductive StableStackIso (limits : Validate.Limits)
    (validation : Validate.Context) (locRel : Nat → Nat → Prop) :
    List Continuation → List Continuation → Prop where
  | nil : StableStackIso limits validation locRel [] []
  | cons {baseline rewritten : Continuation}
      {baselineTail rewrittenTail : List Continuation}
      (head : StableContinuationIso limits validation locRel
        baseline rewritten)
      (tail : StableStackIso limits validation locRel
        baselineTail rewrittenTail) :
      StableStackIso limits validation locRel
        (baseline :: baselineTail) (rewritten :: rewrittenTail)

/-- Runtime values retained in a suspended frame avoid one location.  Credit
reservations are controlled separately by the no-live-credit invariant and do
not denote ordinary live heap roots. -/
def FrameValuesAvoidLocation (location : Nat) (frame : Frame) : Prop :=
  ∀ value ∈ frame.values.toList, value ≠ .loc location

def FrameCreditsAvoidLocation (location : Nat) (frame : Frame) : Prop :=
  CreditsAvoidLocation location frame.credits.toList

def ContinuationValuesAvoidLocation (location : Nat) :
    Continuation → Prop
  | .resume frame => FrameValuesAvoidLocation location frame
  | .applyMore arguments frame =>
      (∀ value ∈ arguments.toList, value ≠ .loc location) ∧
        FrameValuesAvoidLocation location frame

def ContinuationCreditsAvoidLocation (location : Nat) :
    Continuation → Prop
  | .resume frame => FrameCreditsAvoidLocation location frame
  | .applyMore _ frame => FrameCreditsAvoidLocation location frame

def StackValuesAvoidLocation (location : Nat) :
    List Continuation → Prop
  | [] => True
  | continuation :: rest =>
      ContinuationValuesAvoidLocation location continuation ∧
        StackValuesAvoidLocation location rest

def StackCreditsAvoidLocation (location : Nat) :
    List Continuation → Prop
  | [] => True
  | continuation :: rest =>
      ContinuationCreditsAvoidLocation location continuation ∧
        StackCreditsAvoidLocation location rest

theorem StableFrameIso.mono {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {oldRel newRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite oldRel baseline rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation) :
    StableFrameIso rewrite newRel baseline rewritten :=
  ⟨frame.baselineDefinition, frame.rewrittenDefinition, frame.block, frame.pc,
    frame.values.mono lift, frame.credits.mono lift⟩

theorem StableFrameRel.mono {limits : Validate.Limits}
    {validation : Validate.Context} {oldRel newRel : Nat → Nat → Prop}
    {baseline rewritten : Frame}
    (frame : StableFrameRel limits validation oldRel baseline rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation) :
    StableFrameRel limits validation newRel baseline rewritten := by
  cases frame with
  | rewritten rewrite related => exact .rewritten rewrite (related.mono lift)

theorem StableContinuationIso.mono {limits : Validate.Limits}
    {validation : Validate.Context} {oldRel newRel : Nat → Nat → Prop}
    {baseline rewritten : Continuation}
    (continuation : StableContinuationIso limits validation oldRel
      baseline rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation) :
    StableContinuationIso limits validation newRel baseline rewritten := by
  cases continuation with
  | resume frame => exact .resume (frame.mono lift)
  | applyMore arguments frame =>
      exact .applyMore (arguments.mono lift) (frame.mono lift)

theorem StableStackIso.mono {limits : Validate.Limits}
    {validation : Validate.Context} {oldRel newRel : Nat → Nat → Prop}
    {baseline rewritten : List Continuation}
    (stack : StableStackIso limits validation oldRel baseline rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      newRel baselineLocation rewrittenLocation) :
    StableStackIso limits validation newRel baseline rewritten := by
  induction stack with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono lift) ih

/-- Change the location relation of a stable frame when every rewritten value
survives and each old related location pair embeds into the new relation. -/
theorem StableFrameIso.transportRelation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {oldRel newRel : Nat → Nat → Prop} {removed : Nat}
    {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite oldRel baseline rewritten)
    (avoids : FrameValuesAvoidLocation removed rewritten)
    (creditsAvoid : FrameCreditsAvoidLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableFrameIso rewrite newRel baseline rewritten :=
  ⟨frame.baselineDefinition, frame.rewrittenDefinition, frame.block, frame.pc,
    rvalsIso_transport_avoiding_right lift frame.values avoids,
    frame.credits.transportRelation creditsAvoid lift⟩

theorem StableFrameRel.transportRelation {limits : Validate.Limits}
    {validation : Validate.Context} {oldRel newRel : Nat → Nat → Prop}
    {removed : Nat} {baseline rewritten : Frame}
    (frame : StableFrameRel limits validation oldRel baseline rewritten)
    (avoids : FrameValuesAvoidLocation removed rewritten)
    (creditsAvoid : FrameCreditsAvoidLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableFrameRel limits validation newRel baseline rewritten := by
  cases frame with
  | rewritten rewrite related =>
      exact .rewritten rewrite
        (related.transportRelation avoids creditsAvoid lift)

theorem StableContinuationIso.transportRelation
    {limits : Validate.Limits} {validation : Validate.Context}
    {oldRel newRel : Nat → Nat → Prop} {removed : Nat}
    {baseline rewritten : Continuation}
    (continuation : StableContinuationIso limits validation oldRel
      baseline rewritten)
    (avoids : ContinuationValuesAvoidLocation removed rewritten)
    (creditsAvoid : ContinuationCreditsAvoidLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableContinuationIso limits validation newRel baseline rewritten := by
  cases continuation with
  | resume frame =>
      exact .resume (frame.transportRelation avoids creditsAvoid lift)
  | applyMore arguments frame =>
      exact .applyMore
        (rvalsIso_transport_avoiding_right lift arguments avoids.1)
        (frame.transportRelation avoids.2 creditsAvoid lift)

/-- An already-related suspended stack remains related after physical reuse
when its rewritten values do not mention the consumed source location. -/
theorem StableStackIso.transportRelation {limits : Validate.Limits}
    {validation : Validate.Context} {oldRel newRel : Nat → Nat → Prop}
    {removed : Nat} {baseline rewritten : List Continuation}
    (stack : StableStackIso limits validation oldRel baseline rewritten)
    (avoids : StackValuesAvoidLocation removed rewritten)
    (creditsAvoid : StackCreditsAvoidLocation removed rewritten)
    (lift : ∀ {baselineLocation rewrittenLocation},
      oldRel baselineLocation rewrittenLocation →
      rewrittenLocation ≠ removed →
      newRel baselineLocation rewrittenLocation) :
    StableStackIso limits validation newRel baseline rewritten := by
  induction stack with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons
        (head.transportRelation avoids.1 creditsAvoid.1 lift)
        (ih avoids.2 creditsAvoid.2)

inductive StableControlIso (limits : Validate.Limits)
    (validation : Validate.Context) (locRel : Nat → Nat → Prop) :
    Control → Control → Prop where
  | running {baselineFrame rewrittenFrame : Frame}
      {baselineStack rewrittenStack : List Continuation}
      (frame : StableFrameRel limits validation locRel
        baselineFrame rewrittenFrame)
      (stack : StableStackIso limits validation locRel
        baselineStack rewrittenStack) :
      StableControlIso limits validation locRel
        (.running baselineFrame baselineStack)
        (.running rewrittenFrame rewrittenStack)
  | halted {baselineValue rewrittenValue : RVal}
      (value : IxIR1.Sim.RValIso locRel baselineValue rewrittenValue) :
      StableControlIso limits validation locRel
        (.halted baselineValue) (.halted rewrittenValue)

/-- Stable heaps are either fixed-address equal in semantic contents or
related by a physical-to-baseline allocation-history bijection.  Historical
dead/dead rows keep stale but unreachable register and credit locations
compositional across ordinary reclamation steps. -/
inductive StableHeapRel (baseline rewritten : Store) :
    (Nat → Nat → Prop) → Prop where
  | contents (same : HeapContentsEq baseline rewritten) :
      StableHeapRel baseline rewritten (fun left right => left = right)
  | isomorphic
      (iso : IxIR1.Sim.HeapHistoryIso rewritten.heap baseline.heap) :
      StableHeapRel baseline rewritten
        (fun baselineLocation rewrittenLocation =>
          iso.locRel rewrittenLocation baselineLocation)

/-- Stable machine states combine heap and control relations.  The rewritten
machine retains at least the baseline heap budget because reset/reuse removes
baseline traversal work; observational counters remain outside this semantic
relation. -/
inductive StableMachineRel (limits : Validate.Limits)
    (validation : Validate.Context) (baseline rewritten : Machine) : Prop where
  | related (locRel : Nat → Nat → Prop)
      (heap : StableHeapRel baseline.store rewritten.store locRel)
      (fuel : baseline.heapFuel ≤ rewritten.heapFuel)
      (control : StableControlIso limits validation locRel
        baseline.control rewritten.control) :
      StableMachineRel limits validation baseline rewritten

/-- Build the stable machine relation from a baseline-to-rewritten allocation
history.  `StableHeapRel` stores the symmetric orientation so its public
location relation continues to run from baseline values to rewritten values. -/
theorem StableMachineRel.history {limits : Validate.Limits}
    {validation : Validate.Context} {baseline rewritten : Machine}
    (heap : IxIR1.Sim.HeapHistoryIso baseline.store.heap
      rewritten.store.heap)
    (fuel : baseline.heapFuel ≤ rewritten.heapFuel)
    (control : StableControlIso limits validation heap.locRel
      baseline.control rewritten.control) :
    StableMachineRel limits validation baseline rewritten := by
  exact .related heap.locRel (.isomorphic heap.symm) fuel control

/-- Inversion of the uniform machine relation at a halted baseline state.
The rewritten state must also be halted, with a related result value and the
same heap/fuel witnesses retained for the runner-level theorem. -/
theorem StableMachineRel.haltedParts {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineStore : Store} {baselineFuel : Nat} {baselineValue : RVal}
    {rewritten : Machine}
    (relation : StableMachineRel limits validation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .halted baselineValue }
      rewritten) :
    ∃ rewrittenStore rewrittenFuel rewrittenValue locRel,
      rewritten =
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .halted rewrittenValue } ∧
        StableHeapRel baselineStore rewrittenStore locRel ∧
        baselineFuel ≤ rewrittenFuel ∧
        IxIR1.Sim.RValIso locRel baselineValue rewrittenValue := by
  cases rewritten with
  | mk rewrittenStore rewrittenFuel rewrittenControl =>
      cases relation with
      | related locRel heap fuel control =>
          cases control with
          | halted value =>
              exact ⟨rewrittenStore, rewrittenFuel, _, locRel, rfl, heap,
                fuel, value⟩

theorem StableFrameIso.entry {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {locRel : Nat → Nat → Prop}
    {baselineValues rewrittenValues : Array RVal}
    (values : IxIR1.Sim.RValsIso locRel
      baselineValues.toList rewrittenValues.toList) :
    StableFrameIso rewrite locRel
      { definition := source, values := baselineValues }
      { definition := rewrite.definition, values := rewrittenValues } := by
  exact ⟨rfl, rfl, rfl, rfl, values, .nil⟩

theorem StableFrameIso.atPosition {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {locRel : Nat → Nat → Prop} {block pc : Nat}
    {baselineValues rewrittenValues : Array RVal}
    {credits : Array (Option Credit)}
    (values : IxIR1.Sim.RValsIso locRel
      baselineValues.toList rewrittenValues.toList)
    (creditsRelated : StableCreditsIso locRel
      credits.toList credits.toList) :
    StableFrameIso rewrite locRel
      { definition := source
        block
        pc
        values := baselineValues
        credits }
      { definition := rewrite.definition
        block
        pc
        values := rewrittenValues
        credits } := by
  exact ⟨rfl, rfl, rfl, rfl, values, creditsRelated⟩

/-- A successful current-block lookup in a related source frame dispatches
through the rewrite's exhaustive unchanged/accepted decision. -/
theorem StableFrameIso.blockCase {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {block : Block}
    (found : baseline.definition.blocks[baseline.block]? = some block) :
    Reuse.FunctionRewrite.BlockCase rewrite baseline.block := by
  have sourceAt : source.blocks[baseline.block]? = some block := by
    rw [← frame.baselineDefinition]
    exact found
  exact rewrite.blockCaseOfLookup sourceAt

/-- Advancing related frames and appending related results preserves the
stable frame relation. -/
theorem StableFrameIso.advancePush {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {baselineValue rewrittenValue : RVal}
    (value : IxIR1.Sim.RValIso locRel baselineValue rewrittenValue) :
    StableFrameIso rewrite locRel
      { baseline with
        pc := baseline.pc + 1
        values := baseline.values.push baselineValue }
      { rewritten with
        pc := rewritten.pc + 1
        values := rewritten.values.push rewrittenValue } := by
  refine ⟨frame.baselineDefinition, frame.rewrittenDefinition,
    frame.block, congrArg (fun pc => pc + 1) frame.pc, ?_, frame.credits⟩
  simpa using rvalsIso_append frame.values value

/-- Appending a result to related value files, without advancing control, is
the frame operation performed when an ordinary return resumes its caller. -/
theorem StableFrameIso.push {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {baselineValue rewrittenValue : RVal}
    (value : IxIR1.Sim.RValIso locRel baselineValue rewrittenValue) :
    StableFrameIso rewrite locRel
      { baseline with values := baseline.values.push baselineValue }
      { rewritten with values := rewritten.values.push rewrittenValue } := by
  refine ⟨frame.baselineDefinition, frame.rewrittenDefinition,
    frame.block, frame.pc, ?_, frame.credits⟩
  simpa using rvalsIso_append frame.values value

theorem StableFrameIso.advance {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten) :
    StableFrameIso rewrite locRel
      { baseline with pc := baseline.pc + 1 }
      { rewritten with pc := rewritten.pc + 1 } := by
  exact ⟨frame.baselineDefinition, frame.rewrittenDefinition,
    frame.block, congrArg (fun pc => pc + 1) frame.pc,
    frame.values, frame.credits⟩

/-- A successful credit lookup in one related frame finds a related credit in
the other frame. -/
theorem StableFrameIso.creditLookup {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {id : CreditId} {baselineCredit : Credit}
    (lookedUp : CreditLookup baseline id baselineCredit) :
    ∃ rewrittenCredit,
      CreditLookup rewritten id rewrittenCredit ∧
        StableCreditIso locRel (some baselineCredit)
          (some rewrittenCredit) := by
  have baselineFound : baseline.credits[id]? =
      some (some baselineCredit) :=
    (CreditTake.of_lookup lookedUp).target_eq.2
  have baselineListFound : baseline.credits.toList[id]? =
      some (some baselineCredit) := by
    simpa using baselineFound
  obtain ⟨rewrittenSlot, rewrittenListFound, related⟩ :=
    frame.credits.get? baselineListFound
  cases rewrittenSlot with
  | none => cases related
  | some rewrittenCredit =>
      have rewrittenFound : rewritten.credits[id]? =
          some (some rewrittenCredit) := by
        simpa using rewrittenListFound
      exact ⟨rewrittenCredit, CreditLookup.of_getElem rewrittenFound, related⟩

theorem StableFrameIso.noLiveCredits {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    (cleared : NoLiveCredits baseline) : NoLiveCredits rewritten := by
  unfold NoLiveCredits at cleared ⊢
  rw [← Array.any_toList] at cleared ⊢
  rw [← frame.credits.any_isSome_eq]
  exact cleared

/-- Consuming corresponding credit slots without changing control preserves
the frame relation and returns related authorities. -/
theorem StableFrameIso.takeIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten baselineNext : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {id : CreditId} {baselineCredit : Credit}
    (taken : CreditTake baseline id baselineNext baselineCredit) :
    ∃ rewrittenNext rewrittenCredit,
      CreditTake rewritten id rewrittenNext rewrittenCredit ∧
        StableCreditIso locRel (some baselineCredit)
          (some rewrittenCredit) ∧
        StableFrameIso rewrite locRel baselineNext rewrittenNext := by
  obtain ⟨baselineNextEq, baselineFound⟩ := taken.target_eq
  have baselineLookup : CreditLookup baseline id baselineCredit :=
    CreditLookup.of_getElem baselineFound
  obtain ⟨rewrittenCredit, rewrittenLookup, creditRelated⟩ :=
    frame.creditLookup baselineLookup
  let rewrittenNext : Frame :=
    { rewritten with
      credits := rewritten.credits.setIfInBounds id none }
  have rewrittenTaken : CreditTake rewritten id rewrittenNext
      rewrittenCredit := CreditTake.of_lookup rewrittenLookup
  refine ⟨rewrittenNext, rewrittenCredit, rewrittenTaken, creditRelated, ?_⟩
  subst baselineNext
  exact ⟨frame.baselineDefinition, frame.rewrittenDefinition, frame.block,
    frame.pc, frame.values, frame.credits.array_set_none id⟩

/-- Batch edge-credit consumption is equivariant under the stable frame
relation.  The transferred credit vector is related pointwise, including
transport of physical reservation locations. -/
theorem StableFrameIso.takeManyIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten baselineNext : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {ids : Array CreditId} {baselineCredits : Array Credit}
    (taken : CreditTakeMany baseline ids baselineNext baselineCredits) :
    ∃ rewrittenNext rewrittenCredits,
      CreditTakeMany rewritten ids rewrittenNext rewrittenCredits ∧
        StableCreditsIso locRel
          (baselineCredits.map some).toList
          (rewrittenCredits.map some).toList ∧
        StableFrameIso rewrite locRel baselineNext rewrittenNext := by
  have follow : ∀ {baselineCurrent : Frame} {remaining : List CreditId}
      {baselineTarget : Frame} {baselineOutput : List Credit},
      CreditTakeSequence baselineCurrent remaining baselineTarget
          baselineOutput →
      ∀ {rewrittenCurrent : Frame},
        StableFrameIso rewrite locRel baselineCurrent rewrittenCurrent →
        ∃ rewrittenTarget rewrittenOutput,
          CreditTakeSequence rewrittenCurrent remaining rewrittenTarget
              rewrittenOutput ∧
            StableCreditsIso locRel (baselineOutput.map some)
              (rewrittenOutput.map some) ∧
            StableFrameIso rewrite locRel baselineTarget rewrittenTarget := by
    intro baselineCurrent remaining baselineTarget baselineOutput sequence
    induction sequence with
    | nil current =>
        intro rewrittenCurrent related
        exact ⟨rewrittenCurrent, [], .nil rewrittenCurrent, .nil, related⟩
    | @cons current middle target id remaining credit credits head tail ih =>
        intro rewrittenCurrent related
        obtain ⟨rewrittenMiddle, rewrittenCredit, rewrittenHead,
            creditRelated, middleRelated⟩ := related.takeIso head
        obtain ⟨rewrittenTarget, rewrittenCredits, rewrittenTail,
            creditsRelated, targetRelated⟩ := ih middleRelated
        exact ⟨rewrittenTarget, rewrittenCredit :: rewrittenCredits,
          .cons rewrittenHead rewrittenTail,
          .cons creditRelated creditsRelated, targetRelated⟩
  obtain ⟨rewrittenNext, rewrittenOutput, rewrittenSequence,
      outputRelated, nextRelated⟩ := follow taken.sequence frame
  let rewrittenCredits : Array Credit := rewrittenOutput.toArray
  have rewrittenTaken : CreditTakeMany rewritten ids rewrittenNext
      rewrittenCredits := by
    simpa [rewrittenCredits] using rewrittenSequence.toMany
  refine ⟨rewrittenNext, rewrittenCredits, rewrittenTaken, ?_, nextRelated⟩
  simpa [rewrittenCredits] using outputRelated

/-- Consuming corresponding credit slots preserves the frame relation and
returns related logical or physical authorities. -/
theorem StableFrameIso.advanceTakeIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten baselineNext : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {id : CreditId} {baselineCredit : Credit}
    (taken : CreditTake { baseline with pc := baseline.pc + 1 }
      id baselineNext baselineCredit) :
    ∃ rewrittenNext rewrittenCredit,
      CreditTake { rewritten with pc := rewritten.pc + 1 }
          id rewrittenNext rewrittenCredit ∧
        StableCreditIso locRel (some baselineCredit)
          (some rewrittenCredit) ∧
        StableFrameIso rewrite locRel baselineNext rewrittenNext := by
  obtain ⟨baselineNextEq, baselineFound⟩ := taken.target_eq
  have baselineLookup : CreditLookup baseline id baselineCredit :=
    CreditLookup.of_getElem baselineFound
  obtain ⟨rewrittenCredit, rewrittenLookup, creditRelated⟩ :=
    frame.creditLookup baselineLookup
  let rewrittenNext : Frame :=
    { rewritten with
      pc := rewritten.pc + 1
      credits := rewritten.credits.setIfInBounds id none }
  have rewrittenTaken : CreditTake
      { rewritten with pc := rewritten.pc + 1 }
      id rewrittenNext rewrittenCredit := by
    exact CreditTake.of_lookup (rewrittenLookup.congrDefinition
      rewritten.definition)
  refine ⟨rewrittenNext, rewrittenCredit, rewrittenTaken, creditRelated, ?_⟩
  subst baselineNext
  exact ⟨frame.baselineDefinition, frame.rewrittenDefinition, frame.block,
    congrArg (fun pc => pc + 1) frame.pc, frame.values,
    frame.credits.array_set_none id⟩

/-- Consuming a constructor appends corresponding field vectors and credits
while advancing otherwise-related frames. -/
theorem StableFrameIso.advanceAppendCreditIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {baselineFields rewrittenFields : Array RVal}
    (fields : IxIR1.Sim.RValsIso locRel
      baselineFields.toList rewrittenFields.toList)
    {baselineCredit rewrittenCredit : Credit}
    (credit : StableCreditIso locRel (some baselineCredit)
      (some rewrittenCredit)) :
    StableFrameIso rewrite locRel
      { baseline with
        pc := baseline.pc + 1
        values := baseline.values ++ baselineFields
        credits := baseline.credits.push (some baselineCredit) }
      { rewritten with
        pc := rewritten.pc + 1
        values := rewritten.values ++ rewrittenFields
        credits := rewritten.credits.push (some rewrittenCredit) } := by
  refine ⟨frame.baselineDefinition, frame.rewrittenDefinition,
    frame.block, congrArg (fun pc => pc + 1) frame.pc, ?_, ?_⟩
  · simpa using rvalsIso_append_pair frame.values fields
  · simpa using frame.credits.append (.cons credit .nil)

/-- Consuming a constructor appends its common field vector and a common
credit while advancing otherwise-related exact-location frames. -/
theorem StableFrameIso.advanceAppendCredit {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten)
    (fields : Array RVal) (credit : Credit) :
    StableFrameIso rewrite (fun left right => left = right)
      { baseline with
        pc := baseline.pc + 1
        values := baseline.values ++ fields
        credits := baseline.credits.push (some credit) }
      { rewritten with
        pc := rewritten.pc + 1
        values := rewritten.values ++ fields
        credits := rewritten.credits.push (some credit) } := by
  refine ⟨frame.baselineDefinition, frame.rewrittenDefinition,
    frame.block, congrArg (fun pc => pc + 1) frame.pc, ?_, ?_⟩
  · simpa using rvalsIso_append_refl frame.values fields.toList
  · simpa using frame.credits.append
      (.cons (StableCreditIso.refl (some credit)) .nil)

/-- Under identity location transport, related frame value files are
literally equal. -/
theorem StableFrameIso.values_eq {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten) :
    baseline.values = rewritten.values := by
  apply Array.toList_inj.mp
  exact frame.values.eq_of_location_eq

/-- Under identity location transport, related credit files are literally
equal. -/
theorem StableFrameIso.credits_eq {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten) :
    baseline.credits = rewritten.credits := by
  apply Array.toList_inj.mp
  exact frame.credits.eq_of_location_eq

theorem StableFrameIso.rewritten_eq {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten) :
    rewritten = { baseline with definition := rewrite.definition } := by
  have definitionEq := frame.rewrittenDefinition
  have blockEq := frame.block
  have pcEq := frame.pc
  have valuesEq := frame.values_eq
  have creditsEq := frame.credits_eq
  cases baseline with
  | mk baselineDefinition baselineBlock baselinePc baselineValues
      baselineCredits =>
      cases rewritten with
      | mk rewrittenDefinition rewrittenBlock rewrittenPc rewrittenValues
          rewrittenCredits =>
          simp only at definitionEq blockEq pcEq valuesEq creditsEq ⊢
          rw [definitionEq, ← blockEq, ← pcEq, ← valuesEq,
            ← creditsEq]

/-- Consuming one credit after advancing control is definition-insensitive.
The rewritten frame consumes the same slot and lands in the canonical frame
obtained by replacing only the source definition. -/
theorem StableFrameIso.advanceTake {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten baselineNext : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten)
    {id : CreditId} {credit : Credit}
    (taken : CreditTake { baseline with pc := baseline.pc + 1 }
      id baselineNext credit) :
    CreditTake { rewritten with pc := rewritten.pc + 1 }
        id { baselineNext with definition := rewrite.definition } credit ∧
      StableFrameIso rewrite (fun left right => left = right)
        baselineNext { baselineNext with definition := rewrite.definition } := by
  have rewrittenTaken := taken.congrDefinition rewrite.definition
  have startEq :
      ({ rewritten with pc := rewritten.pc + 1 } : Frame) =
        { { baseline with pc := baseline.pc + 1 } with
          definition := rewrite.definition } := by
    rw [frame.rewritten_eq]
  rw [startEq]
  refine ⟨rewrittenTaken, ?_⟩
  obtain ⟨nextEq, _⟩ := taken.target_eq
  subst baselineNext
  exact ⟨frame.baselineDefinition, rfl, rfl, rfl,
    IxIR1.Sim.RValsIso.refl baseline.values.toList,
    StableCreditsIso.refl _⟩

/-- A checked edge transfer is equivariant under related value registers and
credit files.  The target-block ABI theorem supplies the only rewrite-specific
fact needed at the destination. -/
theorem StableFrameIso.edgeTransferIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {locRel : Nat → Nat → Prop} {baseline rewritten baselineTarget : Frame}
    (frame : StableFrameIso rewrite locRel baseline rewritten)
    {edge : Edge}
    {baselineImplicit rewrittenImplicit : Array RVal}
    (implicitValues : IxIR1.Sim.RValsIso locRel
      baselineImplicit.toList rewrittenImplicit.toList)
    (transferred : EdgeTransfer baseline edge baselineImplicit
      baselineTarget) :
    ∃ rewrittenTarget,
      EdgeTransfer rewritten edge rewrittenImplicit rewrittenTarget ∧
        StableFrameIso rewrite locRel baselineTarget rewrittenTarget := by
  obtain ⟨baselineValues, baselineCredits, baselineAfter, sourceBlock,
      baselineResolved, baselineTaken, baselineCleared, sourceBlockAt,
      baselineValueArity, baselineCreditArity, baselineTargetEq⟩ :=
    transferred.parts
  obtain ⟨rewrittenValues, rewrittenResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values baselineResolved
  obtain ⟨rewrittenAfter, rewrittenCredits, rewrittenTaken,
      creditsRelated, afterRelated⟩ := frame.takeManyIso baselineTaken
  have rewrittenCleared : NoLiveCredits rewrittenAfter :=
    afterRelated.noLiveCredits baselineCleared
  have sourceBlockAt' : source.blocks[edge.target]? = some sourceBlock := by
    rw [← afterRelated.baselineDefinition]
    exact sourceBlockAt
  obtain ⟨rewrittenBlock, rewrittenBlockAt, valueParams, creditParams⟩ :=
    rewrite.targetBlockAbi sourceBlockAt'
  have rewrittenBlockAt' :
      rewrittenAfter.definition.blocks[edge.target]? =
        some rewrittenBlock := by
    rw [afterRelated.rewrittenDefinition]
    exact rewrittenBlockAt
  have allValuesRelated : IxIR1.Sim.RValsIso locRel
      (baselineImplicit ++ baselineValues).toList
      (rewrittenImplicit ++ rewrittenValues).toList := by
    simpa using rvalsIso_append_pair implicitValues valuesRelated
  have valueSizes : (baselineImplicit ++ baselineValues).size =
      (rewrittenImplicit ++ rewrittenValues).size := by
    simpa using rvalsIso_length_eq allValuesRelated
  have rewrittenValueArity :
      (rewrittenImplicit ++ rewrittenValues).size =
        rewrittenBlock.valueParams.size :=
    valueSizes.symm.trans <| baselineValueArity.trans <|
      (congrArg Array.size valueParams).symm
  have creditSizes : baselineCredits.size = rewrittenCredits.size := by
    simpa using creditsRelated.length_eq
  have rewrittenCreditArity : rewrittenCredits.size =
      rewrittenBlock.creditParams.size :=
    creditSizes.symm.trans <| baselineCreditArity.trans <|
      (congrArg Array.size creditParams).symm
  let rewrittenTarget : Frame :=
    { rewrittenAfter with
      block := edge.target
      pc := 0
      values := rewrittenImplicit ++ rewrittenValues
      credits := rewrittenCredits.map some }
  have rewrittenTransferred : EdgeTransfer rewritten edge rewrittenImplicit
      rewrittenTarget := by
    exact EdgeTransfer.of_parts rewrittenResolved rewrittenTaken
      rewrittenCleared rewrittenBlockAt' rewrittenValueArity
      rewrittenCreditArity
  refine ⟨rewrittenTarget, rewrittenTransferred, ?_⟩
  subst baselineTarget
  exact ⟨afterRelated.baselineDefinition, afterRelated.rewrittenDefinition,
    rfl, rfl, allValuesRelated, creditsRelated⟩

/-- A checked edge out of a stable source frame executes in the rewritten
definition at the same block ID.  `FunctionRewrite.targetBlockAbi` supplies
exactly the target-block compatibility required by `EdgeTransfer`. -/
theorem StableFrameIso.edgeTransfer {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    {rewrite : Reuse.FunctionRewrite limits validation source}
    {baseline rewritten baselineTarget : Frame}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baseline rewritten)
    {edge : Edge} {implicitValues : Array RVal}
    (transferred : EdgeTransfer baseline edge implicitValues baselineTarget) :
    EdgeTransfer rewritten edge implicitValues
        { baselineTarget with definition := rewrite.definition } ∧
      StableFrameIso rewrite (fun left right => left = right)
        baselineTarget
        { baselineTarget with definition := rewrite.definition } := by
  obtain ⟨sourceTargetBlock, sourceTargetAt⟩ := transferred.targetBlock
  have sourceTargetAt' : source.blocks[edge.target]? =
      some sourceTargetBlock := by
    rw [← frame.baselineDefinition]
    exact sourceTargetAt
  obtain ⟨rewrittenTargetBlock, rewrittenTargetAt, valueParams,
      creditParams⟩ := rewrite.targetBlockAbi sourceTargetAt'
  have rewrittenTransfer := transferred.congrDefinition sourceTargetAt
    rewrittenTargetAt valueParams creditParams
  rw [← frame.rewritten_eq] at rewrittenTransfer
  have baselineTargetDefinition : baselineTarget.definition = source :=
    transferred.definition.trans frame.baselineDefinition
  refine ⟨rewrittenTransfer, ?_⟩
  exact ⟨baselineTargetDefinition, rfl, rfl, rfl,
    IxIR1.Sim.RValsIso.refl baselineTarget.values.toList,
    StableCreditsIso.refl baselineTarget.credits.toList⟩

theorem StableFrameRel.entry {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {locRel : Nat → Nat → Prop}
    {baselineValues rewrittenValues : Array RVal}
    (values : IxIR1.Sim.RValsIso locRel
      baselineValues.toList rewrittenValues.toList) :
    StableFrameRel limits validation locRel
      { definition := source, values := baselineValues }
      { definition := rewrite.definition, values := rewrittenValues } :=
  .rewritten rewrite (StableFrameIso.entry rewrite values)

theorem StableFrameRel.push {limits : Validate.Limits}
    {validation : Validate.Context} {locRel : Nat → Nat → Prop}
    {baseline rewritten : Frame}
    (frame : StableFrameRel limits validation locRel baseline rewritten)
    {baselineValue rewrittenValue : RVal}
    (value : IxIR1.Sim.RValIso locRel baselineValue rewrittenValue) :
    StableFrameRel limits validation locRel
      { baseline with values := baseline.values.push baselineValue }
      { rewritten with values := rewritten.values.push rewrittenValue } := by
  cases frame with
  | rewritten rewrite related =>
      exact .rewritten rewrite (related.push value)

/-- Related recursive arguments and an already-related continuation stack
form the stable control state reached by every accepted-site theorem. -/
theorem StableControlIso.recursiveCall {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {locRel : Nat → Nat → Prop}
    {baselineValues rewrittenValues : Array RVal}
    {baselineStack rewrittenStack : List Continuation}
    (values : IxIR1.Sim.RValsIso locRel
      baselineValues.toList rewrittenValues.toList)
    (stack : StableStackIso limits validation locRel
      baselineStack rewrittenStack) :
    StableControlIso limits validation locRel
      (.running { definition := source, values := baselineValues }
        baselineStack)
      (.running { definition := rewrite.definition, values := rewrittenValues }
        rewrittenStack) :=
  .running (StableFrameRel.entry rewrite values) stack

/-- Exact-content recursive-call states inhabit the uniform machine relation
with identity location transport. -/
theorem StableMachineRel.contentsRecursiveCall {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineValues rewrittenValues : Array RVal}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (values : IxIR1.Sim.RValsIso (fun left right => left = right)
      baselineValues.toList rewrittenValues.toList)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack) :
    StableMachineRel limits validation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running
          { definition := source, values := baselineValues } baselineStack }
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := rewrittenValues }
          rewrittenStack } :=
  .related (fun left right => left = right) (.contents heap) fuel
    (StableControlIso.recursiveCall rewrite values stack)

/-- Physical recursive-call states inhabit the same relation using the
target-to-baseline heap bijection produced by reuse soundness. -/
theorem StableMachineRel.isomorphicRecursiveCall
    {limits : Validate.Limits} {validation : Validate.Context}
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineValues rewrittenValues : Array RVal}
    {baselineStack rewrittenStack : List Continuation}
    (iso : IxIR1.Sim.HeapIso rewrittenStore.heap baselineStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (values : IxIR1.Sim.RValsIso
      (fun baselineLocation rewrittenLocation =>
        iso.locRel rewrittenLocation baselineLocation)
      baselineValues.toList rewrittenValues.toList)
    (stack : StableStackIso limits validation
      (fun baselineLocation rewrittenLocation =>
        iso.locRel rewrittenLocation baselineLocation)
      baselineStack rewrittenStack) :
    StableMachineRel limits validation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running
          { definition := source, values := baselineValues } baselineStack }
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := rewrittenValues }
          rewrittenStack } :=
  .related
    (fun baselineLocation rewrittenLocation =>
      iso.locRel rewrittenLocation baselineLocation)
    (.isomorphic (heapIsoToHistory iso))
    fuel
    (StableControlIso.recursiveCall rewrite values stack)

theorem StableContinuationIso.applyMoreOrResume
    {limits : Validate.Limits} {validation : Validate.Context}
    {baseline rewritten : Frame}
    (arguments : Array RVal)
    (frame : StableFrameRel limits validation (fun left right => left = right)
      baseline rewritten) :
    StableContinuationIso limits validation (fun left right => left = right)
      (if arguments.isEmpty then .resume baseline
        else .applyMore arguments baseline)
      (if arguments.isEmpty then .resume rewritten
        else .applyMore arguments rewritten) := by
  by_cases empty : arguments.isEmpty
  · simp only [empty]
    exact .resume frame
  · simp only [empty]
    exact .applyMore (IxIR1.Sim.RValsIso.refl arguments.toList) frame

theorem StableContinuationIso.applyMoreOrResumeIso
    {limits : Validate.Limits} {validation : Validate.Context}
    {locRel : Nat → Nat → Prop}
    {baselineArguments rewrittenArguments : Array RVal}
    {baseline rewritten : Frame}
    (arguments : IxIR1.Sim.RValsIso locRel
      baselineArguments.toList rewrittenArguments.toList)
    (frame : StableFrameRel limits validation locRel baseline rewritten) :
    StableContinuationIso limits validation locRel
      (if baselineArguments.isEmpty then .resume baseline
        else .applyMore baselineArguments baseline)
      (if rewrittenArguments.isEmpty then .resume rewritten
        else .applyMore rewrittenArguments rewritten) := by
  have sizes : baselineArguments.size = rewrittenArguments.size := by
    simpa using rvalsIso_length_eq arguments
  have emptyEq : baselineArguments.isEmpty = rewrittenArguments.isEmpty := by
    simp [Array.isEmpty, sizes]
  by_cases empty : baselineArguments.isEmpty
  · have rewrittenEmpty : rewrittenArguments.isEmpty := by
      simpa [emptyEq] using empty
    simp only [empty, rewrittenEmpty]
    exact .resume frame
  · have rewrittenNonempty : ¬rewrittenArguments.isEmpty := by
      simpa [emptyEq] using empty
    simp only [empty, rewrittenNonempty]
    exact .applyMore arguments frame

/-! ## Accepted macros from exact-content states -/

/-- The logical hot accepted macro is compositional over exact semantic heap
contents and heap-fuel dominance.  In particular, source and target stores
may already differ in every observational counter; only their live node array
must agree. -/
theorem acceptedHotLogicalStableSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel remaining rewrittenFuel : Nat}
    {baselineStack rewrittenStack : List Continuation}
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {ambient : List IxIR1.Sim.Root} {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (sourceBoxAt : baselineStore.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (owned : IxIR1.Sim.RootOwnership baselineStore.heap
      (⟨.shared, .loc location⟩ :: ambient))
    (retained : RetainSharedMany baselineStore fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    let rewrittenAllocation :=
      (logicalHotResetStore rewrittenStore location).allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
    let baselineTarget : Machine :=
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := callValues } baselineStack }
    let rewrittenTarget : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := callValues }
          rewrittenStack }
    Steps baselineContext .logical (2 * site.shape.fieldCount + 3)
        baselineMachine baselineTarget ∧
      Steps rewrittenContext .logical 4 rewrittenMachine rewrittenTarget ∧
      StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨sourceAt, resetAt, hotAt, _coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  have rewrittenBoxAt : rewrittenStore.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩ := by
    rw [← heap.get?_eq location]
    exact sourceBoxAt
  have baselineResetContents : HeapContentsEq baselineReleased
      (logicalHotResetStore baselineStore location) :=
    hotPrefix_contents sourceBoxAt owned retained released
  have resetCongruence : HeapContentsEq
      (logicalHotResetStore baselineStore location)
      (logicalHotResetStore rewrittenStore location) := by
    simpa [logicalHotResetStore] using
      (((heap.tickResetAttempt).kill location).tickHotReset)
  have resetContents : HeapContentsEq baselineReleased
      (logicalHotResetStore rewrittenStore location) :=
    baselineResetContents.trans resetCongruence
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let rewrittenAllocation :=
    (logicalHotResetStore rewrittenStore location).allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
  have allocationContents : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      resetContents.allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have allocationLocation : baselineAllocation.2 =
      rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      resetContents.allocNode_location .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have rewrittenFieldWorlds : FieldWorlds
      (logicalHotResetStore rewrittenStore location)
      allocationSchema newFields :=
    resetContents.fieldWorlds baselineFieldWorlds
  have rewrittenTailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc rewrittenAllocation.2))
      site.shape.tailArguments = .ok callValues := by
    rw [← allocationLocation]
    simpa [baselineAllocation] using tailResolved
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have rewrittenNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have rewrittenArity : callValues.size =
      rewrite.definition.signature.params.size := by
    simpa using arity
  let baselineMachine : Machine :=
    { store := baselineStore
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := parameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store := rewrittenStore
      heapFuel := rewrittenFuel
      control := .running
        { definition := rewrite.definition
          block := index
          values := parameters
          credits := #[] }
        rewrittenStack }
  have baselineExecution : Steps baselineContext .logical
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := callValues } baselineStack } := by
    simpa [baselineMachine, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := .logical)
        (definition := source) (blockId := index)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := remaining)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt (by rfl) parameterCount fieldCount sourceResolved sourceBoxAt
        rfl retained released allocationSchemaAt allocationResolved
        baselineFieldWorlds tailResolved arity sourceNonempty
  have rewrittenExecution : Steps rewrittenContext .logical 4
      rewrittenMachine
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := callValues }
          rewrittenStack } := by
    simpa [rewrittenMachine, rewrittenAllocation, logicalHotResetStore] using
      hotLogicalAcceptedControl site
        (context := rewrittenContext) (definition := rewrite.definition)
        (resetId := index) (hotId := source.blocks.size + helperOffset)
        (coldId := source.blocks.size + helperOffset + 1)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location)
        (box := ⟨.shared, 1,
          .ctorN site.shape.sourceConstructor fields⟩)
        (sourceSchema := sourceSchema) (allocationSchema := allocationSchema)
        (machine := rewrittenMachine) (stack := rewrittenStack)
        resetAt hotAt rewrittenSourceSchemaAt rewrittenAllocationSchemaAt
        sourceLayout allocationLayout (by rfl) parameterCount fieldCount
        sourceResolved (ConstructorView.of_box rewrittenBoxAt rfl rfl) rfl
        allocationResolved
        (by simpa [logicalHotResetStore] using rewrittenFieldWorlds)
        (by simpa [rewrittenAllocation, logicalHotResetStore] using
          rewrittenTailResolved)
        rewrittenArity rewrittenNonempty
  have outputFuel : remaining ≤ rewrittenFuel :=
    Nat.le_trans (releaseShared_remaining_le released) fuel
  exact ⟨by simpa [baselineMachine, baselineAllocation] using baselineExecution,
    by simpa [rewrittenMachine, rewrittenAllocation] using rewrittenExecution,
    StableMachineRel.contentsRecursiveCall rewrite allocationContents outputFuel
      (IxIR1.Sim.RValsIso.refl callValues.toList) stack⟩

/-- The cold accepted macro is likewise compositional over exact semantic
contents.  The baseline retain batch is transported to the rewritten store;
the two parent decrements then agree in contents while the rewritten reset
adds only observational counters. -/
theorem acceptedColdStableSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained : Store}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel rewrittenFuel rc retainedRc : Nat}
    {baselineStack rewrittenStack : List Continuation}
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (sourceBoxAt : baselineStore.get? location = some
      ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩)
    (shared : 1 < rc)
    (retained : RetainSharedMany baselineStore fields baselineRetained)
    (retainedAt : baselineRetained.get? location = some
      ⟨.shared, retainedRc,
        .ctorN site.shape.sourceConstructor fields⟩)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds : FieldWorlds
      (baselineDecrementStore baselineRetained location
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩)
      allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc ((baselineDecrementStore baselineRetained location
          ⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor fields⟩).allocNode .shared
              (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    let baselineReleased := baselineDecrementStore baselineRetained location
      ⟨.shared, retainedRc,
        .ctorN site.shape.sourceConstructor fields⟩
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor newFields)
    ∃ rewrittenRetained,
      let rewrittenReleased := baselineDecrementStore rewrittenRetained location
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩
      let rewrittenReset := rewrittenReleased.tickResetAttempt.tickColdReset
      let rewrittenAllocation := rewrittenReset.allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
      let baselineTarget : Machine :=
        { store := baselineAllocation.1
          heapFuel := fieldFuel
          control := .running
            { definition := source, values := callValues } baselineStack }
      let rewrittenTarget : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { definition := rewrite.definition, values := callValues }
            rewrittenStack }
      RetainSharedMany rewrittenStore fields rewrittenRetained ∧
        Steps baselineContext interpretation
          (2 * site.shape.fieldCount + 3) baselineMachine baselineTarget ∧
        Steps rewrittenContext interpretation 4 rewrittenMachine
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨sourceAt, resetAt, _hotAt, coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  have rewrittenBoxAt : rewrittenStore.get? location = some
      ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩ := by
    rw [← heap.get?_eq location]
    exact sourceBoxAt
  obtain ⟨rewrittenRetained, rewrittenRetainedRun, retainedContents⟩ :=
    heap.retainSharedMany retained
  have rewrittenRetainedAt : rewrittenRetained.get? location = some
      ⟨.shared, retainedRc,
        .ctorN site.shape.sourceConstructor fields⟩ := by
    rw [← retainedContents.get?_eq location]
    exact retainedAt
  obtain ⟨actualRetainedRc, actualRetainedAt, baselineReleasedRun,
      _baselineResetRetained, _baselineHeapEq⟩ :=
    coldPrefix_commutes (heapFuel := fieldFuel) sourceBoxAt shared retained
  have actualBoxEq :
      (⟨.shared, actualRetainedRc,
          .ctorN site.shape.sourceConstructor fields⟩ : IxIR1.NodeBox) =
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩ :=
    Option.some.inj (actualRetainedAt.symm.trans retainedAt)
  have actualRcEq : actualRetainedRc = retainedRc := by
    cases actualBoxEq
    rfl
  subst actualRetainedRc
  obtain ⟨rewrittenActualRc, rewrittenActualAt, _rewrittenReleasedRun,
      rewrittenResetRetained, _rewrittenHeapEq⟩ :=
    coldPrefix_commutes (heapFuel := fieldFuel) rewrittenBoxAt shared
      rewrittenRetainedRun
  have rewrittenBoxEq :
      (⟨.shared, rewrittenActualRc,
          .ctorN site.shape.sourceConstructor fields⟩ : IxIR1.NodeBox) =
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩ :=
    Option.some.inj (rewrittenActualAt.symm.trans rewrittenRetainedAt)
  have rewrittenRcEq : rewrittenActualRc = retainedRc := by
    cases rewrittenBoxEq
    rfl
  subst rewrittenActualRc
  let baselineReleased := baselineDecrementStore baselineRetained location
    ⟨.shared, retainedRc,
      .ctorN site.shape.sourceConstructor fields⟩
  let rewrittenReleased := baselineDecrementStore rewrittenRetained location
    ⟨.shared, retainedRc,
      .ctorN site.shape.sourceConstructor fields⟩
  let rewrittenReset := rewrittenReleased.tickResetAttempt.tickColdReset
  have releasedContents : HeapContentsEq baselineReleased
      rewrittenReleased := by
    simpa [baselineReleased, rewrittenReleased, baselineDecrementStore] using
      (retainedContents.rcTick.setBox location
        { (⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor fields⟩ : IxIR1.NodeBox) with
          rc := retainedRc - 1 })
  have resetContents : HeapContentsEq baselineReleased rewrittenReset := by
    apply releasedContents.trans
    exact ⟨rfl⟩
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  let rewrittenAllocation := rewrittenReset.allocNode .shared
    (.ctorN site.shape.allocationConstructor newFields)
  have allocationContents : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      resetContents.allocNode .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have allocationLocation : baselineAllocation.2 =
      rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      resetContents.allocNode_location .shared
        (.ctorN site.shape.allocationConstructor newFields)
  have rewrittenFieldWorlds :
      FieldWorlds rewrittenReset allocationSchema newFields :=
    resetContents.fieldWorlds baselineFieldWorlds
  have rewrittenTailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc rewrittenAllocation.2))
      site.shape.tailArguments = .ok callValues := by
    rw [← allocationLocation]
    simpa [baselineReleased, baselineAllocation] using tailResolved
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have rewrittenNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have rewrittenArity : callValues.size =
      rewrite.definition.signature.params.size := by
    simpa using arity
  let baselineMachine : Machine :=
    { store := baselineStore
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := parameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store := rewrittenStore
      heapFuel := rewrittenFuel
      control := .running
        { definition := rewrite.definition
          block := index
          values := parameters
          credits := #[] }
        rewrittenStack }
  have baselineExecution : Steps baselineContext interpretation
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := fieldFuel
        control := .running
          { definition := source, values := callValues } baselineStack } := by
    simpa [baselineMachine, baselineReleased, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := interpretation)
        (definition := source) (blockId := index)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := fieldFuel)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt (by rfl) parameterCount fieldCount sourceResolved sourceBoxAt
        rfl retained (by simpa [baselineReleased] using baselineReleasedRun)
        allocationSchemaAt allocationResolved
        (by simpa [baselineReleased] using baselineFieldWorlds)
        (by simpa [baselineReleased, baselineAllocation] using tailResolved)
        arity sourceNonempty
  have rewrittenExecution : Steps rewrittenContext interpretation 4
      rewrittenMachine
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := callValues }
          rewrittenStack } := by
    simpa [rewrittenMachine, rewrittenReset, rewrittenReleased,
      rewrittenAllocation] using
      coldAcceptedControl site
        (context := rewrittenContext) (interpretation := interpretation)
        (definition := rewrite.definition) (resetId := index)
        (hotId := source.blocks.size + helperOffset)
        (coldId := source.blocks.size + helperOffset + 1)
        (parameters := parameters) (fields := fields)
        (newFields := newFields) (callValues := callValues)
        (location := location)
        (box := ⟨.shared, rc,
          .ctorN site.shape.sourceConstructor fields⟩)
        (sourceSchema := sourceSchema) (allocationSchema := allocationSchema)
        (machine := rewrittenMachine) (resetStore := rewrittenReset)
        (stack := rewrittenStack) resetAt coldAt rewrittenSourceSchemaAt
        rewrittenAllocationSchemaAt sourceLayout allocationLayout (by rfl)
        parameterCount fieldCount sourceResolved
        (ConstructorView.of_box rewrittenBoxAt rfl rfl) shared
        (by simpa [rewrittenMachine, coldResetStartStore, rewrittenReset,
          rewrittenReleased] using
          rewrittenResetRetained)
        allocationResolved
        (by simpa [rewrittenReset] using rewrittenFieldWorlds)
        (by simpa [rewrittenAllocation] using rewrittenTailResolved)
        rewrittenArity rewrittenNonempty
  have outputFuel : fieldFuel ≤ rewrittenFuel := by omega
  refine ⟨rewrittenRetained, rewrittenRetainedRun, ?_, ?_, ?_⟩
  · simpa [baselineMachine, baselineReleased, baselineAllocation] using
      baselineExecution
  · simpa [rewrittenMachine, rewrittenReleased, rewrittenReset,
      rewrittenAllocation] using rewrittenExecution
  · exact StableMachineRel.contentsRecursiveCall rewrite allocationContents
      outputFuel (IxIR1.Sim.RValsIso.refl callValues.toList) stack

/-! ## Accepted physical macro from an isomorphic state -/

/-- A physical hot accepted block composes with an existing live-location
bijection. Baseline and rewritten register files, constructor fields, and
continuations may already use different locations. The consumed source pair
is replaced by the reused-target/fresh-baseline pair, all surviving pairs are
preserved, and both executions rejoin at a stable recursive-call state. -/
theorem acceptedHotPhysicalStableSimulationIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    (inputIso : IxIR1.Sim.HeapIso rewrittenStore.heap baselineStore.heap)
    {baselineParameters rewrittenParameters baselineFields rewrittenFields
      baselineNewFields rewrittenNewFields baselineCallValues : Array RVal}
    {baselineLocation rewrittenLocation fieldFuel remaining rewrittenFuel :
      Nat}
    {baselineStack rewrittenStack : List Continuation}
    (parameters : IxIR1.Sim.RValsIso
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      baselineParameters.toList rewrittenParameters.toList)
    (stack : StableStackIso limits validation
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      baselineStack rewrittenStack)
    (stackAvoids : StackValuesAvoidLocation rewrittenLocation rewrittenStack)
    (stackCreditsAvoids :
      StackCreditsAvoidLocation rewrittenLocation rewrittenStack)
    {baselineBefore baselineAfter rewrittenBefore rewrittenAfter :
      List IxIR1.Sim.Root}
    {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (locations : inputIso.locRel rewrittenLocation baselineLocation)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : baselineParameters.size = site.shape.parameterCount)
    (fieldCount : baselineFields.size = site.shape.fieldCount)
    (baselineSourceResolved :
      resolveAtom baselineParameters (.reg site.shape.source) =
        .ok (.loc baselineLocation))
    (rewrittenSourceResolved :
      resolveAtom rewrittenParameters (.reg site.shape.source) =
        .ok (.loc rewrittenLocation))
    (baselineAt : baselineStore.get? baselineLocation = some
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor baselineFields⟩)
    (rewrittenAt : rewrittenStore.get? rewrittenLocation = some
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor rewrittenFields⟩)
    (baselineOwned : IxIR1.Sim.RootOwnership baselineStore.heap
      (⟨.shared, .loc baselineLocation⟩ :: baselineBefore))
    (rewrittenOwned : IxIR1.Sim.RootOwnership rewrittenStore.heap
      (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenBefore))
    (retained : RetainSharedMany baselineStore baselineFields
      baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc baselineLocation) = .ok (baselineReleased, remaining))
    (baselinePartition :
      (IxIR1.Sim.rootsFor .shared baselineFields.toList ++
          baselineBefore).Perm
        (IxIR1.Sim.rootsFor .shared baselineNewFields.toList ++
          baselineAfter))
    (rewrittenPartition :
      (IxIR1.Sim.rootsFor .shared rewrittenFields.toList ++
          rewrittenBefore).Perm
        (IxIR1.Sim.rootsFor .shared rewrittenNewFields.toList ++
          rewrittenAfter))
    (mapped : MappedValuesInRoots site.shape
      (baselinePrefixValues rewrittenParameters rewrittenFields)
      (IxIR1.Sim.rootsFor .shared rewrittenNewFields.toList ++
        rewrittenAfter))
    (baselineAllocationResolved : resolveAtoms
      (baselinePrefixValues baselineParameters baselineFields)
      site.shape.allocationArguments = .ok baselineNewFields)
    (rewrittenAllocationResolved : resolveAtoms
      (baselinePrefixValues rewrittenParameters rewrittenFields)
      site.shape.allocationArguments = .ok rewrittenNewFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema baselineNewFields)
    (rewrittenFieldWorlds : FieldWorlds
      (physicalHotResetStore rewrittenStore rewrittenLocation)
      allocationSchema rewrittenNewFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues baselineParameters baselineFields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor baselineNewFields)).2))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := baselineParameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := rewrittenParameters
            credits := #[] }
          rewrittenStack }
    let baselineAllocation := baselineReleased.allocNode .shared
      (.ctorN site.shape.allocationConstructor baselineNewFields)
    ∃ physical : Store,
      ∃ outputIso : IxIR1.Sim.HeapIso physical.heap
          baselineAllocation.1.heap,
      ∃ physicalCallValues : Array RVal,
      physicalHotReuseStore rewrittenStore rewrittenLocation
          (.ctorN site.shape.allocationConstructor rewrittenNewFields)
          allocationSchema.fields.size = .ok physical ∧
      IxIR1.Sim.RootOwnership physical.heap
          (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenAfter) ∧
      IxIR1.Sim.RootOwnership baselineAllocation.1.heap
          (⟨.shared, .loc baselineAllocation.2⟩ :: baselineAfter) ∧
      outputIso.locRel rewrittenLocation baselineAllocation.2 ∧
      (∀ {rewrittenCandidate baselineCandidate : Nat},
        inputIso.locRel rewrittenCandidate baselineCandidate →
        rewrittenCandidate ≠ rewrittenLocation →
        outputIso.locRel rewrittenCandidate baselineCandidate) ∧
      Steps baselineContext .physical (2 * site.shape.fieldCount + 3)
        baselineMachine
        { store := baselineAllocation.1
          heapFuel := remaining
          control := .running
            { definition := source, values := baselineCallValues }
            baselineStack } ∧
      Steps rewrittenContext .physical 4 rewrittenMachine
        { store := physical
          heapFuel := rewrittenFuel
          control := .running
            { definition := rewrite.definition, values := physicalCallValues }
            rewrittenStack } ∧
      IxIR1.Sim.RValsIso
          (fun baselineCandidate rewrittenCandidate =>
            outputIso.locRel rewrittenCandidate baselineCandidate)
          baselineCallValues.toList physicalCallValues.toList ∧
      StableStackIso limits validation
          (fun baselineCandidate rewrittenCandidate =>
            outputIso.locRel rewrittenCandidate baselineCandidate)
          baselineStack rewrittenStack ∧
      StableMachineRel limits validation
        { store := baselineAllocation.1
          heapFuel := remaining
          control := .running
            { definition := source, values := baselineCallValues }
            baselineStack }
        { store := physical
          heapFuel := rewrittenFuel
          control := .running
            { definition := rewrite.definition, values := physicalCallValues }
            rewrittenStack } := by
  dsimp only
  obtain ⟨sourceAt, resetAt, hotAt, _coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, sourceSchemaFields, allocationSchemaFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  have uniformAllocationFields : allocationSchema.fields =
      Array.replicate site.shape.fieldCount .shared :=
    allocationSchemaFields.trans sourceSchemaFields
  have parameterSizes : baselineParameters.size = rewrittenParameters.size := by
    simpa using rvalsIso_length_eq parameters
  have rewrittenParameterCount : rewrittenParameters.size =
      site.shape.parameterCount := parameterSizes.symm.trans parameterCount
  obtain ⟨leftBox, rightBox, leftLive, rightLive, boxesRelated⟩ :=
    inputIso.related_live locations
  have leftBoxEq : leftBox =
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor rewrittenFields⟩ :=
    Option.some.inj (leftLive.symm.trans rewrittenAt)
  have rightBoxEq : rightBox =
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor baselineFields⟩ :=
    Option.some.inj (rightLive.symm.trans baselineAt)
  subst leftBox
  subst rightBox
  have rewrittenToBaselineFields : IxIR1.Sim.RValsIso inputIso.locRel
      rewrittenFields.toList baselineFields.toList := by
    cases boxesRelated.node with
    | ctor related => exact related
  have fieldsRelated : IxIR1.Sim.RValsIso
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      baselineFields.toList rewrittenFields.toList :=
    rvalsIso_symm rewrittenToBaselineFields
  have fieldSizes : baselineFields.size = rewrittenFields.size := by
    simpa using rvalsIso_length_eq fieldsRelated
  have rewrittenFieldCount : rewrittenFields.size = site.shape.fieldCount :=
    fieldSizes.symm.trans fieldCount
  have prefixRelated : IxIR1.Sim.RValsIso
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      (baselinePrefixValues baselineParameters baselineFields).toList
      (baselinePrefixValues rewrittenParameters rewrittenFields).toList := by
    simpa [baselinePrefixValues] using
      rvalsIso_append_pair
        (rvalsIso_append_pair parameters fieldsRelated) fieldsRelated
  obtain ⟨actualRewrittenNewFields, actualRewrittenResolved,
      newFieldsRelated⟩ :=
    resolveAtoms_iso prefixRelated baselineAllocationResolved
  have actualNewFieldsEq : actualRewrittenNewFields = rewrittenNewFields :=
    Except.ok.inj
      (actualRewrittenResolved.symm.trans rewrittenAllocationResolved)
  subst actualRewrittenNewFields
  have prefixContents : HeapContentsEq baselineReleased
      (logicalHotResetStore baselineStore baselineLocation) :=
    hotPrefix_contents baselineAt baselineOwned retained released
  have baselineMissing : baselineReleased.get? baselineLocation = none := by
    rw [prefixContents.get?_eq baselineLocation]
    change (logicalHotResetStore baselineStore baselineLocation).heap.get?
      baselineLocation = none
    rw [logicalHotResetStore_heap]
    exact IxIR1.Sim.get?_kill_same baselineAt
  have baselineNewFieldsAvoid : ∀ value ∈ baselineNewFields.toList,
      value ≠ .loc baselineLocation :=
    FieldWorlds.avoidsMissing uniformAllocationFields baselineFieldWorlds
      baselineMissing
  have rewrittenNewFieldsAvoid : ∀ value ∈ rewrittenNewFields.toList,
      value ≠ .loc rewrittenLocation :=
    rvalsIso_right_avoids_of_left inputIso locations newFieldsRelated
      baselineNewFieldsAvoid
  have restrictedNewFields : IxIR1.Sim.RValsIso
      (fun rewrittenCandidate baselineCandidate =>
        inputIso.locRel rewrittenCandidate baselineCandidate ∧
          rewrittenCandidate ≠ rewrittenLocation)
      rewrittenNewFields.toList baselineNewFields.toList :=
    rvalsIso_restrict_left (rvalsIso_symm newFieldsRelated)
      rewrittenNewFieldsAvoid
  let baselineAllocation := baselineReleased.allocNode .shared
    (.ctorN site.shape.allocationConstructor baselineNewFields)
  obtain ⟨physical, reused, outputIso, physicalOwned,
      baselineAllocationOwned, outputResult, outputExtends⟩ :=
    hotPrefixReuse_sound_under_iso
      (baselineStore := baselineStore) (rewrittenStore := rewrittenStore)
      (baselineRetained := baselineRetained)
      (baselineReleased := baselineReleased)
      (baselineLocation := baselineLocation)
      (rewrittenLocation := rewrittenLocation)
      (oldCid := site.shape.sourceConstructor)
      (newCid := site.shape.allocationConstructor)
      (baselineFields := baselineFields) (rewrittenFields := rewrittenFields)
      (baselineNewFields := baselineNewFields)
      (rewrittenNewFields := rewrittenNewFields) (fieldFuel := fieldFuel)
      (remaining := remaining) (baselineBefore := baselineBefore)
      (baselineAfter := baselineAfter) (rewrittenBefore := rewrittenBefore)
      (rewrittenAfter := rewrittenAfter) allocationSchema.fields.size inputIso
      locations baselineAt rewrittenAt baselineOwned rewrittenOwned retained
      released baselinePartition rewrittenPartition restrictedNewFields
  obtain ⟨physicalAgain, reusedAgain, physicalHeap⟩ :=
    physicalHotReuseStore_ok
      (.ctorN site.shape.allocationConstructor rewrittenNewFields)
      allocationSchema.fields.size rewrittenAt
  have physicalEq : physicalAgain = physical :=
    Except.ok.inj (reusedAgain.symm.trans reused)
  subst physicalAgain
  have physicalAt : physical.get? rewrittenLocation = some
      ⟨.shared, 1,
        .ctorN site.shape.allocationConstructor rewrittenNewFields⟩ := by
    change physical.heap.get? rewrittenLocation = _
    rw [physicalHeap]
    exact IxIR1.Sim.get?_reuseSharedNodeStore_same rewrittenAt
  let outputRel : Nat → Nat → Prop :=
    fun baselineCandidate rewrittenCandidate =>
      outputIso.locRel rewrittenCandidate baselineCandidate
  have translatedPrefix : TranslatedValuesIso site.shape outputRel
      (baselinePrefixValues baselineParameters baselineFields)
      (helperEntryValues site.shape.source rewrittenParameters
        rewrittenFields) := by
    intro sourceId targetId baselineValue relevant translated baselineValueAt
    obtain ⟨rewrittenValue, rewrittenValueAt, inputValueRelated⟩ :=
      rvalsIso_array_getElem? prefixRelated baselineValueAt
    have helperValueAt :=
      valuesRel_helperEntry rewrittenParameterCount rewrittenFieldCount
        site.fits.sourceBound sourceId targetId translated
    rw [rewrittenValueAt] at helperValueAt
    have supported :=
      mapped sourceId targetId rewrittenValue relevant translated
        rewrittenValueAt
    have rewrittenValueAvoid : rewrittenValue ≠ .loc rewrittenLocation :=
      by
        cases rewrittenValue with
        | loc location =>
            obtain ⟨world, member⟩ := supported
            rcases List.mem_append.mp member with fieldMember | survivorMember
            · rw [IxIR1.Sim.rootsFor, List.mem_map] at fieldMember
              obtain ⟨field, fieldMem, rootEq⟩ := fieldMember
              have fieldEq : field = .loc location :=
                congrArg IxIR1.Sim.Root.value rootEq
              subst field
              exact rewrittenNewFieldsAvoid _ fieldMem
            · exact physicalOwned.sole_root_ne physicalAt survivorMember
        | lit literal => intro impossible; cases impossible
        | erased => intro impossible; cases impossible
    have outputValueRelated : IxIR1.Sim.RValIso outputRel
        baselineValue rewrittenValue := by
      cases inputValueRelated with
      | loc locationRelated =>
          apply IxIR1.Sim.RValIso.loc
          apply outputExtends locationRelated
          intro same
          apply rewrittenValueAvoid
          cases same
          rfl
      | lit => exact .lit
      | erased => exact .erased
    exact ⟨rewrittenValue, helperValueAt.symm, outputValueRelated⟩
  have baselinePrefixSize :
      (baselinePrefixValues baselineParameters baselineFields).size =
        site.shape.parameterCount + 2 * site.shape.fieldCount := by
    simp [baselinePrefixValues, parameterCount, fieldCount, Nat.two_mul]
  have rewrittenHelperSize :
      (helperEntryValues site.shape.source rewrittenParameters
        rewrittenFields).size =
        site.shape.fieldCount + (site.shape.parameterCount - 1) := by
    simp [helperEntryValues, List.length_eraseIdx, rewrittenParameterCount,
      rewrittenFieldCount, site.fits.sourceBound]
  have translatedAfterAllocation : TranslatedValuesIso site.shape outputRel
      ((baselinePrefixValues baselineParameters baselineFields).push
        (.loc baselineAllocation.2))
      ((helperEntryValues site.shape.source rewrittenParameters
        rewrittenFields).push (.loc rewrittenLocation)) :=
    TranslatedValuesIso.pushResult translatedPrefix (.loc outputResult)
      baselinePrefixSize rewrittenHelperSize site.fits.sourceBound
  have sourceNonempty : source.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem sourceAt
  have rewrittenNonempty : rewrite.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem resetAt
  have rewrittenArity : baselineCallValues.size =
      rewrite.definition.signature.params.size := by
    simpa using arity
  let baselineMachine : Machine :=
    { store := baselineStore
      heapFuel := fieldFuel + 1
      control := .running
        { definition := source
          block := index
          values := baselineParameters
          credits := #[] }
        baselineStack }
  let rewrittenMachine : Machine :=
    { store := rewrittenStore
      heapFuel := rewrittenFuel
      control := .running
        { definition := rewrite.definition
          block := index
          values := rewrittenParameters
          credits := #[] }
        rewrittenStack }
  have baselineExecution : Steps baselineContext .physical
      (2 * site.shape.fieldCount + 3) baselineMachine
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := baselineCallValues }
          baselineStack } := by
    simpa [baselineMachine, baselineAllocation] using
      baselineAcceptedControl site
        (context := baselineContext) (interpretation := .physical)
        (definition := source) (blockId := index)
        (parameters := baselineParameters) (fields := baselineFields)
        (newFields := baselineNewFields) (callValues := baselineCallValues)
        (location := baselineLocation) (machine := baselineMachine)
        (retainedStore := baselineRetained)
        (releasedStore := baselineReleased) (remaining := remaining)
        (allocationSchema := allocationSchema) (stack := baselineStack)
        sourceAt (by rfl) parameterCount fieldCount baselineSourceResolved
        baselineAt rfl retained released allocationSchemaAt
        baselineAllocationResolved baselineFieldWorlds tailResolved arity
        sourceNonempty
  obtain ⟨physicalCallValues, rewrittenExecution, callsRelated⟩ :=
    hotPhysicalAcceptedControlTranslated site
      (context := rewrittenContext) (definition := rewrite.definition)
      (resetId := index) (hotId := source.blocks.size + helperOffset)
      (coldId := source.blocks.size + helperOffset + 1)
      (parameters := rewrittenParameters) (fields := rewrittenFields)
      (newFields := rewrittenNewFields)
      (baselineTailValues :=
        (baselinePrefixValues baselineParameters baselineFields).push
          (.loc baselineAllocation.2))
      (baselineCallValues := baselineCallValues)
      (location := rewrittenLocation)
      (box := ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor rewrittenFields⟩)
      (sourceSchema := sourceSchema) (allocationSchema := allocationSchema)
      (machine := rewrittenMachine) (stack := rewrittenStack)
      (store := physical) (locRel := outputRel) resetAt hotAt
      rewrittenSourceSchemaAt rewrittenAllocationSchemaAt sourceLayout
      allocationLayout (by rfl) rewrittenParameterCount rewrittenFieldCount
      rewrittenSourceResolved
      (ConstructorView.of_box rewrittenAt rfl rfl) rfl
      rewrittenAllocationResolved
      (by simpa [physicalHotResetStore] using rewrittenFieldWorlds)
      (by simpa [physicalHotReuseStore, physicalHotResetStore] using reused)
      translatedAfterAllocation
      (by simpa [baselineAllocation] using tailResolved) rewrittenArity
      rewrittenNonempty
  have outputStack : StableStackIso limits validation outputRel
      baselineStack rewrittenStack :=
    stack.transportRelation stackAvoids stackCreditsAvoids (by
      intro baselineCandidate rewrittenCandidate related different
      exact outputExtends related different)
  have outputFuel : remaining ≤ rewrittenFuel :=
    Nat.le_trans (releaseShared_remaining_le released) fuel
  have relatedMachine : StableMachineRel limits validation
      { store := baselineAllocation.1
        heapFuel := remaining
        control := .running
          { definition := source, values := baselineCallValues }
          baselineStack }
      { store := physical
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition, values := physicalCallValues }
          rewrittenStack } :=
    StableMachineRel.isomorphicRecursiveCall rewrite outputIso outputFuel
      callsRelated outputStack
  exact ⟨physical, outputIso, physicalCallValues, reused, physicalOwned,
    by simpa [baselineAllocation] using baselineAllocationOwned,
    by simpa [baselineAllocation] using outputResult,
    outputExtends,
    by simpa [baselineMachine, baselineAllocation] using baselineExecution,
    by simpa [rewrittenMachine] using rewrittenExecution,
    callsRelated, outputStack, relatedMachine⟩

/-! ## Allocation-history unchanged execution -/

/-- An unchanged `move` is equivariant under an arbitrary allocation-history
isomorphism.  Unlike the exact-content theorem below, the target register may
contain a numerically different but related location. -/
theorem unchangedMoveStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] = .move atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push baselineValue }
          baselineStack }
    ∃ rewrittenValue,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push rewrittenValue }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .move atom := by
    simpa only [← frame.pc] using instruction
  refine ⟨rewrittenValue,
    Step.move rfl sourceAt pc instruction resolved,
    Step.move rfl targetAt targetPc targetInstruction targetResolved, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite (frame.advancePush valueRelated)) stack)

/-- Constructor projection follows corresponding locations and fields through
an allocation-history isomorphism. -/
theorem unchangedFetchStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {cid : CtorId} {field : Nat}
    {baselineLocation : Nat} {baselineBox : IxIR1.NodeBox}
    {baselineFields : Array RVal} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .fetch atom cid field)
    (resolved : resolveAtom baselineFrame.values atom =
      .ok (.loc baselineLocation))
    (boxAt : baselineStore.get? baselineLocation = some baselineBox)
    (node : baselineBox.node = .ctorN cid baselineFields)
    (fieldAt : baselineFields[field]? = some baselineValue) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push baselineValue }
          baselineStack }
    ∃ rewrittenValue,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push rewrittenValue }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ :=
        heap.boxes locations (by
          change baselineStore.heap.get? baselineLocation = some baselineBox
          exact boxAt)
      have nodes : IxIR1.Sim.NodeIso heap.locRel
          (.ctorN cid baselineFields) rewrittenBox.node := by
        simpa only [← node] using boxes.node
      obtain ⟨rewrittenFields, rewrittenNode, fieldsRelated⟩ :=
        nodeIso_ctor_left nodes
      obtain ⟨rewrittenValue, rewrittenFieldAt, valueRelated⟩ :=
        rvalsIso_array_getElem? fieldsRelated fieldAt
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .fetch atom cid field := by
        simpa only [← frame.pc] using instruction
      refine ⟨rewrittenValue,
        Step.fetch rfl sourceAt pc instruction resolved boxAt node fieldAt,
        Step.fetch rfl targetAt targetPc targetInstruction targetResolved
          ?_ rewrittenNode rewrittenFieldAt, ?_⟩
      · change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
        exact rewrittenAt
      · exact StableMachineRel.history heap fuel
          (.running
            (.rewritten rewrite (frame.advancePush valueRelated)) stack)

/-- Shallow unique reclamation kills corresponding live locations while
retaining their pair as a dead/dead history row.  This is the first unchanged
case that cannot be expressed compositionally with a live-only `HeapIso`. -/
theorem unchangedFreeUniqueStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {cid : CtorId}
    {baselineLocation : Nat} {baselineBox : IxIR1.NodeBox}
    {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .freeUnique atom cid)
    (resolved : resolveAtom baselineFrame.values atom =
      .ok (.loc baselineLocation))
    (boxAt : baselineStore.get? baselineLocation = some baselineBox)
    (unique : baselineBox.world = .unique)
    (node : baselineBox.node = .ctorN cid baselineFields)
    (scalarFields : baselineFields.all RVal.isScalar = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        store := baselineStore.kill baselineLocation
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    ∃ rewrittenLocation,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          store := rewrittenStore.kill rewrittenLocation
          control := .running
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ :=
        heap.boxes locations (by
          change baselineStore.heap.get? baselineLocation = some baselineBox
          exact boxAt)
      have nodes : IxIR1.Sim.NodeIso heap.locRel
          (.ctorN cid baselineFields) rewrittenBox.node := by
        simpa only [← node] using boxes.node
      obtain ⟨rewrittenFields, rewrittenNode, fieldsRelated⟩ :=
        nodeIso_ctor_left nodes
      have fieldsEq : baselineFields = rewrittenFields := by
        apply Array.toList_inj.mp
        apply fieldsRelated.eq_of_allScalar
        rw [Array.all_toList]
        exact scalarFields
      have rewrittenScalar : rewrittenFields.all RVal.isScalar = true := by
        rw [← fieldsEq]
        exact scalarFields
      have rewrittenUnique : rewrittenBox.world = .unique :=
        boxes.world.symm.trans unique
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .freeUnique atom cid := by
        simpa only [← frame.pc] using instruction
      let outputHeap : IxIR1.Sim.HeapHistoryIso
          (baselineStore.kill baselineLocation).heap
          (rewrittenStore.kill rewrittenLocation).heap :=
        heap.kill locations (by
          change baselineStore.heap.get? baselineLocation = some baselineBox
          exact boxAt) rewrittenAt
      refine ⟨rewrittenLocation,
        Step.freeUnique rfl sourceAt pc instruction resolved boxAt unique node
          scalarFields,
        Step.freeUnique rfl targetAt targetPc targetInstruction targetResolved
          ?_ rewrittenUnique rewrittenNode rewrittenScalar, ?_⟩
      · change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
        exact rewrittenAt
      · have outputFrame : StableFrameIso rewrite outputHeap.locRel
            { baselineFrame with pc := baselineFrame.pc + 1 }
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 } := by
          change StableFrameIso rewrite heap.locRel _ _
          exact frame.advance
        have outputStack : StableStackIso limits validation outputHeap.locRel
            baselineStack rewrittenStack := by
          change StableStackIso limits validation heap.locRel _ _
          exact stack
        exact StableMachineRel.history outputHeap fuel
          (.running (.rewritten rewrite outputFrame) outputStack)

/-- Fresh constructor allocation extends the history with the two fresh
locations and transports the schema check across related field vectors. -/
theorem unchangedAllocStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema}
    {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .alloc world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (fieldWorlds : FieldWorlds baselineStore schema baselineValues) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation :=
      baselineStore.allocNode world (.ctorN cid baselineValues)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ rewrittenValues,
      let rewrittenAllocation :=
        rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
      let rewrittenNext : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .alloc world cid arguments := by
    simpa only [← frame.pc] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetFieldWorlds : FieldWorlds rewrittenStore schema rewrittenValues :=
    fieldWorlds.transport (heapHistoryIso_fieldValuesWorldEq heap valuesRelated)
  let baselineAllocation :=
    baselineStore.allocNode world (.ctorN cid baselineValues)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap :=
    heap.alloc (.ctor valuesRelated)
  have oldExtends : ∀ {baselineLocation rewrittenLocation},
      heap.locRel baselineLocation rewrittenLocation →
      outputHeap.locRel baselineLocation rewrittenLocation := by
    intro baselineLocation rewrittenLocation related
    exact .inr related
  have resultRelated : IxIR1.Sim.RValIso outputHeap.locRel
      (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) := by
    exact .loc (.inl ⟨rfl, rfl⟩)
  have outputFrame := (frame.mono oldExtends).advancePush resultRelated
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenValues,
    by simpa [baselineAllocation] using
      (Step.alloc (context := baselineContext)
        (interpretation := interpretation)
        (machine :=
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack })
        rfl sourceAt pc instruction schemaAt resolved fieldWorlds),
    by simpa [rewrittenAllocation] using
      (Step.alloc (context := rewrittenContext)
        (interpretation := interpretation)
        (machine :=
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack })
        rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetFieldWorlds), ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- An absent `allocWith` credit is consumed at corresponding frame slots;
both executions then make related fresh allocations. -/
theorem unchangedAllocWithAbsentStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (fieldWorlds : FieldWorlds baselineStore schema baselineValues)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (absent : credit.presence = .absent) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation :=
      baselineStore.allocNode world (.ctorN cid baselineValues)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ (rewrittenValues : Array RVal) (rewrittenTaken : Frame),
      let rewrittenAllocation :=
        rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
      let rewrittenNext : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenTaken with
              values := rewrittenTaken.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← frame.pc] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetFieldWorlds : FieldWorlds rewrittenStore schema rewrittenValues :=
    fieldWorlds.transport (heapHistoryIso_fieldValuesWorldEq heap valuesRelated)
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨layoutRelated, targetAbsent⟩ :=
    creditRelated.absent_parts absent
  have targetLayout : rewrittenCredit.layout = schema.layout :=
    layoutRelated.symm.trans layout
  let baselineAllocation :=
    baselineStore.allocNode world (.ctorN cid baselineValues)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap :=
    heap.alloc (.ctor valuesRelated)
  have oldExtends : ∀ {baselineLocation rewrittenLocation},
      heap.locRel baselineLocation rewrittenLocation →
      outputHeap.locRel baselineLocation rewrittenLocation := by
    intro baselineLocation rewrittenLocation related
    exact .inr related
  have resultRelated : IxIR1.Sim.RValIso outputHeap.locRel
      (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) :=
    .loc (.inl ⟨rfl, rfl⟩)
  have outputFrame := (takenFrame.mono oldExtends).push resultRelated
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenValues, rewrittenTaken,
    by simpa [baselineAllocation] using
      (Step.allocWithAbsent (context := baselineContext)
        (interpretation := interpretation)
        (machine :=
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack })
        rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
          absent),
    by simpa [rewrittenAllocation] using
      (Step.allocWithAbsent (context := rewrittenContext)
        (interpretation := interpretation)
        (machine :=
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack })
        rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
          targetFieldWorlds targetTaken targetLayout targetAbsent), ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- A logical `allocWith` credit is consumed at corresponding frame slots;
both executions then make related fresh allocations. -/
theorem unchangedAllocWithLogicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (fieldWorlds : FieldWorlds baselineStore schema baselineValues)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present none) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation :=
      baselineStore.allocNode world (.ctorN cid baselineValues)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ (rewrittenValues : Array RVal) (rewrittenTaken : Frame),
      let rewrittenAllocation :=
        rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
      let rewrittenNext : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenTaken with
              values := rewrittenTaken.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      Step baselineContext .logical baselineMachine baselineNext ∧
        Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← frame.pc] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetFieldWorlds : FieldWorlds rewrittenStore schema rewrittenValues :=
    fieldWorlds.transport (heapHistoryIso_fieldValuesWorldEq heap valuesRelated)
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨layoutRelated, targetPresent⟩ :=
    creditRelated.logical_parts present
  have targetLayout : rewrittenCredit.layout = schema.layout :=
    layoutRelated.symm.trans layout
  let baselineAllocation :=
    baselineStore.allocNode world (.ctorN cid baselineValues)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid rewrittenValues)
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap :=
    heap.alloc (.ctor valuesRelated)
  have oldExtends : ∀ {baselineLocation rewrittenLocation},
      heap.locRel baselineLocation rewrittenLocation →
      outputHeap.locRel baselineLocation rewrittenLocation := by
    intro baselineLocation rewrittenLocation related
    exact .inr related
  have resultRelated : IxIR1.Sim.RValIso outputHeap.locRel
      (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) :=
    .loc (.inl ⟨rfl, rfl⟩)
  have outputFrame := (takenFrame.mono oldExtends).push resultRelated
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenValues, rewrittenTaken,
    by simpa [baselineAllocation] using
      (Step.allocWithLogical (context := baselineContext)
        (machine :=
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack })
        rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
          present),
    by simpa [rewrittenAllocation] using
      (Step.allocWithLogical (context := rewrittenContext)
        (machine :=
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack })
        rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
          targetFieldWorlds targetTaken targetLayout targetPresent), ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- Physical `allocWith` consumes corresponding (possibly differently
numbered) reservations and revives their history row with related nodes. -/
theorem unchangedAllocWithPhysicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {baselineValues : Array RVal}
    {baselineLocation : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (fieldWorlds : FieldWorlds baselineStore schema baselineValues)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present (some baselineLocation))
    (reused : baselineStore.reuseReservation baselineLocation world
      (.ctorN cid baselineValues) schema.fields.size = .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc baselineLocation) }
          baselineStack }
    ∃ (rewrittenValues : Array RVal) (rewrittenTaken : Frame)
        (rewrittenLocation : Nat) (rewrittenOut : Store),
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenTaken with
              values := rewrittenTaken.values.push (.loc rewrittenLocation) }
            rewrittenStack }
      rewrittenStore.reuseReservation rewrittenLocation world
          (.ctorN cid rewrittenValues) schema.fields.size = .ok rewrittenOut ∧
        Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← frame.pc] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetFieldWorlds : FieldWorlds rewrittenStore schema rewrittenValues :=
    fieldWorlds.transport (heapHistoryIso_fieldValuesWorldEq heap valuesRelated)
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨rewrittenLocation, layoutRelated, targetPresent, locations⟩ :=
    creditRelated.physical_parts present
  have targetLayout : rewrittenCredit.layout = schema.layout :=
    layoutRelated.symm.trans layout
  obtain ⟨rewrittenOut, outputHeap, targetReused, outputRelation⟩ :=
    reuseReservation_historyIso heap locations (.ctor valuesRelated) reused
  have outputFrame : StableFrameIso rewrite outputHeap.locRel
      { baselineTaken with
        values := baselineTaken.values.push (.loc baselineLocation) }
      { rewrittenTaken with
        values := rewrittenTaken.values.push (.loc rewrittenLocation) } := by
    rw [outputRelation]
    exact takenFrame.push (.loc locations)
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenValues, rewrittenTaken, rewrittenLocation, rewrittenOut,
    targetReused,
    Step.allocWithPhysical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
        present reused,
    Step.allocWithPhysical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetFieldWorlds targetTaken targetLayout targetPresent targetReused,
    ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- Discarding related absent credits consumes corresponding frame slots and
leaves the allocation history unchanged. -/
theorem unchangedDiscardCreditAbsentStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (absent : credit.presence = .absent) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    ∃ rewrittenTaken : Frame,
      let rewrittenNext : Machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenTaken rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← frame.pc] using instruction
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨_, targetAbsent⟩ := creditRelated.absent_parts absent
  refine ⟨rewrittenTaken,
    Step.discardCreditAbsent
      (context := baselineContext) (interpretation := interpretation)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken absent,
    Step.discardCreditAbsent
      (context := rewrittenContext) (interpretation := interpretation)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken targetAbsent, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite takenFrame) stack)

/-- Discarding related logical credits consumes corresponding frame slots and
leaves the allocation history unchanged. -/
theorem unchangedDiscardCreditLogicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (present : credit.presence = .present none) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    ∃ rewrittenTaken : Frame,
      let rewrittenNext : Machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenTaken rewrittenStack }
      Step baselineContext .logical baselineMachine baselineNext ∧
        Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← frame.pc] using instruction
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨_, targetPresent⟩ := creditRelated.logical_parts present
  refine ⟨rewrittenTaken,
    Step.discardCreditLogical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken present,
    Step.discardCreditLogical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken targetPresent, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite takenFrame) stack)

/-- Discarding related physical credits releases corresponding reserved
slots, which may have different concrete addresses. -/
theorem unchangedDiscardCreditPhysicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {baselineLocation : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (present : credit.presence = .present (some baselineLocation))
    (released : baselineStore.releaseReservation baselineLocation =
      .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    ∃ (rewrittenTaken : Frame) (rewrittenLocation : Nat)
        (rewrittenOut : Store),
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running rewrittenTaken rewrittenStack }
      rewrittenStore.releaseReservation rewrittenLocation = .ok rewrittenOut ∧
        Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← frame.pc] using instruction
  obtain ⟨rewrittenTaken, rewrittenCredit, targetTaken, creditRelated,
      takenFrame⟩ := frame.advanceTakeIso taken
  obtain ⟨rewrittenLocation, _, targetPresent, locations⟩ :=
    creditRelated.physical_parts present
  obtain ⟨rewrittenOut, outputHeap, targetReleased, outputRelation⟩ :=
    releaseReservation_historyIso heap locations released
  have outputFrame : StableFrameIso rewrite outputHeap.locRel
      baselineTaken rewrittenTaken := by
    rw [outputRelation]
    exact takenFrame
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenTaken, rewrittenLocation, rewrittenOut, targetReleased,
    Step.discardCreditPhysical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken present released,
    Step.discardCreditPhysical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken targetPresent
        targetReleased, ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- Logical unique extraction follows a related constructor, kills both
locations, and appends related fields plus matching logical credits. -/
theorem unchangedTakeUniqueLogicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {baselineLocation : Nat}
    {baselineBox : IxIR1.NodeBox} {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .takeUnique target cid)
    (schemaAt : baselineContext.schemas .unique cid = some schema)
    (resolved : resolveAtom baselineFrame.values target =
      .ok (.loc baselineLocation))
    (viewed : ConstructorView baselineStore baselineLocation .unique cid
      baselineBox baselineFields)
    (unitRC : baselineBox.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present none }
    let baselineNext : Machine :=
      { store := baselineStore.kill baselineLocation
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    ∃ (rewrittenLocation : Nat) (rewrittenFields : Array RVal),
      let rewrittenNext : Machine :=
        { store := rewrittenStore.kill rewrittenLocation
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ rewrittenFields
              credits := rewrittenFrame.credits.push (some credit) }
            rewrittenStack }
      Step baselineContext .logical baselineMachine baselineNext ∧
        Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨baselineAt, baselineWorld, baselineNode⟩ := viewed.parts
      obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ :=
        heap.boxes locations (by
          change baselineStore.heap.get? baselineLocation = some baselineBox
          exact baselineAt)
      have nodes : IxIR1.Sim.NodeIso heap.locRel
          (.ctorN cid baselineFields) rewrittenBox.node := by
        simpa only [← baselineNode] using boxes.node
      obtain ⟨rewrittenFields, rewrittenNode, fieldsRelated⟩ :=
        nodeIso_ctor_left nodes
      have rewrittenWorld : rewrittenBox.world = .unique :=
        boxes.world.symm.trans baselineWorld
      have rewrittenRc : rewrittenBox.rc = 1 :=
        boxes.rc.symm.trans unitRC
      have targetViewed : ConstructorView rewrittenStore rewrittenLocation
          .unique cid rewrittenBox rewrittenFields := by
        apply ConstructorView.of_box
        · change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
          exact rewrittenAt
        · exact rewrittenWorld
        · exact rewrittenNode
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .takeUnique target cid := by
        simpa only [← frame.pc] using instruction
      have targetSchemaAt : rewrittenContext.schemas .unique cid =
          some schema := by
        rw [← schemas]
        exact schemaAt
      let outputHeap := heap.kill locations (by
        change baselineStore.heap.get? baselineLocation = some baselineBox
        exact baselineAt) rewrittenAt
      have outputFrame : StableFrameIso rewrite outputHeap.locRel
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push
              (some { layout := schema.layout, presence := .present none }) }
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ rewrittenFields
            credits := rewrittenFrame.credits.push
              (some { layout := schema.layout, presence := .present none }) } := by
        change StableFrameIso rewrite heap.locRel _ _
        exact frame.advanceAppendCreditIso fieldsRelated
          (.logical schema.layout)
      have outputStack : StableStackIso limits validation outputHeap.locRel
          baselineStack rewrittenStack := by
        change StableStackIso limits validation heap.locRel _ _
        exact stack
      refine ⟨rewrittenLocation, rewrittenFields,
        Step.takeUniqueLogical
          (context := baselineContext)
          (machine :=
            { store := baselineStore
              heapFuel := baselineFuel
              control := .running baselineFrame baselineStack })
          rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
        Step.takeUniqueLogical
          (context := rewrittenContext)
          (machine :=
            { store := rewrittenStore
              heapFuel := rewrittenFuel
              control := .running rewrittenFrame rewrittenStack })
          rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
            targetViewed rewrittenRc, ?_⟩
      exact StableMachineRel.history outputHeap fuel
        (.running (.rewritten rewrite outputFrame) outputStack)

/-- Physical unique extraction reserves corresponding constructor slots and
records location-related physical credits. -/
theorem unchangedTakeUniquePhysicalStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {baselineLocation : Nat}
    {baselineBox : IxIR1.NodeBox} {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .takeUnique target cid)
    (schemaAt : baselineContext.schemas .unique cid = some schema)
    (resolved : resolveAtom baselineFrame.values target =
      .ok (.loc baselineLocation))
    (viewed : ConstructorView baselineStore baselineLocation .unique cid
      baselineBox baselineFields)
    (unitRC : baselineBox.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineCredit : Credit :=
      { layout := schema.layout,
        presence := .present (some baselineLocation) }
    let baselineNext : Machine :=
      { store := baselineStore.reserve baselineLocation
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push (some baselineCredit) }
          baselineStack }
    ∃ (rewrittenLocation : Nat) (rewrittenFields : Array RVal),
      let rewrittenCredit : Credit :=
        { layout := schema.layout,
          presence := .present (some rewrittenLocation) }
      let rewrittenNext : Machine :=
        { store := rewrittenStore.reserve rewrittenLocation
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ rewrittenFields
              credits := rewrittenFrame.credits.push (some rewrittenCredit) }
            rewrittenStack }
      Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨baselineAt, baselineWorld, baselineNode⟩ := viewed.parts
      obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ :=
        heap.boxes locations (by
          change baselineStore.heap.get? baselineLocation = some baselineBox
          exact baselineAt)
      have nodes : IxIR1.Sim.NodeIso heap.locRel
          (.ctorN cid baselineFields) rewrittenBox.node := by
        simpa only [← baselineNode] using boxes.node
      obtain ⟨rewrittenFields, rewrittenNode, fieldsRelated⟩ :=
        nodeIso_ctor_left nodes
      have rewrittenWorld : rewrittenBox.world = .unique :=
        boxes.world.symm.trans baselineWorld
      have rewrittenRc : rewrittenBox.rc = 1 :=
        boxes.rc.symm.trans unitRC
      have targetViewed : ConstructorView rewrittenStore rewrittenLocation
          .unique cid rewrittenBox rewrittenFields := by
        apply ConstructorView.of_box
        · change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
          exact rewrittenAt
        · exact rewrittenWorld
        · exact rewrittenNode
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .takeUnique target cid := by
        simpa only [← frame.pc] using instruction
      have targetSchemaAt : rewrittenContext.schemas .unique cid =
          some schema := by
        rw [← schemas]
        exact schemaAt
      let outputHeap := reserve_historyIso heap locations (by
        change baselineStore.heap.get? baselineLocation = some baselineBox
        exact baselineAt) rewrittenAt
      have outputFrame : StableFrameIso rewrite outputHeap.locRel
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push
              (some { layout := schema.layout, presence :=
                .present (some baselineLocation) }) }
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ rewrittenFields
            credits := rewrittenFrame.credits.push
              (some { layout := schema.layout, presence :=
                .present (some rewrittenLocation) }) } := by
        change StableFrameIso rewrite heap.locRel _ _
        exact frame.advanceAppendCreditIso fieldsRelated
          (.physical locations)
      have outputStack : StableStackIso limits validation outputHeap.locRel
          baselineStack rewrittenStack := by
        change StableStackIso limits validation heap.locRel _ _
        exact stack
      refine ⟨rewrittenLocation, rewrittenFields,
        Step.takeUniquePhysical
          (context := baselineContext)
          (machine :=
            { store := baselineStore
              heapFuel := baselineFuel
              control := .running baselineFrame baselineStack })
          rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
        Step.takeUniquePhysical
          (context := rewrittenContext)
          (machine :=
            { store := rewrittenStore
              heapFuel := rewrittenFuel
              control := .running rewrittenFrame rewrittenStack })
          rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
            targetViewed rewrittenRc, ?_⟩
      exact StableMachineRel.history outputHeap fuel
        (.running (.rewritten rewrite outputFrame) outputStack)

/-- A logical hot shared reset follows a related unit-refcount constructor,
kills both locations, and records matching logical credits. -/
theorem unchangedResetSharedLogicalHotStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {baselineLocation : Nat}
    {baselineBox : IxIR1.NodeBox} {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target =
      .ok (.loc baselineLocation))
    (viewed : ConstructorView baselineStore baselineLocation .shared cid
      baselineBox baselineFields)
    (unitRC : baselineBox.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present none }
    let baselineNext : Machine :=
      { store := ((baselineStore.tickResetAttempt).kill
          baselineLocation).tickHotReset
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    ∃ (rewrittenLocation : Nat) (rewrittenFields : Array RVal),
      let rewrittenNext : Machine :=
        { store := ((rewrittenStore.tickResetAttempt).kill
            rewrittenLocation).tickHotReset
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ rewrittenFields
              credits := rewrittenFrame.credits.push (some credit) }
            rewrittenStack }
      Step baselineContext .logical baselineMachine baselineNext ∧
        Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, rewrittenFields, rewrittenAt, targetViewed,
          boxes, fieldsRelated⟩ :=
        constructorView_historyIso heap locations viewed
      obtain ⟨baselineAt, _, _⟩ := viewed.parts
      have rewrittenRc : rewrittenBox.rc = 1 :=
        boxes.rc.symm.trans unitRC
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .resetShared target cid := by
        simpa only [← frame.pc] using instruction
      have targetSchemaAt : rewrittenContext.schemas .shared cid =
          some schema := by
        rw [← schemas]
        exact schemaAt
      let killed := heap.kill locations (by
        change baselineStore.heap.get? baselineLocation = some baselineBox
        exact baselineAt) (by
          change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
          exact rewrittenAt)
      let outputHeap : IxIR1.Sim.HeapHistoryIso
          (((baselineStore.tickResetAttempt).kill
            baselineLocation).tickHotReset).heap
          (((rewrittenStore.tickResetAttempt).kill
            rewrittenLocation).tickHotReset).heap := by
        simpa [Eval.Store.tickResetAttempt, Eval.Store.tickHotReset] using killed
      have outputFrame : StableFrameIso rewrite outputHeap.locRel
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push
              (some { layout := schema.layout, presence := .present none }) }
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ rewrittenFields
            credits := rewrittenFrame.credits.push
              (some { layout := schema.layout, presence := .present none }) } := by
        change StableFrameIso rewrite heap.locRel _ _
        exact frame.advanceAppendCreditIso fieldsRelated
          (.logical schema.layout)
      have outputStack : StableStackIso limits validation outputHeap.locRel
          baselineStack rewrittenStack := by
        change StableStackIso limits validation heap.locRel _ _
        exact stack
      refine ⟨rewrittenLocation, rewrittenFields,
        Step.resetSharedLogicalHot
          (context := baselineContext)
          (machine :=
            { store := baselineStore
              heapFuel := baselineFuel
              control := .running baselineFrame baselineStack })
          rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
        Step.resetSharedLogicalHot
          (context := rewrittenContext)
          (machine :=
            { store := rewrittenStore
              heapFuel := rewrittenFuel
              control := .running rewrittenFrame rewrittenStack })
          rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
            targetViewed rewrittenRc, ?_⟩
      exact StableMachineRel.history outputHeap fuel
        (.running (.rewritten rewrite outputFrame) outputStack)

/-- A physical hot shared reset reserves corresponding constructor slots and
records location-related physical credits. -/
theorem unchangedResetSharedPhysicalHotStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {baselineLocation : Nat}
    {baselineBox : IxIR1.NodeBox} {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target =
      .ok (.loc baselineLocation))
    (viewed : ConstructorView baselineStore baselineLocation .shared cid
      baselineBox baselineFields)
    (unitRC : baselineBox.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineCredit : Credit :=
      { layout := schema.layout,
        presence := .present (some baselineLocation) }
    let baselineNext : Machine :=
      { store := ((baselineStore.tickResetAttempt).reserve
          baselineLocation).tickHotReset
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push (some baselineCredit) }
          baselineStack }
    ∃ (rewrittenLocation : Nat) (rewrittenFields : Array RVal),
      let rewrittenCredit : Credit :=
        { layout := schema.layout,
          presence := .present (some rewrittenLocation) }
      let rewrittenNext : Machine :=
        { store := ((rewrittenStore.tickResetAttempt).reserve
            rewrittenLocation).tickHotReset
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ rewrittenFields
              credits := rewrittenFrame.credits.push (some rewrittenCredit) }
            rewrittenStack }
      Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, rewrittenFields, rewrittenAt, targetViewed,
          boxes, fieldsRelated⟩ :=
        constructorView_historyIso heap locations viewed
      obtain ⟨baselineAt, _, _⟩ := viewed.parts
      have rewrittenRc : rewrittenBox.rc = 1 :=
        boxes.rc.symm.trans unitRC
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .resetShared target cid := by
        simpa only [← frame.pc] using instruction
      have targetSchemaAt : rewrittenContext.schemas .shared cid =
          some schema := by
        rw [← schemas]
        exact schemaAt
      let reserved := reserve_historyIso
        (left := baselineStore.tickResetAttempt)
        (right := rewrittenStore.tickResetAttempt) heap locations (by
          simpa [Eval.Store.tickResetAttempt, Eval.Store.get?] using
            baselineAt) (by
          simpa [Eval.Store.tickResetAttempt, Eval.Store.get?] using
            rewrittenAt)
      let outputHeap : IxIR1.Sim.HeapHistoryIso
          (((baselineStore.tickResetAttempt).reserve
            baselineLocation).tickHotReset).heap
          (((rewrittenStore.tickResetAttempt).reserve
            rewrittenLocation).tickHotReset).heap := by
        simpa [Eval.Store.tickHotReset] using reserved
      have outputFrame : StableFrameIso rewrite outputHeap.locRel
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push
              (some { layout := schema.layout, presence :=
                .present (some baselineLocation) }) }
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ rewrittenFields
            credits := rewrittenFrame.credits.push
              (some { layout := schema.layout, presence :=
                .present (some rewrittenLocation) }) } := by
        change StableFrameIso rewrite heap.locRel _ _
        exact frame.advanceAppendCreditIso fieldsRelated
          (.physical locations)
      have outputStack : StableStackIso limits validation outputHeap.locRel
          baselineStack rewrittenStack := by
        change StableStackIso limits validation heap.locRel _ _
        exact stack
      refine ⟨rewrittenLocation, rewrittenFields,
        Step.resetSharedPhysicalHot
          (context := baselineContext)
          (machine :=
            { store := baselineStore
              heapFuel := baselineFuel
              control := .running baselineFrame baselineStack })
          rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
        Step.resetSharedPhysicalHot
          (context := rewrittenContext)
          (machine :=
            { store := rewrittenStore
              heapFuel := rewrittenFuel
              control := .running rewrittenFrame rewrittenStack })
          rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
            targetViewed rewrittenRc, ?_⟩
      exact StableMachineRel.history outputHeap fuel
        (.running (.rewritten rewrite outputFrame) outputStack)

/-- A cold shared reset transports the parent decrement and field-retain loop
through allocation history, then appends related fields and absent credits. -/
theorem unchangedResetSharedColdStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {baselineLocation : Nat}
    {baselineBox : IxIR1.NodeBox} {baselineFields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target =
      .ok (.loc baselineLocation))
    (viewed : ConstructorView baselineStore baselineLocation .shared cid
      baselineBox baselineFields)
    (shared : 1 < baselineBox.rc)
    (retained : RetainSharedMany
      ((((baselineStore.tickResetAttempt).setBox baselineLocation
        { baselineBox with rc := baselineBox.rc - 1 }).rcTick).tickColdReset)
      baselineFields baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .absent }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    ∃ (rewrittenFields : Array RVal) (rewrittenOut : Store),
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ rewrittenFields
              credits := rewrittenFrame.credits.push (some credit) }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenResolved, targetResolved, resolvedRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases resolvedRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, rewrittenFields, rewrittenAt, targetViewed,
          boxes, fieldsRelated⟩ :=
        constructorView_historyIso heap locations viewed
      obtain ⟨baselineAt, _, _⟩ := viewed.parts
      have rewrittenShared : 1 < rewrittenBox.rc := by
        rw [← boxes.rc]
        exact shared
      have targetPc : rewrittenFrame.pc < block.instructions.size := by
        rw [← frame.pc]
        exact pc
      have targetInstruction : block.instructions[rewrittenFrame.pc] =
          .resetShared target cid := by
        simpa only [← frame.pc] using instruction
      have targetSchemaAt : rewrittenContext.schemas .shared cid =
          some schema := by
        rw [← schemas]
        exact schemaAt
      let updated := heap.setBox locations (by
        change baselineStore.heap.get? baselineLocation = some baselineBox
        exact baselineAt) (by
          change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
          exact rewrittenAt)
        (show IxIR1.Sim.NodeBoxIso heap.locRel
            { baselineBox with rc := baselineBox.rc - 1 }
            { rewrittenBox with rc := rewrittenBox.rc - 1 } from
          ⟨boxes.world, congrArg (fun rc => rc - 1) boxes.rc, boxes.node⟩)
      let beforeHistory : IxIR1.Sim.HeapHistoryIso
          ((((baselineStore.tickResetAttempt).setBox baselineLocation
            { baselineBox with rc := baselineBox.rc - 1 }).rcTick).tickColdReset).heap
          ((((rewrittenStore.tickResetAttempt).setBox rewrittenLocation
            { rewrittenBox with rc := rewrittenBox.rc - 1 }).rcTick).tickColdReset).heap := by
        simpa [Eval.Store.tickResetAttempt, Eval.Store.tickColdReset] using
          updated.rcTick
      have retainedFields : IxIR1.Sim.RValsIso beforeHistory.locRel
          baselineFields.toList rewrittenFields.toList := by
        change IxIR1.Sim.RValsIso heap.locRel _ _
        exact fieldsRelated
      obtain ⟨rewrittenOut, outputHeap, targetRetained, outputRelation⟩ :=
        retainSharedMany_historyIso beforeHistory retainedFields retained
      have outputFrame : StableFrameIso rewrite outputHeap.locRel
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ baselineFields
            credits := baselineFrame.credits.push
              (some { layout := schema.layout, presence := .absent }) }
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ rewrittenFields
            credits := rewrittenFrame.credits.push
              (some { layout := schema.layout, presence := .absent }) } := by
        rw [outputRelation]
        change StableFrameIso rewrite heap.locRel _ _
        exact frame.advanceAppendCreditIso fieldsRelated
          (.absent schema.layout)
      have outputStack : StableStackIso limits validation outputHeap.locRel
          baselineStack rewrittenStack := by
        rw [outputRelation]
        change StableStackIso limits validation beforeHistory.locRel _ _
        change StableStackIso limits validation heap.locRel _ _
        exact stack
      refine ⟨rewrittenFields, rewrittenOut,
        Step.resetSharedCold
          (context := baselineContext) (interpretation := interpretation)
          (machine :=
            { store := baselineStore
              heapFuel := baselineFuel
              control := .running baselineFrame baselineStack })
          rfl sourceAt pc instruction schemaAt resolved viewed shared retained,
        Step.resetSharedCold
          (context := rewrittenContext) (interpretation := interpretation)
          (machine :=
            { store := rewrittenStore
              heapFuel := rewrittenFuel
              control := .running rewrittenFrame rewrittenStack })
          rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
            targetViewed rewrittenShared targetRetained, ?_⟩
      exact StableMachineRel.history outputHeap fuel
        (.running (.rewritten rewrite outputFrame) outputStack)

/-- Shared retain updates corresponding refcounts and appends the related
resolved values to the two frames. -/
theorem unchangedRetainSharedStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .retainShared atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (retained : retainShared baselineStore baselineValue = .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push baselineValue }
          baselineStack }
    ∃ rewrittenValue rewrittenOut,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push rewrittenValue }
            rewrittenStack }
      retainShared rewrittenStore rewrittenValue = .ok rewrittenOut ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  obtain ⟨rewrittenOut, outputHeap, targetRetained, outputRelation⟩ :=
    retainShared_historyIso heap valueRelated retained
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .retainShared atom := by
    simpa only [← frame.pc] using instruction
  have outputFrame : StableFrameIso rewrite outputHeap.locRel
      { baselineFrame with
        pc := baselineFrame.pc + 1
        values := baselineFrame.values.push baselineValue }
      { rewrittenFrame with
        pc := rewrittenFrame.pc + 1
        values := rewrittenFrame.values.push rewrittenValue } := by
    rw [outputRelation]
    exact frame.advancePush valueRelated
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenValue, rewrittenOut, targetRetained,
    Step.retainShared rfl sourceAt pc instruction resolved retained,
    Step.retainShared rfl targetAt targetPc targetInstruction targetResolved
      targetRetained, ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- Deep shared release follows related child graphs, retains reclaimed pairs
as history rows, and preserves the rewritten machine's fuel advantage. -/
theorem unchangedReleaseSharedStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .releaseShared atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (released : releaseShared baselineFuel baselineStore baselineValue =
      .ok (baselineOut, baselineRemaining)) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    ∃ rewrittenValue rewrittenOut rewrittenRemaining,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
            rewrittenStack }
      releaseShared rewrittenFuel rewrittenStore rewrittenValue =
          .ok (rewrittenOut, rewrittenRemaining) ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  obtain ⟨rewrittenOut, rewrittenRemaining, outputHeap, targetReleased,
      outputFuel, outputRelation⟩ :=
    releaseSharedWork_historyIso heap fuel
      (.cons valueRelated .nil) (by
        unfold releaseShared at released
        exact released)
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .releaseShared atom := by
    simpa only [← frame.pc] using instruction
  have outputFrame : StableFrameIso rewrite outputHeap.locRel
      { baselineFrame with pc := baselineFrame.pc + 1 }
      { rewrittenFrame with pc := rewrittenFrame.pc + 1 } := by
    rw [outputRelation]
    exact frame.advance
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenValue, rewrittenOut, rewrittenRemaining,
    by simpa [releaseShared] using targetReleased,
    Step.releaseShared rfl sourceAt pc instruction resolved released,
    Step.releaseShared rfl targetAt targetPc targetInstruction targetResolved
      (by simpa [releaseShared] using targetReleased), ?_⟩
  exact StableMachineRel.history outputHeap outputFuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- Deep unique destruction follows corresponding constructor trees and
preserves the rewritten traversal-fuel advantage. -/
theorem unchangedDropUniqueStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .dropUnique atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (dropped : dropUnique baselineFuel baselineStore baselineValue =
      .ok (baselineOut, baselineRemaining)) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    ∃ rewrittenValue rewrittenOut rewrittenRemaining,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
            rewrittenStack }
      dropUnique rewrittenFuel rewrittenStore rewrittenValue =
          .ok (rewrittenOut, rewrittenRemaining) ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  obtain ⟨rewrittenOut, rewrittenRemaining, outputHeap, targetDropped,
      outputFuel, outputRelation⟩ :=
    dropUniqueWork_historyIso heap fuel (.cons valueRelated .nil) (by
      unfold dropUnique at dropped
      exact dropped)
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .dropUnique atom := by
    simpa only [← frame.pc] using instruction
  have outputFrame : StableFrameIso rewrite outputHeap.locRel
      { baselineFrame with pc := baselineFrame.pc + 1 }
      { rewrittenFrame with pc := rewrittenFrame.pc + 1 } := by
    rw [outputRelation]
    exact frame.advance
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenValue, rewrittenOut, rewrittenRemaining,
    by simpa [dropUnique] using targetDropped,
    Step.dropUnique rfl sourceAt pc instruction resolved dropped,
    Step.dropUnique rfl targetAt targetPc targetInstruction targetResolved
      (by simpa [dropUnique] using targetDropped), ?_⟩
  exact StableMachineRel.history outputHeap outputFuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- A recursive call resolves related argument vectors, enters the two
versions of the current function, and suspends related callers. -/
theorem unchangedCallSelfStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {arguments : Array Atom}
    {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .callSelf arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (arity : baselineValues.size =
      baselineFrame.definition.signature.params.size)
    (nonempty : baselineFrame.definition.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := baselineFrame.definition, values := baselineValues }
          (.resume { baselineFrame with pc := baselineFrame.pc + 1 } ::
            baselineStack) }
    ∃ rewrittenValues,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { definition := rewrittenFrame.definition,
              values := rewrittenValues }
            (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 } ::
              rewrittenStack) }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .callSelf arguments := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have sourceArity : baselineValues.size = source.signature.params.size := by
    simpa [frame.baselineDefinition] using arity
  have targetArity : rewrittenValues.size =
      rewrittenFrame.definition.signature.params.size := by
    rw [← sizeEq, frame.rewrittenDefinition, rewrite.definition_signature]
    exact sourceArity
  have targetNonempty : rewrittenFrame.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem targetAt
  refine ⟨rewrittenValues,
    Step.callSelfCleared rfl sourceAt pc instruction noCredits resolved arity
      nonempty,
    Step.callSelfCleared rfl targetAt targetPc targetInstruction
      targetNoCredits targetResolved targetArity targetNonempty, ?_⟩
  have callee : StableFrameRel limits validation heap.locRel
      { definition := baselineFrame.definition, values := baselineValues }
      { definition := rewrittenFrame.definition, values := rewrittenValues } := by
    rw [frame.baselineDefinition, frame.rewrittenDefinition]
    exact StableFrameRel.entry rewrite valuesRelated
  have resume : StableContinuationIso limits validation heap.locRel
      (.resume { baselineFrame with pc := baselineFrame.pc + 1 })
      (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 }) :=
    .resume (.rewritten rewrite frame.advance)
  exact StableMachineRel.history heap fuel
    (.running callee (.cons resume stack))

/-- A direct call follows the declaration rewrite selected at the same
address and enters related callee argument vectors. -/
theorem unchangedCallFnStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .call address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (arity : baselineValues.size = calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := calleeSource, values := baselineValues }
          (.resume { baselineFrame with pc := baselineFrame.pc + 1 } ::
            baselineStack) }
    ∃ rewrittenValues,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { definition := calleeRewrite.definition,
              values := rewrittenValues }
            (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 } ::
              rewrittenStack) }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .call address arguments := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have targetArity : rewrittenValues.size =
      calleeRewrite.definition.signature.params.size := by
    rw [← sizeEq, calleeRewrite.definition_signature]
    exact arity
  have targetNonempty : calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  refine ⟨rewrittenValues,
    Step.callFnCleared rfl sourceAt pc instruction noCredits resolved
      baselineDeclaration arity nonempty,
    Step.callFnCleared rfl targetAt targetPc targetInstruction
      targetNoCredits targetResolved rewrittenDeclaration targetArity
      targetNonempty, ?_⟩
  have callee : StableFrameRel limits validation heap.locRel
      { definition := calleeSource, values := baselineValues }
      { definition := calleeRewrite.definition, values := rewrittenValues } :=
    StableFrameRel.entry calleeRewrite valuesRelated
  have resume : StableContinuationIso limits validation heap.locRel
      (.resume { baselineFrame with pc := baselineFrame.pc + 1 })
      (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 }) :=
    .resume (.rewritten callerRewrite frame.advance)
  exact StableMachineRel.history heap fuel
    (.running callee (.cons resume stack))

/-- Partial application of a function resolves related captures and extends
the allocation history with related PAP nodes. -/
theorem unchangedPappFnStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .papp address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (papSafe : calleeSource.signature.papSafe = true)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (under : baselineValues.size < calleeSource.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode .shared
      (.papN address calleeSource.signature.params.size baselineValues)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ rewrittenValues : Array RVal,
      let rewrittenAllocation := rewrittenStore.allocNode .shared
        (.papN address calleeSource.signature.params.size rewrittenValues)
      let rewrittenNext : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .papp address arguments := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have targetPapSafe : calleeRewrite.definition.signature.papSafe = true := by
    simpa using papSafe
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have targetUnder :
      rewrittenValues.size < calleeRewrite.definition.signature.params.size := by
    rw [← sizeEq, calleeRewrite.definition_signature]
    exact under
  let baselineAllocation := baselineStore.allocNode .shared
    (.papN address calleeSource.signature.params.size baselineValues)
  let rewrittenAllocation := rewrittenStore.allocNode .shared
    (.papN address calleeSource.signature.params.size rewrittenValues)
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap := heap.alloc (.pap valuesRelated)
  have oldExtends : ∀ {baselineLocation rewrittenLocation},
      heap.locRel baselineLocation rewrittenLocation →
      outputHeap.locRel baselineLocation rewrittenLocation := by
    intro baselineLocation rewrittenLocation related
    exact .inr related
  have resultRelated : IxIR1.Sim.RValIso outputHeap.locRel
      (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) :=
    .loc (.inl ⟨rfl, rfl⟩)
  have outputFrame := (frame.mono oldExtends).advancePush resultRelated
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenValues,
    by simpa [baselineAllocation] using
      (Step.pappFnCleared
        (context := baselineContext) (interpretation := interpretation)
        (machine :=
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack })
        rfl sourceAt pc instruction noCredits baselineDeclaration papSafe
          resolved under),
    by simpa [rewrittenAllocation, calleeRewrite.definition_signature] using
      (Step.pappFnCleared
        (context := rewrittenContext) (interpretation := interpretation)
        (machine :=
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack })
        rfl targetAt targetPc targetInstruction targetNoCredits
          rewrittenDeclaration targetPapSafe targetResolved targetUnder), ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten callerRewrite outputFrame) outputStack)

/-- Partial application of an extern resolves related captures and extends
the allocation history with related PAP nodes. -/
theorem unchangedPappExternStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {baselineValues : Array RVal} {arity : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .papp address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern arity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern arity))
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (under : baselineValues.size < arity) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode .shared
      (.papN address arity baselineValues)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ rewrittenValues : Array RVal,
      let rewrittenAllocation := rewrittenStore.allocNode .shared
        (.papN address arity rewrittenValues)
      let rewrittenNext : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .papp address arguments := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have targetUnder : rewrittenValues.size < arity := by
    rw [← sizeEq]
    exact under
  let baselineAllocation := baselineStore.allocNode .shared
    (.papN address arity baselineValues)
  let rewrittenAllocation := rewrittenStore.allocNode .shared
    (.papN address arity rewrittenValues)
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap := heap.alloc (.pap valuesRelated)
  have oldExtends : ∀ {baselineLocation rewrittenLocation},
      heap.locRel baselineLocation rewrittenLocation →
      outputHeap.locRel baselineLocation rewrittenLocation := by
    intro baselineLocation rewrittenLocation related
    exact .inr related
  have resultRelated : IxIR1.Sim.RValIso outputHeap.locRel
      (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) :=
    .loc (.inl ⟨rfl, rfl⟩)
  have outputFrame := (frame.mono oldExtends).advancePush resultRelated
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenValues,
    by simpa [baselineAllocation] using
      (Step.pappExternCleared
        (context := baselineContext) (interpretation := interpretation)
        (machine :=
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack })
        rfl sourceAt pc instruction noCredits baselineDeclaration resolved
          under),
    by simpa [rewrittenAllocation] using
      (Step.pappExternCleared
        (context := rewrittenContext) (interpretation := interpretation)
        (machine :=
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack })
        rfl targetAt targetPc targetInstruction targetNoCredits
          rewrittenDeclaration targetResolved targetUnder), ?_⟩
  exact StableMachineRel.history outputHeap fuel
    (.running (.rewritten rewrite outputFrame) outputStack)

/-- A successful extern call forces related arguments to be literally equal
scalars, so the shared oracle returns the same scalar result on both sides. -/
theorem unchangedExternStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (oracles : baselineContext.oracle = rewrittenContext.oracle)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {baselineValues : Array RVal}
    {arity : Nat} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .extern address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern arity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern arity))
    (argumentArity : baselineValues.size = arity)
    (called : ScalarOracleCall baselineContext address baselineValues value) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push value }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push value }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  obtain ⟨argumentsScalar, valueScalar⟩ := called.scalar
  have listEq : baselineValues.toList = rewrittenValues.toList := by
    apply valuesRelated.eq_of_allScalar
    rw [Array.all_toList]
    exact argumentsScalar
  have valuesEq : baselineValues = rewrittenValues :=
    Array.toList_inj.mp listEq
  subst rewrittenValues
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .extern address arguments := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have targetCalled :
      ScalarOracleCall rewrittenContext address baselineValues value :=
    called.congrOracle oracles
  refine ⟨
    Step.externCleared rfl sourceAt pc instruction noCredits resolved
      baselineDeclaration argumentArity called,
    Step.externCleared rfl targetAt targetPc targetInstruction targetNoCredits
      targetResolved rewrittenDeclaration argumentArity targetCalled, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running
      (.rewritten rewrite
        (frame.advancePush
          (IxIR1.Sim.RValIso.refl_of_scalar valueScalar)))
      stack)

/-! ## Allocation-history dynamic application -/

/-- Erased dynamic application releases corresponding argument vectors and
resumes related callers with the common erased value. -/
theorem unchangedApplyTransferErasedIso {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineArguments rewrittenArguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (resume : StableFrameRel limits validation heap.locRel
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (released : releaseSharedWork baselineFuel baselineStore
      baselineArguments.toList = .ok (baselineOut, baselineRemaining)) :
    let baselineTarget : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push .erased }
          baselineStack }
    ∃ rewrittenOut rewrittenRemaining,
      let rewrittenTarget : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push .erased }
            rewrittenStack }
      releaseSharedWork rewrittenFuel rewrittenStore
          rewrittenArguments.toList = .ok (rewrittenOut, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel .erased baselineArguments baselineResume baselineStack
          baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel .erased rewrittenArguments rewrittenResume
          rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenOut, rewrittenRemaining, outputHeap, targetReleased,
      outputFuel, outputRelation⟩ :=
    releaseSharedWork_historyIso heap fuel arguments released
  have outputResume : StableFrameRel limits validation outputHeap.locRel
      { baselineResume with values := baselineResume.values.push .erased }
      { rewrittenResume with values := rewrittenResume.values.push .erased } := by
    rw [outputRelation]
    exact resume.push .erased
  have outputStack : StableStackIso limits validation outputHeap.locRel
      baselineStack rewrittenStack := by
    rw [outputRelation]
    exact stack
  refine ⟨rewrittenOut, rewrittenRemaining, targetReleased,
    ApplyTransfer.erased released, ApplyTransfer.erased targetReleased, ?_⟩
  exact StableMachineRel.history outputHeap outputFuel
    (.running outputResume outputStack)

/-- Under-saturated PAP application follows a related PAP, performs
corresponding retain/release work, and allocates related extended PAPs. -/
theorem unchangedApplyTransferPapUnderIso {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineLocation rewrittenLocation : Nat}
    {baselineBox : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {baselineCaptured baselineArguments rewrittenArguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (locations : heap.locRel baselineLocation rewrittenLocation)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (resume : StableFrameRel limits validation heap.locRel
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (boxAt : baselineStore.get? baselineLocation = some baselineBox)
    (shared : baselineBox.world = .shared)
    (node : baselineBox.node = .papN address arity baselineCaptured)
    (capturedUnder : baselineCaptured.size < arity)
    (retained : RetainSharedMany baselineStore baselineCaptured
      baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc baselineLocation] = .ok (baselineReleased, baselineRemaining))
    (totalUnder : (baselineCaptured ++ baselineArguments).size < arity) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.papN address arity (baselineCaptured ++ baselineArguments))
    let baselineTarget : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ (rewrittenCaptured : Array RVal)
        (rewrittenRetained rewrittenReleased : Store)
        (rewrittenRemaining : Nat),
      let rewrittenAllocation := rewrittenReleased.allocNode .shared
        (.papN address arity (rewrittenCaptured ++ rewrittenArguments))
      let rewrittenTarget : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      RetainSharedMany rewrittenStore rewrittenCaptured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained
            [.loc rewrittenLocation] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc baselineLocation) baselineArguments baselineResume
          baselineStack baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc rewrittenLocation) rewrittenArguments
          rewrittenResume rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ := heap.boxes locations (by
    change baselineStore.heap.get? baselineLocation = some baselineBox
    exact boxAt)
  have papNodes : IxIR1.Sim.NodeIso heap.locRel
      (.papN address arity baselineCaptured) rewrittenBox.node := by
    simpa only [← node] using boxes.node
  obtain ⟨rewrittenCaptured, rewrittenNode, capturedRelated⟩ :=
    nodeIso_pap_left papNodes
  have rewrittenShared : rewrittenBox.world = .shared :=
    boxes.world.symm.trans shared
  have rewrittenCapturedUnder : rewrittenCaptured.size < arity := by
    have sizes : baselineCaptured.size = rewrittenCaptured.size := by
      simpa using rvalsIso_length_eq capturedRelated
    rw [← sizes]
    exact capturedUnder
  have totalRelated : IxIR1.Sim.RValsIso heap.locRel
      (baselineCaptured ++ baselineArguments).toList
      (rewrittenCaptured ++ rewrittenArguments).toList := by
    simpa using capturedRelated.append arguments
  have rewrittenTotalUnder :
      (rewrittenCaptured ++ rewrittenArguments).size < arity := by
    have sizes : (baselineCaptured ++ baselineArguments).size =
        (rewrittenCaptured ++ rewrittenArguments).size := by
      simpa using rvalsIso_length_eq totalRelated
    rw [← sizes]
    exact totalUnder
  obtain ⟨rewrittenRetained, retainedHeap, targetRetained,
      retainedRelation⟩ :=
    retainSharedMany_historyIso heap capturedRelated retained
  have retainedLocation : retainedHeap.locRel baselineLocation
      rewrittenLocation := by
    rw [retainedRelation]
    exact locations
  obtain ⟨rewrittenReleased, rewrittenRemaining, releasedHeap,
      targetReleased, outputFuel, releasedRelation⟩ :=
    releaseSharedWork_historyIso retainedHeap fuel
      (.cons (.loc retainedLocation) .nil) released
  have totalReleased : IxIR1.Sim.RValsIso releasedHeap.locRel
      (baselineCaptured ++ baselineArguments).toList
      (rewrittenCaptured ++ rewrittenArguments).toList := by
    rw [releasedRelation, retainedRelation]
    exact totalRelated
  let baselineAllocation := baselineReleased.allocNode .shared
    (.papN address arity (baselineCaptured ++ baselineArguments))
  let rewrittenAllocation := rewrittenReleased.allocNode .shared
    (.papN address arity (rewrittenCaptured ++ rewrittenArguments))
  let outputHeap : IxIR1.Sim.HeapHistoryIso baselineAllocation.1.heap
      rewrittenAllocation.1.heap := releasedHeap.alloc (.pap totalReleased)
  have oldExtends : ∀ {leftLocation rightLocation},
      heap.locRel leftLocation rightLocation →
      outputHeap.locRel leftLocation rightLocation := by
    intro leftLocation rightLocation related
    apply Or.inr
    rw [releasedRelation, retainedRelation]
    exact related
  have outputResume := (resume.mono oldExtends).push
    (IxIR1.Sim.RValIso.loc (Or.inl ⟨rfl, rfl⟩))
  have outputStack := stack.mono oldExtends
  refine ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
    rewrittenRemaining,
    targetRetained, targetReleased,
    ApplyTransfer.papUnder boxAt shared node capturedUnder retained released
      totalUnder,
    ApplyTransfer.papUnder (by
      change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
      exact rewrittenAt) rewrittenShared rewrittenNode rewrittenCapturedUnder
      targetRetained targetReleased rewrittenTotalUnder, ?_⟩
  exact StableMachineRel.history outputHeap outputFuel
    (.running outputResume outputStack)

/-- Saturated or over-saturated application follows a related PAP, performs
corresponding ownership traffic, and enters related callee rewrites with
related supplied and excess argument slices. -/
theorem unchangedApplyTransferPapFnIso {limits : Validate.Limits}
    {validation : Validate.Context} {calleeSource : Function}
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineLocation rewrittenLocation : Nat}
    {baselineBox : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {baselineCaptured baselineArguments rewrittenArguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (locations : heap.locRel baselineLocation rewrittenLocation)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (resume : StableFrameRel limits validation heap.locRel
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (boxAt : baselineStore.get? baselineLocation = some baselineBox)
    (shared : baselineBox.world = .shared)
    (node : baselineBox.node = .papN address arity baselineCaptured)
    (capturedUnder : baselineCaptured.size < arity)
    (retained : RetainSharedMany baselineStore baselineCaptured
      baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc baselineLocation] = .ok (baselineReleased, baselineRemaining))
    (totalEnough : arity ≤ (baselineCaptured ++ baselineArguments).size)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (papSafe : calleeSource.signature.papSafe = true)
    (suppliedArity :
      ((baselineCaptured ++ baselineArguments).extract 0 arity).size =
        calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let baselineTotal := baselineCaptured ++ baselineArguments
    let baselineSupplied := baselineTotal.extract 0 arity
    let baselineExcess := baselineTotal.extract arity baselineTotal.size
    let baselineContinuation : Continuation :=
      if baselineExcess.isEmpty then .resume baselineResume
      else .applyMore baselineExcess baselineResume
    let baselineTarget : Machine :=
      { store := baselineReleased
        heapFuel := baselineRemaining
        control := .running
          { definition := calleeSource, values := baselineSupplied }
          (baselineContinuation :: baselineStack) }
    ∃ (rewrittenCaptured : Array RVal)
        (rewrittenRetained rewrittenReleased : Store)
        (rewrittenRemaining : Nat),
      let rewrittenTotal := rewrittenCaptured ++ rewrittenArguments
      let rewrittenSupplied := rewrittenTotal.extract 0 arity
      let rewrittenExcess := rewrittenTotal.extract arity rewrittenTotal.size
      let rewrittenContinuation : Continuation :=
        if rewrittenExcess.isEmpty then .resume rewrittenResume
        else .applyMore rewrittenExcess rewrittenResume
      let rewrittenTarget : Machine :=
        { store := rewrittenReleased
          heapFuel := rewrittenRemaining
          control := .running
            { definition := calleeRewrite.definition,
              values := rewrittenSupplied }
            (rewrittenContinuation :: rewrittenStack) }
      RetainSharedMany rewrittenStore rewrittenCaptured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained
            [.loc rewrittenLocation] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc baselineLocation) baselineArguments baselineResume
          baselineStack baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc rewrittenLocation) rewrittenArguments
          rewrittenResume rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ := heap.boxes locations (by
    change baselineStore.heap.get? baselineLocation = some baselineBox
    exact boxAt)
  have papNodes : IxIR1.Sim.NodeIso heap.locRel
      (.papN address arity baselineCaptured) rewrittenBox.node := by
    simpa only [← node] using boxes.node
  obtain ⟨rewrittenCaptured, rewrittenNode, capturedRelated⟩ :=
    nodeIso_pap_left papNodes
  have rewrittenShared : rewrittenBox.world = .shared :=
    boxes.world.symm.trans shared
  have rewrittenCapturedUnder : rewrittenCaptured.size < arity := by
    have sizes : baselineCaptured.size = rewrittenCaptured.size := by
      simpa using rvalsIso_length_eq capturedRelated
    rw [← sizes]
    exact capturedUnder
  have totalRelated : IxIR1.Sim.RValsIso heap.locRel
      (baselineCaptured ++ baselineArguments).toList
      (rewrittenCaptured ++ rewrittenArguments).toList := by
    simpa using capturedRelated.append arguments
  have totalSizes : (baselineCaptured ++ baselineArguments).size =
      (rewrittenCaptured ++ rewrittenArguments).size := by
    simpa using rvalsIso_length_eq totalRelated
  have rewrittenTotalEnough :
      arity ≤ (rewrittenCaptured ++ rewrittenArguments).size := by
    rw [← totalSizes]
    exact totalEnough
  have suppliedRelated : IxIR1.Sim.RValsIso heap.locRel
      ((baselineCaptured ++ baselineArguments).extract 0 arity).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).toList :=
    rvalsIso_array_extract totalRelated 0 arity
  have excessRelated : IxIR1.Sim.RValsIso heap.locRel
      ((baselineCaptured ++ baselineArguments).extract arity
        (baselineCaptured ++ baselineArguments).size).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract arity
        (rewrittenCaptured ++ rewrittenArguments).size).toList := by
    have extracted := rvalsIso_array_extract totalRelated arity
      (baselineCaptured ++ baselineArguments).size
    simpa [totalSizes] using extracted
  have targetPapSafe :
      calleeRewrite.definition.signature.papSafe = true := by
    simpa using papSafe
  have targetSuppliedArity :
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).size =
        calleeRewrite.definition.signature.params.size := by
    have sizes :
        ((baselineCaptured ++ baselineArguments).extract 0 arity).size =
          ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).size := by
      simpa using rvalsIso_length_eq suppliedRelated
    rw [← sizes, calleeRewrite.definition_signature]
    exact suppliedArity
  have targetNonempty :
      calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  obtain ⟨rewrittenRetained, retainedHeap, targetRetained,
      retainedRelation⟩ :=
    retainSharedMany_historyIso heap capturedRelated retained
  have retainedLocation : retainedHeap.locRel baselineLocation
      rewrittenLocation := by
    rw [retainedRelation]
    exact locations
  obtain ⟨rewrittenReleased, rewrittenRemaining, releasedHeap,
      targetReleased, outputFuel, releasedRelation⟩ :=
    releaseSharedWork_historyIso retainedHeap fuel
      (.cons (.loc retainedLocation) .nil) released
  have suppliedReleased : IxIR1.Sim.RValsIso releasedHeap.locRel
      ((baselineCaptured ++ baselineArguments).extract 0 arity).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).toList := by
    rw [releasedRelation, retainedRelation]
    exact suppliedRelated
  have excessReleased : IxIR1.Sim.RValsIso releasedHeap.locRel
      ((baselineCaptured ++ baselineArguments).extract arity
        (baselineCaptured ++ baselineArguments).size).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract arity
        (rewrittenCaptured ++ rewrittenArguments).size).toList := by
    rw [releasedRelation, retainedRelation]
    exact excessRelated
  have resumeReleased : StableFrameRel limits validation releasedHeap.locRel
      baselineResume rewrittenResume := by
    rw [releasedRelation, retainedRelation]
    exact resume
  have stackReleased : StableStackIso limits validation releasedHeap.locRel
      baselineStack rewrittenStack := by
    rw [releasedRelation, retainedRelation]
    exact stack
  let continuation := StableContinuationIso.applyMoreOrResumeIso
    excessReleased resumeReleased
  refine ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
    rewrittenRemaining, targetRetained, targetReleased,
    ApplyTransfer.papFn boxAt shared node capturedUnder retained released
      totalEnough baselineDeclaration papSafe suppliedArity nonempty,
    ApplyTransfer.papFn (by
      change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
      exact rewrittenAt) rewrittenShared rewrittenNode rewrittenCapturedUnder
      targetRetained targetReleased rewrittenTotalEnough rewrittenDeclaration
      targetPapSafe targetSuppliedArity targetNonempty, ?_⟩
  exact StableMachineRel.history releasedHeap outputFuel
    (.running (StableFrameRel.entry calleeRewrite suppliedReleased)
      (.cons continuation stackReleased))

/-- Exactly saturated application of a related PAP to an extern transports
the ownership work, proves the supplied slices are the same scalars, and
resumes related callers with the common scalar result. -/
theorem unchangedApplyTransferPapExternIso {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineLocation rewrittenLocation : Nat}
    {baselineBox : IxIR1.NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity expectedArity : Nat}
    {baselineCaptured baselineArguments rewrittenArguments : Array RVal}
    {value : RVal} {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (locations : heap.locRel baselineLocation rewrittenLocation)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (resume : StableFrameRel limits validation heap.locRel
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (oracles : baselineContext.oracle = rewrittenContext.oracle)
    (boxAt : baselineStore.get? baselineLocation = some baselineBox)
    (shared : baselineBox.world = .shared)
    (node : baselineBox.node = .papN address arity baselineCaptured)
    (capturedUnder : baselineCaptured.size < arity)
    (retained : RetainSharedMany baselineStore baselineCaptured
      baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc baselineLocation] = .ok (baselineReleased, baselineRemaining))
    (totalEnough : arity ≤ (baselineCaptured ++ baselineArguments).size)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern expectedArity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern expectedArity))
    (suppliedArity :
      ((baselineCaptured ++ baselineArguments).extract 0 arity).size =
        expectedArity)
    (remainingEmpty :
      ((baselineCaptured ++ baselineArguments).extract arity
        (baselineCaptured ++ baselineArguments).size).isEmpty = true)
    (called : ScalarOracleCall baselineContext address
      ((baselineCaptured ++ baselineArguments).extract 0 arity) value) :
    let baselineTarget : Machine :=
      { store := baselineReleased
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push value }
          baselineStack }
    ∃ (rewrittenCaptured : Array RVal)
        (rewrittenRetained rewrittenReleased : Store)
        (rewrittenRemaining : Nat),
      let rewrittenTarget : Machine :=
        { store := rewrittenReleased
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push value }
            rewrittenStack }
      RetainSharedMany rewrittenStore rewrittenCaptured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained
            [.loc rewrittenLocation] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc baselineLocation) baselineArguments baselineResume
          baselineStack baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc rewrittenLocation) rewrittenArguments
          rewrittenResume rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenBox, rewrittenAt, boxes⟩ := heap.boxes locations (by
    change baselineStore.heap.get? baselineLocation = some baselineBox
    exact boxAt)
  have papNodes : IxIR1.Sim.NodeIso heap.locRel
      (.papN address arity baselineCaptured) rewrittenBox.node := by
    simpa only [← node] using boxes.node
  obtain ⟨rewrittenCaptured, rewrittenNode, capturedRelated⟩ :=
    nodeIso_pap_left papNodes
  have rewrittenShared : rewrittenBox.world = .shared :=
    boxes.world.symm.trans shared
  have rewrittenCapturedUnder : rewrittenCaptured.size < arity := by
    have sizes : baselineCaptured.size = rewrittenCaptured.size := by
      simpa using rvalsIso_length_eq capturedRelated
    rw [← sizes]
    exact capturedUnder
  have totalRelated : IxIR1.Sim.RValsIso heap.locRel
      (baselineCaptured ++ baselineArguments).toList
      (rewrittenCaptured ++ rewrittenArguments).toList := by
    simpa using capturedRelated.append arguments
  have totalSizes : (baselineCaptured ++ baselineArguments).size =
      (rewrittenCaptured ++ rewrittenArguments).size := by
    simpa using rvalsIso_length_eq totalRelated
  have rewrittenTotalEnough :
      arity ≤ (rewrittenCaptured ++ rewrittenArguments).size := by
    rw [← totalSizes]
    exact totalEnough
  have suppliedRelated : IxIR1.Sim.RValsIso heap.locRel
      ((baselineCaptured ++ baselineArguments).extract 0 arity).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).toList :=
    rvalsIso_array_extract totalRelated 0 arity
  have excessRelated : IxIR1.Sim.RValsIso heap.locRel
      ((baselineCaptured ++ baselineArguments).extract arity
        (baselineCaptured ++ baselineArguments).size).toList
      ((rewrittenCaptured ++ rewrittenArguments).extract arity
        (rewrittenCaptured ++ rewrittenArguments).size).toList := by
    have extracted := rvalsIso_array_extract totalRelated arity
      (baselineCaptured ++ baselineArguments).size
    simpa [totalSizes] using extracted
  have targetSuppliedArity :
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).size =
        expectedArity := by
    have sizes :
        ((baselineCaptured ++ baselineArguments).extract 0 arity).size =
          ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).size := by
      simpa using rvalsIso_length_eq suppliedRelated
    rw [← sizes]
    exact suppliedArity
  have targetRemainingEmpty :
      ((rewrittenCaptured ++ rewrittenArguments).extract arity
        (rewrittenCaptured ++ rewrittenArguments).size).isEmpty = true := by
    have lengths := rvalsIso_length_eq excessRelated
    have sizes :
        ((baselineCaptured ++ baselineArguments).extract arity
          (baselineCaptured ++ baselineArguments).size).size =
        ((rewrittenCaptured ++ rewrittenArguments).extract arity
          (rewrittenCaptured ++ rewrittenArguments).size).size := by
      simpa only [Array.length_toList] using lengths
    have emptyEq :
        ((baselineCaptured ++ baselineArguments).extract arity
          (baselineCaptured ++ baselineArguments).size).isEmpty =
        ((rewrittenCaptured ++ rewrittenArguments).extract arity
          (rewrittenCaptured ++ rewrittenArguments).size).isEmpty := by
      simp only [Array.isEmpty]
      rw [sizes]
    rw [← emptyEq]
    exact remainingEmpty
  obtain ⟨argumentsScalar, valueScalar⟩ := called.scalar
  have suppliedListsEq :
      ((baselineCaptured ++ baselineArguments).extract 0 arity).toList =
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity).toList := by
    apply suppliedRelated.eq_of_allScalar
    rw [Array.all_toList]
    exact argumentsScalar
  have suppliedEq :
      (baselineCaptured ++ baselineArguments).extract 0 arity =
      (rewrittenCaptured ++ rewrittenArguments).extract 0 arity :=
    Array.toList_inj.mp suppliedListsEq
  have targetCalled : ScalarOracleCall rewrittenContext address
      ((rewrittenCaptured ++ rewrittenArguments).extract 0 arity) value := by
    rw [← suppliedEq]
    exact called.congrOracle oracles
  obtain ⟨rewrittenRetained, retainedHeap, targetRetained,
      retainedRelation⟩ :=
    retainSharedMany_historyIso heap capturedRelated retained
  have retainedLocation : retainedHeap.locRel baselineLocation
      rewrittenLocation := by
    rw [retainedRelation]
    exact locations
  obtain ⟨rewrittenReleased, rewrittenRemaining, releasedHeap,
      targetReleased, outputFuel, releasedRelation⟩ :=
    releaseSharedWork_historyIso retainedHeap fuel
      (.cons (.loc retainedLocation) .nil) released
  have outputResume : StableFrameRel limits validation releasedHeap.locRel
      { baselineResume with values := baselineResume.values.push value }
      { rewrittenResume with values := rewrittenResume.values.push value } := by
    rw [releasedRelation, retainedRelation]
    exact resume.push (IxIR1.Sim.RValIso.refl_of_scalar valueScalar)
  have outputStack : StableStackIso limits validation releasedHeap.locRel
      baselineStack rewrittenStack := by
    rw [releasedRelation, retainedRelation]
    exact stack
  refine ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
    rewrittenRemaining, targetRetained, targetReleased,
    ApplyTransfer.papExtern boxAt shared node capturedUnder retained released
      totalEnough baselineDeclaration suppliedArity remainingEmpty called,
    ApplyTransfer.papExtern (by
      change rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
      exact rewrittenAt) rewrittenShared rewrittenNode rewrittenCapturedUnder
      targetRetained targetReleased rewrittenTotalEnough rewrittenDeclaration
      targetSuppliedArity targetRemainingEmpty targetCalled, ?_⟩
  exact StableMachineRel.history releasedHeap outputFuel
    (.running outputResume outputStack)

/-- Exhaustive allocation-history simulation of dynamic application.  The
source transfer selects its runtime branch; related values select the
corresponding target function and argument payloads. -/
theorem unchangedApplyTransferIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFunction rewrittenFunction : RVal}
    {baselineArguments rewrittenArguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {baselineTarget : Machine}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (function : IxIR1.Sim.RValIso heap.locRel
      baselineFunction rewrittenFunction)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (resume : StableFrameRel limits validation heap.locRel
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFunction
      baselineArguments baselineResume baselineStack baselineTarget) :
    ∃ rewrittenTarget,
      ApplyTransfer
          (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation rewrittenStore rewrittenFuel rewrittenFunction
          rewrittenArguments rewrittenResume rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  have classified := transferred.classify
  cases classified with
  | erased released =>
      cases function with
      | erased =>
          obtain ⟨rewrittenOut, rewrittenRemaining, targetReleased,
              sourceTransfer, targetTransfer, related⟩ :=
            unchangedApplyTransferErasedIso
              (baselineContext := Eval.Context.ofProgram sourceProgram
                validation.schemas oracle)
              (rewrittenContext := Eval.Context.ofProgram trace.target
                validation.schemas oracle)
              heap fuel arguments resume stack released
          exact ⟨_, targetTransfer, related⟩
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      cases function with
      | @loc _ rewrittenLocation locations =>
          obtain ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
              rewrittenRemaining, targetRetained, targetReleased,
              sourceTransfer, targetTransfer, related⟩ :=
            unchangedApplyTransferPapUnderIso
              (baselineContext := Eval.Context.ofProgram sourceProgram
                validation.schemas oracle)
              (rewrittenContext := Eval.Context.ofProgram trace.target
                validation.schemas oracle)
              heap fuel locations arguments resume stack boxAt shared node
                capturedUnder retained released totalUnder
          exact ⟨_, targetTransfer, related⟩
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      cases function with
      | @loc _ rewrittenLocation locations =>
          obtain ⟨calleeRewrite, targetDeclaration⟩ :=
            trace.context_fn declaration
          obtain ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
              rewrittenRemaining, targetRetained, targetReleased,
              sourceTransfer, targetTransfer, related⟩ :=
            unchangedApplyTransferPapFnIso calleeRewrite heap fuel locations
              arguments resume stack boxAt shared node capturedUnder retained
              released totalEnough declaration targetDeclaration papSafe
              suppliedArity nonempty
          exact ⟨_, targetTransfer, related⟩
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      cases function with
      | @loc _ rewrittenLocation locations =>
          have targetDeclaration := trace.context_extern declaration
          obtain ⟨rewrittenCaptured, rewrittenRetained, rewrittenReleased,
              rewrittenRemaining, targetRetained, targetReleased,
              sourceTransfer, targetTransfer, related⟩ :=
            unchangedApplyTransferPapExternIso
              (baselineContext := Eval.Context.ofProgram sourceProgram
                validation.schemas oracle)
              (rewrittenContext := Eval.Context.ofProgram trace.target
                validation.schemas oracle)
              heap fuel locations arguments resume stack rfl boxAt shared node
              capturedUnder retained released totalEnough declaration
              targetDeclaration suppliedArity remainingEmpty called
          exact ⟨_, targetTransfer, related⟩

/-- A source dynamic application in an unchanged block determines a target
application over related function and argument values. -/
theorem unchangedApplyStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {baselineTarget : Machine}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {functionAtom : Atom} {argumentAtoms : Array Atom}
    {baselineFunction : RVal} {baselineArguments : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .apply functionAtom argumentAtoms)
    (noCredits : NoLiveCredits baselineFrame)
    (functionResolved : resolveAtom baselineFrame.values functionAtom =
      .ok baselineFunction)
    (argumentsResolved : resolveAtoms baselineFrame.values argumentAtoms =
      .ok baselineArguments)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFunction
      baselineArguments { baselineFrame with pc := baselineFrame.pc + 1 }
      baselineStack baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  obtain ⟨rewrittenFunction, targetFunctionResolved, functionRelated⟩ :=
    resolveAtom_iso frame.values functionResolved
  obtain ⟨rewrittenArguments, targetArgumentsResolved, argumentsRelated⟩ :=
    resolveAtoms_iso frame.values argumentsResolved
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    rw [← frame.pc]
    exact pc
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .apply functionAtom argumentAtoms := by
    simpa only [← frame.pc] using instruction
  have targetNoCredits := frame.noLiveCredits noCredits
  have resume : StableFrameRel limits validation heap.locRel
      { baselineFrame with pc := baselineFrame.pc + 1 }
      { rewrittenFrame with pc := rewrittenFrame.pc + 1 } :=
    .rewritten rewrite frame.advance
  obtain ⟨rewrittenTarget, targetTransferred, related⟩ :=
    unchangedApplyTransferIso trace heap fuel functionRelated argumentsRelated
      resume stack transferred
  refine ⟨rewrittenTarget,
    Step.applyCleared rfl sourceAt pc instruction noCredits functionResolved
      argumentsResolved transferred,
    Step.applyCleared rfl targetAt targetPc targetInstruction targetNoCredits
      targetFunctionResolved targetArgumentsResolved targetTransferred,
    related⟩

/-! ## Exact-content dynamic application -/

/-- Erased dynamic application releases the same argument vector in both
machines, consuming at most the rewritten machine's additional heap fuel. -/
theorem unchangedApplyTransferErased {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {arguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (resume : StableFrameRel limits validation (fun left right => left = right)
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (released : releaseSharedWork baselineFuel baselineStore arguments.toList =
      .ok (baselineOut, baselineRemaining)) :
    let baselineTarget : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push .erased }
          baselineStack }
    ∃ rewrittenOut rewrittenRemaining,
      let rewrittenTarget : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push .erased }
            rewrittenStack }
      releaseSharedWork rewrittenFuel rewrittenStore arguments.toList =
          .ok (rewrittenOut, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel .erased arguments baselineResume baselineStack
          baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel .erased arguments rewrittenResume rewrittenStack
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenOut, rewrittenRemaining, targetReleased,
      outputHeap, outputFuel⟩ :=
    heap.releaseSharedWork_of_le fuel released
  refine ⟨rewrittenOut, rewrittenRemaining, targetReleased,
    ApplyTransfer.erased released, ApplyTransfer.erased targetReleased, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap)
    outputFuel
    (.running (resume.push (IxIR1.Sim.RValIso.refl .erased)) stack)

/-- Under-saturated PAP application performs congruent retain/release work,
allocates the same extended PAP payload, and resumes related callers with the
corresponding fresh location. -/
theorem unchangedApplyTransferPapUnder {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {location : Nat} {box : NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured arguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (resume : StableFrameRel limits validation (fun left right => left = right)
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (boxAt : baselineStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany baselineStore captured baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc location] = .ok (baselineReleased, baselineRemaining))
    (totalUnder : (captured ++ arguments).size < arity) :
    let baselineAllocation := baselineReleased.allocNode .shared
      (.papN address arity (captured ++ arguments))
    let baselineTarget : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push (.loc baselineAllocation.2) }
          baselineStack }
    ∃ rewrittenRetained rewrittenReleased rewrittenRemaining,
      let rewrittenAllocation := rewrittenReleased.allocNode .shared
        (.papN address arity (captured ++ arguments))
      let rewrittenTarget : Machine :=
        { store := rewrittenAllocation.1
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push
                (.loc rewrittenAllocation.2) }
            rewrittenStack }
      RetainSharedMany rewrittenStore captured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained [.loc location] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc location) arguments baselineResume baselineStack
          baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc location) arguments rewrittenResume
          rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq location]
    exact boxAt
  obtain ⟨rewrittenRetained, targetRetained, retainedHeap⟩ :=
    heap.retainSharedMany retained
  obtain ⟨rewrittenReleased, rewrittenRemaining, targetReleased,
      releasedHeap, outputFuel⟩ :=
    retainedHeap.releaseSharedWork_of_le fuel released
  have locationEq :
      (baselineReleased.allocNode .shared
        (.papN address arity (captured ++ arguments))).2 =
      (rewrittenReleased.allocNode .shared
        (.papN address arity (captured ++ arguments))).2 :=
    releasedHeap.allocNode_location .shared
      (.papN address arity (captured ++ arguments))
  have outputHeap : HeapContentsEq
      (baselineReleased.allocNode .shared
        (.papN address arity (captured ++ arguments))).1
      (rewrittenReleased.allocNode .shared
        (.papN address arity (captured ++ arguments))).1 :=
    releasedHeap.allocNode .shared
      (.papN address arity (captured ++ arguments))
  refine ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
    targetRetained, targetReleased, ?_, ?_, ?_⟩
  · exact ApplyTransfer.papUnder boxAt shared node capturedUnder retained
      released totalUnder
  · exact ApplyTransfer.papUnder targetBoxAt shared node capturedUnder
      targetRetained targetReleased totalUnder
  · exact .related (fun left right => left = right) (.contents outputHeap)
      outputFuel
      (.running (resume.push (IxIR1.Sim.RValIso.loc locationEq)) stack)

/-- Saturated and over-saturated PAP application enter related declaration
rewrites.  The shared captured vector is retained/released congruently, while
the common excess vector selects related `resume` or `applyMore`
continuations. -/
theorem unchangedApplyTransferPapFn {limits : Validate.Limits}
    {validation : Validate.Context} {calleeSource : Function}
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {location : Nat} {box : NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity : Nat}
    {captured arguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (resume : StableFrameRel limits validation (fun left right => left = right)
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (boxAt : baselineStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany baselineStore captured baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc location] = .ok (baselineReleased, baselineRemaining))
    (totalEnough : arity ≤ (captured ++ arguments).size)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (papSafe : calleeSource.signature.papSafe = true)
    (suppliedArity :
      ((captured ++ arguments).extract 0 arity).size =
        calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let total := captured ++ arguments
    let supplied := total.extract 0 arity
    let remaining := total.extract arity total.size
    let baselineContinuation : Continuation :=
      if remaining.isEmpty then .resume baselineResume
      else .applyMore remaining baselineResume
    let rewrittenContinuation : Continuation :=
      if remaining.isEmpty then .resume rewrittenResume
      else .applyMore remaining rewrittenResume
    let baselineTarget : Machine :=
      { store := baselineReleased
        heapFuel := baselineRemaining
        control := .running
          { definition := calleeSource, values := supplied }
          (baselineContinuation :: baselineStack) }
    ∃ rewrittenRetained rewrittenReleased rewrittenRemaining,
      let rewrittenTarget : Machine :=
        { store := rewrittenReleased
          heapFuel := rewrittenRemaining
          control := .running
            { definition := calleeRewrite.definition, values := supplied }
            (rewrittenContinuation :: rewrittenStack) }
      RetainSharedMany rewrittenStore captured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained [.loc location] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc location) arguments baselineResume baselineStack
          baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc location) arguments rewrittenResume
          rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq location]
    exact boxAt
  obtain ⟨rewrittenRetained, targetRetained, retainedHeap⟩ :=
    heap.retainSharedMany retained
  obtain ⟨rewrittenReleased, rewrittenRemaining, targetReleased,
      releasedHeap, outputFuel⟩ :=
    retainedHeap.releaseSharedWork_of_le fuel released
  have targetPapSafe :
      calleeRewrite.definition.signature.papSafe = true := by
    simpa using papSafe
  have targetSuppliedArity :
      ((captured ++ arguments).extract 0 arity).size =
        calleeRewrite.definition.signature.params.size := by
    simpa using suppliedArity
  have targetNonempty :
      calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  let supplied := (captured ++ arguments).extract 0 arity
  let remaining := (captured ++ arguments).extract arity
    (captured ++ arguments).size
  have continuation : StableContinuationIso limits validation
      (fun left right => left = right)
      (if remaining.isEmpty then .resume baselineResume
        else .applyMore remaining baselineResume)
      (if remaining.isEmpty then .resume rewrittenResume
        else .applyMore remaining rewrittenResume) :=
    StableContinuationIso.applyMoreOrResume remaining resume
  refine ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
    targetRetained, targetReleased, ?_, ?_, ?_⟩
  · exact ApplyTransfer.papFn boxAt shared node capturedUnder retained released
      totalEnough baselineDeclaration papSafe suppliedArity nonempty
  · exact ApplyTransfer.papFn targetBoxAt shared node capturedUnder
      targetRetained targetReleased totalEnough rewrittenDeclaration
      targetPapSafe targetSuppliedArity targetNonempty
  · exact .related (fun left right => left = right) (.contents releasedHeap)
      outputFuel
      (.running
        (StableFrameRel.entry calleeRewrite
          (IxIR1.Sim.RValsIso.refl supplied.toList))
        (.cons continuation stack))

/-- Exactly saturated PAP application to a scalar extern observes the same
oracle value in both contexts and resumes related callers immediately. -/
theorem unchangedApplyTransferPapExtern {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {location : Nat} {box : NodeBox}
    {address : Ix.Compiler.Ixon.Address} {arity expectedArity : Nat}
    {captured arguments : Array RVal} {value : RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (resume : StableFrameRel limits validation (fun left right => left = right)
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (oracles : baselineContext.oracle = rewrittenContext.oracle)
    (boxAt : baselineStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany baselineStore captured baselineRetained)
    (released : releaseSharedWork baselineFuel baselineRetained
      [.loc location] = .ok (baselineReleased, baselineRemaining))
    (totalEnough : arity ≤ (captured ++ arguments).size)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern expectedArity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern expectedArity))
    (suppliedArity :
      ((captured ++ arguments).extract 0 arity).size = expectedArity)
    (remainingEmpty :
      ((captured ++ arguments).extract arity
        (captured ++ arguments).size).isEmpty = true)
    (called : ScalarOracleCall baselineContext address
      ((captured ++ arguments).extract 0 arity) value) :
    let baselineTarget : Machine :=
      { store := baselineReleased
        heapFuel := baselineRemaining
        control := .running
          { baselineResume with
            values := baselineResume.values.push value }
          baselineStack }
    ∃ rewrittenRetained rewrittenReleased rewrittenRemaining,
      let rewrittenTarget : Machine :=
        { store := rewrittenReleased
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenResume with
              values := rewrittenResume.values.push value }
            rewrittenStack }
      RetainSharedMany rewrittenStore captured rewrittenRetained ∧
        releaseSharedWork rewrittenFuel rewrittenRetained [.loc location] =
          .ok (rewrittenReleased, rewrittenRemaining) ∧
        ScalarOracleCall rewrittenContext address
          ((captured ++ arguments).extract 0 arity) value ∧
        ApplyTransfer baselineContext interpretation baselineStore
          baselineFuel (.loc location) arguments baselineResume baselineStack
          baselineTarget ∧
        ApplyTransfer rewrittenContext interpretation rewrittenStore
          rewrittenFuel (.loc location) arguments rewrittenResume
          rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq location]
    exact boxAt
  obtain ⟨rewrittenRetained, targetRetained, retainedHeap⟩ :=
    heap.retainSharedMany retained
  obtain ⟨rewrittenReleased, rewrittenRemaining, targetReleased,
      releasedHeap, outputFuel⟩ :=
    retainedHeap.releaseSharedWork_of_le fuel released
  have targetCalled : ScalarOracleCall rewrittenContext address
      ((captured ++ arguments).extract 0 arity) value :=
    called.congrOracle oracles
  refine ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
    targetRetained, targetReleased, targetCalled, ?_, ?_, ?_⟩
  · exact ApplyTransfer.papExtern boxAt shared node capturedUnder retained
      released totalEnough baselineDeclaration suppliedArity remainingEmpty
      called
  · exact ApplyTransfer.papExtern targetBoxAt shared node capturedUnder
      targetRetained targetReleased totalEnough rewrittenDeclaration
      suppliedArity remainingEmpty targetCalled
  · exact .related (fun left right => left = right) (.contents releasedHeap)
      outputFuel
      (.running (resume.push (IxIR1.Sim.RValIso.refl value)) stack)

/-- Exhaustive exact-content simulation of an arbitrary successful dynamic
dispatch.  The evaluator's case witness selects the corresponding branch
proof, while the program rewrite trace supplies the related function or
preserved extern declaration at a PAP target. -/
theorem unchangedApplyTransfer {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {function : RVal} {arguments : Array RVal}
    {baselineResume rewrittenResume : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {baselineTarget : Machine}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (resume : StableFrameRel limits validation (fun left right => left = right)
      baselineResume rewrittenResume)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel function arguments
      baselineResume baselineStack baselineTarget) :
    ∃ rewrittenTarget,
      ApplyTransfer
          (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation rewrittenStore rewrittenFuel function arguments
          rewrittenResume rewrittenStack rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  have classified := transferred.classify
  cases classified with
  | erased released =>
      obtain ⟨rewrittenOut, rewrittenRemaining, targetReleased,
          sourceTransfer, targetTransfer, related⟩ :=
        unchangedApplyTransferErased
          (baselineContext :=
            Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (rewrittenContext :=
            Eval.Context.ofProgram trace.target validation.schemas oracle)
          (interpretation := interpretation)
          heap fuel resume stack released
      exact ⟨_, targetTransfer, related⟩
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      obtain ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
          targetRetained, targetReleased, sourceTransfer, targetTransfer,
          related⟩ :=
        unchangedApplyTransferPapUnder
          (baselineContext :=
            Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (rewrittenContext :=
            Eval.Context.ofProgram trace.target validation.schemas oracle)
          (interpretation := interpretation)
          heap fuel resume stack boxAt shared node capturedUnder retained
          released totalUnder
      exact ⟨_, targetTransfer, related⟩
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ := trace.context_fn declaration
      obtain ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
          targetRetained, targetReleased, sourceTransfer, targetTransfer,
          related⟩ :=
        unchangedApplyTransferPapFn calleeRewrite heap fuel resume stack boxAt
          shared node capturedUnder retained released totalEnough declaration
          targetDeclaration papSafe suppliedArity nonempty
      exact ⟨_, targetTransfer, related⟩
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      have targetDeclaration := trace.context_extern declaration
      obtain ⟨rewrittenRetained, rewrittenReleased, rewrittenRemaining,
          targetRetained, targetReleased, targetCalled, sourceTransfer,
          targetTransfer, related⟩ :=
        unchangedApplyTransferPapExtern
          (baselineContext :=
            Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (rewrittenContext :=
            Eval.Context.ofProgram trace.target validation.schemas oracle)
          (interpretation := interpretation)
          heap fuel resume stack rfl boxAt shared node capturedUnder retained
          released totalEnough declaration targetDeclaration suppliedArity
          remainingEmpty called
      exact ⟨_, targetTransfer, related⟩

/-- Lift any already-related dynamic dispatch through an unchanged `apply`
instruction.  Branch-specific transfer theorems discharge the three
successful runtime shapes without duplicating instruction decoding. -/
theorem unchangedApplyStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {baselineTarget rewrittenTarget : Machine}
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    {block : Block} {functionAtom : Atom} {argumentAtoms : Array Atom}
    {function : RVal} {arguments : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .apply functionAtom argumentAtoms)
    (noCredits : NoLiveCredits baselineFrame)
    (functionResolved : resolveAtom baselineFrame.values functionAtom =
      .ok function)
    (argumentsResolved : resolveAtoms baselineFrame.values argumentAtoms =
      .ok arguments)
    (baselineTransferred : ApplyTransfer baselineContext interpretation
      baselineStore baselineFuel function arguments
      { baselineFrame with pc := baselineFrame.pc + 1 }
      baselineStack baselineTarget)
    (rewrittenTransferred : ApplyTransfer rewrittenContext interpretation
      rewrittenStore rewrittenFuel function arguments
      { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
      rewrittenStack rewrittenTarget)
    (related : StableMachineRel limits validation baselineTarget
      rewrittenTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineTarget ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenTarget ∧
      StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .apply functionAtom argumentAtoms := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetFunctionResolved :
      resolveAtom rewrittenFrame.values functionAtom = .ok function := by
    rw [← frame.values_eq]
    exact functionResolved
  have targetArgumentsResolved :
      resolveAtoms rewrittenFrame.values argumentAtoms = .ok arguments := by
    rw [← frame.values_eq]
    exact argumentsResolved
  exact ⟨
    Step.applyCleared rfl sourceAt pc instruction noCredits functionResolved
      argumentsResolved baselineTransferred,
    Step.applyCleared rfl targetAt targetPc targetInstruction targetNoCredits
      targetFunctionResolved targetArgumentsResolved rewrittenTransferred,
    related⟩

/-- A source `apply` transfer in an unchanged block is enough to produce the
rewritten transfer and stable successor.  Runtime-case inversion and
declaration selection are discharged internally from the whole-program
rewrite trace. -/
theorem unchangedApplyStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {baselineTarget : Machine}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {functionAtom : Atom} {argumentAtoms : Array Atom}
    {function : RVal} {arguments : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .apply functionAtom argumentAtoms)
    (noCredits : NoLiveCredits baselineFrame)
    (functionResolved : resolveAtom baselineFrame.values functionAtom =
      .ok function)
    (argumentsResolved : resolveAtoms baselineFrame.values argumentAtoms =
      .ok arguments)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel function arguments
      { baselineFrame with pc := baselineFrame.pc + 1 }
      baselineStack baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation baselineMachine baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation rewrittenMachine rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have resume : StableFrameRel limits validation
      (fun left right => left = right)
      { baselineFrame with pc := baselineFrame.pc + 1 }
      { rewrittenFrame with pc := rewrittenFrame.pc + 1 } :=
    .rewritten rewrite frame.advance
  obtain ⟨rewrittenTarget, targetTransferred, related⟩ :=
    unchangedApplyTransfer trace heap fuel resume stack transferred
  refine ⟨rewrittenTarget, ?_⟩
  exact unchangedApplyStep rewrite frame sourceAt targetAt pc instruction
    noCredits functionResolved argumentsResolved transferred targetTransferred
    related

/-- Lift any already-related dynamic dispatch through an unchanged return-time
`applyMore` continuation.  The active callee's result-world check transports
through exact heap contents and its preserved signature. -/
theorem unchangedRetApplyMoreStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineCaller rewrittenCaller : Frame}
    {arguments : Array RVal}
    {baselineRest rewrittenRest : List Continuation}
    {baselineTarget rewrittenTarget : Machine}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (noCredits : NoLiveCredits baselineFrame)
    (world : value.hasWorld baselineStore
      baselineFrame.definition.signature.result = true)
    (baselineTransferred : ApplyTransfer baselineContext interpretation
      baselineStore baselineFuel value arguments baselineCaller baselineRest
      baselineTarget)
    (rewrittenTransferred : ApplyTransfer rewrittenContext interpretation
      rewrittenStore rewrittenFuel value arguments rewrittenCaller rewrittenRest
      rewrittenTarget)
    (related : StableMachineRel limits validation baselineTarget
      rewrittenTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame
          (.applyMore arguments baselineCaller :: baselineRest) }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame
          (.applyMore arguments rewrittenCaller :: rewrittenRest) }
    Step baselineContext interpretation baselineMachine baselineTarget ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenTarget ∧
      StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : value.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq, ← heap.rvalHasWorld_eq]
    exact world
  exact ⟨
    Step.retApplyMoreCleared rfl sourceAt pc terminator resolved noCredits world
      baselineTransferred,
    Step.retApplyMoreCleared rfl targetAt targetPc terminator targetResolved
      targetNoCredits targetWorld rewrittenTransferred,
    related⟩

/-- A source return-time `applyMore` transfer likewise determines the target
transfer exhaustively from the rewrite trace. -/
theorem unchangedRetApplyMoreStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineCaller rewrittenCaller : Frame}
    {arguments : Array RVal}
    {baselineRest rewrittenRest : List Continuation}
    {baselineTarget : Machine}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (caller : StableFrameRel limits validation (fun left right => left = right)
      baselineCaller rewrittenCaller)
    (rest : StableStackIso limits validation (fun left right => left = right)
      baselineRest rewrittenRest)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (noCredits : NoLiveCredits baselineFrame)
    (world : value.hasWorld baselineStore
      baselineFrame.definition.signature.result = true)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel value arguments baselineCaller
      baselineRest baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame
          (.applyMore arguments baselineCaller :: baselineRest) }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame
          (.applyMore arguments rewrittenCaller :: rewrittenRest) }
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation baselineMachine baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation rewrittenMachine rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  dsimp only
  obtain ⟨rewrittenTarget, targetTransferred, related⟩ :=
    unchangedApplyTransfer trace heap fuel caller rest transferred
  refine ⟨rewrittenTarget, ?_⟩
  exact unchangedRetApplyMoreStep rewrite heap frame sourceAt targetAt pc
    terminator resolved noCredits world transferred targetTransferred related

/-! ## Unchanged-block lockstep cases -/

/-- The first unchanged instruction case: identical `move` code advances
both related frames in lockstep and preserves exact semantic heap contents.
This is the template consumed by the exhaustive no-op block induction. -/
theorem unchangedMoveStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] = .move atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push value }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push value }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction :
      block.instructions[rewrittenFrame.pc] = .move atom := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  refine ⟨Step.move rfl sourceAt pc instruction resolved,
    Step.move rfl targetAt targetPc targetInstruction targetResolved, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running
      (.rewritten rewrite (frame.advancePush (IxIR1.Sim.RValIso.refl value)))
      stack)

/-- Constructor projection from an unchanged block observes the same node and
appends the same field value on exact-content heaps. -/
theorem unchangedFetchStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {cid : CtorId} {field location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .fetch atom cid field)
    (resolved : resolveAtom baselineFrame.values atom = .ok (.loc location))
    (boxAt : baselineStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (fieldAt : fields[field]? = some value) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push value }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push value }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .fetch atom cid field := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq location]
    exact boxAt
  refine ⟨Step.fetch rfl sourceAt pc instruction resolved boxAt node fieldAt,
    Step.fetch rfl targetAt targetPc targetInstruction targetResolved
      targetBoxAt node fieldAt, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running
      (.rewritten rewrite (frame.advancePush (IxIR1.Sim.RValIso.refl value)))
      stack)

/-- An unchanged shallow unique free kills the same fixed location on both
exact-content heaps. -/
theorem unchangedFreeUniqueStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {cid : CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .freeUnique atom cid)
    (resolved : resolveAtom baselineFrame.values atom = .ok (.loc location))
    (boxAt : baselineStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.all RVal.isScalar = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        store := baselineStore.kill location
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        store := rewrittenStore.kill location
        control := .running
          { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .freeUnique atom cid := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq location]
    exact boxAt
  refine ⟨Step.freeUnique rfl sourceAt pc instruction resolved boxAt unique
      node scalarFields,
    Step.freeUnique rfl targetAt targetPc targetInstruction targetResolved
      targetBoxAt unique node scalarFields, ?_⟩
  exact .related (fun left right => left = right)
    (.contents (heap.kill location)) fuel
    (.running (.rewritten rewrite frame.advance) stack)

/-- Ordinary allocation in an unchanged block chooses corresponding fresh
locations and preserves exact heap contents. -/
theorem unchangedAllocStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema}
    {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .alloc world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (fieldWorlds : FieldWorlds baselineStore schema values) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
    let rewrittenAllocation :=
      rewrittenStore.allocNode world (.ctorN cid values)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push (.loc rewrittenAllocation.2) }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid values)
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .alloc world cid arguments := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetFieldWorlds : FieldWorlds rewrittenStore schema values :=
    heap.fieldWorlds fieldWorlds
  have locationEq : baselineAllocation.2 = rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode_location world (.ctorN cid values)
  have outputHeap : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode world (.ctorN cid values)
  have sourceStep := Step.alloc
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction schemaAt resolved fieldWorlds
  have targetStep := Step.alloc
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
      targetFieldWorlds
  refine ⟨by simpa [baselineAllocation] using sourceStep,
    by simpa [rewrittenAllocation] using targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite
        (frame.advancePush (IxIR1.Sim.RValIso.loc locationEq)))
      stack)

/-- An unchanged `allocWith` fed an absent credit consumes the same slot and
falls back to corresponding fresh allocations on exact-content heaps. -/
theorem unchangedAllocWithAbsentStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (fieldWorlds : FieldWorlds baselineStore schema values)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (absent : credit.presence = .absent) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
    let rewrittenAllocation :=
      rewrittenStore.allocNode world (.ctorN cid values)
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc baselineAllocation.2) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenTaken with
            values := rewrittenTaken.values.push (.loc rewrittenAllocation.2) }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid values)
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetFieldWorlds : FieldWorlds rewrittenStore schema values :=
    heap.fieldWorlds fieldWorlds
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  have locationEq : baselineAllocation.2 = rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode_location world (.ctorN cid values)
  have outputHeap : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode world (.ctorN cid values)
  have sourceStep := Step.allocWithAbsent
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
      absent
  have targetStep := Step.allocWithAbsent
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
      targetFieldWorlds targetTaken layout absent
  refine ⟨by simpa [baselineAllocation] using sourceStep,
    by simpa [rewrittenAllocation] using targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite
        (takenFrame.push (IxIR1.Sim.RValIso.loc locationEq)))
      stack)

/-- A present logical credit records the same opportunity in both runs;
semantic allocation remains fresh and lockstep. -/
theorem unchangedAllocWithLogicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (fieldWorlds : FieldWorlds baselineStore schema values)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present none) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
    let rewrittenAllocation :=
      rewrittenStore.allocNode world (.ctorN cid values)
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc baselineAllocation.2) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenTaken with
            values := rewrittenTaken.values.push (.loc rewrittenAllocation.2) }
          rewrittenStack }
    Step baselineContext .logical baselineMachine baselineNext ∧
      Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  let baselineAllocation := baselineStore.allocNode world (.ctorN cid values)
  let rewrittenAllocation :=
    rewrittenStore.allocNode world (.ctorN cid values)
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetFieldWorlds : FieldWorlds rewrittenStore schema values :=
    heap.fieldWorlds fieldWorlds
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  have locationEq : baselineAllocation.2 = rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode_location world (.ctorN cid values)
  have outputHeap : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode world (.ctorN cid values)
  have sourceStep := Step.allocWithLogical
    (context := baselineContext)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
      present
  have targetStep := Step.allocWithLogical
    (context := rewrittenContext)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
      targetFieldWorlds targetTaken layout present
  refine ⟨by simpa [baselineAllocation] using sourceStep,
    by simpa [rewrittenAllocation] using targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite
        (takenFrame.push (IxIR1.Sim.RValIso.loc locationEq)))
      stack)

/-- Physical `allocWith` reuses the same reserved fixed location in both
exact-content heaps and appends that location to related frames. -/
theorem unchangedAllocWithPhysicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {world : Owned} {cid : CtorId} {arguments : Array Atom}
    {schema : CtorSchema} {values : Array RVal} {location : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : baselineContext.schemas world cid = some schema)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (fieldWorlds : FieldWorlds baselineStore schema values)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present (some location))
    (reused : baselineStore.reuseReservation location world
      (.ctorN cid values) schema.fields.size = .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineTaken with
            values := baselineTaken.values.push (.loc location) }
          baselineStack }
    ∃ rewrittenOut,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenTaken with
              values := rewrittenTaken.values.push (.loc location) }
            rewrittenStack }
      rewrittenStore.reuseReservation location world (.ctorN cid values)
          schema.fields.size = .ok rewrittenOut ∧
        Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .allocWith creditId world cid arguments := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas world cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetFieldWorlds : FieldWorlds rewrittenStore schema values :=
    heap.fieldWorlds fieldWorlds
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  obtain ⟨rewrittenOut, targetReused, outputHeap⟩ :=
    heap.reuseReservation reused
  refine ⟨rewrittenOut, targetReused,
    Step.allocWithPhysical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved fieldWorlds taken layout
        present reused,
    Step.allocWithPhysical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetFieldWorlds targetTaken layout present targetReused, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite
        (takenFrame.push (IxIR1.Sim.RValIso.refl (.loc location))))
      stack)

/-- Discarding an absent credit consumes the same frame slot and leaves both
exact-content heaps untouched. -/
theorem unchangedDiscardCreditAbsentStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (absent : credit.presence = .absent) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenTaken rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← pcs] using instruction
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  refine ⟨
    Step.discardCreditAbsent
      (context := baselineContext) (interpretation := interpretation)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken absent,
    Step.discardCreditAbsent
      (context := rewrittenContext) (interpretation := interpretation)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken absent, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite takenFrame) stack)

/-- Discarding a present logical credit consumes the same slot without a
physical heap action. -/
theorem unchangedDiscardCreditLogicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (present : credit.presence = .present none) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenTaken rewrittenStack }
    Step baselineContext .logical baselineMachine baselineNext ∧
      Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← pcs] using instruction
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  refine ⟨
    Step.discardCreditLogical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken present,
    Step.discardCreditLogical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken present, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite takenFrame) stack)

/-- Discarding a physical credit releases the same reserved fixed location
in both exact-content heaps. -/
theorem unchangedDiscardCreditPhysicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTaken : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {location : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .discardCredit creditId)
    (taken : CreditTake { baselineFrame with
      pc := baselineFrame.pc + 1 } creditId baselineTaken credit)
    (present : credit.presence = .present (some location))
    (released : baselineStore.releaseReservation location = .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTaken :=
      { baselineTaken with definition := rewrite.definition }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running baselineTaken baselineStack }
    ∃ rewrittenOut,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running rewrittenTaken rewrittenStack }
      rewrittenStore.releaseReservation location = .ok rewrittenOut ∧
        Step baselineContext .physical baselineMachine baselineNext ∧
        Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .discardCredit creditId := by
    simpa only [← pcs] using instruction
  obtain ⟨targetTaken, takenFrame⟩ := frame.advanceTake taken
  obtain ⟨rewrittenOut, targetReleased, outputHeap⟩ :=
    heap.releaseReservation released
  refine ⟨rewrittenOut, targetReleased,
    Step.discardCreditPhysical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction taken present released,
    Step.discardCreditPhysical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetTaken present
        targetReleased, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running (.rewritten rewrite takenFrame) stack)

/-- Logical unique extraction observes the same constructor, kills the same
fixed slot, and appends identical fields and required credit. -/
theorem unchangedTakeUniqueLogicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .takeUnique target cid)
    (schemaAt : baselineContext.schemas .unique cid = some schema)
    (resolved : resolveAtom baselineFrame.values target = .ok (.loc location))
    (viewed : ConstructorView baselineStore location .unique cid box fields)
    (unitRC : box.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present none }
    let baselineNext : Machine :=
      { store := baselineStore.kill location
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ fields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenStore.kill location
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ fields
            credits := rewrittenFrame.credits.push (some credit) }
          rewrittenStack }
    Step baselineContext .logical baselineMachine baselineNext ∧
      Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .takeUnique target cid := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas .unique cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtom rewrittenFrame.values target = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetViewed :
      ConstructorView rewrittenStore location .unique cid box fields :=
    heap.constructorView viewed
  refine ⟨
    Step.takeUniqueLogical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
    Step.takeUniqueLogical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetViewed unitRC, ?_⟩
  exact .related (fun left right => left = right)
    (.contents (heap.kill location)) fuel
    (.running
      (.rewritten rewrite (frame.advanceAppendCredit fields
        { layout := schema.layout, presence := .present none }))
      stack)

/-- Physical unique extraction reserves the same fixed slot and appends the
same location-bearing required credit in both runs. -/
theorem unchangedTakeUniquePhysicalStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .takeUnique target cid)
    (schemaAt : baselineContext.schemas .unique cid = some schema)
    (resolved : resolveAtom baselineFrame.values target = .ok (.loc location))
    (viewed : ConstructorView baselineStore location .unique cid box fields)
    (unitRC : box.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present (some location) }
    let baselineNext : Machine :=
      { store := baselineStore.reserve location
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ fields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenStore.reserve location
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ fields
            credits := rewrittenFrame.credits.push (some credit) }
          rewrittenStack }
    Step baselineContext .physical baselineMachine baselineNext ∧
      Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .takeUnique target cid := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas .unique cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtom rewrittenFrame.values target = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetViewed :
      ConstructorView rewrittenStore location .unique cid box fields :=
    heap.constructorView viewed
  refine ⟨
    Step.takeUniquePhysical
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
    Step.takeUniquePhysical
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetViewed unitRC, ?_⟩
  exact .related (fun left right => left = right)
    (.contents (heap.reserve location)) fuel
    (.running
      (.rewritten rewrite (frame.advanceAppendCredit fields
        { layout := schema.layout,
          presence := .present (some location) }))
      stack)

/-- A hot logical shared reset kills the same fixed slot, records the same
counter-insensitive heap contents, and appends an identical present credit. -/
theorem unchangedResetSharedLogicalHotStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target = .ok (.loc location))
    (viewed : ConstructorView baselineStore location .shared cid box fields)
    (unitRC : box.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present none }
    let baselineNext : Machine :=
      { store := ((baselineStore.tickResetAttempt).kill location).tickHotReset
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ fields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := ((rewrittenStore.tickResetAttempt).kill location).tickHotReset
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ fields
            credits := rewrittenFrame.credits.push (some credit) }
          rewrittenStack }
    Step baselineContext .logical baselineMachine baselineNext ∧
      Step rewrittenContext .logical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .resetShared target cid := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas .shared cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtom rewrittenFrame.values target = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetViewed :
      ConstructorView rewrittenStore location .shared cid box fields :=
    heap.constructorView viewed
  refine ⟨
    Step.resetSharedLogicalHot
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
    Step.resetSharedLogicalHot
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetViewed unitRC, ?_⟩
  exact .related (fun left right => left = right)
    (.contents (((heap.tickResetAttempt).kill location).tickHotReset)) fuel
    (.running
      (.rewritten rewrite (frame.advanceAppendCredit fields
        { layout := schema.layout, presence := .present none }))
      stack)

/-- A hot physical shared reset reserves the same fixed slot and appends the
same location-bearing present credit in both runs. -/
theorem unchangedResetSharedPhysicalHotStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target = .ok (.loc location))
    (viewed : ConstructorView baselineStore location .shared cid box fields)
    (unitRC : box.rc = 1) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .present (some location) }
    let baselineNext : Machine :=
      { store :=
          ((baselineStore.tickResetAttempt).reserve location).tickHotReset
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ fields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store :=
          ((rewrittenStore.tickResetAttempt).reserve location).tickHotReset
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values ++ fields
            credits := rewrittenFrame.credits.push (some credit) }
          rewrittenStack }
    Step baselineContext .physical baselineMachine baselineNext ∧
      Step rewrittenContext .physical rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .resetShared target cid := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas .shared cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtom rewrittenFrame.values target = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetViewed :
      ConstructorView rewrittenStore location .shared cid box fields :=
    heap.constructorView viewed
  refine ⟨
    Step.resetSharedPhysicalHot
      (context := baselineContext)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved viewed unitRC,
    Step.resetSharedPhysicalHot
      (context := rewrittenContext)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetViewed unitRC, ?_⟩
  exact .related (fun left right => left = right)
    (.contents (((heap.tickResetAttempt).reserve location).tickHotReset)) fuel
    (.running
      (.rewritten rewrite (frame.advanceAppendCredit fields
        { layout := schema.layout,
          presence := .present (some location) }))
      stack)

/-- A cold shared reset transports the parent decrement and the entire field
retain loop across exact-content heaps, then appends the common absent credit. -/
theorem unchangedResetSharedColdStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (schemas : baselineContext.schemas = rewrittenContext.schemas)
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {target : Atom} {cid : CtorId}
    {schema : CtorSchema} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .resetShared target cid)
    (schemaAt : baselineContext.schemas .shared cid = some schema)
    (resolved : resolveAtom baselineFrame.values target = .ok (.loc location))
    (viewed : ConstructorView baselineStore location .shared cid box fields)
    (shared : 1 < box.rc)
    (retained : RetainSharedMany
      ((((baselineStore.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      fields baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let credit : Credit :=
      { layout := schema.layout, presence := .absent }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values ++ fields
            credits := baselineFrame.credits.push (some credit) }
          baselineStack }
    ∃ rewrittenOut,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values ++ fields
              credits := rewrittenFrame.credits.push (some credit) }
            rewrittenStack }
      RetainSharedMany
          ((((rewrittenStore.tickResetAttempt).setBox location
            { box with rc := box.rc - 1 }).rcTick).tickColdReset)
          fields rewrittenOut ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .resetShared target cid := by
    simpa only [← pcs] using instruction
  have targetSchemaAt : rewrittenContext.schemas .shared cid = some schema := by
    rw [← schemas]
    exact schemaAt
  have targetResolved :
      resolveAtom rewrittenFrame.values target = .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetViewed :
      ConstructorView rewrittenStore location .shared cid box fields :=
    heap.constructorView viewed
  have beforeRetain : HeapContentsEq
      ((((baselineStore.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      ((((rewrittenStore.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset) :=
    ((((heap.tickResetAttempt).setBox location
      { box with rc := box.rc - 1 }).rcTick).tickColdReset)
  obtain ⟨rewrittenOut, targetRetained, outputHeap⟩ :=
    beforeRetain.retainSharedMany retained
  refine ⟨rewrittenOut, targetRetained,
    Step.resetSharedCold
      (context := baselineContext) (interpretation := interpretation)
      (machine :=
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack })
      rfl sourceAt pc instruction schemaAt resolved viewed shared retained,
    Step.resetSharedCold
      (context := rewrittenContext) (interpretation := interpretation)
      (machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack })
      rfl targetAt targetPc targetInstruction targetSchemaAt targetResolved
        targetViewed shared targetRetained, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite (frame.advanceAppendCredit fields
        { layout := schema.layout, presence := .absent }))
      stack)

/-- An unchanged recursive call enters the two versions of the same function
and pushes related advanced caller frames. -/
theorem unchangedCallSelfStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {arguments : Array Atom} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .callSelf arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (arity : values.size =
      baselineFrame.definition.signature.params.size)
    (nonempty : baselineFrame.definition.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := baselineFrame.definition, values }
          (.resume { baselineFrame with pc := baselineFrame.pc + 1 } ::
            baselineStack) }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { definition := rewrittenFrame.definition, values }
          (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 } ::
            rewrittenStack) }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .callSelf arguments := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have sourceArity : values.size = source.signature.params.size := by
    simpa [frame.baselineDefinition] using arity
  have targetArity : values.size =
      rewrittenFrame.definition.signature.params.size := by
    simpa [frame.rewrittenDefinition] using sourceArity
  have targetNonempty : rewrittenFrame.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem targetAt
  have sourceStep := Step.callSelfCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction noCredits resolved arity nonempty
  have targetStep := Step.callSelfCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetNoCredits targetResolved
      targetArity targetNonempty
  refine ⟨sourceStep, targetStep, ?_⟩
  have callee : StableFrameRel limits validation
      (fun left right => left = right)
      { definition := baselineFrame.definition, values }
      { definition := rewrittenFrame.definition, values } := by
    rw [frame.baselineDefinition, frame.rewrittenDefinition]
    exact StableFrameRel.entry rewrite (IxIR1.Sim.RValsIso.refl values.toList)
  have resume : StableContinuationIso limits validation
      (fun left right => left = right)
      (.resume { baselineFrame with pc := baselineFrame.pc + 1 })
      (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 }) :=
    .resume (.rewritten rewrite frame.advance)
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running callee (.cons resume stack))

/-- An unchanged direct call follows the declaration rewrite selected at the
same address and pushes related advanced caller frames. -/
theorem unchangedCallFnStep {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .call address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (arity : values.size = calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running { definition := calleeSource, values }
          (.resume { baselineFrame with pc := baselineFrame.pc + 1 } ::
            baselineStack) }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { definition := calleeRewrite.definition, values }
          (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 } ::
            rewrittenStack) }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .call address arguments := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetArity : values.size =
      calleeRewrite.definition.signature.params.size := by
    simpa using arity
  have targetNonempty : calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  have sourceStep := Step.callFnCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction noCredits resolved baselineDeclaration arity
      nonempty
  have targetStep := Step.callFnCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetNoCredits targetResolved
      rewrittenDeclaration targetArity targetNonempty
  refine ⟨sourceStep, targetStep, ?_⟩
  have callee : StableFrameRel limits validation
      (fun left right => left = right)
      { definition := calleeSource, values }
      { definition := calleeRewrite.definition, values } :=
    StableFrameRel.entry calleeRewrite (IxIR1.Sim.RValsIso.refl values.toList)
  have resume : StableContinuationIso limits validation
      (fun left right => left = right)
      (.resume { baselineFrame with pc := baselineFrame.pc + 1 })
      (.resume { rewrittenFrame with pc := rewrittenFrame.pc + 1 }) :=
    .resume (.rewritten callerRewrite frame.advance)
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running callee (.cons resume stack))

/-- An unchanged partial application allocates equal PAP payloads in
exact-content heaps; the declaration rewrite preserves the target signature
and PAP-safety bit used by the runtime check. -/
theorem unchangedPappFnStep {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .papp address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (papSafe : calleeSource.signature.papSafe = true)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (under : values.size < calleeSource.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode .shared
      (.papN address calleeSource.signature.params.size values)
    let rewrittenAllocation := rewrittenStore.allocNode .shared
      (.papN address calleeSource.signature.params.size values)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push (.loc rewrittenAllocation.2) }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  let baselineAllocation := baselineStore.allocNode .shared
    (.papN address calleeSource.signature.params.size values)
  let rewrittenAllocation := rewrittenStore.allocNode .shared
    (.papN address calleeSource.signature.params.size values)
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .papp address arguments := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetPapSafe : calleeRewrite.definition.signature.papSafe = true := by
    simpa using papSafe
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetUnder :
      values.size < calleeRewrite.definition.signature.params.size := by
    simpa using under
  have locationEq : baselineAllocation.2 = rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode_location .shared
        (.papN address calleeSource.signature.params.size values)
  have outputHeap : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode .shared
        (.papN address calleeSource.signature.params.size values)
  have sourceStep := Step.pappFnCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction noCredits baselineDeclaration papSafe resolved
      under
  have targetStep := Step.pappFnCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetNoCredits
      rewrittenDeclaration targetPapSafe targetResolved targetUnder
  refine ⟨by simpa [baselineAllocation] using sourceStep,
    by simpa [rewrittenAllocation] using targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten callerRewrite
        (frame.advancePush (IxIR1.Sim.RValIso.loc locationEq)))
      stack)

/-- An unchanged partial application of an extern allocates the same PAP in
exact-content heaps.  Extern declarations are preserved literally by a
whole-program reuse trace, so unlike the function-targeted case there is no
callee rewrite to enter. -/
theorem unchangedPappExternStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {values : Array RVal} {arity : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .papp address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern arity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern arity))
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (under : values.size < arity) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineAllocation := baselineStore.allocNode .shared
      (.papN address arity values)
    let rewrittenAllocation := rewrittenStore.allocNode .shared
      (.papN address arity values)
    let baselineNext : Machine :=
      { store := baselineAllocation.1
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push (.loc baselineAllocation.2) }
          baselineStack }
    let rewrittenNext : Machine :=
      { store := rewrittenAllocation.1
        heapFuel := rewrittenFuel
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push (.loc rewrittenAllocation.2) }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  let baselineAllocation := baselineStore.allocNode .shared
    (.papN address arity values)
  let rewrittenAllocation := rewrittenStore.allocNode .shared
    (.papN address arity values)
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .papp address arguments := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have locationEq : baselineAllocation.2 = rewrittenAllocation.2 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode_location .shared (.papN address arity values)
  have outputHeap : HeapContentsEq baselineAllocation.1
      rewrittenAllocation.1 := by
    simpa [baselineAllocation, rewrittenAllocation] using
      heap.allocNode .shared (.papN address arity values)
  have sourceStep := Step.pappExternCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc instruction noCredits baselineDeclaration resolved under
  have targetStep := Step.pappExternCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc targetInstruction targetNoCredits
      rewrittenDeclaration targetResolved under
  refine ⟨by simpa [baselineAllocation] using sourceStep,
    by simpa [rewrittenAllocation] using targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite
        (frame.advancePush (IxIR1.Sim.RValIso.loc locationEq)))
      stack)

/-- An unchanged scalar extern instruction resolves the same preserved extern
declaration and observes the same oracle result. -/
theorem unchangedExternStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    (oracles : baselineContext.oracle = rewrittenContext.oracle)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {values : Array RVal}
    {arity : Nat} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .extern address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (baselineDeclaration : baselineContext.declarations address =
      some (.extern arity))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.extern arity))
    (argumentArity : values.size = arity)
    (called : ScalarOracleCall baselineContext address values value) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push value }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { rewrittenFrame with
            pc := rewrittenFrame.pc + 1
            values := rewrittenFrame.values.push value }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .extern address arguments := by
    simpa only [← pcs] using instruction
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetCalled :
      ScalarOracleCall rewrittenContext address values value :=
    called.congrOracle oracles
  refine ⟨Step.externCleared rfl sourceAt pc instruction noCredits resolved
      baselineDeclaration argumentArity called,
    Step.externCleared rfl targetAt targetPc targetInstruction targetNoCredits
      targetResolved rewrittenDeclaration argumentArity targetCalled, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running
      (.rewritten rewrite
        (frame.advancePush (IxIR1.Sim.RValIso.refl value)))
      stack)

/-- An unchanged tail-recursive call re-enters the two versions of the
current function without changing either continuation stack. -/
theorem unchangedTailCallSelfStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {arguments : Array Atom} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCallSelf arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (arity : values.size =
      baselineFrame.definition.signature.params.size)
    (nonempty : baselineFrame.definition.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := baselineFrame.definition, values } baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { definition := rewrittenFrame.definition, values } rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have sourceArity : values.size = source.signature.params.size := by
    simpa [frame.baselineDefinition] using arity
  have targetArity : values.size =
      rewrittenFrame.definition.signature.params.size := by
    simpa [frame.rewrittenDefinition] using sourceArity
  have targetNonempty : rewrittenFrame.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem targetAt
  have sourceStep := Step.tailCallSelfCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc terminator noCredits resolved arity nonempty
  have targetStep := Step.tailCallSelfCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc terminator targetNoCredits targetResolved
      targetArity targetNonempty
  refine ⟨sourceStep, targetStep, ?_⟩
  have callee : StableFrameRel limits validation
      (fun left right => left = right)
      { definition := baselineFrame.definition, values }
      { definition := rewrittenFrame.definition, values } := by
    rw [frame.baselineDefinition, frame.rewrittenDefinition]
    exact StableFrameRel.entry rewrite (IxIR1.Sim.RValsIso.refl values.toList)
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running callee stack)

/-- An unchanged direct tail call selects related source/target declarations
at the same address and enters the rewritten callee with the existing related
stacks. -/
theorem unchangedTailCallFnStep {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {values : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCall address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments = .ok values)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (arity : values.size = calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running { definition := calleeSource, values }
          baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { definition := calleeRewrite.definition, values }
          rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have targetResolved :
      resolveAtoms rewrittenFrame.values arguments = .ok values := by
    rw [← frame.values_eq]
    exact resolved
  have targetArity : values.size =
      calleeRewrite.definition.signature.params.size := by
    simpa using arity
  have targetNonempty : calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  have sourceStep := Step.tailCallFnCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack })
    rfl sourceAt pc terminator noCredits resolved baselineDeclaration arity
      nonempty
  have targetStep := Step.tailCallFnCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack })
    rfl targetAt targetPc terminator targetNoCredits targetResolved
      rewrittenDeclaration targetArity targetNonempty
  refine ⟨sourceStep, targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running
      (StableFrameRel.entry calleeRewrite
        (IxIR1.Sim.RValsIso.refl values.toList))
      stack)

/-- An unchanged return through an ordinary continuation pushes the same
value into related suspended callers.  Exact heap contents also transport
the result-world check used by the return boundary. -/
theorem unchangedRetResumeStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineCaller rewrittenCaller : Frame}
    {baselineRest rewrittenRest : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (caller : StableFrameRel limits validation (fun left right => left = right)
      baselineCaller rewrittenCaller)
    (rest : StableStackIso limits validation (fun left right => left = right)
      baselineRest rewrittenRest)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (noCredits : NoLiveCredits baselineFrame)
    (world : value.hasWorld baselineStore
      baselineFrame.definition.signature.result = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame
          (.resume baselineCaller :: baselineRest) }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame
          (.resume rewrittenCaller :: rewrittenRest) }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineCaller with
            values := baselineCaller.values.push value }
          baselineRest }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running
          { rewrittenCaller with
            values := rewrittenCaller.values.push value }
          rewrittenRest }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : value.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq, ← heap.rvalHasWorld_eq]
    exact world
  have sourceStep := Step.retResumeCleared
    (context := baselineContext) (interpretation := interpretation)
    (machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame
          (.resume baselineCaller :: baselineRest) })
    rfl sourceAt pc terminator resolved noCredits world
  have targetStep := Step.retResumeCleared
    (context := rewrittenContext) (interpretation := interpretation)
    (machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame
          (.resume rewrittenCaller :: rewrittenRest) })
    rfl targetAt targetPc terminator targetResolved targetNoCredits targetWorld
  refine ⟨sourceStep, targetStep, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (caller.push (IxIR1.Sim.RValIso.refl value)) rest)

/-- The outermost unchanged return halts both machines with the same value. -/
theorem unchangedRetHaltStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (noCredits : NoLiveCredits baselineFrame)
    (world : value.hasWorld baselineStore
      baselineFrame.definition.signature.result = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame [] }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame [] }
    let baselineNext : Machine :=
      { baselineMachine with control := .halted value }
    let rewrittenNext : Machine :=
      { rewrittenMachine with control := .halted value }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  have targetNoCredits : NoLiveCredits rewrittenFrame := by
    unfold NoLiveCredits at noCredits ⊢
    rw [← frame.credits_eq]
    exact noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : value.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq, ← heap.rvalHasWorld_eq]
    exact world
  refine ⟨Step.retHaltCleared rfl sourceAt pc terminator resolved noCredits world,
    Step.retHaltCleared rfl targetAt targetPc terminator targetResolved
      targetNoCredits targetWorld, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.halted (IxIR1.Sim.RValIso.refl value))

/-- An unchanged jump transports its checked edge through the rewritten
function's preserved target-block ABI. -/
theorem unchangedJumpStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {edge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .jump edge)
    (transferred : EdgeTransfer baselineFrame edge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  obtain ⟨rewrittenTransfer, targetFrame⟩ := frame.edgeTransfer transferred
  refine ⟨Step.jump rfl sourceAt pc terminator transferred,
    Step.jump rfl targetAt targetPc terminator rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- Constructor dispatch observes the same node in exact-content heaps and
then transports the selected edge through the rewritten target ABI. -/
theorem unchangedSwitchCtorStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {location : Nat} {box : NodeBox}
    {cid : CtorId} {fields : Array RVal} {alternative : CtorAlt}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors natPeel)
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.loc location))
    (boxAt : baselineStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (alternativeAt : constructors.find? (fun candidate =>
      candidate.cid == cid) = some alternative)
    (transferred : EdgeTransfer baselineFrame alternative.edge #[]
      baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved : resolveAtom rewrittenFrame.values scrutinee =
      .ok (.loc location) := by
    rw [← frame.values_eq]
    exact resolved
  have targetBoxAt : rewrittenStore.get? location = some box := by
    rw [← heap.get?_eq]
    exact boxAt
  obtain ⟨rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransfer transferred
  refine ⟨Step.switchCtor rfl sourceAt pc terminator resolved boxAt node
      alternativeAt transferred,
    Step.switchCtor rfl targetAt targetPc terminator targetResolved
      targetBoxAt node alternativeAt rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- The zero arm of an unchanged literal-Nat switch follows the corresponding
rewritten edge. -/
theorem unchangedSwitchNatZeroStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {peel : NatPeel}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.lit (.nat 0)))
    (transferred : EdgeTransfer baselineFrame peel.zero #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved : resolveAtom rewrittenFrame.values scrutinee =
      .ok (.lit (.nat 0)) := by
    rw [← frame.values_eq]
    exact resolved
  obtain ⟨rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransfer transferred
  refine ⟨Step.switchNatZero rfl sourceAt pc terminator resolved transferred,
    Step.switchNatZero rfl targetAt targetPc terminator targetResolved
      rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- The successor arm of an unchanged literal-Nat switch preserves its
implicit predecessor value while transporting the explicit edge. -/
theorem unchangedSwitchNatSuccStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {peel : NatPeel} {predecessor : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (transferred : EdgeTransfer baselineFrame peel.succ
      #[.lit (.nat predecessor)] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetResolved : resolveAtom rewrittenFrame.values scrutinee =
      .ok (.lit (.nat (predecessor + 1))) := by
    rw [← frame.values_eq]
    exact resolved
  obtain ⟨rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransfer transferred
  refine ⟨Step.switchNatSucc rfl sourceAt pc terminator resolved transferred,
    Step.switchNatSucc rfl targetAt targetPc terminator targetResolved
      rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- A present optional credit selects the same unchanged branch and carries
its checked edge into the rewritten definition. -/
theorem unchangedBranchCreditPresentStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {someEdge noneEdge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup baselineFrame creditId credit)
    (present : credit.isPresent = true)
    (transferred : EdgeTransfer baselineFrame someEdge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetLookup := lookedUp.congrDefinition rewrite.definition
  rw [← frame.rewritten_eq] at targetLookup
  obtain ⟨rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransfer transferred
  refine ⟨Step.branchCreditPresent rfl sourceAt pc terminator lookedUp
      present transferred,
    Step.branchCreditPresent rfl targetAt targetPc terminator targetLookup
      present rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- An absent optional credit selects and transports the same fallback edge. -/
theorem unchangedBranchCreditAbsentStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {someEdge noneEdge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup baselineFrame creditId credit)
    (absent : credit.isPresent = false)
    (transferred : EdgeTransfer baselineFrame noneEdge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let rewrittenTarget :=
      { baselineTarget with definition := rewrite.definition }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    let rewrittenNext : Machine :=
      { rewrittenMachine with
        control := .running rewrittenTarget rewrittenStack }
    Step baselineContext interpretation baselineMachine baselineNext ∧
      Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
      StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetLookup := lookedUp.congrDefinition rewrite.definition
  rw [← frame.rewritten_eq] at targetLookup
  obtain ⟨rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransfer transferred
  refine ⟨Step.branchCreditAbsent rfl sourceAt pc terminator lookedUp
      absent transferred,
    Step.branchCreditAbsent rfl targetAt targetPc terminator targetLookup
      absent rewrittenTransfer, ?_⟩
  exact .related (fun left right => left = right) (.contents heap) fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- An unchanged shared retain executes on both exact-content heaps and
preserves the stable relation. -/
theorem unchangedRetainSharedStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .retainShared atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (retained : Eval.retainShared baselineStore value = .ok baselineOut) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineFuel
        control := .running
          { baselineFrame with
            pc := baselineFrame.pc + 1
            values := baselineFrame.values.push value }
          baselineStack }
    ∃ rewrittenOut,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenFuel
          control := .running
            { rewrittenFrame with
              pc := rewrittenFrame.pc + 1
              values := rewrittenFrame.values.push value }
            rewrittenStack }
      Eval.retainShared rewrittenStore value = .ok rewrittenOut ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .retainShared atom := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  obtain ⟨rewrittenOut, targetRetained, outputHeap⟩ :=
    heap.retainShared retained
  refine ⟨rewrittenOut, targetRetained,
    Step.retainShared rfl sourceAt pc instruction resolved retained,
    Step.retainShared rfl targetAt targetPc targetInstruction
      targetResolved targetRetained, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap) fuel
    (.running
      (.rewritten rewrite (frame.advancePush (IxIR1.Sim.RValIso.refl value)))
      stack)

/-- An unchanged deep shared release remains executable when the rewritten
machine has at least the baseline heap fuel.  Any saved fuel is carried into
the rewritten remainder. -/
theorem unchangedReleaseSharedStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] =
      .releaseShared atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (released : Eval.releaseShared baselineFuel baselineStore value =
      .ok (baselineOut, baselineRemaining)) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    ∃ rewrittenOut rewrittenRemaining,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
            rewrittenStack }
      Eval.releaseShared rewrittenFuel rewrittenStore value =
          .ok (rewrittenOut, rewrittenRemaining) ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .releaseShared atom := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  obtain ⟨rewrittenOut, rewrittenRemaining, targetReleased,
      outputHeap, outputFuel⟩ :=
    heap.releaseShared_of_le fuel released
  refine ⟨rewrittenOut, rewrittenRemaining, targetReleased,
    Step.releaseShared rfl sourceAt pc instruction resolved released,
    Step.releaseShared rfl targetAt targetPc targetInstruction
      targetResolved targetReleased, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap)
    outputFuel
    (.running (.rewritten rewrite frame.advance) stack)

/-- The unchanged unique-drop case has the same fuel-dominance behavior as
shared release. -/
theorem unchangedDropUniqueStep {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore baselineOut : Store}
    {baselineFuel rewrittenFuel baselineRemaining : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {atom : Atom} {value : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instruction : block.instructions[baselineFrame.pc] = .dropUnique atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok value)
    (dropped : Eval.dropUnique baselineFuel baselineStore value =
      .ok (baselineOut, baselineRemaining)) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { store := baselineOut
        heapFuel := baselineRemaining
        control := .running
          { baselineFrame with pc := baselineFrame.pc + 1 }
          baselineStack }
    ∃ rewrittenOut rewrittenRemaining,
      let rewrittenNext : Machine :=
        { store := rewrittenOut
          heapFuel := rewrittenRemaining
          control := .running
            { rewrittenFrame with pc := rewrittenFrame.pc + 1 }
            rewrittenStack }
      Eval.dropUnique rewrittenFuel rewrittenStore value =
          .ok (rewrittenOut, rewrittenRemaining) ∧
        Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have pcs : baselineFrame.pc = rewrittenFrame.pc := frame.pc
  have targetPc : rewrittenFrame.pc < block.instructions.size := by
    omega
  have targetInstruction : block.instructions[rewrittenFrame.pc] =
      .dropUnique atom := by
    simpa only [← pcs] using instruction
  have targetResolved :
      resolveAtom rewrittenFrame.values atom = .ok value := by
    rw [← frame.values_eq]
    exact resolved
  obtain ⟨rewrittenOut, rewrittenRemaining, targetDropped,
      outputHeap, outputFuel⟩ := heap.dropUnique_of_le fuel dropped
  refine ⟨rewrittenOut, rewrittenRemaining, targetDropped,
    Step.dropUnique rfl sourceAt pc instruction resolved dropped,
    Step.dropUnique rfl targetAt targetPc targetInstruction
      targetResolved targetDropped, ?_⟩
  exact .related (fun left right => left = right) (.contents outputHeap)
    outputFuel
    (.running (.rewritten rewrite frame.advance) stack)

/-! ## Exhaustive unchanged-block dispatch -/

set_option maxHeartbeats 1000000 in
/-- Every successful instruction in an unchanged block is equivariant under
an arbitrary allocation-history isomorphism. -/
theorem unchangedInstructionStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {instruction : Instr} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instructionAt : block.instructions[baselineFrame.pc] = instruction)
    (classified : InstructionTransferCase
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFrame baselineStack
      instruction baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  let baselineContext :=
    Eval.Context.ofProgram sourceProgram validation.schemas oracle
  let rewrittenContext :=
    Eval.Context.ofProgram trace.target validation.schemas oracle
  cases classified with
  | move resolved =>
      obtain ⟨rewrittenValue, sourceStep, targetStep, related⟩ :=
        unchangedMoveStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved
      exact ⟨_, sourceStep, targetStep, related⟩
  | alloc schemaAt resolved fields =>
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedAllocStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
      exact ⟨_, sourceStep, targetStep, related⟩
  | allocWithAbsent schemaAt resolved fields taken layout absent =>
      obtain ⟨rewrittenValues, rewrittenTaken, sourceStep, targetStep,
          related⟩ :=
        unchangedAllocWithAbsentStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
          taken layout absent
      exact ⟨_, sourceStep, targetStep, related⟩
  | allocWithLogical mode schemaAt resolved fields taken layout present =>
      cases mode
      obtain ⟨rewrittenValues, rewrittenTaken, sourceStep, targetStep,
          related⟩ :=
        unchangedAllocWithLogicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
          taken layout present
      exact ⟨_, sourceStep, targetStep, related⟩
  | allocWithPhysical mode schemaAt resolved fields taken layout present
      reused =>
      cases mode
      obtain ⟨rewrittenValues, rewrittenTaken, rewrittenLocation,
          rewrittenOut, targetReused, sourceStep, targetStep, related⟩ :=
        unchangedAllocWithPhysicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
          taken layout present reused
      exact ⟨_, sourceStep, targetStep, related⟩
  | discardAbsent taken absent =>
      obtain ⟨rewrittenTaken, sourceStep, targetStep, related⟩ :=
        unchangedDiscardCreditAbsentStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt taken absent
      exact ⟨_, sourceStep, targetStep, related⟩
  | discardLogical mode taken present =>
      cases mode
      obtain ⟨rewrittenTaken, sourceStep, targetStep, related⟩ :=
        unchangedDiscardCreditLogicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt taken present
      exact ⟨_, sourceStep, targetStep, related⟩
  | discardPhysical mode taken present released =>
      cases mode
      obtain ⟨rewrittenTaken, rewrittenLocation, rewrittenOut,
          targetReleased, sourceStep, targetStep, related⟩ :=
        unchangedDiscardCreditPhysicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt taken present released
      exact ⟨_, sourceStep, targetStep, related⟩
  | takeUniqueLogical mode schemaAt resolved viewed unitRC =>
      cases mode
      obtain ⟨rewrittenLocation, rewrittenFields, sourceStep, targetStep,
          related⟩ :=
        unchangedTakeUniqueLogicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          unitRC
      exact ⟨_, sourceStep, targetStep, related⟩
  | takeUniquePhysical mode schemaAt resolved viewed unitRC =>
      cases mode
      obtain ⟨rewrittenLocation, rewrittenFields, sourceStep, targetStep,
          related⟩ :=
        unchangedTakeUniquePhysicalStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          unitRC
      exact ⟨_, sourceStep, targetStep, related⟩
  | resetSharedLogicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      obtain ⟨rewrittenLocation, rewrittenFields, sourceStep, targetStep,
          related⟩ :=
        unchangedResetSharedLogicalHotStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          unitRC
      exact ⟨_, sourceStep, targetStep, related⟩
  | resetSharedPhysicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      obtain ⟨rewrittenLocation, rewrittenFields, sourceStep, targetStep,
          related⟩ :=
        unchangedResetSharedPhysicalHotStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          unitRC
      exact ⟨_, sourceStep, targetStep, related⟩
  | resetSharedCold schemaAt resolved viewed shared retained =>
      obtain ⟨rewrittenFields, rewrittenOut, sourceStep, targetStep,
          related⟩ :=
        unchangedResetSharedColdStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          shared retained
      exact ⟨_, sourceStep, targetStep, related⟩
  | retainShared resolved retained =>
      obtain ⟨rewrittenValue, rewrittenOut, targetRetained, sourceStep,
          targetStep, related⟩ :=
        unchangedRetainSharedStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved retained
      exact ⟨_, sourceStep, targetStep, related⟩
  | releaseShared resolved released =>
      obtain ⟨rewrittenValue, rewrittenOut, rewrittenRemaining,
          targetReleased, sourceStep, targetStep, related⟩ :=
        unchangedReleaseSharedStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved released
      exact ⟨_, sourceStep, targetStep, related⟩
  | dropUnique resolved dropped =>
      obtain ⟨rewrittenValue, rewrittenOut, rewrittenRemaining,
          targetDropped, sourceStep, targetStep, related⟩ :=
        unchangedDropUniqueStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved dropped
      exact ⟨_, sourceStep, targetStep, related⟩
  | freeUnique resolved viewed scalarFields =>
      obtain ⟨boxAt, unique, node⟩ := viewed.parts
      obtain ⟨rewrittenLocation, sourceStep, targetStep, related⟩ :=
        unchangedFreeUniqueStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved boxAt unique node
          scalarFields
      exact ⟨_, sourceStep, targetStep, related⟩
  | fetch resolved boxAt node fieldAt =>
      obtain ⟨rewrittenValue, sourceStep, targetStep, related⟩ :=
        unchangedFetchStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved boxAt node fieldAt
      exact ⟨_, sourceStep, targetStep, related⟩
  | callFn noCredits resolved declaration arity nonempty =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedCallFnStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
          frame stack sourceAt targetAt pc instructionAt noCredits resolved
          declaration targetDeclaration arity nonempty
      exact ⟨_, sourceStep, targetStep, related⟩
  | callSelf noCredits resolved arity nonempty =>
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedCallSelfStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt noCredits resolved arity nonempty
      exact ⟨_, sourceStep, targetStep, related⟩
  | pappFn noCredits declaration papSafe resolved under =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedPappFnStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
          frame stack sourceAt targetAt pc instructionAt noCredits declaration
          targetDeclaration papSafe resolved under
      exact ⟨_, sourceStep, targetStep, related⟩
  | pappExtern noCredits declaration resolved under =>
      have targetDeclaration := trace.context_extern declaration
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedPappExternStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt noCredits declaration
          targetDeclaration resolved under
      exact ⟨_, sourceStep, targetStep, related⟩
  | apply noCredits functionResolved argumentsResolved transferred =>
      exact unchangedApplyStepOfTraceIso trace rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt noCredits functionResolved
        argumentsResolved transferred
  | extern noCredits resolved declaration argumentArity called =>
      have targetDeclaration := trace.context_extern declaration
      obtain ⟨sourceStep, targetStep, related⟩ :=
        unchangedExternStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          rfl sourceAt targetAt pc instructionAt noCredits resolved declaration
          targetDeclaration argumentArity called
      exact ⟨_, sourceStep, targetStep, related⟩

set_option maxHeartbeats 1000000 in
/-- Every successful instruction in an unchanged block has a matching target
step and a stable exact-content successor.  The public evaluator case witness
is exhaustive; the whole-program trace supplies any rewritten function or
preserved extern declaration selected dynamically. -/
theorem unchangedInstructionStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {instruction : Instr} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc < block.instructions.size)
    (instructionAt : block.instructions[baselineFrame.pc] = instruction)
    (classified : InstructionTransferCase
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFrame baselineStack
      instruction baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  let baselineContext :=
    Eval.Context.ofProgram sourceProgram validation.schemas oracle
  let rewrittenContext :=
    Eval.Context.ofProgram trace.target validation.schemas oracle
  cases classified with
  | move resolved =>
      exact ⟨_, unchangedMoveStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt resolved⟩
  | alloc schemaAt resolved fields =>
      obtain ⟨sourceStep, targetStep, related⟩ :=
        unchangedAllocStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
      exact ⟨_, sourceStep, targetStep, related⟩
  | allocWithAbsent schemaAt resolved fields taken layout absent =>
      exact ⟨_, unchangedAllocWithAbsentStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved fields
        taken layout absent⟩
  | allocWithLogical mode schemaAt resolved fields taken layout present =>
      cases mode
      exact ⟨_, unchangedAllocWithLogicalStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved fields
        taken layout present⟩
  | allocWithPhysical mode schemaAt resolved fields taken layout present
      reused =>
      cases mode
      obtain ⟨rewrittenOut, targetReused, sourceStep, targetStep, related⟩ :=
        unchangedAllocWithPhysicalStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved fields
          taken layout present reused
      exact ⟨_, sourceStep, targetStep, related⟩
  | discardAbsent taken absent =>
      exact ⟨_, unchangedDiscardCreditAbsentStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt taken absent⟩
  | discardLogical mode taken present =>
      cases mode
      exact ⟨_, unchangedDiscardCreditLogicalStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt taken present⟩
  | discardPhysical mode taken present released =>
      cases mode
      obtain ⟨rewrittenOut, targetReleased, sourceStep, targetStep, related⟩ :=
        unchangedDiscardCreditPhysicalStep
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt taken present released
      exact ⟨_, sourceStep, targetStep, related⟩
  | takeUniqueLogical mode schemaAt resolved viewed unitRC =>
      cases mode
      exact ⟨_, unchangedTakeUniqueLogicalStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
        unitRC⟩
  | takeUniquePhysical mode schemaAt resolved viewed unitRC =>
      cases mode
      exact ⟨_, unchangedTakeUniquePhysicalStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
        unitRC⟩
  | resetSharedLogicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      exact ⟨_, unchangedResetSharedLogicalHotStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
        unitRC⟩
  | resetSharedPhysicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      exact ⟨_, unchangedResetSharedPhysicalHotStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
        stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
        unitRC⟩
  | resetSharedCold schemaAt resolved viewed shared retained =>
      obtain ⟨rewrittenOut, targetRetained, sourceStep, targetStep, related⟩ :=
        unchangedResetSharedColdStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite rfl heap fuel frame
          stack sourceAt targetAt pc instructionAt schemaAt resolved viewed
          shared retained
      exact ⟨_, sourceStep, targetStep, related⟩
  | retainShared resolved retained =>
      obtain ⟨rewrittenOut, targetRetained, sourceStep, targetStep, related⟩ :=
        unchangedRetainSharedStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved retained
      exact ⟨_, sourceStep, targetStep, related⟩
  | releaseShared resolved released =>
      obtain ⟨rewrittenOut, rewrittenRemaining, targetReleased, sourceStep,
          targetStep, related⟩ :=
        unchangedReleaseSharedStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved released
      exact ⟨_, sourceStep, targetStep, related⟩
  | dropUnique resolved dropped =>
      obtain ⟨rewrittenOut, rewrittenRemaining, targetDropped, sourceStep,
          targetStep, related⟩ :=
        unchangedDropUniqueStep (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt resolved dropped
      exact ⟨_, sourceStep, targetStep, related⟩
  | freeUnique resolved viewed scalarFields =>
      obtain ⟨boxAt, unique, node⟩ := viewed.parts
      exact ⟨_, unchangedFreeUniqueStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt resolved boxAt unique node
        scalarFields⟩
  | fetch resolved boxAt node fieldAt =>
      exact ⟨_, unchangedFetchStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt resolved boxAt node fieldAt⟩
  | callFn noCredits resolved declaration arity nonempty =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      exact ⟨_, unchangedCallFnStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
        frame stack sourceAt targetAt pc instructionAt noCredits resolved
        declaration targetDeclaration arity nonempty⟩
  | callSelf noCredits resolved arity nonempty =>
      exact ⟨_, unchangedCallSelfStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt noCredits resolved arity nonempty⟩
  | pappFn noCredits declaration papSafe resolved under =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      exact ⟨_, unchangedPappFnStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
        frame stack sourceAt targetAt pc instructionAt noCredits declaration
        targetDeclaration papSafe resolved under⟩
  | pappExtern noCredits declaration resolved under =>
      have targetDeclaration := trace.context_extern declaration
      exact ⟨_, unchangedPappExternStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt noCredits declaration
        targetDeclaration resolved under⟩
  | apply noCredits functionResolved argumentsResolved transferred =>
      exact unchangedApplyStepOfTrace trace rewrite heap fuel frame stack
        sourceAt targetAt pc instructionAt noCredits functionResolved
        argumentsResolved transferred
  | extern noCredits resolved declaration argumentArity called =>
      have targetDeclaration := trace.context_extern declaration
      exact ⟨_, unchangedExternStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        rfl sourceAt targetAt pc instructionAt noCredits resolved declaration
        targetDeclaration argumentArity called⟩

/-! ## Allocation-history unchanged terminators -/

/-- An unchanged jump transports related explicit values and linear credits
through the selected target-block ABI. -/
theorem unchangedJumpStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {edge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .jump edge)
    (transferred : EdgeTransfer baselineFrame edge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransferIso (.nil) transferred
  refine ⟨rewrittenTarget,
    Step.jump rfl sourceAt pc terminator transferred,
    Step.jump rfl targetAt targetPc terminator rewrittenTransfer, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- The zero arm of a Nat switch preserves its literal observation and
transports the selected edge under the heap history. -/
theorem unchangedSwitchNatZeroStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {peel : NatPeel}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.lit (.nat 0)))
    (transferred : EdgeTransfer baselineFrame peel.zero #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases valueRelated with
  | lit =>
      have targetPc : rewrittenFrame.pc = block.instructions.size :=
        frame.pc.symm.trans pc
      obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
        frame.edgeTransferIso (.nil) transferred
      refine ⟨rewrittenTarget,
        Step.switchNatZero rfl sourceAt pc terminator resolved transferred,
        Step.switchNatZero rfl targetAt targetPc terminator targetResolved
          rewrittenTransfer, ?_⟩
      exact StableMachineRel.history heap fuel
        (.running (.rewritten rewrite targetFrame) stack)

/-- The successor arm preserves its scalar predecessor and transports the
selected edge under the heap history. -/
theorem unchangedSwitchNatSuccStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {peel : NatPeel} {predecessor : Nat}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (transferred : EdgeTransfer baselineFrame peel.succ
      #[.lit (.nat predecessor)] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases valueRelated with
  | lit =>
      have targetPc : rewrittenFrame.pc = block.instructions.size :=
        frame.pc.symm.trans pc
      obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
        frame.edgeTransferIso (.cons .lit .nil) transferred
      refine ⟨rewrittenTarget,
        Step.switchNatSucc rfl sourceAt pc terminator resolved transferred,
        Step.switchNatSucc rfl targetAt targetPc terminator targetResolved
          rewrittenTransfer, ?_⟩
      exact StableMachineRel.history heap fuel
        (.running (.rewritten rewrite targetFrame) stack)

/-- Constructor dispatch follows the related scrutinee location, observes a
constructor with the same identity, and transports its selected edge. -/
theorem unchangedSwitchCtorStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {scrutinee : Atom} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {baselineLocation : Nat} {box : NodeBox}
    {cid : CtorId} {fields : Array RVal} {alternative : CtorAlt}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors natPeel)
    (resolved : resolveAtom baselineFrame.values scrutinee =
      .ok (.loc baselineLocation))
    (boxAt : baselineStore.get? baselineLocation = some box)
    (node : box.node = .ctorN cid fields)
    (alternativeAt : constructors.find? (fun candidate =>
      candidate.cid == cid) = some alternative)
    (transferred : EdgeTransfer baselineFrame alternative.edge #[]
      baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  cases valueRelated with
  | @loc _ rewrittenLocation locations =>
      obtain ⟨rewrittenBox, targetBoxAt, boxesRelated⟩ :=
        heap.boxes locations (by
          change baselineStore.heap.get? baselineLocation = some box
          exact boxAt)
      have nodesRelated : IxIR1.Sim.NodeIso heap.locRel
          (.ctorN cid fields) rewrittenBox.node := by
        rw [← node]
        exact boxesRelated.node
      obtain ⟨rewrittenFields, targetNode, _fieldsRelated⟩ :=
        nodeIso_ctor_left nodesRelated
      have targetPc : rewrittenFrame.pc = block.instructions.size :=
        frame.pc.symm.trans pc
      obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
        frame.edgeTransferIso (.nil) transferred
      refine ⟨rewrittenTarget,
        Step.switchCtor rfl sourceAt pc terminator resolved boxAt node
          alternativeAt transferred,
        Step.switchCtor rfl targetAt targetPc terminator targetResolved
          (by
            change rewrittenStore.heap.get? rewrittenLocation =
              some rewrittenBox
            exact targetBoxAt)
          targetNode alternativeAt rewrittenTransfer, ?_⟩
      exact StableMachineRel.history heap fuel
        (.running (.rewritten rewrite targetFrame) stack)

/-- A present optional credit selects the corresponding target branch; the
credit itself and all credits transferred by the edge may carry related
physical addresses. -/
theorem unchangedBranchCreditPresentStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {someEdge noneEdge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup baselineFrame creditId credit)
    (present : credit.isPresent = true)
    (transferred : EdgeTransfer baselineFrame someEdge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  obtain ⟨rewrittenCredit, targetLookup, creditRelated⟩ :=
    frame.creditLookup lookedUp
  have targetPresent : rewrittenCredit.isPresent = true := by
    rw [← creditRelated.present_parts.2]
    exact present
  obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransferIso (.nil) transferred
  refine ⟨rewrittenTarget,
    Step.branchCreditPresent rfl sourceAt pc terminator lookedUp present
      transferred,
    Step.branchCreditPresent rfl targetAt targetPc terminator targetLookup
      targetPresent rewrittenTransfer, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- An absent optional credit selects the fallback target branch under the
same relation-aware edge transfer. -/
theorem unchangedBranchCreditAbsentStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineTarget : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {creditId : CreditId} {credit : Credit}
    {someEdge noneEdge : Edge}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup baselineFrame creditId credit)
    (absent : credit.isPresent = false)
    (transferred : EdgeTransfer baselineFrame noneEdge #[] baselineTarget) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with control := .running baselineTarget baselineStack }
    ∃ rewrittenTarget : Frame,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running rewrittenTarget rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  obtain ⟨rewrittenCredit, targetLookup, creditRelated⟩ :=
    frame.creditLookup lookedUp
  have targetAbsent : rewrittenCredit.isPresent = false := by
    rw [← creditRelated.present_parts.2]
    exact absent
  obtain ⟨rewrittenTarget, rewrittenTransfer, targetFrame⟩ :=
    frame.edgeTransferIso (.nil) transferred
  refine ⟨rewrittenTarget,
    Step.branchCreditAbsent rfl sourceAt pc terminator lookedUp absent
      transferred,
    Step.branchCreditAbsent rfl targetAt targetPc terminator targetLookup
      targetAbsent rewrittenTransfer, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (.rewritten rewrite targetFrame) stack)

/-- A recursive tail call resolves a related argument vector and re-enters
the two versions of the current function without changing the related stack. -/
theorem unchangedTailCallSelfStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {arguments : Array Atom}
    {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCallSelf arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (arity : baselineValues.size =
      baselineFrame.definition.signature.params.size)
    (nonempty : baselineFrame.definition.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := baselineFrame.definition, values := baselineValues }
          baselineStack }
    ∃ rewrittenValues,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { definition := rewrittenFrame.definition,
              values := rewrittenValues }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits := frame.noLiveCredits noCredits
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have sourceArity : baselineValues.size = source.signature.params.size := by
    simpa [frame.baselineDefinition] using arity
  have targetArity : rewrittenValues.size =
      rewrittenFrame.definition.signature.params.size := by
    rw [← sizeEq, frame.rewrittenDefinition, rewrite.definition_signature]
    exact sourceArity
  have targetNonempty : rewrittenFrame.definition.blocks.isEmpty = false :=
    blocks_nonempty_of_getElem targetAt
  refine ⟨rewrittenValues,
    Step.tailCallSelfCleared rfl sourceAt pc terminator noCredits resolved
      arity nonempty,
    Step.tailCallSelfCleared rfl targetAt targetPc terminator targetNoCredits
      targetResolved targetArity targetNonempty, ?_⟩
  have callee : StableFrameRel limits validation heap.locRel
      { definition := baselineFrame.definition, values := baselineValues }
      { definition := rewrittenFrame.definition, values := rewrittenValues } := by
    rw [frame.baselineDefinition, frame.rewrittenDefinition]
    exact StableFrameRel.entry rewrite valuesRelated
  exact StableMachineRel.history heap fuel (.running callee stack)

/-- A direct tail call follows the declaration rewrite at the same address
and enters the related callee argument vectors. -/
theorem unchangedTailCallFnStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {callerSource calleeSource : Function}
    (callerRewrite : Reuse.FunctionRewrite limits validation callerSource)
    (calleeRewrite : Reuse.FunctionRewrite limits validation calleeSource)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso callerRewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {address : Ix.Compiler.Ixon.Address}
    {arguments : Array Atom} {baselineValues : Array RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCall address arguments)
    (noCredits : NoLiveCredits baselineFrame)
    (resolved : resolveAtoms baselineFrame.values arguments =
      .ok baselineValues)
    (baselineDeclaration : baselineContext.declarations address =
      some (.fn calleeSource))
    (rewrittenDeclaration : rewrittenContext.declarations address =
      some (.fn calleeRewrite.definition))
    (arity : baselineValues.size = calleeSource.signature.params.size)
    (nonempty : calleeSource.blocks.isEmpty = false) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { definition := calleeSource, values := baselineValues }
          baselineStack }
    ∃ rewrittenValues,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { definition := calleeRewrite.definition,
              values := rewrittenValues }
            rewrittenStack }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValues, targetResolved, valuesRelated⟩ :=
    resolveAtoms_iso frame.values resolved
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits := frame.noLiveCredits noCredits
  have sizeEq : baselineValues.size = rewrittenValues.size := by
    simpa using rvalsIso_length_eq valuesRelated
  have targetArity : rewrittenValues.size =
      calleeRewrite.definition.signature.params.size := by
    rw [← sizeEq]
    simpa using arity
  have targetNonempty : calleeRewrite.definition.blocks.isEmpty = false :=
    calleeRewrite.definition_blocks_nonempty nonempty
  refine ⟨rewrittenValues,
    Step.tailCallFnCleared rfl sourceAt pc terminator noCredits resolved
      baselineDeclaration arity nonempty,
    Step.tailCallFnCleared rfl targetAt targetPc terminator targetNoCredits
      targetResolved rewrittenDeclaration targetArity targetNonempty, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (StableFrameRel.entry calleeRewrite valuesRelated) stack)

/-- An ordinary return resolves related results, transports the result-world
check through the heap history, and pushes them into related suspended
callers. -/
theorem unchangedRetResumeStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineCaller rewrittenCaller : Frame}
    {baselineRest rewrittenRest : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (caller : StableFrameRel limits validation heap.locRel
      baselineCaller rewrittenCaller)
    (rest : StableStackIso limits validation heap.locRel
      baselineRest rewrittenRest)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (noCredits : NoLiveCredits baselineFrame)
    (world : baselineValue.hasWorld baselineStore
      baselineFrame.definition.signature.result = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame
          (.resume baselineCaller :: baselineRest) }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame
          (.resume rewrittenCaller :: rewrittenRest) }
    let baselineNext : Machine :=
      { baselineMachine with
        control := .running
          { baselineCaller with
            values := baselineCaller.values.push baselineValue }
          baselineRest }
    ∃ rewrittenValue,
      let rewrittenNext : Machine :=
        { rewrittenMachine with
          control := .running
            { rewrittenCaller with
              values := rewrittenCaller.values.push rewrittenValue }
            rewrittenRest }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits := frame.noLiveCredits noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : rewrittenValue.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq,
      ← heapHistoryIso_rvalHasWorld_eq heap valueRelated]
    exact world
  refine ⟨rewrittenValue,
    Step.retResumeCleared rfl sourceAt pc terminator resolved noCredits world,
    Step.retResumeCleared rfl targetAt targetPc terminator targetResolved
      targetNoCredits targetWorld, ?_⟩
  exact StableMachineRel.history heap fuel
    (.running (caller.push valueRelated) rest)

/-- An outermost return halts with related results after transporting the
callee result-world check through the heap history. -/
theorem unchangedRetHaltStepIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (noCredits : NoLiveCredits baselineFrame)
    (world : baselineValue.hasWorld baselineStore
      baselineFrame.definition.signature.result = true) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame [] }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame [] }
    let baselineNext : Machine :=
      { baselineMachine with control := .halted baselineValue }
    ∃ rewrittenValue,
      let rewrittenNext : Machine :=
        { rewrittenMachine with control := .halted rewrittenValue }
      Step baselineContext interpretation baselineMachine baselineNext ∧
        Step rewrittenContext interpretation rewrittenMachine rewrittenNext ∧
        StableMachineRel limits validation baselineNext rewrittenNext := by
  dsimp only
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits := frame.noLiveCredits noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : rewrittenValue.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq,
      ← heapHistoryIso_rvalHasWorld_eq heap valueRelated]
    exact world
  refine ⟨rewrittenValue,
    Step.retHaltCleared rfl sourceAt pc terminator resolved noCredits world,
    Step.retHaltCleared rfl targetAt targetPc terminator targetResolved
      targetNoCredits targetWorld, ?_⟩
  exact StableMachineRel.history heap fuel (.halted valueRelated)

/-- A return through `applyMore` resolves related return values and feeds the
related saved argument vectors through the exhaustive dynamic application
simulation. -/
theorem unchangedRetApplyMoreStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame baselineCaller rewrittenCaller : Frame}
    {baselineArguments rewrittenArguments : Array RVal}
    {baselineRest rewrittenRest : List Continuation}
    {baselineTarget : Machine}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (arguments : IxIR1.Sim.RValsIso heap.locRel
      baselineArguments.toList rewrittenArguments.toList)
    (caller : StableFrameRel limits validation heap.locRel
      baselineCaller rewrittenCaller)
    (rest : StableStackIso limits validation heap.locRel
      baselineRest rewrittenRest)
    {block : Block} {atom : Atom} {baselineValue : RVal}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom baselineFrame.values atom = .ok baselineValue)
    (noCredits : NoLiveCredits baselineFrame)
    (world : baselineValue.hasWorld baselineStore
      baselineFrame.definition.signature.result = true)
    (transferred : ApplyTransfer
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineValue
      baselineArguments baselineCaller baselineRest baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame
              (.applyMore baselineArguments baselineCaller :: baselineRest) }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame
              (.applyMore rewrittenArguments rewrittenCaller ::
                rewrittenRest) }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  obtain ⟨rewrittenValue, targetResolved, valueRelated⟩ :=
    resolveAtom_iso frame.values resolved
  have targetPc : rewrittenFrame.pc = block.instructions.size :=
    frame.pc.symm.trans pc
  have targetNoCredits := frame.noLiveCredits noCredits
  have resultWorldEq : rewrittenFrame.definition.signature.result =
      baselineFrame.definition.signature.result := by
    rw [frame.rewrittenDefinition, rewrite.definition_signature,
      frame.baselineDefinition]
  have targetWorld : rewrittenValue.hasWorld rewrittenStore
      rewrittenFrame.definition.signature.result = true := by
    rw [resultWorldEq,
      ← heapHistoryIso_rvalHasWorld_eq heap valueRelated]
    exact world
  obtain ⟨rewrittenTarget, targetTransferred, related⟩ :=
    unchangedApplyTransferIso trace heap fuel valueRelated arguments caller
      rest transferred
  refine ⟨rewrittenTarget,
    Step.retApplyMoreCleared rfl sourceAt pc terminator resolved noCredits
      world transferred,
    Step.retApplyMoreCleared rfl targetAt targetPc terminator targetResolved
      targetNoCredits targetWorld targetTransferred,
    related⟩

set_option maxHeartbeats 1000000 in
/-- Every successful terminator in an unchanged block is equivariant under
an arbitrary allocation-history isomorphism. -/
theorem unchangedTerminatorStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {terminator : Terminator} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminatorAt : block.terminator = terminator)
    (classified : TerminatorTransferCase
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFrame baselineStack
      terminator baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  let baselineContext :=
    Eval.Context.ofProgram sourceProgram validation.schemas oracle
  let rewrittenContext :=
    Eval.Context.ofProgram trace.target validation.schemas oracle
  cases classified with
  | jump transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedJumpStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | switchCtor resolved boxAt node alternativeAt transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedSwitchCtorStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt resolved boxAt node alternativeAt
          transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | switchNatZero resolved transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedSwitchNatZeroStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt resolved transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | switchNatSucc resolved transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedSwitchNatSuccStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt resolved transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | branchPresent lookedUp present transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedBranchCreditPresentStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt lookedUp present transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | branchAbsent lookedUp absent transferred =>
      obtain ⟨rewrittenFrameTarget, sourceStep, targetStep, related⟩ :=
        unchangedBranchCreditAbsentStepIso
          (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt lookedUp absent transferred
      exact ⟨_, sourceStep, targetStep, related⟩
  | retResume resolved noCredits world =>
      cases stack with
      | cons head rest =>
          cases head with
          | resume caller =>
              obtain ⟨rewrittenValue, sourceStep, targetStep, related⟩ :=
                unchangedRetResumeStepIso
                  (baselineContext := baselineContext)
                  (rewrittenContext := rewrittenContext) rewrite heap fuel
                  frame caller rest sourceAt targetAt pc terminatorAt resolved
                  noCredits world
              exact ⟨_, sourceStep, targetStep, related⟩
  | retHalt resolved noCredits world =>
      cases stack
      obtain ⟨rewrittenValue, sourceStep, targetStep, related⟩ :=
        unchangedRetHaltStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame
          sourceAt targetAt pc terminatorAt resolved noCredits world
      exact ⟨_, sourceStep, targetStep, related⟩
  | retApplyMore resolved noCredits world transferred =>
      cases stack with
      | cons head rest =>
          cases head with
          | applyMore arguments caller =>
              exact unchangedRetApplyMoreStepOfTraceIso trace rewrite heap
                fuel frame arguments caller rest sourceAt targetAt pc
                terminatorAt resolved noCredits world transferred
  | tailCallFn noCredits resolved declaration arity nonempty =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedTailCallFnStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
          frame stack sourceAt targetAt pc terminatorAt noCredits resolved
          declaration targetDeclaration arity nonempty
      exact ⟨_, sourceStep, targetStep, related⟩
  | tailCallSelf noCredits resolved arity nonempty =>
      obtain ⟨rewrittenValues, sourceStep, targetStep, related⟩ :=
        unchangedTailCallSelfStepIso (baselineContext := baselineContext)
          (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt noCredits resolved arity nonempty
      exact ⟨_, sourceStep, targetStep, related⟩

/-- A source step at a literally preserved block is matched under any
allocation-history isomorphism.  Instruction and terminator classification
remain entirely behind the public evaluator interfaces. -/
theorem unchangedStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {block : Block} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (stepped : Step
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  have classified := stepped.classify
  cases classified with
  | instruction classifiedAt pc instructionAt instructionCase =>
      have blockEq := Option.some.inj (classifiedAt.symm.trans sourceAt)
      cases blockEq
      obtain ⟨rewrittenTarget, _sourceStep, targetStep, related⟩ :=
        unchangedInstructionStepOfTraceIso trace rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt instructionCase
      exact ⟨rewrittenTarget, targetStep, related⟩
  | terminator classifiedAt pc terminatorAt terminatorCase =>
      have blockEq := Option.some.inj (classifiedAt.symm.trans sourceAt)
      cases blockEq
      obtain ⟨rewrittenTarget, _sourceStep, targetStep, related⟩ :=
        unchangedTerminatorStepOfTraceIso trace rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt terminatorCase
      exact ⟨rewrittenTarget, targetStep, related⟩

/-- Every successful terminator in an unchanged block has a matching target
step and stable successor.  Indexed stack cases expose ordinary returns,
outermost returns, and over-application returns without any private evaluator
unfolding. -/
theorem unchangedTerminatorStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {terminator : Terminator} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (pc : baselineFrame.pc = block.instructions.size)
    (terminatorAt : block.terminator = terminator)
    (classified : TerminatorTransferCase
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation baselineStore baselineFuel baselineFrame baselineStack
      terminator baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          baselineTarget ∧
        Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  let baselineContext :=
    Eval.Context.ofProgram sourceProgram validation.schemas oracle
  let rewrittenContext :=
    Eval.Context.ofProgram trace.target validation.schemas oracle
  cases classified with
  | jump transferred =>
      exact ⟨_, unchangedJumpStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt transferred⟩
  | switchCtor resolved boxAt node alternativeAt transferred =>
      exact ⟨_, unchangedSwitchCtorStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt resolved boxAt node alternativeAt
        transferred⟩
  | switchNatZero resolved transferred =>
      exact ⟨_, unchangedSwitchNatZeroStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt resolved transferred⟩
  | switchNatSucc resolved transferred =>
      exact ⟨_, unchangedSwitchNatSuccStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt resolved transferred⟩
  | branchPresent lookedUp present transferred =>
      exact ⟨_, unchangedBranchCreditPresentStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt lookedUp present transferred⟩
  | branchAbsent lookedUp absent transferred =>
      exact ⟨_, unchangedBranchCreditAbsentStep
        (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt lookedUp absent transferred⟩
  | retResume resolved noCredits world =>
      cases stack with
      | cons head rest =>
          cases head with
          | resume caller =>
              exact ⟨_, unchangedRetResumeStep
                (baselineContext := baselineContext)
                (rewrittenContext := rewrittenContext) rewrite heap fuel frame
                caller rest sourceAt targetAt pc terminatorAt resolved
                noCredits world⟩
  | retHalt resolved noCredits world =>
      cases stack
      exact ⟨_, unchangedRetHaltStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame sourceAt
        targetAt pc terminatorAt resolved noCredits world⟩
  | retApplyMore resolved noCredits world transferred =>
      cases stack with
      | cons head rest =>
          cases head with
          | applyMore arguments caller =>
              have argumentsEq := arguments.eq_of_location_eq
              have arraysEq := Array.toList_inj.mp argumentsEq
              subst_vars
              exact unchangedRetApplyMoreStepOfTrace trace rewrite heap fuel
                frame caller rest sourceAt targetAt pc terminatorAt resolved
                noCredits world transferred
  | tailCallFn noCredits resolved declaration arity nonempty =>
      obtain ⟨calleeRewrite, targetDeclaration⟩ :=
        trace.context_fn declaration
      exact ⟨_, unchangedTailCallFnStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite calleeRewrite heap fuel
        frame stack sourceAt targetAt pc terminatorAt noCredits resolved
        declaration targetDeclaration arity nonempty⟩
  | tailCallSelf noCredits resolved arity nonempty =>
      exact ⟨_, unchangedTailCallSelfStep (baselineContext := baselineContext)
        (rewrittenContext := rewrittenContext) rewrite heap fuel frame stack
        sourceAt targetAt pc terminatorAt noCredits resolved arity nonempty⟩

/-- A single public source step at a literally preserved block is matched by
one target step.  This is the whole-step unchanged arm: evaluator inversion,
instruction/terminator dispatch, declarations, heap effects, fuel, frames,
and continuation stacks are all discharged below this interface. -/
theorem unchangedStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {block : Block} {baselineTarget : Machine}
    (sourceAt : baselineFrame.definition.blocks[baselineFrame.block]? =
      some block)
    (targetAt : rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
      some block)
    (stepped : Step
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      baselineTarget) :
    ∃ rewrittenTarget,
      Step (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }
          rewrittenTarget ∧
        StableMachineRel limits validation baselineTarget rewrittenTarget := by
  have classified := stepped.classify
  cases classified with
  | instruction classifiedAt pc instructionAt instructionCase =>
      have blockEq := Option.some.inj (classifiedAt.symm.trans sourceAt)
      cases blockEq
      obtain ⟨rewrittenTarget, _sourceStep, targetStep, related⟩ :=
        unchangedInstructionStepOfTrace trace rewrite heap fuel frame stack
          sourceAt targetAt pc instructionAt instructionCase
      exact ⟨rewrittenTarget, targetStep, related⟩
  | terminator classifiedAt pc terminatorAt terminatorCase =>
      have blockEq := Option.some.inj (classifiedAt.symm.trans sourceAt)
      cases blockEq
      obtain ⟨rewrittenTarget, _sourceStep, targetStep, related⟩ :=
        unchangedTerminatorStepOfTrace trace rewrite heap fuel frame stack
          sourceAt targetAt pc terminatorAt terminatorCase
      exact ⟨rewrittenTarget, targetStep, related⟩

/-- A synchronization-sized transition: each machine takes a positive finite
number of genuine running steps and the two endpoints satisfy the uniform
stable relation.  Unchanged blocks use one step on each side; an accepted
reset/reuse block uses its complete source and replacement macros. -/
inductive StableMacroSimulation (limits : Validate.Limits)
    (validation : Validate.Context) (baselineContext rewrittenContext :
      Eval.Context) (interpretation : Interpretation)
    (baselineStart rewrittenStart : Machine) : Prop where
  | intro (baselineCount rewrittenCount : Nat)
      (baselinePositive : 0 < baselineCount)
      (rewrittenPositive : 0 < rewrittenCount)
      (baselineTarget rewrittenTarget : Machine)
      (baselineSteps : Steps baselineContext interpretation baselineCount
        baselineStart baselineTarget)
      (rewrittenSteps : Steps rewrittenContext interpretation rewrittenCount
        rewrittenStart rewrittenTarget)
      (related : StableMachineRel limits validation baselineTarget
        rewrittenTarget)

/-- One synchronization macro together with preservation of a caller-chosen
global runtime invariant.  Keeping the concrete endpoints in this relation
lets finite-run induction cancel the multi-step baseline prefix and recurse
from the exact synchronized states. -/
inductive StableMacroInvariantStep (limits : Validate.Limits)
    (validation : Validate.Context) (baselineContext rewrittenContext :
      Eval.Context) (interpretation : Interpretation)
    (invariant : Machine → Machine → Prop)
    (baselineStart rewrittenStart : Machine) : Prop where
  | intro (baselineCount rewrittenCount : Nat)
      (baselinePositive : 0 < baselineCount)
      (rewrittenPositive : 0 < rewrittenCount)
      (baselineTarget rewrittenTarget : Machine)
      (baselineSteps : Steps baselineContext interpretation baselineCount
        baselineStart baselineTarget)
      (rewrittenSteps : Steps rewrittenContext interpretation rewrittenCount
        rewrittenStart rewrittenTarget)
      (related : StableMachineRel limits validation baselineTarget
        rewrittenTarget)
      (preserved : invariant baselineTarget rewrittenTarget)

/-- Forget invariant preservation and recover the ordinary synchronization
macro consumed by local simulation clients. -/
theorem StableMacroInvariantStep.simulation {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {invariant : Machine → Machine → Prop}
    {baselineStart rewrittenStart : Machine}
    (step : StableMacroInvariantStep limits validation baselineContext
      rewrittenContext interpretation invariant baselineStart
      rewrittenStart) :
    StableMacroSimulation limits validation baselineContext rewrittenContext
      interpretation baselineStart rewrittenStart := by
  cases step with
  | intro baselineCount rewrittenCount baselinePositive rewrittenPositive
      baselineTarget rewrittenTarget baselineSteps rewrittenSteps related
      _preserved =>
      exact .intro baselineCount rewrittenCount baselinePositive
        rewrittenPositive baselineTarget rewrittenTarget baselineSteps
        rewrittenSteps related

/-- Strengthen a synchronization macro once the global invariant has been
proved at every endpoint exposed by that macro. -/
theorem StableMacroSimulation.preserveInvariant {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {invariant : Machine → Machine → Prop}
    {baselineStart rewrittenStart : Machine}
    (simulation : StableMacroSimulation limits validation baselineContext
      rewrittenContext interpretation baselineStart rewrittenStart)
    (preserved : ∀ {baselineCount rewrittenCount : Nat}
        {baselineTarget rewrittenTarget : Machine},
      Steps baselineContext interpretation baselineCount baselineStart
          baselineTarget →
      Steps rewrittenContext interpretation rewrittenCount rewrittenStart
          rewrittenTarget →
      StableMachineRel limits validation baselineTarget rewrittenTarget →
      invariant baselineTarget rewrittenTarget) :
    StableMacroInvariantStep limits validation baselineContext
      rewrittenContext interpretation invariant baselineStart
      rewrittenStart := by
  cases simulation with
  | intro baselineCount rewrittenCount baselinePositive rewrittenPositive
      baselineTarget rewrittenTarget baselineSteps rewrittenSteps related =>
      exact .intro baselineCount rewrittenCount baselinePositive
        rewrittenPositive baselineTarget rewrittenTarget baselineSteps
        rewrittenSteps related (preserved baselineSteps rewrittenSteps related)

/-- Package a pair of related running one-step transitions as the degenerate
unchanged macro. -/
theorem StableMacroSimulation.ofStepsOne {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    {baselineStart rewrittenStart baselineTarget rewrittenTarget : Machine}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (baselineRunning : baselineStart.control =
      .running baselineFrame baselineStack)
    (rewrittenRunning : rewrittenStart.control =
      .running rewrittenFrame rewrittenStack)
    (baselineStep : Step baselineContext interpretation baselineStart
      baselineTarget)
    (rewrittenStep : Step rewrittenContext interpretation rewrittenStart
      rewrittenTarget)
    (related : StableMachineRel limits validation baselineTarget
      rewrittenTarget) :
    StableMacroSimulation limits validation baselineContext rewrittenContext
      interpretation baselineStart rewrittenStart := by
  exact .intro 1 1 (by omega) (by omega) baselineTarget rewrittenTarget
    (baselineStep.toSteps baselineRunning)
    (rewrittenStep.toSteps rewrittenRunning) related

/-- Package the logical-hot accepted-site theorem as a synchronization macro.
The premises are the runtime facts needed by the optimization, rather than an
already-packaged simulation result. -/
theorem acceptedHotLogicalStableMacroSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel remaining rewrittenFuel : Nat}
    {baselineStack rewrittenStack : List Continuation}
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {ambient : List IxIR1.Sim.Root} {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (sourceBoxAt : baselineStore.get? location = some
      ⟨.shared, 1, .ctorN site.shape.sourceConstructor fields⟩)
    (owned : IxIR1.Sim.RootOwnership baselineStore.heap
      (⟨.shared, .loc location⟩ :: ambient))
    (retained : RetainSharedMany baselineStore fields baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc location) = .ok (baselineReleased, remaining))
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    StableMacroSimulation limits validation baselineContext rewrittenContext
      .logical baselineMachine rewrittenMachine := by
  dsimp only
  obtain ⟨baselineSteps, rewrittenSteps, related⟩ :=
    acceptedHotLogicalStableSimulation rewrite found baselineSchemas
      rewrittenSchemas heap stack fuel allocationSchemaAt parameterCount
      fieldCount sourceResolved sourceBoxAt owned retained released
      allocationResolved baselineFieldWorlds tailResolved arity
  exact .intro (2 * site.shape.fieldCount + 3) 4 (by omega) (by omega) _ _
    baselineSteps rewrittenSteps related

/-- Package the cold accepted-site theorem as a synchronization macro.  The
cold branch is common to logical and physical interpretations. -/
theorem acceptedColdStableMacroSimulation {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained : Store}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    {parameters fields newFields callValues : Array RVal}
    {location fieldFuel rewrittenFuel rc retainedRc : Nat}
    {baselineStack rewrittenStack : List Continuation}
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : parameters.size = site.shape.parameterCount)
    (fieldCount : fields.size = site.shape.fieldCount)
    (sourceResolved : resolveAtom parameters (.reg site.shape.source) =
      .ok (.loc location))
    (sourceBoxAt : baselineStore.get? location = some
      ⟨.shared, rc, .ctorN site.shape.sourceConstructor fields⟩)
    (shared : 1 < rc)
    (retained : RetainSharedMany baselineStore fields baselineRetained)
    (retainedAt : baselineRetained.get? location = some
      ⟨.shared, retainedRc,
        .ctorN site.shape.sourceConstructor fields⟩)
    (allocationResolved : resolveAtoms
      (baselinePrefixValues parameters fields)
      site.shape.allocationArguments = .ok newFields)
    (baselineFieldWorlds : FieldWorlds
      (baselineDecrementStore baselineRetained location
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor fields⟩)
      allocationSchema newFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues parameters fields).push
        (.loc ((baselineDecrementStore baselineRetained location
          ⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor fields⟩).allocNode .shared
              (.ctorN site.shape.allocationConstructor newFields)).2))
      site.shape.tailArguments = .ok callValues)
    (arity : callValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := parameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := parameters
            credits := #[] }
          rewrittenStack }
    StableMacroSimulation limits validation baselineContext rewrittenContext
      interpretation baselineMachine rewrittenMachine := by
  dsimp only
  obtain ⟨_rewrittenRetained, _retained, baselineSteps, rewrittenSteps,
      related⟩ :=
    acceptedColdStableSimulation rewrite found baselineSchemas
      rewrittenSchemas heap stack fuel allocationSchemaAt parameterCount
      fieldCount sourceResolved sourceBoxAt shared retained retainedAt
      allocationResolved baselineFieldWorlds tailResolved arity
  exact .intro (2 * site.shape.fieldCount + 3) 4 (by omega) (by omega) _ _
    baselineSteps rewrittenSteps related

/-- Package the physical-hot accepted-site theorem as a synchronization
macro.  Unlike the exact-content wrappers, the input registers and suspended
continuations may already be related by a nontrivial allocation-history
bijection; the wrapped theorem replaces that relation at the reused location
and preserves it everywhere else that remains reachable. -/
theorem acceptedHotPhysicalStableMacroSimulationIso
    {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained baselineReleased : Store}
    (inputIso : IxIR1.Sim.HeapIso rewrittenStore.heap baselineStore.heap)
    {baselineParameters rewrittenParameters baselineFields rewrittenFields
      baselineNewFields rewrittenNewFields baselineCallValues : Array RVal}
    {baselineLocation rewrittenLocation fieldFuel remaining rewrittenFuel :
      Nat}
    {baselineStack rewrittenStack : List Continuation}
    (parameters : IxIR1.Sim.RValsIso
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      baselineParameters.toList rewrittenParameters.toList)
    (stack : StableStackIso limits validation
      (fun baselineLocation rewrittenLocation =>
        inputIso.locRel rewrittenLocation baselineLocation)
      baselineStack rewrittenStack)
    (stackAvoids : StackValuesAvoidLocation rewrittenLocation rewrittenStack)
    (stackCreditsAvoids :
      StackCreditsAvoidLocation rewrittenLocation rewrittenStack)
    {baselineBefore baselineAfter rewrittenBefore rewrittenAfter :
      List IxIR1.Sim.Root}
    {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (locations : inputIso.locRel rewrittenLocation baselineLocation)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : baselineParameters.size = site.shape.parameterCount)
    (fieldCount : baselineFields.size = site.shape.fieldCount)
    (baselineSourceResolved :
      resolveAtom baselineParameters (.reg site.shape.source) =
        .ok (.loc baselineLocation))
    (rewrittenSourceResolved :
      resolveAtom rewrittenParameters (.reg site.shape.source) =
        .ok (.loc rewrittenLocation))
    (baselineAt : baselineStore.get? baselineLocation = some
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor baselineFields⟩)
    (rewrittenAt : rewrittenStore.get? rewrittenLocation = some
      ⟨.shared, 1,
        .ctorN site.shape.sourceConstructor rewrittenFields⟩)
    (baselineOwned : IxIR1.Sim.RootOwnership baselineStore.heap
      (⟨.shared, .loc baselineLocation⟩ :: baselineBefore))
    (rewrittenOwned : IxIR1.Sim.RootOwnership rewrittenStore.heap
      (⟨.shared, .loc rewrittenLocation⟩ :: rewrittenBefore))
    (retained : RetainSharedMany baselineStore baselineFields
      baselineRetained)
    (released : releaseShared (fieldFuel + 1) baselineRetained
      (.loc baselineLocation) = .ok (baselineReleased, remaining))
    (baselinePartition :
      (IxIR1.Sim.rootsFor .shared baselineFields.toList ++
          baselineBefore).Perm
        (IxIR1.Sim.rootsFor .shared baselineNewFields.toList ++
          baselineAfter))
    (rewrittenPartition :
      (IxIR1.Sim.rootsFor .shared rewrittenFields.toList ++
          rewrittenBefore).Perm
        (IxIR1.Sim.rootsFor .shared rewrittenNewFields.toList ++
          rewrittenAfter))
    (mapped : MappedValuesInRoots site.shape
      (baselinePrefixValues rewrittenParameters rewrittenFields)
      rewrittenAfter)
    (baselineAllocationResolved : resolveAtoms
      (baselinePrefixValues baselineParameters baselineFields)
      site.shape.allocationArguments = .ok baselineNewFields)
    (rewrittenAllocationResolved : resolveAtoms
      (baselinePrefixValues rewrittenParameters rewrittenFields)
      site.shape.allocationArguments = .ok rewrittenNewFields)
    (baselineFieldWorlds :
      FieldWorlds baselineReleased allocationSchema baselineNewFields)
    (rewrittenFieldWorlds : FieldWorlds
      (physicalHotResetStore rewrittenStore rewrittenLocation)
      allocationSchema rewrittenNewFields)
    (tailResolved : resolveAtoms
      ((baselinePrefixValues baselineParameters baselineFields).push
        (.loc (baselineReleased.allocNode .shared
          (.ctorN site.shape.allocationConstructor baselineNewFields)).2))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := baselineParameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := rewrittenParameters
            credits := #[] }
          rewrittenStack }
    StableMacroSimulation limits validation baselineContext rewrittenContext
      .physical baselineMachine rewrittenMachine := by
  dsimp only
  have mappedFull : MappedValuesInRoots site.shape
      (baselinePrefixValues rewrittenParameters rewrittenFields)
      (IxIR1.Sim.rootsFor .shared rewrittenNewFields.toList ++
        rewrittenAfter) := by
    intro sourceId targetId sourceValue relevant translated found
    have supported := mapped sourceId targetId sourceValue relevant translated
      found
    cases sourceValue with
    | loc location =>
        obtain ⟨world, member⟩ := supported
        exact ⟨world, List.mem_append_right _ member⟩
    | lit literal => trivial
    | erased => trivial
  obtain ⟨_physical, _outputIso, _physicalCallValues, _reused,
      _physicalOwned, _baselineOwned, _outputResult, _outputExtends,
      baselineSteps, rewrittenSteps, _callsRelated, _outputStack, related⟩ :=
    acceptedHotPhysicalStableSimulationIso rewrite found baselineSchemas
      rewrittenSchemas inputIso parameters stack stackAvoids
      stackCreditsAvoids fuel locations allocationSchemaAt parameterCount
      fieldCount baselineSourceResolved rewrittenSourceResolved baselineAt
      rewrittenAt baselineOwned rewrittenOwned retained released
      baselinePartition rewrittenPartition mappedFull
      baselineAllocationResolved
      rewrittenAllocationResolved baselineFieldWorlds rewrittenFieldWorlds
      tailResolved arity
  exact .intro (2 * site.shape.fieldCount + 3) 4 (by omega) (by omega) _ _
    baselineSteps rewrittenSteps related

/-- A cold accepted site remains a synchronization macro after an earlier
physical reuse has changed concrete locations.  The source retain/release
prefix is first commuted into the cold-reset order, that order is transported
through the incoming allocation history, and corresponding fresh allocations
extend the history for the recursive call. -/
theorem acceptedColdStableMacroSimulationIso {limits : Validate.Limits}
    {validation : Validate.Context} {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {index helperOffset : Nat} {block : Block}
    {site : Reuse.Site limits validation block}
    (found : Reuse.FunctionDecisions.At rewrite.decisions index helperOffset
      block (.accepted site))
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (baselineSchemas : baselineContext.schemas = validation.schemas)
    (rewrittenSchemas : rewrittenContext.schemas = validation.schemas)
    {baselineStore rewrittenStore baselineRetained : Store}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    {baselineParameters rewrittenParameters baselineFields
      baselineNewFields baselineCallValues : Array RVal}
    {baselineLocation fieldFuel rewrittenFuel rc retainedRc : Nat}
    {baselineStack rewrittenStack : List Continuation}
    (parameters : IxIR1.Sim.RValsIso heap.locRel
      baselineParameters.toList rewrittenParameters.toList)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {allocationSchema : CtorSchema}
    (fuel : fieldFuel + 1 ≤ rewrittenFuel)
    (allocationSchemaAt :
      baselineContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema)
    (parameterCount : baselineParameters.size = site.shape.parameterCount)
    (fieldCount : baselineFields.size = site.shape.fieldCount)
    (baselineSourceResolved :
      resolveAtom baselineParameters (.reg site.shape.source) =
        .ok (.loc baselineLocation))
    (baselineAt : baselineStore.get? baselineLocation = some
      ⟨.shared, rc,
        .ctorN site.shape.sourceConstructor baselineFields⟩)
    (shared : 1 < rc)
    (retained : RetainSharedMany baselineStore baselineFields
      baselineRetained)
    (retainedAt : baselineRetained.get? baselineLocation = some
      ⟨.shared, retainedRc,
        .ctorN site.shape.sourceConstructor baselineFields⟩)
    (baselineAllocationResolved : resolveAtoms
      (baselinePrefixValues baselineParameters baselineFields)
      site.shape.allocationArguments = .ok baselineNewFields)
    (baselineFieldWorlds : FieldWorlds
      (baselineDecrementStore baselineRetained baselineLocation
        ⟨.shared, retainedRc,
          .ctorN site.shape.sourceConstructor baselineFields⟩)
      allocationSchema baselineNewFields)
    (baselineTailResolved : resolveAtoms
      ((baselinePrefixValues baselineParameters baselineFields).push
        (.loc ((baselineDecrementStore baselineRetained baselineLocation
          ⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor baselineFields⟩).allocNode
              .shared
              (.ctorN site.shape.allocationConstructor
                baselineNewFields)).2))
      site.shape.tailArguments = .ok baselineCallValues)
    (arity : baselineCallValues.size = source.signature.params.size) :
    let baselineMachine : Machine :=
      { store := baselineStore
        heapFuel := fieldFuel + 1
        control := .running
          { definition := source
            block := index
            values := baselineParameters
            credits := #[] }
          baselineStack }
    let rewrittenMachine : Machine :=
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running
          { definition := rewrite.definition
            block := index
            values := rewrittenParameters
            credits := #[] }
          rewrittenStack }
    StableMacroSimulation limits validation baselineContext rewrittenContext
      interpretation baselineMachine rewrittenMachine := by
  dsimp only
  obtain ⟨sourceAt, resetAt, _hotAt, coldAt⟩ := rewrite.acceptedAt found
  obtain ⟨sourceSchema, siteAllocationSchema, sourceSchemaAt,
      siteAllocationSchemaAt, _sourceFields, _allocationFields,
      sourceLayout, allocationLayout⟩ :=
    evalRuntimeSchemas site baselineSchemas
  have allocationSchemaEq : siteAllocationSchema = allocationSchema := by
    exact Option.some.inj
      (siteAllocationSchemaAt.symm.trans allocationSchemaAt)
  subst siteAllocationSchema
  have rewrittenSourceSchemaAt :
      rewrittenContext.schemas .shared site.shape.sourceConstructor =
        some sourceSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using sourceSchemaAt
  have rewrittenAllocationSchemaAt :
      rewrittenContext.schemas .shared site.shape.allocationConstructor =
        some allocationSchema := by
    simpa [baselineSchemas, rewrittenSchemas] using allocationSchemaAt
  obtain ⟨rewrittenSourceValue, rewrittenSourceResolved,
      sourceValueRelated⟩ :=
    resolveAtom_iso parameters baselineSourceResolved
  cases sourceValueRelated with
  | @loc _ rewrittenLocation locations =>
      have baselineViewed : ConstructorView baselineStore baselineLocation
          .shared site.shape.sourceConstructor
          ⟨.shared, rc,
            .ctorN site.shape.sourceConstructor baselineFields⟩
          baselineFields :=
        ConstructorView.of_box baselineAt rfl rfl
      obtain ⟨rewrittenBox, rewrittenFields, rewrittenAt,
          rewrittenViewed, boxes, fieldsRelated⟩ :=
        constructorView_historyIso heap locations baselineViewed
      have rewrittenShared : 1 < rewrittenBox.rc := by
        rw [← boxes.rc]
        exact shared
      have parameterSizes : baselineParameters.size =
          rewrittenParameters.size := by
        simpa using rvalsIso_length_eq parameters
      have rewrittenParameterCount : rewrittenParameters.size =
          site.shape.parameterCount :=
        parameterSizes.symm.trans parameterCount
      have fieldSizes : baselineFields.size = rewrittenFields.size := by
        simpa using rvalsIso_length_eq fieldsRelated
      have rewrittenFieldCount : rewrittenFields.size =
          site.shape.fieldCount := fieldSizes.symm.trans fieldCount
      have prefixRelated : IxIR1.Sim.RValsIso heap.locRel
          (baselinePrefixValues baselineParameters baselineFields).toList
          (baselinePrefixValues rewrittenParameters rewrittenFields).toList :=
        by
          simpa [baselinePrefixValues] using
            rvalsIso_append_pair
              (rvalsIso_append_pair parameters fieldsRelated) fieldsRelated
      obtain ⟨rewrittenNewFields, rewrittenAllocationResolved,
          newFieldsRelated⟩ :=
        resolveAtoms_iso prefixRelated baselineAllocationResolved
      obtain ⟨actualRetainedRc, actualRetainedAt, baselineReleasedRun,
          baselineResetRetained, baselineResetHeapEq⟩ :=
        coldPrefix_commutes (heapFuel := fieldFuel) baselineAt shared retained
      have retainedBoxesEqual :
          (⟨.shared, actualRetainedRc,
              .ctorN site.shape.sourceConstructor baselineFields⟩ :
              IxIR1.NodeBox) =
            ⟨.shared, retainedRc,
              .ctorN site.shape.sourceConstructor baselineFields⟩ :=
        Option.some.inj (actualRetainedAt.symm.trans retainedAt)
      have retainedRcEqual : actualRetainedRc = retainedRc := by
        cases retainedBoxesEqual
        rfl
      subst actualRetainedRc
      let baselineReleased :=
        baselineDecrementStore baselineRetained baselineLocation
          ⟨.shared, retainedRc,
            .ctorN site.shape.sourceConstructor baselineFields⟩
      let baselineResetStore :=
        baselineReleased.tickResetAttempt.tickColdReset
      let baselineBox : IxIR1.NodeBox :=
        ⟨.shared, rc,
          .ctorN site.shape.sourceConstructor baselineFields⟩
      let updated := heap.setBox locations
        (show baselineStore.heap.get? baselineLocation = some baselineBox from
          baselineAt)
        (show rewrittenStore.heap.get? rewrittenLocation = some rewrittenBox
          from rewrittenAt)
        (show IxIR1.Sim.NodeBoxIso heap.locRel
            { baselineBox with rc := baselineBox.rc - 1 }
            { rewrittenBox with rc := rewrittenBox.rc - 1 } from
          ⟨boxes.world,
            congrArg (fun count => count - 1) boxes.rc, boxes.node⟩)
      let beforeRetains : IxIR1.Sim.HeapHistoryIso
          (coldResetStartStore baselineStore baselineLocation
            baselineBox).heap
          (coldResetStartStore rewrittenStore rewrittenLocation
            rewrittenBox).heap := by
        simpa [coldResetStartStore, Eval.Store.tickResetAttempt,
          Eval.Store.tickColdReset] using updated.rcTick
      have relatedRetainedFields : IxIR1.Sim.RValsIso
          beforeRetains.locRel baselineFields.toList rewrittenFields.toList :=
        by
          change IxIR1.Sim.RValsIso heap.locRel _ _
          exact fieldsRelated
      obtain ⟨rewrittenResetStore, afterRetains,
          rewrittenResetRetained, afterRetainsRelation⟩ :=
        retainSharedMany_historyIso beforeRetains relatedRetainedFields
          (by
            simpa [baselineBox, baselineReleased, baselineResetStore] using
              baselineResetRetained)
      have baselineResetHeapEq' : baselineReleased.heap =
          baselineResetStore.heap := by
        simpa [baselineReleased, baselineResetStore] using
          baselineResetHeapEq
      let afterCold : IxIR1.Sim.HeapHistoryIso baselineReleased.heap
          rewrittenResetStore.heap :=
        afterRetains.nodesEq
          (congrArg IxIR1.Store.nodes baselineResetHeapEq') rfl
      have afterColdRelation : afterCold.locRel = heap.locRel := by
        calc
          afterCold.locRel = afterRetains.locRel := rfl
          _ = beforeRetains.locRel := afterRetainsRelation
          _ = heap.locRel := rfl
      have newFieldsAfterCold : IxIR1.Sim.RValsIso afterCold.locRel
          baselineNewFields.toList rewrittenNewFields.toList := by
        rw [afterColdRelation]
        exact newFieldsRelated
      have rewrittenFieldWorlds : FieldWorlds rewrittenResetStore
          allocationSchema rewrittenNewFields :=
        baselineFieldWorlds.transport
          (heapHistoryIso_fieldValuesWorldEq afterCold newFieldsAfterCold)
      let baselineAllocation := baselineReleased.allocNode .shared
        (.ctorN site.shape.allocationConstructor baselineNewFields)
      let rewrittenAllocation := rewrittenResetStore.allocNode .shared
        (.ctorN site.shape.allocationConstructor rewrittenNewFields)
      let allocationHistory : IxIR1.Sim.HeapHistoryIso
          baselineAllocation.1.heap rewrittenAllocation.1.heap :=
        afterCold.alloc (.ctor newFieldsAfterCold)
      have oldExtends : ∀ {baselineCandidate rewrittenCandidate : Nat},
          heap.locRel baselineCandidate rewrittenCandidate →
            allocationHistory.locRel baselineCandidate rewrittenCandidate :=
        by
          intro baselineCandidate rewrittenCandidate related
          apply Or.inr
          rw [afterColdRelation]
          exact related
      have prefixAfterAllocation : IxIR1.Sim.RValsIso
          allocationHistory.locRel
          (baselinePrefixValues baselineParameters baselineFields).toList
          (baselinePrefixValues rewrittenParameters rewrittenFields).toList :=
        rvalsIso_mono_rel oldExtends prefixRelated
      have resultRelated : IxIR1.Sim.RValIso allocationHistory.locRel
          (.loc baselineAllocation.2) (.loc rewrittenAllocation.2) :=
        .loc (.inl ⟨rfl, rfl⟩)
      have tailInputsRelated : IxIR1.Sim.RValsIso allocationHistory.locRel
          ((baselinePrefixValues baselineParameters baselineFields).push
            (.loc baselineAllocation.2)).toList
          ((baselinePrefixValues rewrittenParameters rewrittenFields).push
            (.loc rewrittenAllocation.2)).toList := by
        simpa using rvalsIso_append prefixAfterAllocation resultRelated
      obtain ⟨rewrittenCallValues, rewrittenTailResolved,
          callValuesRelated⟩ :=
        resolveAtoms_iso tailInputsRelated
          (by simpa [baselineAllocation, baselineReleased] using
            baselineTailResolved)
      have callSizes : baselineCallValues.size = rewrittenCallValues.size := by
        simpa using rvalsIso_length_eq callValuesRelated
      have rewrittenArity : rewrittenCallValues.size =
          rewrite.definition.signature.params.size := by
        simpa using callSizes.symm.trans arity
      have sourceNonempty : source.blocks.isEmpty = false :=
        blocks_nonempty_of_getElem sourceAt
      have rewrittenNonempty : rewrite.definition.blocks.isEmpty = false :=
        blocks_nonempty_of_getElem resetAt
      let baselineMachine : Machine :=
        { store := baselineStore
          heapFuel := fieldFuel + 1
          control := .running
            { definition := source
              block := index
              values := baselineParameters
              credits := #[] }
            baselineStack }
      let rewrittenMachine : Machine :=
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running
            { definition := rewrite.definition
              block := index
              values := rewrittenParameters
              credits := #[] }
            rewrittenStack }
      have baselineExecution : Steps baselineContext interpretation
          (2 * site.shape.fieldCount + 3) baselineMachine
          { store := baselineAllocation.1
            heapFuel := fieldFuel
            control := .running
              { definition := source, values := baselineCallValues }
              baselineStack } := by
        simpa [baselineMachine, baselineAllocation, baselineReleased] using
          baselineAcceptedControl site
            (context := baselineContext) (interpretation := interpretation)
            (definition := source) (blockId := index)
            (parameters := baselineParameters) (fields := baselineFields)
            (newFields := baselineNewFields)
            (callValues := baselineCallValues)
            (location := baselineLocation) (machine := baselineMachine)
            (retainedStore := baselineRetained)
            (releasedStore := baselineReleased) (remaining := fieldFuel)
            (allocationSchema := allocationSchema) (stack := baselineStack)
            sourceAt (by rfl) parameterCount fieldCount
            baselineSourceResolved baselineAt rfl retained
            (by simpa [baselineReleased] using baselineReleasedRun)
            allocationSchemaAt baselineAllocationResolved
            (by simpa [baselineReleased] using baselineFieldWorlds)
            (by simpa [baselineAllocation, baselineReleased] using
              baselineTailResolved)
            arity sourceNonempty
      have rewrittenExecution : Steps rewrittenContext interpretation 4
          rewrittenMachine
          { store := rewrittenAllocation.1
            heapFuel := rewrittenFuel
            control := .running
              { definition := rewrite.definition,
                values := rewrittenCallValues }
              rewrittenStack } := by
        simpa [rewrittenMachine, rewrittenAllocation] using
          coldAcceptedControl site
            (context := rewrittenContext)
            (interpretation := interpretation)
            (definition := rewrite.definition) (resetId := index)
            (hotId := source.blocks.size + helperOffset)
            (coldId := source.blocks.size + helperOffset + 1)
            (parameters := rewrittenParameters) (fields := rewrittenFields)
            (newFields := rewrittenNewFields)
            (callValues := rewrittenCallValues)
            (location := rewrittenLocation) (box := rewrittenBox)
            (sourceSchema := sourceSchema)
            (allocationSchema := allocationSchema)
            (machine := rewrittenMachine) (resetStore := rewrittenResetStore)
            (stack := rewrittenStack) resetAt coldAt rewrittenSourceSchemaAt
            rewrittenAllocationSchemaAt sourceLayout allocationLayout
            (by rfl) rewrittenParameterCount rewrittenFieldCount
            (by simpa using rewrittenSourceResolved) rewrittenViewed
            rewrittenShared
            (by
              simpa [rewrittenMachine, coldResetStartStore] using
                rewrittenResetRetained)
            rewrittenAllocationResolved rewrittenFieldWorlds
            (by simpa [rewrittenAllocation] using rewrittenTailResolved)
            rewrittenArity rewrittenNonempty
      have outputStack : StableStackIso limits validation
          allocationHistory.locRel baselineStack rewrittenStack :=
        stack.mono oldExtends
      have outputFuel : fieldFuel ≤ rewrittenFuel := by omega
      have related : StableMachineRel limits validation
          { store := baselineAllocation.1
            heapFuel := fieldFuel
            control := .running
              { definition := source, values := baselineCallValues }
              baselineStack }
          { store := rewrittenAllocation.1
            heapFuel := rewrittenFuel
            control := .running
              { definition := rewrite.definition,
                values := rewrittenCallValues }
              rewrittenStack } :=
        StableMachineRel.history allocationHistory outputFuel
          (.running
            (.rewritten rewrite
              (StableFrameIso.entry rewrite callValuesRelated))
            outputStack)
      exact .intro (2 * site.shape.fieldCount + 3) 4 (by omega) (by omega)
        _ _ baselineExecution rewrittenExecution related

/-- Exhaustive synchronization dispatch from an exact-content stable state.
The rewrite's dependent block decision chooses either the proved public
one-step dispatcher or the accepted-site macro supplied by the global runtime
invariant.  Thus later whole-run induction has exactly one accepted-site
obligation, rather than one obligation per ordinary instruction/terminator
shape. -/
theorem stableMacroStepOfTrace {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : HeapContentsEq baselineStore rewrittenStore)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite (fun left right => left = right)
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation (fun left right => left = right)
      baselineStack rewrittenStack)
    {baselineStepTarget : Machine}
    (stepped : Step
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      baselineStepTarget)
    (accepted : ∀ {helperOffset : Nat} {block : Block}
        {site : Reuse.Site limits validation block},
      Reuse.FunctionDecisions.At rewrite.decisions baselineFrame.block
          helperOffset block (.accepted site) →
        StableMacroSimulation limits validation
          (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }) :
    StableMacroSimulation limits validation
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      (Eval.Context.ofProgram trace.target validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack } := by
  have dispatch : ∀ {block : Block},
      baselineFrame.definition.blocks[baselineFrame.block]? = some block →
      StableMacroSimulation limits validation
        (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
        (Eval.Context.ofProgram trace.target validation.schemas oracle)
        interpretation
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack }
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack } := by
    intro block blockAt
    cases frame.blockCase blockAt with
    | unchanged sourceAt targetAt =>
        have sourceBlockAt : source.blocks[baselineFrame.block]? =
            some block := by
          rw [← frame.baselineDefinition]
          exact blockAt
        have blockEq := Option.some.inj (sourceAt.symm.trans sourceBlockAt)
        cases blockEq
        have rewrittenBlockAt :
            rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
              some block := by
          rw [frame.rewrittenDefinition, ← frame.block]
          exact targetAt
        obtain ⟨rewrittenTarget, rewrittenStep, related⟩ :=
          unchangedStepOfTrace trace rewrite heap fuel frame stack blockAt
            rewrittenBlockAt stepped
        exact StableMacroSimulation.ofStepsOne rfl rfl stepped rewrittenStep
          related
    | accepted found =>
        exact accepted found
  cases stepped.classify with
  | instruction blockAt _pc _instructionAt _instructionCase =>
      exact dispatch blockAt
  | terminator blockAt _pc _terminatorAt _terminatorCase =>
      exact dispatch blockAt

/-- Exhaustive synchronization dispatch from an allocation-history-related
stable state.  Ordinary blocks use the relation-aware one-step theorem;
accepted blocks remain a single macro obligation for the global invariant. -/
theorem stableMacroStepOfTraceIso {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    (heap : IxIR1.Sim.HeapHistoryIso baselineStore.heap rewrittenStore.heap)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite heap.locRel
      baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation heap.locRel
      baselineStack rewrittenStack)
    {baselineStepTarget : Machine}
    (stepped : Step
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      baselineStepTarget)
    (accepted : ∀ {helperOffset : Nat} {block : Block}
        {site : Reuse.Site limits validation block},
      Reuse.FunctionDecisions.At rewrite.decisions baselineFrame.block
          helperOffset block (.accepted site) →
        StableMacroSimulation limits validation
          (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }) :
    StableMacroSimulation limits validation
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      (Eval.Context.ofProgram trace.target validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack } := by
  have dispatch : ∀ {block : Block},
      baselineFrame.definition.blocks[baselineFrame.block]? = some block →
      StableMacroSimulation limits validation
        (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
        (Eval.Context.ofProgram trace.target validation.schemas oracle)
        interpretation
        { store := baselineStore
          heapFuel := baselineFuel
          control := .running baselineFrame baselineStack }
        { store := rewrittenStore
          heapFuel := rewrittenFuel
          control := .running rewrittenFrame rewrittenStack } := by
    intro block blockAt
    cases frame.blockCase blockAt with
    | unchanged sourceAt targetAt =>
        have sourceBlockAt : source.blocks[baselineFrame.block]? =
            some block := by
          rw [← frame.baselineDefinition]
          exact blockAt
        have blockEq := Option.some.inj (sourceAt.symm.trans sourceBlockAt)
        cases blockEq
        have rewrittenBlockAt :
            rewrittenFrame.definition.blocks[rewrittenFrame.block]? =
              some block := by
          rw [frame.rewrittenDefinition, ← frame.block]
          exact targetAt
        obtain ⟨rewrittenTarget, rewrittenStep, related⟩ :=
          unchangedStepOfTraceIso trace rewrite heap fuel frame stack blockAt
            rewrittenBlockAt stepped
        exact StableMacroSimulation.ofStepsOne rfl rfl stepped rewrittenStep
          related
    | accepted found =>
        exact accepted found
  cases stepped.classify with
  | instruction blockAt _pc _instructionAt _instructionCase =>
      exact dispatch blockAt
  | terminator blockAt _pc _terminatorAt _terminatorCase =>
      exact dispatch blockAt

/-- Uniform synchronization dispatch over either arm of `StableHeapRel`.
This is the macro-level interface consumed by a future whole-run induction:
the heap representation is no longer exposed to the caller. -/
theorem stableMacroStepOfTraceRel {limits : Validate.Limits}
    {validation : Validate.Context} {sourceProgram : Program}
    (trace : Reuse.Trace limits validation sourceProgram)
    {source : Function}
    (rewrite : Reuse.FunctionRewrite limits validation source)
    {oracle : Ix.Compiler.Ixon.Address → List RVal → Option RVal}
    {interpretation : Interpretation}
    {baselineStore rewrittenStore : Store}
    {baselineFuel rewrittenFuel : Nat}
    {baselineFrame rewrittenFrame : Frame}
    {baselineStack rewrittenStack : List Continuation}
    {locRel : Nat → Nat → Prop}
    (heap : StableHeapRel baselineStore rewrittenStore locRel)
    (fuel : baselineFuel ≤ rewrittenFuel)
    (frame : StableFrameIso rewrite locRel baselineFrame rewrittenFrame)
    (stack : StableStackIso limits validation locRel
      baselineStack rewrittenStack)
    {baselineStepTarget : Machine}
    (stepped : Step
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      baselineStepTarget)
    (accepted : ∀ {helperOffset : Nat} {block : Block}
        {site : Reuse.Site limits validation block},
      Reuse.FunctionDecisions.At rewrite.decisions baselineFrame.block
          helperOffset block (.accepted site) →
        StableMacroSimulation limits validation
          (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
          (Eval.Context.ofProgram trace.target validation.schemas oracle)
          interpretation
          { store := baselineStore
            heapFuel := baselineFuel
            control := .running baselineFrame baselineStack }
          { store := rewrittenStore
            heapFuel := rewrittenFuel
            control := .running rewrittenFrame rewrittenStack }) :
    StableMacroSimulation limits validation
      (Eval.Context.ofProgram sourceProgram validation.schemas oracle)
      (Eval.Context.ofProgram trace.target validation.schemas oracle)
      interpretation
      { store := baselineStore
        heapFuel := baselineFuel
        control := .running baselineFrame baselineStack }
      { store := rewrittenStore
        heapFuel := rewrittenFuel
        control := .running rewrittenFrame rewrittenStack } := by
  cases heap with
  | contents same =>
      exact stableMacroStepOfTrace trace rewrite same fuel frame stack stepped
        accepted
  | isomorphic iso =>
      exact stableMacroStepOfTraceIso trace rewrite iso.symm fuel frame stack
        stepped accepted

/-! ## Finite whole-machine synchronization -/

/-- A global invariant whose synchronized running states always admit one
invariant-preserving macro lifts every finite baseline execution ending in a
halt to a finite rewritten execution.  Baseline macro prefixes are cancelled
from the unique small-step path, and strict positivity supplies the decreasing
measure for strong induction even though accepted sites consume more than one
baseline instruction. -/
theorem stableFiniteExecutionOfMacroInvariant {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (invariant : Machine → Machine → Prop)
    (related : ∀ {baseline rewritten}, invariant baseline rewritten →
      StableMachineRel limits validation baseline rewritten)
    (advance : ∀ {baseline rewritten baselineNext : Machine}
        {frame : Frame} {stack : List Continuation},
      invariant baseline rewritten →
      baseline.control = .running frame stack →
      Step baselineContext interpretation baseline baselineNext →
      StableMacroInvariantStep limits validation baselineContext
        rewrittenContext interpretation invariant baseline rewritten)
    {baselineCount : Nat} {baselineStart rewrittenStart baselineFinal :
      Machine}
    {finalStore : Store} {finalHeapFuel : Nat} {finalValue : RVal}
    (initial : invariant baselineStart rewrittenStart)
    (baselineSteps : Steps baselineContext interpretation baselineCount
      baselineStart baselineFinal)
    (halted : baselineFinal =
      { store := finalStore
        heapFuel := finalHeapFuel
        control := .halted finalValue }) :
    ∃ rewrittenCount rewrittenFinal,
      Steps rewrittenContext interpretation rewrittenCount rewrittenStart
          rewrittenFinal ∧
        invariant baselineFinal rewrittenFinal ∧
        StableMachineRel limits validation baselineFinal rewrittenFinal := by
  induction baselineCount using Nat.strongRecOn generalizing baselineStart
      rewrittenStart baselineFinal with
  | ind baselineCount smaller =>
      cases baselineSteps with
      | refl =>
          exact ⟨0, rewrittenStart, .refl rewrittenStart, initial,
            related initial⟩
      | @cons count before middle after frame stack running head tail =>
          have synchronizedStep := advance initial running head
          cases synchronizedStep with
          | intro macroBaselineCount macroRewrittenCount baselinePositive
              rewrittenPositive macroBaselineTarget macroRewrittenTarget
              macroBaselineSteps macroRewrittenSteps macroRelated preserved =>
              obtain ⟨suffixCount, totalCount, suffixSteps⟩ :=
                macroBaselineSteps.cancelPrefixToHalted
                  (Steps.cons running head tail) halted
              have suffixSmaller : suffixCount < Nat.succ count := by
                omega
              obtain ⟨suffixRewrittenCount, rewrittenFinal,
                  suffixRewrittenSteps, finalInvariant, finalRelated⟩ :=
                smaller suffixCount suffixSmaller preserved suffixSteps halted
              exact ⟨macroRewrittenCount + suffixRewrittenCount,
                rewrittenFinal,
                macroRewrittenSteps.trans suffixRewrittenSteps,
                finalInvariant, finalRelated⟩

/-- Runner-level form of `stableFiniteExecutionOfMacroInvariant`.  A finite
halted baseline execution yields an exact rewritten control budget, a halted
rewritten result related through the final heap relation, and the corresponding
successful `runMachine` equation. -/
theorem stableRunMachineOfMacroInvariant {limits : Validate.Limits}
    {validation : Validate.Context}
    {baselineContext rewrittenContext : Eval.Context}
    {interpretation : Interpretation}
    (invariant : Machine → Machine → Prop)
    (related : ∀ {baseline rewritten}, invariant baseline rewritten →
      StableMachineRel limits validation baseline rewritten)
    (advance : ∀ {baseline rewritten baselineNext : Machine}
        {frame : Frame} {stack : List Continuation},
      invariant baseline rewritten →
      baseline.control = .running frame stack →
      Step baselineContext interpretation baseline baselineNext →
      StableMacroInvariantStep limits validation baselineContext
        rewrittenContext interpretation invariant baseline rewritten)
    {baselineCount : Nat} {baselineStart rewrittenStart : Machine}
    {finalStore : Store} {finalHeapFuel : Nat} {finalValue : RVal}
    (initial : invariant baselineStart rewrittenStart)
    (baselineSteps : Steps baselineContext interpretation baselineCount
      baselineStart
      { store := finalStore
        heapFuel := finalHeapFuel
        control := .halted finalValue }) :
    ∃ rewrittenCount rewrittenStore rewrittenHeapFuel rewrittenValue locRel,
      let rewrittenFinal : Machine :=
        { store := rewrittenStore
          heapFuel := rewrittenHeapFuel
          control := .halted rewrittenValue }
      Steps rewrittenContext interpretation rewrittenCount rewrittenStart
          rewrittenFinal ∧
        invariant
          { store := finalStore
            heapFuel := finalHeapFuel
            control := .halted finalValue }
          rewrittenFinal ∧
        StableHeapRel finalStore rewrittenStore locRel ∧
        finalHeapFuel ≤ rewrittenHeapFuel ∧
        IxIR1.Sim.RValIso locRel finalValue rewrittenValue ∧
        Eval.runMachine rewrittenContext interpretation rewrittenCount
            rewrittenStart =
          .ok
            { store := rewrittenStore
              value := rewrittenValue
              controlRemaining := 0
              heapRemaining := rewrittenHeapFuel } := by
  obtain ⟨rewrittenCount, rewrittenFinal, rewrittenSteps, finalInvariant,
      finalRelated⟩ :=
    stableFiniteExecutionOfMacroInvariant invariant related advance initial
      baselineSteps rfl
  obtain ⟨rewrittenStore, rewrittenHeapFuel, rewrittenValue, locRel,
      rewrittenFinalEq, finalHeap, finalFuel, finalValueRelated⟩ :=
    finalRelated.haltedParts
  subst rewrittenFinal
  refine ⟨rewrittenCount, rewrittenStore, rewrittenHeapFuel, rewrittenValue,
    locRel, rewrittenSteps, finalInvariant, finalHeap, finalFuel,
    finalValueRelated, ?_⟩
  exact rewrittenSteps.runMachine_halted

end Ix.Compiler.IxIR2.ReuseSim
