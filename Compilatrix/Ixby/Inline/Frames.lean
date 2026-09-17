import Compilatrix.Ixby.Inline.Layout

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem check_success {limits : Limits} {program : Program} {frame : Frame} {block : Block}
    (checked : frame.check limits program = .ok block) :
    ∃ function, program.getFunction frame.function = .ok function ∧
      function.blocks[frame.block]? = some block ∧
      frame.locals.size ≤ limits.locals ∧ frame.locals.size = block.locals := by
  cases found : program.getFunction frame.function with
  | error error => simp [Frame.check, found, bind, Except.bind] at checked
  | ok function =>
    cases located : function.blocks[frame.block]? with
    | none => simp [Frame.check, found, located, bind, Except.bind] at checked
    | some actual =>
      by_cases room : limits.locals < frame.locals.size
      · simp [Frame.check, found, located, room, bind, Except.bind] at checked
      · by_cases size : frame.locals.size = actual.locals
        · have equal : actual = block := by
            simpa [Frame.check, found, located, size,
              show ¬limits.locals < actual.locals by omega, bind, Except.bind] using checked
          subst block
          exact ⟨function, rfl, located, by omega, size⟩
        · simp [Frame.check, found, located, room, size, bind, Except.bind] at checked

theorem ProgramRelated.function {limits source target} (related : ProgramRelated limits source target)
    {id : FunctionId} {function : Function} (found : source.getFunction id = .ok function) :
    ∃ candidate, target.getFunction id = .ok candidate ∧ FunctionRelated limits source function candidate := by
  have paired := related.functions.get id
  cases left : source.functions[id]? with
  | none => simp [Program.getFunction, left] at found
  | some before =>
    have equal : before = function := by simpa [Program.getFunction, left] using found
    subst function
    cases right : target.functions[id]? with
    | none => simp [left, right, OptionPaired] at paired
    | some after => exact ⟨after, by simp [Program.getFunction, right], by simpa [left, right, OptionPaired] using paired⟩

theorem FunctionRelated.block {limits source left right} (related : FunctionRelated limits source left right)
    {index : BlockId} {block : Block} (found : left.blocks[index]? = some block) :
    ∃ candidate, right.blocks[index]? = some candidate ∧ BlockRelated limits source block candidate := by
  have paired := related.blocks.get index
  cases located : right.blocks[index]? with
  | none => simp [found, located, OptionPaired] at paired
  | some after => exact ⟨after, rfl, by simpa [found, located, OptionPaired] using paired⟩

theorem ProgramRelated.checked {limits source target} (related : ProgramRelated limits source target)
    {frame : Frame} {block : Block} (checked : frame.check limits source = .ok block) :
    ∃ candidate, frame.check limits target = .ok candidate ∧ BlockRelated limits source block candidate := by
  obtain ⟨before, found, located, room, size⟩ := check_success checked
  obtain ⟨after, candidateFound, relatedFunction⟩ := related.function found
  obtain ⟨candidate, candidateLocated, relatedBlock⟩ := relatedFunction.block located
  refine ⟨candidate, ?_, relatedBlock⟩
  simp [Frame.check, candidateFound, candidateLocated, ← relatedBlock.locals, size,
    show ¬limits.locals < block.locals by omega, bind, Except.bind]

theorem stepEval_same {limits : Limits} {source target : Program} (same : SameLayout source target)
    (state : State) (frame : Frame) (before after : Block)
    (checkedBefore : frame.check limits source = .ok before)
    (checkedAfter : frame.check limits target = .ok after)
    (instruction : before.instruction = after.instruction) :
    stepEval limits source state frame = stepEval limits target state frame := by
  simp only [stepEval, checkedBefore, checkedAfter, bind, Except.bind, instruction]
  cases after.instruction <;>
    simp only [same.evalOp, same.enter, same.transfer, same.selectCase]

theorem step_ret_same {limits : Limits} {source target : Program} (same : SameLayout source target)
    (value : Value) (continuation : Array Continuation) :
    step limits source ⟨.ret value, continuation⟩ = step limits target ⟨.ret value, continuation⟩ := by
  simp only [step]
  cases last : continuation.back? with
  | none => rfl
  | some cont =>
    cases cont with
    | apply args => rfl
    | resume frame => simp only [same.transfer]

end Compilatrix.Ixby.Inline
