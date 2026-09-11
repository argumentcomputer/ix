import Compilatrix.X86.UniqueLoop
import Compilatrix.X86.UniqueSafeControl

/-! The destructive loop preserves return-slot masks left by earlier calls. -/
namespace Compilatrix.X86.UniqueExecution
open UniqueABI UniqueTarget

theorem loopSafeStepsFor (layout : Layout) (values acc : List Word) (counts : Counts) (state : State)
    (invariant : LoopInvariant layout values acc counts state)
    (capacity : values.length + acc.length + 2 ≤ layout.capacity) (positive : 0 < counts.live)
    (holes : Stream.Holes) (access : HeapAccess layout holes [])
    (returnSlot : Stream.ReadableData holes (state.registers .rsp) 8)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (runtime : Runtime) (checked : Checked) (body : List Instr) (code : LoopCode checked body)
    (bodyTrace : ∀ (state : State) (index : Nat), index < layout.capacity →
      state.registers .rdi = layout.base → state.registers .rdx = layout.cell index →
      Trace layout body state (consState state index)) :
    ∃ after nextMemory, LoopResult layout (values.reverse ++ acc) (counts.finish values.length) state after ∧
      Realizes layout outside after.words nextMemory ∧
      Stream.SafeSteps runtime checked ((body.length + 3) * values.length + 16) holes (leaf (state.core memory) 3 0)
        holes (haltedLeaf (after.core nextMemory) 4 13) := by
  induction values generalizing acc counts state memory with
  | nil =>
      let tagged := tagState state 0
      have load := tagTrace layout state .rdx 0 (by simp at capacity; omega) invariant.inputRoot
      have tested := tagState_test state 0 nilTag invariant.input.tagAt
      obtain ⟨tagMemory, tagView, dispatch⟩ := load.safeBranch access outside memory represented runtime checked 3 4 5
        tagCompare .eq code.tag true tested code.hasFinish
      let after := (releaseState tagged 0).setReg .rax (state.registers .rsi)
      have released := releaseTrace layout tagged .rdx 0 (by simp at capacity; omega)
        (by simpa [tagged, tagState] using invariant.context)
        (by simpa [tagged, tagState] using invariant.inputRoot) (by decide)
      have move : Trace layout [Instr.mov .w64 .rax (.reg .rsi)] (releaseState tagged 0) after := by
        refine .cons (.mov _ _ _) ?_
        simpa [after, tagged, tagState] using Trace.nil (layout := layout) after
      obtain ⟨nextMemory, finalView, finish⟩ := (released.append move).safeHalt access outside tagMemory tagView
        runtime checked 4 code.finish
        (by simpa [after, tagged, tagState, releaseState] using returnSlot)
      have words : after.words = releasedWords state.words 0 := by
        simp [after, releaseState_words, tagged, tagState]
      refine ⟨after, nextMemory, ?_, finalView, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.reverse_nil, List.nil_append]
          rw [words]
          apply invariant.accumulator.mono
          intro index lower upper field fieldBound
          exact releasedWords_other state.words (by simp at lower; omega) fieldBound
        · rw [words]
          simpa using invariant.countsAt.release 0 positive
        · rw [words]
          exact releasedWords_cell state.words 0
        · simpa [after] using invariant.accRoot
        · simpa [after, tagged, tagState] using invariant.accRoot
        · simpa [after, tagged, tagState] using invariant.context
        · exact ((PreservesSaved.setReg state .rcx _ rfl).trans (releaseState_saved tagged 0)).trans
            (PreservesSaved.setReg _ .rax _ rfl)
      · exact dispatch.append finish
  | cons head tail ih =>
      let index := tail.length + 1
      let tagged := tagState state index
      have indexBound : index < layout.capacity := by simp only [List.length_cons] at capacity; omega
      have load := tagTrace layout state .rdx index indexBound invariant.inputRoot
      have tested := tagState_test state index consTag invariant.input.1.tagAt
      obtain ⟨tagMemory, tagView, dispatch⟩ := load.safeBranch access outside memory represented runtime checked 3 4 5
        tagCompare .eq code.tag false tested code.hasCons
      let next := consState tagged index
      have consume := bodyTrace tagged index indexBound
        (by simpa [tagged, tagState] using invariant.context)
        (by simpa [tagged, tagState] using invariant.inputRoot)
      obtain ⟨consumeMemory, consumeView, consumed⟩ := consume.safeJump access outside tagMemory tagView runtime checked 5 3
        code.cons code.hasTag
      have words : next.words = consumedWords state.words index (layout.cell (tail.length + 2)) := by
        simp [next, consState_words, tagged, tagState, invariant.accRoot, Nat.add_assoc]
      have chains := chains_cons invariant.input invariant.accumulator
      have nextInvariant : LoopInvariant layout tail (head :: acc) counts.consume next := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [words]
          exact chains.1
        · rw [words]
          exact chains.2
        · rw [words]
          exact invariant.countsAt.consume index _
        · simpa [next, tagged, tagState, index] using invariant.input.1.tailAt
        · simpa [next, tagged, tagState] using invariant.inputRoot
        · simpa [next, tagged, tagState] using invariant.context
      obtain ⟨after, nextMemory, result, finalView, rest⟩ := ih (head :: acc) counts.consume next nextInvariant
        (by simp only [List.length_cons] at *; omega) positive
        (by simpa [next, tagged, tagState, consState, reserveState, reuseState] using returnSlot) consumeMemory consumeView
      refine ⟨after, nextMemory, ?_, finalView, ?_⟩
      · have saved : PreservesSaved state after :=
          ((PreservesSaved.setReg state .rcx _ rfl).trans (consState_saved tagged index)).trans result.saved
        have valueEq : tail.reverse ++ head :: acc = (head :: tail).reverse ++ acc := by
          simp [List.reverse_cons, List.append_assoc]
        rw [valueEq, Counts.finish_consume] at result
        exact { result with saved }
      · have all := dispatch.append (consumed.append rest)
        have cost : (tagInstructions .rdx).length + 1 +
            (body.length + 1 + ((body.length + 3) * tail.length + 16)) =
            (body.length + 3) * (head :: tail).length + 16 := by
          simp only [tagInstructions, List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one]
          omega
        rw [cost] at all
        exact all

end Compilatrix.X86.UniqueExecution
