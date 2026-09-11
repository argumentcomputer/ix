import Ix.Compiler.X86.UniqueMain

/-! Complete reclamation by the separately emitted release entry. The result
records every freed cell and preservation of cells outside the released chain,
so it composes with the main entry's already-freed input nil. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

def Counts.dropped (counts : Counts) (length : Nat) : Counts :=
  { counts with frees := counts.frees + (length + 1), live := counts.live - (length + 1) }

@[simp] theorem Counts.dropped_zero (counts : Counts) : counts.dropped 0 = counts.release := rfl

@[simp] theorem Counts.dropped_release (counts : Counts) (length : Nat) :
    counts.release.dropped length = counts.dropped (length + 1) := by
  cases counts
  simp [Counts.dropped, Counts.release, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]

def CellFrame (before after : Words) (start count : Nat) : Prop :=
  ∀ index, (index < start ∨ start + count ≤ index) → ∀ field < 4,
    after (cellSlot index field) = before (cellSlot index field)

structure DropResult (layout : Layout) (start length : Nat) (counts : Counts) (before after : State) : Prop where
  countsAt : CountsAt layout (counts.dropped length) after.words
  freed : ∀ index, start ≤ index → index ≤ start + length → CellAt after.words index freedTag 0 0
  frame : CellFrame before.words after.words start (length + 1)
  result : after.registers .rax = 0
  context : after.registers .rdi = layout.base
  saved : PreservesSaved before after

theorem releaseSteps (layout : Layout) (values : List Word) (start : Nat) (counts : Counts) (state : State)
    (chain : UpChain layout state.words start values) (counted : CountsAt layout counts state.words)
    (root : state.registers .rsi = layout.cell start) (context : state.registers .rdi = layout.base)
    (capacity : start + values.length < layout.capacity) (live : values.length + 1 ≤ counts.live)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (runtime : Runtime) (checked : Checked) (produced : checked.program = releaseProgram) :
    ∃ after nextMemory, DropResult layout start values.length counts state after ∧
      Realizes layout outside after.words nextMemory ∧
      Steps runtime checked (releaseCost values.length) (leaf (state.core memory) 0 0)
        (haltedLeaf (after.core nextMemory) 2 13) := by
  induction values generalizing start counts state memory with
  | nil =>
      let tagged := tagState state start
      have bound : start < layout.capacity := by simpa using capacity
      have load := tagTrace layout state .rsi start bound root
      have tested := tagState_test state start nilTag chain.tagAt
      obtain ⟨tagMemory, tagView, dispatch⟩ := load.branch outside memory represented runtime checked 0 2 1
        tagCompare .eq (release_tagCode checked produced) true tested
        (release_hasBlock checked produced 2 (by decide))
      let after := (releaseState tagged start).setReg .rax 0
      have release := releaseTrace layout tagged .rsi start bound
        (by simpa [tagged, tagState] using context) (by simpa [tagged, tagState] using root) (by decide)
      have move : Trace layout [Instr.mov .w64 .rax (.imm 0)] (releaseState tagged start) after :=
        .cons (.mov _ _ _) (.nil _)
      obtain ⟨nextMemory, finalView, finish⟩ := (release.append move).ret outside tagMemory tagView
        runtime checked 2 (release_retCode checked produced)
      have words : after.words = releasedWords state.words start := by
        simp [after, releaseState_words, tagged, tagState]
      refine ⟨after, nextMemory, ?_, finalView, dispatch.append finish⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [words]
        exact counted.release start (by simp only [List.length_nil] at live; omega)
      · intro index lower upper
        have equal : index = start := by simp at upper; omega
        subst index
        rw [words]
        exact releasedWords_cell state.words start
      · intro index outsideRange field fieldBound
        rw [words]
        exact releasedWords_other state.words (by simp at outsideRange; omega) fieldBound
      · simp [after]
      · simpa [after, tagged, tagState] using context
      · exact ((PreservesSaved.setReg state .rcx _ rfl).trans (releaseState_saved tagged start)).trans
          (PreservesSaved.setReg _ .rax _ rfl)
  | cons head tail ih =>
      let tagged := tagState state start
      have bound : start < layout.capacity := by simp only [List.length_cons] at capacity; omega
      have load := tagTrace layout state .rsi start bound root
      have tested := tagState_test state start consTag chain.1.tagAt
      obtain ⟨tagMemory, tagView, dispatch⟩ := load.branch outside memory represented runtime checked 0 2 1
        tagCompare .eq (release_tagCode checked produced) false tested
        (release_hasBlock checked produced 1 (by decide))
      let pointed := tagged.setReg .rdx (state.words (cellSlot start 2))
      let next := (releaseState pointed start).setReg .rsi (pointed.registers .rdx)
      have readTail : Trace layout [Instr.load .w64 .rdx (memoryOperand .rsi 16)] tagged pointed :=
        .cons (loadField layout tagged .rsi .rdx start 2 bound (by decide)
          (by simpa [tagged, tagState] using root)) (.nil _)
      have release := releaseTrace layout pointed .rsi start bound
        (by simpa [pointed, tagged, tagState] using context)
        (by simpa [pointed, tagged, tagState] using root) (by decide)
      have move : Trace layout [Instr.mov .w64 .rsi (.reg .rdx)] (releaseState pointed start) next := by
        refine .cons (.mov _ _ _) ?_
        simpa [next] using Trace.nil (layout := layout) next
      obtain ⟨releaseMemory, releaseView, released⟩ := ((readTail.append release).append move).jump
        outside tagMemory tagView runtime checked 1 0 (release_consCode checked produced)
        (release_hasBlock checked produced 0 (by decide))
      have words : next.words = releasedWords state.words start := by
        simp [next, releaseState_words, pointed, tagged, tagState]
      have nextChain : UpChain layout next.words (start + 1) tail := by
        rw [words]
        apply chain.2.mono
        intro index lower upper field fieldBound
        exact releasedWords_other state.words (by omega) fieldBound
      have nextCounted : CountsAt layout counts.release next.words := by
        rw [words]
        exact counted.release start (by simp only [List.length_cons] at live; omega)
      have nextRoot : next.registers .rsi = layout.cell (start + 1) := by
        simpa [next, pointed] using chain.1.tailAt
      have nextContext : next.registers .rdi = layout.base := by
        simpa [next, pointed, tagged, tagState] using context
      obtain ⟨after, nextMemory, result, finalView, rest⟩ := ih (start + 1) counts.release next
        nextChain nextCounted nextRoot nextContext (by simp only [List.length_cons] at capacity; omega)
        (by simp only [List.length_cons] at live; simp only [Counts.release]; omega) releaseMemory releaseView
      have saved : PreservesSaved state after :=
        ((((PreservesSaved.setReg state .rcx _ rfl).trans (PreservesSaved.setReg tagged .rdx _ rfl)).trans
          (releaseState_saved pointed start)).trans (PreservesSaved.setReg _ .rsi _ rfl)).trans result.saved
      refine ⟨after, nextMemory, ⟨?_, ?_, ?_, result.result, result.context, saved⟩, finalView, ?_⟩
      · simpa using result.countsAt
      · intro index lower upper
        by_cases equal : index = start
        · subst index
          apply (releasedWords_cell state.words start).mono
          intro field fieldBound
          rw [result.frame start (Or.inl (by omega)) field fieldBound, words]
        · exact result.freed index (by omega) (by simp only [List.length_cons] at upper; omega)
      · intro index outsideRange field fieldBound
        have elsewhere : index < start + 1 ∨ start + 1 + (tail.length + 1) ≤ index := by
          simp only [List.length_cons] at outsideRange
          omega
        rw [result.frame index elsewhere field fieldBound, words]
        exact releasedWords_other state.words (by simp only [List.length_cons] at outsideRange; omega) fieldBound
      · have all := dispatch.append (released.append rest)
        have cost : (tagInstructions .rsi).length + 1 +
            (([Instr.load .w64 .rdx (memoryOperand .rsi 16)] ++ releaseCell .rsi ++
              [Instr.mov .w64 .rsi (.reg .rdx)]).length + 1 + releaseCost tail.length) =
            releaseCost (head :: tail).length := by
          change 2 + (15 + (17 * tail.length + 16)) = 17 * (tail.length + 1) + 16
          omega
        rw [cost] at all
        exact all

/-- Executing the release entry consumes exactly the returned finite chain. -/
theorem releaseRuns (layout : Layout) (values : List Word) (start : Nat) (counts : Counts) (state : State)
    (chain : UpChain layout state.words start values) (counted : CountsAt layout counts state.words)
    (root : state.registers .rsi = layout.cell start) (context : state.registers .rdi = layout.base)
    (capacity : start + values.length < layout.capacity) (live : values.length + 1 ≤ counts.live)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory)
    (runtime : Runtime) (checked : Checked) (produced : checked.program = releaseProgram) :
    ∃ after nextMemory, DropResult layout start values.length counts state after ∧
      Realizes layout outside after.words nextMemory ∧
      runFrom runtime checked (releaseCost values.length) (state.core memory) =
        haltedLeaf (after.core nextMemory) 2 13 := by
  obtain ⟨after, nextMemory, result, finalView, steps⟩ := releaseSteps layout values start counts state
    chain counted root context capacity live outside memory represented runtime checked produced
  refine ⟨after, nextMemory, result, finalView, ?_⟩
  have entry : checked.program.entry = 0 := by rw [produced]; rfl
  simpa [runFrom, Machine.initial, leaf, entry] using steps.run_eq

end Ix.Compiler.X86.UniqueExecution
