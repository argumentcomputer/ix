import Ix.Compiler.X86.UniqueLoop

/-! The native entry starts from a fresh bounded arena, passes the emitted
capacity checks, constructs its owned input, and returns the reversed chain.
The theorem is parametric in the arena base, surrounding memory, and runtime. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

def guardLoads : List Instr := [.load .w64 .rax (header .cursor), .load .w64 .r11 (header .capacity)]
def guardSubtract : List Instr := [.alu .sub .w64 .r11 (.reg .rax)]
def cursorCompare : Compare := { width := .w64, left := .rax, right := .reg .r11 }
def capacityCompare (values : List Word) : Compare :=
  { width := .w64, left := .r11, right := .imm (UInt32.ofNat (requiredBytes values)) }

theorem main_guard0Code (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    BlockCode checked 0 guardLoads (.branch cursorCompare .unsignedLe 1 6) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem main_guard1Code (values : List Word) (checked : Checked) (produced : checked.program = program values) :
    BlockCode checked 1 guardSubtract (.branch (capacityCompare values) .unsignedGe 2 6) :=
  ⟨by rw [produced]; rfl, by decide⟩

theorem signExtend32_ofNat (value : Nat) (small : value < 0x80000000) :
    signExtend32 (UInt32.ofNat value) = UInt64.ofNat value := by
  have small32 : UInt32.ofNat value < 0x80000000 := by
    change (UInt32.ofNat value).toNat < 2147483648
    rw [UInt32.toNat_ofNat_of_lt' (by change value < 4294967296; omega)]
    exact small
  rw [signExtend32, if_pos small32]
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  omega

structure GuardsPassed (layout : Layout) (before after : State) : Prop where
  words : after.words = initialWords layout
  context : after.registers .rdi = layout.base
  saved : PreservesSaved before after

theorem guardSteps (layout : Layout) (values : List Word) (state : State)
    (capacity : values.length + 2 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (initial : state.words = initialWords layout) (outside memory : Memory)
    (represented : Realizes layout outside state.words memory) (runtime : Runtime)
    (checked : Checked) (produced : checked.program = program values) :
    ∃ after nextMemory, GuardsPassed layout state after ∧ Realizes layout outside after.words nextMemory ∧
      Steps runtime checked 5 (leaf (state.core memory) 0 0) (leaf (after.core nextMemory) 2 0) := by
  let loaded := (state.setReg .rax 0).setReg .r11 (UInt64.ofNat (cellBytes * layout.capacity))
  have loads : Trace layout guardLoads state loaded := by
    refine .cons (.load _ _ _ Field.cursor.index (layout.field_bound .cursor)
      (header_address state layout .cursor context)) (.cons (.load _ _ _ Field.capacity.index
      (layout.field_bound .capacity) (header_address _ layout .capacity ?_)) ?_)
    · simpa using context
    · simpa [loaded, initial, initialWords, Words.set, Field.index] using Trace.nil (layout := layout) loaded
  have cursorOK : cursorCompare.holds .unsignedLe (loaded.core Memory.unmapped) = true := by
    simp [cursorCompare, Compare.holds, Condition.holds, Core.readReg, State.core, loaded,
      AluSource.eval, UInt64.le_iff_toNat_le]
  obtain ⟨loadedMemory, loadedView, first⟩ := loads.branch outside memory represented runtime checked 0 1 6
    cursorCompare .unsignedLe (main_guard0Code values checked produced) true cursorOK
    (main_hasBlock values checked produced 1 (by decide))
  have subtract : Trace layout guardSubtract loaded loaded := by
    refine .cons (.alu _ _ _ _) ?_
    simpa [loaded, AluOp.eval] using Trace.nil (layout := layout) loaded
  have bytesBound : cellBytes * layout.capacity < UInt64.size := by
    have := layout.capacityBound
    simp only [cellBytes, UInt64.size, maxLength] at *
    omega
  have requiredBound : requiredBytes values < UInt64.size := by
    simp only [requiredBytes, cellBytes, UInt64.size] at *
    omega
  have immediate : signExtend32 (UInt32.ofNat (requiredBytes values)) = UInt64.ofNat (requiredBytes values) :=
    signExtend32_ofNat _ (by have := layout.capacityBound; simp only [requiredBytes, cellBytes, maxLength] at *; omega)
  have space : UInt64.ofNat (requiredBytes values) ≤ UInt64.ofNat (cellBytes * layout.capacity) := by
    rw [UInt64.ofNat_le_iff_le requiredBound bytesBound]
    simp only [requiredBytes, cellBytes]
    omega
  have capacityOK : (capacityCompare values).holds .unsignedGe (loaded.core Memory.unmapped) = true := by
    simpa [capacityCompare, Compare.holds, Condition.holds, Core.readReg, State.core,
      loaded, AluSource.eval, immediate] using space
  obtain ⟨nextMemory, finalView, second⟩ := subtract.branch outside loadedMemory loadedView runtime checked 1 2 6
    (capacityCompare values) .unsignedGe (main_guard1Code values checked produced) true capacityOK
    (main_hasBlock values checked produced 2 (by decide))
  refine ⟨loaded, nextMemory, ⟨?_, ?_, ?_⟩, finalView, first.append second⟩
  · exact initial
  · simpa [loaded] using context
  · exact (PreservesSaved.setReg state .rax _ rfl).trans (PreservesSaved.setReg _ .r11 _ rfl)

def mainCounts (length : Nat) : Counts :=
  { allocs := length + 2, frees := 1, reuses := length, live := length + 1,
    peak := length + 2, payload := 2 * length }

@[simp] theorem readyCounts_finish (length : Nat) : (readyCounts (length + 2)).finish length = mainCounts length := by
  simp [readyCounts, Counts.finish, Counts.release, mainCounts]

theorem mainSteps (layout : Layout) (values : List Word) (state : State)
    (capacity : values.length + 2 ≤ layout.capacity) (context : state.registers .rdi = layout.base)
    (initial : state.words = initialWords layout) (outside memory : Memory)
    (represented : Realizes layout outside state.words memory) (runtime : Runtime)
    (checked : Checked) (produced : checked.program = program values) :
    ∃ after nextMemory, LoopResult layout values.reverse (mainCounts values.length) state after ∧
      Realizes layout outside after.words nextMemory ∧
      Steps runtime checked (controlCost values) (leaf (state.core memory) 0 0)
        (haltedLeaf (after.core nextMemory) 4 13) := by
  obtain ⟨guarded, guardMemory, guardResult, guardView, guards⟩ :=
    guardSteps layout values state capacity context initial outside memory represented runtime checked produced
  obtain ⟨initialized, input, inputResult⟩ :=
    initializeTrace layout values guarded capacity guardResult.context guardResult.words
  have bound : values.length ≤ maxLength := by have := layout.capacityBound; omega
  obtain ⟨inputMemory, inputView, inputSteps⟩ := input.jump outside guardMemory guardView runtime checked 2 3
    (main_inputCode values checked produced bound) (main_hasBlock values checked produced 3 (by decide))
  have invariant : LoopInvariant layout values [] (readyCounts (values.length + 2)) initialized :=
    ⟨inputResult.input, inputResult.accumulator, inputResult.counts, inputResult.inputRoot,
      inputResult.accRoot, inputResult.context⟩
  obtain ⟨after, nextMemory, loopResult, finalView, loop⟩ := loopSteps layout values values []
    (readyCounts (values.length + 2)) initialized invariant (by simpa using capacity) (by simp [readyCounts])
    outside inputMemory inputView runtime checked produced
  refine ⟨after, nextMemory, ?_, finalView, ?_⟩
  · have saved := (guardResult.saved.trans inputResult.saved).trans loopResult.saved
    simp only [List.append_nil, readyCounts_finish] at loopResult
    exact { loopResult with saved }
  · have cost : 5 + ((inputInstructions values).length + 1 + (31 * values.length + 16)) = controlCost values := by
      simp only [inputInstructions_length, controlCost]
      omega
    have all := guards.append (inputSteps.append loop)
    rw [cost] at all
    exact all

/-- The public word-level result is about `runFrom` on the emitted program,
with the arena's initial bytes constructed from any surrounding memory. -/
theorem mainRuns (layout : Layout) (values : List Word) (registers : Registers)
    (capacity : values.length + 2 ≤ layout.capacity) (context : registers .rdi = layout.base)
    (outside : Memory) (runtime : Runtime) (checked : Checked) (produced : checked.program = program values) :
    ∃ after nextMemory, LoopResult layout values.reverse (mainCounts values.length)
        ⟨registers, initialWords layout⟩ after ∧
      Realizes layout outside after.words nextMemory ∧
      runFrom runtime checked (controlCost values) ⟨registers, initialMemory layout outside⟩ =
        haltedLeaf (after.core nextMemory) 4 13 := by
  obtain ⟨after, nextMemory, result, finalView, steps⟩ := mainSteps layout values
    ⟨registers, initialWords layout⟩ capacity context rfl outside (initialMemory layout outside)
    (initialMemory_realizes layout outside) runtime checked produced
  refine ⟨after, nextMemory, result, finalView, ?_⟩
  have entry : checked.program.entry = 0 := by rw [produced]; rfl
  simpa [runFrom, Machine.initial, leaf, entry, State.core] using steps.run_eq

end Ix.Compiler.X86.UniqueExecution
