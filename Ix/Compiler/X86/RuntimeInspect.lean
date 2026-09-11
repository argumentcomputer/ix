import Ix.Compiler.X86.RuntimeTarget

/-! Read-only instruction traces preserve the exact byte memory. These
corollaries expose the failure behavior of the runtime-input checks while
remaining steps of the existing permissioned x86 evaluator. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI

def readsOnly : Instr → Bool
  | .mov .. | .lea .. | .alu .. | .load .. => true
  | _ => false

def keepsRegister (register : GPR) : Instr → Bool
  | .mov _ destination _ | .lea destination _ | .alu _ _ destination _ | .load _ destination _ =>
      destination != register
  | .store .. => true
  | _ => false

theorem Effect.words_readOnly {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) (readonly : readsOnly instruction = true) :
    after.words = before.words := by
  cases effect <;> simp_all [readsOnly]

theorem Effect.register_kept {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) (register : GPR)
    (kept : keepsRegister register instruction = true) : after.registers register = before.registers register := by
  cases effect <;> simp_all [keepsRegister, ne_comm]

theorem Trace.words_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true) :
    after.words = before.words := by
  induction trace with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at readonly
      exact (ih readonly.2).trans (first.words_readOnly readonly.1)

theorem Trace.register_kept {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (register : GPR)
    (kept : instructions.all (keepsRegister register) = true) :
    after.registers register = before.registers register := by
  induction trace with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at kept
      exact (ih kept.2).trans (first.register_kept register kept.1)

theorem Trace.saved {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after)
    (kept : ∀ register, Saved register = true → instructions.all (keepsRegister register) = true) :
    PreservesSaved before after := fun register saved => trace.register_kept register (kept register saved)

theorem Effect.sound_readOnly {layout : Layout} {instruction : Instr} {before after : State}
    (effect : Effect layout instruction before after) (readonly : readsOnly instruction = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory) :
    Straight.Effect instruction (before.core memory) (after.core memory) := by
  cases effect with
  | mov _ destination source =>
      have effect := Straight.Effect.mov (before.core memory) destination source
      rw [State.move_core] at effect
      simpa [State.core, State.setReg, Core.setReg] using effect
  | lea _ destination source =>
      have effect := Straight.Effect.lea (before.core memory) destination source
      rw [State.address_core] at effect
      simpa [State.core, State.setReg, Core.setReg] using effect
  | alu _ operation destination source =>
      have effect := Straight.Effect.alu (before.core memory) operation destination source
      rw [State.alu_core] at effect
      simpa [State.core, State.setReg, Core.setReg, Core.readReg] using effect
  | load _ destination source slot bound address =>
      apply Straight.Effect.load (before.core memory) destination source (before.words slot)
      · rw [State.address_core, address]; exact represented.readable slot bound
      · rw [State.address_core, address]; exact represented.view slot bound
  | store => contradiction

theorem Trace.sound_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory) :
    Straight.Sequence instructions (before.core memory) (after.core memory) := by
  induction trace with
  | nil => exact .nil _
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at readonly
      exact .cons (first.sound_readOnly readonly.1 outside memory represented)
        (ih readonly.2 ((first.words_readOnly readonly.1).symm ▸ represented))

theorem Trace.branch_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block yes no : BlockId)
    (comparison : Compare) (condition : Condition)
    (code : BlockCode checked block instructions (.branch comparison condition yes no)) (answer : Bool)
    (holds : comparison.holds condition (after.core Memory.unmapped) = answer)
    (valid : checked.program.hasBlock (if answer then yes else no) = true) :
    Steps runtime checked (instructions.length + 1) (leaf (before.core memory) block 0)
      (leaf (after.core memory) (if answer then yes else no) 0) := by
  have first := (trace.sound_readOnly readonly outside memory represented).steps
    runtime checked block 0 code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact first.append (Steps.single (code.branch runtime _ answer
    ((after.compare_core memory comparison condition).trans holds) valid))

theorem Trace.jump_readOnly {layout : Layout} {instructions : List Instr} {before after : State}
    (trace : Trace layout instructions before after) (readonly : instructions.all readsOnly = true)
    (outside memory : Memory) (represented : Realizes layout outside before.words memory)
    (runtime : Runtime) (checked : Checked) (block target : BlockId)
    (code : BlockCode checked block instructions (.jump target)) (valid : checked.program.hasBlock target = true) :
    Steps runtime checked (instructions.length + 1) (leaf (before.core memory) block 0)
      (leaf (after.core memory) target 0) := by
  have first := (trace.sound_readOnly readonly outside memory represented).steps
    runtime checked block 0 code.segment (by simpa using code.fits)
  simp only [Nat.zero_add] at first
  exact first.append (Steps.single (code.jump valid runtime _))

end Ix.Compiler.X86.UniqueExecution
