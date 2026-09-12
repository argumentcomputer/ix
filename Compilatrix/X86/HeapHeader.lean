import Compilatrix.X86.HeapWorkspace

namespace Compilatrix.X86.HeapHeader
open WordRegion HeapArena

def value (baseline : Bool) (field : Nat) : Word :=
  if baseline && (field == 2 || field == 3 || field == 5) then 1 else 0

def fields : List Nat := [0, 2, 3, 4, 5, 6, 7, 8, 9]

def instructions (baseline : Bool) (fields : List Nat) : List Instr := fields.flatMap fun field =>
  [.mov .w64 .rcx (.imm (value baseline field)), .store .w64 (HeapArena.header field) .rcx]

def write (baseline : Bool) (state : State) (field : Nat) : State :=
  (state.setReg .rcx (value baseline field)).setWord field (value baseline field)

def writeAll (baseline : Bool) : List Nat → State → State
  | [], state => state
  | field :: rest, state => writeAll baseline rest (write baseline state field)

def initialState (baseline : Bool) (state : State) : State := writeAll baseline fields state

theorem instructions_eq (baseline : Bool) : instructions baseline fields = HeapTarget.headerInit baseline := rfl

theorem write_stable (baseline : Bool) (state : State) (field : Nat) : Scalar.Stable state (write baseline state field) :=
  (Scalar.Stable.setReg _ _ _ (by simp)).trans (Scalar.Stable.setWord _ _ _)

theorem writeAll_stable (baseline : Bool) (fields : List Nat) (state : State) :
    Scalar.Stable state (writeAll baseline fields state) := by
  induction fields generalizing state with
  | nil => exact .refl _
  | cons field rest ih => exact (write_stable _ _ _).trans (ih _)

theorem initialize_stable (baseline : Bool) (state : State) : Scalar.Stable state (initialState baseline state) :=
  writeAll_stable _ _ _

theorem write_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (based : Based layout state) (access : Access layout holes returns) (baseline : Bool) {field : Nat} (bound : field < headerWords) :
    SafeTrace layout.region returns (instructions baseline [field]) state holes (write baseline state field) holes := by
  have moved := SafeTrace.mov layout.region returns state holes .rcx (.imm (value baseline field))
  have stored := store_header (state := state.setReg .rcx (value baseline field))
    (based.stable (Scalar.Stable.setReg _ _ _ (by simp))) access .rcx bound
  simpa [instructions, write] using moved.append stored

theorem writeAll_trace {layout : HeapArena.Layout} {holes : Stream.Holes} {returns : List ReturnFrame}
    (access : Access layout holes returns) (baseline : Bool) (fields : List Nat) :
    ∀ (state : State), Based layout state → (∀ field ∈ fields, field < headerWords) →
      SafeTrace layout.region returns (instructions baseline fields) state holes (writeAll baseline fields state) holes := by
  induction fields with
  | nil => intros; exact .nil _ _
  | cons field rest ih =>
      intro state based bound
      have first := write_trace based access baseline (bound field (by simp))
      have rest := ih (write baseline state field) (based.stable (write_stable _ _ _))
        (fun field member => bound field (by simp [member]))
      simpa [instructions, writeAll] using first.append rest

theorem initialize_trace {layout : HeapArena.Layout} {state : State} {holes : Stream.Holes} {returns : List ReturnFrame}
    (based : Based layout state) (access : Access layout holes returns) (baseline : Bool) :
    SafeTrace layout.region returns (HeapTarget.headerInit baseline) state holes (initialState baseline state) holes := by
  rw [← instructions_eq]
  exact writeAll_trace access baseline fields state based (by intro field member; simp [fields] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem writeAll_register {baseline : Bool} {fields : List Nat} {state : State} {register : GPR}
    (different : register ≠ .rcx) : (writeAll baseline fields state).registers register = state.registers register := by
  induction fields generalizing state with
  | nil => rfl
  | cons field rest ih => simp [writeAll, ih, write, different]

@[simp] theorem initialize_register {baseline : Bool} {state : State} {register : GPR} (different : register ≠ .rcx) :
    (initialState baseline state).registers register = state.registers register := writeAll_register different

theorem writeAll_other (baseline : Bool) (fields : List Nat) (state : State) {index : Nat} (outside : index ∉ fields) :
    (writeAll baseline fields state).words index = state.words index := by
  induction fields generalizing state with
  | nil => rfl
  | cons field rest ih =>
      have excluded : index ≠ field ∧ index ∉ rest := by simpa using outside
      simpa [writeAll, write, excluded.1] using ih (write baseline state field) excluded.2

theorem initialize_other (baseline : Bool) (state : State) {index : Nat} (outside : index = 1 ∨ 10 ≤ index) :
    (initialState baseline state).words index = state.words index := by
  apply writeAll_other
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem initialize_word (baseline : Bool) (state : State) {index : Nat} (bound : index < 10) (different : index ≠ 1) :
    (initialState baseline state).words index = value baseline index := by
  have cases : index = 0 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [initialState, fields, writeAll, write]

end Compilatrix.X86.HeapHeader
