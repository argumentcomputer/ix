import IxCC.X86.ObjectExecution
import IxCC.Sem.Clocked

/-!
# An export's execution from the object, as a clocked semantics

`ObjectEval.exec bytes name base core₀ flags` is the run of the export
`name` of the ELF object `bytes`, loaded with its text at `base`, as a
SysV caller starts it: registers and memory `core₀`, the caller's return
address in the word at `rsp`. Text and entry point come from the bytes
(`ELFRead.text?`, `ELF.entry?`), as in `ObjectEval.run`. At clock `k` the
byte machine runs at most `k` steps and stops when control reaches the
return address (`runTo`). The outcome (`finish`):

- control at the return address, `rsp` one word above `core₀`'s and the
  callee-saved registers `core₀`'s: the status in `rax` with the value in
  `rdx` (`statusResult`, the status codes of `Rt.Layout`: 0 the value and the final
  memory; 1 heap, 2 stack, 3 natOverflow; 4 trap; any other status
  `stuck`);
- a return that does not restore `rsp` or a callee-saved register, a byte
  machine fault, or an object without the text, the symbol or the return
  slot: `stuck`;
- otherwise `timeout`.

`exec_mono`: the clock only extends the run.
-/

namespace IxCC.X86.ObjectEval

open IxCC.Sem (Result Resource ClockMono)

/-- Run the byte machine for at most `fuel` steps, stopping when `rip` is
`stop`. -/
def runTo (text : ByteArray) (base stop : Word) : Nat → ByteEval.State → Except ByteEval.Fault ByteEval.State
  | 0, state => .ok state
  | fuel + 1, state =>
      if state.rip = stop then .ok state
      else
        match ByteEval.step text base state with
        | .ok next => runTo text base stop fuel next
        | .error fault => .error fault

/-- An export's status and value as an outcome. -/
def statusResult (status value : Word) (memory : Memory) : Result (Word × Memory) :=
  if status = 0 then .ok (value, memory)
  else if status = 1 then .resource .heap
  else if status = 2 then .resource .stack
  else if status = 3 then .resource .natOverflow
  else if status = 4 then .trap
  else .stuck

/-- The status code of a resource failure. -/
def Resource.code : Resource → Word
  | .heap => 1
  | .stack => 2
  | .natOverflow => 3

/-- Whether a returned state has the caller's `rsp` (past the return
address) and callee-saved registers. -/
def restored (core₀ : Core) (state : ByteEval.State) : Bool :=
  state.core.readReg .rsp == core₀.readReg .rsp + 8 &&
    SysV.calleeSaved.all fun register => state.core.readReg register == core₀.readReg register

/-- The outcome of a byte state the clock stopped at. -/
def finish (core₀ : Core) (retAddr : Word) (state : ByteEval.State) : Result (Word × Memory) :=
  if state.rip = retAddr then
    if restored core₀ state then
      statusResult (state.core.readReg .rax) (state.core.readReg .rdx) state.core.memory
    else .stuck
  else .timeout

/-- The clocked run of the object's export `name` from `core₀`. -/
def exec (bytes : ByteArray) (name : String) (base : Word) (core₀ : Core) (flags : ByteEval.Flags)
    (k : Nat) : Result (Word × Memory) :=
  match ELFRead.text? bytes, ELF.entry? bytes name, core₀.memory.read64? (core₀.readReg .rsp) with
  | some text, some offset, .ok retAddr =>
      match runTo text base retAddr k ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
      | .ok state => finish core₀ retAddr state
      | .error _ => .stuck
  | _, _, _ => .stuck

theorem runTo_stop {text : ByteArray} {base stop : Word} {state : ByteEval.State} (h : state.rip = stop) :
    ∀ fuel, runTo text base stop fuel state = .ok state
  | 0 => rfl
  | _ + 1 => by simp [runTo, h]

/-- Running for `a + b` steps is running for `a`, then for `b`. -/
theorem runTo_add (text : ByteArray) (base stop : Word) (b : Nat) :
    ∀ (a : Nat) (state : ByteEval.State), runTo text base stop (a + b) state =
      match runTo text base stop a state with
      | .ok next => runTo text base stop b next
      | .error fault => .error fault
  | 0, state => by simp [runTo]
  | a + 1, state => by
    rw [Nat.add_right_comm]
    by_cases h : state.rip = stop
    · simp [runTo, h, runTo_stop h]
    · simp only [runTo, h, ite_false]
      cases ByteEval.step text base state with
      | ok next => exact runTo_add text base stop b a next
      | error fault => rfl

theorem finish_timeout {core₀ : Core} {retAddr : Word} {state : ByteEval.State}
    (h : finish core₀ retAddr state ≠ .timeout) : state.rip = retAddr := by
  by_cases hne : state.rip = retAddr
  · exact hne
  · exact absurd (by simp [finish, hne]) h

/-- The object's run is clock monotone. -/
theorem exec_mono (bytes : ByteArray) (name : String) (base : Word) (core₀ : Core) (flags : ByteEval.Flags) :
    ClockMono (exec bytes name base core₀ flags) := by
  intro k k' hle hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold exec at hk ⊢
  cases ht : ELFRead.text? bytes with
  | none => rfl
  | some text =>
    cases he : ELF.entry? bytes name with
    | none => rfl
    | some offset =>
      cases hr : core₀.memory.read64? (core₀.readReg .rsp) with
      | error e => rfl
      | ok retAddr =>
        simp only [ht, he, hr] at hk ⊢
        rw [runTo_add]
        cases hrun : runTo text base retAddr k ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
        | error fault => rfl
        | ok state =>
          rw [hrun] at hk
          simp only at hk ⊢
          rw [runTo_stop (finish_timeout hk)]

end IxCC.X86.ObjectEval
