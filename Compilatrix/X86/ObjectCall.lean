import Compilatrix.X86.ObjectRun

/-!
# A call of any exported symbol, as a clocked semantics

`ObjectEval.call bytes name base core₀ flags` is `ObjectEval.exec` with the
symbol looked up as a linker does: the first global function symbol named
`name` defined in `.text` (`ELF.symbol?`), rather than the entry symbol
(`ELF.entry?`). It runs any export of the object, `main`'s wrapper, `cx_init`
or another root's, the way `runtime_driver.c` calls `cx_init` and
`-DENTRY=cx_<root>`. Everything else is `exec`'s: the text from the bytes,
the caller's return address in the word at `rsp`, at most `k` byte steps
stopping at the return address (`runTo`), and the status and value in
`rax:rdx` (`finish`).

`call_mono`: the clock only extends the run.
-/

namespace Compilatrix.X86.ObjectEval

open Compilatrix.Sem (Result ClockMono)

/-- The clocked run of the object's exported symbol `name` from `core₀`. -/
def call (bytes : ByteArray) (name : String) (base : Word) (core₀ : Core) (flags : ByteEval.Flags)
    (k : Nat) : Result (Word × Memory) :=
  match ELFRead.text? bytes, ELF.symbol? bytes name, core₀.memory.read64? (core₀.readReg .rsp) with
  | some text, some offset, .ok retAddr =>
      match runTo text base retAddr k ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
      | .ok state => finish core₀ retAddr state
      | .error _ => .stuck
  | _, _, _ => .stuck

/-- A call of an exported symbol is clock monotone. -/
theorem call_mono (bytes : ByteArray) (name : String) (base : Word) (core₀ : Core) (flags : ByteEval.Flags) :
    ClockMono (call bytes name base core₀ flags) := by
  intro k k' hle hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold call at hk ⊢
  cases ht : ELFRead.text? bytes with
  | none => rfl
  | some text =>
    cases he : ELF.symbol? bytes name with
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

end Compilatrix.X86.ObjectEval
