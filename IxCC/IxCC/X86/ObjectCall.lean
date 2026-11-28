import IxCC.X86.ObjectRun
import IxCC.X86.ELFRodata

/-!
# A call of any exported symbol, as a clocked semantics

`ObjectEval.call bytes name base core₀ flags` is `ObjectEval.exec` with the
symbol looked up as a linker does: the first global function symbol named
`name` defined in `.text` (`ELF.symbol?`), rather than the entry symbol
(`ELF.entry?`). It runs any export of the object, `main`'s wrapper, `cx_init`
or another root's, the way an executable's shell calls `cx_init` and a root's
`cx_<root>`. Everything else is `exec`'s: the text from the bytes,
the caller's return address in the word at `rsp`, at most `k` byte steps
stopping at the return address (`runTo`), and the status and value in
`rax:rdx` (`finish`).

`call_mono`: the clock only extends the run.
-/

namespace IxCC.X86.ObjectEval

open IxCC.Sem (Result ClockMono)

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

/-- An object's `.rodata` section is loaded read-only at `rodataBase` in `mem`. -/
def RodataLoaded (bytes : ByteArray) (rodataBase : Word) (mem : Memory) : Prop :=
  ∃ rodata, ELFRead.rodata? bytes = some rodata ∧ ELFRodata.RodataMapped rodataBase rodata mem

/-- Read-only framing across `ObjectEval.call`: any successful call preserves
all memory permissions and every non-writable byte. -/
theorem call_readOnlyFrame {bytes : ByteArray} {name : String} {base : Word} {core₀ : Core}
    {flags : ByteEval.Flags} {k : Nat} {val : Word} {mem' : Memory}
    (h : call bytes name base core₀ flags k = .ok (val, mem')) :
    ReadOnlyFrame core₀.memory mem' := by
  unfold call at h
  cases ht : ELFRead.text? bytes with
  | none => simp [ht] at h
  | some text =>
    cases hs : ELF.symbol? bytes name with
    | none => simp [ht, hs] at h
    | some offset =>
      cases hr : core₀.memory.read64? (core₀.readReg .rsp) with
      | error e => simp [ht, hs, hr] at h
      | ok retAddr =>
        simp only [ht, hs, hr] at h
        cases hrun : runTo text base retAddr k ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
        | error e => simp [hrun] at h
        | ok final =>
          simp only [hrun, finish, statusResult] at h
          split at h
          · split at h
            · split at h
              · cases h
                exact runTo_readOnlyFrame hrun
              · split at h
                · cases h
                · split at h
                  · cases h
                  · split at h
                    · cases h
                    · split at h <;> cases h
            · cases h
          · cases h

/-- Read-only `.rodata` preservation across `ObjectEval.call`: if the object's
`.rodata` section is loaded read-only at `rodataBase`, every successful call
preserves it byte-for-byte with unchanged read-only permissions. -/
theorem call_preserves_rodata {bytes : ByteArray} {name : String} {base rodataBase : Word}
    {core₀ : Core} {flags : ByteEval.Flags} {k : Nat} {val : Word} {mem' : Memory}
    (hro : RodataLoaded bytes rodataBase core₀.memory)
    (h : call bytes name base core₀ flags k = .ok (val, mem')) :
    RodataLoaded bytes rodataBase mem' := by
  obtain ⟨rodata, hparse, hm⟩ := hro
  have hfr := call_readOnlyFrame h
  refine ⟨rodata, hparse, ?_⟩
  exact {
    nonzero := hm.nonzero
    aligned := hm.aligned
    fit := hm.fit
    bytes_eq := fun i hi => (hfr.2.2 _ (hm.readonly i hi)).trans (hm.bytes_eq i hi)
    readable := fun i hi => hfr.1.symm ▸ hm.readable i hi
    readonly := fun i hi => hfr.2.1.symm ▸ hm.readonly i hi }

end IxCC.X86.ObjectEval
