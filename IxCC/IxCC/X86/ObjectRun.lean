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

/-! ## Read-only memory framing

No byte-machine step can alter memory permissions or overwrite any byte whose
`writable` bit is `false`. In particular, a `.rodata` section mapped read-only
is preserved byte-for-byte across arbitrary `runTo` and `ObjectEval` runs. -/

section ReadOnlyFraming

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-- `after` preserves all memory permissions of `before` and agrees with
`before` on every byte whose `writable` bit is `false`. -/
def ReadOnlyFrame (before after : Memory) : Prop :=
  after.readable = before.readable ∧
  after.writable = before.writable ∧
  ∀ a : Word, before.writable a = false → after.bytes a = before.bytes a

theorem ReadOnlyFrame.refl (m : Memory) : ReadOnlyFrame m m :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem ReadOnlyFrame.trans {a b c : Memory} (h1 : ReadOnlyFrame a b) (h2 : ReadOnlyFrame b c) :
    ReadOnlyFrame a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun addr hnw =>
    (h2.2.2 addr (h1.2.1.symm ▸ hnw)).trans (h1.2.2 addr hnw)⟩

private theorem rangeAllowed_mem {p : Word → Bool} {addr : Word} :
    ∀ {count : Nat}, Memory.rangeAllowed p addr count = true →
      ∀ j < count, p (addr + UInt64.ofNat j) = true
  | 0, _, _, hj => by omega
  | count + 1, h, j, hj => by
      simp only [Memory.rangeAllowed, Bool.and_eq_true] at h
      by_cases hlast : j = count
      · subst hlast; exact h.2
      · exact rangeAllowed_mem h.1 j (by omega)

private theorem writeLittle_perms (m : Memory) (addr val : Word) :
    ∀ count, (m.writeLittle addr val count).readable = m.readable ∧
      (m.writeLittle addr val count).writable = m.writable
  | 0 => ⟨rfl, rfl⟩
  | count + 1 => by
      simp only [Memory.writeLittle, Memory.writeByte]
      exact writeLittle_perms m addr val count

theorem write?_readOnlyFrame {m m' : Memory} {w : Width} {addr val : Word}
    (h : m.write? w addr val = .ok m') : ReadOnlyFrame m m' := by
  unfold Memory.write? at h
  split at h
  · next hall =>
      cases h
      have hp := writeLittle_perms m addr val w.bytes
      refine ⟨hp.1, hp.2, fun a hnw => ?_⟩
      apply Memory.writeLittle_bytes_outside
      intro j hj heq
      have ht := rangeAllowed_mem hall j hj
      rw [heq] at hnw
      rw [ht] at hnw
      cases hnw
  · cases h

private theorem arg_store_readOnlyFrame {before core after : Core} {w : Width} {val : Word} {arg : Arg}
    (h : arg.store before w val core = .ok after) : ReadOnlyFrame core.memory after.memory := by
  cases arg with
  | reg r => cases h; cases w <;> exact ReadOnlyFrame.refl _
  | imm _ => cases h; exact ReadOnlyFrame.refl _
  | mem addr =>
      simp only [Arg.store] at h
      cases hw : core.memory.write? w (addr.eval before) val with
      | error e => simp [hw] at h
      | ok m' =>
          simp only [hw, Except.ok.injEq, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact write?_readOnlyFrame hw

private theorem writeSlots_readOnlyFrame (before : Core) (slots : List Slot) (args : List Arg)
    (results : List Word) :
    ∀ {core after : Core}, writeSlots before core slots args results = .ok after →
      ReadOnlyFrame core.memory after.memory := by
  induction slots generalizing args results with
  | nil =>
      intro core after h
      cases args <;> (cases h; exact ReadOnlyFrame.refl _)
  | cons slot slots ih =>
      intro core after h
      cases args with
      | nil => cases h; exact ReadOnlyFrame.refl _
      | cons arg args =>
          unfold writeSlots at h
          cases hrole : slot.role <;> rw [hrole] at h
          case read | address => exact ih args results h
          all_goals
            cases hs : arg.store before slot.width (results.headD 0) core with
            | error e => rw [hs] at h; cases h
            | ok mid =>
                rw [hs] at h
                exact (arg_store_readOnlyFrame hs).trans (ih args results.tail h)

private theorem writeImplicits_memory (core : Core) (implicits : List Implicit) (results : List Word) :
    (writeImplicits core implicits results).memory = core.memory := by
  induction implicits generalizing core results with
  | nil => rfl
  | cons imp imps ih =>
      simp only [writeImplicits]
      split
      · rw [ih]; cases imp.width <;> rfl
      · exact ih _ _

private theorem stage_readOnlyFrame {o : Op} {core after : Core} {out : SemOut}
    (h : o.stage core out = .ok after) : ReadOnlyFrame core.memory after.memory := by
  unfold Op.stage at h
  cases hst : (desc o).stack <;> rw [hst] at h
  · cases h; exact ReadOnlyFrame.refl _
  · cases hw : core.memory.write64? (core.readReg .rsp - 8) (out.results.headD 0) with
    | error e => rw [hw] at h; cases h
    | ok m' =>
        rw [hw] at h; cases h
        exact write?_readOnlyFrame hw
  · cases h; exact ReadOnlyFrame.refl _

private theorem op_exec_readOnlyFrame {o : Op} {args : List Arg} {core after : Core}
    {flags flags' : ByteEval.Flags} (h : o.exec args core flags = .ok (after, flags')) :
    ReadOnlyFrame core.memory after.memory := by
  unfold Op.exec Op.run at h
  cases hi : o.inputs args core with
  | error e => simp [hi, Except.mapError] at h
  | ok inputs =>
    cases hsem : (desc o).sem ⟨inputs, flags.restrict (desc o).flagsIn⟩ with
    | error e => simp [hi, hsem, Except.mapError] at h
    | ok out =>
      cases hst : o.stage core out with
      | error e => simp [hi, hsem, hst, Except.mapError] at h
      | ok staged =>
        cases hws : writeSlots core staged (desc o).slots args out.results with
        | error e => simp [hi, hsem, hst, hws, Except.mapError] at h
        | ok written =>
          simp only [hi, hsem, hst, hws, Except.mapError, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h1 := (stage_readOnlyFrame hst).trans (writeSlots_readOnlyFrame core _ args _ hws)
          rw [writeImplicits_memory]
          exact h1

/-- Every single byte-machine step preserves all permissions and every
non-writable byte (such as `.rodata`). -/
theorem step_readOnlyFrame {text : ByteArray} {base : Word} {state next : ByteEval.State}
    (h : ByteEval.step text base state = .ok next) :
    ReadOnlyFrame state.core.memory next.core.memory := by
  unfold ByteEval.step at h
  cases hd : Decode.decodeAt text (state.rip - base).toNat with
  | none => simp [hd] at h
  | some decoded =>
      simp only [hd] at h
      unfold ByteEval.execute at h
      cases hop : decoded.operation with
      | op o args =>
          simp only [hop] at h
          split at h
          · -- call rel32
            cases hw : state.core.memory.write64? (state.core.readReg .rsp - 8)
                (state.rip + UInt64.ofNat decoded.length) with
            | error e => simp [hw, Except.mapError] at h
            | ok m' =>
                simp only [hw, Except.mapError] at h
                cases h
                exact write?_readOnlyFrame hw
          · -- jmp rel32
            cases h
            exact ReadOnlyFrame.refl _
          · -- jcc rel32
            simp only [Except.mapError] at h
            split at h
            · cases h
            · cases h
              exact ReadOnlyFrame.refl _
          · -- ret
            cases hr : state.core.memory.read64? (state.core.readReg .rsp) with
            | error e => simp [hr, Except.mapError] at h
            | ok target =>
                simp only [hr, Except.mapError] at h
                cases h
                exact ReadOnlyFrame.refl _
          · -- any linear instruction via `Op.exec`
            simp only [Except.mapError] at h
            split at h
            · cases h
            · next res hex =>
                cases h
                exact op_exec_readOnlyFrame hex

/-- Any bounded `runTo` execution preserves memory permissions and every
non-writable byte. -/
theorem runTo_readOnlyFrame {text : ByteArray} {base stop : Word} :
    ∀ {fuel : Nat} {state final : ByteEval.State},
      runTo text base stop fuel state = .ok final →
      ReadOnlyFrame state.core.memory final.core.memory
  | 0, state, final, h => by
      simp only [runTo, Except.ok.injEq] at h
      cases h; exact ReadOnlyFrame.refl _
  | fuel + 1, state, final, h => by
      unfold runTo at h
      split at h
      · cases h; exact ReadOnlyFrame.refl _
      · cases hs : ByteEval.step text base state with
        | error e => simp [hs] at h
        | ok next =>
            simp only [hs] at h
            exact (step_readOnlyFrame hs).trans (runTo_readOnlyFrame h)

end ReadOnlyFraming

end IxCC.X86.ObjectEval
