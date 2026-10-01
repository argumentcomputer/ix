import Compilatrix.X86.ObjectRun
import Compilatrix.X86.SafeStepsObject
import Compilatrix.Sem.Simulation

/-!
# Checked typed runs as runs of the object

The bridge from typed `X86.Eval` runs to the object's clocked semantics
`ObjectEval.exec`, through E1/E2 (`Stream.Valid`) and the ELF laws
(`ELF.Valid`), for an export whose caller returns outside the text:

- `exec_exit`: checked steps (`Stream.SafeSteps`) from the entry that end
  as an export does (`Exit`, 05 §6.1) are the object's outcome
  `statusResult st val` at some clock, with memory related outside the
  holes (`ObjectEval.run_exit`);
- `exec_running`: checked steps that end running, `n > 0` of them, leave
  the object running at clock `n − 1` (every typed step is at least one
  byte step, `Stream.safe_progress`);
- `sim_of_ends`: hence, from 05 §6.2's conclusion for every outcome of a
  clocked source (`Ends`, the shape of `Backend.safeSteps`, whose timeout
  clause asks for at least `b k` steps at clock `k`), a `Sem.Sim` from the
  source to the object with any clock map `f` with `k < b (f k)`
  (`sim_of_ends_succ`: `b = id`, `f k = k + 1`).
-/

namespace Compilatrix.X86.ObjectEval

open Compilatrix.Sem (Result Resource ClockMono Sim)

/-- A byte step decodes at `rip`, so `rip` is inside the text. -/
theorem step_inText {text : ByteArray} {base : Word} {state next : ByteEval.State}
    (h : ByteEval.step text base state = .ok next) : (state.rip - base).toNat < text.size := by
  unfold ByteEval.step at h
  cases hd : Decode.decodeAt text (state.rip - base).toNat with
  | none => rw [hd] at h; cases h
  | some d =>
    by_cases hlt : (state.rip - base).toNat < text.size
    · exact hlt
    · have hge : (state.rip - base).toNat ≥ text.size := Nat.le_of_not_lt hlt
      simp [Decode.decodeAt, hge] at hd

/-- A byte run that stays in the text does not stop at an address outside
it. -/
theorem runTo_of_run {text : ByteArray} {base stop : Word} (hout : text.size ≤ (stop - base).toNat) :
    ∀ {n : Nat} {state final : ByteEval.State}, ByteEval.run text base n state = .ok final →
      runTo text base stop n state = .ok final
  | 0, state, final, h => by simpa [ByteEval.run, runTo] using h
  | n + 1, state, final, h => by
    cases hs : ByteEval.step text base state with
    | error e => simp [ByteEval.run, hs] at h; cases h
    | ok next =>
      simp only [ByteEval.run, hs] at h
      have hne : state.rip ≠ stop := fun heq => by
        have := step_inText hs
        rw [heq] at this
        omega
      simp only [runTo, hne, ite_false, hs]
      exact runTo_of_run hout h

/-- Checked steps that end running are at least as many byte steps, ending
in a related state. -/
theorem safeSteps_bytes {runtime : Runtime} {checked : Checked} {output : Encode.Output}
    {externals : Stream.ExternalTargets} (valid : Stream.Valid checked.program output externals) (base : Word)
    {n : Nat} {holes finalHoles : Stream.Holes} {machine after : Machine}
    (steps : Stream.SafeSteps runtime checked n holes machine finalHoles after) :
    ∀ {state : ByteEval.State}, Stream.Related checked.program base holes machine state →
      after.status = .running →
      ∃ count final, n ≤ count ∧ ByteEval.run output.text base count state = .ok final ∧
        Stream.Related checked.program base finalHoles after final := by
  induction steps with
  | refl => exact fun related _ => ⟨0, _, Nat.le_refl 0, rfl, related⟩
  | @cons before middle after holes finalHoles count safe first rest ih =>
    intro state related running
    have middleRunning : middle.status = .running := by
      cases hm : middle.status with
      | running => rfl
      | halted v =>
        have := rest.steps.of_not_running (by simp [hm])
        rw [this, hm] at running; cases running
      | trapped t =>
        have := rest.steps.of_not_running (by simp [hm])
        rw [this, hm] at running; cases running
    obtain ⟨c₁, s₁, pos, _, run₁, related₁⟩ :=
      Stream.safe_progress valid runtime before base holes state related safe (first ▸ middleRunning)
    rw [first] at related₁
    obtain ⟨c₂, final, le₂, run₂, related₂⟩ := ih related₁ running
    refine ⟨c₁ + c₂, final, by omega, ?_, related₂⟩
    rw [Stream.byte_run_add, run₁]
    exact run₂

section Object

variable {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
  (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
  (entry : input.entryBlock = checked.program.entry)
  {base : Word} {core₀ : Core} {flags : ByteEval.Flags} {retAddr : Word}
  (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)

include stream object entry hret in
/-- The object's run from its entry symbol, which is the program's entry
block. -/
theorem exec_eq (k : Nat) :
    exec bytes input.exportName base core₀ flags k =
      match runTo input.encoded.text base retAddr k
          ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ with
      | .ok state => finish core₀ retAddr state
      | .error _ => .stuck := by
  have selected := object.entry
  rw [entry, stream.entryOffset] at selected
  simp only [exec, object.text, selected, hret]
  rfl

include stream object entry hret in
/-- Checked steps from the entry that end as an export does are the
object's outcome at some clock. -/
theorem exec_exit (hout : input.encoded.text.size ≤ (retAddr - base).toNat) {n : Nat}
    {holes : Stream.Holes} {after : Machine} {st val : Word}
    (steps : Stream.SafeSteps Runtime.rejecting checked n (fun _ => False) (Machine.initial checked core₀)
      holes after)
    (exit : Exit core₀ retAddr st val after) :
    ∃ k mem, exec bytes input.exportName base core₀ flags k = statusResult st val mem ∧
      Stream.MemoryRelated holes after.core.memory mem := by
  obtain ⟨count, s, _, _, executed, rip, rax, rdx, rsp, saved, related⟩ :=
    run_exit stream object entry base core₀ flags steps exit
  have selected := object.entry
  rw [entry, stream.entryOffset] at selected
  have hbytes : ByteEval.run input.encoded.text base count
      ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ =
      .ok s := by
    simp only [run, object.text, selected] at executed
    cases hb : ByteEval.run input.encoded.text base count
        ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ with
    | error e => rw [hb] at executed; cases executed
    | ok s' => rw [hb] at executed; cases executed; rfl
  have hrestored : restored core₀ s = true := by
    simp only [restored, Bool.and_eq_true, beq_iff_eq]
    refine ⟨rsp, ?_⟩
    rw [Array.all_eq_true_iff_forall_mem]
    intro r hr
    simp [saved r hr]
  refine ⟨count, s.core.memory, ?_, related⟩
  rw [exec_eq stream object entry hret, runTo_of_run (rip ▸ hout) hbytes]
  simp only [finish, rip, ite_true, hrestored, rax, rdx]

include stream object entry hret in
/-- Checked steps from the entry that end running leave the object running
one clock earlier. -/
theorem exec_running (hout : input.encoded.text.size ≤ (retAddr - base).toNat) {n : Nat}
    {holes : Stream.Holes} {after : Machine}
    (steps : Stream.SafeSteps Runtime.rejecting checked n (fun _ => False) (Machine.initial checked core₀)
      holes after)
    (running : after.status = .running) (pos : 0 < n) :
    exec bytes input.exportName base core₀ flags (n - 1) = .timeout := by
  obtain ⟨count, final, le, executed, _⟩ :=
    safeSteps_bytes stream base steps (Stream.initial_related checked base core₀ flags) running
  obtain ⟨r, hr⟩ : ∃ r, count = (n - 1) + (r + 1) := ⟨count - n, by omega⟩
  rw [hr, Stream.byte_run_add] at executed
  cases h₁ : ByteEval.run input.encoded.text base (n - 1)
      ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ with
  | error e => rw [h₁] at executed; cases executed
  | ok s₁ =>
    rw [h₁] at executed
    simp only [bind, Except.bind] at executed
    cases hs : ByteEval.step input.encoded.text base s₁ with
    | error e => simp [ByteEval.run, hs] at executed; cases executed
    | ok s₂ =>
      have hne : s₁.rip ≠ retAddr := fun heq => by
        have := step_inText hs
        rw [heq] at this
        omega
      rw [exec_eq stream object entry hret, runTo_of_run hout h₁]
      simp [finish, hne]

end Object

/-- 05 §6.2's conclusion (`Backend.safeSteps`) for an outcome `r` of a
clocked source: checked steps from the entry that end as the outcome
says, or in the target's own stack failure (status 2). A value ends with
status 0, its word in `rdx` and `Final` of the final memory; a resource
failure with its code, a trap with 4; a timeout running, after at least
`bound` steps. -/
def Ends (checked : Checked) (core₀ : Core) (retAddr : Word) {α : Type}
    (Final : α → Word → Memory → Stream.Holes → Prop) (bound : Nat) (r : Result α) : Prop :=
  ∃ n holes after, Stream.SafeSteps Runtime.rejecting checked n (fun _ => False) (Machine.initial checked core₀)
      holes after ∧
    ((∃ val, Exit core₀ retAddr 2 val after) ∨
      match r with
      | .ok v => ∃ val, Exit core₀ retAddr 0 val after ∧ Final v val after.core.memory holes
      | .timeout => bound ≤ n ∧ after.status = .running
      | .resource failure => ∃ val, Exit core₀ retAddr (Resource.code failure) val after
      | .trap => ∃ val, Exit core₀ retAddr 4 val after
      | .stuck => True)

/-- `Final` seen through the object's memory: the typed final memory is
related to the object's outside the holes. -/
def Lifted {α : Type} (Final : α → Word → Memory → Stream.Holes → Prop) (v : α) (w : Word × Memory) : Prop :=
  ∃ mem holes, Final v w.1 mem holes ∧ Stream.MemoryRelated holes mem w.2

@[simp] theorem statusResult_zero (val : Word) (mem : Memory) : statusResult 0 val mem = .ok (val, mem) := by
  simp [statusResult]

@[simp] theorem statusResult_code (failure : Resource) (val : Word) (mem : Memory) :
    statusResult (Resource.code failure) val mem = .resource failure := by
  cases failure <;> simp [statusResult, Resource.code]

@[simp] theorem statusResult_four (val : Word) (mem : Memory) : statusResult 4 val mem = .trap := by
  simp [statusResult]

theorem statusResult_two (val : Word) (mem : Memory) : statusResult 2 val mem = .resource .stack :=
  statusResult_code .stack val mem

section Sim

variable {checked : Checked} {input : ELF.Input} {bytes : ByteArray}
  (stream : Stream.Valid checked.program input.encoded) (object : ELF.Valid input bytes)
  (entry : input.entryBlock = checked.program.entry)
  {base : Word} {core₀ : Core} (flags : ByteEval.Flags) {retAddr : Word}
  (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)
  (hout : input.encoded.text.size ≤ (retAddr - base).toNat)

include stream object entry hret hout in
/-- 05 §6.2's conclusion at every clock, with step bound `b k` at clock
`k`, gives a simulation of the source by the object, with any clock map
`f` such that the bound at `f k` exceeds `k`. -/
theorem sim_of_ends {α : Type} {Final : α → Word → Memory → Stream.Holes → Prop} {c : Nat → Result α}
    {b f : Nat → Nat} (hb : ∀ k, k + 1 ≤ b (f k))
    (hends : ∀ k, c k ≠ .stuck → Ends checked core₀ retAddr Final (b k) (c k)) :
    Sim (Lifted Final) f c (exec bytes input.exportName base core₀ flags) where
  forward k hk := by
    cases hc : c k with
    | stuck => exact ⟨0, .stuck⟩
    | timeout => exact absurd hc hk
    | ok v =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex, hf⟩
      · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, hm⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_zero]; exact .ok ⟨_, _, hf, hm⟩⟩
    | resource failure =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex⟩
      · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_code]; exact .resource _⟩
    | trap =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex⟩
      · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout steps ex
        exact ⟨k', by rw [he, statusResult_four]; exact .trap⟩
  timeout k hk := by
    obtain ⟨n, holes, after, steps, h⟩ := hends (f k) (by simp [hk])
    rw [hk] at h
    have hbk := hb k
    rcases h with ⟨val, ex⟩ | ⟨le, running⟩
    · obtain ⟨k', mem, he, _⟩ := exec_exit stream object entry hret hout (flags := flags) steps ex
      rw [statusResult_two] at he
      by_cases ht : exec bytes input.exportName base core₀ flags k = .timeout
      · exact .inl ht
      · refine .inr ⟨.stack, ?_⟩
        rw [(exec_mono bytes input.exportName base core₀ flags).eq_of_ne_timeout (k' := k') ht (by rw [he]; simp), he]
    · have := exec_running stream object entry hret hout (flags := flags) steps running (by omega)
      exact .inl ((exec_mono bytes input.exportName base core₀ flags).timeout_of_le (by omega) this)

include stream object entry hret hout in
/-- With step bound `k` at clock `k`, the clock map is `k ↦ k + 1`. -/
theorem sim_of_ends_succ {α : Type} {Final : α → Word → Memory → Stream.Holes → Prop} {c : Nat → Result α}
    (hends : ∀ k, c k ≠ .stuck → Ends checked core₀ retAddr Final k (c k)) :
    Sim (Lifted Final) (fun k => k + 1) c (exec bytes input.exportName base core₀ flags) :=
  sim_of_ends stream object entry flags hret hout (b := id) (fun _ => Nat.le_refl _) hends

end Sim

end Compilatrix.X86.ObjectEval
