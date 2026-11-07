import IxCC.X86.ObjectCall
import IxCC.X86.ObjectRunSafe

/-!
# Checked typed runs as calls of an exported symbol

`ObjectRunSafe` for `ObjectEval.call`, the run of any exported symbol: the
same bridge from typed `X86.Eval` runs to the object, with the symbol's
offset in place of the entry symbol's. The premises name what the bridge
reads: the object's text is the encoded program's (`ELFRead.text?`), and the
symbol's offset is that of the typed program's entry block
(`ELF.symbol?`). A program with another entry block is the same program
started elsewhere (`Checked.withEntry`): its steps and its encoding do not
read the entry.

- `ELF.Valid.symbol_entry`: in a valid object, the entry symbol is also the
  first global function symbol of its name, so `symbol?` finds it;
  `ELF.Valid.exported` gives the other exports;
- `call_exit`, `call_running`: checked steps that exit as an export does
  are the call's outcome at some clock; checked steps that end running
  leave the call running one clock earlier;
- `call_sim_of_ends`: 05 §6.2's conclusion at every clock (`ObjectEval.Ends`)
  gives a simulation of the source by the call, for any clock map `f` with
  `k < b (f k)`.
-/

namespace IxCC.X86

/-- A well-formed program started at another of its blocks is well formed:
only the entry bound reads the entry. -/
theorem Program.wellFormed_withEntry {p : Program} (wf : p.wellFormed = true) {b : BlockId}
    (hb : b.toNat < p.blocks.size) : ({ p with entry := b } : Program).wellFormed = true := by
  have hp := wf
  simp only [Program.wellFormed, Bool.and_eq_true, and_assoc] at hp ⊢
  obtain ⟨h₁, h₂, -, h₄⟩ := hp
  exact ⟨h₁, h₂, by simpa [Program.hasBlock] using hb, h₄⟩

/-- A checked program started at another of its blocks. -/
def Checked.withEntry (c : Checked) (b : BlockId) (hb : b.toNat < c.program.blocks.size) : Checked :=
  ⟨{ c.program with entry := b }, Program.wellFormed_withEntry c.valid hb⟩

@[simp] theorem Checked.withEntry_program (c : Checked) (b : BlockId) (hb : b.toNat < c.program.blocks.size) :
    (c.withEntry b hb).program = { c.program with entry := b } := rfl

/-- The encoding's certificate does not read the entry. -/
theorem Stream.Valid.withEntry {p : Program} {output : Encode.Output} {externals : Stream.ExternalTargets}
    (valid : Stream.Valid p output externals) (b : BlockId) :
    Stream.Valid { p with entry := b } output externals := by
  cases p
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := valid
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end IxCC.X86

namespace IxCC.X86.ELF

/-- In a valid object the entry symbol is the first global function symbol
of its name defined in `.text`, at the entry block's offset. -/
theorem Valid.symbol_entry {input : Input} {bytes : ByteArray} (valid : Valid input bytes) :
    symbol? bytes input.exportName = input.encoded.blockOffsets[input.entryBlock.toNat]? := by
  obtain ⟨view, parsed, fields⟩ := valid
  obtain ⟨offset, _, found, _, _, _, symbols⟩ := fields.entry
  have hfind : (view.symbols.map symbolMeaning).find? (definesName input.exportName) =
      some (entryMeaning input offset) := by
    rw [symbols, expectedSymbols, List.find?_toArray,
      List.find?_cons_of_neg (by simp [definesName]), List.find?_cons_of_neg (by simp [definesName])]
    simp [definesName, entryMeaning]
  rw [Array.find?_map] at hfind
  obtain ⟨symbol, lookup, meaning⟩ := Option.map_eq_some_iff.mp hfind
  have value := congrArg SymbolMeaning.value meaning
  simp only [symbolMeaning, entryMeaning] at value
  have same : (fun s => definesName input.exportName (symbolMeaning s)) =
      definesName input.exportName ∘ symbolMeaning := rfl
  simp only [symbol?, parsed, Option.bind_eq_bind, Option.bind_some, same, lookup]
  simp [value, found]

end IxCC.X86.ELF

namespace IxCC.X86.ObjectEval

open IxCC.Sem (Result Resource ClockMono Sim)

section Call

variable {checked : Checked} {output : Encode.Output} {bytes : ByteArray} {name : String}
  (stream : Stream.Valid checked.program output) (htext : ELFRead.text? bytes = some output.text)
  (hsym : ELF.symbol? bytes name = output.blockOffsets[checked.program.entry.toNat]?)
  {base : Word} {core₀ : Core} {flags : ByteEval.Flags} {retAddr : Word}
  (hret : core₀.memory.read64? (core₀.readReg .rsp) = .ok retAddr)

include stream htext hsym hret in
/-- The call starts at the typed program's entry block. -/
theorem call_eq (k : Nat) :
    call bytes name base core₀ flags k =
      match runTo output.text base retAddr k
          ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ with
      | .ok state => finish core₀ retAddr state
      | .error _ => .stuck := by
  rw [stream.entryOffset] at hsym
  simp only [call, htext, hsym, hret]
  rfl

include stream htext hsym hret in
/-- Checked steps from the entry that end as an export does are the call's
outcome at some clock. -/
theorem call_exit (hout : output.text.size ≤ (retAddr - base).toNat) {n : Nat}
    {holes : Stream.Holes} {after : Machine} {st val : Word}
    (steps : Stream.SafeSteps Runtime.rejecting checked n (fun _ => False) (Machine.initial checked core₀)
      holes after)
    (exit : Exit core₀ retAddr st val after) :
    ∃ k mem, call bytes name base core₀ flags k = statusResult st val mem ∧
      Stream.MemoryRelated holes after.core.memory mem := by
  obtain ⟨count, s, _, _, executed, rip, related⟩ :=
    steps.run_with_calls stream base _ (Stream.initial_related checked base core₀ flags) exit.halted exit.slot
  have rax := steps.steps.halted_rax rfl exit.halted
  have register (target : GPR) (other : target ≠ .rsp) : s.core.readReg target = after.core.readReg target := by
    rw [← related.readReg target]
    simp [Core.readReg, Core.setReg, Registers.set, other]
  have hrestored : restored core₀ s = true := by
    simp only [restored, Bool.and_eq_true, beq_iff_eq]
    refine ⟨?_, ?_⟩
    · rw [← related.readReg .rsp, exit.rsp]
      simp [Core.readReg, Core.setReg, Registers.set]
    · rw [Array.all_eq_true_iff_forall_mem]
      intro r hr
      have hr' : r ∈ SysV.calleeSaved := hr
      rw [register r (rsp_not_calleeSaved hr'), exit.saved r hr']
      simp
  refine ⟨count, s.core.memory, ?_, related.memory⟩
  rw [call_eq stream htext hsym hret, runTo_of_run (rip ▸ hout) executed]
  simp only [finish, rip, ite_true, hrestored]
  rw [register .rax (by decide), register .rdx (by decide), rax, exit.value]

include stream htext hsym hret in
/-- Checked steps from the entry that end running leave the call running
one clock earlier. -/
theorem call_running (hout : output.text.size ≤ (retAddr - base).toNat) {n : Nat}
    {holes : Stream.Holes} {after : Machine}
    (steps : Stream.SafeSteps Runtime.rejecting checked n (fun _ => False) (Machine.initial checked core₀)
      holes after)
    (running : after.status = .running) (pos : 0 < n) :
    call bytes name base core₀ flags (n - 1) = .timeout := by
  obtain ⟨count, final, le, executed, _⟩ :=
    safeSteps_bytes stream base steps (Stream.initial_related checked base core₀ flags) running
  obtain ⟨r, hr⟩ : ∃ r, count = (n - 1) + (r + 1) := ⟨count - n, by omega⟩
  rw [hr, Stream.byte_run_add] at executed
  cases h₁ : ByteEval.run output.text base (n - 1)
      ⟨core₀, base + UInt64.ofNat (Stream.blockOffset checked.program checked.program.entry.toNat), flags⟩ with
  | error e => rw [h₁] at executed; cases executed
  | ok s₁ =>
    rw [h₁] at executed
    simp only [bind, Except.bind] at executed
    cases hs : ByteEval.step output.text base s₁ with
    | error e => simp [ByteEval.run, hs] at executed; cases executed
    | ok s₂ =>
      have hne : s₁.rip ≠ retAddr := fun heq => by
        have := step_inText hs
        rw [heq] at this
        omega
      rw [call_eq stream htext hsym hret, runTo_of_run hout h₁]
      simp [finish, hne]

include stream htext hsym hret in
/-- 05 §6.2's conclusion at every clock, with step bound `b k` at clock
`k`, gives a simulation of the source by the call, with any clock map `f`
such that the bound at `f k` exceeds `k`. -/
theorem call_sim_of_ends (hout : output.text.size ≤ (retAddr - base).toNat) {α : Type}
    {Final : α → Word → Memory → Stream.Holes → Prop} {c : Nat → Result α}
    {b f : Nat → Nat} (hb : ∀ k, k + 1 ≤ b (f k))
    (hends : ∀ k, c k ≠ .stuck → Ends checked core₀ retAddr Final (b k) (c k)) :
    Sim (Lifted Final) f c (call bytes name base core₀ flags) where
  forward k hk := by
    cases hc : c k with
    | stuck => exact ⟨0, .stuck⟩
    | timeout => exact absurd hc hk
    | ok v =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex, hf⟩
      · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, hm⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_zero]; exact .ok ⟨_, _, hf, hm⟩⟩
    | resource failure =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex⟩
      · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_code]; exact .resource _⟩
    | trap =>
      obtain ⟨n, holes, after, steps, h⟩ := hends k (by simp [hc])
      rw [hc] at h
      rcases h with ⟨val, ex⟩ | ⟨val, ex⟩
      · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_two]; exact .resource _⟩
      · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
        exact ⟨k', by rw [he, statusResult_four]; exact .trap⟩
  timeout k hk := by
    obtain ⟨n, holes, after, steps, h⟩ := hends (f k) (by simp [hk])
    rw [hk] at h
    have hbk := hb k
    rcases h with ⟨val, ex⟩ | ⟨le, running⟩
    · obtain ⟨k', mem, he, _⟩ := call_exit stream htext hsym hret hout (flags := flags) steps ex
      rw [statusResult_two] at he
      by_cases ht : call bytes name base core₀ flags k = .timeout
      · exact .inl ht
      · refine .inr ⟨.stack, ?_⟩
        rw [(call_mono bytes name base core₀ flags).eq_of_ne_timeout (k' := k') ht (by rw [he]; simp), he]
    · have := call_running stream htext hsym hret hout (flags := flags) steps running (by omega)
      exact .inl ((call_mono bytes name base core₀ flags).timeout_of_le (by omega) this)

end Call

end IxCC.X86.ObjectEval
