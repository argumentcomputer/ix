import IxCC.X86.Exe.Machine.Proof.Effects
import IxCC.X86.ByteControl

/-!
# A checked shell's instructions, executed (X0-P, third part)

`Shell.Valid p image origin ex` (what `Shell.check` establishes when the
writer runs it) says where every instruction and terminator of the shell `p`
is in the file and what the byte decoder reads there. This module turns that
into steps of the process, for any shell:

- `Valid.step_instr`, `Valid.step_ok`: a linear instruction is the byte
  machine's `execute` of its operation, and moves `rip` to the next
  instruction (`next_addr`);
- `Valid.run_branch`, `Valid.step_jump`, `Valid.step_ret`: a block's
  terminator, its producer's flags deciding the branch;
- `Valid.callsTo`: an export call is a `call rel32` landing on the export
  (the call lemma's `CallsTo`); `Valid.step_call`: an internal call;
- `Valid.syscall_at`: at a `syscall` the decoder decodes nothing and the
  bytes are `0F 05`, so the only step there is the platform's system call.

**Traces counted in steps.** `RunN` is `Process.Run` with its number of
steps, `TraceN` a trace whose run takes at most `n` steps. Every trace is one
(`Trace.toN`), so a proof about traces may go by induction on the steps.
`TraceN.through`: a trace from the start of a run of `m` byte-machine steps is
empty or passes its end with `m` steps fewer; `TraceN.sys`: a trace from a
`syscall` (nothing decodes and the bytes are `0F 05`, so neither the byte
machine's rule nor `Process.Step`'s `unknown` applies) is empty or begins with
the platform's event for it.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.X86.Encode (instructionOperation linearInstruction)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)

/-! ## Positions -/

theorem fetch_index {pos : Nat} (h : fileBase + pos < 2 ^ 64) :
    (UInt64.ofNat (fileBase + pos) - fetchBase).toNat = pos := by
  have he : UInt64.ofNat (fileBase + pos) - fetchBase = UInt64.ofNat pos := by
    rw [UInt64.ofNat_add]
    show UInt64.ofNat fileBase + UInt64.ofNat pos - UInt64.ofNat fileBase = _
    rw [UInt64.add_comm, UInt64.add_sub_cancel]
  rw [he, UInt64.toNat_ofNat_of_lt' (by show pos < 18446744073709551616; omega)]

theorem instrOffset_zero (blk : Shell.Block) : instrOffset blk 0 = 0 := by
  simp [instrOffset]

theorem instrOffset_succ {blk : Shell.Block} {j : Nat} {i : Shell.Instr} (h : blk.instructions[j]? = some i) :
    instrOffset blk (j + 1) = instrOffset blk j + Shell.Instr.size i := by
  unfold instrOffset
  have h' : blk.instructions.toList[j]? = some i := by rw [Array.getElem?_toList]; exact h
  rw [List.take_add_one, h', List.map_append, List.sum_append]
  simp

/-- The next instruction's address. -/
theorem next_addr {p : Shell.Program} {origin b : Nat} {blk : Shell.Block} {j : Nat} {i : Shell.Instr}
    (hi : blk.instructions[j]? = some i) :
    UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j)) + UInt64.ofNat (Shell.Instr.size i) =
      UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk (j + 1))) := by
  rw [instrOffset_succ hi, ← UInt64.ofNat_add]
  congr 1
  omega

theorem decodes_some {image : ByteArray} {pos : Nat} {op : Decode.Operation} {len : Nat}
    (h : Stream.decodes image pos op len = true) : Decode.decodeAt image pos = some ⟨op, len⟩ := by
  simpa [Stream.decodes] using h

/-! ## Instructions -/

section
variable {p : Shell.Program} {image : ByteArray} {origin : Nat} {ex : String → Option Nat}

/-- **A linear instruction** of a checked shell is the byte machine's `execute` of its operation. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_instr (hv : Shell.Valid p image origin ex) (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat} {i : X86.Instr}
    (hi : blk.instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j))) :
    ByteEval.step image fetchBase s = ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s := by
  have hm := hv.instr b blk hb j _ hi
  have hm' : Stream.decodes image (origin + blockOffset p b + instrOffset blk j) (instructionOperation i)
      (Shell.Instr.size (.instr i)) = true := by
    cases i with
    | call t => exact absurd rfl (hnc t)
    | _ => simp only [Shell.instrMatches, Bool.and_eq_true] at hm; exact hm.2
  have hd := decodes_some hm'
  have hlt := decodeAt_lt hd
  unfold ByteEval.step
  rw [hrip, fetch_index (by omega), hd]

/-- A linear instruction whose `execute` is known, as a step to the next instruction. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_ok (hv : Shell.Valid p image origin ex) (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat} {i : X86.Instr}
    (hi : blk.instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j)))
    {core : Core} {fl : ByteEval.Flags}
    (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Shell.Instr.size (.instr i)), fl⟩) :
    ByteEval.step image fetchBase s =
      .ok ⟨core, UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk (j + 1))), fl⟩ := by
  rw [hv.step_instr hfit hb hi hnc hrip, hex, hrip, next_addr hi]

/-- A linear instruction whose `execute` faults on memory, as a step that faults. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_fault (hv : Shell.Valid p image origin ex) (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat} {i : X86.Instr}
    (hi : blk.instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j)))
    {f : MemoryFault} (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s = .error (.memory f)) :
    ByteEval.step image fetchBase s = .error (.memory f) := by
  rw [hv.step_instr hfit hb hi hnc hrip, hex]

/-- `rip` past `n` bytes. -/
theorem addr_add {rip : Word} {pos : Nat} (h : rip = UInt64.ofNat (fileBase + pos)) (n : Nat) :
    rip + UInt64.ofNat n = UInt64.ofNat (fileBase + (pos + n)) := by
  rw [h, ← UInt64.ofNat_add]
  congr 1
  omega

/-- The address a `rel32` control operation at `pos` reaches, when the check says it reaches block `t`. -/
theorem targets_lands {pos len : Nat} {t : BlockId} {op : Imm32 → Decode.Operation}
    (h : Shell.targets p image origin pos op len t = true) :
    t.toNat < p.blocks.size ∧
    Decode.decodeAt image pos = some ⟨op (Stream.displacement (pos + len) (origin + blockOffset p t.toNat)), len⟩ ∧
    ∀ rip : Word, rip = UInt64.ofNat (fileBase + pos) →
      ByteEval.relative (rip + UInt64.ofNat len) (Stream.displacement (pos + len) (origin + blockOffset p t.toNat)) =
        UInt64.ofNat (fileBase + (origin + blockOffset p t.toNat)) := by
  simp only [Shell.targets, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ht, hfits⟩, hdec⟩ := h
  refine ⟨ht, decodes_some hdec, fun rip hrip => ?_⟩
  have hr := Encode.relative_resolves_base (UInt64.ofNat fileBase) (pos + len) (origin + blockOffset p t.toNat)
    (by push_cast; exact hfits)
  rw [← UInt64.ofNat_add, ← UInt64.ofNat_add] at hr
  rw [addr_add hrip len]
  exact hr

/-- **A branch terminator**: the producer at the terminator's address, then `jcc` and (when not
taken) `jmp`, reach the block the producer's flags choose, with the producer's core and flags. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.run_branch (hv : Shell.Valid p image origin ex)
    (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {o : Op} {args : List Arg} {cond : Condition}
    {yes no : BlockId} (hterm : blk.terminator = .branch o args cond yes no .rel32) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk blk.instructions.size)))
    {core : Core} {fl : ByteEval.Flags} {taken : Bool}
    (hex : ByteEval.execute ⟨.op o args, (Encode.encodeOp o args).size⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Encode.encodeOp o args).size, fl⟩)
    (htest : fl.test cond = some taken) :
    ByteEval.run image fetchBase (if taken then 2 else 3) s =
      .ok ⟨core, UInt64.ofNat (fileBase + (origin + blockOffset p (if taken then yes else no).toNat)), fl⟩ := by
  have hm := hv.term b blk hb
  rw [hterm] at hm
  simp only [Shell.terminatorMatches, Bool.and_eq_true] at hm
  obtain ⟨⟨hprod, hyes⟩, hno⟩ := hm
  have hd := decodes_some hprod
  obtain ⟨-, hdy, hry⟩ := targets_lands hyes
  obtain ⟨-, hdn, hrn⟩ := targets_lands hno
  have hlt := decodeAt_lt hdn
  have hlt' := decodeAt_lt hd
  have hrip₁ := addr_add hrip (Encode.encodeOp o args).size
  have hrip₂ := addr_add hrip₁ 6
  have h1 : ByteEval.step image fetchBase s = .ok ⟨core, UInt64.ofNat (fileBase +
      (origin + blockOffset p b + instrOffset blk blk.instructions.size + (Encode.encodeOp o args).size)), fl⟩ := by
    unfold ByteEval.step
    rw [hrip, fetch_index (by omega), hd]
    dsimp only
    rw [hex, hrip₁]
  have h2 : ByteEval.step image fetchBase ⟨core, UInt64.ofNat (fileBase +
      (origin + blockOffset p b + instrOffset blk blk.instructions.size + (Encode.encodeOp o args).size)), fl⟩ =
      .ok ⟨core, if taken then UInt64.ofNat (fileBase + (origin + blockOffset p yes.toNat))
        else UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk blk.instructions.size +
          (Encode.encodeOp o args).size + 6)), fl⟩ := by
    unfold ByteEval.step
    rw [fetch_index (by omega), hdy]
    dsimp only
    rw [Encode.execute_branch]
    simp only [htest]
    cases taken with
    | true => simp only [↓reduceIte]; rw [hry _ rfl]
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [addr_add rfl 6]
  cases taken with
  | true =>
    show ByteEval.run image fetchBase 2 s = _
    rw [run_succ h1, run_succ h2]
    rfl
  | false =>
    have h3 : ByteEval.step image fetchBase ⟨core, UInt64.ofNat (fileBase +
        (origin + blockOffset p b + instrOffset blk blk.instructions.size + (Encode.encodeOp o args).size + 6)), fl⟩ =
        .ok ⟨core, UInt64.ofNat (fileBase + (origin + blockOffset p no.toNat)), fl⟩ := by
      unfold ByteEval.step
      rw [fetch_index (by omega), hdn]
      dsimp only
      rw [Encode.execute_jump, hrn _ rfl]
    show ByteEval.run image fetchBase 3 s = _
    rw [run_succ h1, run_succ h2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [run_succ h3]
    rfl

/-- **A jump terminator** reaches its block. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_jump (hv : Shell.Valid p image origin ex)
    (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {t : BlockId} (hterm : blk.terminator = .jump t)
    {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk blk.instructions.size))) :
    ByteEval.step image fetchBase s = .ok { s with rip := UInt64.ofNat (fileBase + (origin + blockOffset p t.toNat)) } := by
  have hm := hv.term b blk hb
  rw [hterm] at hm
  simp only [Shell.terminatorMatches] at hm
  obtain ⟨-, hd, hr⟩ := targets_lands hm
  have hlt := decodeAt_lt hd
  unfold ByteEval.step
  rw [hrip, fetch_index (by omega), hd]
  dsimp only
  rw [Encode.execute_jump, hr _ hrip]

/-- **A `ret` terminator** pops its return address. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_ret (hv : Shell.Valid p image origin ex)
    (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) (hterm : blk.terminator = .ret)
    {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk blk.instructions.size))) :
    ByteEval.step image fetchBase s =
      match s.core.memory.read64? (s.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { s with core := s.core.setReg .rsp (s.core.readReg .rsp + 8), rip := target } := by
  have hm := hv.term b blk hb
  rw [hterm] at hm
  simp only [Shell.terminatorMatches] at hm
  have hd := decodes_some hm
  have hlt := decodeAt_lt hd
  unfold ByteEval.step
  rw [hrip, fetch_index (by omega), hd]
  dsimp only
  rw [Encode.execute_ret]
  try rfl

/-- **An internal call** pushes the next instruction's address and enters its block. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.step_call (hv : Shell.Valid p image origin ex)
    (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat} {t : BlockId}
    (hi : blk.instructions[j]? = some (.instr (.call t))) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j))) :
    ByteEval.step image fetchBase s =
      match s.core.memory.write64? (s.core.readReg .rsp - 8)
          (UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk (j + 1)))) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { s.core.setReg .rsp (s.core.readReg .rsp - 8) with memory }
          rip := UInt64.ofNat (fileBase + (origin + blockOffset p t.toNat)), flags := s.flags } := by
  have hm := hv.instr b blk hb j _ hi
  simp only [Shell.instrMatches] at hm
  obtain ⟨-, hd, hr⟩ := targets_lands hm
  have hlt := decodeAt_lt hd
  have hnext : s.rip + UInt64.ofNat 5 =
      UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk (j + 1))) := by
    rw [hrip]; exact next_addr (i := .instr (.call t)) hi
  unfold ByteEval.step
  rw [hrip, fetch_index (by omega), hd]
  dsimp only
  rw [Encode.execute_call, hr _ hrip, hnext]
  try rfl

/-- **An export call** is a `call rel32` landing on the export's file offset. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.callsTo (hv : Shell.Valid p image origin ex)
    (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat} {name : String}
    (hi : blk.instructions[j]? = some (.callExport name)) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j))) :
    ∃ t, ex name = some t ∧ CallsTo image s (UInt64.ofNat (fileBase + t)) := by
  have hm := hv.instr b blk hb j _ hi
  simp only [Shell.instrMatches] at hm
  split at hm
  · rename_i t ht
    simp only [Bool.and_eq_true] at hm
    obtain ⟨hfits, hdec⟩ := hm
    have hd := decodes_some hdec
    have hlt := decodeAt_lt hd
    refine ⟨t, ht, Stream.displacement (origin + blockOffset p b + instrOffset blk j + 5) t, ?_, ?_⟩
    · rw [hrip, fetch_index (by omega), hd]
    · have hr := Encode.relative_resolves_base (UInt64.ofNat fileBase)
        (origin + blockOffset p b + instrOffset blk j + 5) t (by push_cast; exact hfits)
      rw [← UInt64.ofNat_add, ← UInt64.ofNat_add] at hr
      show ByteEval.relative (s.rip + UInt64.ofNat 5) _ = _
      rw [addr_add hrip 5]
      exact hr
  · cases hm

/-- **A `syscall`**: the decoder decodes nothing there and the bytes are `0F 05`. -/
theorem _root_.IxCC.X86.Exe.Shell.Valid.syscall_at (hv : Shell.Valid p image origin ex) (hfit : fileBase + image.size < 2 ^ 64)
    {b : Nat} {blk : Shell.Block} (hb : p.blocks[b]? = some blk) {j : Nat}
    (hi : blk.instructions[j]? = some .syscall) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk j))) :
    Decode.decodeAt image (s.rip - fetchBase).toNat = none ∧ syscallAt image s.rip ∧
      s.rip + 2 = UInt64.ofNat (fileBase + (origin + blockOffset p b + instrOffset blk (j + 1))) := by
  have hm := hv.instr b blk hb j _ hi
  simp only [Shell.instrMatches, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨hnone, h0⟩, h1⟩ := hm
  have hlt : origin + blockOffset p b + instrOffset blk j < image.size := by
    rcases Nat.lt_or_ge (origin + blockOffset p b + instrOffset blk j) image.size with hc | hc
    · exact hc
    · rw [getElem?_neg image _ (by omega)] at h0
      cases h0
  have hidx := fetch_index (pos := origin + blockOffset p b + instrOffset blk j) (by omega)
  refine ⟨by rw [hrip, hidx]; exact hnone, ⟨by rw [hrip, hidx]; exact h0, by rw [hrip, hidx]; exact h1⟩, ?_⟩
  rw [hrip]
  exact next_addr (i := .syscall) hi

end

/-! ## Traces counted in steps -/

/-- A run of the process in exactly `n` steps. -/
inductive RunN (image : ByteArray) : Nat → ByteEval.State → List Sys → ByteEval.State → Prop
  | refl (s : ByteEval.State) : RunN image 0 s [] s
  | step {n : Nat} {s s₁ s' : ByteEval.State} {e : Option Sys} {σ : List Sys}
      (h : Step image s e (some s₁)) (r : RunN image n s₁ σ s') : RunN image (n + 1) s (e.toList ++ σ) s'

theorem Run.toN {image : ByteArray} {s s' : ByteEval.State} {σ : List Sys} (h : Run image s σ s') :
    ∃ n, RunN image n s σ s' := by
  induction h with
  | refl s => exact ⟨0, .refl s⟩
  | step h _ ih => obtain ⟨n, r⟩ := ih; exact ⟨n + 1, .step h r⟩

theorem RunN.toRun {image : ByteArray} {n : Nat} {s s' : ByteEval.State} {σ : List Sys} (h : RunN image n s σ s') :
    Run image s σ s' := by
  induction h with
  | refl s => exact .refl s
  | step h _ ih => exact .step h ih

/-- A trace whose run takes at most `n` steps (the step that ends the process not counted). -/
def TraceN (image : ByteArray) (n : Nat) (s : ByteEval.State) (σ : List Sys) : Prop :=
  (∃ m s', m ≤ n ∧ RunN image m s σ s') ∨
  ∃ m σ₀ s' ev, m ≤ n ∧ σ = σ₀ ++ [ev] ∧ RunN image m s σ₀ s' ∧ Step image s' (some ev) none

theorem Trace.toN {image : ByteArray} {s : ByteEval.State} {σ : List Sys} (h : Trace image s σ) :
    ∃ n, TraceN image n s σ := by
  rcases h with ⟨s', hr⟩ | ⟨σ₀, s', ev, rfl, hr, hs⟩
  · obtain ⟨n, r⟩ := hr.toN; exact ⟨n, .inl ⟨n, s', Nat.le_refl _, r⟩⟩
  · obtain ⟨n, r⟩ := hr.toN; exact ⟨n, .inr ⟨n, σ₀, s', ev, Nat.le_refl _, rfl, r, hs⟩⟩

theorem TraceN.toTrace {image : ByteArray} {n : Nat} {s : ByteEval.State} {σ : List Sys} (h : TraceN image n s σ) :
    Trace image s σ := by
  rcases h with ⟨m, s', -, r⟩ | ⟨m, σ₀, s', ev, -, rfl, r, hs⟩
  · exact .inl ⟨s', r.toRun⟩
  · exact .inr ⟨σ₀, s', ev, rfl, r.toRun, hs⟩

theorem TraceN.mono {image : ByteArray} {n n' : Nat} {s : ByteEval.State} {σ : List Sys} (h : TraceN image n s σ)
    (hle : n ≤ n') : TraceN image n' s σ := by
  rcases h with ⟨m, s', hm, r⟩ | ⟨m, σ₀, s', ev, hm, rfl, r, hs⟩
  · exact .inl ⟨m, s', by omega, r⟩
  · exact .inr ⟨m, σ₀, s', ev, by omega, rfl, r, hs⟩

/-- A run of the process against a run of `m` byte-machine steps from the same state: it stops
inside it (no system call, at a state the byte machine steps from), or passes its end. -/
private theorem RunN.byte_split {image : ByteArray} {k : Nat} {s t : ByteEval.State} {σ : List Sys}
    (r : RunN image k s σ t) : ∀ {m : Nat} {s' : ByteEval.State}, ByteEval.run image fetchBase m s = .ok s' →
      (k < m ∧ σ = [] ∧ ∃ u, ByteEval.step image fetchBase t = .ok u) ∨ (m ≤ k ∧ RunN image (k - m) s' σ t) := by
  induction r with
  | refl s =>
    intro m s' h
    cases m with
    | zero => cases h; exact .inr ⟨Nat.le_refl _, .refl s⟩
    | succ m =>
      obtain ⟨s₁, h₁, -⟩ := ByteAgree.bind_ok h
      exact .inl ⟨by omega, rfl, s₁, h₁⟩
  | step hs r ih =>
    intro m s' h
    cases m with
    | zero => cases h; exact .inr ⟨Nat.zero_le _, .step hs r⟩
    | succ m =>
      obtain ⟨s₁, h₁, h⟩ := ByteAgree.bind_ok h
      obtain ⟨rfl, u, hu, hsu⟩ := Step.of_decodes (decodes_of_step_ok h₁) (defined_of_step_ok h₁) hs
      rw [h₁] at hu
      cases hu
      cases hsu
      rcases ih h with ⟨hk, rfl, hstep⟩ | ⟨hk, r'⟩
      · exact .inl ⟨by omega, rfl, hstep⟩
      · refine .inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_add_right]
        exact r'

/-- **A trace from the start of a run of `m` byte-machine steps** is empty, or a trace from its
end whose run is `m` steps shorter. -/
theorem TraceN.through {image : ByteArray} {n m : Nat} {s s' : ByteEval.State} {σ : List Sys}
    (h : ByteEval.run image fetchBase m s = .ok s') (ht : TraceN image n s σ) :
    σ = [] ∨ (m ≤ n ∧ TraceN image (n - m) s' σ) := by
  rcases ht with ⟨k, t, hk, r⟩ | ⟨k, σ₀, t, ev, hk, rfl, r, hs⟩
  · rcases r.byte_split h with ⟨-, rfl, -⟩ | ⟨hmk, r'⟩
    · exact .inl rfl
    · exact .inr ⟨by omega, .inl ⟨k - m, t, by omega, r'⟩⟩
  · rcases r.byte_split h with ⟨-, rfl, u, hu⟩ | ⟨hmk, r'⟩
    · exact absurd (Step.of_decodes (decodes_of_step_ok hu) (defined_of_step_ok hu) hs).1 (by simp)
    · exact .inr ⟨by omega, .inr ⟨k - m, σ₀, t, ev, by omega, rfl, r', hs⟩⟩

/-- A trace from a state the byte machine faults from is empty. -/
theorem TraceN.nil_of_faults {image : ByteArray} {n n' : Nat} {s : ByteEval.State} {σ : List Sys}
    (h : FaultsWithin image s n') (ht : TraceN image n s σ) : σ = [] :=
  Trace.nil_of_faults h ht.toTrace

/-- **A trace from a `syscall`** (nothing decodes and the bytes are `0F 05`) is empty, or the
platform's event for it followed by a trace from the state after it (none if the call ended the
process). -/
theorem TraceN.sys {image : ByteArray} {n : Nat} {s : ByteEval.State} {σ : List Sys}
    (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
    (ht : TraceN image n s σ) :
    σ = [] ∨ ∃ ev after σ', Syscall s ev after ∧ σ = ev :: σ' ∧
      ((∃ s', after = some s' ∧ 1 ≤ n ∧ TraceN image (n - 1) s' σ') ∨ (after = none ∧ σ' = [])) := by
  have hstep : ∀ {e : Option Sys} {t : Option ByteEval.State}, Step image s e t →
      ∃ ev, e = some ev ∧ Syscall s ev t := by
    intro e t h
    cases h with
    | byte h => exact absurd hd (decodes_of_step_ok h)
    | sys _ _ h => exact ⟨_, rfl, h⟩
    | unknown hu =>
      rcases hu with ⟨-, hnb⟩ | ⟨c, hc⟩
      · exact absurd hb hnb
      · exact absurd hd (decodes_of_undefined hc)
  rcases ht with ⟨k, t, hk, r⟩ | ⟨k, σ₀, t, ev, hk, rfl, r, hs⟩
  · cases r with
    | refl => exact .inl rfl
    | @step k' _ s₁ _ e σ' h r =>
      obtain ⟨ev, rfl, hsys⟩ := hstep h
      exact .inr ⟨ev, some s₁, σ', hsys, rfl, .inl ⟨s₁, rfl, by omega, .inl ⟨k', t, by omega, r⟩⟩⟩
  · cases r with
    | refl =>
      obtain ⟨ev', hev, hsys⟩ := hstep hs
      cases hev
      exact .inr ⟨_, none, [], hsys, rfl, .inr ⟨rfl, rfl⟩⟩
    | @step k' _ s₁ _ e σ' h r =>
      obtain ⟨ev', rfl, hsys⟩ := hstep h
      exact .inr ⟨ev', some s₁, σ' ++ [ev], hsys, rfl,
        .inl ⟨s₁, rfl, by omega, .inr ⟨k', σ', t, ev, by omega, rfl, r, hs⟩⟩⟩

end IxCC.X86.Exe.Process
