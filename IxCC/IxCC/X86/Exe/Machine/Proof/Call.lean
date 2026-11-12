import IxCC.X86.Exe.Process
import IxCC.X86.ByteAgree
import IxCC.X86.DecodeWindow
import IxCC.X86.Memory

/-!
# A call into the object, on the process (X0-P, second part)

The per-call model (`ObjectEval.call`, under a `Driver`) runs the object's
text on a memory whose permissions are the driver's mapping. The process
(`Process.Step`) runs the same instructions fetched from the executable file,
on its own memory. `call_lifts` relates the two at one call site: where the
process is at a `call rel32` landing on the export (`CallsTo`) in the state
the driver gives the call, the process does what the model's outcome says
(`Lifts`): runs `k + 1` instructions for a timeout; returns within `k + 1`
instructions with the status in `rax` (and for a value, the value in `rdx`
and the model's bytes), `rsp` back, the callee-saved registers restored and
no byte outside the mapping changed (`Returned`); or, since nothing is
assumed of the process's permissions, faults on a memory access first.
`two_calls` composes two such calls, `cx_init` and the root from a site of
its own, as `X86.LinkedAt.call` does, given the instructions between them
(`hglue`, which the shell's blocks discharge).

**A memory fault ends the trace.** `Trace.nil_of_faults`: from a state the
byte machine reaches a memory fault from, the process makes no system call
(`Process.Step` has no step at a memory fault); `Trace.through`: a trace from
the start of a run of the byte machine stops inside it, with no system call,
or passes through its end. So a memory fault inside a call leaves the trace a
prefix of one the session model allows. Both rest on `Step.of_decodes`: where
the byte machine steps or faults on memory, `Process.Step`'s other two rules
(the `syscall` and `unknown`, where it promises nothing) do not apply. No
proof here uses the absence of a step anywhere but at a memory fault.

The two hypotheses a caller supplies beyond the call's state: `CallsTo`
(without it a `call` whose displacement does not fit in 32 signed bits lands
elsewhere: the check's `fitsSigned32` gives it), and `hfit`, the text inside
the 64-bit address space from the file's start (without it the process's
fetch offset `rip − fileBase` wraps around and need not be the text's;
the writer's placement, below the zero-filled segments, gives it).
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.Sem (Result Resource Obs)
open IxCC.X86.ByteAgree (OkOrF)

/-! ## The byte machine on the file, against the model's text -/

private theorem byteArray_getElem? (a : ByteArray) (k : Nat) : a[k]? = a.data.toList[k]? := by
  rw [Array.getElem?_toList]
  by_cases h : k < a.size
  · rw [getElem?_pos a k h, Array.getElem?_eq_getElem (show k < a.data.size from h),
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg a k h, Array.getElem?_eq_none (show a.data.size ≤ k from Nat.le_of_not_lt h)]

/-- The file from `off` is the text, then the rest of the file. -/
theorem drop_window {text image : ByteArray} {off : Nat} (hw : ∀ i < text.size, image[off + i]? = text[i]?) :
    image.data.toList.drop off = text.data.toList ++ image.data.toList.drop (off + text.size) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < text.size
  · rw [List.getElem?_append_left (show i < text.data.toList.length by rw [Array.length_toList]; exact hi),
      ← byteArray_getElem?, ← byteArray_getElem?, hw i hi]
  · have hle : text.data.size ≤ i := Nat.le_of_not_lt hi
    have hlen : text.data.toList.length ≤ i := by rw [Array.length_toList]; exact hle
    rw [List.getElem?_append_right hlen, List.getElem?_drop, Array.length_toList]
    congr 1
    show off + i = off + text.data.size + (i - text.data.size)
    omega

theorem decodeAt_lt {t : ByteArray} {j : Nat} {d : Decode.Decoded} (h : Decode.decodeAt t j = some d) :
    j < t.size := by
  refine Nat.lt_of_not_le fun hc => ?_
  unfold Decode.decodeAt at h
  simp [hc] at h

/-- Where the model's text decodes, the file decodes the same. -/
theorem step_window {text image : ByteArray} {off : Nat} (hw : ∀ i < text.size, image[off + i]? = text[i]?)
    (hfit : off + text.size ≤ 2 ^ 64) {base : Word} (hbase : base = UInt64.ofNat (fileBase + off))
    {st st' : ByteEval.State} (h : ByteEval.step text base st = .ok st') :
    ByteEval.step image fetchBase st = .ok st' := by
  unfold ByteEval.step at h ⊢
  cases hd : Decode.decodeAt text (st.rip - base).toNat with
  | none => rw [hd] at h; cases h
  | some d =>
    rw [hd] at h
    have hlt := decodeAt_lt hd
    have himg := Decode.decodeAt_window (drop_window hw) hd
    have hidx : (st.rip - fetchBase).toNat = off + (st.rip - base).toNat := by
      have he : st.rip - fetchBase = (st.rip - base) + UInt64.ofNat off := by
        rw [hbase, UInt64.ofNat_add]
        show st.rip - UInt64.ofNat fileBase = st.rip - (UInt64.ofNat fileBase + UInt64.ofNat off) + UInt64.ofNat off
        generalize st.rip = r
        generalize UInt64.ofNat off = o
        generalize UInt64.ofNat fileBase = b
        have h1 : r = (r - (b + o)) + (b + o) := (UInt64.sub_add_cancel _ _).symm
        calc r - b = ((r - (b + o)) + o) + b - b := by
              rw [UInt64.add_assoc, UInt64.add_comm o b, ← h1]
          _ = (r - (b + o)) + o := UInt64.add_sub_cancel _ _
      have hsz : UInt64.size = 2 ^ 64 := rfl
      have hoff : (UInt64.ofNat off).toNat = off := UInt64.toNat_ofNat_of_lt' (by omega)
      rw [he, UInt64.toNat_add, hoff, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hidx, himg]
    exact h

/-- The same for runs. -/
theorem run_window {text image : ByteArray} {off : Nat} (hw : ∀ i < text.size, image[off + i]? = text[i]?)
    (hfit : off + text.size ≤ 2 ^ 64) {base : Word} (hbase : base = UInt64.ofNat (fileBase + off)) :
    ∀ (m : Nat) {st st' : ByteEval.State}, ByteEval.run text base m st = .ok st' →
      ByteEval.run image fetchBase m st = .ok st'
  | 0, _, _, h => h
  | m + 1, st, st', h => by
    obtain ⟨s₁, h₁, h⟩ := ByteAgree.bind_ok h
    show (ByteEval.step image fetchBase st >>= fun next => ByteEval.run image fetchBase m next) = .ok st'
    rw [step_window hw hfit hbase h₁]
    exact run_window hw hfit hbase m h

/-! ## Runs, `runTo` and faults -/

/-- A run that fails failed at some step. -/
theorem run_error {t : ByteArray} {b : Word} {e : ByteEval.Fault} :
    ∀ (n : Nat) {s : ByteEval.State}, ByteEval.run t b n s = .error e →
      ∃ m < n, ∃ s', ByteEval.run t b m s = .ok s' ∧ ByteEval.step t b s' = .error e
  | 0, _, h => by cases h
  | n + 1, s, h => by
    change (ByteEval.step t b s >>= fun next => ByteEval.run t b n next) = .error e at h
    cases hs : ByteEval.step t b s with
    | error e' =>
      rw [hs] at h
      cases h
      exact ⟨0, by omega, s, rfl, hs⟩
    | ok s₁ =>
      rw [hs] at h
      obtain ⟨m, hm, s', hr, hst⟩ := run_error n h
      refine ⟨m + 1, by omega, s', ?_, hst⟩
      change (ByteEval.step t b s >>= fun next => ByteEval.run t b m next) = .ok s'
      rw [hs]
      exact hr

theorem run_succ {t : ByteArray} {b : Word} {s s₁ : ByteEval.State} (h : ByteEval.step t b s = .ok s₁) (n : Nat) :
    ByteEval.run t b (n + 1) s = ByteEval.run t b n s₁ := by
  change (ByteEval.step t b s >>= fun next => ByteEval.run t b n next) = _
  rw [h]
  rfl

/-- `runTo` is a run of at most its fuel, of exactly its fuel unless it stopped. -/
theorem runTo_run {t : ByteArray} {b stop : Word} :
    ∀ (k : Nat) {s s' : ByteEval.State}, ObjectEval.runTo t b stop k s = .ok s' →
      ∃ m ≤ k, ByteEval.run t b m s = .ok s' ∧ (s'.rip ≠ stop → m = k)
  | 0, s, s', h => by cases h; exact ⟨0, Nat.le_refl _, rfl, fun _ => rfl⟩
  | k + 1, s, s', h => by
    unfold ObjectEval.runTo at h
    by_cases hs : s.rip = stop
    · rw [ite_eq_left hs] at h
      cases h
      exact ⟨0, by omega, rfl, fun hne => absurd hs hne⟩
    · rw [ite_eq_right hs] at h
      cases hst : ByteEval.step t b s with
      | error f => rw [hst] at h; cases h
      | ok s₁ =>
        rw [hst] at h
        obtain ⟨m, hm, hr, hk⟩ := runTo_run k h
        exact ⟨m + 1, by omega, by rw [run_succ hst]; exact hr, fun hne => by rw [hk hne]⟩

/-! ## The call -/

/-- The process faults on a memory access within `n` steps from `s`. -/
def FaultsWithin (image : ByteArray) (s : ByteEval.State) (n : Nat) : Prop :=
  ∃ m < n, ∃ s' fault, ByteEval.run image fetchBase m s = .ok s' ∧
    ByteEval.step image fetchBase s' = .error (.memory fault)

/-- The process at a `call rel32` landing on `target`. -/
def CallsTo (image : ByteArray) (s : ByteEval.State) (target : Word) : Prop :=
  ∃ disp, Decode.decodeAt image (s.rip - fetchBase).toNat = some ⟨.call disp, 5⟩ ∧
    ByteEval.relative (s.rip + 5) disp = target

/-- The process back from a call made under `D` from the bytes `bytes`: at the
return address, `rsp` back, the status in `rax`, no byte outside `D`'s mapping
changed, and the callee-saved registers the caller's (`D.other`). -/
structure Returned (D : Driver) (bytes : Word → UInt8) (status : Word) (s : ByteEval.State) : Prop where
  rip : s.rip = D.ret
  rsp : s.core.readReg .rsp = D.sp + 8
  rax : s.core.readReg .rax = status
  frame : ∀ a, D.mapped a = false → s.core.memory.bytes a = bytes a
  saved : ∀ r ∈ SysV.calleeSaved, s.core.readReg r = D.other r

/-- What the process does at a call whose model outcome at clock `k` is `r`:
for a timeout, `k + 1` steps of the byte machine (so no system call); for a
value, a resource failure or a trap, it returns within `k + 1` steps with the
status (and, for a value, the value in `rdx` and the model's bytes); in each
case, or it faults on a memory access first; for stuck, nothing. -/
def Lifts (image : ByteArray) (D : Driver) (bytes : Word → UInt8) (s : ByteEval.State) (k : Nat) :
    Result (Word × Memory) → Prop
  | .timeout => (∃ s', ByteEval.run image fetchBase (k + 1) s = .ok s') ∨ FaultsWithin image s (k + 1)
  | .stuck => True
  | .ok (w, mem) => (∃ m s', m ≤ k + 1 ∧ ByteEval.run image fetchBase m s = .ok s' ∧ Returned D bytes 0 s' ∧
      s'.core.readReg .rdx = w ∧ s'.core.memory.bytes = mem.bytes) ∨ FaultsWithin image s (k + 1)
  | .resource f => (∃ m s', m ≤ k + 1 ∧ ByteEval.run image fetchBase m s = .ok s' ∧
      Returned D bytes (ObjectEval.Resource.code f) s') ∨ FaultsWithin image s (k + 1)
  | .trap => (∃ m s', m ≤ k + 1 ∧ ByteEval.run image fetchBase m s = .ok s' ∧ Returned D bytes 4 s') ∨
      FaultsWithin image s (k + 1)

theorem Lifts.of_faults {image : ByteArray} {D : Driver} {bytes : Word → UInt8} {s : ByteEval.State} {k : Nat}
    (h : FaultsWithin image s (k + 1)) : ∀ r, Lifts image D bytes s k r
  | .timeout => .inr h
  | .stuck => trivial
  | .ok _ => .inr h
  | .resource _ => .inr h
  | .trap => .inr h

/-- The callee-saved registers a call's entry gives are the caller's own. -/
theorem regs_calleeSaved (D : Driver) (args : List Word) {r : GPR} (hr : r ∈ SysV.calleeSaved) :
    D.regs args r = D.other r := by
  simp [SysV.calleeSaved] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- What a return the model accepts restores. -/
theorem restored_saved {D : Driver} {args : List Word} {bytes : Word → UInt8} {st : ByteEval.State}
    (h : ObjectEval.restored (D.core args bytes) st = true) :
    st.core.readReg .rsp = D.sp + 8 ∧ ∀ r ∈ SysV.calleeSaved, st.core.readReg r = D.other r := by
  unfold ObjectEval.restored at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun r hr => ?_⟩
  have hr' := Array.all_eq_true_iff_forall_mem.1 h.2 r hr
  simp only [beq_iff_eq] at hr'
  rw [hr']
  exact regs_calleeSaved D args hr

/-! ## The driver's call memory -/

theorem sp_addr {D : Driver} {n : Nat} (hD : D.Ok n) {i : Nat} (hi : i < 8) :
    (D.sp + UInt64.ofNat i).toNat = D.sp.toNat + i := by
  have := hD.spTop
  have hsz : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega), Nat.mod_eq_of_lt (by omega)]

theorem slot_mapped {D : Driver} {n : Nat} (hD : D.Ok n) {i : Nat} (hi : i < 8) :
    D.mapped (D.sp + UInt64.ofNat i) = true := by
  have := hD.spTop
  simp only [Driver.mapped, Driver.inStack, Driver.inRegion, sp_addr hD hi, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  right
  omega

theorem mem_writable (D : Driver) (bytes : Word → UInt8) : (D.mem bytes).writable = D.mapped :=
  (ByteAgree.writeLittle_perms (⟨bytes, D.mapped, D.mapped⟩ : Memory) D.sp D.ret 8).2

theorem mem_readable (D : Driver) (bytes : Word → UInt8) : (D.mem bytes).readable = D.mapped :=
  (ByteAgree.writeLittle_perms (⟨bytes, D.mapped, D.mapped⟩ : Memory) D.sp D.ret 8).1

/-- The return address is in the word at `sp`. -/
theorem mem_slot {D : Driver} {n : Nat} (hD : D.Ok n) (bytes : Word → UInt8) :
    (D.mem bytes).read64? D.sp = .ok D.ret := by
  have hr : Memory.rangeAllowed (D.mem bytes).readable D.sp Width.w64.bytes = true := by
    apply Memory.rangeAllowed_of_forall
    intro i hi
    rw [mem_readable]
    exact slot_mapped hD (show i < 8 from hi)
  unfold Memory.read64? Memory.read?
  rw [ite_eq_left hr]
  show Except.ok ((Memory.write64 ⟨bytes, D.mapped, D.mapped⟩ D.sp D.ret).read64 D.sp) = _
  rw [Memory.read64_write64]

/-- A call's bytes outside the mapping are the given ones. -/
theorem mem_unmapped {D : Driver} {n : Nat} (hD : D.Ok n) (bytes : Word → UInt8) {a : Word}
    (ha : D.mapped a = false) : (D.mem bytes).bytes a = bytes a := by
  show (Memory.write64 ⟨bytes, D.mapped, D.mapped⟩ D.sp D.ret).bytes a = bytes a
  rw [Memory.write64_bytes_outside]
  intro i hi heq
  rw [heq, slot_mapped hD hi] at ha
  cases ha

/-- The process's step at a call that lands on `target`. -/
theorem call_step {image : ByteArray} {s : ByteEval.State} {target : Word} (hc : CallsTo image s target) :
    ByteEval.step image fetchBase s =
      match s.core.memory.write64? (s.core.readReg .rsp - 8) (s.rip + 5) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { s.core.setReg .rsp (s.core.readReg .rsp - 8) with memory }
          rip := target
          flags := s.flags } := by
  obtain ⟨disp, hd, hl⟩ := hc
  simp only [ByteEval.step, hd]
  rw [Encode.execute_call]
  simp only [show (UInt64.ofNat 5 : Word) = 5 from rfl, hl]
  rfl

/-! ## The call lemma -/

/-- **A call into the object, on the process.** The process at a `call rel32`
landing on the export `name` of `object` (whose text the file holds at
`textOffset`), in the state the driver `D` gives a call on `args` from the bytes
`bytes` but for `rsp` one word higher (the `call` pushes the return address),
with its own permissions: for the model's outcome at clock `k`, the process
does what `Lifts` says (`k + 1` steps for a timeout; a return with the status,
and for a value the value and the model's bytes, within `k + 1` steps; or a
memory fault first; nothing for stuck). -/
theorem call_lifts {object image text : ByteArray} {textOffset : Nat}
    (htext : ELFRead.text? object = some text) (hw : ∀ i < text.size, image[textOffset + i]? = text[i]?)
    (hfit : textOffset + text.size ≤ 2 ^ 64)
    {name : String} {offset : Nat} (hsym : ELF.symbol? object name = some offset)
    {D : Driver} {n : Nat} (hD : D.Ok n) (hbase : D.base = UInt64.ofNat (fileBase + textOffset))
    {args : List Word} {bytes : Word → UInt8} {s : ByteEval.State}
    (hcall : CallsTo image s (D.base + UInt64.ofNat offset)) (hret : D.ret = s.rip + 5)
    (hregs : ∀ r, r ≠ .rsp → s.core.readReg r = (D.core args bytes).readReg r)
    (hrsp : s.core.readReg .rsp = D.sp + 8) (hbytes : s.core.memory.bytes = bytes)
    (hflags : s.flags = D.flags) (k : Nat) :
    Lifts image D bytes s k (ObjectEval.call object name D.base (D.core args bytes) D.flags k) := by
  have hmodel : ObjectEval.call object name D.base (D.core args bytes) D.flags k =
      match ObjectEval.runTo text D.base D.ret k ⟨D.core args bytes, D.base + UInt64.ofNat offset, D.flags⟩ with
      | .ok state => ObjectEval.finish (D.core args bytes) D.ret state
      | .error _ => .stuck := by
    have hslot : (D.core args bytes).memory.read64? ((D.core args bytes).readReg .rsp) = .ok D.ret :=
      mem_slot hD bytes
    unfold ObjectEval.call
    rw [htext, hsym, hslot]
    rfl
  rw [hmodel]
  have hstep := call_step hcall
  obtain ⟨⟨regs, ⟨b, R, W⟩⟩, rip, fl⟩ := s
  simp only at hbytes hflags hrsp hret hstep
  subst hbytes hflags
  have hrsp8 : regs .rsp - 8 = D.sp := by
    change Core.readReg ⟨regs, ⟨b, R, W⟩⟩ .rsp - 8 = D.sp
    rw [hrsp]
    exact UInt64.add_sub_cancel _ _
  simp only [Core.readReg] at hstep hrsp8
  rw [hrsp8, ← hret] at hstep
  cases hwr : (⟨b, R, W⟩ : Memory).write64? D.sp D.ret with
  | error fault =>
    rw [hwr] at hstep
    exact Lifts.of_faults ⟨0, by omega, _, fault, rfl, hstep⟩ _
  | ok m₁ =>
    rw [hwr] at hstep
    simp only at hstep
    have hm₁ : m₁ = (D.mem b).withPerms R W := by
      unfold Memory.write64? Memory.write? at hwr
      split at hwr
      · cases hwr
        exact ByteAgree.writeLittle_withPerms (R := R) (W := W) (⟨b, D.mapped, D.mapped⟩ : Memory) D.sp D.ret 8
      · cases hwr
    have hregs' : Registers.set regs .rsp D.sp = D.regs args := by
      funext r
      by_cases hr : r = .rsp
      · subst hr
        simp [Registers.set, Driver.regs]
      · simp only [Registers.set, beq_iff_eq, hr, ite_false]
        exact hregs r hr
    have hp₁ : ({
          core := { (⟨regs, ⟨b, R, W⟩⟩ : Core).setReg .rsp D.sp with memory := m₁ }
          rip := D.base + UInt64.ofNat offset
          flags := D.flags } : ByteEval.State) =
        (⟨D.core args b, D.base + UInt64.ofNat offset, D.flags⟩ : ByteEval.State).withPerms R W := by
      simp only [ByteEval.State.withPerms, Core.withPerms, Core.setReg, Driver.core, hregs', hm₁]
    replace hstep := hstep.trans (congrArg (Except.ok (ε := ByteEval.Fault)) hp₁)
    cases hrun : ObjectEval.runTo text D.base D.ret k ⟨D.core args b, D.base + UInt64.ofNat offset, D.flags⟩ with
    | error _ => trivial
    | ok st =>
      simp only
      obtain ⟨j, hjk, hj, hjeq⟩ := runTo_run k hrun
      have hproc := ByteAgree.run_agree (R := R) (W := W) j (run_window hw hfit hbase j hj)
      have hfr := ByteAgree.run_frame j hj
      rcases ByteAgree.OkOrF.cases hproc with hok | ⟨f, herr⟩
      · have hrun' : ByteEval.run image fetchBase (j + 1) ⟨⟨regs, ⟨b, R, W⟩⟩, rip, D.flags⟩ =
            .ok (st.withPerms R W) := by
          rw [run_succ hstep]
          exact hok
        have hframe : ∀ a, D.mapped a = false → (st.withPerms R W).core.memory.bytes a = b a := by
          intro a ha
          show st.core.memory.bytes a = b a
          rw [hfr.bytes a (by show (D.mem b).writable a = false; rw [mem_writable]; exact ha)]
          exact mem_unmapped hD b ha
        unfold ObjectEval.finish
        by_cases hr : st.rip = D.ret
        · rw [ite_eq_left hr]
          by_cases hres : ObjectEval.restored (D.core args b) st = true
          · rw [ite_eq_left hres]
            have hsp : (st.withPerms R W).core.readReg .rsp = D.sp + 8 := (restored_saved hres).1
            have hsaved : ∀ r ∈ SysV.calleeSaved, (st.withPerms R W).core.readReg r = D.other r :=
              (restored_saved hres).2
            have hret' : (st.withPerms R W).rip = D.ret := hr
            unfold ObjectEval.statusResult
            by_cases h0 : st.core.readReg .rax = 0
            · rw [ite_eq_left h0]
              exact .inl ⟨j + 1, st.withPerms R W, by omega, hrun', ⟨hret', hsp, h0, hframe, hsaved⟩, rfl, rfl⟩
            rw [ite_eq_right h0]
            by_cases h1 : st.core.readReg .rax = 1
            · rw [ite_eq_left h1]
              exact .inl ⟨j + 1, st.withPerms R W, by omega, hrun', ⟨hret', hsp, h1, hframe, hsaved⟩⟩
            rw [ite_eq_right h1]
            by_cases h2 : st.core.readReg .rax = 2
            · rw [ite_eq_left h2]
              exact .inl ⟨j + 1, st.withPerms R W, by omega, hrun', ⟨hret', hsp, h2, hframe, hsaved⟩⟩
            rw [ite_eq_right h2]
            by_cases h3 : st.core.readReg .rax = 3
            · rw [ite_eq_left h3]
              exact .inl ⟨j + 1, st.withPerms R W, by omega, hrun', ⟨hret', hsp, h3, hframe, hsaved⟩⟩
            rw [ite_eq_right h3]
            by_cases h4 : st.core.readReg .rax = 4
            · rw [ite_eq_left h4]
              exact .inl ⟨j + 1, st.withPerms R W, by omega, hrun', ⟨hret', hsp, h4, hframe, hsaved⟩⟩
            rw [ite_eq_right h4]
            trivial
          · rw [ite_eq_right hres]
            trivial
        · rw [ite_eq_right hr]
          exact .inl ⟨_, hjeq hr ▸ hrun'⟩
      · obtain ⟨m, hm, s'', hr'', hst''⟩ := run_error j herr
        refine Lifts.of_faults ⟨m + 1, by omega, s'', f, ?_, hst''⟩ _
        rw [run_succ hstep]
        exact hr''


/-- The process at a call of the export `name` of `object`, in the state the
driver `D` gives a call on `args` from the bytes `bytes` (`call_lifts`'
hypotheses at one call site). -/
structure AtCall (image object : ByteArray) (name : String) (D : Driver) (args : List Word)
    (bytes : Word → UInt8) (s : ByteEval.State) : Prop where
  lands : ∃ offset, ELF.symbol? object name = some offset ∧ CallsTo image s (D.base + UInt64.ofNat offset)
  ret : D.ret = s.rip + 5
  regs : ∀ r, r ≠ .rsp → s.core.readReg r = (D.core args bytes).readReg r
  rsp : s.core.readReg .rsp = D.sp + 8
  bytes : s.core.memory.bytes = bytes
  flags : s.flags = D.flags

/-- `call_lifts` at a call site. -/
theorem AtCall.lifts {object image text : ByteArray} {textOffset : Nat}
    (htext : ELFRead.text? object = some text) (hw : ∀ i < text.size, image[textOffset + i]? = text[i]?)
    (hfit : textOffset + text.size ≤ 2 ^ 64) {name : String} {D : Driver} {n : Nat} (hD : D.Ok n)
    (hbase : D.base = UInt64.ofNat (fileBase + textOffset)) {args : List Word} {bytes : Word → UInt8}
    {s : ByteEval.State} (h : AtCall image object name D args bytes s) (k : Nat) :
    Lifts image D bytes s k (ObjectEval.call object name D.base (D.core args bytes) D.flags k) := by
  obtain ⟨offset, hsym, hcall⟩ := h.lands
  exact call_lifts htext hw hfit hsym hD hbase hcall h.ret h.regs h.rsp h.bytes h.flags k

/-! ## Runs of the byte machine, composed -/

theorem run_add {t : ByteArray} {b : Word} :
    ∀ (m n : Nat) (s : ByteEval.State),
      ByteEval.run t b (m + n) s = (ByteEval.run t b m s >>= fun s' => ByteEval.run t b n s')
  | 0, n, s => by rw [Nat.zero_add]; rfl
  | m + 1, n, s => by
    rw [Nat.add_right_comm]
    change (ByteEval.step t b s >>= fun next => ByteEval.run t b (m + n) next) =
      ((ByteEval.step t b s >>= fun next => ByteEval.run t b m next) >>= fun s' => ByteEval.run t b n s')
    cases ByteEval.step t b s with
    | error e => rfl
    | ok s₁ => exact run_add m n s₁

theorem run_comp {t : ByteArray} {b : Word} {m n : Nat} {s s₁ s₂ : ByteEval.State}
    (h₁ : ByteEval.run t b m s = .ok s₁) (h₂ : ByteEval.run t b n s₁ = .ok s₂) :
    ByteEval.run t b (m + n) s = .ok s₂ := by
  rw [run_add, h₁]
  exact h₂

theorem run_prefix {t : ByteArray} {b : Word} {m n : Nat} {s s₂ : ByteEval.State}
    (h : ByteEval.run t b (m + n) s = .ok s₂) : ∃ s₁, ByteEval.run t b m s = .ok s₁ := by
  rw [run_add] at h
  cases hm : ByteEval.run t b m s with
  | error e => rw [hm] at h; cases h
  | ok s₁ => exact ⟨s₁, rfl⟩

theorem FaultsWithin.mono {image : ByteArray} {s : ByteEval.State} {n n' : Nat} (h : FaultsWithin image s n)
    (hle : n ≤ n') : FaultsWithin image s n' := by
  obtain ⟨m, hm, s', f, hr, hs⟩ := h
  exact ⟨m, by omega, s', f, hr, hs⟩

theorem FaultsWithin.shift {image : ByteArray} {s s₁ : ByteEval.State} {m n : Nat}
    (hr : ByteEval.run image fetchBase m s = .ok s₁) (h : FaultsWithin image s₁ n) :
    FaultsWithin image s (m + n) := by
  obtain ⟨j, hj, s', f, hr', hs⟩ := h
  exact ⟨m + j, by omega, s', f, run_comp hr hr', hs⟩

/-! ## A fault ends the trace -/

theorem decodes_of_step_ok {image : ByteArray} {b : Word} {s u : ByteEval.State}
    (h : ByteEval.step image b s = .ok u) : Decode.decodeAt image (s.rip - b).toNat ≠ none := by
  intro hd
  unfold ByteEval.step at h
  rw [hd] at h
  cases h

theorem decodes_of_fault {image : ByteArray} {b : Word} {s : ByteEval.State} {f : MemoryFault}
    (h : ByteEval.step image b s = .error (.memory f)) : Decode.decodeAt image (s.rip - b).toNat ≠ none := by
  intro hd
  unfold ByteEval.step at h
  rw [hd] at h
  cases h

theorem decodes_of_undefined {image : ByteArray} {b : Word} {s : ByteEval.State} {c : Condition}
    (h : ByteEval.step image b s = .error (.undefinedCondition c)) :
    Decode.decodeAt image (s.rip - b).toNat ≠ none := by
  intro hd
  unfold ByteEval.step at h
  rw [hd] at h
  cases h

/-- Where the byte machine steps, it does not stop on an undefined condition. -/
theorem defined_of_step_ok {image : ByteArray} {b : Word} {s u : ByteEval.State}
    (h : ByteEval.step image b s = .ok u) : ∀ c, ByteEval.step image b s ≠ .error (.undefinedCondition c) :=
  fun _ hc => by rw [h] at hc; cases hc

/-- Where the byte machine faults on memory, it does not stop on an undefined condition. -/
theorem defined_of_fault {image : ByteArray} {b : Word} {s : ByteEval.State} {f : MemoryFault}
    (h : ByteEval.step image b s = .error (.memory f)) :
    ∀ c, ByteEval.step image b s ≠ .error (.undefinedCondition c) :=
  fun _ hc => by rw [h] at hc; cases hc

/-- Where the byte decoder decodes and the byte machine does not stop on an
undefined condition, the process's only step is the byte machine's (neither
the `syscall` rule nor `Process.Step`'s `unknown` applies; at a memory fault or
a divide error there is none). -/
theorem Step.of_decodes {image : ByteArray} {s : ByteEval.State} {e : Option Sys} {t : Option ByteEval.State}
    (hd : Decode.decodeAt image (s.rip - fetchBase).toNat ≠ none)
    (hc : ∀ c, ByteEval.step image fetchBase s ≠ .error (.undefinedCondition c)) (h : Step image s e t) :
    e = none ∧ ∃ u, ByteEval.step image fetchBase s = .ok u ∧ t = some u := by
  cases h with
  | byte h => exact ⟨rfl, _, h, rfl⟩
  | sys hd' _ _ => exact absurd hd' hd
  | unknown hu =>
    rcases hu with ⟨hd', -⟩ | ⟨c, hc'⟩
    · exact absurd hd' hd
    · exact absurd hc' (hc c)

/-- **A run of the process from the start of a run of the byte machine** stops
inside it, with no system call and at a state the byte machine steps from, or
passes through its end. -/
theorem Run.through {image : ByteArray} :
    ∀ (n : Nat) {s s' t : ByteEval.State} {σ : List Sys}, ByteEval.run image fetchBase n s = .ok s' →
      Run image s σ t → (σ = [] ∧ ∃ u, ByteEval.step image fetchBase t = .ok u) ∨ Run image s' σ t
  | 0, s, s', t, σ, h, hr => by cases h; exact .inr hr
  | n + 1, s, s', t, σ, h, hr => by
    obtain ⟨s₁, h₁, h⟩ := ByteAgree.bind_ok h
    cases hr with
    | refl => exact .inl ⟨rfl, s₁, h₁⟩
    | step hs r =>
      obtain ⟨rfl, u, hu, hsu⟩ := Step.of_decodes (decodes_of_step_ok h₁) (defined_of_step_ok h₁) hs
      rw [h₁] at hu
      cases hu
      cases hsu
      exact Run.through n h r

/-- **The same for traces**: a trace from the start of a run of the byte
machine is empty or a trace from its end. -/
theorem Trace.through {image : ByteArray} {n : Nat} {s s' : ByteEval.State} {σ : List Sys}
    (h : ByteEval.run image fetchBase n s = .ok s') (ht : Trace image s σ) : σ = [] ∨ Trace image s' σ := by
  rcases ht with ⟨t, hr⟩ | ⟨σ₀, t, ev, rfl, hr, hs⟩
  · rcases Run.through n h hr with ⟨rfl, -⟩ | hr'
    · exact .inl rfl
    · exact .inr (.inl ⟨t, hr'⟩)
  · rcases Run.through n h hr with ⟨rfl, u, hu⟩ | hr'
    · exact absurd (Step.of_decodes (decodes_of_step_ok hu) (defined_of_step_ok hu) hs).1 (by simp)
    · exact .inr (.inr ⟨σ₀, t, ev, rfl, hr', hs⟩)

/-- **A memory fault ends the trace**: from a state the byte machine reaches a
memory fault from, every trace of the process is empty (`Process.Step` has no
step at a memory fault). -/
theorem Trace.nil_of_faults {image : ByteArray} {s : ByteEval.State} {n : Nat} {σ : List Sys}
    (h : FaultsWithin image s n) (ht : Trace image s σ) : σ = [] := by
  obtain ⟨m, -, s', f, hr, hf⟩ := h
  rcases Trace.through hr ht with hnil | hts
  · exact hnil
  · have hd := decodes_of_fault hf
    have hc := defined_of_fault hf
    rcases hts with ⟨t, hr'⟩ | ⟨σ₀, t, ev, rfl, hr', hs⟩
    · cases hr' with
      | refl => rfl
      | step hs _ =>
        obtain ⟨-, u, hu, -⟩ := Step.of_decodes hd hc hs
        rw [hf] at hu
        cases hu
    · cases hr' with
      | refl => exact absurd (Step.of_decodes hd hc hs).1 (by simp)
      | step hs' _ =>
        obtain ⟨-, u, hu, -⟩ := Step.of_decodes hd hc hs'
        rw [hf] at hu
        cases hu

/-! ## The two calls of an iteration -/

/-- What the process does from the first of a caller's two calls (`cx_init`
under `L.linked.driver`, the root under `L.rootDriver`), for the outcome `res`
of `L.call` at clock `k`: as `Lifts`, within `bound` instructions, a value's
readback being `L.call`'s observation (`Linked.observe`); a resource failure
or a trap returns from either call. -/
def CallsLift (image : ByteArray) (L : LinkedAt) (r : Linked.Root) (s₀ : ByteEval.State) (bound k : Nat) :
    Result (Option Obs) → Prop
  | .timeout => (∃ s', ByteEval.run image fetchBase (k + 1) s₀ = .ok s') ∨ FaultsWithin image s₀ bound
  | .stuck => True
  | .ok o => (∃ m s' w mem, m ≤ bound ∧ ByteEval.run image fetchBase m s₀ = .ok s' ∧
      Returned L.rootDriver L.linked.driver.initBytes 0 s' ∧ s'.core.readReg .rdx = w ∧
      s'.core.memory.bytes = mem.bytes ∧ L.linked.observe r w mem = o) ∨ FaultsWithin image s₀ bound
  | .resource f => (∃ m s', m ≤ bound ∧ ByteEval.run image fetchBase m s₀ = .ok s' ∧
      (Returned L.linked.driver L.linked.driver.initBytes (ObjectEval.Resource.code f) s' ∨
        Returned L.rootDriver L.linked.driver.initBytes (ObjectEval.Resource.code f) s')) ∨
      FaultsWithin image s₀ bound
  | .trap => (∃ m s', m ≤ bound ∧ ByteEval.run image fetchBase m s₀ = .ok s' ∧
      (Returned L.linked.driver L.linked.driver.initBytes 4 s' ∨ Returned L.rootDriver L.linked.driver.initBytes 4 s')) ∨
      FaultsWithin image s₀ bound

theorem CallsLift.of_faults {image : ByteArray} {L : LinkedAt} {r : Linked.Root} {s₀ : ByteEval.State}
    {bound k : Nat} (h : FaultsWithin image s₀ bound) : ∀ res, CallsLift image L r s₀ bound k res
  | .timeout => .inr h
  | .stuck => trivial
  | .ok _ => .inr h
  | .resource _ => .inr h
  | .trap => .inr h

/-- **The two calls of an iteration, on the process.** From the process at
`cx_init`'s call site in `L.linked.driver`'s call state, and given the
instructions between the calls (`hglue`: from every return of `cx_init` with
status 0, `g` instructions reach the root's call site in `L.rootDriver`'s call
state on the bytes `cx_init` left, or fault), the process does what `L.call`'s
outcome at clock `k` says (`CallsLift`), within `2 (k + 1) + g` instructions. -/
theorem two_calls {image text : ByteArray} {textOffset : Nat} {L : LinkedAt}
    (htext : ELFRead.text? L.linked.object = some text) (hw : ∀ i < text.size, image[textOffset + i]? = text[i]?)
    (hfit : textOffset + text.size ≤ 2 ^ 64) {n : Nat} (hD : L.linked.driver.Ok n) (hD' : L.rootDriver.Ok n)
    (hbase : L.linked.driver.base = UInt64.ofNat (fileBase + textOffset))
    {r : Linked.Root} {ns : List Nat} (hns : ns.all (· < 2 ^ 64) = true) {s₀ : ByteEval.State}
    (hinit : AtCall image L.linked.object L.linked.init L.linked.driver
      [L.linked.driver.size, L.linked.driver.budget] L.linked.driver.initBytes s₀)
    {g : Nat}
    (hglue : ∀ s₁, Returned L.linked.driver L.linked.driver.initBytes 0 s₁ →
      (∃ s₂, ByteEval.run image fetchBase g s₁ = .ok s₂ ∧
        AtCall image L.linked.object r.symbol L.rootDriver (ns.map UInt64.ofNat) s₁.core.memory.bytes s₂) ∨
      FaultsWithin image s₁ g)
    (k : Nat) : CallsLift image L r s₀ (k + 1 + g + (k + 1)) k (L.call r ns k) := by
  have h₁ := hinit.lifts htext hw hfit hD hbase k
  unfold LinkedAt.call
  rw [ite_eq_left hns]
  unfold Linked.initCall
  cases hi : ObjectEval.call L.linked.object L.linked.init L.linked.driver.base
      (L.linked.driver.core [L.linked.driver.size, L.linked.driver.budget] L.linked.driver.initBytes)
      L.linked.driver.flags k with
  | timeout =>
    rw [hi] at h₁
    rcases h₁ with h | h
    · exact .inl h
    · exact .inr (h.mono (by omega))
  | stuck => trivial
  | resource f =>
    rw [hi] at h₁
    rcases h₁ with ⟨m, s', hm, hr, hret⟩ | h
    · exact .inl ⟨m, s', by omega, hr, .inl hret⟩
    · exact .inr (h.mono (by omega))
  | trap =>
    rw [hi] at h₁
    rcases h₁ with ⟨m, s', hm, hr, hret⟩ | h
    · exact .inl ⟨m, s', by omega, hr, .inl hret⟩
    · exact .inr (h.mono (by omega))
  | ok v =>
    obtain ⟨w₀, mem₀⟩ := v
    rw [hi] at h₁
    rcases h₁ with ⟨m₁, s₁, hm₁, hr₁, hret₁, -, hb₁⟩ | h
    · rcases hglue s₁ hret₁ with ⟨s₂, hr₂, hat⟩ | h
      · rw [hb₁] at hat
        have h₂ := hat.lifts htext hw hfit hD' (by exact hbase) k
        have hr₁₂ := run_comp hr₁ hr₂
        -- bytes outside the mapping: the root call's frame, then cx_init's
        have hfr : ∀ (s' : ByteEval.State),
            (∀ a, L.rootDriver.mapped a = false → s'.core.memory.bytes a = mem₀.bytes a) →
            ∀ a, L.rootDriver.mapped a = false → s'.core.memory.bytes a = L.linked.driver.initBytes a := by
          intro s' hs' a ha
          rw [hs' a ha, ← hb₁]
          exact hret₁.frame a ha
        show CallsLift image L r s₀ (k + 1 + g + (k + 1)) k
          (Sem.Result.map (fun v' => L.linked.observe r v'.1 v'.2)
            (ObjectEval.call L.linked.object r.symbol L.rootDriver.base
              (L.rootDriver.core (ns.map UInt64.ofNat) mem₀.bytes) L.rootDriver.flags k))
        cases hc : ObjectEval.call L.linked.object r.symbol L.rootDriver.base
            (L.rootDriver.core (ns.map UInt64.ofNat) mem₀.bytes) L.rootDriver.flags k with
        | timeout =>
          rw [hc] at h₂
          rcases h₂ with ⟨s₃, hr₃⟩ | h
          · obtain ⟨s₄, hr₄⟩ := run_prefix (n := m₁ + g) (m := k + 1) (by rw [Nat.add_comm (k + 1) (m₁ + g)]; exact run_comp hr₁₂ hr₃)
            exact .inl ⟨s₄, hr₄⟩
          · exact .inr ((h.shift hr₁₂).mono (by omega))
        | stuck => trivial
        | ok v' =>
          obtain ⟨w, mem⟩ := v'
          rw [hc] at h₂
          rcases h₂ with ⟨m₃, s₃, hm₃, hr₃, hret₃, hrdx, hbytes⟩ | h
          · exact .inl ⟨m₁ + g + m₃, s₃, w, mem, by omega, run_comp hr₁₂ hr₃,
              ⟨hret₃.rip, hret₃.rsp, hret₃.rax, hfr s₃ hret₃.frame, hret₃.saved⟩, hrdx, hbytes, rfl⟩
          · exact .inr ((h.shift hr₁₂).mono (by omega))
        | resource f =>
          rw [hc] at h₂
          rcases h₂ with ⟨m₃, s₃, hm₃, hr₃, hret₃⟩ | h
          · exact .inl ⟨m₁ + g + m₃, s₃, by omega, run_comp hr₁₂ hr₃,
              .inr ⟨hret₃.rip, hret₃.rsp, hret₃.rax, hfr s₃ hret₃.frame, hret₃.saved⟩⟩
          · exact .inr ((h.shift hr₁₂).mono (by omega))
        | trap =>
          rw [hc] at h₂
          rcases h₂ with ⟨m₃, s₃, hm₃, hr₃, hret₃⟩ | h
          · exact .inl ⟨m₁ + g + m₃, s₃, by omega, run_comp hr₁₂ hr₃,
              .inr ⟨hret₃.rip, hret₃.rsp, hret₃.rax, hfr s₃ hret₃.frame, hret₃.saved⟩⟩
          · exact .inr ((h.shift hr₁₂).mono (by omega))
      · exact CallsLift.of_faults ((h.shift hr₁).mono (by omega)) _
    · exact CallsLift.of_faults (h.mono (by omega)) _

end IxCC.X86.Exe.Process
