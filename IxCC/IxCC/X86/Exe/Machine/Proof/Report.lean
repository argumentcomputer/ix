import IxCC.X86.Exe.Machine.Proof.Glue

/-!
# The shell's failure report, as system calls (X0-P, third part)

Every failure of a machine executable's shell ends in one of its eight
message blocks: the message's address and length and the failure's status,
then `report`, which calls the message writer (`write`, `writeSys`,
`writeAdv`, `writeRet`) on the shell's own stack and exits with the status;
a part the platform refuses exits with 74 (`writeErr`). This module proves
that from a message block every trace of the process is a prefix of the
system calls `Process.Report` describes for that failure's status and
message (`report`).

- `syscall_write`, `syscall_exit`, `syscall_prctl`, `syscall_seccomp`: what
  `Process.Syscall` allows at each of the shell's system calls, with the
  arguments the shell passes;
- `TraceN.write`, `TraceN.exit`, `TraceN.prctl`, `TraceN.seccomp`: the same
  for traces from a `syscall`;
- `message_slice`: the message of a failure is in the file's read-only data
  where its block says, so a memory holding the file holds it;
- `AtWrite` and `write_loop`: the message writer, by induction on the steps;
- `exit_path`: the `exit` block's system call.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.X86.Encode (instructionOperation)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)
open SB

/-! ## The platform at the shell's system calls -/

theorem syscall_write {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State} (h : Syscall s ev after)
    (hax : s.core.readReg .rax = 1) :
    ∃ result rcx r11 fl, ev = .write (s.core.readReg .rdi)
        (slice s.core.memory (s.core.readReg .rsi) (s.core.readReg .rdx).toNat) result ∧
      after = some (returned s result rcx r11 fl) ∧
      (result.toNat < 2 ^ 63 → result.toNat ≤ (s.core.readReg .rdx).toNat) := by
  cases h with
  | prctl h _ => rw [hax] at h; exact absurd h (by decide)
  | seccomp h _ _ => rw [hax] at h; exact absurd h (by decide)
  | write _ hc => exact ⟨_, _, _, _, rfl, rfl, hc⟩
  | exit h => rw [hax] at h; exact absurd h (by decide)
  | other h => exact absurd (.inr (.inr (.inl hax))) h

theorem syscall_exit {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State} (h : Syscall s ev after)
    (hax : s.core.readReg .rax = 60) : ev = .exit (s.core.readReg .rdi) ∧ after = none := by
  cases h with
  | prctl h _ => rw [hax] at h; exact absurd h (by decide)
  | seccomp h _ _ => rw [hax] at h; exact absurd h (by decide)
  | write h _ => rw [hax] at h; exact absurd h (by decide)
  | exit _ => exact ⟨rfl, rfl⟩
  | other h => exact absurd (.inr (.inr (.inr hax))) h

theorem syscall_prctl {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State} (h : Syscall s ev after)
    (hax : s.core.readReg .rax = 157) (hdi : s.core.readReg .rdi = prSetNoNewPrivs) :
    ∃ result rcx r11 fl, ev = .prctl (s.core.readReg .rdi) (s.core.readReg .rsi) result ∧
      after = some (returned s result rcx r11 fl) := by
  cases h with
  | prctl _ _ => exact ⟨_, _, _, _, rfl, rfl⟩
  | seccomp h _ _ => rw [hax] at h; exact absurd h (by decide)
  | write h _ => rw [hax] at h; exact absurd h (by decide)
  | exit h => rw [hax] at h; exact absurd h (by decide)
  | other h => exact absurd (.inl ⟨hax, hdi⟩) h

theorem syscall_seccomp {s : ByteEval.State} {ev : Sys} {after : Option ByteEval.State} (h : Syscall s ev after)
    (hax : s.core.readReg .rax = 317) (hdi : s.core.readReg .rdi = seccompSetModeFilter)
    (hsi : s.core.readReg .rsi = 0) :
    ∃ result rcx r11 fl, ev = .seccomp (s.core.readReg .rdi) (s.core.readReg .rsi) (s.core.readReg .rdx) result ∧
      after = some (returned s result rcx r11 fl) := by
  cases h with
  | prctl h _ => rw [hax] at h; exact absurd h (by decide)
  | seccomp _ _ _ => exact ⟨_, _, _, _, rfl, rfl⟩
  | write h _ => rw [hax] at h; exact absurd h (by decide)
  | exit h => rw [hax] at h; exact absurd h (by decide)
  | other h => exact absurd (.inr (.inl ⟨hax, hdi, hsi⟩)) h

section
variable {image : ByteArray} {n : Nat} {s : ByteEval.State} {σ : List Sys}

/-- A trace from the shell's `write`: empty, or the write and a trace from the state after it. -/
theorem TraceN.write (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
    (hax : s.core.readReg .rax = 1) (ht : TraceN image n s σ) :
    σ = [] ∨ ∃ result rcx r11 fl σ', σ = .write (s.core.readReg .rdi)
        (slice s.core.memory (s.core.readReg .rsi) (s.core.readReg .rdx).toNat) result :: σ' ∧
      (result.toNat < 2 ^ 63 → result.toNat ≤ (s.core.readReg .rdx).toNat) ∧
      1 ≤ n ∧ TraceN image (n - 1) (returned s result rcx r11 fl) σ' := by
  rcases TraceN.sys hd hb ht with rfl | ⟨ev, after, σ', hs, rfl, hrest⟩
  · exact .inl rfl
  · obtain ⟨result, rcx, r11, fl, rfl, rfl, hc⟩ := syscall_write hs hax
    rcases hrest with ⟨s', hs', hn, ht'⟩ | ⟨hnone, -⟩
    · cases hs'
      exact .inr ⟨result, rcx, r11, fl, σ', rfl, hc, hn, ht'⟩
    · cases hnone

/-- A trace from the shell's `exit` is a prefix of the exit. -/
theorem TraceN.exit (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
    (hax : s.core.readReg .rax = 60) (ht : TraceN image n s σ) : σ <+: [.exit (s.core.readReg .rdi)] := by
  rcases TraceN.sys hd hb ht with rfl | ⟨ev, after, σ', hs, rfl, hrest⟩
  · exact List.nil_prefix
  · obtain ⟨rfl, rfl⟩ := syscall_exit hs hax
    rcases hrest with ⟨s', hs', -⟩ | ⟨-, rfl⟩
    · cases hs'
    · exact List.prefix_refl _

/-- A trace from the shell's `prctl`. -/
theorem TraceN.prctl (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
    (hax : s.core.readReg .rax = 157) (hdi : s.core.readReg .rdi = prSetNoNewPrivs) (ht : TraceN image n s σ) :
    σ = [] ∨ ∃ result rcx r11 fl σ', σ = .prctl (s.core.readReg .rdi) (s.core.readReg .rsi) result :: σ' ∧
      1 ≤ n ∧ TraceN image (n - 1) (returned s result rcx r11 fl) σ' := by
  rcases TraceN.sys hd hb ht with rfl | ⟨ev, after, σ', hs, rfl, hrest⟩
  · exact .inl rfl
  · obtain ⟨result, rcx, r11, fl, rfl, rfl⟩ := syscall_prctl hs hax hdi
    rcases hrest with ⟨s', hs', hn, ht'⟩ | ⟨hnone, -⟩
    · cases hs'
      exact .inr ⟨result, rcx, r11, fl, σ', rfl, hn, ht'⟩
    · cases hnone

/-- A trace from the shell's `seccomp`. -/
theorem TraceN.seccomp (hd : Decode.decodeAt image (s.rip - fetchBase).toNat = none) (hb : syscallAt image s.rip)
    (hax : s.core.readReg .rax = 317) (hdi : s.core.readReg .rdi = seccompSetModeFilter)
    (hsi : s.core.readReg .rsi = 0) (ht : TraceN image n s σ) :
    σ = [] ∨ ∃ result rcx r11 fl σ', σ = .seccomp (s.core.readReg .rdi) (s.core.readReg .rsi)
        (s.core.readReg .rdx) result :: σ' ∧
      1 ≤ n ∧ TraceN image (n - 1) (returned s result rcx r11 fl) σ' := by
  rcases TraceN.sys hd hb ht with rfl | ⟨ev, after, σ', hs, rfl, hrest⟩
  · exact .inl rfl
  · obtain ⟨result, rcx, r11, fl, rfl, rfl⟩ := syscall_seccomp hs hax hdi hsi
    rcases hrest with ⟨s', hs', hn, ht'⟩ | ⟨hnone, -⟩
    · cases hs'
      exact .inr ⟨result, rcx, r11, fl, σ', rfl, hn, ht'⟩
    · cases hnone

/-- A trace from a state the byte machine faults from in one step is empty. -/
theorem TraceN.nil_of_step_fault {f : MemoryFault}
    (h : ByteEval.step image fetchBase s = .error (.memory f)) (ht : TraceN image n s σ) : σ = [] :=
  TraceN.nil_of_faults (n' := 1) ⟨0, by decide, s, f, rfl, h⟩ ht

end

/-! ## Bytes -/

/-- The bytes of a slice from a later address. -/
theorem slice_drop {m : Memory} {a : Word} {len : Nat} {rest : List UInt8} (h : slice m a len = rest) (r : Nat) :
    slice m (a + UInt64.ofNat r) (len - r) = rest.drop r := by
  subst h
  apply List.ext_getElem
  · simp [slice]
  · intro i h1 h2
    simp only [slice, List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [UInt64.add_assoc, ← UInt64.ofNat_add]

theorem slice_length (m : Memory) (a : Word) (len : Nat) : (slice m a len).length = len := by
  simp [slice]

private theorem toList_loop (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k → ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, h => by
    unfold ByteArray.toList.loop
    rw [ite_eq_right (show ¬ i < bs.size by omega)]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; change bs.size ≤ i; omega), List.append_nil]
  | k + 1, i, r, h => by
    have hi : i < bs.size := by omega
    unfold ByteArray.toList.loop
    rw [ite_eq_left hi, toList_loop bs k (i + 1) _ (by omega),
      List.drop_eq_getElem_cons (i := i) (by rw [Array.length_toList]; exact hi)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    simp [ByteArray.get!, getElem!_pos bs.data i hi]

theorem ByteArray.toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop bs _ 0 [] rfl]
  simp

theorem text_length (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [ByteArray.toList_eq_data, Array.length_toList]
  rfl

theorem messageOf_status (f : Machine.Failure) : messageOf f.status = f.text.toUTF8.toList := by
  cases f <;> rfl

theorem failure_split (f : Machine.Failure) :
    ∃ before after, Machine.Failure.all.takeWhile (· != f) = before ∧ Machine.Failure.all = before ++ f :: after := by
  cases f <;> exact ⟨_, _, rfl, rfl⟩

theorem flatMap_text_length (l : List Machine.Failure) :
    (l.flatMap fun (g : Machine.Failure) => g.text.toUTF8.toList).length =
      (l.map fun (g : Machine.Failure) => g.text.utf8ByteSize).sum := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.flatMap_cons, List.length_append, ih, text_length, List.map_cons, List.sum_cons]

theorem filter_prefix_length (a : Nat) :
    (filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a).length = 112 := rfl

theorem messageAt_fst (a : Nat) (f : Machine.Failure) :
    (Machine.messageAt a f).1 = a + 112 + ((Machine.Failure.all.takeWhile (· != f)).map
      fun (g : Machine.Failure) => g.text.utf8ByteSize).sum := by
  show fprogAddr a + 16 + _ = _
  unfold fprogAddr filterLength
  omega

/-- The message of `f` ends inside the read-only data. -/
theorem message_end_le (a : Nat) (f : Machine.Failure) :
    (Machine.messageAt a f).1 - a + (Machine.messageAt a f).2 ≤ (Machine.dataBytes a).size := by
  obtain ⟨before, after, htw, hall⟩ := failure_split f
  rw [messageAt_fst, htw]
  show _ + f.text.utf8ByteSize ≤ (filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a ++
    (Machine.Failure.all.flatMap fun (g : Machine.Failure) => g.text.toUTF8.toList)).toArray.size
  rw [hall, List.flatMap_append, List.flatMap_cons, List.size_toArray, List.length_append, filter_prefix_length,
    List.length_append, List.length_append, flatMap_text_length, text_length]
  omega

/-- **The message of `f` in the read-only data.** -/
theorem dataBytes_message (a : Nat) (f : Machine.Failure) {i : Nat} (hi : i < f.text.utf8ByteSize) :
    (Machine.dataBytes a)[(Machine.messageAt a f).1 - a + i]? =
      some (f.text.toUTF8.toList[i]'(by rw [text_length]; exact hi)) := by
  obtain ⟨before, after, htw, hall⟩ := failure_split f
  rw [messageAt_fst, htw, byteArray_getElem?]
  show ((filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a ++
    (Machine.Failure.all.flatMap fun (g : Machine.Failure) => g.text.toUTF8.toList)).toArray)[_]? = _
  rw [hall, List.flatMap_append, List.flatMap_cons, List.getElem?_toArray]
  have h112 := filter_prefix_length a
  have hb := flatMap_text_length before
  rw [show a + 112 + (before.map fun (g : Machine.Failure) => g.text.utf8ByteSize).sum - a + i =
    (filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a).length +
      ((before.flatMap fun (g : Machine.Failure) => g.text.toUTF8.toList).length + i) by omega]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [text_length]; exact hi), List.getElem?_eq_getElem]

theorem getElem!_of_getElem? {a : ByteArray} {i : Nat} {v : UInt8} (h : a[i]? = some v) : a[i]! = v := by
  rw [getElem!_def, h]

section
variable {L : Machine.Layout} {step : String} {object : ByteArray} (ce : Machine.Certified L step object)

/-- **A failure's message is where its block says**, in a memory holding the file. -/
theorem message_slice (f : Machine.Failure) {m : Memory}
    (hfile : ∀ i < ce.checked.bytes.size, m.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!) :
    slice m (UInt64.ofNat (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).1)
      (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).2 = messageOf f.status := by
  have ff := Machine.fileFacts ce.checked
  obtain ⟨hdsize, hdata⟩ := ff.data
  have hsize := ff.size
  have hde := ff.dataEnd
  have hfs : ce.checked.plan.placement.fileSize =
      ce.checked.plan.placement.shellOffset + ce.checked.plan.placement.shellSize := rfl
  have hend := message_end_le (fileBase + ce.checked.plan.placement.dataOffset) f
  have hP := messageAt_fst (fileBase + ce.checked.plan.placement.dataOffset) f
  have hlen : (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).2 = f.text.utf8ByteSize := rfl
  rw [messageOf_status]
  apply List.ext_getElem
  · rw [slice_length, text_length, hlen]
  · intro i h1 h2
    have hi : i < f.text.utf8ByteSize := by rw [slice_length, hlen] at h1; exact h1
    have hlt : (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).1 -
        (fileBase + ce.checked.plan.placement.dataOffset) + i < ce.checked.plan.placement.dataSize := by
      rw [← hdsize]; omega
    have hidx := hdata _ hlt
    rw [dataBytes_message _ f hi] at hidx
    simp only [slice, List.getElem_map, List.getElem_range]
    rw [← UInt64.ofNat_add, show (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).1 + i =
      fileBase + (ce.checked.plan.placement.dataOffset +
        ((Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).1 -
          (fileBase + ce.checked.plan.placement.dataOffset) + i)) by omega]
    rw [hfile _ (by omega), getElem!_of_getElem? hidx]

/-- A failure's message fits in a word. -/
theorem message_length_lt (f : Machine.Failure) :
    (Machine.messageAt (fileBase + ce.checked.plan.placement.dataOffset) f).2 < 2 ^ 64 := by
  have ff := Machine.fileFacts ce.checked
  have h1 := message_end_le (fileBase + ce.checked.plan.placement.dataOffset) f
  rw [ff.data.1] at h1
  have := ff.dataEnd
  have := ff.size
  have := file_fit ce
  have hfs : ce.checked.plan.placement.fileSize =
      ce.checked.plan.placement.shellOffset + ce.checked.plan.placement.shellSize := rfl
  omega

/-! ## The message writer -/

/-- The message writer at `write` (block 33) with `rest` still to write to
standard error, the status in `r15` and its return address in the top word of
the shell's stack. -/
structure AtWrite (ce : Machine.Certified L step object) (status : Nat) (rest : List UInt8) (s : ByteEval.State) :
    Prop where
  rip : s.rip = UInt64.ofNat (shellAddr L step ce.checked 33 0)
  rdi : s.core.readReg .rdi = 2
  rdx : (s.core.readReg .rdx).toNat = rest.length
  bytes : slice s.core.memory (s.core.readReg .rsi) rest.length = rest
  r15 : s.core.readReg .r15 = UInt64.ofNat status
  rsp : s.core.readReg .rsp = UInt64.ofNat L.shellTop - 8
  ret : s.core.memory.read64 (UInt64.ofNat L.shellTop - 8) = UInt64.ofNat (shellAddr L step ce.checked 32 4)

/-- **The `exit` block**: a trace from it is a prefix of `exit(rdi)`. -/
theorem exit_path {s : ByteEval.State} (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked 27 0))
    {n : Nat} {σ : List Sys} (ht : TraceN ce.checked.bytes n s σ) : σ <+: [.exit (s.core.readReg .rdi)] := by
  have e1 : ByteEval.step ce.checked.bytes fetchBase s =
      .ok ⟨s.core.setReg .rax (UInt64.ofNat 60), UInt64.ofNat (shellAddr L step ce.checked 27 1), s.flags⟩ :=
    mstep_ok ce (b := 27) (j := 0) (by decide) (s := s) (i := Instr.mov .w64 .rax (.imm (UInt64.ofNat 60)))
      (by rw [block_exit]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) hrip (exec_mov _ _ _ _)
  rcases TraceN.through (run_one e1) ht with rfl | ⟨-, ht'⟩
  · exact List.nil_prefix
  · obtain ⟨hd, hb, -⟩ := msyscall_at ce (b := 27) (j := 1) (by decide) (by rw [block_exit]; rfl)
      (s := ⟨s.core.setReg .rax (UInt64.ofNat 60), UInt64.ofNat (shellAddr L step ce.checked 27 1), s.flags⟩) rfl
    have hax : (s.core.setReg .rax (UInt64.ofNat 60)).readReg .rax = 60 := rfl
    exact TraceN.exit (s := ⟨s.core.setReg .rax (UInt64.ofNat 60), UInt64.ofNat (shellAddr L step ce.checked 27 1),
      s.flags⟩) hd hb hax ht'

theorem truncate64 (v : Word) : Width.w64.truncate v = v := by
  apply UInt64.toBitVec_inj.mp
  change v.toBitVec &&& BitVec.allOnes 64 = v.toBitVec
  exact BitVec.and_allOnes

theorem signedValue_w64 (v : Word) :
    Width.w64.signedValue v =
      if v.toNat < 9223372036854775808 then (v.toNat : Int) else (v.toNat : Int) - 18446744073709551616 := by
  unfold Width.signedValue
  rw [truncate64]
  rfl

/-- What `cmp r, 0` with `jle` (signed) decides. -/
theorem signedLe_zero (v : Word) :
    Condition.holds .signedLe .w64 v (signExtend32 (UInt32.ofNat 0)) = decide (v.toNat = 0 ∨ 2 ^ 63 ≤ v.toNat) := by
  have hv := v.toNat_lt
  have h0 : signExtend32 (UInt32.ofNat 0) = 0 := by decide
  rw [h0]
  show decide (Width.w64.signedValue v ≤ Width.w64.signedValue 0) = _
  have hz : (0 : Word).toNat = 0 := rfl
  rw [signedValue_w64, signedValue_w64, hz, ite_eq_left (show (0 : Nat) < 9223372036854775808 by decide)]
  apply decide_eq_decide.mpr
  by_cases h : v.toNat < 9223372036854775808
  · rw [ite_eq_left h]
    constructor <;> intro h' <;> omega
  · rw [ite_eq_right h]
    constructor <;> intro h' <;> omega

theorem report_nil (status : Nat) (m : List UInt8) : ∃ b ρ, Report status m b ρ ∧ ([] : List Sys) <+: ρ := by
  cases m with
  | nil => exact ⟨true, _, .done, List.nil_prefix⟩
  | cons x xs => exact ⟨false, _, .refused (r := 0) (List.cons_ne_nil x xs) (.inl rfl), List.nil_prefix⟩

/-- **The message writer**: from `write` with `rest` left, a trace is a prefix of a report of `rest`. -/
theorem write_loop : ∀ (n : Nat) {status : Nat} {rest : List UInt8} {s : ByteEval.State} {σ : List Sys},
    AtWrite ce status rest s → TraceN ce.checked.bytes n s σ → ∃ b ρ, Report status rest b ρ ∧ σ <+: ρ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro status rest s σ hw ht
  let img := ce.checked.bytes
  let a : Nat → Nat → Word := fun b j => UInt64.ofNat (shellAddr L step ce.checked b j)
  let cmp : Compare := { width := .w64, left := .rdx, right := .imm (UInt32.ofNat 0) }
  have h0 : signExtend32 (UInt32.ofNat 0) = 0 := by decide
  cases rest with
  | nil =>
    have hrdx : s.core.readReg .rdx = 0 := UInt64.toNat_inj.mp (by rw [hw.rdx]; rfl)
    -- write: rdx = 0, to writeRet
    have e1 : ByteEval.run img fetchBase 2 s = .ok ⟨s.core, a 36 0, cmp.flags s.core⟩ :=
      mrun_branch ce (b := 33) (by decide) (o := cmp.row.1) (args := cmp.row.2) (cond := .eq) (yes := 36) (no := 34)
        (by rw [block_write]; rfl) (s := s) (core := s.core) (fl := cmp.flags s.core)
        (by rw [hw.rip, block_write]; rfl) (exec_compare _ _ _) (taken := true)
        (by rw [compare_test]
            show some (Condition.holds .eq .w64 (s.core.readReg .rdx) (signExtend32 (UInt32.ofNat 0))) = some true
            rw [h0, hrdx]; rfl)
    -- writeRet: ret to report's fifth instruction
    have hret : ByteEval.step img fetchBase ⟨s.core, a 36 0, cmp.flags s.core⟩ =
        match s.core.memory.read64? (s.core.readReg .rsp) with
        | .error fault => .error (.memory fault)
        | .ok target => .ok ⟨s.core.setReg .rsp (s.core.readReg .rsp + 8), target, cmp.flags s.core⟩ :=
      mstep_ret ce (b := 36) (by decide) (by rw [block_writeRet])
        (s := ⟨s.core, a 36 0, cmp.flags s.core⟩) (by rw [block_writeRet]; rfl)
    cases hrd : s.core.memory.read64? (s.core.readReg .rsp) with
    | error f =>
      rw [hrd] at hret
      rcases TraceN.through e1 ht with rfl | ⟨-, ht'⟩
      · exact ⟨true, _, .done, List.nil_prefix⟩
      · exact ⟨true, _, .done, by rw [TraceN.nil_of_step_fault hret ht']; exact List.nil_prefix⟩
    | ok target =>
      rw [hrd] at hret
      have htarget : target = a 32 4 := by
        rw [read64?_value hrd, hw.rsp, hw.ret]
      let k2 := s.core.setReg .rsp (s.core.readReg .rsp + 8)
      have e2 : ByteEval.step img fetchBase ⟨s.core, a 36 0, cmp.flags s.core⟩ = .ok ⟨k2, a 32 4, cmp.flags s.core⟩ := by
        rw [hret, htarget]
      -- report, instruction 4: mov rdi, r15; then jmp exit
      let k3 := k2.setReg .rdi (k2.readReg .r15)
      have e3 : ByteEval.step img fetchBase ⟨k2, a 32 4, cmp.flags s.core⟩ = .ok ⟨k3, a 32 5, cmp.flags s.core⟩ :=
        mstep_ok ce (b := 32) (j := 4) (by decide) (s := ⟨k2, a 32 4, cmp.flags s.core⟩)
          (i := Instr.mov .w64 .rdi (.reg .r15)) (by rw [block_report]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl
          (exec_mov _ _ _ _)
      have e4 : ByteEval.step img fetchBase ⟨k3, a 32 5, cmp.flags s.core⟩ = .ok ⟨k3, a 27 0, cmp.flags s.core⟩ :=
        mstep_jump ce (b := 32) (by decide) (t := 27) (by rw [block_report]; rfl) (s := ⟨k3, a 32 5, cmp.flags s.core⟩)
          (by rw [block_report]; rfl)
      have hrun : ByteEval.run img fetchBase 5 s = .ok ⟨k3, a 27 0, cmp.flags s.core⟩ :=
        run_comp e1 (run_comp (run_one e2) (run_comp (run_one e3) (run_one e4)))
      have hrdi : k3.readReg .rdi = UInt64.ofNat status := by
        show s.core.readReg .r15 = _
        exact hw.r15
      rcases TraceN.through hrun ht with rfl | ⟨-, ht'⟩
      · exact ⟨true, _, .done, List.nil_prefix⟩
      · have h : _ <+: [Sys.exit (k3.readReg .rdi)] := exit_path ce (s := ⟨k3, a 27 0, cmp.flags s.core⟩) rfl ht'
        rw [hrdi] at h
        exact ⟨true, _, .done, h⟩
  | cons x xs =>
    have hne : x :: xs ≠ [] := List.cons_ne_nil x xs
    have hrdx : s.core.readReg .rdx ≠ 0 := by
      intro hz
      have := hw.rdx
      rw [hz] at this
      simp at this
    -- write: rdx ≠ 0, to writeSys
    have e1 : ByteEval.run img fetchBase 3 s = .ok ⟨s.core, a 34 0, cmp.flags s.core⟩ :=
      mrun_branch ce (b := 33) (by decide) (o := cmp.row.1) (args := cmp.row.2) (cond := .eq) (yes := 36) (no := 34)
        (by rw [block_write]; rfl) (s := s) (core := s.core) (fl := cmp.flags s.core)
        (by rw [hw.rip, block_write]; rfl) (exec_compare _ _ _) (taken := false)
        (by rw [compare_test]
            show some (Condition.holds .eq .w64 (s.core.readReg .rdx) (signExtend32 (UInt32.ofNat 0))) = some false
            rw [h0]; simp [Condition.holds, hrdx])
    -- writeSys: mov rax, 1; syscall
    let k2 := s.core.setReg .rax (UInt64.ofNat 1)
    have e2 : ByteEval.step img fetchBase ⟨s.core, a 34 0, cmp.flags s.core⟩ = .ok ⟨k2, a 34 1, cmp.flags s.core⟩ :=
      mstep_ok ce (b := 34) (j := 0) (by decide) (s := ⟨s.core, a 34 0, cmp.flags s.core⟩)
        (i := Instr.mov .w64 .rax (.imm (UInt64.ofNat 1))) (by rw [block_writeSys]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl
        (exec_mov _ _ _ _)
    have hrun : ByteEval.run img fetchBase 4 s = .ok ⟨k2, a 34 1, cmp.flags s.core⟩ := run_comp e1 (run_one e2)
    obtain ⟨hd, hb, hnext⟩ := msyscall_at ce (b := 34) (j := 1) (by decide) (by rw [block_writeSys]; rfl)
      (s := ⟨k2, a 34 1, cmp.flags s.core⟩) rfl
    let s2 : ByteEval.State := ⟨k2, a 34 1, cmp.flags s.core⟩
    rcases TraceN.through hrun ht with rfl | ⟨hn4, ht'⟩
    · exact report_nil _ _
    rcases TraceN.write (s := s2) hd hb rfl ht' with rfl | ⟨r, rcx, r11, fl, σ', rfl, hcount, hn1, ht''⟩
    · exact report_nil _ _
    have hev : Sys.write (s2.core.readReg .rdi) (slice s2.core.memory (s2.core.readReg .rsi) (s2.core.readReg .rdx).toNat) r =
        .write 2 (x :: xs) r := by
      show Sys.write (s.core.readReg .rdi) (slice s.core.memory (s.core.readReg .rsi) (s.core.readReg .rdx).toNat) r = _
      rw [hw.rdi, hw.rdx, hw.bytes]
    rw [hev]
    -- after the call: cmp rax, 0; jle writeErr
    let s3 := returned s2 r rcx r11 fl
    have h3rip : s3.rip = a 34 2 := hnext
    have h3rax : s3.core.readReg .rax = r := rfl
    let cmp2 : Compare := { width := .w64, left := .rax, right := .imm (UInt32.ofNat 0) }
    by_cases href : r.toNat = 0 ∨ 2 ^ 63 ≤ r.toNat
    · -- refused: writeErr, exit 74
      have e3 : ByteEval.run img fetchBase 2 s3 = .ok ⟨s3.core, a 37 0, cmp2.flags s3.core⟩ :=
        mrun_branch ce (b := 34) (by decide) (o := cmp2.row.1) (args := cmp2.row.2) (cond := .signedLe) (yes := 37)
          (no := 35) (by rw [block_writeSys]; rfl) (s := s3) (core := s3.core) (fl := cmp2.flags s3.core)
          (by rw [h3rip, block_writeSys]; rfl) (exec_compare _ _ _) (taken := true)
          (by rw [compare_test]
              show some (Condition.holds .signedLe .w64 (s3.core.readReg .rax) (signExtend32 (UInt32.ofNat 0))) = _
              rw [signedLe_zero, h3rax]; simp [href])
      let k4 := s3.core.setReg .rdi (UInt64.ofNat 74)
      have e4 : ByteEval.step img fetchBase ⟨s3.core, a 37 0, cmp2.flags s3.core⟩ = .ok ⟨k4, a 37 1, cmp2.flags s3.core⟩ :=
        mstep_ok ce (b := 37) (j := 0) (by decide) (s := ⟨s3.core, a 37 0, cmp2.flags s3.core⟩)
          (i := Instr.mov .w64 .rdi (.imm (UInt64.ofNat 74))) (by rw [block_writeErr]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl
          (exec_mov _ _ _ _)
      have e5 : ByteEval.step img fetchBase ⟨k4, a 37 1, cmp2.flags s3.core⟩ = .ok ⟨k4, a 27 0, cmp2.flags s3.core⟩ :=
        mstep_jump ce (b := 37) (by decide) (t := 27) (by rw [block_writeErr]; rfl) (s := ⟨k4, a 37 1, cmp2.flags s3.core⟩)
          (by rw [block_writeErr]; rfl)
      have hrun2 : ByteEval.run img fetchBase 4 s3 = .ok ⟨k4, a 27 0, cmp2.flags s3.core⟩ :=
        run_comp e3 (run_comp (run_one e4) (run_one e5))
      refine ⟨false, _, .refused hne href, ?_⟩
      rcases TraceN.through hrun2 ht'' with rfl | ⟨-, ht3⟩
      · exact (List.prefix_cons_inj _).mpr List.nil_prefix
      · exact (List.prefix_cons_inj _).mpr (exit_path ce (s := ⟨k4, a 27 0, cmp2.flags s3.core⟩) rfl ht3)
    · -- written: writeAdv, back to write
      have hr0 : 0 < r.toNat := by omega
      have hr63 : r.toNat < 2 ^ 63 := by omega
      have hle : r.toNat ≤ (x :: xs).length := by
        have := hcount hr63
        rwa [show s2.core.readReg .rdx = s.core.readReg .rdx from rfl, hw.rdx] at this
      have e3 : ByteEval.run img fetchBase 3 s3 = .ok ⟨s3.core, a 35 0, cmp2.flags s3.core⟩ :=
        mrun_branch ce (b := 34) (by decide) (o := cmp2.row.1) (args := cmp2.row.2) (cond := .signedLe) (yes := 37)
          (no := 35) (by rw [block_writeSys]; rfl) (s := s3) (core := s3.core) (fl := cmp2.flags s3.core)
          (by rw [h3rip, block_writeSys]; rfl) (exec_compare _ _ _) (taken := false)
          (by rw [compare_test]
              show some (Condition.holds .signedLe .w64 (s3.core.readReg .rax) (signExtend32 (UInt32.ofNat 0))) = _
              rw [signedLe_zero, h3rax]; simp [href])
      obtain ⟨fl4, h4⟩ := exec_alu ⟨s3.core, a 35 0, cmp2.flags s3.core⟩ .add .w64 .rsi (.reg .rax)
        (Shell.Instr.size (.instr (Instr.alu .add .w64 .rsi (.reg .rax))))
      let k4 := s3.core.setReg .rsi (s3.core.readReg .rsi + s3.core.readReg .rax)
      have e4 : ByteEval.step img fetchBase ⟨s3.core, a 35 0, cmp2.flags s3.core⟩ = .ok ⟨k4, a 35 1, fl4⟩ :=
        mstep_ok ce (b := 35) (j := 0) (by decide) (s := ⟨s3.core, a 35 0, cmp2.flags s3.core⟩)
          (i := Instr.alu .add .w64 .rsi (.reg .rax)) (by rw [block_writeAdv]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl h4
      obtain ⟨fl5, h5⟩ := exec_alu ⟨k4, a 35 1, fl4⟩ .sub .w64 .rdx (.reg .rax)
        (Shell.Instr.size (.instr (Instr.alu .sub .w64 .rdx (.reg .rax))))
      let k5 := k4.setReg .rdx (k4.readReg .rdx - k4.readReg .rax)
      have e5 : ByteEval.step img fetchBase ⟨k4, a 35 1, fl4⟩ = .ok ⟨k5, a 35 2, fl5⟩ :=
        mstep_ok ce (b := 35) (j := 1) (by decide) (s := ⟨k4, a 35 1, fl4⟩)
          (i := Instr.alu .sub .w64 .rdx (.reg .rax)) (by rw [block_writeAdv]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl h5
      have e6 : ByteEval.step img fetchBase ⟨k5, a 35 2, fl5⟩ = .ok ⟨k5, a 33 0, fl5⟩ :=
        mstep_jump ce (b := 35) (by decide) (t := 33) (by rw [block_writeAdv]; rfl) (s := ⟨k5, a 35 2, fl5⟩)
          (by rw [block_writeAdv]; rfl)
      have hrun2 : ByteEval.run img fetchBase 6 s3 = .ok ⟨k5, a 33 0, fl5⟩ :=
        run_comp e3 (run_comp (run_one e4) (run_comp (run_one e5) (run_one e6)))
      -- the writer again, with the rest
      have hrsi : k5.readReg .rsi = s.core.readReg .rsi + UInt64.ofNat r.toNat := by
        show s.core.readReg .rsi + r = _
        rw [UInt64.ofNat_toNat]
      have hrdx' : (k5.readReg .rdx).toNat = (x :: xs).length - r.toNat := by
        show (s.core.readReg .rdx - r).toNat = _
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hw.rdx]; exact hle), hw.rdx]
      have hw' : AtWrite ce status ((x :: xs).drop r.toNat) ⟨k5, a 33 0, fl5⟩ := by
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hw.rdi
        · show (k5.readReg .rdx).toNat = _
          rw [hrdx', List.length_drop]
        · show slice s.core.memory (k5.readReg .rsi) _ = _
          rw [hrsi, List.length_drop]
          exact slice_drop hw.bytes r.toNat
        · exact hw.r15
        · exact hw.rsp
        · exact hw.ret
      rcases TraceN.through hrun2 ht'' with rfl | ⟨hn6, ht3⟩
      · obtain ⟨b, ρ, hρ, -⟩ := report_nil status ((x :: xs).drop r.toNat)
        exact ⟨b, _, .part hne ⟨hr0, hle⟩ hρ, (List.prefix_cons_inj _).mpr List.nil_prefix⟩
      · obtain ⟨b, ρ, hρ, hp⟩ := ih (n - 4 - 1 - 6) (by omega) hw' ht3
        exact ⟨b, _, .part hne ⟨hr0, hle⟩ hρ, (List.prefix_cons_inj _).mpr hp⟩

/-- **The report**: from the message block of a failure, in a memory holding
the file, every trace is a prefix of the report of its message with its
status. -/
theorem report (f : Machine.Failure) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked (Machine.B.message f) 0))
    (hfile : ∀ i < ce.checked.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.checked.bytes n s σ) :
    ∃ b ρ, Report f.status (messageOf f.status) b ρ ∧ σ <+: ρ := by
  let img := ce.checked.bytes
  let a : Nat → Nat → Word := fun b j => UInt64.ofNat (shellAddr L step ce.checked b j)
  let D := fileBase + ce.checked.plan.placement.dataOffset
  let mb := Machine.B.message f
  have hb : mb < 46 := message_index f
  have hblk : blockAt (shellOf ce.checked) mb = msgBlock D f := block_message L step D f
  -- the message block: mov rsi, address; mov rdx, length; mov r15, status; jmp report
  let k1 := s.core.setReg .rsi (UInt64.ofNat (Machine.messageAt D f).1)
  have e1 : ByteEval.step img fetchBase s = .ok ⟨k1, a mb 1, s.flags⟩ :=
    mstep_ok ce (b := mb) (j := 0) hb (s := s) (i := Instr.mov .w64 .rsi (.imm (UInt64.ofNat (Machine.messageAt D f).1)))
      (by rw [hblk]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) hrip (exec_mov _ _ _ _)
  let k2 := k1.setReg .rdx (UInt64.ofNat (Machine.messageAt D f).2)
  have e2 : ByteEval.step img fetchBase ⟨k1, a mb 1, s.flags⟩ = .ok ⟨k2, a mb 2, s.flags⟩ :=
    mstep_ok ce (b := mb) (j := 1) hb (s := ⟨k1, a mb 1, s.flags⟩)
      (i := Instr.mov .w64 .rdx (.imm (UInt64.ofNat (Machine.messageAt D f).2)))
      (by rw [hblk]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  let k3 := k2.setReg .r15 (UInt64.ofNat f.status)
  have e3 : ByteEval.step img fetchBase ⟨k2, a mb 2, s.flags⟩ = .ok ⟨k3, a mb 3, s.flags⟩ :=
    mstep_ok ce (b := mb) (j := 2) hb (s := ⟨k2, a mb 2, s.flags⟩) (i := Instr.mov .w64 .r15 (.imm (UInt64.ofNat f.status)))
      (by rw [hblk]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  have e4 : ByteEval.step img fetchBase ⟨k3, a mb 3, s.flags⟩ = .ok ⟨k3, a 32 0, s.flags⟩ :=
    mstep_jump ce (b := mb) hb (t := 32) (by rw [hblk]; rfl) (s := ⟨k3, a mb 3, s.flags⟩) (by rw [hblk]; rfl)
  -- report: mov r11, shellTop; mov rsp, r11; mov rdi, 2; call write
  let T : Word := UInt64.ofNat L.shellTop
  let k5 := k3.setReg .r11 T
  have e5 : ByteEval.step img fetchBase ⟨k3, a 32 0, s.flags⟩ = .ok ⟨k5, a 32 1, s.flags⟩ :=
    mstep_ok ce (b := 32) (j := 0) (by decide) (s := ⟨k3, a 32 0, s.flags⟩) (i := Instr.mov .w64 .r11 (.imm T))
      (by rw [block_report]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  let k6 := k5.setReg .rsp (k5.readReg .r11)
  have e6 : ByteEval.step img fetchBase ⟨k5, a 32 1, s.flags⟩ = .ok ⟨k6, a 32 2, s.flags⟩ :=
    mstep_ok ce (b := 32) (j := 1) (by decide) (s := ⟨k5, a 32 1, s.flags⟩) (i := Instr.mov .w64 .rsp (.reg .r11))
      (by rw [block_report]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  let k7 := k6.setReg .rdi (UInt64.ofNat 2)
  have e7 : ByteEval.step img fetchBase ⟨k6, a 32 2, s.flags⟩ = .ok ⟨k7, a 32 3, s.flags⟩ :=
    mstep_ok ce (b := 32) (j := 2) (by decide) (s := ⟨k6, a 32 2, s.flags⟩) (i := Instr.mov .w64 .rdi (.imm (UInt64.ofNat 2)))
      (by rw [block_report]; rfl) (ne_call_of_op ⟨_, _, rfl⟩) rfl (exec_mov _ _ _ _)
  have hrun : ByteEval.run img fetchBase 7 s = .ok ⟨k7, a 32 3, s.flags⟩ :=
    run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4)
      (run_comp (run_one e5) (run_comp (run_one e6) (run_one e7))))))
  have hcall : ByteEval.step img fetchBase ⟨k7, a 32 3, s.flags⟩ =
      match k7.memory.write64? (T - 8) (a 32 4) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok ⟨{ k7.setReg .rsp (T - 8) with memory }, a 33 0, s.flags⟩ :=
    mstep_call ce (b := 32) (j := 3) (by decide) (t := 33) (by rw [block_report]; rfl) (s := ⟨k7, a 32 3, s.flags⟩) rfl
  rcases TraceN.through hrun ht with rfl | ⟨-, ht'⟩
  · exact report_nil _ _
  cases hwr : k7.memory.write64? (T - 8) (a 32 4) with
  | error fault =>
    rw [hwr] at hcall
    rw [TraceN.nil_of_step_fault hcall ht']
    exact report_nil _ _
  | ok mem =>
    rw [hwr] at hcall
    let k8 : Core := { k7.setReg .rsp (T - 8) with memory := mem }
    have hmem : mem = s.core.memory.write64 (T - 8) (a 32 4) := by
      unfold Memory.write64? Memory.write? at hwr
      split at hwr
      · cases hwr; rfl
      · cases hwr
    have ff := Machine.fileFacts ce.checked
    obtain ⟨h1, h2, -, h4, -⟩ := layout_numbers ce
    have hd : dataBase = 268435456 := rfl
    have hfile' : ∀ i < ce.checked.bytes.size, mem.bytes (UInt64.ofNat (fileBase + i)) = ce.checked.bytes[i]! := by
      intro i hi
      rw [hmem, Memory.write64_bytes_outside]
      · exact hfile i hi
      · intro j hj heq
        have hfit := file_fit ce
        have hbl := ff.below
        have hsz := ff.size
        have e1 : (UInt64.ofNat (fileBase + i)).toNat = fileBase + i := toNat_small (by omega)
        have e2 : (T - 8 + UInt64.ofNat j).toNat = L.shellTop - 8 + j := by
          have hT : T.toNat = L.shellTop := toNat_small (by omega)
          rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hT]; show 8 ≤ _; omega),
            hT, toNat_small (show j < 2 ^ 64 by omega)]
          show (L.shellTop - 8 + j) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have := congrArg UInt64.toNat heq
        rw [e1, e2] at this
        omega
    have hw : AtWrite ce f.status (messageOf f.status) ⟨k8, a 33 0, s.flags⟩ := by
      have hlen : (Machine.messageAt D f).2 = (messageOf f.status).length := by
        rw [messageOf_status, text_length]; rfl
      refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
      · show (UInt64.ofNat (Machine.messageAt D f).2).toNat = _
        rw [toNat_small (message_length_lt ce f), hlen]
      · show slice mem (UInt64.ofNat (Machine.messageAt D f).1) _ = _
        rw [← hlen]
        exact message_slice ce f hfile'
      · show mem.read64 (T - 8) = _
        rw [hmem]
        exact Memory.read64_write64 _ _ _
    rcases TraceN.through (run_one hcall) ht' with rfl | ⟨-, ht''⟩
    · exact report_nil _ _
    · exact write_loop ce _ hw ht''

end

end IxCC.X86.Exe.Process
