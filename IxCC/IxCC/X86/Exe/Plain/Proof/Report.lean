import IxCC.X86.Exe.Plain.Proof.Blocks

/-! # Plain Shell: `write`, `exit`, Failure Reports, Fail Dispatch & Decimal Rendering

Proves all exit-bound paths of the plain `--exe` shell (`X86.Exe.Code.shell`):
- `plain_exit_path`: block 17 (`exit(rdi)`)
- `plain_write_loop`: blocks 18–22 + 47 (`write` loop with short-write and overrun guard)
- `plain_report_path`: `B.message m` → `B.report` → `ReportsMsg input.arity m`
- `plain_fail_path`: blocks 33–36 (`fail` → `.heap` / `.stack` / `.natOverflow` / `.trap` / `.abi`)
- `plain_result_path`: blocks 12–16 (`result` → `tag` → `render` → `digit` loop → `output`)
  producing `PrintsResult input.result v` or `ReportsMsg input.arity .notValue`. -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open PB

/-! ## Message slices in `dataBytes` -/

theorem plain_message_split (m : Message) :
    ∃ before after, Message.all.takeWhile (· != m) = before ∧ Message.all = before ++ m :: after := by
  cases m <;> exact ⟨_, _, rfl, rfl⟩

theorem plain_flatMap_text_length (arity : Nat) (l : List Message) :
    (l.flatMap fun (g : Message) => (g.text arity).toUTF8.toList).length =
      (l.map fun (g : Message) => (g.text arity).utf8ByteSize).sum := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [List.flatMap_cons, List.length_append, ih, text_length, List.map_cons, List.sum_cons]

theorem plain_messageAt_fst (arity a : Nat) (m : Message) :
    (messageAt arity a m).1 = a + 112 +
      ((Message.all.takeWhile (· != m)).map fun (g : Message) => (g.text arity).utf8ByteSize).sum := by
  show fprogAddr a + 16 + _ = _
  unfold fprogAddr filterLength
  omega

theorem plain_message_end_le (arity a : Nat) (m : Message) :
    (messageAt arity a m).1 - a + (messageAt arity a m).2 ≤ (dataBytes arity a).size := by
  obtain ⟨before, after, htw, hall⟩ := plain_message_split m
  rw [plain_messageAt_fst, htw]
  show _ + (m.text arity).utf8ByteSize ≤
    (filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a ++
      (Message.all.flatMap fun (g : Message) => (g.text arity).toUTF8.toList)).toArray.size
  rw [hall, List.flatMap_append, List.flatMap_cons, List.size_toArray, List.length_append,
    filter_prefix_length, List.length_append, List.length_append, plain_flatMap_text_length, text_length]
  omega

theorem plain_dataBytes_message (arity a : Nat) (m : Message) {i : Nat}
    (hi : i < (m.text arity).utf8ByteSize) :
    (dataBytes arity a)[(messageAt arity a m).1 - a + i]? =
      some ((m.text arity).toUTF8.toList[i]'(by rw [text_length]; exact hi)) := by
  obtain ⟨before, after, htw, hall⟩ := plain_message_split m
  rw [plain_messageAt_fst, htw, byteArray_getElem?]
  show ((filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a ++
    (Message.all.flatMap fun (g : Message) => (g.text arity).toUTF8.toList)).toArray)[_]? = _
  rw [hall, List.flatMap_append, List.flatMap_cons, List.getElem?_toArray]
  have h112 := filter_prefix_length a
  have hb := plain_flatMap_text_length arity before
  rw [show a + 112 + (before.map fun (g : Message) => (g.text arity).utf8ByteSize).sum - a + i =
    (filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 a).length +
      ((before.flatMap fun (g : Message) => (g.text arity).toUTF8.toList).length + i) by omega]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [text_length]; exact hi), List.getElem?_eq_getElem]

section
variable {input : X86.Exe.Input} (ce : Certified input)

theorem plain_message_slice (m : Message) {mem : Memory}
    (hfile : ∀ i < ce.bytes.size, mem.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!) :
    slice mem (UInt64.ofNat (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).1)
      (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).2 =
      (m.text input.arity).toUTF8.toList := by
  have ff := plainFileFacts ce
  obtain ⟨hdsize, hdata⟩ := ff.data
  have hsize := ff.size
  have hde := ff.dataEnd
  have hfs : ce.plan.placement.fileSize = ce.plan.placement.shellOffset + ce.plan.placement.shellSize := rfl
  have hend := plain_message_end_le input.arity (fileBase + ce.plan.placement.dataOffset) m
  have hP := plain_messageAt_fst input.arity (fileBase + ce.plan.placement.dataOffset) m
  have hlen : (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).2 =
      (m.text input.arity).utf8ByteSize := rfl
  apply List.ext_getElem
  · rw [slice_length, text_length, hlen]
  · intro i h1 h2
    have hi : i < (m.text input.arity).utf8ByteSize := by rw [slice_length, hlen] at h1; exact h1
    have hlt : (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).1 -
        (fileBase + ce.plan.placement.dataOffset) + i < ce.plan.placement.dataSize := by
      rw [← hdsize]; omega
    have hidx := hdata _ hlt
    rw [plain_dataBytes_message _ _ m hi] at hidx
    simp only [slice, List.getElem_map, List.getElem_range]
    rw [← UInt64.ofNat_add,
      show (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).1 + i =
        fileBase + (ce.plan.placement.dataOffset +
          ((messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).1 -
            (fileBase + ce.plan.placement.dataOffset) + i)) by omega]
    rw [hfile _ (by omega), getElem!_of_getElem? hidx]

theorem plain_message_length_lt (m : Message) :
    (messageAt input.arity (fileBase + ce.plan.placement.dataOffset) m).2 < 2 ^ 64 := by
  have ff := plainFileFacts ce
  have h1 := plain_message_end_le input.arity (fileBase + ce.plan.placement.dataOffset) m
  rw [ff.data.1] at h1
  have := ff.dataEnd
  have := ff.size
  have := plain_file_fit ce
  have hfs : ce.plan.placement.fileSize = ce.plan.placement.shellOffset + ce.plan.placement.shellSize := rfl
  omega

/-! ## `exit` (block 17) -/

theorem plain_exit_path {s : ByteEval.State} (hrip : s.rip = paddr ce 17 0)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n s σ) :
    σ <+: [.exit (s.core.readReg .rdi)] := by
  have e1 : ByteEval.step ce.bytes fetchBase s =
      .ok ⟨s.core.setReg .rax (UInt64.ofNat 60), paddr ce 17 1, s.flags⟩ :=
    pstep_ok ce (b := 17) (j := 0) (by decide) (s := s)
      (i := Instr.mov .w64 .rax (.imm (UInt64.ofNat 60)))
      (by rw [PB.block_exit]; rfl) (by intro t h; cases h) hrip (exec_mov _ _ _ _)
  rcases TraceN.through (run_one e1) ht with rfl | ⟨-, ht'⟩
  · exact List.nil_prefix
  · obtain ⟨hd, hb, -⟩ := psyscall_at ce (b := 17) (j := 1) (by decide)
      (by rw [PB.block_exit]; rfl) (s := ⟨s.core.setReg .rax (UInt64.ofNat 60), paddr ce 17 1, s.flags⟩) rfl
    exact TraceN.exit (s := ⟨s.core.setReg .rax (UInt64.ofNat 60), paddr ce 17 1, s.flags⟩) hd hb rfl ht'

/-! ## Generic `write` loop (blocks 18–22, 47) -/

private theorem plain_writeErr_path {s : ByteEval.State} (hrip : s.rip = paddr ce 22 0)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n s σ) :
    σ <+: [.exit (UInt64.ofNat writeFailed)] := by
  have e1 : ByteEval.step ce.bytes fetchBase s =
      .ok ⟨s.core.setReg .rdi (UInt64.ofNat writeFailed), paddr ce 22 1, s.flags⟩ :=
    pstep_ok ce (b := 22) (j := 0) (by decide) (s := s)
      (i := Instr.mov .w64 .rdi (.imm (UInt64.ofNat writeFailed)))
      (by rw [PB.block_writeErr]; rfl) (by intro t h; cases h) hrip (exec_mov _ _ _ _)
  have e2 := pstep_jump ce (b := 22) (by decide) (t := UInt32.ofNat 17)
    (by rw [PB.block_writeErr])
    (s := ⟨s.core.setReg .rdi (UInt64.ofNat writeFailed), paddr ce 22 1, s.flags⟩)
    (by rw [PB.block_writeErr]; rfl)
  rcases TraceN.through (run_comp (run_one e1) (run_one e2)) ht with rfl | ⟨-, ht'⟩
  · exact List.nil_prefix
  · exact plain_exit_path ce (s := ⟨s.core.setReg .rdi (UInt64.ofNat writeFailed), paddr ce 17 0, s.flags⟩) rfl ht'

/-- **Generic `write` loop**: from block 18 (`B.write`) with `fd` in `rdi`, `rest`
at `[rsi .. rsi + rdx)`, shell return address `retAddr` on the dedicated shell
stack at `shellTop - 8`, and continuation `hcont` exiting with `status` after
`ret`, every trace is a prefix of `WriteSeq fd status rest ok full`. -/
theorem plain_write_loop : ∀ (n : Nat) {fd : Word} {status : Nat} {retAddr : Word}
    {rest : List UInt8} {s : ByteEval.State} {σ : List Sys},
    s.rip = paddr ce 18 0 →
    s.core.readReg .rdi = fd →
    (s.core.readReg .rdx).toNat = rest.length →
    slice s.core.memory (s.core.readReg .rsi) rest.length = rest →
    s.core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 →
    s.core.memory.read64 (UInt64.ofNat input.layout.shellTop - 8) = retAddr →
    (∀ (c' : Core) (fl' : ByteEval.Flags) (n' : Nat) (σ' : List Sys),
      n' ≤ n →
      c'.memory = s.core.memory →
      c'.readReg .rsp = UInt64.ofNat input.layout.shellTop →
      c'.readReg .r15 = s.core.readReg .r15 →
      TraceN ce.bytes n' ⟨c', retAddr, fl'⟩ σ' →
      σ' <+: [.exit (UInt64.ofNat status)]) →
    TraceN ce.bytes n s σ →
    ∃ ok full, WriteSeq fd status rest ok full ∧ σ <+: full := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro fd status retAddr rest s σ hrip hdi hdx hbytes hrsp hret hcont ht
    have hL := plainLayout_numbers ce
    have htop8 : (UInt64.ofNat input.layout.shellTop - 8) + 8 = UInt64.ofNat input.layout.shellTop := by
      have hd : dataBase = 268435456 := rfl
      have hge : 8 ≤ input.layout.shellTop := by omega
      have hlt : input.layout.shellTop < 2 ^ 64 := by omega
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_sub_of_le]
      · rw [toNat_small hlt, show (8 : Word).toNat = 8 from rfl]
        rw [Nat.sub_add_cancel hge]; exact Nat.mod_eq_of_lt hlt
      · rw [UInt64.le_iff_toNat_le, toNat_small hlt, show (8 : Word).toNat = 8 from rfl]; omega
    by_cases hemp : rest = []
    · subst hemp
      have hdx0 : s.core.readReg .rdx = 0 := UInt64.toNat_inj.mp hdx
      have h0 : Condition.holds .eq .w64 (s.core.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = true := by
        rw [hdx0]; decide
      obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 18) (j := 0) (by decide) (by rw [PB.block_write]; rfl)
        (by rw [PB.block_write]) s.core s.flags h0
      have e1' : ByteEval.run ce.bytes fetchBase 2 s = .ok ⟨s.core, paddr ce 21 0, f1⟩ := by
        rw [show s = ⟨s.core, paddr ce 18 0, s.flags⟩ from by rw [← hrip]]; exact e1
      rcases TraceN.through e1' ht with rfl | ⟨hn1, ht1⟩
      · exact ⟨true, _, .done, List.nil_prefix⟩
      have eret := pstep_ret ce (b := 21) (by decide) (by rw [PB.block_writeRet])
        (s := ⟨s.core, paddr ce 21 0, f1⟩) (by rw [PB.block_writeRet]; rfl)
      cases hr64 : s.core.memory.read64? (s.core.readReg .rsp) with
      | error f =>
        rw [hr64] at eret
        have := TraceN.nil_of_step_fault eret ht1
        subst this
        exact ⟨true, _, .done, List.nil_prefix⟩
      | ok target =>
        rw [hr64] at eret
        have htgt : target = retAddr := by
          rw [read64?_value hr64, hrsp, hret]
        subst htgt
        rcases TraceN.through (run_one eret) ht1 with rfl | ⟨hn2, ht2⟩
        · exact ⟨true, _, .done, List.nil_prefix⟩
        have hdone := hcont (s.core.setReg .rsp (s.core.readReg .rsp + 8)) f1 (n - 2 - 1) σ
          (by omega) rfl (by show s.core.readReg .rsp + 8 = _; rw [hrsp, htop8])
          rfl ht2
        exact ⟨true, _, .done, hdone⟩
    · have hdxNe : s.core.readReg .rdx ≠ 0 := by
        intro h0
        have : rest.length = 0 := by rw [← hdx, h0]; rfl
        exact hemp (List.eq_nil_of_length_eq_zero this)
      have hcond : Condition.holds .eq .w64 (s.core.readReg .rdx) (signExtend32 (UInt32.ofNat 0)) = false := by
        have hz : signExtend32 (UInt32.ofNat 0) = 0 := by decide
        rw [hz, pholds_eq]
        simpa using hdxNe
      obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 18) (j := 0) (by decide) (by rw [PB.block_write]; rfl)
        (by rw [PB.block_write]) s.core s.flags hcond
      have e1' : ByteEval.run ce.bytes fetchBase 3 s = .ok ⟨s.core, paddr ce 19 0, f1⟩ := by
        rw [show s = ⟨s.core, paddr ce 18 0, s.flags⟩ from by rw [← hrip]]; exact e1
      rcases TraceN.through e1' ht with rfl | ⟨hn1, ht1⟩
      · exact writeSeq_nil fd status rest
      -- block 19: mov rax, 1; syscall
      have e2 := pstep_movI ce (b := 19) (j := 0) (by decide) (r := .rax) (v := 1)
        (by rw [PB.block_writeSys]; rfl) s.core f1
      let k1 := s.core.setReg .rax (UInt64.ofNat 1)
      rcases TraceN.through (run_one e2) ht1 with rfl | ⟨hn2, ht2⟩
      · exact writeSeq_nil fd status rest
      obtain ⟨hd, hb, hnext⟩ := psyscall_at ce (b := 19) (j := 1) (by decide)
        (by rw [PB.block_writeSys]; rfl) (s := ⟨k1, paddr ce 19 1, f1⟩) rfl
      rcases TraceN.write (s := ⟨k1, paddr ce 19 1, f1⟩) hd hb rfl ht2 with
        rfl | ⟨r, rcx, r11, fl2, σ2, rfl, hrcount, hn3, ht3⟩
      · exact writeSeq_nil fd status rest
      have hdi1 : k1.readReg .rdi = fd := hdi
      have hsi1 : k1.readReg .rsi = s.core.readReg .rsi := rfl
      have hdx1 : k1.readReg .rdx = s.core.readReg .rdx := rfl
      have hmem1 : k1.memory = s.core.memory := rfl
      have hslice1 : slice k1.memory (k1.readReg .rsi) (k1.readReg .rdx).toNat = rest := by
        rw [hmem1, hsi1, hdx1, hdx, hbytes]
      rw [hdi1, hslice1]
      let s3 := returned ⟨k1, paddr ce 19 1, f1⟩ r rcx r11 fl2
      have hs3rip : s3.rip = paddr ce 19 2 := hnext
      have hs3ax : s3.core.readReg .rax = r := rfl
      have hs3dx : s3.core.readReg .rdx = s.core.readReg .rdx := rfl
      have hs3si : s3.core.readReg .rsi = s.core.readReg .rsi := rfl
      have hs3di : s3.core.readReg .rdi = fd := hdi
      have hs3sp : s3.core.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 := hrsp
      have hs3r15 : s3.core.readReg .r15 = s.core.readReg .r15 := rfl
      have hs3mem : s3.core.memory = s.core.memory := rfl
      -- cmp rax, 0; jle writeErr
      by_cases hbad : r.toNat = 0 ∨ 2 ^ 63 ≤ r.toNat
      · have hle : Condition.holds .signedLe .w64 (s3.core.readReg .rax) (signExtend32 (UInt32.ofNat 0)) = true := by
          rw [hs3ax, signedLe_zero]; exact decide_eq_true hbad
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 19) (j := 2) (by decide) (by rw [PB.block_writeSys]; rfl)
          (by rw [PB.block_writeSys]) s3.core s3.flags hle
        have e3' : ByteEval.run ce.bytes fetchBase 2 s3 = .ok ⟨s3.core, paddr ce 22 0, f3⟩ := by
          rw [show s3 = ⟨s3.core, paddr ce 19 2, s3.flags⟩ from by rw [← hs3rip]]; exact e3
        rcases TraceN.through e3' ht3 with rfl | ⟨-, ht4⟩
        · exact ⟨false, _, .refused hemp (by rcases hbad with h | h; exact .inl h; exact .inr (.inl h)),
            ⟨[_], rfl⟩⟩
        have hex := plain_writeErr_path ce (s := ⟨s3.core, paddr ce 22 0, f3⟩) rfl ht4
        exact ⟨false, _, .refused hemp (by rcases hbad with h | h; exact .inl h; exact .inr (.inl h)),
          List.cons_prefix_cons.mpr ⟨rfl, hex⟩⟩
      · have hpos : 0 < r.toNat := by omega
        have hlt63 : r.toNat < 2 ^ 63 := by omega
        have hle_false : Condition.holds .signedLe .w64 (s3.core.readReg .rax) (signExtend32 (UInt32.ofNat 0)) = false := by
          rw [hs3ax, signedLe_zero]; exact decide_eq_false hbad
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 19) (j := 2) (by decide) (by rw [PB.block_writeSys]; rfl)
          (by rw [PB.block_writeSys]) s3.core s3.flags hle_false
        have e3' : ByteEval.run ce.bytes fetchBase 3 s3 = .ok ⟨s3.core, paddr ce 20 0, f3⟩ := by
          rw [show s3 = ⟨s3.core, paddr ce 19 2, s3.flags⟩ from by rw [← hs3rip]]; exact e3
        rcases TraceN.through e3' ht3 with rfl | ⟨hn4, ht4⟩
        · have hle_r : r.toNat ≤ rest.length := by
            have := hrcount hlt63; rw [hdx1, hdx] at this; exact this
          obtain ⟨ok, full', hw', hp'⟩ := writeSeq_nil fd status (rest.drop r.toNat)
          exact ⟨ok, _, .step hemp hpos hle_r hw', List.cons_prefix_cons.mpr ⟨rfl, hp'⟩⟩
        -- block 20: cmp rax, rdx; ja writeErr else writeStep (block 47)
        have hle_r : r.toNat ≤ rest.length := by
          have := hrcount hlt63; rw [hdx1, hdx] at this; exact this
        have hgt_false : Condition.holds .unsignedGt .w64 (s3.core.readReg .rax) (s3.core.readReg .rdx) = false := by
          rw [hs3ax, hs3dx, pholds_unsignedGt, hdx]
          exact decide_eq_false (by omega)
        obtain ⟨f4, e4⟩ := prun_cmpR ce (b := 20) (j := 0) (by decide) (by rw [PB.block_writeAdv]; rfl)
          (by rw [PB.block_writeAdv]) s3.core f3 hgt_false
        rcases TraceN.through e4 ht4 with rfl | ⟨hn5, ht5⟩
        · obtain ⟨ok, full', hw', hp'⟩ := writeSeq_nil fd status (rest.drop r.toNat)
          exact ⟨ok, _, .step hemp hpos hle_r hw', List.cons_prefix_cons.mpr ⟨rfl, hp'⟩⟩
        -- block 47: add rsi, rax; sub rdx, rax; jmp write (18)
        obtain ⟨f5, e5⟩ := pstep_alu ce (b := 47) (j := 0) (by decide)
          (by rw [PB.block_writeStep]; rfl) s3.core f4
        let k5 := s3.core.writeReg .w64 .rsi (AluOp.add.eval (s3.core.readReg .rsi) (s3.core.readReg .rax))
        obtain ⟨f6, e6⟩ := pstep_alu ce (b := 47) (j := 1) (by decide)
          (by rw [PB.block_writeStep]; rfl) k5 f5
        let k6 := k5.writeReg .w64 .rdx (AluOp.sub.eval (k5.readReg .rdx) (k5.readReg .rax))
        have e7 := pstep_jump ce (b := 47) (by decide) (t := UInt32.ofNat 18)
          (by rw [PB.block_writeStep]) (s := ⟨k6, paddr ce 47 2, f6⟩) (by rw [PB.block_writeStep]; rfl)
        rcases TraceN.through (run_comp (run_one e5) (run_comp (run_one e6) (run_one e7))) ht5 with
          rfl | ⟨hn6, ht6⟩
        · obtain ⟨ok, full', hw', hp'⟩ := writeSeq_nil fd status (rest.drop r.toNat)
          exact ⟨ok, _, .step hemp hpos hle_r hw', List.cons_prefix_cons.mpr ⟨rfl, hp'⟩⟩
        have hk6_si : k6.readReg .rsi = s.core.readReg .rsi + UInt64.ofNat r.toNat := by
          simp only [k6, k5, Core.writeReg, Core.readReg, Core.setReg, Registers.set,
            AluOp.eval, UInt64.ofNat_toNat]
          rfl
        have hk6_dx : (k6.readReg .rdx).toNat = (rest.drop r.toNat).length := by
          have hsub : k6.readReg .rdx = s.core.readReg .rdx - r := by
            simp only [k6, k5, Core.writeReg, Core.readReg, Core.setReg, Registers.set,
              AluOp.eval]
            rfl
          rw [hsub, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hdx]; exact hle_r), hdx,
            List.length_drop]
        have hk6_mem : k6.memory = s.core.memory := hs3mem
        have hk6_slice : slice k6.memory (k6.readReg .rsi) (rest.drop r.toNat).length = rest.drop r.toNat := by
          rw [hk6_mem, hk6_si, List.length_drop]
          exact slice_drop hbytes r.toNat
        have hk6_di : k6.readReg .rdi = fd := hs3di
        have hk6_sp : k6.readReg .rsp = UInt64.ofNat input.layout.shellTop - 8 := hs3sp
        have hk6_r15 : k6.readReg .r15 = s.core.readReg .r15 := hs3r15
        have hlt_n : n - 3 - 1 - 1 - 3 - 3 - 3 < n := by omega
        obtain ⟨ok, full', hw', hp'⟩ := ih (n - 3 - 1 - 1 - 3 - 3 - 3) hlt_n
          (s := ⟨k6, paddr ce 18 0, f6⟩) rfl hk6_di hk6_dx hk6_slice hk6_sp
          (by rw [hk6_mem]; exact hret)
          (fun c' fl' n' σ' hn' hm' hsp' hr15' ht' =>
            hcont c' fl' n' σ' (by omega) (by rw [hm', hk6_mem]) hsp' (by rw [hr15', hk6_r15]) ht')
          ht6
        exact ⟨ok, _, .step hemp hpos hle_r hw', List.cons_prefix_cons.mpr ⟨rfl, hp'⟩⟩

/-! ## Failure report (`B.message m` → `B.report`) -/

/-- From `B.message m` (with file bytes intact), every trace is a `ReportsMsg input.arity m`. -/
theorem plain_report_path (m : Message) {core : Core} {fl : ByteEval.Flags}
    (hfile : ∀ i < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce (B.message m) 0, fl⟩ σ) :
    ReportsMsg input.arity m σ := by
  let D := fileBase + ce.plan.placement.dataOffset
  let a := (messageAt input.arity D m).1
  let len := (messageAt input.arity D m).2
  have hbm : B.message m < 48 := message_lt m
  have e1 := pstep_movI ce hbm (j := 0) (r := .rsi) (v := a) (by rw [PB.block_message]; rfl) core fl
  let k1 := core.setReg .rsi (UInt64.ofNat a)
  have e2 := pstep_movI ce hbm (j := 1) (r := .rdx) (v := len) (by rw [PB.block_message]; rfl) k1 fl
  let k2 := k1.setReg .rdx (UInt64.ofNat len)
  have e3 := pstep_movI ce hbm (j := 2) (r := .r15) (v := m.status) (by rw [PB.block_message]; rfl) k2 fl
  let k3 := k2.setReg .r15 (UInt64.ofNat m.status)
  have e4 := pstep_jump ce hbm (t := UInt32.ofNat 37) (by rw [PB.block_message])
    (s := ⟨k3, paddr ce (B.message m) 3, fl⟩) (by rw [PB.block_message]; rfl)
  -- block 37: mov rsp, shellTop; mov rdi, 2; call write (18)
  have e5 := pstep_movI ce (b := 37) (j := 0) (by decide) (r := .rsp) (v := input.layout.shellTop)
    (by rw [PB.block_report]; rfl) k3 fl
  let k4 := k3.setReg .rsp (UInt64.ofNat input.layout.shellTop)
  have e6 := pstep_movI ce (b := 37) (j := 1) (by decide) (r := .rdi) (v := 2)
    (by rw [PB.block_report]; rfl) k4 fl
  let k5 := k4.setReg .rdi (UInt64.ofNat 2)
  have hrun := run_comp (run_one e1) (run_comp (run_one e2) (run_comp (run_one e3)
    (run_comp (run_one e4) (run_comp (run_one e5) (run_one e6)))))
  rcases TraceN.through hrun ht with rfl | ⟨hn1, ht1⟩
  · exact writeSeq_nil 2 m.status ((m.text input.arity).toUTF8.toList)
  have ecall := pstep_call ce (b := 37) (j := 2) (by decide) (t := UInt32.ofNat 18)
    (by rw [PB.block_report]; rfl) (s := ⟨k5, paddr ce 37 2, fl⟩) rfl
  cases hw : k5.memory.write64? (k5.readReg .rsp - 8) (paddr ce 37 3) with
  | error f =>
    rw [hw] at ecall
    have := TraceN.nil_of_step_fault ecall ht1
    subst this
    exact writeSeq_nil 2 m.status ((m.text input.arity).toUTF8.toList)
  | ok mem' =>
    rw [hw] at ecall
    rcases TraceN.through (run_one ecall) ht1 with rfl | ⟨hn2, ht2⟩
    · exact writeSeq_nil 2 m.status ((m.text input.arity).toUTF8.toList)
    have hmemEq : mem' = core.memory.write .w64 (UInt64.ofNat input.layout.shellTop - 8) (paddr ce 37 3) :=
      write?_ok hw
    -- file bytes lie strictly below dataBase, whereas shellTop - 8 >= dataBase
    have hfile' : ∀ i < ce.bytes.size, mem'.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]! := by
      intro i hi
      rw [hmemEq]
      have hff := plainFileFacts ce
      have hL := plainLayout_numbers ce
      have hd : dataBase = 268435456 := rfl
      have hfb : fileBase = 4194304 := rfl
      rw [write_bytes_apart]
      · exact hfile i hi
      · intro j hj heq
        simp [Width.bytes] at hj
        have h1 : (UInt64.ofNat (fileBase + i)).toNat = fileBase + i := toNat_small (by have := hff.below; rw [hff.size] at hi; omega)
        have h2 : (UInt64.ofNat input.layout.shellTop - 8 + UInt64.ofNat j).toNat =
            input.layout.shellTop - 8 + j := by
          have hsub : (UInt64.ofNat input.layout.shellTop - 8).toNat = input.layout.shellTop - 8 := by
            rw [UInt64.toNat_sub_of_le]
            · rw [toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]
            · rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]; omega
          rw [toNat_add_small _ j (by omega), hsub]
        have h3 := congrArg UInt64.toNat heq
        rw [h1, h2] at h3
        have := hff.below
        rw [hff.size] at hi
        omega
    have hdx_len : (UInt64.ofNat len).toNat = ((m.text input.arity).toUTF8.toList).length := by
      rw [toNat_small (plain_message_length_lt ce m), text_length]; rfl
    have hslice := plain_message_slice ce m hfile'
    have hretW : mem'.read64 (UInt64.ofNat input.layout.shellTop - 8) = paddr ce 37 3 := by
      rw [hmemEq]; exact write_read64_same _ _ _
    exact plain_write_loop ce (n - 6 - 1) (fd := 2) (status := m.status) (retAddr := paddr ce 37 3)
      (rest := (m.text input.arity).toUTF8.toList)
      (s := ⟨{ k5.setReg .rsp (UInt64.ofNat input.layout.shellTop - 8) with memory := mem' }, paddr ce 18 0, fl⟩)
      rfl rfl hdx_len (by rw [text_length]; exact hslice) rfl hretW
      (fun c' fl' n' σ' _ _ _ hr15' ht' => by
        -- block 37 instr 3: mov rdi, r15; jmp exit (17)
        have ea := pstep_movR ce (b := 37) (j := 3) (by decide) (d := .rdi) (s := .r15)
          (by rw [PB.block_report]; rfl) c' fl'
        have eb := pstep_jump ce (b := 37) (by decide) (t := UInt32.ofNat 17)
          (by rw [PB.block_report]) (s := ⟨c'.setReg .rdi (c'.readReg .r15), paddr ce 37 4, fl'⟩)
          (by rw [PB.block_report]; rfl)
        rcases TraceN.through (run_comp (run_one ea) (run_one eb)) ht' with rfl | ⟨-, ht''⟩
        · exact List.nil_prefix
        · have hr15'' : c'.readReg .r15 = UInt64.ofNat m.status := hr15'
          have hx := plain_exit_path ce (s := ⟨c'.setReg .rdi (c'.readReg .r15), paddr ce 17 0, fl'⟩) rfl ht''
          rw [show (c'.setReg .rdi (c'.readReg .r15)).readReg .rdi = UInt64.ofNat m.status from hr15''] at hx
          exact hx)
      ht2

/-! ## Fail dispatch (blocks 33–36) -/

/-- `B.fail` (block 33) maps nonzero `rax` status codes to their message blocks:
`1 ↦ .heap`, `2 ↦ .stack`, `3 ↦ .natOverflow`, `4 ↦ .trap`, any other `↦ .abi`. -/
def failMessage (status : Word) : Message :=
  if status == 1 then .heap
  else if status == 2 then .stack
  else if status == 3 then .natOverflow
  else if status == 4 then .trap
  else .abi

theorem plain_fail_path {core : Core} {fl : ByteEval.Flags}
    (hfile : ∀ i < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 33 0, fl⟩ σ) :
    ReportsMsg input.arity (failMessage (core.readReg .rax)) σ := by
  let v := core.readReg .rax
  by_cases h1 : v = 1
  · have hm : failMessage v = .heap := by rw [h1]; rfl
    rw [hm]
    have hc : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 1)) = true := by
      rw [h1]; decide
    obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 33) (j := 0) (by decide) (by rw [PB.block_fail]; rfl)
      (by rw [PB.block_fail]) core fl hc
    rcases TraceN.through e1 ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 2 Message.heap.status ((Message.heap.text input.arity).toUTF8.toList)
    exact plain_report_path ce .heap hfile ht1
  · have hc1 : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 1)) = false := by
      rw [show signExtend32 (UInt32.ofNat 1) = 1 by decide, pholds_eq]
      simpa using h1
    obtain ⟨f1, e1⟩ := prun_cmpI ce (b := 33) (j := 0) (by decide) (by rw [PB.block_fail]; rfl)
      (by rw [PB.block_fail]) core fl hc1
    rcases TraceN.through e1 ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 2 _ _
    by_cases h2 : v = 2
    · have hm : failMessage v = .stack := by rw [h2]; rfl
      rw [hm]
      have hc : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 2)) = true := by
        rw [h2]; decide
      obtain ⟨f2, e2⟩ := prun_cmpI ce (b := 34) (j := 0) (by decide) (by rw [PB.block_fail2]; rfl)
        (by rw [PB.block_fail2]) core f1 hc
      rcases TraceN.through e2 ht1 with rfl | ⟨-, ht2⟩
      · exact writeSeq_nil 2 _ _
      exact plain_report_path ce .stack hfile ht2
    · have hc2 : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 2)) = false := by
        rw [show signExtend32 (UInt32.ofNat 2) = 2 by decide, pholds_eq]
        simpa using h2
      obtain ⟨f2, e2⟩ := prun_cmpI ce (b := 34) (j := 0) (by decide) (by rw [PB.block_fail2]; rfl)
        (by rw [PB.block_fail2]) core f1 hc2
      rcases TraceN.through e2 ht1 with rfl | ⟨-, ht2⟩
      · exact writeSeq_nil 2 _ _
      by_cases h3 : v = 3
      · have hm : failMessage v = .natOverflow := by rw [h3]; rfl
        rw [hm]
        have hc : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 3)) = true := by
          rw [h3]; decide
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 35) (j := 0) (by decide) (by rw [PB.block_fail3]; rfl)
          (by rw [PB.block_fail3]) core f2 hc
        rcases TraceN.through e3 ht2 with rfl | ⟨-, ht3⟩
        · exact writeSeq_nil 2 _ _
        exact plain_report_path ce .natOverflow hfile ht3
      · have hc3 : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 3)) = false := by
          rw [show signExtend32 (UInt32.ofNat 3) = 3 by decide, pholds_eq]
          simpa using h3
        obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 35) (j := 0) (by decide) (by rw [PB.block_fail3]; rfl)
          (by rw [PB.block_fail3]) core f2 hc3
        rcases TraceN.through e3 ht2 with rfl | ⟨-, ht3⟩
        · exact writeSeq_nil 2 _ _
        by_cases h4 : v = 4
        · have hm : failMessage v = .trap := by rw [h4]; rfl
          rw [hm]
          have hc : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 4)) = true := by
            rw [h4]; decide
          obtain ⟨f4, e4⟩ := prun_cmpI ce (b := 36) (j := 0) (by decide) (by rw [PB.block_fail4]; rfl)
            (by rw [PB.block_fail4]) core f3 hc
          rcases TraceN.through e4 ht3 with rfl | ⟨-, ht4⟩
          · exact writeSeq_nil 2 _ _
          exact plain_report_path ce .trap hfile ht4
        · have hm : failMessage v = .abi := by simp [failMessage, h1, h2, h3, h4]
          rw [hm]
          have hc4 : Condition.holds .eq .w64 v (signExtend32 (UInt32.ofNat 4)) = false := by
            rw [show signExtend32 (UInt32.ofNat 4) = 4 by decide, pholds_eq]
            simpa using h4
          obtain ⟨f4, e4⟩ := prun_cmpI ce (b := 36) (j := 0) (by decide) (by rw [PB.block_fail4]; rfl)
            (by rw [PB.block_fail4]) core f3 hc4
          rcases TraceN.through e4 ht3 with rfl | ⟨-, ht4⟩
          · exact writeSeq_nil 2 _ _
          exact plain_report_path ce .abi hfile ht4

/-! ## Result rendering & stdout output (blocks 12–16) -/

private theorem write8_slice_cons {mem : Memory} {pos : Word} {rest : List UInt8} {b : Word}
    (hpos : pos.toNat ≥ 1) (hhi : pos.toNat + rest.length < 2 ^ 64)
    (hslice : slice mem pos rest.length = rest) :
    slice (mem.write .w8 (pos - 1) b) (pos - 1) (rest.length + 1) =
      UInt8.ofNat b.toNat :: rest := by
  have hsub : (pos - 1).toNat = pos.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hpos)]
    rfl
  apply List.ext_getElem
  · simp [slice_length]
  · intro i h1 h2
    simp only [slice, List.getElem_map, List.getElem_range]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      show (mem.writeLittle (pos - 1) b 1).bytes (pos - 1 + UInt64.ofNat 0) = UInt8.ofNat b.toNat
      rw [Memory.writeLittle_bytes _ _ _ (by decide) (by decide), byte_of]
    | succ i' =>
      simp only [List.getElem_cons_succ]
      have hne : pos - 1 + UInt64.ofNat (i' + 1) ≠ pos - 1 := by
        intro heq
        have h1' := congrArg UInt64.toNat heq
        rw [toNat_add_small _ (i' + 1) (by rw [slice_length] at h1; omega), hsub] at h1'
        omega
      have hne' : ∀ j < Width.w8.bytes, pos - 1 + UInt64.ofNat (i' + 1) ≠ (pos - 1) + UInt64.ofNat j := by
        intro j hj
        have hj0 : j = 0 := by simp [Width.bytes] at hj; omega
        subst hj0
        simpa using hne
      rw [write_bytes_apart hne']
      have haddr : pos - 1 + UInt64.ofNat (i' + 1) = pos + UInt64.ofNat i' := by
        apply UInt64.toNat_inj.mp
        rw [toNat_add_small _ (i' + 1) (by rw [slice_length] at h1; omega),
            toNat_add_small _ i' (by rw [slice_length] at h1; omega), hsub]
        omega
      rw [haddr]
      have hget := congrArg (fun l => l[i']?) hslice
      have hi' : i' < rest.length := by rw [slice_length] at h1; omega
      simp only [slice, List.getElem?_map, List.getElem?_range, hi',
        List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at hget
      exact hget

private theorem slice_write64_apart (ce : Certified input) {mem : Memory} {pos : Nat} {val : Word}
    (hlo : 40 ≤ pos) (hhi : pos ≤ 103) :
    slice (mem.write .w64 (UInt64.ofNat input.layout.shellTop - 8) val)
      (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) =
    slice mem (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  apply List.ext_getElem
  · simp [slice_length]
  · intro i h1 h2
    simp only [slice, List.getElem_map, List.getElem_range]
    rw [write_bytes_apart]
    intro j hj heq
    have h1' : (UInt64.ofNat (input.layout.stackTop + pos) + UInt64.ofNat i).toNat =
        input.layout.stackTop + pos + i := by
      rw [← UInt64.ofNat_add, toNat_small (by rw [slice_length] at h1; omega)]
    have h2' : (UInt64.ofNat input.layout.shellTop - 8 + UInt64.ofNat j).toNat =
        input.layout.shellTop - 8 + j := by
      have hsub : (UInt64.ofNat input.layout.shellTop - 8).toNat = input.layout.shellTop - 8 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (8 : Word).toNat = 8 from rfl]; omega),
          toNat_small (by omega)]; rfl
      rw [toNat_add_small _ j (by simp [Width.bytes] at hj; omega), hsub]
    have h3 := congrArg UInt64.toNat heq
    rw [h1', h2'] at h3
    rw [slice_length] at h1
    omega

/-- Shared call-to-`write` + `exit 0` tail for block 16 (`B.output`) for both `.nat` and `.enum k`.
Taking `k : Core` as a parameter keeps the `Core.setReg` chain abstract in the kernel. -/
private theorem plain_output_call_write {kind : ResultKind} {v : Nat} {j : Nat}
    {k : Core} {fl : ByteEval.Flags} {pos : Nat}
    (hcall : (blockAt (plainShellOf ce) 16).instructions[j]? = some (.instr (.call (UInt32.ofNat 18))))
    (hmov0 : (blockAt (plainShellOf ce) 16).instructions[j + 1]? = some (SB.mI .rdi 0))
    (hsz : (blockAt (plainShellOf ce) 16).instructions.size = j + 2)
    (hjmp : (blockAt (plainShellOf ce) 16).terminator = SB.jmp 17)
    (hdi : k.readReg .rdi = 1)
    (hrsp : k.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    (hsi : k.readReg .rsi = UInt64.ofNat (input.layout.stackTop + pos))
    (hdx : (k.readReg .rdx).toNat = (renderPlain kind v).length)
    (hlo : 40 ≤ pos) (hhi : pos ≤ 103)
    (hlen : (renderPlain kind v).length = 104 - pos)
    (hslice : slice k.memory (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) = renderPlain kind v)
    {n : Nat} {σ : List Sys} (ht1 : TraceN ce.bytes n ⟨k, paddr ce 16 j, fl⟩ σ) :
    PrintsResult kind v σ := by
  have ecall := pstep_call ce (b := 16) (j := j) (by decide) (t := UInt32.ofNat 18)
    hcall (s := ⟨k, paddr ce 16 j, fl⟩) rfl
  cases hw : k.memory.write64? (k.readReg .rsp - 8) (paddr ce 16 (j + 1)) with
  | error f =>
    rw [hw] at ecall
    have := TraceN.nil_of_step_fault ecall ht1
    subst this
    exact writeSeq_nil 1 0 (renderPlain kind v)
  | ok mem' =>
    rw [hw] at ecall
    rcases TraceN.through (run_one ecall) ht1 with rfl | ⟨-, ht2⟩
    · exact writeSeq_nil 1 0 (renderPlain kind v)
    have hmemEq : mem' = k.memory.write .w64 (UInt64.ofNat input.layout.shellTop - 8) (paddr ce 16 (j + 1)) := by
      rw [hrsp] at hw; exact write?_ok hw
    have hslice' : slice mem' (k.readReg .rsi) (renderPlain kind v).length = renderPlain kind v := by
      rw [hsi, hmemEq, hlen, slice_write64_apart ce hlo hhi, hslice]
    have hretW : mem'.read64 (UInt64.ofNat input.layout.shellTop - 8) = paddr ce 16 (j + 1) := by
      rw [hmemEq]; exact write_read64_same _ _ _
    rw [hrsp] at ht2
    exact plain_write_loop ce _ (fd := 1) (status := 0) (retAddr := paddr ce 16 (j + 1))
      (rest := renderPlain kind v)
      (s := ⟨{ k.setReg .rsp (UInt64.ofNat input.layout.shellTop - 8) with memory := mem' }, paddr ce 18 0, fl⟩)
      rfl hdi hdx hslice' rfl hretW
      (fun c' fl' n' σ' _ _ _ _ ht' => by
        have ea := pstep_movI ce (b := 16) (j := j + 1) (by decide) (r := .rdi) (v := 0) hmov0 c' fl'
        have eb := pstep_jump ce (b := 16) (by decide) (t := UInt32.ofNat 17) hjmp
          (s := ⟨c'.setReg .rdi 0, paddr ce 16 (j + 2), fl'⟩) (by rw [hsz])
        rcases TraceN.through (run_comp (run_one ea) (run_one eb)) ht' with rfl | ⟨-, ht''⟩
        · exact List.nil_prefix
        · exact plain_exit_path ce (s := ⟨c'.setReg .rdi 0, paddr ce 17 0, fl'⟩) rfl ht'')
      ht2

private theorem plain_output_nat (hkind : input.result = .nat) {v : Nat}
    {core : Core} {fl : ByteEval.Flags} {pos : Nat}
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    (hsi : core.readReg .rsi = UInt64.ofNat (input.layout.stackTop + pos))
    (hlo : 41 ≤ pos) (hhi : pos ≤ 103)
    (hslice : slice core.memory (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) = natDecimal v ++ [10])
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 16 0, fl⟩ σ) :
    PrintsResult .nat v σ := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have hlenEq : (natDecimal v ++ [10]).length = 104 - pos := by
    have := congrArg List.length hslice; rw [slice_length] at this; exact this.symm
  have e1 := pstep_lea ce (b := 16) (j := 0) (by decide)
    (by rw [PB.block_output_nat _ hkind]; rfl) core fl
  let k1 := core.setReg .rdx ((SB.at_ .rbp 104).eval core)
  obtain ⟨f2, e2⟩ := pstep_alu ce (b := 16) (j := 1) (by decide)
    (by rw [PB.block_output_nat _ hkind]; rfl) k1 fl
  let k2 := k1.writeReg .w64 .rdx (AluOp.sub.eval (k1.readReg .rdx) (k1.readReg .rsi))
  have e3 := pstep_movI ce (b := 16) (j := 2) (by decide) (r := .rdi) (v := 1)
    (by rw [PB.block_output_nat _ hkind]; rfl) k2 f2
  let k3 := k2.setReg .rdi 1
  rcases TraceN.through (run_comp (run_one e1) (run_comp (run_one e2) (run_one e3))) ht with
    rfl | ⟨-, ht1⟩
  · exact writeSeq_nil 1 0 (renderPlain .nat v)
  have hdxVal : (k3.readReg .rdx).toNat = (renderPlain .nat v).length := by
    have h104 : (SB.at_ .rbp 104).eval core = UInt64.ofNat (input.layout.stackTop + 104) := by
      rw [eval_at core .rbp (by decide), hrbp, ← UInt64.ofNat_add]
    have hk2dx : k3.readReg .rdx = UInt64.ofNat (input.layout.stackTop + 104) -
        UInt64.ofNat (input.layout.stackTop + pos) := by
      change (SB.at_ .rbp 104).eval core - core.readReg .rsi = _
      rw [h104, hsi]
    rw [hk2dx, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), toNat_small (by omega)]; omega),
      toNat_small (by omega), toNat_small (by omega)]
    simp only [renderPlain]
    omega
  exact plain_output_call_write ce (kind := .nat) (v := v) (j := 3) (k := k3) (fl := f2) (pos := pos)
    (by rw [PB.block_output_nat _ hkind]; rfl)
    (by rw [PB.block_output_nat _ hkind]; rfl)
    (by rw [PB.block_output_nat _ hkind]; rfl)
    (by rw [PB.block_output_nat _ hkind])
    rfl hrsp hsi hdxVal (by omega) hhi hlenEq hslice ht1

private theorem plain_output_enum {k : Nat} (hkind : input.result = .enum k) {v : Nat}
    {core : Core} {fl : ByteEval.Flags} {pos : Nat}
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    (hsi : core.readReg .rsi = UInt64.ofNat (input.layout.stackTop + pos))
    (hlo : 41 ≤ pos) (hhi : pos ≤ 103)
    (hslice : slice core.memory (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) = natDecimal v ++ [10])
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 16 0, fl⟩ σ) :
    PrintsResult (.enum k) v σ := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have hlenEq : (natDecimal v ++ [10]).length = 104 - pos := by
    have := congrArg List.length hslice; rw [slice_length] at this; exact this.symm
  have e0 := pstep_movI ce (b := 16) (j := 0) (by decide) (r := .rdx) (v := 35)
    (by rw [PB.block_output_enum _ k hkind]; rfl) core fl
  let c0 := core.setReg .rdx (UInt64.ofNat 35)
  obtain ⟨f1, e1⟩ := pstep_alu ce (b := 16) (j := 1) (by decide)
    (by rw [PB.block_output_enum _ k hkind]; rfl) c0 fl
  let c1 := c0.writeReg .w64 .rsi (AluOp.sub.eval (c0.readReg .rsi) (signExtend32 (UInt32.ofNat 1)))
  rcases TraceN.through (run_comp (run_one e0) (run_one e1)) ht with rfl | ⟨-, ht0⟩
  · exact writeSeq_nil 1 0 (renderPlain (.enum k) v)
  rcases pstep_store8 ce (b := 16) (j := 2) (by decide)
    (by rw [PB.block_output_enum _ k hkind]; rfl) c1 f1 with
    ⟨mem0, hw0, e2⟩ | ⟨_, efault⟩
  · let c2 : Core := { c1 with memory := mem0 }
    have e3 := pstep_lea ce (b := 16) (j := 3) (by decide)
      (by rw [PB.block_output_enum _ k hkind]; rfl) c2 f1
    let c3 := c2.setReg .rdx ((SB.at_ .rbp 104).eval c2)
    obtain ⟨f4, e4⟩ := pstep_alu ce (b := 16) (j := 4) (by decide)
      (by rw [PB.block_output_enum _ k hkind]; rfl) c3 f1
    let c4 := c3.writeReg .w64 .rdx (AluOp.sub.eval (c3.readReg .rdx) (c3.readReg .rsi))
    have e5 := pstep_movI ce (b := 16) (j := 5) (by decide) (r := .rdi) (v := 1)
      (by rw [PB.block_output_enum _ k hkind]; rfl) c4 f4
    let c5 := c4.setReg .rdi 1
    rcases TraceN.through (run_comp (run_one e2) (run_comp (run_one e3) (run_comp (run_one e4) (run_one e5)))) ht0 with
      rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 1 0 (renderPlain (.enum k) v)
    have heqPos : UInt64.ofNat (input.layout.stackTop + (pos - 1)) =
        UInt64.ofNat (input.layout.stackTop + pos) - 1 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (1 : Word).toNat = 1 from rfl]; omega),
        toNat_small (by omega), toNat_small (by omega)]
      show input.layout.stackTop + (pos - 1) = input.layout.stackTop + pos - 1; omega
    have hsi1 : c1.readReg .rsi = UInt64.ofNat (input.layout.stackTop + (pos - 1)) := by
      change core.readReg .rsi - signExtend32 (UInt32.ofNat 1) = _
      rw [hsi, show signExtend32 (UInt32.ofNat 1) = 1 by decide, heqPos]
    have hmem0Eq : mem0 = core.memory.write .w8 (UInt64.ofNat (input.layout.stackTop + pos) - 1) (UInt64.ofNat 35) := by
      have heval : (SB.at_ .rsi).eval c1 = UInt64.ofNat (input.layout.stackTop + pos) - 1 := by
        rw [eval_at c1 .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hsi1, heqPos]
      rw [heval] at hw0
      exact write?_ok hw0
    have hslice0 : slice mem0 (UInt64.ofNat (input.layout.stackTop + (pos - 1))) (104 - (pos - 1)) =
        renderPlain (.enum k) v := by
      rw [hmem0Eq, heqPos, show 104 - (pos - 1) = (104 - pos) + 1 by omega]
      have hws := write8_slice_cons (mem := core.memory) (pos := UInt64.ofNat (input.layout.stackTop + pos))
        (rest := natDecimal v ++ [10]) (b := UInt64.ofNat 35)
        (by rw [toNat_small (by omega)]; omega)
        (by rw [toNat_small (by omega), hlenEq]; omega)
        (by rw [hlenEq]; exact hslice)
      rw [hlenEq] at hws
      exact hws
    have hdxVal : (c5.readReg .rdx).toNat = (renderPlain (.enum k) v).length := by
      have h104 : (SB.at_ .rbp 104).eval c2 = UInt64.ofNat (input.layout.stackTop + 104) := by
        have hbp2 : c2.readReg .rbp = UInt64.ofNat input.layout.stackTop := hrbp
        rw [eval_at c2 .rbp (by decide), hbp2, ← UInt64.ofNat_add]
      have hc5dx : c5.readReg .rdx = UInt64.ofNat (input.layout.stackTop + 104) -
          UInt64.ofNat (input.layout.stackTop + (pos - 1)) := by
        change (SB.at_ .rbp 104).eval c2 - c1.readReg .rsi = _
        rw [h104, hsi1]
      rw [hc5dx, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), toNat_small (by omega)]; omega),
        toNat_small (by omega), toNat_small (by omega)]
      simp only [renderPlain, List.cons_append, List.length_cons]
      have : (natDecimal v).length + 1 = 104 - pos := by simpa using hlenEq
      omega
    have hrlen : (renderPlain (.enum k) v).length = 104 - (pos - 1) := by
      simp only [renderPlain, List.cons_append, List.length_cons]
      have : (natDecimal v).length + 1 = 104 - pos := by simpa using hlenEq
      omega
    exact plain_output_call_write ce (kind := .enum k) (v := v) (j := 6) (k := c5) (fl := f4) (pos := pos - 1)
      (by rw [PB.block_output_enum _ k hkind]; rfl)
      (by rw [PB.block_output_enum _ k hkind]; rfl)
      (by rw [PB.block_output_enum _ k hkind]; rfl)
      (by rw [PB.block_output_enum _ k hkind])
      rfl hrsp hsi1 hdxVal (by omega) (by omega) hrlen hslice0 ht1
  · have := TraceN.nil_of_step_fault efault ht0
    subst this
    exact writeSeq_nil 1 0 (renderPlain (.enum k) v)

/-- `B.output` (block 16): optionally prepends `'#'` for `.enum _`, calls `B.write`
with `fd = 1`, and exits `0`. -/
private theorem plain_output_path {kind : ResultKind} (hkind : input.result = kind) {v : Nat}
    {core : Core} {fl : ByteEval.Flags} {pos : Nat}
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    (hsi : core.readReg .rsi = UInt64.ofNat (input.layout.stackTop + pos))
    (hlo : 41 ≤ pos) (hhi : pos ≤ 103)
    (hslice : slice core.memory (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) = natDecimal v ++ [10])
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 16 0, fl⟩ σ) :
    PrintsResult kind v σ := by
  cases kind with
  | nat => exact plain_output_nat ce hkind hrbp hrsp hsi hlo hhi hslice ht
  | enum k => exact plain_output_enum ce hkind hrbp hrsp hsi hlo hhi hslice ht

/-- `B.digit` loop (block 15): renders `m` right-to-left into `[rbp+41 .. rbp+pos)`
before existing suffix `suf` at `[rbp+pos .. rbp+104)`, then jumps to `B.output`. -/
private theorem plain_digit_loop {kind : ResultKind} (hkind : input.result = kind) {v : Nat} :
    ∀ (m : Nat) {pos : Nat} {suf : List UInt8} {core : Core} {fl : ByteEval.Flags} {n : Nat} {σ : List Sys},
      core.readReg .rax = UInt64.ofNat m →
      m < 2 ^ 63 →
      natDecimal m ++ suf = natDecimal v ++ [10] →
      core.readReg .rbp = UInt64.ofNat input.layout.stackTop →
      core.readReg .rsp = UInt64.ofNat input.layout.shellTop →
      core.readReg .rsi = UInt64.ofNat (input.layout.stackTop + pos) →
      41 + (natDecimal m).length ≤ pos →
      pos ≤ 103 →
      slice core.memory (UInt64.ofNat (input.layout.stackTop + pos)) (104 - pos) = suf →
      TraceN ce.bytes n ⟨core, paddr ce 15 0, fl⟩ σ →
      PrintsResult kind v σ := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro pos suf core fl n σ hax hm hdec hrbp hrsp hsi hlo hhi hslice ht
    have hL := plainLayout_numbers ce
    have hd : dataBase = 268435456 := rfl
    -- block 15: mov rdx, 0; mov rcx, 10; div rcx; add rdx, 48; sub rsi, 1; st8 [rsi], rdx; test rax, rax
    have e0 := pstep_movI ce (b := 15) (j := 0) (by decide) (r := .rdx) (v := 0)
      (by rw [PB.block_digit]; rfl) core fl
    let c0 := core.setReg .rdx 0
    have e1 := pstep_movI ce (b := 15) (j := 1) (by decide) (r := .rcx) (v := 10)
      (by rw [PB.block_digit]; rfl) c0 fl
    let c1 := c0.setReg .rcx 10
    have hdivArg : 0 < (c1.readReg .rcx).toNat := by change 0 < (10 : Word).toNat; decide
    obtain ⟨f2, e2⟩ := pstep_div64 ce (b := 15) (j := 2) (by decide) (by rw [PB.block_digit]; rfl) c1 fl rfl hdivArg
    let c2 := (c1.setReg .rax (UInt64.ofNat ((c1.readReg .rax).toNat / (c1.readReg .rcx).toNat))).setReg
      .rdx (UInt64.ofNat ((c1.readReg .rax).toNat % (c1.readReg .rcx).toNat))
    obtain ⟨f3, e3⟩ := pstep_alu ce (b := 15) (j := 3) (by decide) (by rw [PB.block_digit]; rfl) c2 f2
    let c3 := c2.writeReg .w64 .rdx (AluOp.add.eval (c2.readReg .rdx) (signExtend32 (UInt32.ofNat 48)))
    obtain ⟨f4, e4⟩ := pstep_alu ce (b := 15) (j := 4) (by decide) (by rw [PB.block_digit]; rfl) c3 f3
    let c4 := c3.writeReg .w64 .rsi (AluOp.sub.eval (c3.readReg .rsi) (signExtend32 (UInt32.ofNat 1)))
    rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1)
        (run_comp (run_one e2) (run_comp (run_one e3) (run_one e4))))) ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 1 0 (renderPlain kind v)
    rcases pstep_store8 ce (b := 15) (j := 5) (by decide) (by rw [PB.block_digit]; rfl) c4 f4 with
      ⟨mem', hw, e5⟩ | ⟨_, efault⟩
    · let c5 : Core := { c4 with memory := mem' }
      rcases TraceN.through (run_one e5) ht1 with rfl | ⟨-, ht2⟩
      · exact writeSeq_nil 1 0 (renderPlain kind v)
      have hc2ax : c5.readReg .rax = UInt64.ofNat (m / 10) := by
        change UInt64.ofNat ((core.readReg .rax).toNat / (10 : Word).toNat) = _
        rw [hax, toNat_small (by omega), show (10 : Word).toNat = 10 from rfl]
      have hc4dx : c4.readReg .rdx = UInt64.ofNat (m % 10 + 48) := by
        change UInt64.ofNat ((core.readReg .rax).toNat % (10 : Word).toNat) + signExtend32 (UInt32.ofNat 48) = _
        rw [hax, toNat_small (by omega), show (10 : Word).toNat = 10 from rfl,
          show signExtend32 (UInt32.ofNat 48) = UInt64.ofNat 48 by decide, ← UInt64.ofNat_add]
      have hc4si : c4.readReg .rsi = UInt64.ofNat (input.layout.stackTop + (pos - 1)) := by
        have hsub1 : UInt64.ofNat (input.layout.stackTop + pos) - signExtend32 (UInt32.ofNat 1) =
            UInt64.ofNat (input.layout.stackTop + (pos - 1)) := by
          rw [show signExtend32 (UInt32.ofNat 1) = 1 by decide]
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (1 : Word).toNat = 1 from rfl]; omega),
            toNat_small (by omega), toNat_small (by omega)]
          show input.layout.stackTop + pos - 1 = input.layout.stackTop + (pos - 1); omega
        change core.readReg .rsi - signExtend32 (UInt32.ofNat 1) = _
        rw [hsi]; exact hsub1
      have hsufLen : suf.length = 104 - pos := by
        have := congrArg List.length hslice; rw [slice_length] at this; exact this.symm
      have hslice' : slice mem' (UInt64.ofNat (input.layout.stackTop + (pos - 1))) (104 - (pos - 1)) =
          UInt8.ofNat (m % 10 + 48) :: suf := by
        have heqPos : UInt64.ofNat (input.layout.stackTop + (pos - 1)) =
            UInt64.ofNat (input.layout.stackTop + pos) - 1 := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_small (by omega), show (1 : Word).toNat = 1 from rfl]; omega),
            toNat_small (by omega), toNat_small (by omega)]
          show input.layout.stackTop + (pos - 1) = input.layout.stackTop + pos - 1; omega
        have heval : (SB.at_ .rsi).eval c4 = UInt64.ofNat (input.layout.stackTop + pos) - 1 := by
          rw [eval_at c4 .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hc4si, heqPos]
        have hmemEq : mem' = core.memory.write .w8 (UInt64.ofNat (input.layout.stackTop + pos) - 1)
            (UInt64.ofNat (m % 10 + 48)) := by
          rw [heval, hc4dx] at hw; exact write?_ok hw
        rw [hmemEq, heqPos, show 104 - (pos - 1) = (104 - pos) + 1 by omega]
        have hws := write8_slice_cons (mem := core.memory) (pos := UInt64.ofNat (input.layout.stackTop + pos))
          (rest := suf) (b := UInt64.ofNat (m % 10 + 48))
          (by rw [toNat_small (by omega)]; omega)
          (by rw [toNat_small (by omega), hsufLen]; omega)
          (by rw [hsufLen]; exact hslice)
        rw [hsufLen] at hws
        rw [hws, toNat_small (by omega)]
      by_cases hq : m / 10 = 0
      · have hlt10 : m < 10 := by omega
        have hax0 : (c5.readReg .rax != 0) = false := by rw [hc2ax, hq]; rfl
        obtain ⟨f6, e6⟩ := prun_ifNz ce (b := 15) (j := 6) (by decide) (by rw [PB.block_digit]; rfl)
          (by rw [PB.block_digit]) c5 f4 hax0
        rcases TraceN.through e6 ht2 with rfl | ⟨-, ht3⟩
        · exact writeSeq_nil 1 0 (renderPlain kind v)
        have hdec' : UInt8.ofNat (m % 10 + 48) :: suf = natDecimal v ++ [10] := by
          rw [← hdec, natDecimal_lt_ten hlt10, Nat.mod_eq_of_lt hlt10]; rfl
        have hposLo : 41 ≤ pos - 1 := by
          have : (natDecimal m).length = 1 := by rw [natDecimal_lt_ten hlt10]; rfl
          omega
        exact plain_output_path ce hkind (core := c5) (pos := pos - 1)
          (by exact hrbp) (by exact hrsp) hc4si hposLo (by omega)
          (by change slice mem' _ _ = _; rw [hslice', hdec']) ht3
      · have haxNz : (c5.readReg .rax != 0) = true := by
          rw [hc2ax]
          have hne : UInt64.ofNat (m / 10) ≠ 0 := by
            intro h0
            have := congrArg UInt64.toNat h0
            rw [toNat_small (by omega)] at this
            exact hq this
          simpa using hne
        obtain ⟨f6, e6⟩ := prun_ifNz ce (b := 15) (j := 6) (by decide) (by rw [PB.block_digit]; rfl)
          (by rw [PB.block_digit]) c5 f4 haxNz
        rcases TraceN.through e6 ht2 with rfl | ⟨-, ht3⟩
        · exact writeSeq_nil 1 0 (renderPlain kind v)
        have hdec' : natDecimal (m / 10) ++ (UInt8.ofNat (m % 10 + 48) :: suf) = natDecimal v ++ [10] := by
          rw [← hdec, natDecimal_eq_step m hq, List.append_assoc]; rfl
        have hlenStep : (natDecimal m).length = (natDecimal (m / 10)).length + 1 := by
          rw [natDecimal_eq_step m hq, List.length_append, List.length_singleton]
        exact ih (m / 10) (Nat.div_lt_self (by omega) (by decide)) (pos := pos - 1)
          (suf := UInt8.ofNat (m % 10 + 48) :: suf) (core := c5)
          hc2ax (by omega) hdec' hrbp hrsp hc4si (by omega) (by omega) hslice' ht3
    · have := TraceN.nil_of_step_fault efault ht1
      subst this
      exact writeSeq_nil 1 0 (renderPlain kind v)

/-- `B.render` (block 14) → `B.digit` → `B.output`. -/
private theorem plain_render_path {kind : ResultKind} (hkind : input.result = kind) {v : Nat}
    (hv : v < 2 ^ 63) {core : Core} {fl : ByteEval.Flags}
    (hax : core.readReg .rax = UInt64.ofNat v)
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 14 0, fl⟩ σ) :
    PrintsResult kind v σ := by
  have hL := plainLayout_numbers ce
  have hd : dataBase = 268435456 := rfl
  have e0 := pstep_lea ce (b := 14) (j := 0) (by decide) (by rw [PB.block_render]; rfl) core fl
  let c0 := core.setReg .rsi ((SB.at_ .rbp 103).eval core)
  have e1 := pstep_movI ce (b := 14) (j := 1) (by decide) (r := .r8) (v := 10)
    (by rw [PB.block_render]; rfl) c0 fl
  let c1 := c0.setReg .r8 10
  rcases TraceN.through (run_comp (run_one e0) (run_one e1)) ht with rfl | ⟨-, ht0⟩
  · exact writeSeq_nil 1 0 (renderPlain kind v)
  rcases pstep_store8 ce (b := 14) (j := 2) (by decide) (by rw [PB.block_render]; rfl) c1 fl with
    ⟨mem', hw, e2⟩ | ⟨_, efault⟩
  · let c2 : Core := { c1 with memory := mem' }
    have e3 := pstep_jump ce (b := 14) (by decide) (t := UInt32.ofNat 15)
      (by rw [PB.block_render]) (s := ⟨c2, paddr ce 14 3, fl⟩) (by rw [PB.block_render]; rfl)
    rcases TraceN.through (run_comp (run_one e2) (run_one e3)) ht0 with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 1 0 (renderPlain kind v)
    have hsi : c2.readReg .rsi = UInt64.ofNat (input.layout.stackTop + 103) := by
      change (SB.at_ .rbp 103).eval core = _
      rw [eval_at core .rbp (by decide), hrbp, ← UInt64.ofNat_add]
    have hmemEq : mem' = core.memory.write .w8 (UInt64.ofNat (input.layout.stackTop + 103)) 10 := by
      have heval : (SB.at_ .rsi).eval c1 = UInt64.ofNat (input.layout.stackTop + 103) := by
        rw [eval_at c1 .rsi (by decide), show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]; exact hsi
      rw [heval] at hw; exact write?_ok hw
    have hslice : slice mem' (UInt64.ofNat (input.layout.stackTop + 103)) (104 - 103) = [10] := by
      rw [hmemEq]
      simp only [slice, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
      show [(core.memory.writeLittle (UInt64.ofNat (input.layout.stackTop + 103)) 10 1).bytes
        (UInt64.ofNat (input.layout.stackTop + 103) + UInt64.ofNat 0)] = [10]
      rw [Memory.writeLittle_bytes _ _ _ (by decide) (by decide), byte_of]
      rfl
    have ⟨_, hlen19⟩ := natDecimal_length_le v hv
    exact plain_digit_loop ce hkind (v := v) v (pos := 103) (suf := [10]) (core := c2)
      hax hv rfl hrbp hrsp hsi (by omega) (Nat.le_refl _) hslice ht1
  · have := TraceN.nil_of_step_fault efault ht0
    subst this
    exact writeSeq_nil 1 0 (renderPlain kind v)

/-- Whether the returned word `w` satisfies the plain-shell result tag check. -/
def plainResultOk (kind : ResultKind) (w : Word) : Bool :=
  (w.toNat % 2 == 1) &&
    match kind with
    | .nat => true
    | .enum k => decide (w.toNat / 2 < k)

/-- **From `B.result` (block 12)**: checks the returned word `rdx` against
`input.result` (odd tag; for `.enum n`, `< n`), rendering valid values to stdout
(`PrintsResult`) and rejecting invalid words via `ReportsMsg .notValue`. -/
theorem plain_result_path {core : Core} {fl : ByteEval.Flags}
    (hrbp : core.readReg .rbp = UInt64.ofNat input.layout.stackTop)
    (hrsp : core.readReg .rsp = UInt64.ofNat input.layout.shellTop)
    (hfile : ∀ i < ce.bytes.size, core.memory.bytes (UInt64.ofNat (fileBase + i)) = ce.bytes[i]!)
    {n : Nat} {σ : List Sys} (ht : TraceN ce.bytes n ⟨core, paddr ce 12 0, fl⟩ σ) :
    let w := core.readReg .rdx
    if plainResultOk input.result w then
      PrintsResult input.result (w.toNat / 2) σ
    else
      ReportsMsg input.arity .notValue σ := by
  let w := core.readReg .rdx
  change if plainResultOk input.result w then PrintsResult input.result (w.toNat / 2) σ
         else ReportsMsg input.arity .notValue σ
  have hwlt : w.toNat < 2 ^ 64 := w.toBitVec.isLt
  have e0 := pstep_movR ce (b := 12) (j := 0) (by decide) (d := .rax) (s := .rdx)
    (by rw [PB.block_result]; rfl) core fl
  let c0 := core.setReg .rax w
  have e1 := pstep_movR ce (b := 12) (j := 1) (by decide) (d := .rcx) (s := .rdx)
    (by rw [PB.block_result]; rfl) c0 fl
  let c1 := c0.setReg .rcx w
  obtain ⟨f2, e2⟩ := pstep_alu ce (b := 12) (j := 2) (by decide) (by rw [PB.block_result]; rfl) c1 fl
  let c2 := c1.writeReg .w32 .rcx (AluOp.and.eval (c1.readReg .rcx) (signExtend32 (UInt32.ofNat 1)))
  have hcx : (c2.readReg .rcx).toNat = w.toNat % 2 := by
    change (Width.w32.truncate (w &&& signExtend32 (UInt32.ofNat 1))).toNat = _
    exact odd_test w
  by_cases hodd : w.toNat % 2 = 1
  · have hcxNe : c2.readReg .rcx ≠ 0 := ne_of_toNat (by rw [hcx]; change w.toNat % 2 ≠ 0; omega)
    have hcond : Condition.holds .eq .w64 (c2.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = false := by
      rw [show signExtend32 (UInt32.ofNat 0) = 0 by decide, pholds_eq]
      simpa using hcxNe
    obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 12) (j := 3) (by decide) (by rw [PB.block_result]; rfl)
      (by rw [PB.block_result]) c2 f2 hcond
    -- block 13: shr rax, 1
    cases hkind : input.result with
    | nat =>
      have hok : plainResultOk .nat w = true := by simp [plainResultOk, hodd]
      rw [hok]; simp only [↓reduceIte]
      rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1)
          (run_comp (run_one e2) e3))) ht with rfl | ⟨-, ht1⟩
      · exact writeSeq_nil 1 0 (renderPlain .nat (w.toNat / 2))
      obtain ⟨f4, e4⟩ := pstep_shr ce (b := 13) (j := 0) (by decide)
        (by rw [PB.block_tag_nat _ hkind]; rfl) c2 f3
      let c3 := c2.setReg .rax ⟨(ShiftOp.shr.apply .w64 (c2.readReg .rax) (shiftCount .w64 1)).setWidth 64⟩
      have e5 := pstep_jump ce (b := 13) (by decide) (t := UInt32.ofNat 14)
        (by rw [PB.block_tag_nat _ hkind]) (s := ⟨c3, paddr ce 13 1, f4⟩)
        (by rw [PB.block_tag_nat _ hkind]; rfl)
      rcases TraceN.through (run_comp (run_one e4) (run_one e5)) ht1 with rfl | ⟨-, ht2⟩
      · exact writeSeq_nil 1 0 (renderPlain .nat (w.toNat / 2))
      have hax3 : c3.readReg .rax = UInt64.ofNat (w.toNat / 2) := by
        apply UInt64.toNat_inj.mp
        change ({ toBitVec := (ShiftOp.shr.apply .w64 w (shiftCount .w64 (UInt64.ofNat 1))).setWidth 64 } : Word).toNat = _
        rw [shr_toNat w 1 (by decide), toNat_small (by omega)]
      exact plain_render_path ce hkind (v := w.toNat / 2) (by omega) hax3 hrbp hrsp ht2
    | enum k =>
      have hff := plainFileFacts ce
      have hklt : k < 2 ^ 31 := by have hr := hff.resultOk; rw [hkind] at hr; exact hr.2
      have hseK : signExtend32 (UInt32.ofNat k) = UInt64.ofNat k := by
        have hk32 : (UInt32.ofNat k).toNat = k := UInt32.toNat_ofNat_of_lt' (by show k < 4294967296; omega)
        have hlt32 : UInt32.ofNat k < 2147483648 := by
          rw [UInt32.lt_iff_toNat_lt, hk32]; show k < 2147483648; omega
        simp only [signExtend32, hlt32, ↓reduceIte]
        apply UInt64.toNat_inj.mp
        rw [UInt32.toNat_toUInt64, hk32, toNat_small (by omega)]
      by_cases hlt : w.toNat / 2 < k
      · have hok : plainResultOk (.enum k) w = true := by simp [plainResultOk, hodd, hlt]
        rw [hok]; simp only [↓reduceIte]
        rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1)
            (run_comp (run_one e2) e3))) ht with rfl | ⟨-, ht1⟩
        · exact writeSeq_nil 1 0 (renderPlain (.enum k) (w.toNat / 2))
        obtain ⟨f4, e4⟩ := pstep_shr ce (b := 13) (j := 0) (by decide)
          (by rw [PB.block_tag_enum _ k hkind]; rfl) c2 f3
        let c3 := c2.setReg .rax ⟨(ShiftOp.shr.apply .w64 (c2.readReg .rax) (shiftCount .w64 1)).setWidth 64⟩
        have hax3 : c3.readReg .rax = UInt64.ofNat (w.toNat / 2) := by
          apply UInt64.toNat_inj.mp
          change ({ toBitVec := (ShiftOp.shr.apply .w64 w (shiftCount .w64 (UInt64.ofNat 1))).setWidth 64 } : Word).toNat = _
          rw [shr_toNat w 1 (by decide), toNat_small (by omega)]
        have hgeF : Condition.holds .unsignedGe .w64 (c3.readReg .rax) (signExtend32 (UInt32.ofNat k)) = false := by
          rw [hax3, hseK, pholds_unsignedGe, toNat_small (by omega), toNat_small (by omega)]
          exact decide_eq_false (by omega)
        obtain ⟨f5, e5⟩ := prun_cmpI ce (b := 13) (j := 1) (by decide)
          (by rw [PB.block_tag_enum _ k hkind]; rfl)
          (by rw [PB.block_tag_enum _ k hkind]) c3 f4 hgeF
        rcases TraceN.through (run_comp (run_one e4) e5) ht1 with rfl | ⟨-, ht2⟩
        · exact writeSeq_nil 1 0 (renderPlain (.enum k) (w.toNat / 2))
        exact plain_render_path ce hkind (v := w.toNat / 2) (by omega) hax3 hrbp hrsp ht2
      · have hnok : plainResultOk (.enum k) w = false := by simp [plainResultOk, hlt]
        rw [hnok]; simp only [Bool.false_eq_true, ↓reduceIte]
        rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1)
            (run_comp (run_one e2) e3))) ht with rfl | ⟨-, ht1⟩
        · exact writeSeq_nil 2 _ _
        obtain ⟨f4, e4⟩ := pstep_shr ce (b := 13) (j := 0) (by decide)
          (by rw [PB.block_tag_enum _ k hkind]; rfl) c2 f3
        let c3 := c2.setReg .rax ⟨(ShiftOp.shr.apply .w64 (c2.readReg .rax) (shiftCount .w64 1)).setWidth 64⟩
        have hax3 : c3.readReg .rax = UInt64.ofNat (w.toNat / 2) := by
          apply UInt64.toNat_inj.mp
          change ({ toBitVec := (ShiftOp.shr.apply .w64 w (shiftCount .w64 (UInt64.ofNat 1))).setWidth 64 } : Word).toNat = _
          rw [shr_toNat w 1 (by decide), toNat_small (by omega)]
        have hgeT : Condition.holds .unsignedGe .w64 (c3.readReg .rax) (signExtend32 (UInt32.ofNat k)) = true := by
          rw [hax3, hseK, pholds_unsignedGe, toNat_small (by omega), toNat_small (by omega)]
          exact decide_eq_true (by omega)
        obtain ⟨f5, e5⟩ := prun_cmpI ce (b := 13) (j := 1) (by decide)
          (by rw [PB.block_tag_enum _ k hkind]; rfl)
          (by rw [PB.block_tag_enum _ k hkind]) c3 f4 hgeT
        rcases TraceN.through (run_comp (run_one e4) e5) ht1 with rfl | ⟨-, ht2⟩
        · exact writeSeq_nil 2 _ _
        exact plain_report_path ce .notValue (core := c3) hfile ht2
  · have hnok : plainResultOk input.result w = false := by simp [plainResultOk, hodd]
    rw [hnok]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hcx0 : c2.readReg .rcx = 0 := UInt64.toNat_inj.mp (by rw [hcx]; show w.toNat % 2 = 0; omega)
    have hcond : Condition.holds .eq .w64 (c2.readReg .rcx) (signExtend32 (UInt32.ofNat 0)) = true := by
      rw [hcx0]; decide
    obtain ⟨f3, e3⟩ := prun_cmpI ce (b := 12) (j := 3) (by decide) (by rw [PB.block_result]; rfl)
      (by rw [PB.block_result]) c2 f2 hcond
    rcases TraceN.through (run_comp (run_one e0) (run_comp (run_one e1)
        (run_comp (run_one e2) e3))) ht with rfl | ⟨-, ht1⟩
    · exact writeSeq_nil 2 _ _
    exact plain_report_path ce .notValue (core := c2) hfile ht1

end

end IxCC.X86.Exe.Plain
