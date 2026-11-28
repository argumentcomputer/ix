import IxCC.X86.Exe.Plain.Proof.Spec
import IxCC.X86.Exe.Machine.Proof.Paths

/-! # The Plain Shell's Blocks, Layout Facts & Extra Instruction Effects

Provides the block-level byte-machine stepping primitives for the plain `--exe`
shell (`X86.Exe.Code.shell`, 48 blocks), reusing `X86.Exe.Machine.Proof.{Effects,
Steps, Call, Placement, Paths}` and adding the 3 plain-shell-specific arithmetic
instruction lemmas (`exec_umul64`, `exec_div64`, `exec_add64_branch`). -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Plain

open IxCC.X86
open IxCC.X86.Exe
open IxCC.X86.Exe.Process
open IxCC.X86.Encode (instructionOperation execute_linear)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)

/-! ## Extra instruction effects for `parse` and `digit` -/

/-- `mul r` (64-bit widening unsigned multiply `rdx:rax := r * rax`). -/
theorem exec_umul64 (s : ByteEval.State) (r : GPR) (len : Nat) :
    let prod := (s.core.readReg r).toNat * (s.core.readReg .rax).toNat
    ∃ fl, ByteEval.execute ⟨instructionOperation (.op (Op.mulM .w64) [.reg r]), len⟩ s =
      .ok ⟨(s.core.setReg .rax (UInt64.ofNat (prod % 2 ^ 64))).setReg .rdx (UInt64.ofNat (prod / 2 ^ 64)),
        s.rip + UInt64.ofNat len, fl⟩ := by
  dsimp only
  rw [instructionOperation, execute_linear rfl]
  simp only [Op.exec, Op.run, Op.inputs, Op.stage, desc, Op.mulM, Table.umulDesc, Table.rmSlot,
    Table.umulSem, readSlots, writeSlots, writeImplicits, Arg.load, Except.mapError, bind,
    Except.bind, pure, Except.pure, Core.writeReg, Width.bits, truncate64]
  exact ⟨_, rfl⟩

/-- `div r` (64-bit unsigned divide `rax := dividend / r`, `rdx := dividend % r`)
when `rdx = 0` and `0 < r.toNat`. -/
theorem exec_div64 (s : ByteEval.State) (r : GPR) (len : Nat)
    (hhi : s.core.readReg .rdx = 0) (hd : 0 < (s.core.readReg r).toNat) :
    ∃ fl, ByteEval.execute ⟨instructionOperation (.op (Op.divM .w64) [.reg r]), len⟩ s =
      .ok ⟨(s.core.setReg .rax (UInt64.ofNat ((s.core.readReg .rax).toNat / (s.core.readReg r).toNat))).setReg
          .rdx (UInt64.ofNat ((s.core.readReg .rax).toNat % (s.core.readReg r).toNat)),
        s.rip + UInt64.ofNat len, fl⟩ := by
  rw [instructionOperation, execute_linear rfl]
  simp only [Op.exec, Op.run, Op.inputs, Op.stage, desc, Op.divM, Table.divDesc, Table.rmSlot,
    Table.divSem, Role.reads, Role.writes, readSlots, readImplicits, writeSlots,
    writeImplicits, Arg.load, Except.mapError, bind, Except.bind, pure, Except.pure, Core.writeReg,
    Width.bits, truncate64, hhi, List.filterMap_cons, List.filterMap_nil, List.cons_append,
    List.nil_append, List.headD, List.tail, ↓reduceIte]
  have hzero : (0 : Word).toNat = 0 := rfl
  rw [hzero]
  have hcond : (((s.core.readReg r).toNat == 0) || decide ((s.core.readReg r).toNat ≤ 0)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    omega
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
  exact ⟨_, rfl⟩

/-- `add rax, rcx` as a branch producer (sets `rax := rax + rcx` and `CF = (2^64 ≤ rax + rcx)`). -/
theorem exec_add64_mr (s : ByteEval.State) (d r : GPR) (len : Nat) :
    ByteEval.execute ⟨.op { mn := .add, w := .w64, form := .MR } [.reg d, .reg r], len⟩ s =
      .ok ⟨s.core.setReg d (s.core.readReg d + s.core.readReg r), s.rip + UInt64.ofNat len,
        ByteEval.aluFlags .add .w64 (s.core.readReg d) (s.core.readReg r)⟩ := by
  rw [execute_linear rfl]
  simp only [Op.exec, Op.run, Op.inputs, Op.stage, desc, Table.arithDesc, Table.addArith,
    Table.Arith.sem, Table.Arith.role, Role.reads, Option.isSome_some,
    ↓reduceIte, Table.rmSlot, Table.regSlot, Table.aluSem, readSlots, readImplicits, writeSlots,
    writeImplicits, Arg.load, Arg.store, Except.mapError, bind, Except.bind, pure, Except.pure,
    Core.writeReg, AluOp.eval, List.filterMap_nil, List.cons_append,
    List.nil_append, List.headD, ByteEval.merge_allSet]

/-- What `add`'s flags say of `.unsignedLt` (`jb`, i.e. carry flag `CF`): unsigned 64-bit overflow. -/
theorem add64_carry_test (a b : Word) :
    (ByteEval.aluFlags .add .w64 a b).test .unsignedLt =
      some (decide (2 ^ 64 ≤ a.toNat + b.toNat)) := by
  simp only [ByteEval.aluFlags, ByteEval.Flags.test, ByteEval.addFlags, Width.bits, BitVec.setWidth_eq]
  rfl

/-! ## Checked file facts for plain `--exe` -/

/-- Extract `plan` preconditions from `X86.Exe.plan input parts = .ok pl`. -/
theorem plan_parts {input : X86.Exe.Input} {parts : ObjectParts} {pl : Plan}
    (h : X86.Exe.plan input parts = .ok pl) :
    input.arity ≤ 5 ∧
    (match input.result with | .enum n => 0 < n ∧ n < 2 ^ 31 | .nat => True) ∧
    input.layout.check = true ∧
    planFor input.frame parts = .ok pl := by
  unfold X86.Exe.plan at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · rename_i har
    cases hr : input.result with
    | nat =>
      simp only [hr] at h
      split at h
      · rename_i hL
        exact ⟨har, trivial, hL, h⟩
      · cases h
    | enum n =>
      simp only [hr] at h
      split at h
      · cases h
      · rename_i hne
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hne
        split at h
        · rename_i hL
          exact ⟨har, ⟨by omega, by omega⟩, hL, h⟩
        · cases h
  · cases h

/-- View a `Certified input` as a `Checked input.frame input.object` (for `Process.Loaded`). -/
def Certified.checked {input : X86.Exe.Input} (ce : Certified input) :
    Checked input.frame input.object :=
  ⟨ce.bytes, ce.plan, by
    obtain ⟨parts, hp, hq, hf⟩ := ce.valid
    obtain ⟨_, _, _, hpf⟩ := plan_parts hq
    exact ⟨parts, hp, hpf, ⟨hf.header, hf.size, hf.gaps, hf.text, hf.data, hf.shell, hf.calls, hf.lands⟩⟩⟩

/-- Key numerical and slice facts of a certified plain executable. -/
structure PlainFileFacts {input : X86.Exe.Input} (ce : Certified input) : Prop where
  arity : input.arity ≤ 5
  resultOk : match input.result with | .enum n => 0 < n ∧ n < 2 ^ 31 | .nat => True
  layoutCheck : input.layout.check = true
  size : ce.bytes.size = ce.plan.placement.fileSize
  below : fileBase + ce.plan.placement.fileSize ≤ dataBase
  textEnd : ce.plan.placement.textOffset + ce.plan.placement.textSize ≤ ce.plan.placement.dataOffset
  dataEnd : ce.plan.placement.dataOffset + ce.plan.placement.dataSize ≤ ce.plan.placement.shellOffset
  text : ∃ parsed, ELFRead.parse input.object = some parsed ∧
    parsed.text.size = ce.plan.placement.textSize ∧
    ∀ i < ce.plan.placement.textSize, ce.bytes[ce.plan.placement.textOffset + i]? = parsed.text[i]?
  data : (dataBytes input.arity (fileBase + ce.plan.placement.dataOffset)).size = ce.plan.placement.dataSize ∧
    ∀ i < ce.plan.placement.dataSize,
      ce.bytes[ce.plan.placement.dataOffset + i]? =
        (dataBytes input.arity (fileBase + ce.plan.placement.dataOffset))[i]?
  stackArea : 0 < input.layout.stackArea
  regionEnd : input.layout.regionStart + input.layout.regionArea ≤ 2 ^ 47
  regionSize : 0 < input.layout.regionArea

theorem plainFileFacts {input : X86.Exe.Input} (ce : Certified input) : PlainFileFacts ce := by
  obtain ⟨parts, _, hq, hf⟩ := ce.valid
  obtain ⟨har, hres, hL, hpf⟩ := plan_parts hq
  have hp := planFor_facts hpf
  have hseg := hp.segments
  have happ := hp.apart
  simp only [Input.frame, Layout.segments, segmentsOk, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hseg
  simp only [Input.frame, Layout.segments, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, apart, Bool.or_eq_true, decide_eq_true_eq] at happ
  obtain ⟨parsed, hparse, htext⟩ := hf.text
  obtain ⟨_, htsize, htext⟩ := slice_getElem? htext
  obtain ⟨_, hdsize, hdata⟩ := slice_getElem? hf.data
  have hd : dataBase = 268435456 := rfl
  have hfb : fileBase = 4194304 := rfl
  have h1 := le_alignUp (ce.plan.placement.textOffset + ce.plan.placement.textSize) 8 (by decide)
  have h2 := le_alignUp (ce.plan.placement.dataOffset + ce.plan.placement.dataSize) 16 (by decide)
  rw [← hp.dataOffset] at h1
  rw [← hp.shellOffset] at h2
  refine ⟨har, hres, hL, hf.size, ?_, h1, h2, ⟨parsed, hparse, htsize, htext⟩, ⟨hdsize, hdata⟩,
    by omega, by omega, by omega⟩
  rcases happ.1 with h | h <;> omega

theorem plainLayout_numbers {input : X86.Exe.Input} (ce : Certified input) :
    let L := input.layout
    256 ≤ L.stackArea ∧
    L.stack + 256 ≤ L.stackArea ∧
    L.stackTop = dataBase + L.stackArea - 256 ∧
    L.shellTop = dataBase + L.stackArea ∧
    L.regionStart = dataBase + L.stackArea + 0x1000 ∧
    L.region ≤ L.regionArea ∧
    L.regionStart + L.regionArea ≤ 2 ^ 47 ∧
    8192 ≤ L.stack ∧ 4096 ≤ L.region ∧ 64 ≤ L.budget ∧ L.budget = L.stack - 4096 := by
  have ff := plainFileFacts ce
  have hL := ff.layoutCheck
  simp only [Layout.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨_, hs⟩, hr⟩, _⟩ := hL
  have hsa : input.layout.stack + 256 ≤ input.layout.stackArea := by
    simp only [Layout.stackArea, pageAlign, scratch]; omega
  have hra : input.layout.region ≤ input.layout.regionArea := by
    simp only [Layout.regionArea, pageAlign]; omega
  refine ⟨by omega, hsa, rfl, rfl, rfl, hra, ff.regionEnd, hs, hr, ?_, rfl⟩
  simp only [Layout.budget, stackReserve]; omega

/-! ## Shell blocks & stepping helpers -/

/-- The `Spec` used by `ce : Certified input`. -/
abbrev plainSpec {input : X86.Exe.Input} (ce : Certified input) : Spec :=
  { arity := input.arity, result := input.result, root := input.root, layout := input.layout,
    data := fileBase + ce.plan.placement.dataOffset }

/-- The plain shell program of `ce`. -/
abbrev plainShellOf {input : X86.Exe.Input} (ce : Certified input) : Shell.Program :=
  shell (plainSpec ce)

theorem plainShell_size (s : Spec) : (shell s).blocks.size = 48 := rfl

theorem plainShell_get {input : X86.Exe.Input} (ce : Certified input) {b : Nat} (hb : b < 48) :
    (plainShellOf ce).blocks[b]? = some (blockAt (plainShellOf ce) b) :=
  blocks_get (by rw [plainShell_size]; exact hb)

/-- The address of instruction `j` of block `b` in the plain shell. -/
def plainAddr {input : X86.Exe.Input} (ce : Certified input) (b j : Nat) : Nat :=
  fileBase + (ce.plan.placement.shellOffset + blockOffset (plainShellOf ce) b +
    instrOffset (blockAt (plainShellOf ce) b) j)

/-- Word address of instruction `j` of block `b`. -/
abbrev paddr {input : X86.Exe.Input} (ce : Certified input) (b j : Nat) : Word :=
  UInt64.ofNat (plainAddr ce b j)

theorem plainAddr_zero {input : X86.Exe.Input} (ce : Certified input) (b : Nat) :
    plainAddr ce b 0 = fileBase + (ce.plan.placement.shellOffset + blockOffset (plainShellOf ce) b) := by
  simp [plainAddr, instrOffset_zero]

theorem plain_file_fit {input : X86.Exe.Input} (ce : Certified input) :
    fileBase + ce.bytes.size < 2 ^ 64 := by
  have ff := plainFileFacts ce
  have hd : dataBase = 268435456 := rfl
  rw [ff.size]
  have := ff.below
  omega

theorem plain_entry_addr {input : X86.Exe.Input} (ce : Certified input) :
    UInt64.ofNat (fileBase + ce.plan.placement.shellOffset) = paddr ce 0 0 := by
  show _ = UInt64.ofNat (fileBase + (ce.plan.placement.shellOffset +
    blockOffset (plainShellOf ce) 0 + instrOffset (blockAt (plainShellOf ce) 0) 0))
  simp [blockOffset, instrOffset]

section Steps
variable {input : X86.Exe.Input} (ce : Certified input)

theorem pstep_ok {b j : Nat} (hb : b < 48) {i : X86.Instr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t)
    {s : ByteEval.State} (hrip : s.rip = paddr ce b j) {core : Core} {fl : ByteEval.Flags}
    (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Shell.Instr.size (.instr i)), fl⟩) :
    ByteEval.step ce.bytes fetchBase s = .ok ⟨core, paddr ce b (j + 1), fl⟩ :=
  ce.shell.step_ok (plain_file_fit ce) (plainShell_get ce hb) hi hnc hrip hex

theorem pstep_fault {b j : Nat} (hb : b < 48) {i : X86.Instr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t)
    {s : ByteEval.State} (hrip : s.rip = paddr ce b j) {f : MemoryFault}
    (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s = .error (.memory f)) :
    ByteEval.step ce.bytes fetchBase s = .error (.memory f) :=
  ce.shell.step_fault (plain_file_fit ce) (plainShell_get ce hb) hi hnc hrip hex

theorem prun_branch {b : Nat} (hb : b < 48) {o : Op} {args : List Arg} {cond : Condition}
    {yes no : BlockId}
    (hterm : (blockAt (plainShellOf ce) b).terminator = .branch o args cond yes no .rel32)
    {s : ByteEval.State} (hrip : s.rip = paddr ce b (blockAt (plainShellOf ce) b).instructions.size)
    {core : Core} {fl : ByteEval.Flags} {taken : Bool}
    (hex : ByteEval.execute ⟨.op o args, (Encode.encodeOp o args).size⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Encode.encodeOp o args).size, fl⟩)
    (htest : fl.test cond = some taken) :
    ByteEval.run ce.bytes fetchBase (if taken then 2 else 3) s =
      .ok ⟨core, paddr ce (if taken then yes else no).toNat 0, fl⟩ := by
  rw [paddr, plainAddr_zero]
  exact ce.shell.run_branch (plain_file_fit ce) (plainShell_get ce hb) hterm hrip hex htest

theorem pstep_jump {b : Nat} (hb : b < 48) {t : BlockId}
    (hterm : (blockAt (plainShellOf ce) b).terminator = .jump t) {s : ByteEval.State}
    (hrip : s.rip = paddr ce b (blockAt (plainShellOf ce) b).instructions.size) :
    ByteEval.step ce.bytes fetchBase s = .ok { s with rip := paddr ce t.toNat 0 } := by
  rw [paddr, plainAddr_zero]
  exact ce.shell.step_jump (plain_file_fit ce) (plainShell_get ce hb) hterm hrip

theorem pstep_ret {b : Nat} (hb : b < 48) (hterm : (blockAt (plainShellOf ce) b).terminator = .ret)
    {s : ByteEval.State} (hrip : s.rip = paddr ce b (blockAt (plainShellOf ce) b).instructions.size) :
    ByteEval.step ce.bytes fetchBase s =
      match s.core.memory.read64? (s.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { s with core := s.core.setReg .rsp (s.core.readReg .rsp + 8), rip := target } :=
  ce.shell.step_ret (plain_file_fit ce) (plainShell_get ce hb) hterm hrip

theorem pstep_call {b j : Nat} (hb : b < 48) {t : BlockId}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr (.call t)))
    {s : ByteEval.State} (hrip : s.rip = paddr ce b j) :
    ByteEval.step ce.bytes fetchBase s =
      match s.core.memory.write64? (s.core.readReg .rsp - 8) (paddr ce b (j + 1)) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { s.core.setReg .rsp (s.core.readReg .rsp - 8) with memory }
          rip := paddr ce t.toNat 0, flags := s.flags } := by
  have h0 : paddr ce t.toNat 0 =
      UInt64.ofNat (fileBase + (ce.plan.placement.shellOffset + blockOffset (plainShellOf ce) t.toNat)) := by
    rw [paddr, plainAddr_zero]
  rw [h0]
  exact ce.shell.step_call (plain_file_fit ce) (plainShell_get ce hb) hi hrip

theorem pcallsTo {b j : Nat} (hb : b < 48) {name : String}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.callExport name))
    {s : ByteEval.State} (hrip : s.rip = paddr ce b j) :
    ∃ offset, ELF.symbol? input.object name = some offset ∧
      CallsTo ce.bytes s (UInt64.ofNat (fileBase + ce.plan.placement.textOffset) + UInt64.ofNat offset) := by
  obtain ⟨t, ht, hc⟩ := ce.shell.callsTo (plain_file_fit ce) (plainShell_get ce hb) hi hrip
  simp only [exportAt, Option.map_eq_some_iff] at ht
  obtain ⟨offset, hoff, rfl⟩ := ht
  refine ⟨offset, hoff, ?_⟩
  rw [← UInt64.ofNat_add, Nat.add_assoc]
  exact hc

theorem psyscall_at {b j : Nat} (hb : b < 48)
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some .syscall)
    {s : ByteEval.State} (hrip : s.rip = paddr ce b j) :
    Decode.decodeAt ce.bytes (s.rip - fetchBase).toNat = none ∧ syscallAt ce.bytes s.rip ∧
      s.rip + 2 = paddr ce b (j + 1) :=
  ce.shell.syscall_at (plain_file_fit ce) (plainShell_get ce hb) hi hrip

theorem plainAddr_in {b j : Nat} (hb : b < 48) {i : X86.Instr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t) :
    plainAddr ce b j < fileBase + ce.bytes.size := by
  have hm := ce.shell.instr b _ (plainShell_get ce hb) j _ hi
  have hm' : Stream.decodes ce.bytes
      (ce.plan.placement.shellOffset + blockOffset (plainShellOf ce) b +
        instrOffset (blockAt (plainShellOf ce) b) j) (instructionOperation i) (Shell.Instr.size (.instr i)) = true := by
    cases i with
    | call t => exact absurd rfl (hnc t)
    | _ => simp only [Shell.instrMatches, Bool.and_eq_true] at hm; exact hm.2
  have := decodeAt_lt (decodes_some hm')
  unfold plainAddr
  omega

theorem plainAddr_term_in {b : Nat} (hb : b < 48) :
    plainAddr ce b (blockAt (plainShellOf ce) b).instructions.size < fileBase + ce.bytes.size := by
  have hval : Shell.Valid (plainShellOf ce) ce.bytes ce.plan.placement.shellOffset
      (exportAt input.object ce.plan.placement) := ce.shell
  have ht := hval.term b _ (plainShell_get ce hb)
  unfold plainAddr
  cases h : (blockAt (plainShellOf ce) b).terminator with
  | ret =>
    rw [h] at ht
    have := decodeAt_lt (decodes_some ht)
    omega
  | jump target =>
    rw [h] at ht
    simp only [Shell.terminatorMatches, Shell.targets, Bool.and_eq_true] at ht
    have := decodeAt_lt (decodes_some ht.2)
    omega
  | branch o args cond yes no kind =>
    rw [h] at ht
    cases kind with
    | rel32 =>
      simp only [Shell.terminatorMatches, Bool.and_eq_true] at ht
      have := decodeAt_lt (decodes_some ht.1.1)
      omega
    | fall =>
      simp [Shell.terminatorMatches] at ht
  | tailCall target =>
    rw [h] at ht
    simp only [Shell.terminatorMatches, Shell.targets, Bool.and_eq_true] at ht
    have := decodeAt_lt (decodes_some ht.2)
    omega

theorem plainAddr_below {b j : Nat} (h : plainAddr ce b j < fileBase + ce.bytes.size) :
    plainAddr ce b j < dataBase := by
  have ff := plainFileFacts ce
  rw [ff.size] at h
  have := ff.below
  omega

/-- Convenient step wrappers for common plain-shell instructions. -/
theorem pstep_movI {b j : Nat} (hb : b < 48) {r : GPR} {v : Nat}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.mI r v))
    (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core.setReg r (UInt64.ofNat v), paddr ce b (j + 1), fl⟩ :=
  pstep_ok ce hb (i := Instr.mov .w64 r (.imm (UInt64.ofNat v))) hi
    (by intro t h; cases h) rfl (exec_mov _ _ _ _)

theorem pstep_movR {b j : Nat} (hb : b < 48) {d s : GPR}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.mR d s))
    (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core.setReg d (core.readReg s), paddr ce b (j + 1), fl⟩ :=
  pstep_ok ce hb (i := Instr.mov .w64 d (.reg s)) hi
    (by intro t h; cases h) rfl (exec_mov _ _ _ _)

theorem pstep_lea {b j : Nat} (hb : b < 48) {r : GPR} {a : MemAddr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr (Instr.lea r a)))
    (core : Core) (fl : ByteEval.Flags) :
    ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core.setReg r (a.eval core), paddr ce b (j + 1), fl⟩ :=
  pstep_ok ce hb (i := Instr.lea r a) hi
    (by intro t h; cases h) rfl (exec_lea _ _ _ _)

theorem pstep_alu {b j : Nat} (hb : b < 48) {op : AluOp} {w : Width} {r : GPR} {src : AluSource}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr (Instr.alu op w r src)))
    (core : Core) (fl : ByteEval.Flags) :
    ∃ fl', ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core.writeReg w r (op.eval (core.readReg r) (src.eval core)), paddr ce b (j + 1), fl'⟩ :=
  let ⟨fl', hx⟩ := exec_alu ⟨core, paddr ce b j, fl⟩ op w r src (Shell.Instr.size (.instr (Instr.alu op w r src)))
  ⟨fl', pstep_ok ce hb hi (by intro t h; cases src <;> cases h) rfl hx⟩

theorem pstep_shr {b j : Nat} (hb : b < 48) {r : GPR} {v : Nat}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? =
      some (.instr (.op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)])))
    (core : Core) (fl : ByteEval.Flags) :
    ∃ fl', ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core.setReg r ⟨(ShiftOp.shr.apply .w64 (core.readReg r) (shiftCount .w64 (UInt64.ofNat v))).setWidth 64⟩,
        paddr ce b (j + 1), fl'⟩ :=
  ⟨_, pstep_ok ce hb (s := ⟨core, paddr ce b j, fl⟩)
    (i := .op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)]) hi
    (by intro t h; cases h) rfl (exec_shr _ _ _ _)⟩

theorem pstep_umul64 {b j : Nat} (hb : b < 48) {r : GPR}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr (.op (Op.mulM .w64) [.reg r])))
    (core : Core) (fl : ByteEval.Flags) :
    let prod := (core.readReg r).toNat * (core.readReg .rax).toNat
    ∃ fl', ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨(core.setReg .rax (UInt64.ofNat (prod % 2 ^ 64))).setReg .rdx (UInt64.ofNat (prod / 2 ^ 64)),
        paddr ce b (j + 1), fl'⟩ :=
  let ⟨fl', hx⟩ := exec_umul64 ⟨core, paddr ce b j, fl⟩ r (Shell.Instr.size (.instr (.op (Op.mulM .w64) [.reg r])))
  ⟨fl', pstep_ok ce hb (s := ⟨core, paddr ce b j, fl⟩)
    (i := .op (Op.mulM .w64) [.reg r]) hi (by intro t h; cases h) rfl hx⟩

theorem pstep_div64 {b j : Nat} (hb : b < 48) {r : GPR}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (.instr (.op (Op.divM .w64) [.reg r])))
    (core : Core) (fl : ByteEval.Flags)
    (hhi : core.readReg .rdx = 0) (hd : 0 < (core.readReg r).toNat) :
    ∃ fl', ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨(core.setReg .rax (UInt64.ofNat ((core.readReg .rax).toNat / (core.readReg r).toNat))).setReg
          .rdx (UInt64.ofNat ((core.readReg .rax).toNat % (core.readReg r).toNat)),
        paddr ce b (j + 1), fl'⟩ :=
  let ⟨fl', hx⟩ := exec_div64 ⟨core, paddr ce b j, fl⟩ r (Shell.Instr.size (.instr (.op (Op.divM .w64) [.reg r]))) hhi hd
  ⟨fl', pstep_ok ce hb (s := ⟨core, paddr ce b j, fl⟩)
    (i := .op (Op.divM .w64) [.reg r]) hi (by intro t h; cases h) rfl hx⟩

theorem pstep_load64 {b j : Nat} (hb : b < 48) {r : GPR} {a : MemAddr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.ld r a))
    (core : Core) (fl : ByteEval.Flags) :
    (∃ v, core.memory.read64? (a.eval core) = .ok v ∧
      ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core.setReg r v, paddr ce b (j + 1), fl⟩) ∨
    (∃ f, ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ = .error (.memory f)) := by
  have hx := exec_load64 ⟨core, paddr ce b j, fl⟩ r a (Shell.Instr.size (SB.ld r a))
  cases hr : core.memory.read64? (a.eval core) with
  | ok v =>
    rw [hr] at hx
    exact .inl ⟨v, rfl, pstep_ok ce hb hi (by intro t h; cases h) rfl hx⟩
  | error f =>
    rw [hr] at hx
    exact .inr ⟨f, pstep_fault ce hb hi (by intro t h; cases h) rfl hx⟩

theorem pstep_load8 {b j : Nat} (hb : b < 48) {r : GPR} {a : MemAddr}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.ld8 r a))
    (core : Core) (fl : ByteEval.Flags) :
    (∃ v, core.memory.read? .w8 (a.eval core) = .ok v ∧
      ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core.setReg r (Width.w8.truncate v), paddr ce b (j + 1), fl⟩) ∨
    (∃ f, ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ = .error (.memory f)) := by
  have hx := exec_load8 ⟨core, paddr ce b j, fl⟩ r a (Shell.Instr.size (SB.ld8 r a))
  cases hr : core.memory.read? .w8 (a.eval core) with
  | ok v =>
    rw [hr] at hx
    exact .inl ⟨v, rfl, pstep_ok ce hb hi (by intro t h; cases h) rfl hx⟩
  | error f =>
    rw [hr] at hx
    exact .inr ⟨f, pstep_fault ce hb hi (by intro t h; cases h) rfl hx⟩

theorem pstep_store64 {b j : Nat} (hb : b < 48) {a : MemAddr} {r : GPR}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.st a r))
    (core : Core) (fl : ByteEval.Flags) :
    (∃ m, core.memory.write64? (a.eval core) (core.readReg r) = .ok m ∧
      ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨{ core with memory := m }, paddr ce b (j + 1), fl⟩) ∨
    (∃ f, ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ = .error (.memory f)) := by
  have hx := exec_store64 ⟨core, paddr ce b j, fl⟩ a r (Shell.Instr.size (SB.st a r))
  cases hw : core.memory.write64? (a.eval core) (core.readReg r) with
  | ok m =>
    rw [hw] at hx
    exact .inl ⟨m, rfl, pstep_ok ce hb hi (by intro t h; cases h) rfl hx⟩
  | error f =>
    rw [hw] at hx
    exact .inr ⟨f, pstep_fault ce hb hi (by intro t h; cases h) rfl hx⟩

theorem pstep_store8 {b j : Nat} (hb : b < 48) {a : MemAddr} {r : GPR}
    (hi : (blockAt (plainShellOf ce) b).instructions[j]? = some (SB.st8 a r))
    (core : Core) (fl : ByteEval.Flags) :
    (∃ m, core.memory.write? .w8 (a.eval core) (core.readReg r) = .ok m ∧
      ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨{ core with memory := m }, paddr ce b (j + 1), fl⟩) ∨
    (∃ f, ByteEval.step ce.bytes fetchBase ⟨core, paddr ce b j, fl⟩ = .error (.memory f)) := by
  have hx := exec_store8 ⟨core, paddr ce b j, fl⟩ a r (Shell.Instr.size (SB.st8 a r))
  cases hw : core.memory.write? .w8 (a.eval core) (core.readReg r) with
  | ok m =>
    rw [hw] at hx
    exact .inl ⟨m, rfl, pstep_ok ce hb hi (by intro t h; cases h) rfl hx⟩
  | error f =>
    rw [hw] at hx
    exact .inr ⟨f, pstep_fault ce hb hi (by intro t h; cases h) rfl hx⟩

theorem pholds_eq (a b : Word) : Condition.holds .eq .w64 a b = (a == b) := by
  simp [Condition.holds]

theorem pholds_ne (a b : Word) : Condition.holds .ne .w64 a b = (a != b) := by
  simp [Condition.holds]

theorem pholds_unsignedGt (a b : Word) : Condition.holds .unsignedGt .w64 a b = decide (b.toNat < a.toNat) := by
  simp [Condition.holds, UInt64.lt_iff_toNat_lt]

theorem pholds_unsignedGe (a b : Word) : Condition.holds .unsignedGe .w64 a b = decide (b.toNat ≤ a.toNat) := by
  simp [Condition.holds, UInt64.le_iff_toNat_le]

theorem prun_ifNz {b j : Nat} (hb : b < 48)
    (hsz : (blockAt (plainShellOf ce) b).instructions.size = j)
    {r : GPR} {t f : Nat}
    (hterm : (blockAt (plainShellOf ce) b).terminator = SB.ifNz r t f)
    (core : Core) (fl : ByteEval.Flags) {taken : Bool} (htk : (core.readReg r != 0) = taken)
    (ht : t < 48 := by decide) (hf : f < 48 := by decide) :
    ∃ fl', ByteEval.run ce.bytes fetchBase (if taken then 2 else 3) ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core, paddr ce (if taken then t else f) 0, fl'⟩ := by
  have h := prun_branch ce hb (o := { mn := .test, w := .w64, form := .MR })
    (args := [.reg r, .reg r]) (cond := .ne) (yes := UInt32.ofNat t) (no := UInt32.ofNat f)
    hterm (s := ⟨core, paddr ce b j, fl⟩) (by rw [hsz]) (exec_test _ _ _ _)
    (taken := taken) (by rw [test_ne_self, htk])
  cases taken with
  | true =>
    have h' : ByteEval.run ce.bytes fetchBase 2 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat t).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h'
    exact ⟨_, h'⟩
  | false =>
    have h' : ByteEval.run ce.bytes fetchBase 3 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat f).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show f < 4294967296; omega)] at h'
    exact ⟨_, h'⟩

theorem prun_cmpI {b j : Nat} (hb : b < 48)
    (hsz : (blockAt (plainShellOf ce) b).instructions.size = j)
    {r : GPR} {v : Nat} {c : Condition} {t f : Nat}
    (hterm : (blockAt (plainShellOf ce) b).terminator = SB.cmpI r v c t f)
    (core : Core) (fl : ByteEval.Flags) {taken : Bool}
    (htk : c.holds .w64 (core.readReg r) (signExtend32 (UInt32.ofNat v)) = taken)
    (ht : t < 48 := by decide) (hf : f < 48 := by decide) :
    ∃ fl', ByteEval.run ce.bytes fetchBase (if taken then 2 else 3) ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core, paddr ce (if taken then t else f) 0, fl'⟩ := by
  let cmp : Compare := { width := .w64, left := r, right := .imm (UInt32.ofNat v) }
  have h := prun_branch ce hb (o := cmp.row.1) (args := cmp.row.2) (cond := c)
    (yes := UInt32.ofNat t) (no := UInt32.ofNat f) hterm (s := ⟨core, paddr ce b j, fl⟩)
    (by rw [hsz]) (exec_compare cmp _ _) (taken := taken) (by rw [compare_test]; exact congrArg some htk)
  cases taken with
  | true =>
    have h' : ByteEval.run ce.bytes fetchBase 2 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat t).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h'
    exact ⟨_, h'⟩
  | false =>
    have h' : ByteEval.run ce.bytes fetchBase 3 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat f).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show f < 4294967296; omega)] at h'
    exact ⟨_, h'⟩

theorem prun_cmpR {b j : Nat} (hb : b < 48)
    (hsz : (blockAt (plainShellOf ce) b).instructions.size = j)
    {r s : GPR} {c : Condition} {t f : Nat}
    (hterm : (blockAt (plainShellOf ce) b).terminator = SB.cmpR r s c t f)
    (core : Core) (fl : ByteEval.Flags) {taken : Bool}
    (htk : c.holds .w64 (core.readReg r) (core.readReg s) = taken)
    (ht : t < 48 := by decide) (hf : f < 48 := by decide) :
    ∃ fl', ByteEval.run ce.bytes fetchBase (if taken then 2 else 3) ⟨core, paddr ce b j, fl⟩ =
      .ok ⟨core, paddr ce (if taken then t else f) 0, fl'⟩ := by
  let cmp : Compare := { width := .w64, left := r, right := .reg s }
  have h := prun_branch ce hb (o := cmp.row.1) (args := cmp.row.2) (cond := c)
    (yes := UInt32.ofNat t) (no := UInt32.ofNat f) hterm (s := ⟨core, paddr ce b j, fl⟩)
    (by rw [hsz]) (exec_compare cmp _ _) (taken := taken) (by rw [compare_test]; exact congrArg some htk)
  cases taken with
  | true =>
    have h' : ByteEval.run ce.bytes fetchBase 2 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat t).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show t < 4294967296; omega)] at h'
    exact ⟨_, h'⟩
  | false =>
    have h' : ByteEval.run ce.bytes fetchBase 3 ⟨core, paddr ce b j, fl⟩ =
        .ok ⟨core, paddr ce (UInt32.ofNat f).toNat 0, _⟩ := h
    rw [UInt32.toNat_ofNat_of_lt' (by show f < 4294967296; omega)] at h'
    exact ⟨_, h'⟩

end Steps

/-! ## Literal block statements (`rfl`) -/

namespace PB

abbrev atIdx (b : GPR) (disp : Nat) (idx : IndexReg) (sc : Scale) : MemAddr :=
  { base := some b, index := some idx, scale := sc, displacement := UInt32.ofNat disp }
abbrev addR (d s : GPR) : Shell.Instr := .instr (Instr.alu .add .w64 d (.reg s))
abbrev subR (d s : GPR) : Shell.Instr := .instr (Instr.alu .sub .w64 d (.reg s))
abbrev mulM (r : GPR) : Shell.Instr := .instr (.op (Op.mulM .w64) [.reg r])
abbrev divM (r : GPR) : Shell.Instr := .instr (.op (Op.divM .w64) [.reg r])

theorem block_start (s : Spec) : blockAt (shell s) 0 =
    ⟨#[SB.mI .rax 157, SB.mI .rdi 38, SB.mI .rsi 1, SB.mI .rdx 0, SB.mI .r10 0, SB.mI .r8 0, .syscall],
      SB.ifNz .rax 46 1⟩ := rfl

theorem block_seccomp (s : Spec) : blockAt (shell s) 1 =
    ⟨#[SB.mI .rax 317, SB.mI .rdi 1, SB.mI .rsi 0, SB.mI .rdx (fprogAddr s.data), .syscall],
      SB.ifNz .rax 46 2⟩ := rfl

theorem block_args (s : Spec) : blockAt (shell s) 2 =
    ⟨#[SB.ld .rbx (SB.at_ .rsp), .instr (Instr.lea .r12 (SB.at_ .rsp 8)),
      SB.mI .rsp s.layout.shellTop, SB.mI .rbp s.layout.stackTop,
      SB.mI .rax 0, SB.st (SB.at_ .rbp 0) .rax, SB.st (SB.at_ .rbp 8) .rax,
      SB.st (SB.at_ .rbp 16) .rax, SB.st (SB.at_ .rbp 24) .rax, SB.st (SB.at_ .rbp 32) .rax,
      SB.mI .r14 s.layout.regionStart, SB.mI .r13 s.layout.stackTop],
      SB.cmpI .rbx (s.arity + 1) .ne 38 3⟩ := rfl

theorem block_loopInit (s : Spec) : blockAt (shell s) 3 = ⟨#[SB.mI .r15 0], SB.jmp 4⟩ := rfl
theorem block_loopHead (s : Spec) : blockAt (shell s) 4 = ⟨#[], SB.cmpI .r15 s.arity .unsignedGe 8 5⟩ := rfl
theorem block_parseArg (s : Spec) : blockAt (shell s) 5 =
    ⟨#[SB.ld .rsi (atIdx .r12 8 .r15 .eight), .instr (.call (UInt32.ofNat 23))], SB.cmpI .rdx 0 .ne 6 7⟩ := rfl
theorem block_parseErr (s : Spec) : blockAt (shell s) 6 = ⟨#[], SB.cmpI .rdx 1 .eq 42 39⟩ := rfl
theorem block_storeArg (s : Spec) : blockAt (shell s) 7 =
    ⟨#[SB.st (atIdx .rbp 0 .r15 .eight) .rax, SB.addI .r15 1], SB.jmp 4⟩ := rfl
theorem block_callInit (s : Spec) : blockAt (shell s) 8 =
    ⟨#[SB.mI .rax s.layout.budget, SB.st (SB.at_ .r14 16) .rax, SB.mR .rdi .r14,
      SB.mI .rsi s.layout.region, SB.mI .rdx s.layout.budget,
      SB.mI .rcx 0, SB.mI .r8 0, SB.mI .r9 0, SB.mR .rsp .r13, .callExport initSymbol],
      SB.cmpR .rsp .r13 .ne 44 9⟩ := rfl
theorem block_initBack (s : Spec) : blockAt (shell s) 9 =
    ⟨#[SB.mI .rsp s.layout.shellTop], SB.ifNz .rax 33 10⟩ := rfl
theorem block_callRoot (s : Spec) : blockAt (shell s) 10 =
    ⟨#[SB.mR .rdi .r14, SB.ld .rsi (SB.at_ .rbp 0), SB.ld .rdx (SB.at_ .rbp 8),
      SB.ld .rcx (SB.at_ .rbp 16), SB.ld .r8 (SB.at_ .rbp 24), SB.ld .r9 (SB.at_ .rbp 32),
      SB.mI .r10 0, SB.mI .r11 0, SB.mR .rsp .r13, .callExport s.root],
      SB.cmpR .rsp .r13 .ne 44 11⟩ := rfl
theorem block_rootBack (s : Spec) : blockAt (shell s) 11 =
    ⟨#[SB.mI .rsp s.layout.shellTop], SB.ifNz .rax 33 12⟩ := rfl
theorem block_result (s : Spec) : blockAt (shell s) 12 =
    ⟨#[SB.mR .rax .rdx, SB.mR .rcx .rdx, .instr (Instr.alu .and .w32 .rcx (.imm 1))],
      SB.cmpI .rcx 0 .eq 45 13⟩ := rfl
theorem block_tag_nat (s : Spec) (h : s.result = .nat) : blockAt (shell s) 13 =
    ⟨#[SB.shrI .rax 1], SB.jmp 14⟩ := by cases s; cases h; rfl
theorem block_tag_enum (s : Spec) (n : Nat) (h : s.result = .enum n) : blockAt (shell s) 13 =
    ⟨#[SB.shrI .rax 1], SB.cmpI .rax n .unsignedGe 45 14⟩ := by cases s; cases h; rfl
theorem block_render (s : Spec) : blockAt (shell s) 14 =
    ⟨#[.instr (Instr.lea .rsi (SB.at_ .rbp 103)), SB.mI .r8 10, SB.st8 (SB.at_ .rsi) .r8], SB.jmp 15⟩ := rfl
theorem block_digit (s : Spec) : blockAt (shell s) 15 =
    ⟨#[SB.mI .rdx 0, SB.mI .rcx 10, divM .rcx, SB.addI .rdx 48, SB.subI .rsi 1, SB.st8 (SB.at_ .rsi) .rdx],
      SB.ifNz .rax 15 16⟩ := rfl
theorem block_output_nat (s : Spec) (h : s.result = .nat) : blockAt (shell s) 16 =
    ⟨#[.instr (Instr.lea .rdx (SB.at_ .rbp 104)), subR .rdx .rsi, SB.mI .rdi 1,
      .instr (.call (UInt32.ofNat 18)), SB.mI .rdi 0],
      SB.jmp 17⟩ := by cases s; cases h; rfl
theorem block_output_enum (s : Spec) (n : Nat) (h : s.result = .enum n) : blockAt (shell s) 16 =
    ⟨#[SB.mI .rdx 35, SB.subI .rsi 1, SB.st8 (SB.at_ .rsi) .rdx,
      .instr (Instr.lea .rdx (SB.at_ .rbp 104)), subR .rdx .rsi, SB.mI .rdi 1,
      .instr (.call (UInt32.ofNat 18)), SB.mI .rdi 0],
      SB.jmp 17⟩ := by cases s; cases h; rfl
theorem block_exit (s : Spec) : blockAt (shell s) 17 = ⟨#[SB.mI .rax 60, .syscall, .ud2], SB.jmp 17⟩ := rfl
theorem block_write (s : Spec) : blockAt (shell s) 18 = ⟨#[], SB.cmpI .rdx 0 .eq 21 19⟩ := rfl
theorem block_writeSys (s : Spec) : blockAt (shell s) 19 =
    ⟨#[SB.mI .rax 1, .syscall], SB.cmpI .rax 0 .signedLe 22 20⟩ := rfl
theorem block_writeAdv (s : Spec) : blockAt (shell s) 20 = ⟨#[], SB.cmpR .rax .rdx .unsignedGt 22 47⟩ := rfl
theorem block_writeRet (s : Spec) : blockAt (shell s) 21 = ⟨#[], .ret⟩ := rfl
theorem block_writeErr (s : Spec) : blockAt (shell s) 22 = ⟨#[SB.mI .rdi writeFailed], SB.jmp 17⟩ := rfl
theorem block_parse (s : Spec) : blockAt (shell s) 23 =
    ⟨#[SB.mI .rax 0, SB.mI .r9 0, SB.ld8 .rcx (SB.at_ .rsi)], SB.cmpI .rcx 0 .eq 32 24⟩ := rfl
theorem block_parseLoop (s : Spec) : blockAt (shell s) 24 =
    ⟨#[SB.ld8 .rcx (SB.at_ .rsi)], SB.cmpI .rcx 0 .eq 31 25⟩ := rfl
theorem block_parseDigit (s : Spec) : blockAt (shell s) 25 =
    ⟨#[SB.subI .rcx 48], SB.cmpI .rcx 9 .unsignedGt 32 26⟩ := rfl
theorem block_parseMul (s : Spec) : blockAt (shell s) 26 =
    ⟨#[SB.mI .r8 10, mulM .r8], SB.cmpI .rdx 0 .ne 27 28⟩ := rfl
theorem block_parseOvf1 (s : Spec) : blockAt (shell s) 27 = ⟨#[SB.mI .r9 1], SB.jmp 28⟩ := rfl
theorem block_parseAdd (s : Spec) : blockAt (shell s) 28 =
    ⟨#[], .branch { mn := .add, w := .w64, form := .MR } [.reg .rax, .reg .rcx] .unsignedLt
      (UInt32.ofNat 29) (UInt32.ofNat 30)⟩ := rfl
theorem block_parseOvf2 (s : Spec) : blockAt (shell s) 29 = ⟨#[SB.mI .r9 1], SB.jmp 30⟩ := rfl
theorem block_parseNext (s : Spec) : blockAt (shell s) 30 = ⟨#[SB.addI .rsi 1], SB.jmp 24⟩ := rfl
theorem block_parseDone (s : Spec) : blockAt (shell s) 31 = ⟨#[SB.mR .rdx .r9], .ret⟩ := rfl
theorem block_parseBad (s : Spec) : blockAt (shell s) 32 = ⟨#[SB.mI .rdx 2], .ret⟩ := rfl
theorem block_fail (s : Spec) : blockAt (shell s) 33 = ⟨#[], SB.cmpI .rax 1 .eq 40 34⟩ := rfl
theorem block_fail2 (s : Spec) : blockAt (shell s) 34 = ⟨#[], SB.cmpI .rax 2 .eq 41 35⟩ := rfl
theorem block_fail3 (s : Spec) : blockAt (shell s) 35 = ⟨#[], SB.cmpI .rax 3 .eq 42 36⟩ := rfl
theorem block_fail4 (s : Spec) : blockAt (shell s) 36 = ⟨#[], SB.cmpI .rax 4 .eq 43 44⟩ := rfl
theorem block_report (s : Spec) : blockAt (shell s) 37 =
    ⟨#[SB.mI .rsp s.layout.shellTop, SB.mI .rdi 2, .instr (.call (UInt32.ofNat 18)), SB.mR .rdi .r15], SB.jmp 17⟩ := rfl

def pmsgBlock (arity data : Nat) (m : Message) : Shell.Block :=
  let (a, n) := messageAt arity data m
  ⟨#[SB.mI .rsi a, SB.mI .rdx n, SB.mI .r15 m.status], SB.jmp 37⟩

theorem block_count (s : Spec) : blockAt (shell s) 38 = pmsgBlock s.arity s.data .count := rfl
theorem block_numeral (s : Spec) : blockAt (shell s) 39 = pmsgBlock s.arity s.data .numeral := rfl
theorem block_heap (s : Spec) : blockAt (shell s) 40 = pmsgBlock s.arity s.data .heap := rfl
theorem block_stack (s : Spec) : blockAt (shell s) 41 = pmsgBlock s.arity s.data .stack := rfl
theorem block_natOverflow (s : Spec) : blockAt (shell s) 42 = pmsgBlock s.arity s.data .natOverflow := rfl
theorem block_trap (s : Spec) : blockAt (shell s) 43 = pmsgBlock s.arity s.data .trap := rfl
theorem block_abi (s : Spec) : blockAt (shell s) 44 = pmsgBlock s.arity s.data .abi := rfl
theorem block_notValue (s : Spec) : blockAt (shell s) 45 = pmsgBlock s.arity s.data .notValue := rfl
theorem block_confine (s : Spec) : blockAt (shell s) 46 = pmsgBlock s.arity s.data .confine := rfl
theorem block_writeStep (s : Spec) : blockAt (shell s) 47 =
    ⟨#[addR .rsi .rax, subR .rdx .rax], SB.jmp 18⟩ := rfl

theorem block_message (s : Spec) (m : Message) :
    blockAt (shell s) (B.message m) =
      let (a, n) := messageAt s.arity s.data m
      ⟨#[SB.mI .rsi a, SB.mI .rdx n, SB.mI .r15 m.status], SB.jmp 37⟩ := by
  cases m
  · exact block_count s
  · exact block_numeral s
  · exact block_heap s
  · exact block_stack s
  · exact block_natOverflow s
  · exact block_trap s
  · exact block_abi s
  · exact block_notValue s
  · exact block_confine s

theorem message_lt (m : Message) : B.message m < 48 := by
  cases m <;> decide

end PB

end IxCC.X86.Exe.Plain
