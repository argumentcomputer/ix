import IxCC.X86.Exe.Machine.Proof.Steps
import IxCC.X86.Exe.Machine.Proof.Placement

/-!
# The machine shell's blocks, as steps of the process (X0-P, third part)

The generic shell of a machine executable (`Machine.shell`, 46 blocks) at
the addresses its checked file gives it: `shellAddr L step c b j` is the
address of instruction `j` of block `b`. A block of the shell is
`blockAt (shellOf c) b`, and its instructions and terminator are read off the
program by `rfl` (the message blocks through `msgBlock`, which states the
same block with `Machine.messageAt`'s two numbers).

`shell_valid` and `file_fit` are what every step lemma needs: the
shell check's facts and the file inside the address space. `mstep_ok`,
`mstep_fault`, `mrun_branch`, `mstep_jump`, `mstep_ret`, `mstep_call`,
`mcallsTo` and `msyscall_at` are `X86/Exe/Machine/Proof/Steps.lean`'s lemmas
for a certified machine executable, its targets stated as block addresses.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

open IxCC.X86.Encode (instructionOperation)
open IxCC.X86.Exe.Shell (blockOffset instrOffset)

/-- Block `b` of a shell (the default block past the last). -/
def blockAt (p : Shell.Program) (b : Nat) : Shell.Block := (p.blocks[b]?).getD default

theorem blocks_get {p : Shell.Program} {b : Nat} (h : b < p.blocks.size) : p.blocks[b]? = some (blockAt p b) := by
  simp only [blockAt, Array.getElem?_eq_getElem h, Option.getD_some]

theorem shell_size (L : Machine.Layout) (step : String) (data : Nat) :
    (Machine.shell L step data).blocks.size = 46 := rfl

section
variable {L : Machine.Layout} {step : String} {object : ByteArray}

/-- The shell of a machine executable. -/
abbrev shellOf (c : Checked (Machine.frame L step) object) : Shell.Program :=
  Machine.shell L step (fileBase + c.plan.placement.dataOffset)

/-- The address of instruction `j` of the shell's block `b`. -/
def shellAddr (L : Machine.Layout) (step : String) (c : Checked (Machine.frame L step) object) (b j : Nat) : Nat :=
  fileBase + (c.plan.placement.shellOffset + blockOffset (shellOf c) b + instrOffset (blockAt (shellOf c) b) j)

theorem shellAddr_zero (c : Checked (Machine.frame L step) object) (b : Nat) :
    shellAddr L step c b 0 = fileBase + (c.plan.placement.shellOffset + blockOffset (shellOf c) b) := by
  simp [shellAddr, instrOffset_zero]

theorem shell_get (c : Checked (Machine.frame L step) object) {b : Nat} (hb : b < 46) :
    (shellOf c).blocks[b]? = some (blockAt (shellOf c) b) :=
  blocks_get (by rw [shell_size]; exact hb)

/-- The shell check's facts for a certified machine executable. -/
theorem shell_valid (ce : Machine.Certified L step object) :
    Shell.Valid (shellOf ce.checked) ce.checked.bytes ce.checked.plan.placement.shellOffset
      (Machine.exportAt object ce.checked.plan.placement) := ce.shell

/-- The file lies inside the address space. -/
theorem file_fit (ce : Machine.Certified L step object) : fileBase + ce.checked.bytes.size < 2 ^ 64 := by
  have h := Machine.fileFacts ce.checked
  have hd : dataBase = 268435456 := rfl
  rw [h.size]
  have := h.below
  omega

/-- A shell address is inside the address space. -/
theorem shellAddr_lt (ce : Machine.Certified L step object) {b j : Nat}
    (h : shellAddr L step ce.checked b j < fileBase + ce.checked.bytes.size) : shellAddr L step ce.checked b j < 2 ^ 64 := by
  have := file_fit ce
  omega

variable (ce : Machine.Certified L step object)

/-- A linear instruction of the machine shell, as a step to the next instruction. -/
theorem mstep_ok {b j : Nat} (hb : b < 46) {i : X86.Instr}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t)
    {s : ByteEval.State} (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b j)) {core : Core}
    {fl : ByteEval.Flags}
    (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Shell.Instr.size (.instr i)), fl⟩) :
    ByteEval.step ce.checked.bytes fetchBase s = .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked b (j + 1)), fl⟩ :=
  (shell_valid ce).step_ok (file_fit ce) (shell_get ce.checked hb) hi hnc hrip hex

/-- A linear instruction of the machine shell that faults on memory. -/
theorem mstep_fault {b j : Nat} (hb : b < 46) {i : X86.Instr}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr i)) (hnc : ∀ t, i ≠ .call t)
    {s : ByteEval.State} (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b j)) {f : MemoryFault}
    (hex : ByteEval.execute ⟨instructionOperation i, Shell.Instr.size (.instr i)⟩ s = .error (.memory f)) :
    ByteEval.step ce.checked.bytes fetchBase s = .error (.memory f) :=
  (shell_valid ce).step_fault (file_fit ce) (shell_get ce.checked hb) hi hnc hrip hex

/-- A branch terminator of the machine shell. -/
theorem mrun_branch {b : Nat} (hb : b < 46) {o : Op} {args : List Arg} {cond : Condition} {yes no : BlockId}
    (hterm : (blockAt (shellOf ce.checked) b).terminator = .branch o args cond yes no .rel32) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b (blockAt (shellOf ce.checked) b).instructions.size))
    {core : Core} {fl : ByteEval.Flags} {taken : Bool}
    (hex : ByteEval.execute ⟨.op o args, (Encode.encodeOp o args).size⟩ s =
      .ok ⟨core, s.rip + UInt64.ofNat (Encode.encodeOp o args).size, fl⟩)
    (htest : fl.test cond = some taken) :
    ByteEval.run ce.checked.bytes fetchBase (if taken then 2 else 3) s =
      .ok ⟨core, UInt64.ofNat (shellAddr L step ce.checked (if taken then yes else no).toNat 0), fl⟩ := by
  rw [shellAddr_zero]
  exact (shell_valid ce).run_branch (file_fit ce) (shell_get ce.checked hb) hterm hrip hex htest

/-- A jump terminator of the machine shell. -/
theorem mstep_jump {b : Nat} (hb : b < 46) {t : BlockId}
    (hterm : (blockAt (shellOf ce.checked) b).terminator = .jump t) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b (blockAt (shellOf ce.checked) b).instructions.size)) :
    ByteEval.step ce.checked.bytes fetchBase s = .ok { s with rip := UInt64.ofNat (shellAddr L step ce.checked t.toNat 0) } := by
  rw [shellAddr_zero]
  exact (shell_valid ce).step_jump (file_fit ce) (shell_get ce.checked hb) hterm hrip

/-- The `ret` terminator of the machine shell. -/
theorem mstep_ret {b : Nat} (hb : b < 46) (hterm : (blockAt (shellOf ce.checked) b).terminator = .ret)
    {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b (blockAt (shellOf ce.checked) b).instructions.size)) :
    ByteEval.step ce.checked.bytes fetchBase s =
      match s.core.memory.read64? (s.core.readReg .rsp) with
      | .error fault => .error (.memory fault)
      | .ok target => .ok { s with core := s.core.setReg .rsp (s.core.readReg .rsp + 8), rip := target } :=
  (shell_valid ce).step_ret (file_fit ce) (shell_get ce.checked hb) hterm hrip

/-- An internal call of the machine shell. -/
theorem mstep_call {b j : Nat} (hb : b < 46) {t : BlockId}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.instr (.call t))) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b j)) :
    ByteEval.step ce.checked.bytes fetchBase s =
      match s.core.memory.write64? (s.core.readReg .rsp - 8) (UInt64.ofNat (shellAddr L step ce.checked b (j + 1))) with
      | .error fault => .error (.memory fault)
      | .ok memory => .ok {
          core := { s.core.setReg .rsp (s.core.readReg .rsp - 8) with memory }
          rip := UInt64.ofNat (shellAddr L step ce.checked t.toNat 0), flags := s.flags } := by
  rw [shellAddr_zero]
  exact (shell_valid ce).step_call (file_fit ce) (shell_get ce.checked hb) hi hrip

/-- An export call of the machine shell lands on the export. -/
theorem mcallsTo {b j : Nat} (hb : b < 46) {name : String}
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some (.callExport name)) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b j)) :
    ∃ offset, ELF.symbol? object name = some offset ∧
      CallsTo ce.checked.bytes s (UInt64.ofNat (fileBase + ce.checked.plan.placement.textOffset) + UInt64.ofNat offset) := by
  obtain ⟨t, ht, hc⟩ := (shell_valid ce).callsTo (file_fit ce) (shell_get ce.checked hb) hi hrip
  simp only [Machine.exportAt, Option.map_eq_some_iff] at ht
  obtain ⟨offset, hoff, rfl⟩ := ht
  refine ⟨offset, hoff, ?_⟩
  rw [← UInt64.ofNat_add, Nat.add_assoc]
  exact hc

/-- A `syscall` of the machine shell. -/
theorem msyscall_at {b j : Nat} (hb : b < 46)
    (hi : (blockAt (shellOf ce.checked) b).instructions[j]? = some .syscall) {s : ByteEval.State}
    (hrip : s.rip = UInt64.ofNat (shellAddr L step ce.checked b j)) :
    Decode.decodeAt ce.checked.bytes (s.rip - fetchBase).toNat = none ∧ syscallAt ce.checked.bytes s.rip ∧
      s.rip + 2 = UInt64.ofNat (shellAddr L step ce.checked b (j + 1)) :=
  (shell_valid ce).syscall_at (file_fit ce) (shell_get ce.checked hb) hi hrip

end

/-! ## The shell's blocks, stated

`Machine.lean`'s builders are private, so the blocks are stated here with
public ones (`SB`), each block by its own `rfl` lemma: the elaborator unfolds
the shell once per lemma, and a proof that uses a block reads its
instructions off the stated literal. -/

namespace SB

abbrev mI (r : GPR) (v : Nat) : Shell.Instr := .instr (Instr.mov .w64 r (.imm (UInt64.ofNat v)))
abbrev mR (d s : GPR) : Shell.Instr := .instr (Instr.mov .w64 d (.reg s))
abbrev at_ (b : GPR) (disp : Nat := 0) : MemAddr :=
  { base := some b, index := none, scale := .one, displacement := UInt32.ofNat disp }
abbrev ld (d : GPR) (a : MemAddr) : Shell.Instr := .instr (Instr.load .w64 d a)
abbrev ld8 (d : GPR) (a : MemAddr) : Shell.Instr := .instr (Instr.load .w8 d a)
abbrev st (a : MemAddr) (s : GPR) : Shell.Instr := .instr (Instr.store .w64 a s)
abbrev st8 (a : MemAddr) (s : GPR) : Shell.Instr := .instr (Instr.store .w8 a s)
abbrev addI (r : GPR) (v : Nat) : Shell.Instr := .instr (Instr.alu .add .w64 r (.imm (UInt32.ofNat v)))
abbrev subI (r : GPR) (v : Nat) : Shell.Instr := .instr (Instr.alu .sub .w64 r (.imm (UInt32.ofNat v)))
abbrev andI (r : GPR) (v : Nat) : Shell.Instr := .instr (Instr.alu .and .w64 r (.imm (UInt32.ofNat v)))
abbrev addR (d s : GPR) : Shell.Instr := .instr (Instr.alu .add .w64 d (.reg s))
abbrev subR (d s : GPR) : Shell.Instr := .instr (Instr.alu .sub .w64 d (.reg s))
abbrev shrI (r : GPR) (v : Nat) : Shell.Instr :=
  .instr (.op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)])
abbrev cmpI (r : GPR) (v : Nat) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .imm (UInt32.ofNat v) } c (UInt32.ofNat t) (UInt32.ofNat f)
abbrev cmpR (r s : GPR) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .reg s } c (UInt32.ofNat t) (UInt32.ofNat f)
abbrev ifNz (r : GPR) (t f : Nat) : Terminator :=
  .branch { mn := .test, w := .w64, form := .MR } [.reg r, .reg r] .ne (UInt32.ofNat t) (UInt32.ofNat f)
abbrev jmp (b : Nat) : Terminator := .jump (UInt32.ofNat b)

end SB

open SB

section
variable (L : Machine.Layout) (step : String) (data : Nat)

theorem block_start : blockAt (Machine.shell L step data) 0 =
    ⟨#[mI .rax 157, mI .rdi 38, mI .rsi 1, mI .rdx 0, mI .r10 0, mI .r8 0, .syscall], ifNz .rax 45 1⟩ := rfl
theorem block_seccomp : blockAt (Machine.shell L step data) 1 =
    ⟨#[mI .rax 317, mI .rdi 1, mI .rsi 0, mI .rdx (fprogAddr data), .syscall], ifNz .rax 45 2⟩ := rfl
theorem block_args : blockAt (Machine.shell L step data) 2 =
    ⟨#[ld .rbx (at_ .rsp), .instr (Instr.lea .r12 (at_ .rsp 8)), mI .r10 L.callTop], cmpI .rbx 0 .eq 3 4⟩ := rfl
theorem block_argsNone : blockAt (Machine.shell L step data) 3 =
    ⟨#[st (at_ .r10 16) .r12, mI .rax 0, st (at_ .r10 8) .rax], jmp 5⟩ := rfl
theorem block_argsSome : blockAt (Machine.shell L step data) 4 =
    ⟨#[mR .rax .rbx, subI .rax 1, st (at_ .r10 8) .rax, addI .r12 8, st (at_ .r10 16) .r12, ld .rcx (at_ .r12),
      st (at_ .r10 24) .rcx], jmp 5⟩ := rfl
theorem block_setup : blockAt (Machine.shell L step data) 5 =
    ⟨#[mI .rax 0, st (at_ .r10) .rax, mI .r11 L.shellTop, mR .rsp .r11], jmp 6⟩ := rfl
theorem block_loop : blockAt (Machine.shell L step data) 6 =
    ⟨#[mI .r14 L.regionStart, mI .rax L.budget, st (at_ .r14 16) .rax, mR .rdi .r14, mI .rsi L.region,
      mI .rdx L.budget, mI .rcx 0, mI .r8 0, mI .r9 0, mI .r11 L.callTop, mR .rsp .r11, .callExport initSymbol,
      mI .r11 L.callTop], cmpR .rsp .r11 .ne 42 7⟩ := rfl
theorem block_initBack : blockAt (Machine.shell L step data) 7 =
    ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 8⟩ := rfl
theorem block_callStep : blockAt (Machine.shell L step data) 8 =
    ⟨#[mI .r10 L.callTop, ld .rsi (at_ .r10), ld .rdx (at_ .r10 8), mI .rdi L.regionStart, mI .rcx 0, mI .r8 0,
      mI .r9 0, mI .r11 L.callTop, mR .rsp .r11, .callExport step, mI .r11 L.callTop], cmpR .rsp .r11 .ne 42 9⟩ := rfl
theorem block_stepBack : blockAt (Machine.shell L step data) 9 =
    ⟨#[mI .r11 L.shellTop, mR .rsp .r11], ifNz .rax 28 10⟩ := rfl
theorem block_decode : blockAt (Machine.shell L step data) 10 =
    ⟨#[mR .rcx .rdx, .instr (Instr.alu .and .w32 .rcx (.imm 1))], cmpI .rcx 0 .eq 43 11⟩ := rfl
theorem block_split : blockAt (Machine.shell L step data) 11 =
    ⟨#[shrI .rdx 1, mR .rax .rdx, andI .rax 2047, shrI .rdx 11, mI .r10 L.callTop, st (at_ .r10) .rdx,
      mR .rcx .rax, andI .rcx 7, shrI .rax 3], cmpI .rcx 0 .eq 12 13⟩ := rfl
theorem block_kindArg : blockAt (Machine.shell L step data) 12 = ⟨#[], cmpI .rax 0 .ne 44 16⟩ := rfl
theorem block_kind1 : blockAt (Machine.shell L step data) 13 = ⟨#[], cmpI .rcx 1 .eq 21 14⟩ := rfl
theorem block_kind2 : blockAt (Machine.shell L step data) 14 = ⟨#[], cmpI .rcx 2 .eq 22 15⟩ := rfl
theorem block_kind3 : blockAt (Machine.shell L step data) 15 = ⟨#[], cmpI .rcx 3 .eq 26 44⟩ := rfl
theorem block_arg : blockAt (Machine.shell L step data) 16 =
    ⟨#[mI .r10 L.callTop, ld .r11 (at_ .r10 16), ld .rsi (at_ .r11)], cmpI .rsi 0 .eq 17 18⟩ := rfl
theorem block_noMore : blockAt (Machine.shell L step data) 17 =
    ⟨#[mI .rax 257, st (at_ .r10 8) .rax], jmp 6⟩ := rfl
theorem block_argByte : blockAt (Machine.shell L step data) 18 =
    ⟨#[ld .rsi (at_ .r10 24), ld8 .rax (at_ .rsi)], cmpI .rax 0 .eq 20 19⟩ := rfl
theorem block_argNext : blockAt (Machine.shell L step data) 19 =
    ⟨#[addI .rsi 1, st (at_ .r10 24) .rsi, st (at_ .r10 8) .rax], jmp 6⟩ := rfl
theorem block_argEnd : blockAt (Machine.shell L step data) 20 =
    ⟨#[mI .rax 256, st (at_ .r10 8) .rax, addI .r11 8, st (at_ .r10 16) .r11, ld .rcx (at_ .r11),
      st (at_ .r10 24) .rcx], jmp 6⟩ := rfl
theorem block_out : blockAt (Machine.shell L step data) 21 = ⟨#[mI .rdi 1], jmp 23⟩ := rfl
theorem block_err : blockAt (Machine.shell L step data) 22 = ⟨#[mI .rdi 2], jmp 23⟩ := rfl
theorem block_write1 : blockAt (Machine.shell L step data) 23 =
    ⟨#[mI .r10 L.callTop, st8 (at_ .r10 32) .rax, .instr (Instr.lea .rsi (at_ .r10 32)), mI .rdx 1, mI .rax 1,
      .syscall], cmpI .rax 1 .eq 24 25⟩ := rfl
theorem block_written : blockAt (Machine.shell L step data) 24 =
    ⟨#[mI .r10 L.callTop, mI .rax 0, st (at_ .r10 8) .rax], jmp 6⟩ := rfl
theorem block_notWritten : blockAt (Machine.shell L step data) 25 =
    ⟨#[mI .r10 L.callTop, mI .rax 1, st (at_ .r10 8) .rax], jmp 6⟩ := rfl
theorem block_exitCode : blockAt (Machine.shell L step data) 26 = ⟨#[mR .rdi .rax], jmp 27⟩ := rfl
theorem block_exit : blockAt (Machine.shell L step data) 27 = ⟨#[mI .rax 60, .syscall], jmp 27⟩ := rfl
theorem block_fail1 : blockAt (Machine.shell L step data) 28 = ⟨#[], cmpI .rax 1 .eq 38 29⟩ := rfl
theorem block_fail2 : blockAt (Machine.shell L step data) 29 = ⟨#[], cmpI .rax 2 .eq 39 30⟩ := rfl
theorem block_fail3 : blockAt (Machine.shell L step data) 30 = ⟨#[], cmpI .rax 3 .eq 40 31⟩ := rfl
theorem block_fail4 : blockAt (Machine.shell L step data) 31 = ⟨#[], cmpI .rax 4 .eq 41 42⟩ := rfl
theorem block_report : blockAt (Machine.shell L step data) 32 =
    ⟨#[mI .r11 L.shellTop, mR .rsp .r11, mI .rdi 2, .instr (.call (UInt32.ofNat 33)), mR .rdi .r15], jmp 27⟩ := rfl
theorem block_write : blockAt (Machine.shell L step data) 33 = ⟨#[], cmpI .rdx 0 .eq 36 34⟩ := rfl
theorem block_writeSys : blockAt (Machine.shell L step data) 34 =
    ⟨#[mI .rax 1, .syscall], cmpI .rax 0 .signedLe 37 35⟩ := rfl
theorem block_writeAdv : blockAt (Machine.shell L step data) 35 = ⟨#[addR .rsi .rax, subR .rdx .rax], jmp 33⟩ := rfl
theorem block_writeRet : blockAt (Machine.shell L step data) 36 = ⟨#[], .ret⟩ := rfl
theorem block_writeErr : blockAt (Machine.shell L step data) 37 = ⟨#[mI .rdi 74], jmp 27⟩ := rfl

/-- A message block (the shell's `messageBlock`): the message's address and length, its status,
then the report. -/
def msgBlock (data : Nat) (f : Machine.Failure) : Shell.Block :=
  ⟨#[mI .rsi (Machine.messageAt data f).1, mI .rdx (Machine.messageAt data f).2, mI .r15 f.status], jmp 32⟩

theorem block_heap : blockAt (Machine.shell L step data) 38 = msgBlock data .heap := rfl
theorem block_stack : blockAt (Machine.shell L step data) 39 = msgBlock data .stack := rfl
theorem block_natOverflow : blockAt (Machine.shell L step data) 40 = msgBlock data .natOverflow := rfl
theorem block_trap : blockAt (Machine.shell L step data) 41 = msgBlock data .trap := rfl
theorem block_abi : blockAt (Machine.shell L step data) 42 = msgBlock data .abi := rfl
theorem block_notValue : blockAt (Machine.shell L step data) 43 = msgBlock data .notValue := rfl
theorem block_request : blockAt (Machine.shell L step data) 44 = msgBlock data .request := rfl
theorem block_confine : blockAt (Machine.shell L step data) 45 = msgBlock data .confine := rfl

theorem message_index (f : Machine.Failure) : Machine.B.message f < 46 := by cases f <;> decide

theorem block_message (f : Machine.Failure) :
    blockAt (Machine.shell L step data) (Machine.B.message f) = msgBlock data f := by
  cases f
  · exact block_heap L step data
  · exact block_stack L step data
  · exact block_natOverflow L step data
  · exact block_trap L step data
  · exact block_abi L step data
  · exact block_notValue L step data
  · exact block_request L step data
  · exact block_confine L step data

end

end IxCC.X86.Exe.Process
