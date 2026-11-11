import IxCC.X86.Exe.Validate
import IxCC.Exe.Machine

/-!
# The generic shell of a numeric state machine

`ixcc compile --exe FILE --machine` writes the executable of a numeric state
machine (`IxCC/Exe/Machine.lean`): a root `step : Nat → Nat → Nat` run by
this shell, a `Shell.Program` encoded by the compiler's own encoder and laid
out by the frame writer (`writeFor`). The shell is the same for every
machine: its constants are the memory layout, its read-only data's address
and the step's export symbol. It parses and renders nothing; a program does
that in Lean (`IxCC/lib/IxccExe.lean`). It is trusted code: nothing here
proves that it does what this note says (`docs/trusted-extern-ledger.md`,
`x86-linux-machine-shell`).

**What it does.**
1. It confines the process before anything else, as `--exe`'s shell does:
   `prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)`, then `seccomp` with that shell's
   filter (`X86.Exe.filter`: only `write` to file descriptor 1 or 2, and
   `exit`); a refusal ends the run with status 75.
2. It reads `argc` and `argv` from the initial stack (System V x86-64 psABI,
   "Process Initialization") into an argument cursor: the slot of the current
   argument (from `argv[1]`) and the next byte in it. With `argc = 0` there
   are no arguments.
3. It keeps the state, the event, the cursor and a one-byte output buffer in
   its own 256 bytes above the call stack's top, outside the region and the
   call stack: it relies on nothing a call leaves in the registers. The first
   call gets state 0 and event `argc − 1`.
4. Each iteration stores the stack budget at `region + 16`, sets `rsp` to the
   call top and calls `cx_init(region, size, budget)`, then
   `step(region, state, event)` (`rcx`, `r8`, `r9` zero), checking after each
   that `rsp` came back (status 70) and mapping a nonzero status to 65 to 68
   (70 for an unknown one). The region is re-initialised for every call:
   nothing of the program outlives a call.
5. It checks that the result word is a `Nat`'s (odd; status 71), splits its
   value into the next state (`/ 2048`) and the request field (`% 2048`), and
   performs the request: `arg` moves the cursor and answers the byte, 256 at
   the end of an argument or 257 after the last; `write` writes the one byte
   to file descriptor 1 or 2 and answers 0 if the kernel wrote it, else 1;
   `exit` ends the process with the program's status; any other field ends
   the run with status 72.
6. A failure writes a fixed message to standard error (status 74 if that
   write fails) and exits with its status.

So a run makes `prctl`, `seccomp`, then `write` to 1 or 2 and finally `exit`.

**Memory** (`Layout`): the program stack and the shell's 256 bytes in one
zero-filled segment at `dataBase` (the stack below the call top, the shell's
bytes above it); the region in a zero-filled segment of its own, one unmapped
page above, with nothing mapped right below it or past its last page.
`Layout.driver_canonicalOk` proves the driver contract at every call site and
for every initial bytes (a call's memory is whatever the previous call left).
-/

namespace IxCC.X86.Exe.Machine

open IxCC.X86 IxCC.X86.Exe

/-! ## Memory -/

/-- The stack and the region, in bytes. The defaults are `--exe`'s. -/
structure Layout where
  stack : Nat := 8 * 2 ^ 20
  region : Nat := 64 * 2 ^ 20
  deriving BEq, Repr, Inhabited

/-- The shell's own bytes above the call top: the state (at 0), the event
(8), the cursor's argument slot (16) and byte (24), the output byte (32),
and the shell's stack up to 256. -/
def scratch : Nat := 256

/-- The unmapped page between the stack segment and the region. -/
def gap : Nat := 0x1000

namespace Layout

/-- The stack segment: the stack and the shell's bytes, in pages. -/
def stackArea (L : Layout) : Nat := alignUp (L.stack + scratch) 0x1000
/-- The stack pointer each call is entered with, before its return address. -/
def callTop (L : Layout) : Nat := dataBase + L.stackArea - scratch
/-- The top of the shell's own stack. -/
def shellTop (L : Layout) : Nat := dataBase + L.stackArea
def regionStart (L : Layout) : Nat := dataBase + L.stackArea + gap
def budget (L : Layout) : Nat := L.stack - stackReserve

/-- The zero-filled segments: the stack segment, then the region's. -/
def segments (L : Layout) : List (Nat × Nat) :=
  [(dataBase, L.stackArea), (L.regionStart, alignUp L.region 0x1000)]

/-- The sizes the writer accepts: a stack that is a multiple of 16 and at least
8 KiB, a region of at least `cx_init`'s 4 KiB, and both segments with the gap
at most `maxDataBytes`. -/
def check (L : Layout) : Bool :=
  L.stack % 16 == 0 && decide (8192 ≤ L.stack) && decide (4096 ≤ L.region) &&
    decide (L.stackArea + gap + alignUp L.region 0x1000 ≤ maxDataBytes)

/-- The driver a call whose return address is `ret` is meant to see, for object
text at file offset `textOffset`, from the bytes `init`. -/
def driverWith (L : Layout) (textOffset ret : Nat) (init : Word → UInt8) : Driver where
  base := UInt64.ofNat (fileBase + textOffset)
  region := UInt64.ofNat L.regionStart
  size := UInt64.ofNat L.region
  budget := UInt64.ofNat L.budget
  sp := UInt64.ofNat (L.callTop - 8)
  ret := UInt64.ofNat ret
  init
  flags := {}
  other := fun _ => 0

/-- The driver of the first call, from the loader's zeros. -/
def driver (L : Layout) (textOffset ret : Nat) : Driver := L.driverWith textOffset ret fun _ => 0

private theorem toNat_small {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (by show n < 18446744073709551616; omega)

/-- **The layout keeps the driver contract** at every call: for a layout
`check` accepts, object text below the return address and a return address
below the zero-filled segments, every clause of `Driver.CanonicalOk` holds,
whatever the bytes the call starts from. -/
theorem driver_canonicalOk (L : Layout) (hL : L.check = true) {textOffset textSize ret : Nat}
    (hText : fileBase + textOffset + textSize ≤ ret) (hRet : ret < dataBase) (init : Word → UInt8) :
    (L.driverWith textOffset ret init).CanonicalOk textSize := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨h16, hs⟩, hr⟩, hmax⟩ := hL
  simp only [maxDataBytes, stackArea, gap, alignUp, scratch] at hmax
  have hd : dataBase = 268435456 := rfl
  have hf : fileBase = 4194304 := rfl
  have hbase : (UInt64.ofNat (fileBase + textOffset)).toNat = fileBase + textOffset :=
    toNat_small (by omega)
  have hreg : (UInt64.ofNat L.regionStart).toNat = L.regionStart :=
    toNat_small (by simp only [regionStart, stackArea, gap, alignUp, scratch]; omega)
  have hsize : (UInt64.ofNat L.region).toNat = L.region := toNat_small (by omega)
  have hbud : (UInt64.ofNat L.budget).toNat = L.budget :=
    toNat_small (by simp only [budget, stackReserve]; omega)
  have hsp : (UInt64.ofNat (L.callTop - 8)).toNat = L.callTop - 8 :=
    toNat_small (by simp only [callTop, stackArea, alignUp, scratch]; omega)
  have hret : (UInt64.ofNat ret).toNat = ret := toNat_small (by omega)
  have hsub : (UInt64.ofNat ret - UInt64.ofNat (fileBase + textOffset)).toNat =
      ret - (fileBase + textOffset) := by
    rw [UInt64.toNat_sub_of_le]
    · rw [hret, hbase]
    · rw [UInt64.le_iff_toNat_le, hret, hbase]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [driverWith, hbase, hreg, hsize, hbud, hsp, hret, hsub] <;>
    (try simp only [regionStart, callTop, budget, stackReserve, stackArea, gap, alignUp, scratch]) <;>
    omega

/-- The segments a checked layout gives are ones the writer accepts. -/
theorem segmentsOk_of_check (L : Layout) (hL : L.check = true) : segmentsOk L.segments = true := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨_, hs⟩, hr⟩, hmax⟩ := hL
  simp only [maxDataBytes, stackArea, gap, alignUp, scratch] at hmax
  simp only [segments, segmentsOk, regionStart, stackArea, gap, alignUp, scratch, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq]
  have hd : dataBase = 268435456 := rfl
  omega

/-- The default layout (an 8 MiB stack and a 64 MiB region) is accepted. -/
theorem default_check : ({} : Layout).check = true := by decide

end Layout

/-! ## The read-only data -/

/-- The shell's failures, each with a message on standard error and a status. -/
inductive Failure where
  | heap | stack | natOverflow | trap | abi | notValue | request | confine
  deriving BEq, DecidableEq, Repr, Inhabited

def Failure.all : List Failure := [.heap, .stack, .natOverflow, .trap, .abi, .notValue, .request, .confine]

/-- The messages: `--exe`'s, and one for a request outside the interface. -/
def Failure.text : Failure → String
  | .heap => Message.text 0 .heap
  | .stack => Message.text 0 .stack
  | .natOverflow => Message.text 0 .natOverflow
  | .trap => Message.text 0 .trap
  | .abi => Message.text 0 .abi
  | .notValue => Message.text 0 .notValue
  | .request => "ixcc: the program made a request outside the platform interface\n"
  | .confine => Message.text 0 .confine

def Failure.status : Failure → Nat
  | .heap => IxCC.Exe.Machine.statusOf .heap
  | .stack => IxCC.Exe.Machine.statusOf .stack
  | .natOverflow => IxCC.Exe.Machine.statusOf .natOverflow
  | .trap => IxCC.Exe.Machine.statusTrap
  | .abi => IxCC.Exe.Machine.statusAbi
  | .notValue => IxCC.Exe.Machine.statusNotValue
  | .request => IxCC.Exe.Machine.statusRequest
  | .confine => IxCC.Exe.Machine.statusConfine

/-- The read-only data at `addr` (8-aligned): `--exe`'s seccomp filter, its
`struct sock_fprog`, then the messages. -/
def dataBytes (addr : Nat) : ByteArray :=
  ⟨(filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 addr ++
    (Failure.all.flatMap fun (f : Failure) => f.text.toUTF8.toList)).toArray⟩

/-- The address and length of a failure's message. -/
def messageAt (addr : Nat) (f : Failure) : Nat × Nat :=
  let before := Failure.all.takeWhile (· != f)
  (fprogAddr addr + 16 + (before.map fun (g : Failure) => g.text.utf8ByteSize).sum, f.text.utf8ByteSize)

/-! ## The code -/

section Builders

private def ins (i : X86.Instr) : Shell.Instr := .instr i
private def movI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.mov .w64 r (.imm (UInt64.ofNat v)))
private def movR (d s : GPR) : Shell.Instr := ins (X86.Instr.mov .w64 d (.reg s))
private def at_ (b : GPR) (disp : Nat := 0) : MemAddr :=
  { base := some b, index := none, scale := .one, displacement := UInt32.ofNat disp }
private def ld (d : GPR) (a : MemAddr) : Shell.Instr := ins (X86.Instr.load .w64 d a)
private def ld8 (d : GPR) (a : MemAddr) : Shell.Instr := ins (X86.Instr.load .w8 d a)
private def st (a : MemAddr) (s : GPR) : Shell.Instr := ins (X86.Instr.store .w64 a s)
private def st8 (a : MemAddr) (s : GPR) : Shell.Instr := ins (X86.Instr.store .w8 a s)
private def addI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.alu .add .w64 r (.imm (UInt32.ofNat v)))
private def subI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.alu .sub .w64 r (.imm (UInt32.ofNat v)))
private def andI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.alu .and .w64 r (.imm (UInt32.ofNat v)))
private def addR (d s : GPR) : Shell.Instr := ins (X86.Instr.alu .add .w64 d (.reg s))
private def subR (d s : GPR) : Shell.Instr := ins (X86.Instr.alu .sub .w64 d (.reg s))
private def shrI (r : GPR) (v : Nat) : Shell.Instr :=
  ins (.op { mn := .shr, w := .w64, form := .MI } [.reg r, .imm (UInt64.ofNat v)])
private def call (b : Nat) : Shell.Instr := ins (.call (UInt32.ofNat b))

private def cmpI (r : GPR) (v : Nat) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .imm (UInt32.ofNat v) } c (UInt32.ofNat t) (UInt32.ofNat f)
private def cmpR (r s : GPR) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .reg s } c (UInt32.ofNat t) (UInt32.ofNat f)
/-- `test r, r` and branch if nonzero. -/
private def ifNonzero (r : GPR) (t f : Nat) : Terminator :=
  .branch { mn := .test, w := .w64, form := .MR } [.reg r, .reg r] .ne (UInt32.ofNat t) (UInt32.ofNat f)
private def jump (b : Nat) : Terminator := .jump (UInt32.ofNat b)
private def blk (is : Array Shell.Instr) (t : Terminator) : Shell.Block := { instructions := is, terminator := t }

end Builders

/-! Block numbers. -/
namespace B
def start := 0
def seccomp := 1
def args := 2
def argsNone := 3
def argsSome := 4
def setup := 5
def loop := 6
def initBack := 7
def callStep := 8
def stepBack := 9
def decode := 10
def split := 11
def kindArg := 12
def kind1 := 13
def kind2 := 14
def kind3 := 15
def arg := 16
def noMore := 17
def argByte := 18
def argNext := 19
def argEnd := 20
def out := 21
def err := 22
def write1 := 23
def written := 24
def notWritten := 25
def exitCode := 26
def exit := 27
def fail1 := 28
def fail2 := 29
def fail3 := 30
def fail4 := 31
def report := 32
def write := 33
def writeSys := 34
def writeAdv := 35
def writeRet := 36
def writeErr := 37
/-- The message blocks, in `Failure.all`'s order. -/
def message (f : Failure) : Nat := 38 + (Failure.all.takeWhile (· != f)).length
end B

/-- A message block: the message's address and length, its status, then the
report. -/
private def messageBlock (data : Nat) (f : Failure) : Shell.Block :=
  let (a, n) := messageAt data f
  blk #[movI .rsi a, movI .rdx n, movI .r15 f.status] (jump B.report)

/-- The shell for layout `L`, calling `cx_init` and `step`, with its read-only
data at `data` (see the module note). Its own bytes are at `C = callTop`:
the state at `C`, the event at `C + 8`, the argument slot at `C + 16`, the
argument byte's address at `C + 24`, the output byte at `C + 32`; its stack
ends at `C + 256`. -/
def shell (L : Layout) (step : String) (data : Nat) : Shell.Program :=
  let C := L.callTop
  let body : Array Shell.Block := #[
    -- start: prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)
    blk #[movI .rax 157, movI .rdi 38, movI .rsi 1, movI .rdx 0, movI .r10 0, movI .r8 0, .syscall]
      (ifNonzero .rax (B.message .confine) B.seccomp),
    -- seccomp(SECCOMP_SET_MODE_FILTER, 0, &program)
    blk #[movI .rax 317, movI .rdi 1, movI .rsi 0, movI .rdx (fprogAddr data), .syscall]
      (ifNonzero .rax (B.message .confine) B.args),
    -- args: rbx argc, r12 argv
    blk #[ld .rbx (at_ .rsp), ins (X86.Instr.lea .r12 (at_ .rsp 8)), movI .r10 C]
      (cmpI .rbx 0 .eq B.argsNone B.argsSome),
    -- argsNone: the slot argv[0], which is null; event 0
    blk #[st (at_ .r10 16) .r12, movI .rax 0, st (at_ .r10 8) .rax] (jump B.setup),
    -- argsSome: event argc - 1, the slot argv[1] and its first byte
    blk #[movR .rax .rbx, subI .rax 1, st (at_ .r10 8) .rax, addI .r12 8, st (at_ .r10 16) .r12,
        ld .rcx (at_ .r12), st (at_ .r10 24) .rcx]
      (jump B.setup),
    -- setup: state 0, the shell's own stack
    blk #[movI .rax 0, st (at_ .r10) .rax, movI .r11 L.shellTop, movR .rsp .r11] (jump B.loop),
    -- loop: the budget at region + 16, then cx_init(region, size, budget)
    blk #[movI .r14 L.regionStart, movI .rax L.budget, st (at_ .r14 16) .rax, movR .rdi .r14,
        movI .rsi L.region, movI .rdx L.budget, movI .rcx 0, movI .r8 0, movI .r9 0,
        movI .r11 C, movR .rsp .r11, .callExport initSymbol, movI .r11 C]
      (cmpR .rsp .r11 .ne (B.message .abi) B.initBack),
    -- initBack
    blk #[movI .r11 L.shellTop, movR .rsp .r11] (ifNonzero .rax B.fail1 B.callStep),
    -- callStep: step(region, state, event)
    blk #[movI .r10 C, ld .rsi (at_ .r10), ld .rdx (at_ .r10 8), movI .rdi L.regionStart,
        movI .rcx 0, movI .r8 0, movI .r9 0, movI .r11 C, movR .rsp .r11, .callExport step, movI .r11 C]
      (cmpR .rsp .r11 .ne (B.message .abi) B.stepBack),
    -- stepBack
    blk #[movI .r11 L.shellTop, movR .rsp .r11] (ifNonzero .rax B.fail1 B.decode),
    -- decode: the word must be odd (a Nat)
    blk #[movR .rcx .rdx, ins (X86.Instr.alu .and .w32 .rcx (.imm 1))]
      (cmpI .rcx 0 .eq (B.message .notValue) B.split),
    -- split: the state to C, rcx the kind, rax the payload
    blk #[shrI .rdx 1, movR .rax .rdx, andI .rax 2047, shrI .rdx 11, movI .r10 C, st (at_ .r10) .rdx,
        movR .rcx .rax, andI .rcx 7, shrI .rax 3]
      (cmpI .rcx 0 .eq B.kindArg B.kind1),
    -- kindArg: arg has no payload
    blk #[] (cmpI .rax 0 .ne (B.message .request) B.arg),
    blk #[] (cmpI .rcx 1 .eq B.out B.kind2),
    blk #[] (cmpI .rcx 2 .eq B.err B.kind3),
    blk #[] (cmpI .rcx 3 .eq B.exitCode (B.message .request)),
    -- arg: r11 the slot, rsi the argument it holds
    blk #[movI .r10 C, ld .r11 (at_ .r10 16), ld .rsi (at_ .r11)] (cmpI .rsi 0 .eq B.noMore B.argByte),
    -- noMore: 257
    blk #[movI .rax 257, st (at_ .r10 8) .rax] (jump B.loop),
    -- argByte: rax the next byte
    blk #[ld .rsi (at_ .r10 24), ld8 .rax (at_ .rsi)] (cmpI .rax 0 .eq B.argEnd B.argNext),
    -- argNext: answer the byte, move on
    blk #[addI .rsi 1, st (at_ .r10 24) .rsi, st (at_ .r10 8) .rax] (jump B.loop),
    -- argEnd: answer 256, the next slot and its first byte
    blk #[movI .rax 256, st (at_ .r10 8) .rax, addI .r11 8, st (at_ .r10 16) .r11, ld .rcx (at_ .r11),
        st (at_ .r10 24) .rcx]
      (jump B.loop),
    -- out, err: the descriptor
    blk #[movI .rdi 1] (jump B.write1),
    blk #[movI .rdi 2] (jump B.write1),
    -- write1: write(rdi, C + 32, 1); 0 if it wrote the byte, else 1
    blk #[movI .r10 C, st8 (at_ .r10 32) .rax, ins (X86.Instr.lea .rsi (at_ .r10 32)), movI .rdx 1,
        movI .rax 1, .syscall]
      (cmpI .rax 1 .eq B.written B.notWritten),
    blk #[movI .r10 C, movI .rax 0, st (at_ .r10 8) .rax] (jump B.loop),
    blk #[movI .r10 C, movI .rax 1, st (at_ .r10 8) .rax] (jump B.loop),
    -- exitCode: the program's status
    blk #[movR .rdi .rax] (jump B.exit),
    -- exit(rdi)
    blk #[movI .rax 60, .syscall] (jump B.exit),
    -- fail: rax is the status
    blk #[] (cmpI .rax 1 .eq (B.message .heap) B.fail2),
    blk #[] (cmpI .rax 2 .eq (B.message .stack) B.fail3),
    blk #[] (cmpI .rax 3 .eq (B.message .natOverflow) B.fail4),
    blk #[] (cmpI .rax 4 .eq (B.message .trap) (B.message .abi)),
    -- report: the message to standard error on the shell's stack, then exit with r15
    blk #[movI .r11 L.shellTop, movR .rsp .r11, movI .rdi 2, call B.write, movR .rdi .r15] (jump B.exit),
    -- write(edi, rsi, rdx) until done; a failure exits 74
    blk #[] (cmpI .rdx 0 .eq B.writeRet B.writeSys),
    blk #[movI .rax 1, .syscall] (cmpI .rax 0 .signedLe B.writeErr B.writeAdv),
    blk #[addR .rsi .rax, subR .rdx .rax] (jump B.write),
    blk #[] .ret,
    blk #[movI .rdi IxCC.Exe.Machine.statusWriteFailed] (jump B.exit)]
  { blocks := body ++ (Failure.all.map (messageBlock data)).toArray }

/-! ## The executable -/

/-- The frame of a machine executable: the shell for `L` calling `cx_init` and
`step`, over the stack segment and the region's. -/
def frame (L : Layout) (step : String) : Frame where
  data := dataBytes
  code := shell L step
  exports := [initSymbol, step]
  segments := L.segments

/-- A checked executable of frame `f` over layout `L`: the frame's check, and
the driver contract at each of the frame's calls into the object, for every
bytes the call starts from. (Stated for any frame, so that the structure's
declaration does not unfold the shell.) -/
structure CertifiedFor (f : Frame) (L : Layout) (object : ByteArray) where
  checked : Checked f object
  contract : ∀ c ∈ checked.plan.calls, ∀ init : Word → UInt8,
    (L.driverWith checked.plan.placement.textOffset c.ret init).CanonicalOk checked.plan.placement.textSize

/-- A checked machine executable: `CertifiedFor` the machine frame. -/
abbrev Certified (L : Layout) (step : String) (object : ByteArray) := CertifiedFor (frame L step) L object

/-- Write the executable of `object` whose step is the export `step`, check
it, and establish the contract at its calls; refuse if any fails. -/
def writeChecked (L : Layout) (step : String) (object : ByteArray) : Except Error (Certified L step object) :=
  if hL : L.check = true then
    match writeFor (frame L step) object with
    | .error e => .error e
    | .ok c =>
      if hc : ∀ x ∈ c.plan.calls, fileBase + c.plan.placement.textOffset + c.plan.placement.textSize ≤ x.ret ∧
          x.ret < dataBase then
        .ok (CertifiedFor.mk c fun x hm init => L.driver_canonicalOk hL (hc x hm).1 (hc x hm).2 init)
      else .error .contract
  else .error .layout

end IxCC.X86.Exe.Machine
