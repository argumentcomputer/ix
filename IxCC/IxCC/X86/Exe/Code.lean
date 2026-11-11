import IxCC.X86.Exe.Shell
import IxCC.X86.Exe.Layout

/-!
# The shell of a standalone executable

The code that runs a compiled root as a Linux process, written as a
`Shell.Program` and encoded by the compiler's own encoder. It is trusted
code: nothing here proves that it does what this note says
(`docs/trusted-extern-ledger.md`).

**What it does, in order.**
1. It confines the process before reading anything: `prctl(PR_SET_NO_NEW_PRIVS,
   1, 0, 0, 0)`, then `seccomp(SECCOMP_SET_MODE_FILTER, 0, &program)` with the
   classic-BPF program `filter`, which kills the process on any system call
   but `write` to file descriptor 1 or 2 and `exit` (and on any architecture
   but x86-64). A refusal of either call ends the run with status 75. (A
   filter, not `SECCOMP_MODE_STRICT`: strict mode cannot be entered under an
   existing filter, such as a build sandbox's, and allows `read`, which the
   shell does not need.)
2. It reads `argc` and `argv` from the initial stack (System V x86-64
   psABI, "Process Initialization"), requires exactly the root's parameter
   count, and parses each argument as a decimal natural number: one or more
   ASCII digits, nothing else (no sign, no space, no prefix, no empty
   argument). A wrong count ends with status 2, an argument that is not a
   numeral with status 3, each with a message on standard error. A numeral of
   `2^64` or more is the model's `natOverflow` (`X86.Linked.call`: an argument
   the driver cannot pass), reported as the wrapper's status 3 is.
3. It stores the stack budget at `region + 16`, sets `rsp` to the stack's top
   and calls `cx_init(region, size, budget)`, then the root's export with the
   region in `rdi` and the arguments in `rsi`…`r9` (zero beyond the arity),
   restoring its own stack pointer after each call (`Layout`'s note says which
   driver each call is meant to see). The export wrappers save and restore
   `rbx`, `rbp` and `r12`–`r15`, where the shell keeps its state.
4. It checks that each call returned with `rsp` restored (status 70
   otherwise), and maps a nonzero status to a message on standard error and
   status `64 + status`: 65 heap, 66 stack, 67 `natOverflow`, 68 trap (70
   for an unknown status).
5. It renders the result: a `Nat` (the word `2n + 1`) in decimal, a
   field-less constructor (the word `2k + 1`, `k` below the constructor count)
   as `#k`, as `Rt.renderObs` prints them, followed
   by a newline; a word of neither shape ends with status 71. It writes the
   line to standard output (status 74 if a write fails) and exits with 0.

So a run makes exactly these system calls: `prctl`, `seccomp`, then `write`
(once, unless the kernel writes part of the line) and `exit`.
-/

namespace IxCC.X86.Exe

open IxCC.X86

/-- What the root returns, as the shell renders it. -/
inductive ResultKind where
  /-- A `Nat`, in decimal. -/
  | nat
  /-- A constructor without fields of an inductive of `ctors` constructors, as
  `#k`. -/
  | enum (ctors : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

/-! ## The read-only data -/

/-- The messages the shell writes to standard error. -/
inductive Message where
  | count | numeral | heap | stack | natOverflow | trap | abi | notValue | confine
  deriving BEq, DecidableEq, Repr, Inhabited

def Message.all : List Message :=
  [.count, .numeral, .heap, .stack, .natOverflow, .trap, .abi, .notValue, .confine]

def Message.text (arity : Nat) : Message → String
  | .count =>
    match arity with
    | 0 => "ixcc: expected no arguments\n"
    | 1 => "ixcc: expected 1 argument, a decimal natural number\n"
    | n => s!"ixcc: expected {n} arguments, each a decimal natural number\n"
  | .numeral => "ixcc: an argument is not a decimal natural number\n"
  | .heap => "ixcc: heap exhausted\n"
  | .stack => "ixcc: stack exhausted\n"
  | .natOverflow => "ixcc: natOverflow (a natural number reached 2^63)\n"
  | .trap => "ixcc: trap\n"
  | .abi => "ixcc: the root returned in breach of the calling convention\n"
  | .notValue => "ixcc: the result is not a value of the root's result type\n"
  | .confine => "ixcc: cannot confine the process with seccomp\n"

/-- The exit status that goes with each message. -/
def Message.status : Message → Nat
  | .count => 2
  | .numeral => 3
  | .heap => 65
  | .stack => 66
  | .natOverflow => 67
  | .trap => 68
  | .abi => 70
  | .notValue => 71
  | .confine => 75

/-- The exit status of a failed write. -/
def writeFailed : Nat := 74

def le16 (v : Nat) : List UInt8 := [UInt8.ofNat v, UInt8.ofNat (v / 256)]
def le32 (v : Nat) : List UInt8 := (List.range 4).map fun i => UInt8.ofNat (v / 256 ^ i)
def le64 (v : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (v / 256 ^ i)

/-- One classic-BPF instruction (`struct sock_filter`): code, the two jump
offsets, the constant. -/
def bpf (code jt jf k : Nat) : List UInt8 := le16 code ++ [UInt8.ofNat jt, UInt8.ofNat jf] ++ le32 k

/-- The seccomp filter, over `struct seccomp_data` (the system-call number at
0, the architecture at 4, the first argument at 16, its high half at 20):
allow `exit` (60), and `write` (1) to file descriptor 1 or 2; kill the process
for anything else or another architecture. -/
def filter : List UInt8 :=
  bpf 0x20 0 0 4 ++                 -- 0: A := arch
  bpf 0x15 0 8 0xC000003E ++        -- 1: x86-64, else kill
  bpf 0x20 0 0 0 ++                 -- 2: A := nr
  bpf 0x15 7 0 60 ++                -- 3: exit: allow
  bpf 0x15 0 5 1 ++                 -- 4: write, else kill
  bpf 0x20 0 0 20 ++                -- 5: A := high half of the descriptor
  bpf 0x15 0 3 0 ++                 -- 6: zero, else kill
  bpf 0x20 0 0 16 ++                -- 7: A := the descriptor
  bpf 0x15 2 0 1 ++                 -- 8: 1: allow
  bpf 0x15 1 0 2 ++                 -- 9: 2: allow, else kill
  bpf 0x06 0 0 0x80000000 ++        -- 10: SECCOMP_RET_KILL_PROCESS
  bpf 0x06 0 0 0x7fff0000           -- 11: SECCOMP_RET_ALLOW

def filterLength : Nat := 12

/-- The read-only data at absolute address `addr` (8-aligned): the filter, its
`struct sock_fprog` (length, padding, pointer), then the messages. -/
def dataBytes (arity addr : Nat) : ByteArray :=
  ⟨(filter ++ le16 filterLength ++ List.replicate 6 (0 : UInt8) ++ le64 addr ++
    (Message.all.flatMap fun (m : Message) => (m.text arity).toUTF8.toList)).toArray⟩

/-- The address of the `struct sock_fprog`. -/
def fprogAddr (addr : Nat) : Nat := addr + 8 * filterLength

/-- The address and length of a message. -/
def messageAt (arity addr : Nat) (m : Message) : Nat × Nat :=
  let before := Message.all.takeWhile (· != m)
  (fprogAddr addr + 16 + (before.map fun (m' : Message) => (m'.text arity).utf8ByteSize).sum, (m.text arity).utf8ByteSize)

/-! ## The code -/

/-- What the shell is built for. -/
structure Spec where
  arity : Nat
  result : ResultKind
  /-- The root's export symbol. -/
  root : String
  layout : Layout
  /-- The absolute address of the read-only data (`dataBytes`). -/
  data : Nat
  deriving Inhabited

/-- The export symbol of `cx_init`. -/
def initSymbol : String := "cx_init"

section Builders

private def ins (i : X86.Instr) : Shell.Instr := .instr i
private def movI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.mov .w64 r (.imm (UInt64.ofNat v)))
private def movR (d s : GPR) : Shell.Instr := ins (X86.Instr.mov .w64 d (.reg s))
private def addr (b : GPR) (disp : Nat := 0) (index : Option IndexReg := none) (scale : Scale := .one) : MemAddr :=
  { base := some b, index, scale, displacement := UInt32.ofNat disp }
private def ld (d : GPR) (a : MemAddr) : Shell.Instr := ins (X86.Instr.load .w64 d a)
private def ld8 (d : GPR) (a : MemAddr) : Shell.Instr := ins (X86.Instr.load .w8 d a)
private def st (a : MemAddr) (s : GPR) : Shell.Instr := ins (X86.Instr.store .w64 a s)
private def st8 (a : MemAddr) (s : GPR) : Shell.Instr := ins (X86.Instr.store .w8 a s)
private def addI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.alu .add .w64 r (.imm (UInt32.ofNat v)))
private def subI (r : GPR) (v : Nat) : Shell.Instr := ins (X86.Instr.alu .sub .w64 r (.imm (UInt32.ofNat v)))
private def addR (d s : GPR) : Shell.Instr := ins (X86.Instr.alu .add .w64 d (.reg s))
private def subR (d s : GPR) : Shell.Instr := ins (X86.Instr.alu .sub .w64 d (.reg s))
private def call (b : Nat) : Shell.Instr := ins (.call (UInt32.ofNat b))

private def cmpI (r : GPR) (v : Nat) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .imm (UInt32.ofNat v) } c (UInt32.ofNat t) (UInt32.ofNat f)
private def cmpR (r s : GPR) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .reg s } c (UInt32.ofNat t) (UInt32.ofNat f)
/-- `test r, r` and branch if nonzero. -/
private def ifNonzero (r : GPR) (t f : Nat) : Terminator :=
  .branch { mn := .test, w := .w64, form := .MR } [.reg r, .reg r] .ne (UInt32.ofNat t) (UInt32.ofNat f)
private def jump (b : Nat) : Terminator := .jump (UInt32.ofNat b)

end Builders

/-! Block numbers. -/
namespace B
def start := 0
def seccomp := 1
def args := 2
def loopInit := 3
def loopHead := 4
def parseArg := 5
def parseErr := 6
def storeArg := 7
def callInit := 8
def initBack := 9
def callRoot := 10
def rootBack := 11
def result := 12
def tag := 13
def render := 14
def digit := 15
def output := 16
def exit := 17
def write := 18
def writeSys := 19
def writeAdv := 20
def writeRet := 21
def writeErr := 22
def parse := 23
def parseLoop := 24
def parseDigit := 25
def parseMul := 26
def parseOvf1 := 27
def parseAdd := 28
def parseOvf2 := 29
def parseNext := 30
def parseDone := 31
def parseBad := 32
def fail := 33
def fail2 := 34
def fail3 := 35
def fail4 := 36
def report := 37
/-- The message blocks, in `Message.all`'s order. -/
def message (m : Message) : Nat := 38 + (Message.all.takeWhile (· != m)).length
end B

/-- A message block: the message's address and length, its status, then the
report. -/
private def messageBlock (s : Spec) (m : Message) : Shell.Block :=
  let (a, n) := messageAt s.arity s.data m
  { instructions := (if m == .abi then #[movR .rsp .rbp] else #[]) ++
      #[movI .rsi a, movI .rdx n, movI .r15 m.status]
    terminator := jump B.report }

/-- The shell (see the module note). Registers: `rbx` argc, `r12` argv, `rbp`
the scratch area on the initial stack (the five argument words at `rbp`, the
output line ending at `rbp + 64`), `r13` the program stack's top, `r14` the
region, `r15` the argument index, later the exit status. -/
def shell (s : Spec) : Shell.Program :=
  let L := s.layout
  let blk (is : Array Shell.Instr) (t : Terminator) : Shell.Block := { instructions := is, terminator := t }
  let body : Array Shell.Block := #[
    -- start: prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)
    blk #[movI .rax 157, movI .rdi 38, movI .rsi 1, movI .rdx 0, movI .r10 0, movI .r8 0, .syscall]
      (ifNonzero .rax (B.message .confine) B.seccomp),
    -- seccomp: seccomp(SECCOMP_SET_MODE_FILTER, 0, &program)
    blk #[movI .rax 317, movI .rdi 1, movI .rsi 0, movI .rdx (fprogAddr s.data), .syscall]
      (ifNonzero .rax (B.message .confine) B.args),
    -- args
    blk #[ld .rbx (addr .rsp), ins (X86.Instr.lea .r12 (addr .rsp 8)), subI .rsp 64, movR .rbp .rsp,
        movI .rax 0, st (addr .rbp 0) .rax, st (addr .rbp 8) .rax, st (addr .rbp 16) .rax,
        st (addr .rbp 24) .rax, st (addr .rbp 32) .rax, movI .r14 L.regionStart, movI .r13 L.stackTop]
      (cmpI .rbx (s.arity + 1) .ne (B.message .count) B.loopInit),
    -- loopInit
    blk #[movI .r15 0] (jump B.loopHead),
    -- loopHead
    blk #[] (cmpI .r15 s.arity .unsignedGe B.callInit B.parseArg),
    -- parseArg: rsi := argv[i + 1]
    blk #[ld .rsi (addr .r12 8 (some .r15) .eight), call B.parse] (cmpI .rdx 0 .ne B.parseErr B.storeArg),
    -- parseErr: 2^64 or more is natOverflow; anything else is not a numeral
    blk #[] (cmpI .rdx 1 .eq (B.message .natOverflow) (B.message .numeral)),
    -- storeArg
    blk #[st (addr .rbp 0 (some .r15) .eight) .rax, addI .r15 1] (jump B.loopHead),
    -- callInit: the budget at region + 16, then cx_init(region, size, budget)
    blk #[movI .rax L.budget, st (addr .r14 16) .rax, movR .rdi .r14, movI .rsi L.region,
        movI .rdx L.budget, movR .rsp .r13, .callExport initSymbol]
      (cmpR .rsp .r13 .ne (B.message .abi) B.initBack),
    -- initBack
    blk #[movR .rsp .rbp] (ifNonzero .rax B.fail B.callRoot),
    -- callRoot: root(region, a1, ..., a5)
    blk #[movR .rdi .r14, ld .rsi (addr .rbp 0), ld .rdx (addr .rbp 8), ld .rcx (addr .rbp 16),
        ld .r8 (addr .rbp 24), ld .r9 (addr .rbp 32), movR .rsp .r13, .callExport s.root]
      (cmpR .rsp .r13 .ne (B.message .abi) B.rootBack),
    -- rootBack
    blk #[movR .rsp .rbp] (ifNonzero .rax B.fail B.result),
    -- result: the value word must be odd
    blk #[movR .rax .rdx, movR .rcx .rdx, ins (X86.Instr.alu .and .w32 .rcx (.imm 1))]
      (cmpI .rcx 0 .eq (B.message .notValue) B.tag),
    -- tag: rax := the number or the constructor index
    blk #[ins (.op { mn := .shr, w := .w64, form := .MI } [.reg .rax, .imm 1])]
      (match s.result with
       | .nat => jump B.render
       | .enum n => cmpI .rax n .unsignedGe (B.message .notValue) B.render),
    -- render: the newline at rbp + 63
    blk #[ins (X86.Instr.lea .rsi (addr .rbp 63)), movI .r8 10, st8 (addr .rsi) .r8] (jump B.digit),
    -- digit: one decimal digit, right to left
    blk #[movI .rdx 0, movI .rcx 10, ins (.op (Op.divM .w64) [.reg .rcx]), addI .rdx 48, subI .rsi 1,
        st8 (addr .rsi) .rdx]
      (ifNonzero .rax B.digit B.output),
    -- output: '#' for a constructor, then write(1, line) and exit(0)
    blk ((match s.result with
          | .nat => #[]
          | .enum _ => #[movI .rdx 35, subI .rsi 1, st8 (addr .rsi) .rdx]) ++
        #[ins (X86.Instr.lea .rdx (addr .rbp 64)), subR .rdx .rsi, movI .rdi 1, call B.write, movI .rdi 0])
      (jump B.exit),
    -- exit(rdi)
    blk #[movI .rax 60, .syscall] (jump B.exit),
    -- write(edi, rsi, rdx) until done
    blk #[] (cmpI .rdx 0 .eq B.writeRet B.writeSys),
    blk #[movI .rax 1, .syscall] (cmpI .rax 0 .signedLe B.writeErr B.writeAdv),
    blk #[addR .rsi .rax, subR .rdx .rax] (jump B.write),
    blk #[] .ret,
    blk #[movI .rdi writeFailed] (jump B.exit),
    -- parse(rsi): rax the value mod 2^64; rdx 0 a numeral, 1 one of 2^64 or more, 2 not a numeral
    blk #[movI .rax 0, movI .r9 0, ld8 .rcx (addr .rsi)] (cmpI .rcx 0 .eq B.parseBad B.parseLoop),
    blk #[ld8 .rcx (addr .rsi)] (cmpI .rcx 0 .eq B.parseDone B.parseDigit),
    blk #[subI .rcx 48] (cmpI .rcx 9 .unsignedGt B.parseBad B.parseMul),
    blk #[movI .r8 10, ins (.op (Op.mulM .w64) [.reg .r8])] (cmpI .rdx 0 .ne B.parseOvf1 B.parseAdd),
    blk #[movI .r9 1] (jump B.parseAdd),
    blk #[] (.branch { mn := .add, w := .w64, form := .MR } [.reg .rax, .reg .rcx] .unsignedLt
      (UInt32.ofNat B.parseOvf2) (UInt32.ofNat B.parseNext)),
    blk #[movI .r9 1] (jump B.parseNext),
    blk #[addI .rsi 1] (jump B.parseLoop),
    blk #[movR .rdx .r9] .ret,
    blk #[movI .rdx 2] .ret,
    -- fail: rax is the status
    blk #[] (cmpI .rax 1 .eq (B.message .heap) B.fail2),
    blk #[] (cmpI .rax 2 .eq (B.message .stack) B.fail3),
    blk #[] (cmpI .rax 3 .eq (B.message .natOverflow) B.fail4),
    blk #[] (cmpI .rax 4 .eq (B.message .trap) (B.message .abi)),
    -- report: the message to standard error, then exit with r15
    blk #[movI .rdi 2, call B.write, movR .rdi .r15] (jump B.exit)]
  { blocks := body ++ (Message.all.map (messageBlock s)).toArray }

end IxCC.X86.Exe
