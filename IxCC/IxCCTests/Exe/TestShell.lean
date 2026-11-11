import IxCC.X86.Exe.Validate

/-!
# The test shell: native runs of compiled objects with no C

The native suites run compiled objects as standalone executables that IxCC
writes (`X86.Exe.writeFor`), with this shell as their frame instead of the
production shell of `IxCC/X86/Exe/Code.lean`. It is test code: it lives here,
outside the production API, and nothing proves it does what this note says.

**What it does.** It confines the process (`prctl(PR_SET_NO_NEW_PRIVS)`, then a
seccomp filter that kills the process on any system call but `read` from file
descriptor 0, `write` to 1 or 2, and `exit`; status 75 if either is refused)
and then serves requests from standard input, one after another, until end of
input at a request boundary (status 0). A request is eight little-endian
64-bit words:

| word 0 | words 1 to 7 | what the shell does |
| --- | --- | --- |
| 0 | — | exits with status 0 |
| 1 | `k`, `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9` | calls the frame's `k`th export with those six argument registers, with sentinels in `rbx`, `rbp` and `r12` to `r15` and `rsp` at `callTop` (so the callee sees `callTop - 8` and its return address there), and answers three words: `rax`, `rdx`, and 1 if the six sentinels and `rsp` came back unchanged, else 0 |
| 2 | `address`, `length` | answers the `length` bytes at `address` |
| 3 | `address`, `length` | reads `length` more bytes from standard input into memory at `address` |

Every range of a read or a write must lie inside the region (`lo` to `hi`);
anything else ends the run: status 80 if standard input fails or ends inside
a request, 82 for an unknown request, 83 for an export index out of range, 84
for a range outside the region, 74 if a write fails.

So the host (`IxCCTests.Exe.Session`, `IxCCTests.Rt.Native`) does in Lean what
the C runtime driver did before X1: it stores the stack budget at
`region + 16`, calls `cx_init` and then the root once per input line, reads
the result word and the object area back and decodes the result twice
(`Rt.readback` and the independent decoder `IxCCTests.Rt.Decoder`).

**Why binary requests.** The shell parses and renders nothing: requests and
answers are machine words and raw bytes, so the text protocols the C drivers
spoke, the parsing of numbers (`strtoull` accepted `0x10`, `12x` and `-1`) and
the decoding of results are host code in Lean, where they are tested like the
rest of the suites, and the machine code the native gates trust is only a
request loop, a bounds check and the calls.

**Memory.** The program stack and the shell's own 256 bytes (the request and
answer buffers and the shell's stack) share one zero-filled segment at
`dataBase`: the program's stack below `callTop`, the shell's bytes above it.
The region follows the stack in the same segment, page-aligned, or lies in
its own zero-filled segment at a fixed address (`Mem.fixed`, for the back
end's generated programs, whose results depend on the region's address).
Below the program stack nothing is mapped, so a stack that ran past its
bottom faults, as one past a guard page does.
-/

namespace IxCCTests.Exe.TestShell

open IxCC.X86 IxCC.X86.Exe

/-! ## Memory -/

/-- The shell's own bytes at the top of the stack segment: the request (64
bytes), the answer (24 bytes) and its stack. -/
def reserve : Nat := 256

/-- A test executable's memory: a program stack of at least `stack` bytes
(the stack budget is `stack - 4096`), and a region of
`region` bytes after the stack or at `fixed`. -/
structure Mem where
  stack : Nat
  region : Nat
  fixed : Option Nat := none
  deriving BEq, Repr, Inhabited

namespace Mem

/-- The stack segment's size: the stack and the shell's bytes, in pages. -/
def stackArea (m : Mem) : Nat := alignUp (m.stack + reserve) 0x1000

/-- The stack pointer each call is entered with, before its return address. -/
def callTop (m : Mem) : Nat := dataBase + m.stackArea - reserve

def scratch (m : Mem) : Nat := m.callTop
def request (m : Mem) : Nat := m.scratch
def answer (m : Mem) : Nat := m.scratch + 64
def shellTop (m : Mem) : Nat := m.scratch + reserve

/-- The region's first byte. -/
def base (m : Mem) : Nat := m.fixed.getD (dataBase + m.stackArea)

/-- The stack budget stored at `region + 16`. -/
def budget (m : Mem) : Nat := m.stack - 4096

def segments (m : Mem) : List (Nat × Nat) :=
  match m.fixed with
  | some at_ => [(at_, alignUp m.region 0x1000), (dataBase, m.stackArea)]
  | none => [(dataBase, m.stackArea + m.region)]

/-- What the writer needs of the memory: a stack the budget can be taken
from, a region that holds the budget word, stack and region within the
executable writer's bound (`maxDataBytes`), and a fixed region below the file. -/
def ok (m : Mem) : Bool :=
  m.stack % 16 == 0 && decide (8192 ≤ m.stack) && decide (24 ≤ m.region) &&
    decide (m.stackArea + m.region ≤ maxDataBytes) &&
    (m.fixed.all fun a => decide (a + alignUp m.region 0x1000 ≤ fileBase))

end Mem

/-! ## The seccomp filter -/

/-- Allow `exit` (60), `write` (1) to file descriptor 1 or 2 and `read` (0)
from file descriptor 0; kill the process for anything else or another
architecture. Jumps count instructions after the next. -/
def seccompFilter : List UInt8 :=
  bpf 0x20 0 0 4 ++                 -- 0: A := arch
  bpf 0x15 0 13 0xC000003E ++       -- 1: x86-64, else kill
  bpf 0x20 0 0 0 ++                 -- 2: A := nr
  bpf 0x15 12 0 60 ++               -- 3: exit: allow
  bpf 0x15 1 0 1 ++                 -- 4: write: to 6
  bpf 0x15 5 9 0 ++                 -- 5: read: to 11, else kill
  bpf 0x20 0 0 20 ++                -- 6: A := the descriptor's high half
  bpf 0x15 0 7 0 ++                 -- 7: zero, else kill
  bpf 0x20 0 0 16 ++                -- 8: A := the descriptor
  bpf 0x15 6 0 1 ++                 -- 9: 1: allow
  bpf 0x15 5 4 2 ++                 -- 10: 2: allow, else kill
  bpf 0x20 0 0 20 ++                -- 11: A := the descriptor's high half
  bpf 0x15 0 2 0 ++                 -- 12: zero, else kill
  bpf 0x20 0 0 16 ++                -- 13: A := the descriptor
  bpf 0x15 1 0 0 ++                 -- 14: 0: allow, else kill
  bpf 0x06 0 0 0x80000000 ++        -- 15: SECCOMP_RET_KILL_PROCESS
  bpf 0x06 0 0 0x7fff0000           -- 16: SECCOMP_RET_ALLOW

def seccompLength : Nat := 17

/-- The read-only data at `addr`: the filter and its `struct sock_fprog`. -/
def data (addr : Nat) : ByteArray :=
  ⟨(seccompFilter ++ le16 seccompLength ++ List.replicate 6 (0 : UInt8) ++ le64 addr).toArray⟩

def fprog (addr : Nat) : Nat := addr + 8 * seccompLength

/-! ## The code -/

/-- The sentinels in the callee-saved registers. -/
def sentinels : List (GPR × Nat) :=
  [(.rbx, 0x1111111111111111), (.rbp, 0x2222222222222222), (.r12, 0x3333333333333333),
   (.r13, 0x4444444444444444), (.r14, 0x5555555555555555), (.r15, 0x6666666666666666)]

/-- Exit statuses. -/
def exitInput : Nat := 80
def exitRequest : Nat := 82
def exitExport : Nat := 83
def exitRange : Nat := 84
def exitWrite : Nat := 74
def exitConfine : Nat := 75

section Builders

private def ins (i : IxCC.X86.Instr) : Shell.Instr := .instr i
private def movI (r : GPR) (v : Nat) : Shell.Instr := ins (IxCC.X86.Instr.mov .w64 r (.imm (UInt64.ofNat v)))
private def movR (d s : GPR) : Shell.Instr := ins (IxCC.X86.Instr.mov .w64 d (.reg s))
private def at_ (b : GPR) (disp : Nat := 0) : MemAddr :=
  { base := some b, index := none, scale := .one, displacement := UInt32.ofNat disp }
private def ld (d : GPR) (a : MemAddr) : Shell.Instr := ins (IxCC.X86.Instr.load .w64 d a)
private def st (a : MemAddr) (s : GPR) : Shell.Instr := ins (IxCC.X86.Instr.store .w64 a s)
private def addR (d s : GPR) : Shell.Instr := ins (IxCC.X86.Instr.alu .add .w64 d (.reg s))
private def subR (d s : GPR) : Shell.Instr := ins (IxCC.X86.Instr.alu .sub .w64 d (.reg s))
private def call (b : Nat) : Shell.Instr := ins (.call (UInt32.ofNat b))
private def cmpI (r : GPR) (v : Nat) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .imm (UInt32.ofNat v) } c (UInt32.ofNat t) (UInt32.ofNat f)
private def cmpR (r s : GPR) (c : Condition) (t f : Nat) : Terminator :=
  Terminator.compare { width := .w64, left := r, right := .reg s } c (UInt32.ofNat t) (UInt32.ofNat f)
private def ifNonzero (r : GPR) (t f : Nat) : Terminator :=
  .branch { mn := .test, w := .w64, form := .MR } [.reg r, .reg r] .ne (UInt32.ofNat t) (UInt32.ofNat f)
private def jump (b : Nat) : Terminator := .jump (UInt32.ofNat b)
private def blk (is : Array Shell.Instr) (t : Terminator) : Shell.Block := { instructions := is, terminator := t }

end Builders

/-! Block numbers. -/
namespace Blk
def start := 0
def seccomp := 1
def setup := 2
def loop := 3
def loopCheck := 4
def loopCheck2 := 5
def dispatch := 6
def dispatch2 := 7
def dispatch3 := 8
def opCall := 9
def after := 10
def check (i : Nat) := 11 + i   -- 11 … 16: the six sentinels
def checkSp := 17
def okSet := 18
def respond := 19
def opRead := 20
def read2 := 21
def read3 := 22
def read4 := 23
def opWrite := 24
def write2 := 25
def write3 := 26
def write4 := 27
def write5 := 28
def readFull := 29
def rfLoop := 30
def rfSys := 31
def rfGot := 32
def rfAdv := 33
def rfEof := 34
def rfEof2 := 35
def rfEofRet := 36
def rfOk := 37
def rfErr := 38
def writeFull := 39
def wfSys := 40
def wfAdv := 41
def wfRet := 42
def exit := 43
def exitOk := 44
def exitInput := 45
def exitRequest := 46
def exitExport := 47
def exitRange := 48
def exitWrite := 49
def exitConfine := 50
def select (j : Nat) := 52 + 2 * j
def callExport (j : Nat) := 53 + 2 * j
def dispatch4 := 51
end Blk

/-- The shell for memory `m` calling `exports`, with its data at `data`. -/
def program (m : Mem) (exports : List String) (dataAt : Nat) : Shell.Program :=
  let n := exports.length
  let lo := m.base
  let hi := m.base + m.region
  let checks : Array Shell.Block := (sentinels.zipIdx.map fun ((r, v), i) =>
    blk #[movI .rcx v] (cmpR r .rcx .ne Blk.respond (if i + 1 < sentinels.length then Blk.check (i + 1) else Blk.checkSp))).toArray
  -- bounds: lo ≤ rsi, rsi ≤ hi, rdx ≤ hi - rsi
  let fixed : Array Shell.Block := #[
    -- start: prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)
    blk #[movI .rax 157, movI .rdi 38, movI .rsi 1, movI .rdx 0, movI .r10 0, movI .r8 0, .syscall]
      (ifNonzero .rax Blk.exitConfine Blk.seccomp),
    -- seccomp(SECCOMP_SET_MODE_FILTER, 0, &program)
    blk #[movI .rax 317, movI .rdi 1, movI .rsi 0, movI .rdx (fprog dataAt), .syscall]
      (ifNonzero .rax Blk.exitConfine Blk.setup),
    -- setup: the shell's own stack
    blk #[movI .r10 m.shellTop, movR .rsp .r10] (jump Blk.loop),
    -- loop: one request, end of input allowed
    blk #[movI .rsi m.request, movI .rdx 64, movI .rdi 1, call Blk.readFull] (jump Blk.loopCheck),
    blk #[] (cmpI .rax 0 .eq Blk.dispatch Blk.loopCheck2),
    blk #[] (cmpI .rax 1 .eq Blk.exitOk Blk.exitInput),
    -- dispatch on word 0
    blk #[movI .r12 m.request, ld .rax (at_ .r12)] (cmpI .rax 1 .eq Blk.opCall Blk.dispatch2),
    blk #[] (cmpI .rax 2 .eq Blk.opRead Blk.dispatch3),
    blk #[] (cmpI .rax 3 .eq Blk.opWrite Blk.dispatch4),
    -- opCall: rax := the export index
    blk #[movI .r12 m.request, ld .rax (at_ .r12 8)] (jump (if n == 0 then Blk.exitExport else Blk.select 0)),
    -- after a call: the answer, then the sentinels and rsp
    blk #[movI .r10 m.answer, st (at_ .r10) .rax, st (at_ .r10 8) .rdx, movI .r11 0, st (at_ .r10 16) .r11]
      (jump (Blk.check 0))] ++ checks ++ #[
    blk #[movI .rcx m.callTop] (cmpR .rsp .rcx .ne Blk.respond Blk.okSet),
    blk #[movI .r10 m.answer, movI .r11 1, st (at_ .r10 16) .r11] (jump Blk.respond),
    -- respond: write the answer
    blk #[movI .r10 m.shellTop, movR .rsp .r10, movI .rdi 1, movI .rsi m.answer, movI .rdx 24, call Blk.writeFull]
      (jump Blk.loop),
    -- opRead
    blk #[movI .r12 m.request, ld .rsi (at_ .r12 8), ld .rdx (at_ .r12 16), movI .rcx lo]
      (cmpR .rsi .rcx .unsignedLt Blk.exitRange Blk.read2),
    blk #[movI .rcx hi] (cmpR .rsi .rcx .unsignedGt Blk.exitRange Blk.read3),
    blk #[movI .rcx hi, subR .rcx .rsi] (cmpR .rdx .rcx .unsignedGt Blk.exitRange Blk.read4),
    blk #[movI .rdi 1, call Blk.writeFull] (jump Blk.loop),
    -- opWrite
    blk #[movI .r12 m.request, ld .rsi (at_ .r12 8), ld .rdx (at_ .r12 16), movI .rcx lo]
      (cmpR .rsi .rcx .unsignedLt Blk.exitRange Blk.write2),
    blk #[movI .rcx hi] (cmpR .rsi .rcx .unsignedGt Blk.exitRange Blk.write3),
    blk #[movI .rcx hi, subR .rcx .rsi] (cmpR .rdx .rcx .unsignedGt Blk.exitRange Blk.write4),
    blk #[movI .rdi 0, call Blk.readFull] (jump Blk.write5),
    blk #[] (cmpI .rax 0 .eq Blk.loop Blk.exitInput),
    -- readFull(rsi, rdx, rdi = end of input allowed at the start):
    -- rax 0 done, 1 end of input at the start, 2 failed or ended inside
    blk #[movR .r9 .rdi, movI .r10 0] (jump Blk.rfLoop),
    blk #[] (cmpI .rdx 0 .eq Blk.rfOk Blk.rfSys),
    blk #[movI .rax 0, movI .rdi 0, .syscall] (cmpI .rax 0 .signedLt Blk.rfErr Blk.rfGot),
    blk #[] (cmpI .rax 0 .eq Blk.rfEof Blk.rfAdv),
    blk #[addR .rsi .rax, subR .rdx .rax, addR .r10 .rax] (jump Blk.rfLoop),
    blk #[] (cmpI .r10 0 .eq Blk.rfEof2 Blk.rfErr),
    blk #[] (cmpI .r9 0 .eq Blk.rfErr Blk.rfEofRet),
    blk #[movI .rax 1] .ret,
    blk #[movI .rax 0] .ret,
    blk #[movI .rax 2] .ret,
    -- writeFull(rdi, rsi, rdx)
    blk #[] (cmpI .rdx 0 .eq Blk.wfRet Blk.wfSys),
    blk #[movI .rax 1, .syscall] (cmpI .rax 0 .signedLe Blk.exitWrite Blk.wfAdv),
    blk #[addR .rsi .rax, subR .rdx .rax] (jump Blk.writeFull),
    blk #[] .ret,
    -- exit(rdi)
    blk #[movI .rax 60, .syscall] (jump Blk.exit),
    blk #[movI .rdi 0] (jump Blk.exit),
    blk #[movI .rdi exitInput] (jump Blk.exit),
    blk #[movI .rdi exitRequest] (jump Blk.exit),
    blk #[movI .rdi exitExport] (jump Blk.exit),
    blk #[movI .rdi exitRange] (jump Blk.exit),
    blk #[movI .rdi exitWrite] (jump Blk.exit),
    blk #[movI .rdi exitConfine] (jump Blk.exit),
    -- dispatch4: word 0 is 0, the end of the session
    blk #[] (cmpI .rax 0 .eq Blk.exitOk Blk.exitRequest)]
  let calls : Array Shell.Block := (exports.zipIdx.flatMap fun (symbol, j) =>
    [blk #[] (cmpI .rax j .eq (Blk.callExport j) (if j + 1 < n then Blk.select (j + 1) else Blk.exitExport)),
     blk (#[movI .r12 m.request, ld .rdi (at_ .r12 16), ld .rsi (at_ .r12 24), ld .rdx (at_ .r12 32),
         ld .rcx (at_ .r12 40), ld .r8 (at_ .r12 48), ld .r9 (at_ .r12 56)] ++
         (sentinels.map fun (r, v) => movI r v).toArray ++
         #[movI .r10 m.callTop, movR .rsp .r10, .callExport symbol])
       (jump Blk.after)]).toArray
  { blocks := fixed ++ calls }

/-- The frame of a test executable for memory `m` calling `exports`. -/
def frame (m : Mem) (exports : List String) : Frame where
  data := data
  code := program m exports
  exports := exports
  segments := m.segments

/-- Write a test executable: `object` with this shell calling `exports`, in
memory `m`, checked by the executable check for its frame. -/
def writeExe (m : Mem) (exports : List String) (object : ByteArray) : Except String ByteArray := do
  unless m.ok do throw s!"the test shell's memory {repr m} is outside what it supports"
  match writeFor (frame m exports) object with
  | .ok c => pure c.bytes
  | .error e => throw e.render

end IxCCTests.Exe.TestShell
