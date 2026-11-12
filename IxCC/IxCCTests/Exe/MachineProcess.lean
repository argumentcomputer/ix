import IxCC.X86.Exe.Machine.Proof.Blocks
import IxCC.Exe.Machine

/-! The shell against the session model, on real machine executables: the
differential behind the shell theorem (X0-P, `shell_sound`).

* `simulate` is the process as the platform's specification modules allow
  it: the byte machine fetching from the written file (`Process.Step`), and
  at a `syscall` the platform's system call (`Process.Syscall`) with answers
  the test chooses (`Answers`; `rcx`, `r11` and the flags after a call are
  given garbage). All memory is readable and writable, one of the
  permission assignments the theorem quantifies over. A memory fault or a
  divide error ends the run (`Stop.fault`); where `Process.Step` promises
  nothing (`Process.Unspecified`: nothing decodes and the bytes are not
  `0F 05`, which includes `rip` outside the file, or a condition on an
  undefined flag) every continuation is a trace of the specification, so the
  simulation stops there (`Stop.unspecified`), and the comparison may claim
  something only if no run stops there before a call the model shows stuck
  (`unspecifiedOk`; the theorem's corollary `Process.shell_unspecified`).
* `model` is the session model (`Performs`, `Denotes`, `Report`) read as a
  function of the object's calls (`Lang.run` of `Process.linkedOf` under a
  driver of the layout) and of the same answers, with how its run ended
  (`ModelEnd`); `allows` is what `Process.Shows` allows of a trace against
  it.
* `monitored` checks along a run the location clause of the loop invariant
  (`AtLoop`'s cursor): at every arrival at `loop` the argument cursor's slot
  words and bytes are outside the zero-filled segments and the loader's, and
  every write of the shell's code and of the object's lands inside the
  segments.

A run's memory is a table over the loader's bytes (`tableMem`), refreshed
after each step at the addresses the step may have written. -/

namespace IxCCTests.Exe.MachineProcess

open IxCC IxCC.X86 IxCC.X86.Exe IxCC.X86.Exe.Process
open IxCC.Sem (Result Obs Lang)
open IxCC.Exe.Machine (Config Request nextArg split natOf statusOf statusTrap statusNotValue statusRequest
  statusWriteFailed statusConfine written notWritten)

/-- The platform's answers: `prctl`'s, `seccomp`'s, and the result of the `i`-th write of `n`
bytes. -/
structure Answers where
  prctl : Word := 0
  seccomp : Word := 0
  write : Nat → Nat → Word := fun _ n => UInt64.ofNat n

def tableMem (tbl : Std.HashMap Word UInt8) (base : Word → UInt8) : Memory :=
  ⟨fun a => tbl.getD a (base a), fun _ => true, fun _ => true⟩

/-- The addresses an operation may write (an over-approximation: its memory operands and the
word below `rsp`). -/
def mayWrite (s : ByteEval.State) : Decode.Operation → List Word
  | .op _ args =>
    let mems := args.filterMap fun
      | .mem a => some (a.eval s.core)
      | _ => none
    ((s.core.readReg .rsp - 8) :: mems).flatMap fun a => (List.range 8).map fun i => a + UInt64.ofNat i

/-- Why `simulate` stopped: `exit`; a memory fault or a divide error (no step: the process
ends); the fuel; a system call the specification leaves open (`Sys.other`, after which it allows
anything); or a state where `Process.Step` promises nothing (`Process.Unspecified`). -/
inductive Stop where
  | exited | fault | fuel | other | unspecified
  deriving BEq, Repr

/-- Outside the segments `segs` (`Process.OutsideSegments`, decided). -/
def outside (segs : List (Nat × Nat)) (a : Word) : Bool :=
  segs.all fun seg => decide (a.toNat < seg.1) || decide (seg.1 + seg.2 ≤ a.toNat)

/-- The argument cursor from `slot`, walked to its null slot: whether every slot word and every
argument byte up to its NUL is outside the segments and the loader's (`orig`). -/
def cursorOk (m : Memory) (segs : List (Nat × Nat)) (orig : Word → UInt8) : Nat → Word → Bool
  | 0, _ => false
  | fuel + 1, slot =>
    let wordOk := (List.range 8).all fun b =>
      let a := slot + UInt64.ofNat b
      outside segs a && m.bytes a == orig a
    let p := m.read64 slot
    let rec bytes : Nat → Word → Bool
      | 0, _ => false
      | n + 1, a => outside segs a && m.bytes a == orig a && (m.bytes a == 0 || bytes n (a + 1))
    wordOk && (p == 0 || (bytes 4096 p && cursorOk m segs orig fuel (slot + 8)))

/-- What `simulate` saw: the system calls, why it stopped, the steps, the arrivals at `loopAt`
with a bad cursor (`monitor`), and the writes outside the segments. -/
structure Run where
  trace : List Sys
  stop : Stop
  steps : Nat
  arrivals : Nat := 0
  badCursor : Nat := 0
  badWrites : Nat := 0
  writes : Nat := 0

/-- **The process** (`Process.Step` with `Process.Syscall`) under `ans`, for at most `fuel`
steps. With `monitor := some (segs, loopAt, C, orig)` it also checks the loop invariant's
location clause (see the module note). -/
def simulate (image : ByteArray) (ans : Answers) (fuel : Nat) (s₀ : ByteEval.State) (base : Word → UInt8)
    (tbl₀ : Std.HashMap Word UInt8) (monitor : Option (List (Nat × Nat) × Word × Word × (Word → UInt8)) := none) :
    Run := Id.run do
  let mut s := s₀
  let mut tbl := tbl₀
  let mut acc : Array Sys := #[]
  let mut nw := 0
  let mut r : Run := { trace := [], stop := .fuel, steps := fuel }
  for i in [0:fuel] do
    if let some (segs, loopAt, C, orig) := monitor then
      if s.rip == loopAt then
        r := { r with arrivals := r.arrivals + 1 }
        let m := s.core.memory
        unless cursorOk m segs orig 4096 (m.read64 (C + 16)) do r := { r with badCursor := r.badCursor + 1 }
    let off := (s.rip - fetchBase).toNat
    match Decode.decodeAt image off with
    | some d =>
      if let some (segs, _, _, _) := monitor then
        match d.operation with
        | .op o args =>
          for w in o.writes args s.core do
            r := { r with writes := r.writes + 1 }
            for k in List.range w.bytes do
              if outside segs (w.address + UInt64.ofNat k) then
                r := { r with badWrites := r.badWrites + 1 }
      match ByteEval.step image fetchBase s with
      | .ok s' =>
        for a in mayWrite s d.operation do
          tbl := tbl.insert a (s'.core.memory.bytes a)
        s := { s' with core := { s'.core with memory := tableMem tbl base } }
      | .error (.memory _) | .error .divideError => return { r with trace := acc.toList, stop := .fault, steps := i }
      -- a condition on an undefined flag (the byte machine reports `decode` only where nothing decodes)
      | .error (.undefinedCondition _) | .error (.decode _) =>
        return { r with trace := acc.toList, stop := .unspecified, steps := i }
    | none =>
      if image[off]? == some 0x0f && image[off + 1]? == some 0x05 then
        let rax := s.core.readReg .rax
        let rdi := s.core.readReg .rdi
        let rsi := s.core.readReg .rsi
        let rdx := s.core.readReg .rdx
        if rax == 157 && rdi == prSetNoNewPrivs then
          acc := acc.push (.prctl rdi rsi ans.prctl)
          s := returned s ans.prctl 0xdeadbeef 0xfeedface {}
        else if rax == 317 && rdi == seccompSetModeFilter && rsi == 0 then
          acc := acc.push (.seccomp rdi rsi rdx ans.seccomp)
          s := returned s ans.seccomp 0xdeadbeef 0xfeedface {}
        else if rax == 1 then
          let res := ans.write nw rdx.toNat
          nw := nw + 1
          acc := acc.push (.write rdi (slice s.core.memory rsi rdx.toNat) res)
          s := returned s res 0xdeadbeef 0xfeedface { carry := some true, zero := some false }
        else if rax == 60 then
          acc := acc.push (.exit rdi)
          return { r with trace := acc.toList, stop := .exited, steps := i }
        else
          acc := acc.push (.other rax)
          return { r with trace := acc.toList, stop := .other, steps := i }
      -- nothing decodes and the bytes are not `0F 05` (every `rip` outside the file)
      else return { r with trace := acc.toList, stop := .unspecified, steps := i }
  return { r with trace := acc.toList }

/-! ## The session model, as a function -/

def report (ans : Answers) (status : Nat) : List UInt8 → Nat → Nat → List Sys
  | _, _, 0 => []
  | m, nw, fuel + 1 =>
    if m.isEmpty then [.exit (UInt64.ofNat status)]
    else
      let res := ans.write nw m.length
      if res.toNat = 0 ∨ 2 ^ 63 ≤ res.toNat then [.write 2 m res, .exit (UInt64.ofNat statusWriteFailed)]
      else .write 2 m res :: report ans status (m.drop res.toNat) (nw + 1) fuel

/-- How a run of the model ended: with an event that ends the session (an exit or a report), at a
call that timed out (or with the iterations spent), or at a call the model shows stuck (after which
`Process.Shows` allows any trace that has passed the model's). -/
inductive ModelEnd where
  | event | timeout | stuck
  deriving BEq, Repr

/-- The model's system calls from `c` under the calls `callF` (the write counter `nw`), and how it
ended. -/
def modelLoop (callF : Nat → Nat → Result (Option Obs)) (ans : Answers) :
    Nat → Config → Nat → List Sys × ModelEnd
  | 0, _, _ => ([], .timeout)
  | fuel + 1, c, nw =>
    let fail := fun s => (report ans s (messageOf s) nw 1000, ModelEnd.event)
    match callF c.state c.event with
    | .ok o =>
      match natOf o with
      | some w =>
        match Request.decode (split w).2 with
        | some .arg =>
          modelLoop callF ans fuel ⟨(split w).1, (nextArg c.args).1, (nextArg c.args).2⟩ nw
        | some (.write fd b) =>
          let res := ans.write nw 1
          let (rest, ended) := modelLoop callF ans fuel
            ⟨(split w).1, if res == 1 then written else notWritten, c.args⟩ (nw + 1)
          (.write (UInt64.ofNat fd) [UInt8.ofNat b] res :: rest, ended)
        | some (.exit code) => ([.exit (UInt64.ofNat code)], .event)
        | none => fail statusRequest
      | none => fail statusNotValue
    | .resource f => fail (statusOf f)
    | .trap => fail statusTrap
    | .timeout => ([], .timeout)
    | .stuck => ([], .stuck)

/-- The model's system calls from the first configuration on `args`, the confinement first, and how
its run ended. -/
def model (callF : Nat → Nat → Result (Option Obs)) (data : Nat) (args : List (List Nat)) (ans : Answers) :
    List Sys × ModelEnd :=
  if ans.prctl != 0 then
    (.prctl prSetNoNewPrivs 1 ans.prctl :: report ans statusConfine (messageOf statusConfine) 0 1000, .event)
  else if ans.seccomp != 0 then
    (.prctl prSetNoNewPrivs 1 0 :: .seccomp seccompSetModeFilter 0 (UInt64.ofNat (fprogAddr data)) ans.seccomp ::
      report ans statusConfine (messageOf statusConfine) 0 1000, .event)
  else
    let (rest, ended) := modelLoop callF ans 10000 (Config.initial args) 0
    (started data ++ rest, ended)

/-- What `Process.Shows` allows of a trace `σ`, against the model's run `ρ` on the same answers
that ended as `e`: a prefix of `ρ`, or, when the model's last call is stuck, any trace that has
passed `ρ` (nothing is claimed after a stuck call). -/
def allows (ρ : List Sys) (e : ModelEnd) (σ : List Sys) : Bool :=
  σ.isPrefixOf ρ || (e == .stuck && ρ.isPrefixOf σ)

/-- A run stopped where `Process.Step` promises nothing only after it passed the model's run up to
a call the model shows stuck (`Process.shell_unspecified`): otherwise the specification would allow
the process every continuation where the theorem claims something. -/
def unspecifiedOk (run : Run) (ρ : List Sys) (e : ModelEnd) : Bool :=
  run.stop != .unspecified || (e == .stuck && ρ.isPrefixOf run.trace)

/-! ## The loader's post-state -/

def garbage (k : Nat) : Registers := fun r =>
  let i : Nat := match r with
    | .rax => 1 | .rcx => 2 | .rdx => 3 | .rbx => 4 | .rsp => 5 | .rbp => 6 | .rsi => 7 | .rdi => 8
    | .r8 => 9 | .r9 => 10 | .r10 => 11 | .r11 => 12 | .r12 => 13 | .r13 => 14 | .r14 => 15 | .r15 => 16
  UInt64.ofNat (0x0123456789abcdef * (i + k) + 0x1111 * k)

def put64 (t : Std.HashMap Word UInt8) (a v : Word) : Std.HashMap Word UInt8 :=
  (List.range 8).foldl (fun t i => t.insert (a + UInt64.ofNat i) ((v >>> UInt64.ofNat (8 * i)).toUInt8)) t

/-- The file's bytes at `fileBase`, zero elsewhere. -/
def fileBytes (image : ByteArray) : Word → UInt8 := fun a =>
  let i := (a - fetchBase).toNat
  if i < image.size then image[i]! else 0

/-- The loader's post-state (`Process.Loaded`): `rip` the shell's first byte, the file at
`fileBase`, the argument block (`ArgBlock`: argc, argv, a null, the strings from `strAt`) at
`sp`; `argc = 0` when `noName`. Registers and flags garbage. -/
def loaded (image : ByteArray) (shellOffset : Nat) (sp strAt : Word) (args : List String) (noName : Bool) :
    ByteEval.State × Std.HashMap Word UInt8 := Id.run do
  let mut tbl : Std.HashMap Word UInt8 := {}
  let strs := if noName then [] else "prog" :: args
  tbl := put64 tbl sp (UInt64.ofNat strs.length)
  let mut at_ := strAt
  let mut slot := sp + 8
  for str in strs do
    tbl := put64 tbl slot at_
    for b in str.toUTF8.toList do
      tbl := tbl.insert at_ b
      at_ := at_ + 1
    tbl := tbl.insert at_ 0
    at_ := at_ + 1
    slot := slot + 8
  tbl := put64 tbl slot 0
  let s : ByteEval.State := { core := ⟨(garbage 7).set .rsp sp, tableMem tbl (fileBytes image)⟩
                              rip := UInt64.ofNat (fileBase + shellOffset), flags := { zero := some true } }
  return (s, tbl)

/-! ## The cases -/

structure Case where
  name : String
  root : String
  layout : Machine.Layout := {}
  args : List String := []
  noName : Bool := false
  ans : Answers := {}
  sp : Word := 0x7ffffffde000
  strAt : Word := 0x7ffffffd0000
  /-- The exit status the run ends with. -/
  status : Nat
  /-- Run only with `--all-machine-cases` (the longest runs). -/
  extra : Bool := false

def small : Machine.Layout := { stack := 8192, region := 4096 }
def large : Machine.Layout := { stack := 1 <<< 39, region := (1 <<< 39) - (1 <<< 13) }

/-- The 22 end-to-end cases (`IxCC/plans/x2/h3/StatementProbe.lean`'s, with the statuses the
model gives). -/
def cases : List Case := [
  { name := "echo on two arguments", root := "Machines.echo", args := ["ab", "c"], status := 235 },
  { name := "echo on none", root := "Machines.echo", status := 5 },
  { name := "echo on an empty block (argc = 0)", root := "Machines.echo", noName := true, status := 5 },
  { name := "echo on empty arguments", root := "Machines.echo", args := ["", "x", ""], status := 253 },
  { name := "echo with its writes refused", root := "Machines.echo", args := ["abc"],
    ans := { write := fun i _ => if i % 2 == 0 then 0 else (0 : Word) - 5 }, status := 74 },
  { name := "echo at a 2^39 layout (movabs constants)", root := "Machines.echo", args := ["ab"], layout := large,
    status := 40 },
  { name := "echo at the smallest layout", root := "Machines.echo", args := ["ab"], layout := small, status := 40 },
  { name := "echo with its block at the top of memory", root := "Machines.echo", args := ["ab"],
    sp := (0 : Word) - 24, strAt := 0x2000, status := 40 },
  { name := "the identity on 123", root := "Machines.idMain", args := ["123"], status := 0 },
  { name := "the identity on 12x", root := "Machines.idMain", args := ["12x"], status := 3, extra := true },
  { name := "the identity on no argument", root := "Machines.idMain", status := 2 },
  { name := "the identity on 2^48", root := "Machines.idMain", args := ["281474976710656"], status := 67, extra := true },
  { name := "fib on 10", root := "Machines.fibMain", args := ["10"], status := 0 },
  { name := "fib on 5000 with an 8 KiB stack (the step's resource failure)", root := "Machines.fibMain",
    args := ["5000"], layout := small, status := 66 },
  { name := "fib through a closure on 10", root := "Machines.fibMainHO", args := ["10"], status := 0 },
  { name := "a request outside the interface", root := "Machines.badRequest", status := 72 },
  { name := "its report written short", root := "Machines.badRequest",
    ans := { write := fun i n => if n ≤ 1 then 1 else UInt64.ofNat (min n (5 + i % 3)) }, status := 72 },
  { name := "its report refused mid-way (0)", root := "Machines.badRequest",
    ans := { write := fun i n => if i == 2 then 0 else UInt64.ofNat (min n 7) }, status := 74 },
  { name := "its report refused mid-way (-EFAULT)", root := "Machines.badRequest",
    ans := { write := fun i n => if i == 1 then (0 : Word) - 14 else UInt64.ofNat (min n 9) }, status := 74 },
  { name := "prctl refused", root := "Machines.echo", ans := { prctl := 1 }, status := 75 },
  { name := "seccomp refused, the report written short", root := "Machines.echo",
    ans := { seccomp := (0 : Word) - 22, write := fun _ n => UInt64.ofNat (min n 11) }, status := 75 },
  { name := "seccomp refused, the report refused", root := "Machines.echo",
    ans := { seccomp := 1, write := fun _ _ => 0 }, status := 74 }]

/-- The model's calls for an object at layout `L`: `cx_init` under the layout's driver, the
step from the site the shell's `callStep` block gives. -/
def callsOf (L : Machine.Layout) {step : String} {object : ByteArray} (c : Checked (Machine.frame L step) object)
    (roots : List Linked.Root) (fuel : Nat := 2000000) : Nat → Nat → Result (Option Obs) :=
  let pl := c.plan.placement
  let D := L.driverWith pl.textOffset (shellAddr L step c Machine.B.loop 12) (fun _ => 0)
  let site : Driver.Site := ⟨UInt64.ofNat (shellAddr L step c Machine.B.callStep 10), {}, fun _ => 0⟩
  fun s e => Lang.run (linkedOf object roots D site) (0, [s, e]) fuel

/-- The exit status a trace ends with. -/
def exitOf : List Sys → Option Nat
  | [] => none
  | [.exit s] => some s.toNat
  | _ :: rest => exitOf rest

end IxCCTests.Exe.MachineProcess
