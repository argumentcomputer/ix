import IxCCTests.Exe.Run
import IxCCTests.Exe.MachineSessions
import IxCCTests.Exe.MachineProcess

/-! The numeric state machines' part of `tests-exe`: what `ixcc compile --exe
FILE --machine` writes (`IxCC/X86/Exe/Machine.lean`), for the roots of the
`phase1-machines` family, whose parsing and rendering are Lean
(`IxCC/lib/IxccExe.lean`).

* **The library is the family's**: the family's source begins with
  `lib/IxccExe.lean`'s text, byte for byte.
* **The interface**: every version-0 request decodes to itself and fits the
  request field.
* **The layout and the shell**: `Layout.check` accepts the layouts inside the
  driver contract and refuses the others; the shell encodes for small and
  default layouts with five system-call sites and its two calls, `cx_init`
  then the step; its read-only data starts with `--exe`'s seccomp filter.
* **The writer and its check**: the executables of the family's roots pass
  `checkFrame` with five program headers, and every header byte, a sample of
  every part, every 64th truncation and an appended byte are refused; the
  writer refuses a missing export and layouts outside the contract;
* **The shell check** (`Shell.check`, run by `Machine.writeChecked`): the
  family's executables pass it, and it refuses an opcode, a block
  displacement, the step call's target and the system-call bytes, each
  changed, and the first byte of every instruction and terminator, changed;
  the file decides the call lemma's call-site facts (`AtCall`) at the real
  `cx_init` and step calls; fib's executable is written at the smallest and a
  large layout; the writer refuses a shell with an unwind or a branch falling
  through;
  `Exe.machine` refuses first roots of another shape (`exe.machine`);
  `ixcc compile --machine` without `--exe` is a usage error.
* **Natively** (`--run`, x86-64 Linux): `fib` with Lean parsing and rendering
  against `--exe`'s `fib` on the same arguments (equal output and status, the
  message differing only for numerals of `2^63` and more); the identity at the
  range's edges; `fib` through a closure; a request outside the interface
  (72); a write the platform refuses (stdout closed: the program exits 74);
  three `echo` sessions against the transcripts Lean's interpreter printed;
  the confinement read from `/proc`; the system calls under `strace`; and
  `ixcc compile --exe --machine` in-process.
* **The shell against the session model** (`shellAgainstModel`; the content of the shell
  theorem, X0-P): the process as the platform's specification modules allow it, simulated on the
  written files, against the session model on the same answers, in 15 cases (22 with
  `--all-machine-cases`, which adds the two longest runs and the two roots the suite does not
  otherwise compile): no arguments, `argc = 0`, empty arguments, refused writes, the smallest
  and a `movabs` layout, the argument block at the top of memory, a non-numeral, the step's
  resource failure, the confinement refused, the report written short and refused; along each run,
  the cursor outside the segments and unchanged at every arrival at `loop` and every write inside
  them, and no state where `Process.Step` promises nothing reached before a call the model shows
  stuck; the process just after each call returns; a negative control; and a case past a stuck call
  (`echo` with its step's first bytes made undecodable: the model's step call is stuck, the process
  stops where the specification promises nothing, and the comparison then claims nothing). -/

namespace IxCCTests.Exe.Machine

open IxCC IxCC.Recheck IxCCTests.Src IxCCTests.Corpus IxCCTests.Exe.Suite
open System
open IxCC.X86.Exe.Machine (Layout)

def machines : FilePath := "fixtures/corpus/phase1-machines/corpus.json"
def library : FilePath := "lib/IxccExe.lean"
def source : FilePath := "fixtures/corpus/phase1-machines/src/Machines.lean"

/-- The range message of `IxccExe.Main1`. -/
def rangeMessage : String := "ixcc: a number is 2^48 or more, past a numeric state machine's range\n"

/-- One run's exit status and its standard output and error as bytes. -/
def runBytes (exe : FilePath) (args : List String) : IO (UInt32 × ByteArray × ByteArray) := do
  let child ← IO.Process.spawn { cmd := exe.toString, args := args.toArray, stdout := .piped, stderr := .piped }
  let out ← child.stdout.readBinToEnd
  let err ← child.stderr.readBinToEnd
  return (← child.wait, out, err)

def hexBytes (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in List.range (cs.size / 2) do
    out := out.push (UInt8.ofNat (16 * digit cs[2 * i]! + digit cs[2 * i + 1]!))
  return out

/-- Sessions of `Machines.echo` and the transcripts `lean --run` printed for
them (`printf 'session Machines.echo ARG…\n' | lean -Dlinter.all=false --run
src/Machines.lean`, from the family's directory: standard output and error in
hex, the status, the number of calls). -/
def echoSessions : List (List String × String × String × Nat × Nat) :=
  [(["ab", "c"], "64644b3235323939303639390a", "0a0a", 235, 22),
   ([], "353338310a", "", 5, 7),
   (["é~"], "c6816f323039333636393737350a", "0a", 143, 21)]

/-- **The shell against the session model** (`IxCCTests.Exe.MachineProcess`; the shell theorem's
content, tested): on real executables, the process as the platform's specification modules allow
it against the session model on the same answers; along each run, the loop invariant's location
clause; the process just after each call returns with each status; and, as a negative control, a
state at `loop` whose argument slot lies in the region (the invariant without its location clause,
which the shell proof's first statement of `from_loop` allowed) giving a trace the model does not
allow. `arts` are the artifacts the part compiled; `--all-machine-cases` adds the cases of
`Machines.fibMainHO` and `Machines.badRequest`. -/
def shellAgainstModel (a : Assert) (o : IxCCTests.Exe.Suite.Options) (arts : Array (String × Artifact)) :
    IO (Array String) := do
  let mut out : Array String := #[]
  let mut arts := arts
  if o.allCases then
    for root in ["Machines.fibMainHO", "Machines.badRequest"] do
      let (_, _, art) ← compileNamed machines "machines" root
      arts := arts.push (root, art)
  let t0 ← IO.monoMsNow
  let mut ran := 0
  let mut skipped : List String := []
  let mut steps := 0
  let mut arrivals := 0
  let mut writes := 0
  for cs in MachineProcess.cases do
    match (if cs.extra && !o.allCases then none else arts.find? (·.1 == cs.root)) with
    | none => skipped := skipped ++ [cs.name]
    | some (_, art) =>
      let .ok r := IxCC.Exe.machine art | expect a false s!"{cs.root}: not a machine"
      match X86.Exe.Machine.writeChecked cs.layout r.symbol art.object with
      | .error e => expect a false s!"{cs.name}: writeChecked refused: {repr e}"
      | .ok ce =>
        let image := ce.checked.bytes
        let pl := ce.checked.plan.placement
        let (s₀, tbl) := MachineProcess.loaded image pl.shellOffset cs.sp cs.strAt cs.args cs.noName
        let orig : X86.Word → UInt8 := fun x => tbl.getD x (MachineProcess.fileBytes image x)
        let loopAt := UInt64.ofNat (X86.Exe.Process.shellAddr cs.layout r.symbol ce.checked X86.Exe.Machine.B.loop 0)
        let run := MachineProcess.simulate image cs.ans 3000000 s₀ (MachineProcess.fileBytes image) tbl
          (some (cs.layout.segments, loopAt, UInt64.ofNat cs.layout.callTop, orig))
        let callF := MachineProcess.callsOf cs.layout ce.checked art.linkedRoots
        let args := cs.args.map fun s => s.toUTF8.toList.map (·.toNat)
        let (ρ, ended) := MachineProcess.model callF (X86.Exe.fileBase + pl.dataOffset) args cs.ans
        expect a (MachineProcess.unspecifiedOk run ρ ended)
          s!"{cs.name}: the process reached a state where Process.Step promises nothing (stopped after \
            {run.steps} steps, {run.trace.length} system calls) before any call the model shows stuck"
        expect a (run.stop == .exited && ended == .event && run.trace == ρ)
          s!"{cs.name}: the process's {run.trace.length} system calls are not the model's {ρ.length}"
        expectEq a (MachineProcess.exitOf run.trace) (some cs.status) s!"{cs.name}: the exit status"
        expect a (run.badCursor == 0) s!"{cs.name}: at {run.badCursor} arrivals at loop the cursor is inside \
          the segments or changed"
        expect a (run.badWrites == 0) s!"{cs.name}: {run.badWrites} bytes written outside the segments"
        expect a (cs.ans.prctl != 0 || cs.ans.seccomp != 0 || run.arrivals > 0) s!"{cs.name}: never at loop"
        ran := ran + 1
        steps := steps + run.steps
        arrivals := arrivals + run.arrivals
        writes := writes + run.writes
  out := out.push s!"the shell against the session model: {ran} cases, each trace the model's with its exit \
    status ({steps} steps); at {arrivals} arrivals at loop the cursor outside the segments and unchanged, and \
    {writes} writes all inside the segments; {skipped.length} cases not run (--all-machine-cases); {(← IO.monoMsNow) - t0} ms"
  -- just after each call returns (echo, the default layout): each status, a moved rsp, an even word
  let some (_, echoArt) := arts.find? (·.1 == "Machines.echo") | throw (IO.userError "no echo artifact")
  let .ok echoRoot := IxCC.Exe.machine echoArt | throw (IO.userError "echo is not a machine")
  let L : Layout := {}
  let .ok ce := X86.Exe.Machine.writeChecked L echoRoot.symbol echoArt.object
    | throw (IO.userError "echo's executable is not written")
  let image := ce.checked.bytes
  let base := MachineProcess.fileBytes image
  let C : X86.Word := UInt64.ofNat L.callTop
  let tbl := MachineProcess.put64 (MachineProcess.put64 {} C 0) (C + 8) 0
  let retOf (call : Nat) : Nat :=
    if call == 0 then X86.Exe.Process.shellAddr L echoRoot.symbol ce.checked X86.Exe.Machine.B.loop 12
    else X86.Exe.Process.shellAddr L echoRoot.symbol ce.checked X86.Exe.Machine.B.callStep 10
  let mut returns := 0
  for call in [0, 1] do
    for (st, rdx, moved, status) in [((1 : X86.Word), (0 : X86.Word), false, 65), (2, 0, false, 66),
        (3, 0, false, 67), (4, 0, false, 68), (5, 0, false, 70), (0, 7, true, 70), (1, 0, true, 70)] do
      let regs := (((MachineProcess.garbage 2).set .rsp (if moved then C - 16 else C)).set .rax st).set .rdx rdx
      let s : X86.ByteEval.State := { core := ⟨regs, MachineProcess.tableMem tbl base⟩, rip := UInt64.ofNat (retOf call) }
      let run := MachineProcess.simulate image {} 100000 s base tbl
      expect a (run.stop == .exited &&
          run.trace == MachineProcess.report {} status (X86.Exe.Process.messageOf status) 0 1000)
        s!"after call {call} with status {st.toNat}{if moved then ", rsp moved" else ""}: not the report of {status}"
      returns := returns + 1
  for (rdx, want) in [((6 : X86.Word), MachineProcess.report {} IxCC.Exe.Machine.statusNotValue
        (X86.Exe.Process.messageOf IxCC.Exe.Machine.statusNotValue) 0 1000), (7 + 8 * 2048, [.exit 0])] do
    let regs := (((MachineProcess.garbage 2).set .rsp C).set .rax 0).set .rdx rdx
    let s : X86.ByteEval.State := { core := ⟨regs, MachineProcess.tableMem tbl base⟩, rip := UInt64.ofNat (retOf 1) }
    let run := MachineProcess.simulate image {} 100000 s base tbl
    expect a (run.stop == .exited && run.trace == want) s!"after the step returns {rdx.toNat}: not what the model says"
    returns := returns + 1
  out := out.push s!"the shell just after a call returns: {returns} cases (statuses 1 to 5, a moved rsp, an even \
    and an odd word) as the model says"
  -- the negative control: an argument slot in the region (`region + 16`, which the loop block itself
  -- overwrites); the control: the same state with the slot outside the segments
  let callF := MachineProcess.callsOf L ce.checked echoArt.linkedRoots
  let (ρ, _) := MachineProcess.modelLoop callF {} 10000 (IxCC.Exe.Machine.Config.initial []) 0
  let loopAt := UInt64.ofNat (X86.Exe.Process.shellAddr L echoRoot.symbol ce.checked X86.Exe.Machine.B.loop 0)
  for (slot, allowed) in [((UInt64.ofNat (L.regionStart + 16) : X86.Word), false), (0x5000, true)] do
    let t := MachineProcess.put64 (MachineProcess.put64 (MachineProcess.put64 tbl (C + 16) slot) (C + 24) 0x3000) slot 0
    let t := (t.insert 0x3000 90).insert 0x3001 0
    let s : X86.ByteEval.State := { core := ⟨MachineProcess.garbage 9, MachineProcess.tableMem t base⟩, rip := loopAt }
    let σ := (MachineProcess.simulate image {} 3000000 s base t).trace
    expect a ((σ.length ≤ ρ.length && σ == ρ.take σ.length) == allowed)
      s!"the argument slot at {slot.toNat}: the trace is {if allowed then "not " else ""}one the model allows"
  out := out.push "the negative control: an argument slot in the region gives a trace the model does not allow; \
    outside the segments, the model's"
  -- past a call the model shows stuck the comparison claims nothing: echo's object with the first
  -- eight bytes of its step made `06` (no instruction in 64-bit mode; the byte decoder decodes
  -- nothing there), and its executable; the model's first step call is stuck, and the process,
  -- entering the step, reaches a state where `Process.Step` promises nothing
  let some view := X86.ELFRead.parse echoArt.object | throw (IO.userError "echo's object does not parse")
  let some textSection := view.sections[1]? | throw (IO.userError "echo's object has no text section")
  let some stepAt := X86.ELF.symbol? echoArt.object echoRoot.symbol | throw (IO.userError "echo has no step export")
  let broken := (List.range 8).foldl (fun o i => o.set! (textSection.header.offset + stepAt + i) 0x06) echoArt.object
  match X86.Exe.Machine.writeChecked L echoRoot.symbol broken with
  | .error e => expect a false s!"echo with an undecodable step: writeChecked refused: {repr e}"
  | .ok cb =>
    let img := cb.checked.bytes
    let bpl := cb.checked.plan.placement
    let off := bpl.textOffset + stepAt
    expect a ((X86.Decode.decodeAt img off).isNone && img[off]? == some 0x06)
      "echo with an undecodable step: the step's first bytes decode"
    let (b₀, bt) := MachineProcess.loaded img bpl.shellOffset 0x7ffffffde000 0x7ffffffd0000 [] false
    let run := MachineProcess.simulate img {} 3000000 b₀ (MachineProcess.fileBytes img) bt
    let data := X86.Exe.fileBase + bpl.dataOffset
    let (ρ, e) := MachineProcess.model (MachineProcess.callsOf L cb.checked echoArt.linkedRoots) data [] {}
    let more : List X86.Exe.Process.Sys := [.write 1 [65] 1, .other 59, .exit 0]
    expect a (e == .stuck && ρ == X86.Exe.Process.started data)
      s!"echo with an undecodable step: the model does not stop at a stuck first call ({repr e}, \
        {ρ.length} system calls)"
    expect a (run.stop == .unspecified && run.trace == ρ)
      s!"echo with an undecodable step: the process does not stop where Process.Step promises nothing \
        ({repr run.stop}, {run.trace.length} system calls)"
    expect a (MachineProcess.unspecifiedOk run ρ e && MachineProcess.allows ρ e run.trace &&
        MachineProcess.allows ρ e (run.trace ++ more))
      "echo with an undecodable step: the comparison claims something past the stuck call"
    expect a (!MachineProcess.allows ρ .event (run.trace ++ more))
      "echo with an undecodable step: the comparison allows anything even where the model's run ends with an event"
  out := out.push "past a stuck call: echo with an undecodable step stops where Process.Step promises nothing, \
    having made the model's system calls up to its stuck call; the comparison then allows any continuation"
  return out

def part (a : Assert) (o : IxCCTests.Exe.Suite.Options) (work : FilePath) : IO (Array String) := do
  let mut out := #[]
  -- the library is the family's
  let lib ← IO.FS.readFile library
  let src ← IO.FS.readFile source
  expect a (src.startsWith lib) s!"{source} does not begin with {library}"
  out := out.push s!"the family's source begins with {library} ({lib.utf8ByteSize} bytes)"
  -- the interface
  for q in [IxCC.Exe.Machine.Request.arg, .write 1 0, .write 1 255, .write 2 10, .exit 0, .exit 255] do
    expect a (IxCC.Exe.Machine.Request.decode q.encode == some q && q.encode < IxCC.Exe.Machine.requestSpan)
      s!"request {repr q}: field {q.encode}"
  for r in [8, 4, 5, 6, 7, 2047] do
    expect a (IxCC.Exe.Machine.Request.decode r).isNone s!"request field {r} decodes"
  -- the layout
  expect a ({} : Layout).check "the default layout"
  for (stack, region, ok) in [(8192, 4096, true), (1 <<< 28, 1 <<< 24, true), (8176, 4096, false),
      (8200, 4096, false), (8192, 4095, false), (1 <<< 39, (1 <<< 39) - (1 <<< 13), true),
      (1 <<< 39, 1 <<< 39, false), (0, 1 <<< 20, false)] do
    expectEq a (({ stack, region } : Layout).check) ok s!"machine Layout.check --stack {stack} --region {region}"
  -- the shell
  for L in [({ stack := 8192, region := 4096 } : Layout), {}] do
    let p := X86.Exe.Machine.shell L "cx_step" 0x400400
    match X86.Exe.Shell.encode p with
    | .error _ => expect a false s!"the machine shell does not encode for {repr L}"
    | .ok e =>
      let sites := X86.Exe.Shell.syscallOffsets p e
      expectEq a sites.length 5 s!"the machine shell's system-call sites, {repr L}"
      for off in sites do
        expect a (e.text[off]? == some 0x0f && e.text[off + 1]? == some 0x05) s!"syscall at {off}"
      expect a (e.exportCalls.toList.map (·.2) == [X86.Exe.initSymbol, "cx_step"]) "the shell's calls"
      out := out.push s!"the shell for {repr L}: {e.text.size} bytes, {p.blocks.size} blocks"
  let data := X86.Exe.Machine.dataBytes 0x400800
  expect a (data.toList.take X86.Exe.filter.length == X86.Exe.filter) "the shell's filter is --exe's"
  -- the writer and its check, on the family's roots
  let mut fibArt? : Option Artifact := none
  let mut arts : Array (String × Artifact) := #[]
  for root in ["Machines.fibMain", "Machines.idMain", "Machines.echo"] do
    let (_, _, art) ← compileNamed machines "machines" root
    if root == "Machines.fibMain" then fibArt? := some art
    arts := arts.push (root, art)
    match IxCC.Exe.buildMachine art with
    | .error e => expect a false s!"{root}: {e.render}"
    | .ok ⟨r, c⟩ =>
      let f := X86.Exe.Machine.frame {} r.symbol
      let bytes := c.checked.bytes
      let p := c.checked.plan.placement
      expect a (X86.Exe.checkFrame f art.object bytes) s!"{root}: the check refuses the written file"
      expectEq a c.checked.plan.calls.length 2 s!"{root}: calls"
      expectEq a c.checked.plan.syscalls.length 5 s!"{root}: system-call sites"
      let sample (lo n : Nat) := (List.range ((n + 6) / 7)).map (lo + 7 * ·)
      let offsets := List.range (X86.Exe.headersSizeFor f.segments.length) ++ sample p.noteOffset p.noteSize ++
        sample p.textOffset p.textSize ++ sample p.dataOffset p.dataSize ++ sample p.shellOffset p.shellSize
      let mut refused := 0
      for off in offsets do
        let some byte := bytes[off]? | continue
        expect a (!X86.Exe.checkFrame f art.object (bytes.set! off (byte ^^^ 0x10)))
          s!"{root}: byte {off} changed, accepted"
        refused := refused + 1
      for len in (List.range (bytes.size / 64)).map (· * 64) do
        expect a (!X86.Exe.checkFrame f art.object (bytes.extract 0 len)) s!"{root}: truncated to {len}, accepted"
        refused := refused + 1
      expect a (!X86.Exe.checkFrame f art.object (bytes.push 0)) s!"{root}: a byte appended, accepted"
      out := out.push s!"{root}: {bytes.size} bytes (text {p.textSize}, data {p.dataSize}, shell {p.shellSize}), \
        {f.segments.length + 3} program headers; {refused + 1} mutations refused"
      -- the shell check (`Shell.check`, which `writeChecked` runs): the written file passes; an opcode, a
      -- block's displacement, the step call's target and the system-call bytes, each changed, are refused,
      -- and so is the first byte of every instruction and terminator, changed
      let pl := c.checked.plan
      let shellOk (b : ByteArray) : Bool := X86.Exe.Machine.shellOk f art.object pl b
      expect a (shellOk bytes) s!"{root}: the shell check refuses the written file"
      let prog := f.code (X86.Exe.fileBase + p.dataOffset)
      let blockAt (b : Nat) : Nat := p.shellOffset + X86.Exe.Shell.blockOffset prog b
      let flip (off : Nat) (mask : UInt8) : ByteArray :=
        match bytes[off]? with
        | some byte => bytes.set! off (byte ^^^ mask)
        | none => bytes
      let setup := prog.blocks[X86.Exe.Machine.B.setup]!
      let named : List (String × Nat × UInt8) :=
        [("an opcode (loop's first instruction)", blockAt X86.Exe.Machine.B.loop, 0x10),
         ("a block displacement (setup's jump to loop)",
           blockAt X86.Exe.Machine.B.setup + X86.Exe.Shell.instrOffset setup setup.instructions.size + 1, 0x01),
         ("the step call's target", (pl.calls[1]?.map (·.field)).getD 0, 0x01),
         ("the system-call bytes (0F 05 to 0F 04 at the first site)", (pl.syscalls.head?.getD 0) + 1, 0x01)]
      for (what, off, mask) in named do
        expect a (p.shellOffset ≤ off && off < p.shellOffset + p.shellSize) s!"{root}: {what}: byte {off} outside the shell"
        expect a (!shellOk (flip off mask)) s!"{root}: {what} changed (byte {off}), the shell check accepts"
      let mut swept := 0
      for b in List.range prog.blocks.size do
        let blk := prog.blocks[b]!
        for j in List.range (blk.instructions.size + 1) do
          let off := blockAt b + X86.Exe.Shell.instrOffset blk j
          expect a (!shellOk (flip off 0x10)) s!"{root}: block {b}, item {j}: its first byte changed, accepted"
          swept := swept + 1
      out := out.push s!"{root}: the shell check passes the file and refuses {named.length} named mutations and \
        the first byte of each of its {swept} instructions and terminators, changed"
      -- the parts of the call lemma's call site (`AtCall`, `IxCC/X86/Exe/Machine/Proof/Call.lean`) that the
      -- file decides, at the real `cx_init` and step call sites: the call decodes and lands on its export,
      -- its return address and the stack pointer it leaves are the driver's, the driver keeps the
      -- contract, and the file holds the object's text inside the address space
      let text := (X86.ELFRead.text? art.object).getD ByteArray.empty
      expect a ((X86.ELFRead.text? art.object).isSome && decide (p.textOffset + text.size ≤ 2 ^ 64) &&
          (List.range text.size).all fun i => bytes[p.textOffset + i]? == text[i]?)
        s!"{root}: the file does not hold the object's text at {p.textOffset}"
      for c in pl.calls do
        let D := ({} : Layout).driverWith p.textOffset c.ret fun _ => 0
        let pos := c.field - 1
        let rip : X86.Word := UInt64.ofNat (X86.Exe.fileBase + pos)
        let lands := match X86.ELF.symbol? art.object c.symbol, X86.Decode.decodeAt bytes pos with
          | some offset, some ⟨.op _ [.imm v], 5⟩ =>
            X86.Decode.decodeAt bytes (rip - UInt64.ofNat X86.Exe.fileBase).toNat ==
                some ⟨X86.Decode.Operation.call v.toUInt32, 5⟩ &&
              X86.ByteEval.relative (rip + 5) v.toUInt32 == D.base + UInt64.ofNat offset
          | _, _ => false
        expect a (lands && D.ret == rip + 5 && D.sp + 8 == UInt64.ofNat ({} : Layout).callTop &&
            D.checkOk p.textSize)
          s!"{root}: the call of {c.symbol} at byte {pos} is not a call site the call lemma describes"
      out := out.push s!"{root}: the file decides the call lemma's call-site facts at its {pl.calls.length} calls"
      -- the shell proof's drivers take their return addresses from the shell's block offsets
      -- (`X86.Exe.Process.shellAddr`, `initDriverOf`, `stepSite`): they are the plan's recorded ones
      let computed := [X86.Exe.Process.shellAddr {} r.symbol c.checked X86.Exe.Machine.B.loop 12,
        X86.Exe.Process.shellAddr {} r.symbol c.checked X86.Exe.Machine.B.callStep 10]
      expect a (pl.calls.map (·.ret) == computed)
        s!"{root}: the calls' return addresses {pl.calls.map (·.ret)} are not the shell's {computed}"
      -- `textSize_eq` and `machine_linkedRoot` (the executable theorems' production facts) on this
      -- artifact: the file's text is the encoded text, and the linked object's root 0 is the root
      -- `Exe.machine` accepts, with two parameters and a `Nat` result
      expectEq a p.textSize art.backend.encoded.text.size s!"{root}: the file's text size"
      let rootOk := match art.linkedRoots[0]? with
        | some x => x.symbol == r.symbol && x.params == 2 && (match x.ty with | some (_, .nat) => true | _ => false)
        | none => false
      expect a rootOk s!"{root}: the linked object's root 0 is not the machine's step"
      out := out.push s!"{root}: the drivers' return addresses are the plan's; the text size and root 0 are \
        what the executable theorems say"
  out := out ++ (← shellAgainstModel a o arts)
  let some fibArt := fibArt? | throw (IO.userError "Machines.fibMain did not compile")
  -- refusals
  let some fibRoot := fibArt.roots.head? | throw (IO.userError "Machines.fibMain: no root")
  let refused (label : String) (L : Layout) (step : String) (want : X86.Exe.Error) : IO Unit :=
    match X86.Exe.Machine.writeChecked L step fibArt.object with
    | .ok _ => expect a false s!"{label}: written"
    | .error e => expectEq a (repr e |>.pretty) (repr want |>.pretty) s!"{label}: refusal"
  refused "a missing export" {} "cx_nothing" (.missingExport "cx_nothing")
  refused "a stack under 8 KiB" { stack := 4096 } fibRoot.symbol .layout
  refused "a region under 4 KiB" { region := 4095 } fibRoot.symbol .layout
  -- the shell check at the smallest and a large layout (whose constants need `movabs`)
  for L in [({ stack := 8192, region := 4096 } : Layout), { stack := 1 <<< 39, region := (1 <<< 39) - (1 <<< 13) }] do
    match X86.Exe.Machine.writeChecked L fibRoot.symbol fibArt.object with
    | .ok _ => pure ()
    | .error e => expect a false s!"fib's machine executable for {repr L}: {repr e}"
  -- the writer refuses a shell the check does not cover: an unwind (not a linear row) or a branch whose
  -- false edge falls through, each in the first block; the machine frame itself is written
  let machineFrame := X86.Exe.Machine.frame {} fibRoot.symbol
  let firstBlock (g : X86.Exe.Shell.Block → X86.Exe.Shell.Block) : X86.Exe.Frame :=
    { machineFrame with code := fun d => { blocks := (machineFrame.code d).blocks.modify 0 g } }
  let unwind : X86.Exe.Shell.Instr :=
    .instr (.unwind { base := some .rbp, index := none, scale := .one, displacement := 0 })
  let falls (blk : X86.Exe.Shell.Block) : X86.Exe.Shell.Block :=
    match blk.terminator with
    | .branch o args cond t e _ => { blk with terminator := .branch o args cond t e .fall }
    | _ => blk
  for (what, fr) in [("an unwind", firstBlock fun blk => { blk with instructions := #[unwind] ++ blk.instructions }),
      ("a branch falling through", firstBlock falls)] do
    match X86.Exe.Machine.writeCheckedFor fr {} fibArt.object with
    | .ok _ => expect a false s!"a machine shell with {what}: written"
    | .error e =>
      expectEq a (repr e |>.pretty) (repr X86.Exe.Error.invalidExecutable |>.pretty)
        s!"a machine shell with {what}: refusal"
  match X86.Exe.Machine.writeCheckedFor machineFrame {} fibArt.object with
  | .ok _ => pure ()
  | .error e => expect a false s!"writeCheckedFor of the machine frame: {repr e}"
  out := out.push "the shell check: fib's executable at the smallest and a large layout written; a shell with an \
    unwind or a falling-through branch refused (invalidExecutable)"
  for (manifest, fixture, root) in [(benchK1, "fib", "entry"), (abi, "abi", "Abi.bool2"), (abi, "abi", "Abi.nat3")] do
    let (_, _, art) ← compileNamed manifest fixture root
    match IxCC.Exe.machine art with
    | .error e => expectEq a e.code "exe.machine" s!"{root}: refusal"
    | .ok _ => expect a false s!"{root} accepted as a machine"
  let mx := "fixtures/corpus/phase1-machines"
  let code ← IxCC.Cli.main ["compile", s!"{mx}/machines.ixe", "--equations", s!"{mx}/machines.equations.json",
    "--root", "Machines.fibMain", "-o", (work / "m.o").toString, "--machine"]
  expectEq a code 2 "--machine without --exe"
  let fx := "fixtures/ixon-v4/bench-k1"
  let code ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--exe", (work / "not-a-machine").toString, "--machine"]
  expectEq a code 1 "ixcc compile --exe --machine of a root of one parameter"
  out := out.push "refusals: a missing export, two layouts; fib's entry, Abi.bool2 and Abi.nat3 (exe.machine); \
    --machine without --exe, and --machine on fib's entry"
  if !o.run then return out
  -- natively: fib with Lean parsing and rendering, against --exe's fib
  let fibM := work / "fib.machine"
  let idM := work / "id.machine"
  let fibHO := work / "fibho.machine"
  let bad := work / "bad.machine"
  let echo := work / "echo.machine"
  for (root, path) in [("Machines.fibMain", fibM), ("Machines.idMain", idM), ("Machines.fibMainHO", fibHO),
      ("Machines.badRequest", bad), ("Machines.echo", echo)] do
    let (_, _, art) ← compileNamed machines "machines" root
    match IxCC.Exe.buildMachine art with
    | .error e => throw (IO.userError s!"{root}: {e.render}")
    | .ok ⟨_, c⟩ => IxCCTests.Exe.writeExe path c.checked.bytes
  let (_, _, x0Art) ← compileNamed benchK1 "fib" "entry"
  let fibX0 := work / "fib.exe"
  match ← IxCCTests.Exe.build fibX0 x0Art {} with
  | .error e => throw (IO.userError e.render)
  | .ok () => pure ()
  let numeral := X86.Exe.Message.text 1 .numeral
  let same := [["0"], ["1"], ["2"], ["10"], ["25"], ["007"], [], ["1", "2"], ["1", "2", "3"], [""], ["12x"],
    ["x12"], ["-1"], ["+1"], [" 1"], ["1 "], ["0x10"], ["1_0"], ["١"], ["18446744073709551616x"]]
  for args in same do
    let m ← IxCCTests.Exe.run fibM args
    let x ← IxCCTests.Exe.run fibX0 args
    expect a (m.code == x.code && m.stdout == x.stdout && m.stderr == x.stderr)
      s!"fib {args}: the machine exits {m.code}, {repr m.stdout}, {repr m.stderr}; --exe exits {x.code}, \
        {repr x.stdout}, {repr x.stderr}"
  for big in ["9223372036854775808", "18446744073709551615", "18446744073709551616",
      "340282366920938463463374607431768211456"] do
    let x ← IxCCTests.Exe.run fibX0 [big]
    expectEq a x.code 67 s!"--exe fib {big}"
    runChecked a "the fib machine" fibM [big] 67 "" rangeMessage
  out := out.push s!"fib with Lean parsing and rendering against --exe's fib: {same.length} argument lists \
    alike (counts, non-numerals, numerals), and four numerals of 2^63 and more exit 67 (the machine's \
    message is its range's)"
  runChecked a "the identity" idM ["281474976710655"] 0 "281474976710655\n" ""
  runChecked a "the identity" idM ["0"] 0 "0\n" ""
  runChecked a "the identity" idM ["281474976710656"] 67 "" rangeMessage
  runChecked a "fib through a closure" fibHO ["25"] 0 "75025\n" ""
  runChecked a "fib through a closure" fibHO ["x"] 3 "" numeral
  runChecked a "a request outside the interface" bad [] 72 ""
    (X86.Exe.Machine.Failure.text .request)
  out := out.push "the identity at 2^48 - 1 and 2^48; fib through a closure; a request outside the interface (72)"
  -- a write the platform refuses: standard output closed, so the program exits 74
  let closed ← IO.Process.output { cmd := "sh", args := #["-c", "exec \"$0\" \"$@\" >&-", fibM.toString, "10"] }
  expect a (closed.exitCode == 74 && closed.stderr.isEmpty)
    s!"fib 10 with standard output closed: exit {closed.exitCode}, {repr closed.stderr}"
  out := out.push "a refused write (standard output closed): the program exits 74"
  -- echo sessions against Lean's interpreter
  for (args, o', e', status, _) in echoSessions do
    let (code, stdout, stderr) ← runBytes echo args
    expect a (code.toNat == status && stdout == hexBytes o' && stderr == hexBytes e')
      s!"echo {args}: exit {code}, {stdout.size} and {stderr.size} bytes"
  out := out.push s!"echo: {echoSessions.length} sessions equal the transcripts of Lean's interpreter"
  -- the long sessions, three ways: Lean's transcript, the executable, and the
  -- session model (`Exe.Machine.runFor`, whose trace `runFor_performs` says the
  -- model allows) with the linked object's calls on the byte evaluator, under
  -- the driver the executable's step call is meant to see
  let (_, _, echoArt) ← compileNamed machines "machines" "Machines.echo"
  expectEq a MachineSessions.transcripts.length MachineSessions.sessions.length
    "the long sessions' transcripts (run tests-exe --session-lines through the oracle)"
  match IxCC.Exe.buildMachine echoArt with
  | .error e => expect a false s!"Machines.echo: {e.render}"
  | .ok ⟨_, c⟩ =>
    let some stepCall := c.checked.plan.calls[1]? | throw (IO.userError "Machines.echo: no step call")
    let D := ({} : Layout).driverWith c.checked.plan.placement.textOffset stepCall.ret fun _ => 0
    let call := fun s e => IxCC.Sem.Lang.run (echoArt.linked D) (0, [s, e]) 1000000
    let mut longest := 0
    for (args, (o', e', status, calls)) in MachineSessions.sessions.zip MachineSessions.transcripts do
      let bytes := args.map fun s => s.toUTF8.toList.map (·.toNat)
      let t := IxCC.Exe.Machine.runFor call true 100000 (.initial bytes)
      let outB : ByteArray := ⟨(t.filterMap fun | .write 1 b true => some (UInt8.ofNat b) | _ => none).toArray⟩
      let errB : ByteArray := ⟨(t.filterMap fun | .write 2 b true => some (UInt8.ofNat b) | _ => none).toArray⟩
      let ended := match t.getLast? with
        | some (.exit code) => some code
        | _ => none
      let size := (bytes.map List.length).sum
      expect a (outB == hexBytes o' && errB == hexBytes e' && ended == some status && t.length == calls)
        s!"echo, {size} argument bytes: the model on the byte evaluator makes {t.length} calls and ends \
          {repr ended}; Lean's interpreter {calls} and {status}"
      expect a (1000 ≤ calls && 600 ≤ size) s!"echo: a session of {calls} calls over {size} bytes"
      let (code, stdout, stderr) ← runBytes echo args
      expect a (code.toNat == status && stdout == hexBytes o' && stderr == hexBytes e')
        s!"echo, {size} argument bytes: the executable exits {code} with {stdout.size} and {stderr.size} bytes"
      longest := max longest calls
    out := out.push s!"echo: {MachineSessions.sessions.length} long sessions (up to {longest} calls) agree three \
      ways: Lean's transcript, the executable, and the session model on the byte evaluator"
  -- confinement, read from /proc while a long run is under way
  let mine := filters (← IO.FS.readFile "/proc/self/status")
  let child ← IO.Process.spawn { cmd := fibM.toString, args := #["38"], stdout := .null, stderr := .null }
  let status := s!"/proc/{child.pid}/status"
  let mut seen := false
  for _ in List.range 2000 do
    match ← (IO.FS.readFile status).toBaseIO with
    | .ok text =>
      if filters text == mine.map (· + 1) && field text "Seccomp" == some "2" &&
          field text "NoNewPrivs" == some "1" then
        seen := true
        break
    | .error _ => break
    IO.sleep 1
  let code ← child.wait
  expect a seen s!"fib 38: no added seccomp filter seen in /proc (this process has {mine})"
  expectEq a code 0 "fib 38: exit"
  out := out.push "confinement: one seccomp filter more than the suite's, filter mode, NoNewPrivs, while running"
  -- the system calls under strace: prctl, seccomp, then writes to 1 or 2, then exit
  if let some st := o.strace then
    for (exe, args) in [(fibM, ["20"]), (fibM, ["x"]), (echo, ["ab"])] do
      let log := work / "strace-machine.log"
      let _ ← IO.Process.output { cmd := st, args := #["-qq", "-o", log.toString, exe.toString] ++ args.toArray }
      let text ← IO.FS.readFile log
      let calls : List String := (text.splitOn "\n").filter fun (l : String) => !l.isEmpty && !l.startsWith "+++"
      let names : List String := calls.map fun (l : String) => (l.takeWhile (· != '(')).toString.trimAscii.toString
      expect a (names.take 3 == ["execve", "prctl", "seccomp"] && names.getLast? == some "exit" &&
          (names.drop 3).dropLast.all (· == "write") && names.length > 4)
        s!"{exe} {args}: its system calls under strace: {names}"
      expect a (calls.all fun l => !(l.startsWith "write(") || l.startsWith "write(1," || l.startsWith "write(2,")
        s!"{exe} {args}: a write to a descriptor other than 1 or 2"
    out := out.push "system calls under strace: execve, prctl, seccomp, then writes to 1 or 2, then exit"
  -- ixcc compile --exe --machine, in-process
  let cliExe := work / "cli_machine"
  let code ← IxCC.Cli.main ["compile", s!"{mx}/machines.ixe", "--equations", s!"{mx}/machines.equations.json",
    "--root", "Machines.fibMain", "--exe", cliExe.toString, "--machine", "--stack", "65536", "--region", "8192"]
  expectEq a code 0 "ixcc compile --exe --machine"
  runChecked a "ixcc compile --exe --machine" cliExe ["10"] 0 "55\n" ""
  out := out.push "ixcc compile --exe --machine: fib runs"
  return out

end IxCCTests.Exe.Machine
