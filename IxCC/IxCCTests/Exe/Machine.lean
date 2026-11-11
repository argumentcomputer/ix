import IxCCTests.Exe.Run

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
  `Exe.machine` refuses first roots of another shape (`exe.machine`);
  `ixcc compile --machine` without `--exe` is a usage error.
* **Natively** (`--run`, x86-64 Linux): `fib` with Lean parsing and rendering
  against `--exe`'s `fib` on the same arguments (equal output and status, the
  message differing only for numerals of `2^63` and more); the identity at the
  range's edges; `fib` through a closure; a request outside the interface
  (72); a write the platform refuses (stdout closed: the program exits 74);
  three `echo` sessions against the transcripts Lean's interpreter printed;
  the confinement read from `/proc`; the system calls under `strace`; and
  `ixcc compile --exe --machine` in-process. -/

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
  for root in ["Machines.fibMain", "Machines.idMain", "Machines.echo"] do
    let (_, _, art) ← compileNamed machines "machines" root
    if root == "Machines.fibMain" then fibArt? := some art
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
