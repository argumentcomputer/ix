import IxCCTests.Corpus.Run
import IxCC.Cli

/-! The standalone executable suite (`tests-exe`): what `ixcc compile --exe`
writes, apart from the corpus's cases (which `tests-corpus --exe` runs as
executables against SrcEval, ByteEval and the C driver).

* **The layout**: `Layout.check` accepts the layouts inside the driver
  contract and refuses the others; every executable written below carries
  the contract at both of its calls (`Certified.contract`).
* **The shell**: for every arity up to five and each result kind it encodes,
  makes exactly four system calls (`prctl`, `seccomp`, `write`, `exit`) and
  calls `cx_init`, then the root.
* **The writer and its check**: executables of K1 roots and of the scalar
  ABI corpus's `Bool` and enumeration roots pass `X86.Exe.check`; every mutated
  byte of the headers, a sample of every part, every truncation and an
  appended byte are refused; the writer refuses a missing export, more than
  five parameters, an empty enumeration and layouts outside the contract;
  `Exe.fragment` refuses a root with a non-`Nat` parameter (`exe.params`) and
  constructor-tree results (`exe.result`).
* **Natively** (`--run`, x86-64 Linux only): malformed arguments end with
  their own status and message and print nothing; arguments of `2^64` and
  more end as `natOverflow`; a trapping root (written directly, since its
  parameter is not a `Nat`) ends with status 68 as ByteEval traps; the
  process runs under a seccomp filter with no new privileges (read from
  `/proc` while it runs); with `--strace PATH` its system calls are exactly
  `execve`, `prctl`, `seccomp`, `write` and `exit`, on success and on
  failure; and `ixcc compile --exe` itself, in-process, writes executables
  (also of a plain-RC `Nat` root) and refuses what it should. -/

namespace IxCCTests.Exe.Suite

open IxCC IxCC.Recheck IxCCTests.Src IxCCTests.Corpus
open System
open IxCC.X86.Exe (Layout ResultKind)

structure Options where
  run : Bool := false
  strace : Option String := none
  deriving Inhabited

/-- Compile one root of a corpus fixture (as `tests-corpus` does). -/
def compileNamed (manifest : FilePath) (fixture root : String) : IO (Corpus.Root × Cert × Artifact) := do
  let m ← Family.read manifest
  let some f := m.fixtures.find? (·.name == fixture) | throw (IO.userError s!"no fixture {fixture}")
  let some r := f.roots.find? (·.name == root) | throw (IO.userError s!"no root {root}")
  match ← compileRoot m f r with
  | .ok (cert, art) => pure (r, cert, art)
  | .error e => throw (IO.userError s!"{root}: {e.render}")

def benchK1 : FilePath := "fixtures/ixon-v4/bench-k1/corpus.json"
def scalar : FilePath := "fixtures/corpus/phase1-scalar/corpus.json"
def resource : FilePath := "fixtures/corpus/phase1-resource/corpus.json"
def abi : FilePath := "fixtures/corpus/phase1-abi/corpus.json"

/-! ## The layout and the shell -/

def layoutPart (a : Assert) : IO Unit := do
  expect a ({} : Layout).check "the default layout is inside the contract"
  for (stack, region, ok) in [(8192, 4096, true), (1 <<< 28, 1 <<< 24, true), (8176, 4096, false),
      (8200, 4096, false), (8192, 4095, false), (1 <<< 39, 1 <<< 39, true), (1 <<< 39, (1 <<< 39) + 1, false),
      (0, 1 <<< 20, false)] do
    expectEq a (({ stack, region } : Layout).check) ok s!"Layout.check --stack {stack} --region {region}"

def shellPart (a : Assert) : IO Unit := do
  for arity in List.range 6 do
    for result in [ResultKind.nat, .enum 1, .enum 2, .enum 200] do
      let spec : X86.Exe.Spec := { arity, result, root := "cx_root", layout := {}, data := 0x400400 }
      let p := X86.Exe.shell spec
      match IxCC.X86.Exe.Shell.encode p with
      | .error _ => expect a false s!"the shell for arity {arity}, {repr result} does not encode"
      | .ok e =>
        expectEq a (IxCC.X86.Exe.Shell.syscallOffsets p e).length 4 s!"arity {arity}: system calls"
        expect a (e.exportCalls.toList.map (·.2) == [X86.Exe.initSymbol, "cx_root"])
          s!"arity {arity}: the calls into the object"
        -- each system call is the two bytes `0F 05`
        for off in IxCC.X86.Exe.Shell.syscallOffsets p e do
          expect a (e.text[off]? == some 0x0f && e.text[off + 1]? == some 0x05) s!"arity {arity}: syscall at {off}"
  expectEq a X86.Exe.filter.length (8 * X86.Exe.filterLength) "the filter's length"

/-! ## The writer and its check -/

/-- Every one-bit change of the bytes at `offsets`, every truncation at the
`step`th prefixes and an appended byte are refused by the check. -/
def mutations (a : Assert) (label : String) (i : X86.Exe.Input) (bytes : ByteArray) (offsets : List Nat)
    (step : Nat) : IO Nat := do
  let mut n := 0
  for off in offsets do
    let some b := bytes[off]? | continue
    let mutated := bytes.set! off (b ^^^ 0x10)
    expect a (!X86.Exe.check i mutated) s!"{label}: byte {off} changed, accepted"
    n := n + 1
  for len in (List.range (bytes.size / step)).map (· * step) do
    expect a (!X86.Exe.check i (bytes.extract 0 len)) s!"{label}: truncated to {len}, accepted"
    n := n + 1
  expect a (!X86.Exe.check i (bytes.push 0)) s!"{label}: a byte appended, accepted"
  return n + 1

def writerPart (a : Assert) (work : FilePath) : IO (Array String) := do
  let mut out := #[]
  for (manifest, fixture, root) in [(benchK1, "fib", "entry"), (benchK1, "gcd", "entry"),
      (benchK1, "tak", "entry"), (abi, "abi", "Abi.bool1"), (abi, "abi", "Abi.tri1")] do
    let (r, _, art) ← compileNamed manifest fixture root
    match IxCC.Exe.build art with
    | .error e => expect a false s!"{fixture}/{root}: {e.render}"
    | .ok ⟨i, c⟩ =>
      expect a (X86.Exe.check i c.bytes) s!"{fixture}/{root}: the check refuses the written file"
      expectEq a i.arity r.params s!"{fixture}/{root}: arity"
      expectEq a c.plan.calls.length 2 s!"{fixture}/{root}: calls"
      expectEq a c.plan.syscalls.length 4 s!"{fixture}/{root}: system calls"
      let p := c.plan.placement
      let sample (lo n : Nat) := (List.range ((n + 6) / 7)).map (lo + 7 * ·)
      let offsets := List.range X86.Exe.headersSize ++ sample p.noteOffset p.noteSize ++
        sample p.textOffset p.textSize ++ sample p.dataOffset p.dataSize ++ sample p.shellOffset p.shellSize
      let n ← mutations a s!"{fixture}/{root}" i c.bytes offsets 16
      out := out.push s!"{fixture}/{root}: {c.bytes.size} bytes (text {p.textSize}, data {p.dataSize}, \
        shell {p.shellSize}); {n} mutations refused"
  -- the writer's refusals
  let (_, _, fib) ← compileNamed benchK1 "fib" "entry"
  let base : X86.Exe.Input := { object := fib.object, root := "cx_entry", arity := 1, result := .nat }
  let refused (label : String) (i : X86.Exe.Input) (want : X86.Exe.Error) : IO Unit :=
    match X86.Exe.writeChecked i with
    | .ok _ => expect a false s!"{label}: written"
    | .error e => expectEq a (repr e |>.pretty) (repr want |>.pretty) s!"{label}: refusal"
  refused "a missing export" { base with root := "cx_nothing" } (.missingExport "cx_nothing")
  refused "six parameters" { base with arity := 6 } (.arity 6)
  refused "an empty enumeration" { base with result := .enum 0 } .enumeration
  refused "a stack under 8 KiB" { base with layout := { stack := 4096 } } .layout
  refused "a region under 4 KiB" { base with layout := { region := 4095 } } .layout
  refused "not an object" { base with object := ByteArray.mk #[0x7f, 0x45, 0x4c, 0x46] } .unreadableObject
  -- the fragment's refusals
  let (_, _, trap) ← compileNamed resource "resource" "Resource.trapEmpty"
  match IxCC.Exe.fragment trap with
  | .error e => expectEq a e.code "exe.params" "Resource.trapEmpty: refusal"
  | .ok _ => expect a false "Resource.trapEmpty (an Empty parameter) is accepted"
  -- ixcc compile --exe's refusals
  let fx := "fixtures/ixon-v4/bench-k1"
  let rs := "fixtures/rc/real-source"
  let treeExe := work / "cli_tree"
  let code ← IxCC.Cli.main ["compile", s!"{rs}/anonymous.ixe", "--equations", s!"{rs}/consumer.equations.json",
    "--rc", "on", "--exe", treeExe.toString]
  expectEq a code 1 "ixcc compile --exe of a constructor-tree root"
  expect a (!(← treeExe.pathExists)) "the refused executable was written"
  let code ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--exe", (work / "cli_small").toString, "--stack", "4096"]
  expectEq a code 1 "ixcc compile --exe --stack 4096"
  let code ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "-o", (work / "fib.o").toString, "--stack", "65536"]
  expectEq a code 2 "--stack without --exe"
  out := out.push "refusals: a missing export, six parameters, an empty enumeration, two layouts, \
    not an object; Resource.trapEmpty (exe.params); ixcc compile --exe of the RC fixture's \
    constructor-tree root (exe.result), with a 4 KiB stack (exe.layout), and --stack without --exe"
  return out

/-! ## Natively -/

def runChecked (a : Assert) (label : String) (exe : FilePath) (args : List String) (code : UInt32)
    (stdout stderr : String) : IO Unit := do
  let r ← IxCCTests.Exe.run exe args
  expect a (r.code == code && r.stdout == stdout && r.stderr == stderr)
    s!"{label} {args}: exit {r.code}, stdout {repr r.stdout}, stderr {repr r.stderr}; expected exit {code}, \
      stdout {repr stdout}, stderr {repr stderr}"

/-- The system calls of one run under `strace`, by name. -/
def straced (strace : String) (work : FilePath) (exe : FilePath) (args : List String) : IO (List String) := do
  let log := work / "strace.log"
  let _ ← IO.Process.output { cmd := strace, args := #["-qq", "-o", log.toString, exe.toString] ++ args.toArray }
  let text ← IO.FS.readFile log
  return (text.splitOn "\n").filterMap fun line =>
    let name := (line.takeWhile (· != '(')).toString.trimAscii.toString
    if name.isEmpty || name.startsWith "+++" then none else some name

/-- A field of `/proc/PID/status`. -/
def field (status name : String) : Option String :=
  (status.splitOn "\n").findSome? fun line =>
    if line.startsWith (name ++ ":") then some ((line.drop (name.length + 1)).trimAscii.toString) else none

/-- The number of seccomp filters in `/proc/PID/status`. -/
def filters (status : String) : Option Nat := (field status "Seccomp_filters").bind String.toNat?

def nativePart (a : Assert) (o : Options) (work : FilePath) : IO (Array String) := do
  let mut out := #[]
  let (_, _, fibArt) ← compileNamed benchK1 "fib" "entry"
  let (_, _, gcdArt) ← compileNamed benchK1 "gcd" "entry"
  let fib := work / "fib"
  let gcd := work / "gcd"
  for (path, art) in [(fib, fibArt), (gcd, gcdArt)] do
    match ← IxCCTests.Exe.build path art {} with
    | .error e => throw (IO.userError e.render)
    | .ok () => pure ()
  let count1 := X86.Exe.Message.text 1 .count
  let count2 := X86.Exe.Message.text 2 .count
  let numeral := X86.Exe.Message.text 1 .numeral
  let natOverflow := X86.Exe.Message.text 1 .natOverflow
  runChecked a "fib" fib ["25"] 0 "75025\n" ""
  runChecked a "fib" fib ["007"] 0 "13\n" ""
  runChecked a "fib" fib [] 2 "" count1
  runChecked a "fib" fib ["1", "2"] 2 "" count1
  for bad in ["", "12x", "x12", "-1", "+1", " 1", "1 ", "0x10", "1_0", "١"] do
    runChecked a "fib" fib [bad] 3 "" numeral
  for big in ["9223372036854775808", "18446744073709551615", "18446744073709551616",
      "340282366920938463463374607431768211456"] do
    runChecked a "fib" fib [big] 67 "" natOverflow
  -- a numeral past 2^64 followed by junk is not a numeral
  runChecked a "fib" fib ["18446744073709551616x"] 3 "" numeral
  runChecked a "gcd" gcd ["1071", "462"] 0 "21\n" ""
  runChecked a "gcd" gcd ["1071"] 2 "" count2
  runChecked a "gcd" gcd ["1071", "462", "1"] 2 "" count2
  runChecked a "gcd" gcd ["1071", "4x"] 3 "" numeral
  out := out.push "malformed arguments: counts, ten non-numerals, four numerals of 2^63 and more"
  -- a root of no parameters
  let m ← Family.read abi
  let zero := m.fixtures.flatMap fun f => f.roots.filter (fun r => r.params == 0 && r.result == "nat" &&
    r.decline.isNone && !r.cases.isEmpty) |>.map (f, ·)
  if let some (f, r) := zero.head? then
    let (_, _, art) ← compileNamed abi f.name r.name
    let exe := work / "zero"
    match ← IxCCTests.Exe.build exe art {} with
    | .error e => expect a false s!"{r.name}: {e.render}"
    | .ok () =>
      let some cs := r.cases.head? | pure ()
      runChecked a r.name exe [] 0 s!"{cs.value}\n" ""
      runChecked a r.name exe ["0"] 2 "" (X86.Exe.Message.text 0 .count)
      out := out.push s!"no parameters: {r.name}"
  -- a trap: the writer runs a root the CLI refuses (its parameter is Empty)
  let (_, cert, trapArt) ← compileNamed resource "resource" "Resource.trapEmpty"
  let some root := trapArt.roots.head? | throw (IO.userError "no root")
  let i : X86.Exe.Input := { object := trapArt.object, root := root.symbol, arity := root.params, result := .nat }
  match X86.Exe.writeChecked i with
  | .error e => expect a false s!"Resource.trapEmpty: {e.render}"
  | .ok c =>
    let exe := work / "trap"
    IxCCTests.Exe.writeExe exe c.bytes
    runChecked a "Resource.trapEmpty" exe ((List.replicate root.params "0")) 68 ""
      (X86.Exe.Message.text 1 .trap)
    let compiled ← Pipeline.Levels.assemble "trapEmpty" cert trapArt
    let (outcome, _) ← Pipeline.Levels.runLevel compiled "bytes" (List.replicate root.params 0)
    expectEq a outcome "status 4" "Resource.trapEmpty: ByteEval"
    out := out.push "a trap: Resource.trapEmpty, status 68 as ByteEval's status 4"
  -- confinement, read from /proc while a long run is under way: one more
  -- seccomp filter than this process has (a build sandbox may have its own),
  -- filter mode, and no new privileges
  let mine := filters (← IO.FS.readFile "/proc/self/status")
  let child ← IO.Process.spawn { cmd := fib.toString, args := #["40"], stdout := .null, stderr := .null }
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
  expect a seen s!"fib 40: no added seccomp filter seen in /proc (this process has {mine})"
  expectEq a code 0 "fib 40: exit"
  out := out.push s!"confinement: one seccomp filter more than the suite's ({mine.getD 0}), filter mode, \
    NoNewPrivs, while running"
  -- the system calls, under strace
  if let some st := o.strace then
    let calls := ["execve", "prctl", "seccomp", "write", "exit"]
    expect a ((← straced st work fib ["20"]) == calls) "fib 20: its system calls under strace"
    expect a ((← straced st work fib ["x"]) == calls) "fib x: its system calls under strace"
    expect a ((← straced st work gcd []) == calls) "gcd: its system calls under strace"
    out := out.push s!"system calls under strace: {", ".intercalate calls}, on success and on two failures"
  -- ixcc compile --exe, in-process
  let fx := "fixtures/ixon-v4/bench-k1"
  let cliExe := work / "cli_fib"
  let code ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--exe", cliExe.toString, "--stack", "65536", "--region", "4096"]
  expectEq a code 0 "ixcc compile --exe"
  runChecked a "ixcc compile --exe" cliExe ["10"] 0 "55\n" ""
  let rcExe := work / "cli_fib_rc"
  let code ← IxCC.Cli.main ["compile", s!"{fx}/fib.ixe", "--equations", s!"{fx}/fib.equations.json",
    "--rc", "on", "--exe", rcExe.toString]
  expectEq a code 0 "ixcc compile --rc on --exe"
  runChecked a "ixcc compile --rc on --exe" rcExe ["10"] 0 "55\n" ""
  out := out.push "ixcc compile --exe: fib, immortal and plain RC, runs"
  return out

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--run" :: rest => do return { (← parseOptions rest) with run := true }
  | "--strace" :: s :: rest => do return { (← parseOptions rest) with strace := some s }
  | arg :: _ => throw s!"unknown argument {arg}"

/-- Usage: `tests-exe [--run [--strace PATH]]`. -/
def main (args : List String) : IO UInt32 := do
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-exe: {e}"; return 2
  let a ← IO.mkRef 0
  try
    IO.println "tests-exe"
    let part (name : String) (body : IO (Array String)) : IO Unit := do
      let before ← a.get
      let (lines, ms) ← timed body
      IO.println s!"  {name}: {(← a.get) - before} assertions, {ms} ms"
      for l in lines do IO.println s!"    {l}"
    part "layout" (do layoutPart a; pure #[])
    part "shell" (do shellPart a; pure #[])
    IO.FS.withTempDir fun work => do
      part "writer and check" (writerPart a work)
      if o.run then part "native" (nativePart a o work)
      else IO.println "  native: skipped (no --run)"
    IO.println s!"tests-exe: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-exe: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Exe.Suite
