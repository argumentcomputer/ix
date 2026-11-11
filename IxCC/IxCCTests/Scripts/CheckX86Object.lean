import IxCC.Tools.X86Check

/-! Inspect and natively run independently generated ELF files. All byte and
address expectations are frozen here rather than obtained from compiler code.
With `--ixcc`, objects the compiler writes in this run are also linked, never
run, by the system linker (`linkCompiled`). -/

open System IxCC.Tools.Check IxCC.Tools.X86Check

private structure Fixture where
  name : String
  kind : String
  expected : Nat
  ixonRoot : String := "-"
  ir1Root : String := String.join (List.replicate 32 "42")

private def fixtures : List Fixture := [
  { name := "arithmetic", kind := "arithmetic", expected := 42 },
  { name := "direct-call", kind := "direct-call", expected := 42 },
  { name := "runtime", kind := "runtime", expected := 0x2000 },
  { name := "unwind", kind := "unwind", expected := 1 },
  { name := "exports", kind := "exports", expected := 42 }
]

private def reportValue (text key : String) : IO String := do
  need (text.startsWith key) s!"expected {key} in fixture report: {text}"
  return (text.drop key.length).toString

private def generate (exe : String) (fixture : Fixture) (path : FilePath)
    : IO (ByteArray × Option Nat × Nat) := do
  let output ← run exe #[fixture.kind, path.toString]
  let fields := words output
  need (output == " ".intercalate fields || output == " ".intercalate fields ++ "\n")
    s!"malformed fixture report: {output}"
  let [kind, source, localValue, size, ixon, ir1] := fields
    | throw (IO.userError s!"fixture did not report success: {output}")
  need (kind == s!"fixture={fixture.kind}") s!"wrong fixture report: {output}"
  let source ← reportValue source "source="
  let source ← if source == "-" then pure none
    else some <$> present source.toNat? "invalid source observation"
  let localValue ← present (← reportValue localValue "local=").toNat? "invalid local observation"
  let size ← present (← reportValue size "bytes=").toNat? "invalid byte count"
  need (ixon == s!"ixon={fixture.ixonRoot}" && ir1 == s!"ir1={fixture.ir1Root}")
    s!"address golden drifted for {fixture.name}\n{output}"
  let payload ← IO.FS.readBinFile path
  need (payload.size == size) s!"wrong reported byte size for {fixture.name}"
  need (payload.extract 0 7 == (← checked (unhex "7f 45 4c 46 02 01 01")))
    s!"invalid ELF64 prefix for {fixture.name}"
  need (containsBytes payload (← provenance fixture.ir1Root))
    s!"missing exact provenance bytes for {fixture.name}"
  return (payload, source, localValue)

private def inspect (readelf objdump : String) (fixture : Fixture) (path : FilePath) : IO Unit := do
  let elf ← inspectElf readelf path
  let disassembly ← disassemble objdump path
  let expected ← match fixture.kind with
    | "arithmetic" => pure ["mov    eax,0x28", "add    rax,0x2", "cmp    rax,0x2a", "je     18", "jmp    19"]
    | "direct-call" => pure ["push   rbp", "call   c", "pop    rbp", "add    rax,0x2", "mov    eax,0x28"]
    | "runtime" => pure [
        "push   rbp", "mov    edi,0x10", "mov    esi,0x8",
        "r_x86_64_pc32\tixcc_rt_allocate-0x4", "pop    rbp"]
    | "unwind" => pure [
        "push   r15", "lea    r15,[rdi+0x40]", "mov    qword ptr [r15-0x40],rsp", "lea    r11,[rsp-0x40]",
        "cmp    r11,qword ptr [r15-0x38]", "jb", "mov    rsp,qword ptr [r15-0x40]", "xor    edx,edx", "pop    rbx"]
    | "exports" => pure ["push   rbp", "call   c <ixcc_forty>", "pop    rbp", "add    rax,0x2",
        "<ixcc_forty>:", "mov    eax,0x28"]
    | _ => throw (IO.userError "unknown fixture kind")
  requireAll disassembly expected s!"{fixture.name}: disassembly"
  if fixture.kind == "exports" then
    -- Both symbols are global functions defined in .text (section 1), the
    -- further export at the callee's offset.
    let defined := ((elf.splitOn "\n").map words).filterMap fun
      | [_, value, _, "FUNC", "GLOBAL", "DEFAULT", "1", name] => some (name, value)
      | _ => none
    need (defined == [("ixcc_main", "0000000000000000"), ("ixcc_forty", "000000000000000c")])
      s!"exports: expected two defined global function symbols\n{elf}"
  if fixture.kind == "runtime" then
    requireAll elf ["R_X86_64_PC32", "ixcc_rt_allocate - 4"] "runtime relocation"
  else
    need (elf.contains "There are no relocations in this file.")
      s!"unexpected relocation for {fixture.name}\n{elf}"

/-! ## Objects the compiler writes, accepted by the system linker

`ixcc compile` writes relocatable objects, and the native gates run them as
executables IxCC writes itself, with no linker. So the system linker meets the
compiler's own output here: each object of a representative set is compiled
in this run by the `ixcc` binary and linked by the system linker into a static
executable with no C library or start files, entered at `cx_init`, which is
never run. The linker must accept it, with every global function of the
object required to be defined (`--require-defined`), and `readelf` must find
each of them in the linked file at the linked text's address plus its offset in
the object, and one non-executable `GNU_STACK`. -/

private structure Compiled where
  name : String
  args : List String
  /-- Exports the object must have, beside whatever else it defines. -/
  exports : List String

private def benchK1 (name : String) : Compiled :=
  { name, args := [s!"fixtures/ixon-v4/bench-k1/{name}.ixe", "--equations",
      s!"fixtures/ixon-v4/bench-k1/{name}.equations.json"], exports := ["cx_init", "cx_entry"] }

/-- The five K1 programs as compiled one by one, `k1.ixe`'s five roots in one
object, and the real-source RC fixture on the plain-RC route (with
`cx_drop`). -/
private def compiledSet : List Compiled :=
  ["fib", "sum-loop", "ackermann", "tak", "gcd"].map benchK1 ++
  [{ name := "k1", args := ["fixtures/ixon-v4/k1/k1.ixe", "--equations", "fixtures/ixon-v4/k1/equations.json",
        "--root", "K1.fib", "--root", "K1.sumLoop", "--root", "K1.ack", "--root", "K1.tak", "--root", "K1.gcd"],
      exports := ["cx_init", "cx_K1_fib", "cx_K1_sumLoop", "cx_K1_ack", "cx_K1_tak", "cx_K1_gcd"] },
   { name := "rc-real-source", args := ["fixtures/rc/real-source/anonymous.ixe", "--equations",
        "fixtures/rc/real-source/consumer.equations.json", "--rc", "on"],
      exports := ["cx_init", "cx_drop"] }]

private def hexValue (text : String) : Option Nat :=
  text.foldl (fun acc c => do pure (16 * (← acc) + (← hexDigit c))) (some 0)

/-- `readelf -W -s`: the global function symbols, as name and value. -/
private def globalFunctions (readelf : String) (path : FilePath) : IO (List (String × Nat)) := do
  let out ← run readelf #["-W", "-s", path.toString]
  ((out.splitOn "\n").map words).filterMapM fun
    | [_, value, _, "FUNC", "GLOBAL", _, _, name] => do
      return some (name, ← present (hexValue value) s!"{path}: symbol value {value}")
    | _ => pure none

/-- `readelf -W -S`: the address of the section `.text`. -/
private def textAddress (readelf : String) (path : FilePath) : IO Nat := do
  let out ← run readelf #["-W", "-S", path.toString]
  for line in out.splitOn "\n" do
    match (words line).dropWhile (· != ".text") with
    | ".text" :: _ :: address :: _ =>
      return ← present (hexValue address) s!"{path}: .text address {address}"
    | _ => pure ()
  throw (IO.userError s!"{path}: no .text section\n{out}")

private def linkCompiled (cc readelf ixcc : String) (directory : FilePath) : IO String := do
  let start ← IO.monoMsNow
  let mut exports := 0
  for c in compiledSet do
    let object := directory / s!"compiled-{c.name}.o"
    let executable := directory / s!"compiled-{c.name}"
    let _ ← run ixcc (#["compile"] ++ c.args.toArray ++ #["--no-typecheck", "-o", object.toString])
    let symbols ← globalFunctions readelf object
    for e in c.exports do
      need (symbols.any (·.1 == e)) s!"{c.name}: the object does not define {e}\n{symbols}"
    let _ ← run cc (#["-nostdlib", "-static", "-no-pie", "-Wl,--fatal-warnings", "-Wl,-e,cx_init"] ++
      (symbols.map fun (name, _) => s!"-Wl,--require-defined={name}").toArray ++
      #[object.toString, "-o", executable.toString])
    let header ← run readelf #["-W", "-h", executable.toString]
    requireAll header ["Type:                              EXEC (Executable file)"] s!"{executable}: readelf -h"
    let text ← textAddress readelf executable
    let linked ← globalFunctions readelf executable
    for (name, offset) in symbols do
      need (linked.contains (name, text + offset))
        s!"{c.name}: {name} is not at the linked text plus its object offset {offset}\n{linked}"
    let segments ← run readelf #["-W", "-l", executable.toString]
    let stacks := (segments.splitOn "\n").filter (·.contains "GNU_STACK")
    need (stacks.length == 1 && !stacks.any (·.contains "RWE"))
      s!"{executable}: expected one non-executable GNU_STACK\n{segments}"
    exports := exports + symbols.length
  return s!"{compiledSet.length} objects ixcc compiled in this run linked by the system linker \
    ({exports} exports, each where the object puts it; {(← IO.monoMsNow) - start} ms)"

def main (args : List String) : IO UInt32 := cli "x86 ELF object check failed" do
  let args ← checked (parseArgs ["--fixture", "--readelf", "--objdump", "--cc", "--harness", "--ixcc"] args)
  let some exe := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun directory => do
    for fixture in fixtures do
      let path := directory / s!"{fixture.name}.o"
      let (payload, source, localValue) ← generate exe fixture path
      let (duplicate, duplicateSource, duplicateValue) ←
        generate exe fixture (directory / s!"{fixture.name}-duplicate.o")
      need (payload == duplicate) s!"nondeterministic object for {fixture.name}"
      need (source == duplicateSource && localValue == duplicateValue && localValue == fixture.expected)
        s!"fixture observation drifted for {fixture.name}"
      need (source == none) s!"unexpected source observation for {fixture.name}"
      inspect readelf objdump fixture path
      if let some (cc, harness) := native then
        -- The failure exit runs under a harness that checks sentinels in the
        -- callee-saved registers, rax:rdx, rsp and a second call on the region.
        -- The exports fixture's harness calls both exported symbols by name.
        let harness := if fixture.kind == "unwind" then (harness.parent.getD ".") / "unwind_harness.c"
          else if fixture.kind == "exports" then (harness.parent.getD ".") / "exports_harness.c" else harness
        linkAndRun cc readelf harness path (directory / s!"{fixture.name}-native") localValue
    let suffix := if native.isSome then ", native link/run result match" else ""
    IO.println s!"x86 ELF object check ok: {fixtures.length} deterministic objects, provenance goldens, local semantics, readelf, objdump{suffix}"
    match native, optional args "--ixcc" with
    | some (cc, _), some ixcc => IO.println s!"x86 ELF object check ok: {← linkCompiled cc readelf ixcc directory}"
    | none, some _ => throw (IO.userError "--ixcc needs --cc")
    | _, none => pure ()
