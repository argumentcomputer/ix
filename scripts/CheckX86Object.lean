import Compilatrix.Tools.X86Check

/-! Inspect and natively run independently generated ELF files. All byte and
address expectations are frozen here rather than obtained from compiler code. -/

open System Compilatrix.Tools.Check Compilatrix.Tools.X86Check

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
  { name := "unwind", kind := "unwind", expected := 1 }
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
        "r_x86_64_pc32\tcompilatrix_rt_allocate-0x4", "pop    rbp"]
    | "unwind" => pure [
        "push   r15", "lea    r15,[rdi+0x40]", "mov    qword ptr [r15-0x40],rsp", "lea    r11,[rsp-0x40]",
        "cmp    r11,qword ptr [r15-0x38]", "jb", "mov    rsp,qword ptr [r15-0x40]", "xor    edx,edx", "pop    rbx"]
    | _ => throw (IO.userError "unknown fixture kind")
  requireAll disassembly expected s!"{fixture.name}: disassembly"
  if fixture.kind == "runtime" then
    requireAll elf ["R_X86_64_PC32", "compilatrix_rt_allocate - 4"] "runtime relocation"
  else
    need (elf.contains "There are no relocations in this file.")
      s!"unexpected relocation for {fixture.name}\n{elf}"

def main (args : List String) : IO UInt32 := cli "x86 ELF object check failed" do
  let args ← checked (parseArgs ["--fixture", "--readelf", "--objdump", "--cc", "--harness"] args)
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
        let harness := if fixture.kind == "unwind" then (harness.parent.getD ".") / "unwind_harness.c" else harness
        linkAndRun cc readelf harness path (directory / s!"{fixture.name}-native") localValue
  let suffix := if native.isSome then ", native link/run result match" else ""
  IO.println s!"x86 ELF object check ok: {fixtures.length} deterministic objects, provenance goldens, local semantics, readelf, objdump{suffix}"
