import Ix.Compiler.Tools.X86Check

/-! Inspect and natively run independently generated ELF files. All byte and
address expectations are frozen here rather than obtained from compiler code. -/

open System Ix.Compiler.Tools.Check Ix.Compiler.Tools.X86Check

private structure Fixture where
  name : String
  kind : String
  expected : Nat
  ixonRoot : String := "-"
  ir1Root : String := String.join (List.replicate 32 "42")

private def fixtures : List Fixture := [
  ⟨"arithmetic", "arithmetic", 42, "-", String.join (List.replicate 32 "42")⟩,
  { name := "direct-call", kind := "direct-call", expected := 42 },
  { name := "runtime", kind := "runtime", expected := 0x2000 },
  { name := "selected-scalar", kind := "selected-scalar", expected := 42 },
  { name := "validated-zero", kind := "validated-scalar", expected := 0
    ixonRoot := "11f9a7889be4f23e910d35b8501542c842e16ef4b4c013525b617b2a9c4f8829"
    ir1Root := "a6fd56bbb40c863cd3767059ea82f62fa649e4c906d56fc1d7aec40017c86936" },
  { name := "validated-42", kind := "validated-scalar", expected := 42
    ixonRoot := "2e926c5f48aec39e7f8dccde8e2289a8a97821714339767dc7c789fbb4479874"
    ir1Root := "1898b54e998f21f0f2615354eda8014fb47188a00d9511e6e4ca8f11ac5e20d8" },
  { name := "validated-max", kind := "validated-scalar", expected := 18446744073709551615
    ixonRoot := "b1657e7f011436f0ed6d2c8eafa4269a8996742f3baaf6845199a00891336781"
    ir1Root := "03cec8b3b1f9fa35a552a76dc26f74499cd62be1e7d3e81bb3c7e2f337e8611f" }
]

private def reportValue (text key : String) : IO String := do
  need (text.startsWith key) s!"expected {key} in fixture report: {text}"
  return (text.drop key.length).toString

private def generate (exe : String) (fixture : Fixture) (path : FilePath)
    : IO (ByteArray × Option Nat × Nat) := do
  let extra := if fixture.kind == "validated-scalar" then #[toString fixture.expected] else #[]
  let output ← run exe (#[fixture.kind, path.toString] ++ extra)
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
    | "arithmetic" => pure ["movabs rax,0x28", "add    rax,0x2", "je     23", "jmp    24"]
    | "direct-call" => pure ["push   rbp", "call   f", "pop    rbp", "add    rax,0x2", "movabs rax,0x28"]
    | "runtime" => pure [
        "push   rbp", "movabs rdi,0x10", "movabs rsi,0x8",
        "r_x86_64_pc32\tcompilatrix_rt_allocate-0x4", "pop    rbp"]
    | "selected-scalar" | "validated-scalar" => pure [s!"movabs rax,0x{hexNat fixture.expected}"]
    | _ => throw (IO.userError "unknown fixture kind")
  requireAll disassembly expected s!"{fixture.name}: disassembly"
  if fixture.kind == "runtime" then
    requireAll elf ["R_X86_64_PC32", "compilatrix_rt_allocate - 4"] "runtime relocation"
  else
    need (elf.contains "There are no relocations in this file.")
      s!"unexpected relocation for {fixture.name}\n{elf}"

private def rejectOverflow (exe : String) (directory : FilePath) : IO Unit := do
  let path := directory / "overflow.o"
  let result ← IO.Process.output
    { cmd := exe, args := #["validated-scalar", path.toString, "18446744073709551616"] }
  need (result.exitCode == 2 && result.stderr.contains "unsupportedScalarShape" &&
    !(← path.pathExists)) s!"overflow was not rejected before writing an object\n{result.stdout}{result.stderr}"

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
      let expectedSource := if fixture.kind == "selected-scalar" || fixture.kind == "validated-scalar"
        then some localValue else none
      need (source == expectedSource) s!"source/target observation disagrees for {fixture.name}"
      inspect readelf objdump fixture path
      if let some (cc, harness) := native then
        linkAndRun cc readelf harness path (directory / s!"{fixture.name}-native") localValue
    rejectOverflow exe directory
  let suffix := if native.isSome then ", native link/run result match" else ""
  IO.println s!"x86 ELF object check ok: {fixtures.length} deterministic objects, validated Ixon/IR/target agreement, real provenance goldens, overflow rejection, local semantics, readelf, objdump{suffix}"
