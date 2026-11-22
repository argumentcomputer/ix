import IxCC.Tools.Check

/-! External ELF and native execution checks shared by the repository gates.
These checks intentionally do not import the compiler, encoder, or ELF writer. -/

namespace IxCC.Tools.X86Check

open System Check

def inspectElf (readelf : String) (path : FilePath) (exportName : String := "ixcc_main") : IO String := do
  let elf ← run readelf #["-W", "-h", "-S", "-s", "-r", "-n", path.toString]
  requireAll elf [
    "Class:                             ELF64",
    "Data:                              2's complement, little endian",
    "Type:                              REL (Relocatable file)",
    "Machine:                           Advanced Micro Devices X86-64",
    ".text", ".note.ixcc", ".note.GNU-stack", exportName,
    "IXCC", "0x43495801"
  ] s!"{path}: readelf"
  return elf

/-- Keep decoded instruction rows, excluding filenames, symbol headings and
relocation annotations. Random temporary paths can contain register names. -/
def instructionText (dump : String) : String :=
  String.intercalate "\n" ((dump.splitOn "\n").filter fun line =>
    let parts := words line
    let first := parts.headD ""
    let address := (first.dropEnd 1).toString
    first.endsWith ":" && !address.isEmpty && isHex address.length address &&
      isHex 2 (parts.drop 1 |>.headD ""))

def disassemble (objdump : String) (path : FilePath) (exportName : String := "ixcc_main") : IO String := do
  let result := (← run objdump #["-dr", "-M", "intel", path.toString]).toLower
  requireAll result ["file format elf64-x86-64", s!"<{exportName}>:"] s!"{path}: objdump"
  let instructions := instructionText result
  need (!instructions.contains "(bad)") s!"{path}: decoder emitted (bad)\n{instructions}"
  requireAll instructions ["ret"] s!"{path}: objdump"
  return result

def provenance (root : String) : IO ByteArray := do
  return "ixcc/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root ++ " 01 00 00 00 01 00 00 00")))

def linkAndRun (cc readelf : String) (harness object executable : FilePath)
    (expected : Nat) : IO Unit := do
  let _ ← run cc #[
    "-std=c11", "-Wall", "-Wextra", "-Werror", "-Wl,--fatal-warnings", "-no-pie",
    s!"-DEXPECTED_RESULT={expected}ULL", harness.toString, object.toString,
    "-o", executable.toString]
  let _ ← run executable.toString
  let headers ← run readelf #["-W", "-l", executable.toString]
  let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
  need (stacks.length == 1 && !stacks.any (·.contains "RWE"))
    s!"{executable}: expected one non-executable GNU_STACK\n{headers}"

def nativeArgs (args : List (String × String)) : IO (Option (String × FilePath)) := do
  match optional args "--cc", optional args "--harness" with
  | none, none => return none
  | some cc, some harness => return some (cc, harness)
  | _, _ => throw (IO.userError "--cc and --harness must be supplied together")

end IxCC.Tools.X86Check
