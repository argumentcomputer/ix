import Ix.Compiler.Tools.Check

/-! Independently decode the byte-exact E0 Lean goldens with GNU objdump. -/

open Ix.Compiler.Tools.Check

private def forms := "48 b8 2a 00 00 00 00 00 00 00 40 b6 07 4d 89 d1 " ++
  "4f 0f b6 8c ec 10 00 00 00 4c 89 a5 f8 ff ff ff 4e 8d 94 8b 20 00 00 00 " ++
  "48 81 c0 02 00 00 00 45 31 d1 4d 0f af ca 41 54 41 5c " ++
  "48 81 ec 10 00 00 00 48 81 f8 2a 00 00 00"

private def arithmetic := "48 b8 28 00 00 00 00 00 00 00 48 81 c0 02 00 00 00 " ++
  "48 81 f8 2a 00 00 00 0f 84 05 00 00 00 e9 01 00 00 00 c3 " ++
  "48 b8 00 00 00 00 00 00 00 00 c3"

private def callProgram := "55 e8 09 00 00 00 5d 48 81 c0 02 00 00 00 c3 " ++
  "48 b8 28 00 00 00 00 00 00 00 c3"

private def decode (objdump : String) (payload : String) (expected : List String)
    (label : String) : IO Unit := IO.FS.withTempDir fun directory => do
  let path := directory / "fixture.bin"
  IO.FS.writeBinFile path (← checked (unhex payload))
  let output := (← run objdump
    #["-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel", path.toString]).toLower
  requireAll output expected label
  need (!output.contains "(bad)") s!"{label}: decoder emitted (bad)\n{output}"

def main (args : List String) : IO UInt32 := cli "x86 encoder decoder check failed" do
  let args ← checked (parseArgs ["--objdump"] args)
  let objdump := option args "--objdump" "objdump"
  decode objdump forms [
    "movabs rax,0x2a", "mov    sil,0x7", "mov    r9,r10",
    "movzx  r9,byte ptr [r12+r13*8+0x10]", "mov    qword ptr [rbp-0x8],r12",
    "lea    r10,[rbx+r9*4+0x20]", "add    rax,0x2", "xor    r9d,r10d",
    "imul   r9,r10", "push   r12", "pop    r12", "sub    rsp,0x10", "cmp    rax,0x2a"
  ] "instruction forms"
  decode objdump arithmetic ["je     0x23", "jmp    0x24", "movabs rax,0x0", "ret"]
    "arithmetic branch program"
  decode objdump callProgram [
    "push   rbp", "call   0xf", "pop    rbp", "add    rax,0x2", "movabs rax,0x28", "ret"
  ] "direct call program"
  IO.println "x86 encoder decoder check ok: 13 forms, branch layout, direct call"
