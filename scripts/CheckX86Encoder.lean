import Compilatrix.Tools.Check

/-! Independently decode the byte-exact encoder goldens (`X86/EncodeExamples`)
with GNU objdump. The byte strings are frozen here, not produced by compiler
code. -/

open Compilatrix.Tools.Check

private def forms := "48 b8 2a 00 00 00 00 00 00 00 40 b6 07 4d 89 d1 " ++
  "47 0f b6 4c ec 10 0f b7 43 04 44 8b 04 25 00 01 00 00 4c 89 65 f8 4e 8d 54 8b 20 " ++
  "48 81 c0 02 00 00 00 40 80 ee 01 45 31 d1 01 c8 4d 0f af ca 41 54 41 5c 55 " ++
  "48 81 ec 10 00 00 00 48 81 f8 2a 00 00 00 45 39 d1"

/-- Displacement and REX edges: no displacement, the RBP/R13 disp8-zero hole,
the RSP/R12 SIB hole, disp32, and a byte register that needs a bare REX. -/
private def addressing := "48 89 03 49 89 45 00 48 89 04 24 49 89 84 24 80 00 00 00 " ++
  "4c 89 a5 00 00 fc ff 40 88 e0"

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
    "movzx  r9d,byte ptr [r12+r13*8+0x10]", "movzx  eax,word ptr [rbx+0x4]",
    "mov    r8d,dword ptr ds:0x100", "mov    qword ptr [rbp-0x8],r12",
    "lea    r10,[rbx+r9*4+0x20]", "add    rax,0x2", "sub    sil,0x1", "xor    r9d,r10d",
    "add    eax,ecx", "imul   r9,r10", "push   r12", "pop    r12", "push   rbp",
    "sub    rsp,0x10", "cmp    rax,0x2a", "cmp    r9d,r10d"
  ] "instruction forms"
  decode objdump addressing [
    "mov    qword ptr [rbx],rax", "mov    qword ptr [r13+0x0],rax", "mov    qword ptr [rsp],rax",
    "mov    qword ptr [r12+0x80],rax", "mov    qword ptr [rbp-0x40000],r12", "mov    al,spl"
  ] "addressing and REX forms"
  decode objdump arithmetic ["je     0x23", "jmp    0x24", "movabs rax,0x0", "ret"]
    "arithmetic branch program"
  decode objdump callProgram [
    "push   rbp", "call   0xf", "pop    rbp", "add    rax,0x2", "movabs rax,0x28", "ret"
  ] "direct call program"
  IO.println "x86 encoder decoder check ok: 19 forms, 6 addressing/REX forms, branch layout, direct call"
