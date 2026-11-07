import IxCCTests.Backend.Support

/-!
# Native execution of backend objects

An object is linked with the C runtime driver (`fixtures/x86/backend_driver.c`,
untrusted test code, pinned in the trust ledger) into an executable named
after the case; the driver reads one input per line (`budget a1 … an`, or
`seed S` to fill a fixed region with the Lean test region's pattern) and
prints `status value ok` per input, `ok` meaning the callee-saved
registers and `rsp` came back unchanged.
-/

namespace IxCCTests.Backend.Native

open System

structure Tools where
  cc : String := "cc"
  driver : FilePath := "fixtures/x86/backend_driver.c"
  work : FilePath

/-- Link `object` with the driver; `fixed` maps the region at the Lean
region's address. -/
def link (t : Tools) (name : String) (object : ByteArray) (entry : String) (fixed : Bool := false) :
    IO FilePath := do
  let obj := t.work / s!"{name}.o"
  IO.FS.writeBinFile obj object
  let exe := t.work / name
  let out ← IO.Process.output {
    cmd := t.cc
    args := #["-std=c11", "-O1", "-Wall", "-Wextra", "-Werror", "-Wl,--fatal-warnings", "-no-pie",
      s!"-DENTRY={entry}"] ++ (if fixed then #["-DFIXED_REGION"] else #[]) ++
      #[t.driver.toString, obj.toString, "-o", exe.toString] }
  unless out.exitCode == 0 do throw (IO.userError s!"linking {name} failed:\n{out.stdout}{out.stderr}")
  pure exe

/-- One native result line. -/
structure Line where
  status : Word
  value : Word
  ok : Bool
  deriving BEq, Repr

def parseLine (line : String) : Option Line :=
  match (line.splitOn " ").filter (!·.isEmpty) with
  | [s, v, ok] => do pure ⟨UInt64.ofNat (← s.toNat?), UInt64.ofNat (← v.toNat?), ok == "1"⟩
  | _ => none

/-- Run an executable on input lines; one result per non-`seed` line. -/
def run (exe : FilePath) (lines : List String) : IO (List Line) := do
  let child ← IO.Process.spawn { cmd := exe.toString, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr (String.join (lines.map (· ++ "\n")))
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  unless code == 0 do throw (IO.userError s!"{exe} exited {code}\n{err}")
  let results := ((out.splitOn "\n").filter (!·.isEmpty)).map parseLine
  match results.mapM id with
  | some rs => pure rs
  | none => throw (IO.userError s!"{exe}: malformed output\n{out}")

end IxCCTests.Backend.Native
