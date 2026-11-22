import IxCC.Exe

/-! Running standalone executables in tests: write one, run it on arguments,
and read its exit status, standard output and standard error. -/

namespace IxCCTests.Exe

open System

/-- Write an executable file. -/
def writeExe (path : FilePath) (bytes : ByteArray) : IO Unit := do
  IO.FS.writeBinFile path bytes
  IO.setAccessRights path { user := { read := true, write := true, execution := true } }

/-- One run of an executable. -/
structure Run where
  code : UInt32
  stdout : String
  stderr : String
  deriving Inhabited

def run (exe : FilePath) (args : List String) : IO Run := do
  let out ← IO.Process.output { cmd := exe.toString, args := args.toArray }
  pure { code := out.exitCode, stdout := out.stdout, stderr := out.stderr }

/-- The outcome in the corpus suite's words: `ok`, a driver status (`status
s` for exit `64 + s`, `s` from 1 to 4), or the exit code. -/
def Run.outcome (r : Run) : String :=
  if r.code == 0 then "ok"
  else if 65 ≤ r.code && r.code ≤ 68 then s!"status {r.code - 64}"
  else s!"exit {r.code}"

/-- The observation: standard output without its final newline (`-` when
there is none). -/
def Run.obs (r : Run) : String :=
  if r.code == 0 && r.stdout.endsWith "\n" then (r.stdout.dropEnd 1).toString else "-"

/-- Build a root's executable with `layout` and write it to `path`. -/
def build (path : FilePath) (a : IxCC.Recheck.Artifact) (layout : IxCC.X86.Exe.Layout) :
    IO (Except IxCC.Recheck.Err Unit) := do
  match IxCC.Exe.build a layout with
  | .error e => pure (.error e)
  | .ok ⟨_, c⟩ => writeExe path c.bytes; pure (.ok ())

end IxCCTests.Exe
