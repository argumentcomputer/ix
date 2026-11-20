/-!
# The project's location

Files the executables read and write by default (the Truth Mines store, `ix/ixw`, the package of
the full run) are named relative to the root of this project's checkout, `projectDir`:

1. `IXAI_PROJECT`, when it is set and not empty;
2. otherwise the checkout whose `.lake/build/bin` holds the running executable, which is where
   `lake build` puts `ixai` and `ixai-verify`;
3. otherwise the working directory.

It is computed once, when the program starts.
-/

namespace IxAI

/-- The checkout an executable at `exe` was built in: `P` for `P/.lake/build/bin/NAME`. -/
def checkoutOf? (exe : System.FilePath) : Option System.FilePath := do
  let bin ← exe.parent
  let build ← bin.parent
  let lake ← build.parent
  guard (bin.fileName == some "bin" && build.fileName == some "build" && lake.fileName == some ".lake")
  lake.parent

def locateProject : IO System.FilePath := do
  if let some p := (← IO.getEnv "IXAI_PROJECT") then
    unless p.isEmpty do return p
  let exe? ← try pure (some (← IO.FS.realPath (← IO.appPath))) catch _ => pure none
  match exe?.bind checkoutOf? with
  | some p => return p
  | none => IO.currentDir

initialize projectDir : System.FilePath ← locateProject

end IxAI
