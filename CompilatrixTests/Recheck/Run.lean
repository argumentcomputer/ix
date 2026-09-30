import CompilatrixTests.Recheck.Artifact
import CompilatrixTests.Recheck.Kernel

/-! The `tests-recheck` suite (M1.K1): the recheck path in kernel-evaluable
style. Building the suite evaluates `Recheck.runTyped` on the fib, tak and
gcd artifacts in the kernel (`CompilatrixTests.Recheck.Kernel`); running it
checks that every committed artifact
(`CompilatrixTests/Recheck/Artifacts/*.lean`) equals a fresh ingress,
`produce` and native run, so the kernel's claims are about the live
compiler. -/

namespace CompilatrixTests.Recheck.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

/-- Every committed artifact equals the printer's output on a fresh run. -/
def artifacts (a : Assert) : IO (Array String) := do
  let mut lines := #[]
  for (name, modName) in Artifact.artifacts do
    let x ← Artifact.load name modName
    let (text, stats) := Artifact.render x
    let file := Artifact.path modName
    let old ← IO.FS.readFile file
    expect a (old == text) s!"{file} is stale (run lake exe gen-recheck-artifacts)"
    lines := lines.push stats
  return lines

def main (_args : List String) : IO UInt32 := do
  let a ← IO.mkRef 0
  try
    IO.println "tests-recheck"
    part a "recheck artifacts equal a fresh ingress, produce and run" (artifacts a)
    IO.println s!"tests-recheck: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-recheck: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Recheck.Run
