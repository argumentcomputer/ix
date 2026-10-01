import CompilatrixTests.Recheck.Artifact
import CompilatrixTests.Recheck.Kernel
import CompilatrixTests.Recheck.Audit
import CompilatrixTests.Lir.Gen
import Compilatrix.Lir.SplitEdges

/-! The `tests-recheck` suite (M1.K1): the recheck path in kernel-evaluable
style. Building the suite evaluates, in the kernel
(`CompilatrixTests.Recheck.Kernel`), `Recheck.runTyped` on the fib, tak and
gcd artifacts and the whole `Recheck.run` on fib. Running it checks that
every committed artifact (`CompilatrixTests/Recheck/Artifacts/*.lean`)
equals a fresh ingress, `produce` and native run, so the kernel's claims
are about the live compiler, and that the recheck path's statistics-free
selection (`Select.select`) selects what `Select.run` selects on generated
Lir (`--generated N` for a longer campaign; 1,000 by default). -/

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

/-- The recheck path's selection (`Select.select`, statistics off) selects
what `Select.run` selects, or declines alike, on generated Lir programs. -/
def selection (a : Assert) (count : Nat) : IO (Array String) := do
  let mut selected := 0
  let mut declined := 0
  for seed in [0:count] do
    let (raw, _) := CompilatrixTests.Lir.Gen.program {} (UInt64.ofNat seed)
    let p := raw.splitCriticalEdges
    match Compilatrix.Xv.Select.run p, Compilatrix.Xv.Select.select p with
    | .ok (q, _), .ok q' =>
      expect a (q == q') s!"seed {seed}: Select.select differs from Select.run"
      selected := selected + 1
    | .error e, .error e' =>
      expect a (e.form == e'.form && e.reason == e'.reason && e.fn == e'.fn && e.block == e'.block &&
        e.stmt == e'.stmt) s!"seed {seed}: the declines differ"
      declined := declined + 1
    | _, _ => expect a false s!"seed {seed}: one selection declines, the other does not"
  return #[s!"{count} generated programs: {selected} selected alike, {declined} declined alike"]

def main (args : List String) : IO UInt32 := do
  let count := match args with
    | ["--generated", n] => n.toNat!
    | _ => 1000
  let a ← IO.mkRef 0
  try
    IO.println "tests-recheck"
    part a "recheck artifacts equal a fresh ingress, produce and run" (artifacts a)
    part a "Select.select against Select.run on generated Lir" (selection a count)
    IO.println s!"tests-recheck: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-recheck: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Recheck.Run
