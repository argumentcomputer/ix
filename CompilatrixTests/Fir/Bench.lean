import CompilatrixTests.Fir.Support
import CompilatrixTests.Fir.Differential
import CompilatrixTests.Src.Bench

/-! The bench-k1 entries at their test sizes (`benchmarks/fixtures/
manifest.json`) through Fir, Own and Cfg, against `expected.txt`, with the
sizes of each entry's program at every level. Cfg is small-step, so it runs
`sum-loop` 10⁶ in process; Fir and Own are big-step evaluators whose depth
follows the loop, so `sum-loop` runs there in a child process with a larger
Lean stack (`--entry NAME LEVEL`). K1 allocates nothing (02 §13.4): the final
Own and Cfg heaps are empty. -/

namespace CompilatrixTests.Fir.Bench

open Compilatrix CompilatrixTests.Src CompilatrixTests.Lam CompilatrixTests.Anf

/-- An entry's program at every level, and its root. -/
def entryLevels (name : String) : IO (Levels × Nat) := do
  let e ← eraseLoaded (← loadBench name)
  let A ← Differential.finalAnf e.lam
  let L ← IO.ofExcept (lower A)
  let some root := A.roots.head? | throw (IO.userError s!"{name}: no root")
  return (L, root)

def natResult (label : String) : Option Sem.Obs → IO Nat
  | some (.nat n) => pure n
  | o => throw (IO.userError s!"{label}: result {repr o}")

/-- Run one entry at its test size at one level (`fir`, `own`, `cfg`). -/
def runEntry (name level : String) : IO Nat := do
  let (L, root) ← entryLevels name
  let (args, _) ← CompilatrixTests.Src.Bench.testCase name
  let k := 1 <<< 40
  match level with
  | "fir" =>
    match ← runFir L.fir k root args with
    | .ok v => natResult name (Compilatrix.Fir.readback v)
    | r => throw (IO.userError s!"{name} fir: {firOutcome r}")
  | "own" =>
    match ← runOwn .immortal L.own k root args with
    | .ok (v, H) =>
      unless H.cells.size == 0 do throw (IO.userError s!"{name} own: {H.cells.size} cells allocated")
      natResult name (H.readback v)
    | r => throw (IO.userError s!"{name} own: {ownOutcome r}")
  | _ =>
    match ← runCfg .immortal L.cfg k root args with
    | .ok (v, H) =>
      unless H.cells.size == 0 do throw (IO.userError s!"{name} cfg: {H.cells.size} cells allocated")
      natResult name (H.readback v)
    | r => throw (IO.userError s!"{name} cfg: {ownOutcome r}")

def entries (a : Assert) (self : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let (L, _) ← entryLevels name
    checkLevels a L s!"{name} entry"
    let (args, expected) ← CompilatrixTests.Src.Bench.testCase name
    let mut line := s!"{name} {args} = {expected}:"
    for level in ["cfg", "own", "fir"] do
      let (got, ms) ← timed do
        if name == "sum-loop" && level != "cfg" then
          let env := #[("LEAN_STACK_SIZE_KB", some (toString CompilatrixTests.Src.Bench.deepStackKb))]
          let o ← IO.Process.output { cmd := self.toString, args := #["--entry", name, level], env }
          unless o.exitCode == 0 do
            throw (IO.userError s!"{name} {level} child exited {o.exitCode}: {o.stderr}")
          pure o.stdout.trimAscii.toString.toNat!
        else runEntry name level
      expectEq a got expected s!"{name} {args} at {level}"
      line := line ++ s!" {level} {ms} ms"
    out := out.push line
    out := out.push s!"  {sizes L}"
  return out

end CompilatrixTests.Fir.Bench
