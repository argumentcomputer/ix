import CompilatrixTests.Anf.Differential
import Compilatrix.Anf.Shrink
import Compilatrix.Anf.Inline

/-! The `tests-anf` suite (design note 02 §6–8, §13). -/

namespace CompilatrixTests.Anf.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO Unit) : IO Unit := do
  let before ← a.get
  let ((), ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  (← IO.getStdout).flush

def stages : Differential.Stages := fun L => do
  let p1 ← Compilatrix.Anf.convert L
  let (_, p2, _) ← Compilatrix.Anf.Shrink.produce {} p1
  let mut out := [("P1", p1), ("P2", p2)]
  let mut P := p2
  for i in [0:8] do
    let r := Compilatrix.Anf.Inline.produce {} P
    if r.isEmpty then break
    let (p3, _) ← Compilatrix.Anf.Inline.round P r
    let (_, p2', _) ← Compilatrix.Anf.Shrink.produce {} p3
    out := out ++ [(s!"P3.{i}", p3), (s!"P2.{i}", p2')]
    P := p2'
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--dump", name] =>
    let l ← loadBench name
    let e ← CompilatrixTests.Lam.eraseLoaded l
    for (stage, A) in ← IO.ofExcept (stages e.lam) do
      IO.println s!"== {stage}\n{A.render}"
    return 0
  | _ => pure ()
  let a ← IO.mkRef 0
  try
    IO.println "tests-anf"
    part a "Lam against Anf on k1.ixe and bench-k1, after every pass" do
      for line in ← Differential.packs a stages do IO.println s!"    {line}"
    IO.println s!"tests-anf: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-anf: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Anf.Run
