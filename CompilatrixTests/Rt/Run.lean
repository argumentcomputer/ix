import CompilatrixTests.Rt.Differential
import CompilatrixTests.Rt.Cases
import CompilatrixTests.Rt.Mutants

/-! The `tests-rt` suite (design note 04 §13, M1.F6). -/

namespace CompilatrixTests.Rt.Run

open CompilatrixTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let a ← IO.mkRef 0
  try
    match args with
    | ["--prims"] =>
      let packs := [("k1", fixtures / "k1/k1.ixe", fixtures / "k1/equations.json")] ++
        benchNames.map fun n => (n, fixtures / "bench-k1" / s!"{n}.ixe", fixtures / "bench-k1" / s!"{n}.equations.json")
      for (name, ixe, eqs) in packs do
        let (l, _) ← CompilatrixTests.Lam.Differential.loadWithFirstOrder ixe eqs
        let e ← CompilatrixTests.Lam.eraseLoaded l
        let A ← CompilatrixTests.Fir.Differential.finalAnf e.lam
        let L ← IO.ofExcept (CompilatrixTests.Fir.lower A)
        let ps := L.cfg.funList.flatMap fun (f, fd) => fd.blocks.flatMap fun b => b.body.filterMap fun
          | .bind _ (.fir (.prim op _)) => some (f, op.name)
          | _ => none
        let names := (ps.map (·.2)).eraseDups
        IO.println s!"{name}: {names}"
        for n in names do
          IO.println s!"  {n}: functions {((ps.filter (·.2 == n)).map (·.1)).eraseDups}"
    | ["--generated", n] =>
      part a "generated first-order programs" (Differential.generated a n.toNat!)
    | _ =>
      IO.println "tests-rt"
      part a "primitive sequences at their boundaries" (Cases.prims a)
      part a "hand-written programs, declines and cx_init" (Cases.handWritten a)
      part a "planted mutations" (Mutants.run a)
      part a "k1.ixe and bench-k1: Cfg → Lir" (Differential.packs a)
      part a "bench-k1 entries at their test sizes, at Lir" (Differential.entries a)
      part a "generated first-order programs" (Differential.generated a 1000)
    IO.println s!"tests-rt: {← a.get} assertions passed"
    return 0
  catch e =>
    IO.eprintln s!"tests-rt: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Rt.Run
