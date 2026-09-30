import CompilatrixTests.Anf.Support
import CompilatrixTests.Lam.Differential

/-! Lam against Anf on the Phase 1 fixtures (design note 02 §13 item 3):
every root and first-order constant of `k1.ixe` and of each bench-k1
closure, through Src → Lam → Anf, after every pass of the Phase 1 pipeline:
equal readback, traps, the timeout clause and tick dominance
(`compareRun`), and `WellScoped` after every pass. -/

namespace CompilatrixTests.Anf.Differential

open Compilatrix Compilatrix.Src CompilatrixTests.Src CompilatrixTests.Lam
open CompilatrixTests.Src.Relevance.Stuck (smallTuples rootArgs benchArgs)
open CompilatrixTests.Lam.Differential (loadWithFirstOrder)

/-- The Anf program after each stage. -/
abbrev Stages := LProgram → Except String (List (String × AProgram))

/-- Roots and first-order constants of one pack, after every stage. -/
def pack (a : Assert) (stages : Stages) (label : String) (ixe eqs : System.FilePath)
    (args : String → List (List Nat)) (rootClock : Nat) : IO (Array String) := do
  let (l, fo) ← loadWithFirstOrder ixe eqs
  let e ← eraseLoaded l
  let ss ← IO.ofExcept (stages e.lam)
  let mut out := #[]
  for (stage, A) in ss do
    checkScoped a A s!"{label} after {stage}"
    let mut t : Tally := {}
    for (addr, c) in l.program.roots do
      let some name := l.hints.roots.findSome? fun (a', n) => if a' == addr then n else none
        | continue
      let lr ← lamRoot e c
      for xs in args name do
        t ← compareRun a e.lam A lr xs rootClock s!"{label} {stage} {name}" t
    let mut tf : Tally := {}
    for (c, arity) in fo do
      let name := (Loaded.names l.hints (l.program.addr c)).getD (l.program.short c)
      let lr ← lamRoot e c
      for xs in smallTuples arity do
        tf ← compareRun a e.lam A lr xs 10000 s!"{label} {stage} {name}" tf
    out := out.push s!"{label} after {stage} ({sizeStr A}): roots {t.render}; \
      {fo.size} first-order constants {tf.render}"
  return out

def packs (a : Assert) (stages : Stages) : IO (Array String) := do
  let mut out ← pack a stages "k1.ixe" (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json")
    rootArgs 1000000
  for name in benchNames do
    out := out ++ (← pack a stages name (fixtures / "bench-k1" / s!"{name}.ixe")
      (fixtures / "bench-k1" / s!"{name}.equations.json") (fun _ => benchArgs name) 1000000)
  return out

end CompilatrixTests.Anf.Differential
