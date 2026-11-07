import IxCCTests.Anf.Support
import IxCCTests.Lam.Differential
import IxCC.Anf.Pipeline

/-! Lam against Anf on the Phase 1 fixtures (design note 02 §13 item 3):
every root and first-order constant of `k1.ixe` and of each bench-k1
closure, through Src → Lam → Anf, after every pass of the Phase 1 pipeline:
equal readback, traps, the timeout clause and tick dominance
(`compareRun`), and `WellScoped` after every pass. -/

namespace IxCCTests.Anf.Differential

open IxCC IxCC.Src IxCCTests.Src IxCCTests.Lam
open IxCCTests.Src.Relevance.Stuck (smallTuples rootArgs benchArgs)
open IxCCTests.Lam.Differential (loadWithFirstOrder)

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

/-- The fallback route (no `eqn` entries), whose recursors reach run time:
`r⋆` globals with by-name minors and IHs (P1's thunks and dispatch), `brecOn`
projections, `WellFounded.fix` through `Acc.rec`. -/
def fallback (a : Assert) (stages : Stages) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile (fixtures / "k1/k1.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "k1/equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let l ← match loadEnv { typecheck := false } env { hints with proposals := #[] } with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"fallback load: {d}")
  let e ← eraseLoaded l
  let ss ← IO.ofExcept (stages e.lam)
  let mut out := #[]
  for (stage, A) in ss do
    checkScoped a A s!"fallback after {stage}"
    let mut t : Tally := {}
    for (root, argss) in [("K1.fib", [[0], [1], [2], [7]]),
        ("K1.ack", [[0, 0], [1, 2], [2, 3]]), ("K1.gcd", [[30, 12], [0, 5]]),
        ("K1.tak", [[6, 4, 2, 1]]), ("K1.sumLoop", [[0], [20]])] do
      let lr ← lamRoot e (← rootNamed l root)
      for xs in argss do
        t ← compareRun a e.lam A lr xs 100000 s!"fallback {stage} {root}" t
    let r := IxCC.Anf.Pipeline.residual A
    out := out.push s!"fallback after {stage} ({sizeStr A}): {t.render}; \
      residual fn {r.fns} app {r.apps} glob {r.globs}"
  return out

/-- src-sortpoly, one root at a time (sort-polymorphic code at `Sort 0`). -/
def sortpoly (a : Assert) (stages : Stages) : IO (Array String) := do
  let dir := fixtures / "src-sortpoly"
  let bytes ← IO.FS.readBinFile (dir / "sortpoly.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "sortpoly.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let mut t : Tally := {}
  let mut n := 0
  for root in hints.roots do
    let name := root.2.getD "?"
    if name == IxCCTests.Src.SortPoly.typeRoot then continue
    let l ← match loadEnv { typecheck := false } env { hints with roots := #[root] } with
      | .ok l => pure l
      | .error d => throw (IO.userError s!"src-sortpoly {name}: {d}")
    let e ← eraseLoaded l
    let some c := l.root? | throw (IO.userError s!"src-sortpoly {name}: no root")
    let lr ← lamRoot e c
    for (stage, A) in ← IO.ofExcept (stages e.lam) do
      checkScoped a A s!"src-sortpoly {name} after {stage}"
      for k in [0, 1, 2, 5, 20] do
        t ← compareRun a e.lam A lr [k] 10000 s!"src-sortpoly {name} {stage}" t
      n := n + 1
  return #[s!"src-sortpoly: {n} (root, stage) pairs: {t.render}"]

def packs (a : Assert) (stages : Stages) : IO (Array String) := do
  let mut out ← pack a stages "k1.ixe" (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json")
    rootArgs 1000000
  for name in benchNames do
    out := out ++ (← pack a stages name (fixtures / "bench-k1" / s!"{name}.ixe")
      (fixtures / "bench-k1" / s!"{name}.equations.json") (fun _ => benchArgs name) 1000000)
  return out

end IxCCTests.Anf.Differential
