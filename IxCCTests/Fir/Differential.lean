import IxCCTests.Fir.Support
import IxCCTests.Anf.Differential
import IxCC.Anf.Pipeline

/-! Every Phase 1 level on the fixtures (design note 03 §11, M1.F5): each
root and first-order constant of `k1.ixe` and of the five bench-k1
closures, through Src → Lam → Anf (the Phase 1 pipeline) → Fir → Own → Cfg,
compared level by level (`compareRun`: readback against Anf and Lam, traps,
the clock map of each level and its timeout clause), with well-formedness at
every level and the sizes of each program. The fallback route (no `eqn`
entries), whose output keeps closures, is declined at Fir with the
`fir.closures` diagnostic naming exactly `Pipeline.residual`. -/

namespace IxCCTests.Fir.Differential

open IxCC IxCC.Src IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCCTests.Src.Relevance.Stuck (smallTuples rootArgs benchArgs)
open IxCCTests.Lam.Differential (loadWithFirstOrder)

/-- The pipeline's final Anf program. -/
def finalAnf (L : LProgram) : IO AProgram := do
  let t ← IO.ofExcept (Anf.Pipeline.produce {} L)
  return ((t.stages.getLast?).map (·.2)).getD default

/-- Roots and first-order constants of one pack. -/
def pack (a : Assert) (label : String) (ixe eqs : System.FilePath)
    (args : String → List (List Nat)) (rootClock : Nat) : IO (Array String) := do
  let (l, fo) ← loadWithFirstOrder ixe eqs
  let e ← eraseLoaded l
  let A ← finalAnf e.lam
  let L ← IO.ofExcept (lower A)
  checkLevels a L label
  let mut t : Tally := {}
  for (addr, c) in l.program.roots do
    let some name := l.hints.roots.findSome? fun (a', n) => if a' == addr then n else none
      | continue
    let lr ← lamRoot e c
    let some ar := anfRoot e.lam A lr | throw (IO.userError s!"{label} {name}: no Anf root")
    for xs in args name do
      t ← compareRun a L (some (e.lam, lr)) ar xs rootClock s!"{label} {name}" t
  let mut tf : Tally := {}
  for (c, arity) in fo do
    let name := (Loaded.names l.hints (l.program.addr c)).getD (l.program.short c)
    let lr ← lamRoot e c
    let some ar := anfRoot e.lam A lr | throw (IO.userError s!"{label} {name}: no Anf root")
    for xs in smallTuples arity do
      tf ← compareRun a L (some (e.lam, lr)) ar xs 10000 s!"{label} {name}" tf
  return #[s!"{label}: {sizes L}", s!"  roots {t.render}",
    s!"  {fo.size} first-order constants {tf.render}"]

def packs (a : Assert) : IO (Array String) := do
  let mut out ← pack a "k1.ixe" (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json")
    rootArgs 1000000
  for name in benchNames do
    out := out ++ (← pack a name (fixtures / "bench-k1" / s!"{name}.ixe")
      (fixtures / "bench-k1" / s!"{name}.equations.json") (fun _ => benchArgs name) 1000000)
  return out

/-- The fallback route keeps closures after the middle end (`fn`, `app`,
function `glob`): Fir declines it, naming exactly the residual globals. -/
def fallback (a : Assert) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile (fixtures / "k1/k1.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "k1/equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let l ← match loadEnv { typecheck := false } env { hints with proposals := #[] } with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"fallback load: {d}")
  let e ← eraseLoaded l
  let t ← IO.ofExcept (Anf.Pipeline.produce {} e.lam)
  let mut out := #[]
  let mut declined := 0
  let mut lowered := 0
  for (stage, A) in t.stages do
    let r := Anf.Pipeline.residual A
    match IxCC.Fir.lower A with
    | .error (.closures fns apps globs) =>
      expect a (fns == r.fns && apps == r.apps && globs == r.globs)
        s!"fallback {stage}: the decline names {fns} {apps} {globs}, residual {r.fns} {r.apps} {r.globs}"
      expect a (!(r.fns.isEmpty && r.apps.isEmpty && r.globs.isEmpty))
        s!"fallback {stage}: declined with an empty residual"
      declined := declined + 1
    | .error err => expect a false s!"fallback {stage}: {err.render}"
    | .ok _ =>
      expect a (r.fns.isEmpty && r.apps.isEmpty && r.globs.isEmpty)
        s!"fallback {stage}: lowered although closures remain"
      lowered := lowered + 1
  let final := ((t.stages.getLast?).map (·.2)).getD default
  let diag := match IxCC.Fir.lower final with
    | .error err => err.render
    | .ok _ => "(lowered)"
  expect a (diag.startsWith "fir.closures: declined until P8")
    s!"fallback: the final program is not declined with fir.closures: {diag}"
  out := out.push s!"fallback route: {declined} of {t.stages.length} stages declined, {lowered} lowered"
  out := out.push s!"  final: {diag}"
  return out

end IxCCTests.Fir.Differential
