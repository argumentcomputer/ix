import IxCCTests.Anf.Support
import IxCCTests.Anf.KernelEval
import IxCC.Anf.Pipeline
import IxCCTests.Src.Bench

/-! The K1 shape expectations after the Phase 1 pipeline (design note 02
§13.4, §9), on each bench-k1 entry and on the K1 roots of `k1.ixe`:

* `fib`, `ack`, `tak`, `gcd`: the program reachable from the root is one
  recursive global that calls only itself and primitives, plus the entry
  wrapper calling it; no `fn`, `app`, `glob` (so no dictionary or instance
  CAF), no constructor;
* `sumLoop`: one loop (a self-recursive global) over three live `Nat`
  parameters (the others hold □, which P5 would drop), with no `fn`, `app`,
  `glob` or constructor (no allocation);
* every reachable program is `FirstOrder` (nothing for the Anf → Fir
  boundary to decline) and has no CAF.

These are structural summaries, not golden text. A shape that is not
reached fails with an exact account of what remains (the decline set for
M1.F5). Sizes (Lam, P1, final) are reported per fixture. -/

namespace IxCCTests.Anf.Shapes

open IxCC IxCCTests.Src IxCCTests.Lam
open IxCC.Anf (Program GDef Exp Bind Alt GlobalId)

/-- Counts over an expression. -/
structure Counts where
  fns : Nat := 0
  apps : Nat := 0
  globs : Nat := 0
  cons : Nat := 0
  prims : Nat := 0
  cases : Nat := 0
  joins : Nat := 0
  ticks : Nat := 0
  calls : List GlobalId := []
  deriving Inhabited

def Counts.add (a b : Counts) : Counts :=
  { fns := a.fns + b.fns, apps := a.apps + b.apps, globs := a.globs + b.globs
    cons := a.cons + b.cons, prims := a.prims + b.prims, cases := a.cases + b.cases
    joins := a.joins + b.joins, ticks := a.ticks + b.ticks, calls := a.calls ++ b.calls }

mutual

partial def countExp : Exp → Counts
  | .bind _ b e => (countBind b).add (countExp e)
  | .join _ _ b e => ({ joins := 1 } : Counts).add ((countExp b).add (countExp e))
  | .case _ alts d =>
    let cs := alts.foldl (fun acc (a : Alt) => acc.add (countExp a.body)) ({ cases := 1 } : Counts)
    match d with
    | some e => cs.add (countExp e)
    | none => cs
  | .tick e => ({ ticks := 1 } : Counts).add (countExp e)
  | .jump .. | .ret _ | .trap => {}

partial def countBind : Bind → Counts
  | .fn _ b => ({ fns := 1 } : Counts).add (countExp b)
  | .app .. => { apps := 1 }
  | .glob _ => { globs := 1 }
  | .con .. => { cons := 1 }
  | .prim .. => { prims := 1 }
  | .call g _ => { calls := [g] }
  | .atom _ | .proj .. => {}

end

/-- Globals reachable from `root`. -/
partial def reachable (P : Program) (root : GlobalId) : List GlobalId :=
  go [root] []
where
  go : List GlobalId → List GlobalId → List GlobalId
    | [], seen => seen.reverse
    | g :: todo, seen =>
      if seen.contains g then go todo seen
      else go ((((P.global? g).map (·.body.refs)).getD []) ++ todo) (g :: seen)

/-- Parameters whose variable occurs in the body. -/
def liveParams (gd : GDef) : Nat :=
  (List.range gd.ps.length).countP fun i => gd.body.occ (gd.ps.length - 1 - i) > 0

/-- The shape of the program reachable from a root. -/
structure Shape where
  globals : List GlobalId
  counts : Counts
  recursive : List GlobalId
  cafs : List GlobalId
  firstOrder : Bool
  /-- Per recursive global: its live parameters and its callees other than
  itself. -/
  cores : List (GlobalId × Nat × List GlobalId)
  nodes : Nat

def shapeOf (P : Program) (root : GlobalId) : Shape :=
  let gs := reachable P root
  let per := gs.filterMap fun g => (P.global? g).map fun gd => (g, gd, countExp gd.body)
  let counts := per.foldl (fun acc (_, _, c) => acc.add c) {}
  let recursive := (per.filter fun (g, _, c) => c.calls.contains g).map (·.1)
  let cafs := (per.filter fun (_, gd, _) => gd.ps.isEmpty).map (·.1)
  let isFn := fun h => (P.arity? h).any (· > 0)
  { globals := gs, counts, recursive, cafs
    firstOrder := per.all fun (_, gd, _) => gd.body.firstOrder isFn
    cores := (per.filter fun (g, _, _) => recursive.contains g).map fun (g, gd, c) =>
      (g, liveParams gd, c.calls.eraseDups.filter (· != g))
    nodes := per.foldl (fun n (_, gd, _) => n + gd.body.nodes) 0 }

def Shape.render (s : Shape) : String :=
  let c := s.counts
  s!"{s.globals.length} globals/{s.nodes} nodes, recursive {s.recursive}, CAFs {s.cafs}, \
    fn {c.fns} app {c.apps} glob {c.globs} con {c.cons} prim {c.prims} case {c.cases} \
    join {c.joins} tick {c.ticks}, first order {s.firstOrder}, cores {s.cores}"

/-- The expected shape: `live` is the loop's number of live parameters
(`none` for the recursive functions, whose parameters are all live). -/
def check (a : Assert) (label : String) (P : Program) (root : GlobalId) (live : Option Nat) :
    IO String := do
  let s := shapeOf P root
  let c := s.counts
  let fail := fun (what : String) => s!"{label}: {what}; what remains: {s.render}\n{P.render}"
  expect a s.firstOrder (fail "not FirstOrder")
  expect a (c.fns == 0 && c.apps == 0 && c.globs == 0) (fail "closures or dictionaries remain")
  expect a (c.cons == 0) (fail "an allocation remains")
  expect a s.cafs.isEmpty (fail "a CAF remains")
  expect a (s.recursive.length == 1) (fail "not exactly one recursive global")
  match s.cores with
  | [(g, n, others)] =>
    expect a others.isEmpty (fail s!"the core g{g} calls other globals {others}")
    if let some want := live then
      expect a (n == want) (fail s!"the loop has {n} live parameters, expected {want}")
    -- every other reachable global calls only the core
    for h in s.globals do
      if h == g then continue
      let cs := ((P.global? h).map fun gd => (countExp gd.body).calls.eraseDups).getD []
      expect a (cs.all (· == g)) (fail s!"g{h} calls {cs}, not only the core g{g}")
  | _ => expect a false (fail "no single core")
  return s!"{label}: {s.render}"

/-- Globals and nodes of a Lam program. -/
def lamSize (L : LProgram) : String :=
  s!"{L.size} globals/{L.globalList.foldl (fun n (_, gl) => n + gl.body.nodes) 0} nodes"

def anfSize (P : Program) : String :=
  s!"{P.size} globals/{P.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0} nodes"

/-- The certificate replayed by the recheck reproduces `produce`'s program,
and shrink is idempotent there (02 §13 item 6). -/
def replay (a : Assert) (label : String) (L : LProgram) (tr : Anf.Pipeline.Trace)
    (final : Program) : IO Unit := do
  let again ← IO.ofExcept (Anf.Pipeline.run tr.cert L)
  expect a (again.beq final) s!"{label}: replaying the certificate differs from produce"
  let (c, P, f) ← IO.ofExcept (Anf.Shrink.produce {} final)
  expect a (c.all (· == 0) && f.total == 0 && P.beq final)
    s!"{label}: shrink is not idempotent at the pipeline's fixpoint ({f.render})"

/-- The shape of one bench entry, with its sizes at each end. -/
def bench (a : Assert) (name : String) : IO (Array String) := do
  let e ← eraseLoaded (← loadBench name)
  let tr ← IO.ofExcept (Anf.Pipeline.produce {} e.lam)
  let p1 := ((tr.stages.head?).map (·.2)).getD default
  let final := ((tr.stages.getLast?).map (·.2)).getD default
  let some root := final.roots.head? | throw (IO.userError s!"{name}: no root")
  let line ← check a name final root (if name == "sum-loop" then some 3 else none)
  replay a name e.lam tr final
  let r := Anf.Pipeline.residual final
  return #[s!"{name}: Lam {lamSize e.lam}, P1 {anfSize p1}, final {anfSize final}; \
    residual fn {r.fns} app {r.apps} glob {r.globs}; {tr.cert.steps.length} certificate steps; \
    shrink rules {tr.fires.render}",
    s!"  {line}"]

/-- The final program of a bench entry. -/
def benchFinal (name : String) : IO (Program × Nat) := do
  let e ← eraseLoaded (← loadBench name)
  let tr ← IO.ofExcept (Anf.Pipeline.produce {} e.lam)
  let final := ((tr.stages.getLast?).map (·.2)).getD default
  let some root := final.roots.head? | throw (IO.userError s!"{name}: no root")
  return (final, root)

/-- Run one entry through the pipeline's output and print its result (the
child-process mode, for `sum-loop`'s deep recursion). -/
def runEntry (name : String) : IO Nat := do
  let (final, root) ← benchFinal name
  let (args, _) ← IxCCTests.Src.Bench.testCase name
  match ← runAnf final (1 <<< 40) root args with
  | .ok (.lit (.nat n)) => return n
  | r => throw (IO.userError s!"{name}: {anfOutcome r}")

/-- The bench-k1 entries at their test sizes through the pipeline's output,
against the fixture's expected results. -/
def entries (a : Assert) (self : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let (args, expected) ← IxCCTests.Src.Bench.testCase name
    let (got, ms) ← timed do
      if name == "sum-loop" then
        let env := #[("LEAN_STACK_SIZE_KB", some (toString IxCCTests.Src.Bench.deepStackKb))]
        let out ← IO.Process.output { cmd := self.toString, args := #["--entry", name], env }
        unless out.exitCode == 0 do
          throw (IO.userError s!"{name} child exited {out.exitCode}: {out.stderr}")
        pure out.stdout.trimAscii.toString.toNat!
      else runEntry name
    expectEq a got expected s!"{name} {args} through the Anf pipeline"
    out := out.push s!"{name} {args} = {got} (expected {expected}) in {ms} ms"
  return out

/-- The K1 roots of `k1.ixe` (the whole closure through the pipeline). -/
def k1 (a : Assert) : IO (Array String) := do
  let l ← loadK1
  let e ← eraseLoaded l
  let tr ← IO.ofExcept (Anf.Pipeline.produce {} e.lam)
  let final := ((tr.stages.getLast?).map (·.2)).getD default
  replay a "k1.ixe" e.lam tr final
  let mut out := #[s!"k1.ixe: Lam {lamSize e.lam}, final {anfSize final}"]
  for name in ["K1.fib", "K1.ack", "K1.tak", "K1.sumLoop", "K1.gcd"] do
    let c ← rootNamed l name
    let lr ← lamRoot e c
    let some root := anfRoot e.lam final lr | throw (IO.userError s!"{name}: no Anf root")
    let line ← check a name final root (if name == "K1.sumLoop" then some 3 else none)
    out := out.push s!"  {line}"
  -- least clocks of Lam and of the pipeline's output (the tick overhead)
  for (name, args) in [("K1.fib", [15]), ("K1.ack", [2, 3]), ("K1.tak", [8, 6, 4, 2]),
      ("K1.sumLoop", [100]), ("K1.gcd", [832040, 514229])] do
    let c ← rootNamed l name
    let lr ← lamRoot e c
    let some root := anfRoot e.lam final lr | throw (IO.userError s!"{name}: no Anf root")
    let hi := 100000000
    let ll ← leastClock (fun k => do return notTimeout (← runLam e.lam k lr args)) hi
    let la ← leastClock (fun k => do return notTimeout (← runAnf final k root args)) hi
    expect a (ll.isSome && la.isSome && decide (ll.getD 0 ≤ la.getD 0))
      s!"{name} {args}: least clocks Lam {ll}, Anf {la}"
    out := out.push s!"  {name} {args}: least clock Lam {ll.getD 0}, final Anf {la.getD 0}"
  return out

def run (a : Assert) : IO (Array String) := do
  -- Multi-use small local `.fn` whose occurrences are all saturated head calls:
  -- P1 emits 1 `.fn` and 2 `.app`s; the pipeline β-inlines both leaving 0 `.fn`s.
  let p1 ← IO.ofExcept (Anf.convert KernelEval.sharedCont)
  let c1 := (shapeOf p1 0).counts
  expect a (c1.fns == 1 && c1.apps == 2)
    s!"sharedCont P1: expected 1 fn and 2 apps, got fn {c1.fns} app {c1.apps}"
  let tr ← IO.ofExcept (Anf.Pipeline.produce {} KernelEval.sharedCont)
  let final := ((tr.stages.getLast?).map (·.2)).getD default
  let cf := (shapeOf final 0).counts
  expect a (cf.fns == 0 && cf.apps == 0 && (shapeOf final 0).firstOrder)
    s!"sharedCont final: expected 0 fns and 0 apps, got fn {cf.fns} app {cf.apps}"
  replay a "sharedCont" KernelEval.sharedCont tr final
  let mut out := #[]
  for name in benchNames do
    out := out ++ (← bench a name)
  return out ++ (← k1 a)

end IxCCTests.Anf.Shapes
