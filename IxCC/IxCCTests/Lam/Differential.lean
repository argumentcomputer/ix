import IxCCTests.Lam.Support
import IxCCTests.Src.Relevance.Stuck
import IxCCTests.Src.Bench
import IxCCTests.Src.Rules
import IxCCTests.Src.SortPoly
import IxCCTests.Fixtures.K1
import IxCCTests.Fixtures.SortPoly

/-! SrcEval against Lam on the Phase 1 fixtures:

* **k1.ixe and each bench-k1 closure**, with every first-order constant of
  the closure as an extra root (as the stuck-cause census selects them: no
  universe parameters, `Nat → … → Nat|Bool`, at most three arguments), run
  on its small arguments and on every tuple over `{0, 1, 2}`: equal
  readback, traps and timeouts preserved, least clocks never earlier and
  equal without wrappers;
* **src-sortpoly**, one root at a time: every root but `typeArg` (rejected by
  the checker) erases and matches native Lean on 0–20, `sigmaRoot`'s `PSigma`
  projection included; `unitBoth` makes one global per profile;
* the **fallback route** (no `eqn` entries), whose recursors reach run time:
  `brecOn` through `Nat.rec` with by-name IHs and `PProd` projections,
  `WellFounded.fix` through `Acc.rec`;
* **native Lean** (`IxCCTests.Fixtures.K1`) against Lam on the K1 roots, as `tests-src`
  does for SrcEval; the bench-k1 entries at their test sizes
  (`sum-loop` 10⁶ in a child process with a larger stack);
* `Erase.Input.unbox?` equals `Checked.unbox?` on every inductive whose
  field classes do not depend on the profile, at every profile;
  `WellFormed`, `ModesOk` and erased sizes of every program. -/

namespace IxCCTests.Lam.Differential

open IxCC IxCC.Src IxCC.Src.Relevance IxCCTests.Src
open IxCCTests.Lam
open IxCCTests.Src.Relevance.Stuck (firstOrderConsts smallTuples rootArgs benchArgs)
open IxCCTests.Src.Rules (Gen)
open IxCC.Sem (Result)

/-- A pack loaded with its first-order constants as extra roots. -/
def loadWithFirstOrder (ixe eqs : System.FilePath) : IO (Loaded × Array (CId × Nat)) := do
  let bytes ← IO.FS.readBinFile ixe
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let cfg : LoadConfig := {}
  let (p0, _, _, _) ← IO.ofExcept ((prepare cfg env hints).mapError toString)
  let fo := firstOrderConsts p0
  let extra := fo.filterMap fun (c, _) =>
    let a := p0.addr c
    if hints.roots.any (·.1 == a) then none else some (a, none)
  match loadEnv cfg env { hints with roots := hints.roots ++ extra } with
  | .ok l => return (l, fo)
  | .error d => throw (IO.userError s!"{ixe}: {d}")

/-- Every profile of `n` universe parameters (`n ≤ 3`). -/
def profiles : Nat → List Profile
  | 0 => [[]]
  | n + 1 => (profiles n).flatMap fun p => [true :: p, false :: p]

/-- S3 on lists agrees with the checker's `unbox?`, on every inductive whose
field classes do not depend on the profile (the others have one layout at
every profile, `Erase.Input.layoutClass`). -/
def unboxAgrees (a : Assert) (e : Erased) (label : String) : IO Nat := do
  let mut n := 0
  for c in List.range e.src.size do
    let some (.induct _ lvls _ _ _ ctors) := e.src.decl? c | continue
    if lvls > 3 then continue
    let conditional := ctors.any fun k => match e.checked.ctorRel? k with
      | some r => r.fields.any fun
        | .proof (.allZero (_ :: _)) => true
        | _ => false
      | none => false
    if conditional then continue
    for prof in profiles lvls do
      expect a (e.input.unbox? c prof == e.checked.unbox? e.src c prof)
        s!"{label}: unbox? of {c} at {prof.render}"
      n := n + 1
  return n

def sizes (e : Erased) : String :=
  let keys := e.lam.globalList.map (·.2.key)
  let count := fun (f : Key.GKey → Bool) => (keys.filter f).length
  s!"{e.stats.globals} globals ({count (· matches .const ..)} const, \
    {count (· matches .byName ..)} byName, {count (· matches .recStar ..)} r⋆, \
    {count (· matches .wrapper ..)} wrapper), {e.stats.nodes} nodes, {e.stats.ctors} constructors"

/-- Roots and first-order constants of one pack. -/
def pack (a : Assert) (label : String) (ixe eqs : System.FilePath) (args : String → List (List Nat))
    (rootClock : Nat) : IO (Array String) := do
  let (l, fo) ← loadWithFirstOrder ixe eqs
  let e ← eraseLoaded l
  checkStatic a e label
  let unboxes ← unboxAgrees a e label
  let mut t : Tally := {}
  for (addr, c) in l.program.roots do
    -- The pack's own roots (the extra first-order roots have no sidecar name).
    let some name := l.hints.roots.findSome? fun (a', n) => if a' == addr then n else none
      | continue
    for xs in args name do
      t ← compareRun a e c xs rootClock s!"{label} {name}" t
  let mut tf : Tally := {}
  for (c, arity) in fo do
    let name := (Loaded.names l.hints (l.program.addr c)).getD (l.program.short c)
    for xs in smallTuples arity do
      tf ← compareRun a e c xs 10000 s!"{label} {name}" tf
  return #[s!"{label}: {sizes e}; unbox? agrees at {unboxes} (inductive, profile) pairs",
    s!"  roots: {t.render}", s!"  {fo.size} first-order constants: {tf.render}"]

/-- The erased size of each bench-k1 closure alone (its entry root only). -/
def benchSizes (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let e ← eraseLoaded (← loadBench name)
    checkStatic a e name
    out := out.push s!"{name}: {sizes e}"
  return out

/-- src-sortpoly, one root at a time. -/
def sortpoly (a : Assert) : IO (Array String) := do
  let dir := fixtures / "src-sortpoly"
  let bytes ← IO.FS.readBinFile (dir / "sortpoly.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "sortpoly.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let mut out := #[]
  let mut t : Tally := {}
  for root in hints.roots do
    let name := root.2.getD "?"
    if name == IxCCTests.Src.SortPoly.typeRoot then continue
    let l ← match loadEnv {} env { hints with roots := #[root] } with
      | .ok l => pure l
      | .error d => throw (IO.userError s!"src-sortpoly {name}: {d}")
    match erase l.program l.checked with
    | .error msg => expect a false s!"src-sortpoly {name}: declined: {msg}"
    | .ok e =>
      checkStatic a e name
      let some f := IxCCTests.Src.SortPoly.native name
        | throw (IO.userError s!"src-sortpoly: no native twin for {name}")
      let some c := l.root? | throw (IO.userError s!"src-sortpoly {name}: no root")
      let g ← lamRoot e c
      for n in List.range 21 do
        let r ← runLam e.lam 10000 g [n]
        expect a (match r with | .ok (.lit (.nat m)) => m == f n | _ => false)
          s!"src-sortpoly {name} {n}: Lam {lamOutcome r}, Lean {f n}"
        t ← compareRun a e c [n] 10000 name t
      if name == "SortPoly.unitBoth" then
        let consts := e.lam.globalList.filter fun (_, gl) => gl.key matches .const ..
        let cs := consts.filterMap fun (_, gl) => match gl.key with
          | .const c _ => some c | _ => none
        expect a (cs.length > cs.eraseDups.length) "unitBoth: one constant at two profiles"
      out := out.push s!"{name}: matches native Lean on 0–20; {sizes e}"
  out := out.push s!"src-sortpoly runs: {t.render}"
  return out

def clock : Nat := 1 <<< 40

def agree (a : Assert) (e : Erased) (root : CId) (label : String) (args : List Nat)
    (native : Nat) : IO Unit := do
  let r ← runLam e.lam clock (← lamRoot e root) args
  expect a (match r with | .ok (.lit (.nat n)) => n == native | _ => false)
    s!"{label} {args}: Lam {lamOutcome r}, Lean {native}"

/-- Lam against the K1 fixture compiled natively. -/
def native (a : Assert) : IO Unit := do
  let l ← loadK1
  let e ← eraseLoaded l
  let fib ← rootNamed l "K1.fib"
  for n in [0:26] do agree a e fib "fib" [n] (K1.fib n)
  let ack ← rootNamed l "K1.ack"
  for m in [0:4] do
    for n in [0:6] do agree a e ack "ack" [m, n] (K1.ack m n)
  let tak ← rootNamed l "K1.tak"
  let mut g : Gen := { seed := 7 }
  for _ in [0:120] do
    let (f, g1) := g.next 9
    let (x, g2) := g1.next 13
    let (y, g3) := g2.next 13
    let (z, g4) := g3.next 13
    g := g4
    agree a e tak "tak" [f, x, y, z] (K1.tak f x y z)
  let sumLoop ← rootNamed l "K1.sumLoop"
  for n in [0, 1, 2, 3, 10, 99, 1000, 10000] do agree a e sumLoop "sumLoop" [n] (K1.sumLoop n)
  let gcd ← rootNamed l "K1.gcd"
  for _ in [0:1000] do
    let (x, g1) := g.next (1 <<< 40)
    let (y, g2) := g1.next (1 <<< 40)
    g := g2
    agree a e gcd "gcd" [x, y] (K1.gcd x y)
  for (x, y) in [(0, 0), (0, 7), (7, 0), (2 ^ 40 - 1, 2 ^ 39 + 1)] do
    agree a e gcd "gcd" [x, y] (K1.gcd x y)

/-- Run one bench entry through Lam and print its result (the child-process
mode, for `sum-loop`'s deep recursion). -/
def runEntry (name : String) : IO Nat := do
  let l ← loadBench name
  let e ← eraseLoaded l
  let (args, _) ← IxCCTests.Src.Bench.testCase name
  let some root := l.root? | throw (IO.userError s!"{name}: no root")
  match ← runLam e.lam clock (← lamRoot e root) args with
  | .ok (.lit (.nat n)) => return n
  | r => throw (IO.userError s!"{name}: {lamOutcome r}")

/-- The bench-k1 entries at their test sizes. -/
def bench (a : Assert) (self : System.FilePath) : IO (Array String) := do
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
    expectEq a got expected s!"{name} {args} through Lam"
    out := out.push s!"{name} {args} = {got} (expected {expected}) in {ms} ms"
  return out

/-- Least clocks of SrcEval and Lam on the K1 roots (as `tests-src` reports
SrcEval's): equal, since erasure is clock-exact outside wrappers. -/
def leastClocks (a : Assert) : IO (Array String) := do
  let l ← loadK1
  let e ← eraseLoaded l
  let mut out := #[]
  for (name, args) in [("K1.fib", [15]), ("K1.ack", [2, 3]), ("K1.tak", [8, 6, 4, 2]),
      ("K1.sumLoop", [100]), ("K1.gcd", [832040, 514229])] do
    let c ← rootNamed l name
    let g ← lamRoot e c
    let hi := 10000000
    let s ← leastClock (fun k => do return notTimeout (← runSrc e.src k c args)) hi
    let m ← leastClock (fun k => do return notTimeout (← runLam e.lam k g args)) hi
    expect a (s.isSome && s == m) s!"{name} {args}: least clocks SrcEval {s}, Lam {m}"
    out := out.push s!"{name} {args}: least clock {s.getD 0} (SrcEval and Lam)"
  return out

/-- The fallback route (no `eqn` entries), as `tests-src` runs it: `fib`
through `brecOn` (`Nat.rec` with by-name IHs, projections out of `PProd`,
whose field classes depend on its levels) and `ack` through
`WellFounded.fix` (`Acc.rec`, a subsingleton recursor). -/
def fallback (a : Assert) : IO (Array String) := do
  let bytes ← IO.FS.readBinFile (fixtures / "k1/k1.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "k1/equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let l ← match loadEnv {} env { hints with proposals := #[] } with
    | .ok l => pure l
    | .error d => throw (IO.userError s!"fallback load: {d}")
  let e ← eraseLoaded l
  checkStatic a e "fallback"
  expect a (e.lam.globalList.any fun (_, gl) => gl.key matches .recStar ..)
    "the fallback route has recursors at run time"
  let mut t : Tally := {}
  for (root, argss) in [("K1.fib", [[0], [1], [2], [7], [15]]),
      ("K1.ack", [[0, 0], [1, 2], [2, 3]]), ("K1.gcd", [[30, 12], [0, 5]]),
      ("K1.tak", [[6, 4, 2, 1]]), ("K1.sumLoop", [[0], [20]])] do
    let c ← rootNamed l root
    for xs in argss do
      t ← compareRun a e c xs 1000000 s!"fallback {root}" t
  return #[s!"fallback (no eqn entries): {sizes e}", s!"  {t.render}"]

def packs (a : Assert) : IO (Array String) := do
  let mut out ← pack a "k1.ixe" (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json")
    rootArgs 1000000
  for name in benchNames do
    out := out ++ (← pack a name (fixtures / "bench-k1" / s!"{name}.ixe")
      (fixtures / "bench-k1" / s!"{name}.equations.json") (fun _ => benchArgs name) 1000000)
  return out

end IxCCTests.Lam.Differential
