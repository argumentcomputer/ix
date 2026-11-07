import IxCCTests.Rt.Support
import IxCCTests.Fir.Differential
import IxCCTests.Fir.Gen
import IxCCTests.Src.Bench

/-! Cfg against Lir on the fixtures and on generated programs (M1.F6):

* every root and first-order constant of `k1.ixe` and of the five bench-k1
  closures, through the Phase 1 pipeline to Cfg and then `Rt.lower`
  (`compare`: related values and typed readback, traps, the clock relation
  and the timeout clause), with `Lir.WellFormed` on every program;
* the bench-k1 entries at their test sizes, at Lir, against `expected.txt`;
* generated first-order Anf programs (`IxCCTests.Fir.Gen`: `Nat`,
  `Bool`, pairs and options, join points, loops, allocation), each run on
  the full region and, where Cfg allocates, on object areas just too small
  and just large enough (`fail heap` exactly when the cells do not fit);
  every tenth program also on arguments near 2^63, where a result that
  leaves the words must be `fail natOverflow` (it has no related word). -/

namespace IxCCTests.Rt.Differential

open IxCC IxCC.Src IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCCTests.Fir
open IxCCTests.Src.Relevance.Stuck (smallTuples rootArgs benchArgs)
open IxCCTests.Lam.Differential (loadWithFirstOrder)

/-- Roots and first-order constants of one pack. -/
def pack (a : Assert) (label : String) (ixe eqs : System.FilePath)
    (args : String → List (List Nat)) : IO (Array String) := do
  let (l, fo) ← loadWithFirstOrder ixe eqs
  let e ← eraseLoaded l
  let A ← Differential.finalAnf e.lam
  let S ← IO.ofExcept (lowerAll A)
  checkLir a S.lir label
  let sig := boolSig S.levels.cfg
  let run := fun (name : String) (c : CId) (ar : Nat) (xs : List Nat) =>
    ({ label := s!"{label} {name}", cfg := S.levels.cfg, lir := S.lir, root := ar, args := xs, mem := S.mem
       ty := (resultTy l.program c).map (sig, ·), exact := !reachesProcs S.levels.cfg ar } : Run)
  let mut t : Tally := {}
  for (addr, c) in l.program.roots do
    let some name := l.hints.roots.findSome? fun (a', n) => if a' == addr then n else none
      | continue
    let lr ← lamRoot e c
    let some ar := anfRoot e.lam A lr | throw (IO.userError s!"{label} {name}: no Anf root")
    for xs in args name do
      t ← compare a (run name c ar xs) 10000000 t
  let mut tf : Tally := {}
  for (c, arity) in fo do
    let name := (Loaded.names l.hints (l.program.addr c)).getD (l.program.short c)
    let lr ← lamRoot e c
    let some ar := anfRoot e.lam A lr | throw (IO.userError s!"{label} {name}: no Anf root")
    for xs in smallTuples arity do
      tf ← compare a (run name c ar xs) 1000000 tf
  let lir := S.lir.program
  let blocks := lir.funcs.foldl (fun n f => n + f.blocks.size) 0
  return #[s!"{label}: {lir.funcs.size} Lir functions ({S.levels.cfg.size} and the 3 runtime procedures), {blocks} blocks, \
    {lir.size} statements and terminators (Cfg {S.levels.cfg.blocks} blocks)",
    s!"  roots {t.render}", s!"  {fo.size} first-order constants {tf.render}"]

def packs (a : Assert) : IO (Array String) := do
  let mut out ← pack a "k1.ixe" (fixtures / "k1/k1.ixe") (fixtures / "k1/equations.json") rootArgs
  for name in benchNames do
    out := out ++ (← pack a name (fixtures / "bench-k1" / s!"{name}.ixe")
      (fixtures / "bench-k1" / s!"{name}.equations.json") (fun _ => benchArgs name))
  return out

/-! ## The bench entries at their test sizes -/

/-- An entry's program at Cfg and Lir, and its root. -/
def entry (name : String) : IO (Staged × Nat) := do
  let e ← eraseLoaded (← loadBench name)
  let A ← Differential.finalAnf e.lam
  let S ← IO.ofExcept (lowerAll A [name])
  let some root := A.roots.head? | throw (IO.userError s!"{name}: no root")
  return (S, root)

def entries (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let (S, root) ← entry name
    checkLir a S.lir s!"{name} entry"
    let (args, expected) ← IxCCTests.Src.Bench.testCase name
    let (r, ms) ← timed (runLir S.lir root (1 <<< 40) args S.mem)
    match r with
    | .ok ([w], _) => expectEq a (w.toNat / 2) expected s!"{name} {args} at Lir"
    | r => expect a false s!"{name} {args} at Lir: {lirOutcome r}"
    let lir := S.lir.program
    let f := lir.funcs.toList
    out := out.push s!"{name} {args} = {expected}: Lir {ms} ms; {f.length} functions, \
      {f.foldl (fun n g => n + g.blocks.size) 0} blocks, {lir.size} statements and terminators"
  return out

/-! ## Generated programs -/

/-- The generator's types as readback types: `Bool`, pairs and options are
inductives 0–2, with `IxCCTests.Support.LamGen`'s tags. -/
def genSig : Rt.Sig := { inds := [[[], []], [[.nat, .nat]], [[], [.nat]]] }

def genTy : Gen.Ty → Rt.FoTy
  | .nat => .nat
  | .bool => .ind 0
  | .pair => .ind 1
  | .opt => .ind 2

structure GenStats where
  programs : Nat := 0
  blocks : Nat := 0
  statements : Nat := 0
  /-- Runs on a small object area. -/
  small : Nat := 0
  /-- The slowest runs (milliseconds, seed, arguments). -/
  slow : List (Nat × Nat × List Nat) := []
  tally : Tally := {}

def generated (a : Assert) (count : Nat) : IO (Array String) := do
  let mut s : GenStats := {}
  for seed in [0:count] do
    let (A, ty) := Gen.ofSeedTy seed
    let label := s!"generated seed {seed}"
    let S ← IO.ofExcept ((lowerAll A).mapError (s!"{label}: " ++ ·))
    checkLir a S.lir label
    let mut t := s.tally
    let mut small := s.small
    -- arguments near 2^63 (natOverflow where a value leaves the words) on every tenth program
    let big := if seed % 10 == 0 then [[2 ^ 62], [2 ^ 63 - 1]] else []
    for xs in [[0], [1], [2], [3], [5]] ++ big do
      let r : Run := { label, cfg := S.levels.cfg, lir := S.lir, root := 0, args := xs, mem := S.mem
                       ty := some (genSig, genTy ty) }
      -- a small clock for the large arguments: their recursions run long and
      -- Cfg's exact products grow without bound
      let clock := if xs.any (· ≥ 2 ^ 62) then 400 else 100000
      let (t', ms) ← timed (compare a r clock t)
      t := t'
      s := { s with slow := ((ms, seed, xs) :: s.slow).mergeSort (fun x y => x.1 ≥ y.1) |>.take 3 }
      -- object areas just too small and just large enough
      if let .ok (_, H) ← runCfg .immortal S.levels.cfg clock 0 xs then
        let need := heapBytes H
        if need > 0 then
          for cap in [0, need - 8, need] do
            t ← compare a { r with mem := withLimit S.mem cap, capacity := cap } clock t
            small := small + 1
    let lir := S.lir.program
    s := { s with programs := s.programs + 1, tally := t, small
                  blocks := s.blocks + lir.funcs.foldl (fun n f => n + f.blocks.size) 0
                  statements := s.statements + lir.size }
  return #[s!"{s.programs} generated first-order programs: {s.blocks} Lir blocks, {s.statements} \
      statements and terminators; {s.small} runs on small object areas",
    s!"  {s.tally.render}", s!"  slowest runs (ms, seed, arguments): {s.slow}"]

end IxCCTests.Rt.Differential
