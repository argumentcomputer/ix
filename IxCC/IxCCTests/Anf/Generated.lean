import IxCCTests.Anf.Support
import IxCCTests.Support.LamGen
import IxCC.Anf.Pipeline

/-! Generated Lam programs through the middle end (design note 02 §13 items
5 and 6): every pass is run with **random oracles** (random shrink rounds,
random inline rounds including recursive and uncalled callees, random
specialisation decisions and masks, which the fixed-parameter checker may
reject), since correctness must hold for every certificate; after every step
the program is `WellScoped` and Lam and Anf agree (`compareRun`: readback,
traps, the timeout clause, tick dominance). A random step the replay's budgets
refuse (`Anf.Budget`: it can inline most globals into most callers, step after
step) is counted and skipped; any other refusal fails. The default pipeline also runs
on each program: its certificate replayed by `Pipeline.run` reproduces
`produce`'s program exactly, and shrink is idempotent at its fixpoint. -/

namespace IxCCTests.Anf.Generated

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Support
open IxCCTests.Support.RngM
abbrev Step := IxCC.Anf.Pipeline.Step

/-- A random certificate step for the current program. -/
def randomStep (P : AProgram) (inv : Nat) : RngM Step := do
  let ids := List.range P.size
  match ← weighted [3, 3, 2, 1] with
  | 0 => return .shrink (← ids.mapM fun _ => below 4)
  | 1 =>
    if ← chance 30 then return .inline (Anf.Inline.produce {} P)
    let r ← ids.filterMapM fun f => do
      if ← chance 60 then
        let cs ← ids.filterM fun _ => chance 40
        return some (f, cs)
      else return none
    return .inline r
  | 2 =>
    if ← chance 40 then
      -- the default oracle's decisions (the loop on its step function)
      return .specialize (Anf.Specialize.produce {} inv P)
    let n ← range 1 3
    let ds ← (List.range n).mapM fun _ => do
      let caller ← below P.size
      let callee ← below P.size
      let arity := (P.arity? callee).getD 0
      let mask ← (List.range arity).mapM fun _ => chance 50
      return ({ caller, callee, mask } : Anf.Specialize.Decision)
    return .specialize { inv, decisions := ds }
  | _ => return .prune

structure Stats where
  programs : Nat := 0
  steps : Nat := 0
  rejected : Nat := 0
  tally : Tally := {}
  specs : Nat := 0
  replays : Nat := 0
  /-- Random steps the middle end's budgets refused (`Anf.Budget`). -/
  overBudget : Nat := 0

def argsets : List (List Nat) := [[0], [1], [2], [3], [5]]

def clock : Nat := 3000

/-- Compare Lam and Anf on the root. -/
def compare (a : Assert) (L : LProgram) (A : AProgram) (label : String) (t : Tally) : IO Tally := do
  checkScoped a A label
  let mut t := t
  for xs in argsets do
    t ← compareRun a L A 0 xs clock label t
  return t

/-- One generated program: random certificates, then the default pipeline. -/
def one (a : Assert) (seed : Nat) (s : Stats) : IO Stats := do
  let L := LamGen.ofSeed seed
  unless Lam.wellFormed L && Lam.modesOk L do
    return { s with rejected := s.rejected + 1 }
  let mut s := { s with programs := s.programs + 1 }
  let P1 ← IO.ofExcept ((Anf.convert L).mapError (s!"seed {seed}: " ++ ·))
  s := { s with tally := ← compare a L P1 s!"seed {seed} P1" s.tally }
  -- random certificates
  let mut P := P1
  let mut g := Rng.ofSeed (UInt64.ofNat (seed * 7919 + 13))
  for i in [0:6] do
    let (step, g') := (randomStep P i).run g |>.run
    g := g'
    let before := P.size
    match step.run {} P with
    | .error m =>
      -- A random step can ask for more than the replay's budgets (it inlines
      -- 40% of the globals at 60% of the callers, step after step): refusing
      -- it is the budgets' job, as for any certificate, and the program stays
      -- as it was for the next step. Any other refusal fails the suite.
      unless (m.splitOn "budget").length > 1 do
        throw (IO.userError s!"seed {seed} step {i} ({step.name}): {m}")
      s := { s with overBudget := s.overBudget + 1 }
    | .ok P' =>
      P := P'
      if step matches .specialize _ then s := { s with specs := s.specs + (P.size - before) }
      s := { s with steps := s.steps + 1,
                    tally := ← compare a L P s!"seed {seed} step {i} {step.name}" s.tally }
  -- the default pipeline: replay and idempotence
  let tr ← IO.ofExcept ((Anf.Pipeline.produce {} L).mapError (s!"seed {seed} produce: " ++ ·))
  let final := (tr.stages.getLast?.map (·.2)).getD P1
  s := { s with tally := ← compare a L final s!"seed {seed} pipeline" s.tally }
  let replay ← IO.ofExcept (Anf.Pipeline.run tr.cert L)
  expect a (replay.beq final) s!"seed {seed}: replaying the certificate differs from produce"
  let (c, again, f) ← IO.ofExcept (Anf.Shrink.produce {} final)
  expect a (c.all (· == 0) && f.total == 0 && again.beq final)
    s!"seed {seed}: shrink is not idempotent at the pipeline's fixpoint ({f.render})"
  return { s with replays := s.replays + 1 }

def run (a : Assert) (count : Nat) : IO (Array String) := do
  let mut s : Stats := {}
  for seed in [0:count] do
    s ← one a seed s
  return #[s!"{s.programs} programs ({s.rejected} rejected by WellFormed/ModesOk), \
    {s.steps} random certificate steps ({s.specs} specialisations; {s.overBudget} more refused by \
    the budgets), {s.replays} replays",
    s!"  {s.tally.render}"]

end IxCCTests.Anf.Generated
