import IxCC.Xv.Alloc.Driver
import IxCC.Xv.Print
import IxCCTests.Xv.Support

/-!
# Shared helpers for the allocation tests

Running an allocated program at Xl beside its Xv original: outcomes
(values, heap and context words, or the failure) and the clock charges
each level spends, stepped by hand.
-/

namespace IxCCTests.Xv.Alloc

open IxCC IxCC.Lir IxCC.Xv IxCCTests.Lir IxCCTests.Xv

/-- Step Xl by hand: the outcome, steps taken and charges spent. -/
def countXl (p : LProgram) (env : Xl.Env) (fuel k : Nat) (s : Xl.State) : Outcome × Nat × Nat := Id.run do
  let mut s := s
  let mut k := k
  let mut steps := 0
  let mut charges := 0
  for _ in [:fuel] do
    steps := steps + 1
    match Xl.step p env s with
    | .next s' charge =>
        if charge then
          if k == 0 then return (.timeout, steps, charges)
          k := k - 1
          charges := charges + 1
        s := s'
    | .done v => return (.ok v, steps, charges)
    | .fail r => return (.resource r, steps, charges)
    | .trap => return (.trap, steps, charges)
    | .stuck => return (.stuck, steps, charges)
  return (.timeout, steps, charges)

/-- A runtime-procedure-like environment: odd functions declare a smaller
clobber set than every caller-saved register. -/
def smallClobbers : Xl.Env :=
  { clobbers := fun g => if g % 2 == 1 then [.rax, .rdx, .rcx, .rdi] else X86.SysV.callerSaved.toList }

/-- Compare Xv and Xl at clock 200 (full digest), at clocks `small` and 24
(values only), on the charges each spends, and at Xv's exact clock and one
below. Skips programs that are `stuck` at Xv (the validator's guarantee is
conditional on Xv not being stuck). Returns the steps each level took. -/
def differential (q : VProgram) (g : LProgram) (env : Xl.Env) (args : List Word) (seed : UInt64) :
    Except String (Nat × Nat) := do
  let mem := Region.initial seed
  let xvBig := digest (Xv.eval q 200 args mem Region.ctx)
  if xvBig == .stuck then return (0, 0)
  let xlBig := digest (Xl.eval g env 200 args mem Region.ctx)
  unless xvBig == xlBig do
    throw s!"at clock 200: Xv gives {xvBig.text}, Xl gives {xlBig.text}{if xvBig.light == xlBig.light then " (memory differs)" else ""}"
  for k in [(seed % 4).toNat, 24] do
    let a := light (Xv.eval q k args mem Region.ctx)
    let b := light (Xl.eval g env k args mem Region.ctx)
    unless a == b do throw s!"at clock {k}: Xv gives {a.text}, Xl gives {b.text}"
  let some xs := Xv.State.initial q args mem Region.ctx | throw "no initial Xv state"
  let some ls := Xl.State.initial g args mem Region.ctx | throw "no initial Xl state"
  let (_, xsteps, xcharges) := countRun q (Xv.fuelFor q 200 + 1) 200 xs
  let (lout, lsteps, lcharges) := countXl g env (Xl.fuelFor g 200 + 1) 200 ls
  unless xcharges == lcharges do throw s!"Xv spends {xcharges} charges, Xl {lcharges}"
  unless light lout == xlBig.light do throw s!"stepping Xl by hand gives {(light lout).text}"
  if xvBig != .timeout && xcharges > 0 then
    let atC := light (Xl.eval g env xcharges args mem Region.ctx)
    unless atC == xvBig.light do throw s!"Xl at the exact clock {xcharges} gives {atC.text}"
    let before := light (Xl.eval g env (xcharges - 1) args mem Region.ctx)
    unless before == .timeout do throw s!"Xl at clock {xcharges - 1} gives {before.text}, not timeout"
  return (xsteps, lsteps)

/-- Whether allocation `outs` of `q` runs like `q` (for mutants the validator
accepted): the differential at the default clocks, or `true` when either
level cannot even be built. -/
def equivalent (q : VProgram) (outs : List IxCC.Xv.Alloc.Output) (env : Xl.Env) (args : List Word)
    (seed : UInt64) : Bool :=
  match IxCC.Xv.Alloc.applyProgram q outs with
  | .error _ => true
  | .ok g => (differential q g env args seed).toBool

/-- Static edit counts of an allocation. -/
def countsOf (outs : List IxCC.Xv.Alloc.Output) : IxCC.Xv.Alloc.EditCounts :=
  outs.foldl (fun c o => c.add o.counts) {}

end IxCCTests.Xv.Alloc
