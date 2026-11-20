import IxAICore.Rng

/-!
# Benchmark statistics in integer arithmetic

Every statistic is an integer in fixed units (basis points `1/10^4` for rates, `1/256` for
probabilities), so a report is bit-identical across runs and machines. Bootstrap resamples are
drawn from `IxAICore.Rng` with a fixed seed.
-/

namespace IxAIBench

open IxAICore

/-- A rate in basis points; `0` for an empty denominator. -/
def bp (num den : Nat) : Nat := if den == 0 then 0 else num * 10000 / den

/-- Basis points as a percentage with one decimal, rounded down. -/
def showPct (b : Nat) : String := s!"{b / 100}.{(b % 100) / 10}%"

/-- A signed basis-point gap as a percentage-point difference with one decimal, rounded toward
zero. -/
def showGap (g : Int) : String :=
  let a := g.natAbs
  (if g < 0 then "-" else "+") ++ s!"{a / 100}.{(a % 100) / 10}"

def pad (w : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- A value in units of `1/10^6` with three decimals, rounded down. -/
def showMicro3 (m : Nat) : String := s!"{m / 1000000}.{pad 3 (m % 1000000 / 1000)}"

/-- A signed value in units of `1/10^6` with three decimals, rounded toward zero. -/
def showMicroGap (g : Int) : String := (if g < 0 then "-" else "+") ++ showMicro3 g.natAbs

/-- A value in units of `1/1000` with three decimals. -/
def showMilli (m : Nat) : String := s!"{m / 1000}.{pad 3 (m % 1000)}"

/-! ## Bootstrap -/

structure BootConfig where
  seed : Nat := 20261118
  resamples : Nat := 1000

/-- `B` resamples of `n` indices with replacement, drawn in order from one stream. -/
def resamples (bc : BootConfig) (n : Nat) : Array (Array Nat) := Id.run do
  let mut r := Rng.seeded bc.seed
  let mut out := #[]
  if n == 0 then return out
  for _ in [:bc.resamples] do
    let mut idx := Array.mkEmpty n
    for _ in [:n] do
      let (i, r') := r.below n
      r := r'
      idx := idx.push i
    out := out.push idx
  return out

/-- The 2.5th and 97.5th percentiles of a list of statistics. -/
def percentileCI (vals : Array Int) : Int × Int :=
  if vals.isEmpty then (0, 0) else
  let s := vals.qsort (· < ·)
  let lo := s.size * 25 / 1000
  let hi := min (s.size - 1) (s.size * 975 / 1000 - 1)
  (s[lo]!, s[hi]!)

/-- A statistic of a resampled set of rows, computed from the index array. -/
abbrev Statistic := Array Nat → Int

/-- The 95% percentile-bootstrap interval of `stat` over the resamples. -/
def bootCI (rs : Array (Array Nat)) (stat : Statistic) : Int × Int :=
  percentileCI (rs.map stat)

/-- The 95% interval of the paired difference `a − b`, both computed on each resample. -/
def pairedCI (rs : Array (Array Nat)) (a b : Statistic) : Int × Int :=
  percentileCI (rs.map fun idx => a idx - b idx)

/-! ## Classification -/

/-- One classified example: true class, predicted class (`none` for an invalid answer), and the
stated probability of the prediction in units of `1/256`. -/
structure Pred where
  target : Nat
  pred : Option Nat
  conf : Int
  deriving Repr, Inhabited

def Pred.correct (p : Pred) : Bool := p.pred == some p.target

def countIf {α : Type} (xs : Array α) (f : α → Bool) : Nat := xs.foldl (fun n x => if f x then n + 1 else n) 0

def accuracyBp (ps : Array Pred) : Nat := bp (countIf ps (·.correct)) ps.size

/-- Classes present among the targets or the predictions, in order. -/
def classesOf (arity : Nat) (ps : Array Pred) : List Nat :=
  (List.range arity).filter fun k => ps.any fun p => p.target == k || p.pred == some k

/-- Macro-averaged F1 over the classes present among targets or predictions, in basis points. -/
def macroF1Bp (arity : Nat) (ps : Array Pred) : Nat :=
  let cls := classesOf arity ps
  if cls.isEmpty then 0 else
  let f1s := cls.map fun k =>
    let tp := countIf ps fun p => p.target == k && p.pred == some k
    let fp := countIf ps fun p => p.target != k && p.pred == some k
    let fn := countIf ps fun p => p.target == k && p.pred != some k
    bp (2 * tp) (2 * tp + fp + fn)
  f1s.foldl (· + ·) 0 / cls.length

/-- Mean recall over the classes present among the targets, in basis points. -/
def balancedAccBp (arity : Nat) (ps : Array Pred) : Nat :=
  let cls := (List.range arity).filter fun k => ps.any (·.target == k)
  if cls.isEmpty then 0 else
  let rs := cls.map fun k =>
    bp (countIf ps fun p => p.target == k && p.pred == some k) (countIf ps (·.target == k))
  rs.foldl (· + ·) 0 / cls.length

/-- The most frequent class of a list of labels; the smallest on ties. -/
def majority (arity : Nat) (labels : List Nat) : Nat :=
  (List.range arity).foldl (fun best k =>
    if labels.count k > labels.count best then k else best) 0

/-- Expected calibration error over 10 equal-width confidence bins, in units of `1/1000`:
`Σ_bins |Σ conf − 256 · correct| / (256 · n)`. Invalid answers are excluded. -/
def eceMilli (ps : Array Pred) : Nat :=
  let vs := ps.filter (·.pred.isSome)
  if vs.isEmpty then 0 else
  let binOf := fun (c : Int) => min 9 (c.toNat * 10 / 256)
  let gaps := (List.range 10).map fun b =>
    let inBin := vs.filter (binOf ·.conf == b)
    let confSum := inBin.foldl (fun s p => s + p.conf) 0
    let hits : Int := countIf inBin (·.correct)
    (confSum - 256 * hits).natAbs
  (gaps.foldl (· + ·) 0) * 1000 / (256 * vs.size)

/-- Accuracy on the most confident `cov`% of the examples (by stated probability, ties in input
order), in basis points. -/
def accuracyAtCoverage (ps : Array Pred) (cov : Nat) : Nat × Nat :=
  let ranked := (ps.zipIdx.qsort fun (a, i) (b, j) => a.conf > b.conf || (a.conf == b.conf && i < j)).map (·.1)
  let k := (ps.size * cov + 99) / 100
  (accuracyBp (ranked.extract 0 k), k)

def pick {α : Type} [Inhabited α] (xs : Array α) (idx : Array Nat) : Array α := idx.map (xs[·]!)

end IxAIBench
