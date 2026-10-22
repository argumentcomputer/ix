module

public import Ix.Sharing.Exact.Uniform

@[expose] public section

/-! Component-family specification. The canonical entry fixes K16; offline
callers may supply other parameters and initial DAG/classification. This module
does not redefine valid wire/root inputs or impose a new input-size bound.
It claims neither a total semantic normalizer nor an operational/bit-cost
bound: payload size, output witnesses and optional execution budgets belong
to separate contracts. No budget selects a different family. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact

structure Config where
  experimentK : Nat
  deriving Repr, Inhabited

abbrev Cost := Array Nat → _root_.Int
abbrev Entry := _root_.Int × Array Nat

def sorted (xs : List Nat) : Array Nat :=
  (xs.mergeSort (fun a b => decide (a ≤ b))).toArray

def score (cost : Cost) (chosen : List Nat) (m : Nat) : Entry :=
  let set := sorted (m :: chosen)
  (cost set, set)

/-- Cache the incumbent's score: each remaining extension is evaluated once.
Equal costs use the existing set order, not an independent member-ID tie. -/
def pickTail (cost : Cost) (chosen : List Nat) : Nat × Entry → List Nat → Nat × Entry
  | best, [] => best
  | best, m :: rest =>
    let candidate := (m, score cost chosen m)
    pickTail cost chosen (if betterEntry candidate.2 (some best.2) then candidate else best) rest

def pick (cost : Cost) (chosen : List Nat) (m : Nat) (rest : List Nat) : Nat :=
  (pickTail cost chosen (m, score cost chosen m) rest).1

/-- Fuel is exactly the remaining member count; it is structural recursion,
not an execution budget and never chooses the fallback. -/
def greedyOrderAux (cost : Cost) : Nat → List Nat → List Nat → List Nat
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, chosen, m :: rest =>
    let next := pick cost chosen m rest
    next :: greedyOrderAux cost fuel (next :: chosen) ((m :: rest).erase next)

def greedyOrder (cost : Cost) (members : List Nat) : List Nat :=
  greedyOrderAux cost members.length [] members

def chainSet (cost : Cost) (members : List Nat) (k : Nat) : Array Nat :=
  sorted ((greedyOrder cost members).take k)

/-- Every count is retained, including expensive extensions and both ends. -/
def chain (cost : Cost) (members : List Nat) : List (Array Nat) :=
  let order := greedyOrder cost members
  (List.range (members.length + 1)).map fun k => sorted (order.take k)

/-- Declarative exact family; the executable fold below does not allocate
this exponential list. -/
def choices : List Nat → List Nat → List (Array Nat)
  | [], chosen => [sorted chosen]
  | m :: rest, chosen => choices rest chosen ++ choices rest (m :: chosen)

def family (cfg : Config) (cost : Cost) (members : List Nat) : List (Array Nat) :=
  if members.length ≤ cfg.experimentK then choices members [] else chain cost members

/-- Enumerate admitted subsets with a bounded live recursion path and table;
only the per-count winning rows survive, not every exact subset. -/
def foldChoices (visit : α → Array Nat → α) : List Nat → List Nat → α → α
  | [], chosen, acc => visit acc (sorted chosen)
  | m :: rest, chosen, acc =>
    foldChoices visit rest (m :: chosen) (foldChoices visit rest chosen acc)

def foldFamily (cfg : Config) (cost : Cost) (members : List Nat)
    (visit : α → Array Nat → α) (acc : α) : α :=
  if members.length ≤ cfg.experimentK then foldChoices visit members [] acc
  else (chain cost members).foldl visit acc

/-- Untrimmed best row at every family count; no slack theorem is assumed. -/
def table (cfg : Config) (cost : Cost) (members : List Nat) : CTable :=
  foldFamily cfg cost members (fun tb set => tb.add (cost set, set)) #[]

def componentContext (ex : Expanded) (stage : UStage) (members : Array Nat) : SCtx :=
  mkSCtx ex stage.f stage.up stage.cand stage.b0 stage.vis0 stage.rootCount stage.slack
    stage.theta stage.baseEv stage.widthCs stage.allTrue stage.unc members

/-- `phiE` is the specification; its proved evaluator twins preserve the
component delta. Reference timings are distinct from closure-local timings. -/
def componentDelta (cx : SCtx) (baseline : Nat) (set : Array Nat) : _root_.Int :=
  ((cx.phiE set.contains set).1 : _root_.Int) - (baseline : _root_.Int)

structure ComponentTrace where
  width : Nat
  index : Nat
  exact : Bool
  members : Array Nat
  areaSize : Nat
  closureSize : Nat
  rows : CTable
  /-- Calls of the mathematical subset-cost function, including row emission.
  This is neither a native instruction count nor a bit/space bound. -/
  evaluations : Nat

def component (cfg : Config) (ex : Expanded) (stage : UStage)
    (width index : Nat) (members : Array Nat) : ComponentTrace :=
  let cx := componentContext ex stage members
  let baseline := (cx.phiE (fun _ => false) #[]).1
  let cost := componentDelta cx baseline
  let m := members.size
  let exact := m ≤ cfg.experimentK
  { width, index, exact, members, areaSize := cx.area.size, closureSize := cx.closure.size,
    rows := table cfg cost members.toList,
    evaluations := if exact then 2 ^ m else m * (m + 1) / 2 + m + 1 }

/-- Classification and component indices are fixed before any family walk. -/
def components (cfg : Config) (ex : Expanded) (width : Nat) : Array ComponentTrace :=
  let stage := uniformStage width ex (Prep.ofDag ex.dag)
  stage.comps.mapIdx fun i members => component cfg ex stage width i members

def ids (xs : Array Nat) : String := String.intercalate "," (xs.toList.map toString)

/-- TSV v1 shared with the Rust experiment. The address is a caller label.
Statistics are outside the encoding/compatibility contract. -/
def ComponentTrace.tsv (t : ComponentTrace) (address : String) : String := Id.run do
  let mode := if t.exact then "exact" else "greedy"
  let stem := s!"{address}\t{t.width}\t{t.index}\t{mode}"
  let mut out := #[s!"component\t{stem}\t{ids t.members}\t{t.areaSize}\t{t.closureSize}"]
  for (row, k) in t.rows.zipIdx do
    if let some (delta, selected) := row then
      out := out.push s!"row\t{stem}\t{k}\t{delta}\t{ids selected}"
  out := out.push s!"work\t{stem}\t{t.evaluations}"
  return String.intercalate "\n" out.toList

end Ix.Sharing.FamilyPrototype
