module

public import Ix.Sharing.FamilyContext
import all Ix.Sharing.Family
import all Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.UniformSearchLocal

/-! Isolated scratch-buffer evaluator. No production import or compiler
replacement selects this module. Results must be checked against the ordinary
area evaluator and complete family tables before measuring it. -/

public section

namespace Ix.Sharing.Scratch

open Ix.Sharing.Exact Ix.Sharing.Family

/-- Storage survives a cost evaluation; only the written prefix is observable. -/
structure Rows where
  cost : Array Nat := #[]
  inl : Array Nat := #[]
  sides : Array Nat := #[]
  below : Array Nat := #[]
  deriving Inhabited

private def grow (needed : Nat) (values : Array Nat) : Array Nat :=
  if needed ≤ values.size then values
  else values ++ Array.replicate (needed - values.size) 0

def Rows.ensure (needed : Nat) (rows : Rows) : Rows :=
  let ⟨cost, inl, sides, below⟩ := rows
  ⟨grow needed cost, grow needed inl, grow needed sides, grow needed below⟩

/-- Stale or future slots never replace a base-table value. -/
@[inline] def readPrefix (positions values base : Array Nat) (written term : Nat) : Nat :=
  let position := positions[term]!
  if position != 0 && position - 1 < written && position - 1 < values.size then
    values[position - 1]!
  else base[term]!

theorem readPrefix_eq (positions values base : Array Nat) (written term : Nat)
    (capacity : written ≤ values.size) :
    readPrefix positions values base written term =
      rdA positions (values.extract 0 written) base term := by
  unfold readPrefix rdA
  rw [Array.size_extract_of_le capacity]
  simp only [Nat.sub_zero]
  by_cases before : positions[term]! - 1 < written
  · have present : positions[term]! - 1 < values.size := by omega
    have extracted : positions[term]! - 1 < (values.extract 0 written).size := by
      rw [Array.size_extract_of_le capacity]
      omega
    have same : (values.extract 0 written)[positions[term]! - 1]! =
        values[positions[term]! - 1]! := by
      rw [getElem!_pos (values.extract 0 written) (positions[term]! - 1) extracted,
        getElem!_pos values (positions[term]! - 1) present]
      simp
    simp [before, present, same]
  · simp [before]

def fill (prep : Prep) (opaqueFlags : Array Bool) (base : TBase) (width : Nat)
    (area positions : Array Nat) (available : Array Bool) : Nat → Nat → Rows → Rows
  | 0, _, rows => rows
  | fuel + 1, written, ⟨cost, inl, sides, below⟩ =>
    let (c, i, s, b) := tRow prep opaqueFlags base.tLen base.tTail width
      (avA positions available) (readPrefix positions cost base.cost written)
      (readPrefix positions sides base.sides written)
      (readPrefix positions below base.below written) area[written]!
    fill prep opaqueFlags base width area positions available fuel (written + 1)
      ⟨cost.set! written c, inl.set! written i, sides.set! written s, below.set! written b⟩

def evaluateRows (prep : Prep) (opaqueFlags : Array Bool) (base : TBase) (width : Nat)
    (area positions : Array Nat) (available : Array Bool) (rows : Rows) : Rows :=
  fill prep opaqueFlags base width area positions available area.size 0
    (rows.ensure area.size)

/-- A diagnostic projection, excluded from timing loops because extracting
tables can retain their arrays and defeat unique ownership on the next call. -/
def Rows.prefix (rows : Rows) (count : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat :=
  (rows.cost.extract 0 count, rows.inl.extract 0 count,
    rows.sides.extract 0 count, rows.below.extract 0 count)

/-- Keep the original availability construction and opacity fallback while
isolating reuse of the four value buffers. -/
def phi (context : SCtx) (positions : Array Nat) (base : TBase) (aux : AAux)
    (fallback : Unit → SCtx × Array Nat) (available : Nat → Bool) (stored : Array Nat)
    (scratch : Rows) : (Nat × Nat) × Rows :=
  let rows := evaluateRows context.up.prep context.up.opaq base context.up.w
    context.area positions (memberFlags context positions available) scratch
  let written := context.area.size
  let getCost := readPrefix positions rows.cost base.cost written
  let getInline := readPrefix positions rows.inl base.inl written
  let getSides := readPrefix positions rows.sides base.sides written
  let value :=
    if aux.storedA.all (tGuard context.up.prep base.tTail context.up.w
        getCost getInline getSides) then
      let roots := aux.rootsA.foldl (fun total root => total + getCost root) 0
      let opaqueEntries := aux.storedA.foldl (fun total term => total + getInline term) 0
      let entries := stored.foldl (fun total term => total + getInline term) 0
      (aux.K + roots + opaqueEntries + entries, aux.csize + stored.size)
    else
      let (full, closurePositions) := fallback ()
      phiEL2 full positions closurePositions available stored
  (value, rows)

abbrev CostWithState (σ : Type) := Array Nat → σ → _root_.Int × σ

def scoreWithState (cost : CostWithState σ) (chosen : List Nat) (member : Nat)
    (state : σ) : Entry × σ :=
  let selected := sorted (member :: chosen)
  let (value, state) := cost selected state
  ((value, selected), state)

def pickTailWithState (cost : CostWithState σ) (chosen : List Nat) :
    Nat × Entry → List Nat → σ → (Nat × Entry) × σ
  | best, [], state => (best, state)
  | best, member :: rest, state =>
    let (entry, state) := scoreWithState cost chosen member state
    let candidate := (member, entry)
    let best := if betterEntry candidate.2 (some best.2) then candidate else best
    pickTailWithState cost chosen best rest state

def greedyOrderWithState (cost : CostWithState σ) :
    Nat → List Nat → List Nat → σ → List Nat × σ
  | 0, _, _, state => ([], state)
  | _ + 1, _, [], state => ([], state)
  | fuel + 1, chosen, member :: rest, state =>
    let (first, state) := scoreWithState cost chosen member state
    let ((next, _), state) := pickTailWithState cost chosen (member, first) rest state
    let (tail, state) := greedyOrderWithState cost fuel (next :: chosen)
      ((member :: rest).erase next) state
    (next :: tail, state)

def foldChoicesWithState (cost : CostWithState σ) :
    List Nat → List Nat → CTable → σ → CTable × σ
  | [], chosen, table, state =>
    let selected := sorted chosen
    let (value, state) := cost selected state
    (table.add (value, selected), state)
  | member :: rest, chosen, table, state =>
    let (table, state) := foldChoicesWithState cost rest chosen table state
    foldChoicesWithState cost rest (member :: chosen) table state

def tableWithState (config : Config) (cost : CostWithState σ) (members : List Nat)
    (state : σ) : CTable × σ :=
  if members.length ≤ config.exactLimit then
    foldChoicesWithState cost members [] #[] state
  else
    let (order, state) := greedyOrderWithState cost members.length [] members state
    (List.range (members.length + 1)).foldl (fun (table, state) count =>
      let selected := sorted (order.take count)
      let (value, state) := cost selected state
      (table.add (value, selected), state)) (#[], state)

/-- The same baseline and candidate recipe as the existing light-context
trace. Scratch is an explicit linear argument, never captured by the cost
closure or retained in a table row. The greedy path deliberately retains the
reference's extra row evaluations to isolate buffer reuse. -/
def trace (config : Config) (context : SCtx) (positions : Array Nat) (base : TBase)
    (aux : AAux) (fallback : Unit → SCtx × Array Nat) (width index : Nat)
    (members : Array Nat) (reuse : Bool) (scratch : Rows) : ComponentTrace × Rows :=
  let (baseline, scratch) := phi context positions base aux fallback (fun _ => false) #[]
    (if reuse then scratch else {})
  let cost : CostWithState Rows := fun selected state =>
    let (value, state) := phi context positions base aux fallback selected.contains selected
      (if reuse then state else {})
    ((value.1 : _root_.Int) - (baseline.1 : _root_.Int), state)
  let (rows, scratch) := tableWithState config cost members.toList scratch
  let count := members.size
  ({ width, index, exact := count ≤ config.exactLimit, members,
      areaSize := context.area.size, closureSize := aux.csize, rows,
      evaluations := if count ≤ config.exactLimit then 2 ^ count
        else count * (count + 1) / 2 + count + 1 }, scratch)

abbrev StageState := FamilyState × Rows

/-- The original checked light-context step with explicit scratch ownership.
Fallbacks retain the original implementation and the incoming scratch. -/
def step (reuse : Bool) (config : Config) (limits : Limits) (expanded : Expanded)
    (stage : UStage) (width : Nat) (parents : Array (Array Nat)) (base : TBase)
    (accumulator : StageState) (members : Array Nat) : Except SharingError StageState := do
  let (core, scratch) := accumulator
  let ((results, states, work), areaPositions, closurePositions) := core
  let nextStates ← bump states (familyCalls config members.size) limits.maxStates .states
  if members.all (fun m => decide (m < expanded.dag.size) && !stage.up.opaq[m]!) then
    let area := componentArea stage.up stage.f members
    let areaPositions := setPositions areaPositions area
    if areaOK expanded.dag.size stage.up.opaq parents members area areaPositions then
      let (marks, found, stack) := upWalk parents members closurePositions
      if stack.isEmpty && area.all (fun y => marks[y]! != 0) then
        let light := LightContext.context stage members area
        if localSearchOK light then
          let nextWork ← bump work (familyWork config members.size found.size)
            limits.maxCostEvals .costEvals
          let aux := LightContext.auxiliary expanded stage base area areaPositions found marks
          let closurePositions := clearPositions marks found
          let cached := Thunk.mk fun _ => LightContext.fullContext expanded stage members
          let (trace, scratch) := trace config light areaPositions base aux
            (LightContext.forceContext cached) width results.size members reuse scratch
          let result ← retainedResult stage.slack trace
          return (((results.push result, nextStates, nextWork),
            clearPositions areaPositions area, closurePositions), scratch)
        else
          let core ← familyStepArea config limits expanded stage width parents base
            ((results, states, work), clearPositions areaPositions area,
              clearPositions marks found) members
          return (core, scratch)
      else
        let core ← familyStepArea config limits expanded stage width parents base
          ((results, states, work), clearPositions areaPositions area,
            clearPositions marks found) members
        return (core, scratch)
    else
      let core ← familyStepArea config limits expanded stage width parents base
        ((results, states, work), clearPositions areaPositions area, closurePositions) members
      return (core, scratch)
  else
    let core ← familyStepArea config limits expanded stage width parents base
      ((results, states, work), areaPositions, closurePositions) members
    return (core, scratch)

/-- Buffers survive components within a width and are dropped before its
observable result is returned. The common stage-preparation path is unchanged. -/
def components (reuse : Bool) (config : Config) (limits : Limits) (expanded : Expanded)
    (stage : UStage) (width : Nat) (parents : Array (Array Nat)) :
    Except SharingError MeterState :=
  let base := TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq
  if tStageOK stage.up.prep stage.up.w stage.up.opaq base then
    (stage.comps.foldlM (step reuse config limits expanded stage width parents base)
      (((#[], 0, 0), Array.replicate stage.up.prep.dag.size 0,
        Array.replicate expanded.dag.size 0), {})).map (fun (core, _) => core.1)
  else familyComponents config limits expanded stage width parents

end Ix.Sharing.Scratch
