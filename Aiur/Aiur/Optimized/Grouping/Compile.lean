import Aiur.Optimized.Grouping

namespace Aiur.Optimized.Grouping
open Circuit

variable {F : Type} [Field F] [DecidableEq F]

/-- Zero-coefficient terms are discarded. The remaining supports deliberately
ignore cancellation: this heuristic only chooses columns; `silent` checks it. -/
private def supports : Polynomial F → List (List Nat)
  | .const x => if x = 0 then [] else [[]]
  | .var v => [[v]]
  | .add a b | .sub a b => supports a ++ supports b
  | .mul a b => (supports a).flatMap fun x => (supports b).map fun y => (x ++ y).dedup

def privateColumns (source : Chip F) (selector : Nat) : Except String (List Nat) := do
  let quiet := source.sends.map (·.enable) ++ source.memory.map (·.enable)
  let required := source.constraints.filter (·.degree > 2) ++ quiet
  let mut columns := [selector]
  let mut terms := (required.flatMap supports).filter fun xs => !xs.contains selector
  for _ in List.range source.numVars do
    if terms.isEmpty then break
    let candidates := terms.flatten.dedup
    let best := candidates.foldl (fun (best : Nat × Nat) v =>
      let score := terms.countP (·.contains v)
      if score > best.2 then (v, score) else best) (selector, 0)
    if best.2 == 0 then break
    columns := best.1 :: columns
    terms := terms.filter fun xs => !xs.contains best.1
  -- Cancellation can leave an empty support. A conservative fallback is still
  -- cheap for such uncommon chips, and the result is checked independently.
  for p in required do
    unless silent columns p do columns := (columns ++ Polynomial.vars p).dedup
  unless required.all (silent columns) do throw s!"cannot silence group member {source.name}"
  unless columns.all (· < source.numVars) do throw "group private column out of bounds"
  return columns.mergeSort (· ≤ ·)

structure Lookup (F : Type) where
  enable : Polynomial F
  args : List (Polynomial F)

structure Member (F : Type) where
  name : String
  columns : Array Nat
  selector : Nat
  /-- Private message arguments of degree two, populated after the source row. -/
  writes : List (Nat × Polynomial F) := []
  source : Chip F
  sourceSelector : Nat
  privateCols : List Nat

structure Layout (F : Type) where
  name : String
  width : Nat
  members : List (Member F)
  activation : Polynomial F
  receive : List (Polynomial F)
  sends : List (Lookup F)

def rename (columns : Array Nat) (p : Polynomial F) : Polynomial F :=
  p.subst (fun v => .var (columns[v]?.getD 0))

omit [DecidableEq F] in
@[simp] theorem rename_denote (columns : Array Nat) (p : Polynomial F) (a : Nat → F) :
    (rename columns p).denote a = p.denote (fun v => a (columns[v]?.getD 0)) := by
  simp [rename, Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote]

private def plus (a b : Polynomial F) : Polynomial F := Polynomial.simplify (.add a b)
private def sum (ps : List (Polynomial F)) : Polynomial F := ps.foldl plus (.const 0)

def Member.constraints (m : Member F) : List (Polynomial F) :=
  (member m.source m.sourceSelector m.privateCols).constraints.map (rename m.columns) ++
    m.writes.flatMap fun (column, value) =>
      [.mul (.var m.selector) (.sub (.var column) value), privateZero m.selector column]

def Layout.constraints (g : Layout F) : List (Polynomial F) :=
  let selectors : List (Polynomial F) := g.members.map (fun m => Polynomial.var m.selector)
  let exclusion := (List.range selectors.length).map fun i =>
    Polynomial.mul (selectors[i]?.getD (.const 0)) (sum (selectors.drop (i+1)))
  ((g.members.flatMap Member.constraints ++ exclusion).map Polynomial.simplify).filter (· != .const 0)

/-- Projection from the actual emitted constraints, not a parallel circuit
model. Renaming shares data columns, but the selected member satisfies exactly
the original constraint list. Memory membership is recovered from its selected
lookup messages, just as for an ungrouped physical chip. -/
theorem Layout.member_constraints (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a) :
    Satisfies (member m.source m.sourceSelector m.privateCols).constraints
      (fun v => a (m.columns[v]?.getD 0)) := by
  intro p hp
  have included : rename m.columns p ∈ g.members.flatMap Member.constraints := by
    apply List.mem_flatMap.mpr
    refine ⟨m, present, List.mem_append_left _ ?_⟩
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  by_cases zero : (rename m.columns p).simplify = .const 0
  · have h := congrArg (fun p : Polynomial F => p.denote a) zero
    simpa only [Polynomial.denote_simplify, rename_denote, Scalar.Circuit.ArithExpr.denote] using h
  · have h := valid ((rename m.columns p).simplify) (by
      unfold Layout.constraints
      apply List.mem_filter.mpr
      constructor
      · exact List.mem_map.mpr ⟨_, List.mem_append_left _ included, rfl⟩
      · change (!((rename m.columns p).simplify == .const 0)) = true
        cases h : ((rename m.columns p).simplify == .const 0) with
        | false => rfl
        | true => exact (zero ((Polynomial.beq_eq _ _).mp h)).elim)
    simpa only [Polynomial.denote_simplify, rename_denote] using h

theorem Layout.selected_member_sound (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a)
    (active : a (m.columns[m.sourceSelector]?.getD 0) = 1)
    (memory : ∀ lookup ∈ m.source.memory,
      lookup.Valid rom (fun v => a (m.columns[v]?.getD 0))) :
    m.source.ValidAssignment rom (fun v => a (m.columns[v]?.getD 0)) := by
  exact (member_active m.source m.sourceSelector m.privateCols
    (fun v => a (m.columns[v]?.getD 0)) active).mp ⟨g.member_constraints m present a valid, memory⟩
private def plusArgs (xs ys : List (Polynomial F)) : List (Polynomial F) :=
  (List.range (max xs.length ys.length)).map fun i =>
    plus (xs[i]?.getD (.const 0)) (ys[i]?.getD (.const 0))

private def messages (id : String → Except String Nat) (source : Chip F) :
    Except String (List (Polynomial F) × List (Lookup F)) := do
  let call ← id source.name
  let receive := [.const 1, .const call] ++
    (source.inputs.flatMap WireValue.words).map .var ++ source.output.words
  let sends ← source.sends.mapM fun s => do
    let callee ← id s.channel
    return Lookup.mk s.enable ([.const 1, .const callee] ++
      s.args.flatMap WireValue.words ++ s.result.words.map .var)
  let memory := source.memory.map fun m =>
    Lookup.mk m.enable ([.const 2, .const m.value.words.length, m.address] ++ m.value.words)
  return (receive, sends ++ memory)

/-- Members retain their call identities, even when several typed functions
already share one physical chip. Source chips have already been activated. -/
def compile (name : String) (id : String → Except String Nat)
    (sources : List (Chip F × Nat)) : Except String (Layout F) := do
  unless sources.length ≥ 2 do throw "a function group needs at least two members"
  let selected ← sources.mapM fun (chip, selector) => do
    return (chip, selector, ← privateColumns chip selector)
  let shared := selected.foldl (fun n (chip, _, privateCols) =>
    max n (chip.numVars - privateCols.length)) 0
  let mut next := shared
  let mut members : List (Member F) := []
  let mut receive : List (Polynomial F) := []
  let mut sends : List (Lookup F) := []
  for (chip, selector, privateCols) in selected do
    let sharedCols := (List.range chip.numVars).filter fun v => !privateCols.contains v
    let columns := (List.range chip.numVars).map fun v =>
      if privateCols.contains v then next + privateCols.idxOf v else sharedCols.idxOf v
    next := next + privateCols.length
    let columns := columns.toArray
    let root := columns[selector]?.getD 0
    let rename := rename columns
    let (provided, required) ← messages id chip
    let mut writes : List (Nat × Polynomial F) := []
    let mut transformed : List (List (Polynomial F)) := []
    for args in provided :: required.map (·.args) do
      let mut out := []
      for p in args do
        unless p.degree ≤ 2 do throw s!"lookup degree exceeds two in {chip.name}"
        let value ← if silent privateCols p || p.degree ≤ 1 then
          pure (rename (gate selector privateCols p)).simplify
        else do
          let p := rename p
          if let some (column, _) := writes.find? (fun (_, value) => value == p) then
            pure (.var column)
          else
            let column := next
            next := next + 1
            writes := writes ++ [(column, p)]
            pure (.var column)
        out := out ++ [value]
      transformed := transformed ++ [out]
    receive := plusArgs receive (transformed.headD [])
    let required := required.zip (transformed.drop 1) |>.map fun (lookup, args) =>
      Lookup.mk (rename lookup.enable) args
    sends := (List.range (max sends.length required.length)).map fun i =>
      let a := sends[i]?.getD ⟨.const 0, []⟩
      let b := required[i]?.getD ⟨.const 0, []⟩
      ⟨plus a.enable b.enable, plusArgs a.args b.args⟩
    members := members ++ [⟨chip.name, columns, root, writes, chip, selector, privateCols⟩]
  let selectors := members.map (fun m => Polynomial.var m.selector)
  let layout := Layout.mk name next members (sum selectors) receive sends
  unless layout.constraints.all (fun p => p.degree ≤ 3 && p.inBounds next) do
    throw s!"group {name} exceeds degree or column budget"
  unless (receive ++ sends.flatMap (·.args)).all (fun p => p.degree ≤ 2 && p.inBounds next) &&
      sends.all (fun s => s.enable.degree ≤ 2 && s.enable.inBounds next) do
    throw s!"group {name} has invalid lookup expressions"
  return layout

end Aiur.Optimized.Grouping
