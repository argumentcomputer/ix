import Aiur.Optimized.Grouping.Packets

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

/-- Select the smallest-degree form while keeping the original expression
order. In particular `(1 - branch) * x` can become `(member - branch) * x`
when `branch` is private, avoiding a cubic lookup and its lifted column.
The row and packet certificates check the resulting expressions. -/
def selectArgument (selector : Nat) (privateCols : List Nat) (p : Polynomial F) : Polynomial F :=
  let direct := (gate selector privateCols p).simplify
  let better := fun a b : Polynomial F => if a.degree < b.degree then a else b
  if direct.degree ≤ 1 || silent privateCols p then direct else match p with
  | .add a b => better (Polynomial.simplify (.add (selectArgument selector privateCols a)
      (selectArgument selector privateCols b))) direct
  | .sub a b => better (Polynomial.simplify (.sub (selectArgument selector privateCols a)
      (selectArgument selector privateCols b))) direct
  | .mul a b =>
      let left := Polynomial.simplify (.mul (selectArgument selector privateCols a) b)
      let right := Polynomial.simplify (.mul a (selectArgument selector privateCols b))
      better left (better right direct)
  | _ => direct

def privateColumns (source : Chip F) (selector : Nat)
    (lookupArgs : List (Polynomial F) := []) : Except String (List Nat) := do
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
  -- One additional private factor can silence many quadratic arguments.
  -- Keep only steps that remove at least one distinct materialization: the
  -- private-plus-lifted width cannot increase, and the shared width can shrink.
  let mut pending := (lookupArgs.filter fun p => (selectArgument selector columns p).degree > 2).dedup
  for _ in List.range source.numVars do
    let candidates := (pending.flatMap Polynomial.vars).dedup.filter fun v => !columns.contains v
    let best := candidates.foldl (fun (best : Nat × Nat) v =>
      let score := pending.countP fun p => (selectArgument selector (v :: columns) p).degree ≤ 2
      if score > best.2 then (v, score) else best) (selector, 0)
    if best.2 == 0 then break
    let next := best.1 :: columns
    let remaining := pending.filter fun p => (selectArgument selector next p).degree > 2
    if remaining.length ≥ pending.length then break
    columns := next
    pending := remaining
  unless required.all (silent columns) do throw s!"cannot silence group member {source.name}"
  unless columns.all (· < source.numVars) do throw "group private column out of bounds"
  return columns.mergeSort (· ≤ ·)

/-- Members retain their call identities, even when several typed functions
already share one physical chip. Activate each source before choosing columns. -/
def candidate (name : String) (id : String → Except String Nat)
    (sources : List (Chip F)) (optimizeLookups : Bool := true) : Except String (Layout F) := do
  unless sources.length ≥ 2 do throw "a function group needs at least two members"
  let selected ← sources.mapM fun origin => do
    let chip := Activation.compile origin
    let (provided, required) ← messages id chip
    let args := if optimizeLookups then provided ++ required.flatMap (·.args) else []
    return (origin, ← privateColumns chip origin.numVars args)
  let shared := selected.foldl (fun n (origin, privateCols) =>
    max n (origin.numVars + 1 - privateCols.length)) 0
  let mut next := shared
  let mut members : List (Member F) := []
  let mut receive : List (Polynomial F) := []
  let mut sends : List (Lookup F) := []
  for (origin, privateCols) in selected do
    let chip := Activation.compile origin
    let selector := origin.numVars
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
        let selected := if optimizeLookups then selectArgument selector privateCols p
          else (gate selector privateCols p).simplify
        let value ← if selected.degree ≤ 2 then
          pure (rename selected).simplify
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
    members := members ++ [⟨chip.name, columns, root, writes, origin, privateCols⟩]
  let layout := Layout.mk name next members receive sends
  unless layout.constraints.all (fun p => p.degree ≤ 3 && p.inBounds next) do
    throw s!"group {name} exceeds degree or column budget"
  unless (receive ++ sends.flatMap (·.args)).all (fun p => p.degree ≤ 2 && p.inBounds next) &&
      sends.all (fun s => s.enable.degree ≤ 2 && s.enable.inBounds next) do
    throw s!"group {name} has invalid lookup expressions"
  return layout

/-- The compiler returns a proof-bearing result; uncertified layouts cannot
reach the exporter. Column selection remains an untrusted heuristic. -/
def compile (name : String) (id : String → Except String Nat) (sources : List (Chip F))
    (optimizeLookups : Bool := true) :
    Except String (Checked sources id) := do
  certify sources id (← candidate name id sources optimizeLookups)

end Aiur.Optimized.Grouping
