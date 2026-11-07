import Lean.Data.Json
import Std.Data.HashMap

/-!
# Grouping policy search

Suggest a function-grouping policy from `grouping_tune --metrics` layout
metrics and recorded row counts. This is an untrusted search heuristic, not an
artifact compiler: feed its policy to `grouping_tune --policy` (or the
application exporter) to obtain checked layouts. Every workload's estimated
cells and FFT work must stay within the starting policy's budget; column count
is a smaller secondary objective.

```sh
grouping_search METRICS OUTPUT --prefix P --profile COUNTS SHAPES [--profile ...]
  [--max-members N] [--sweeps N] [--report-only]
```

`COUNTS` holds `function_rows` and `SHAPES` the singleton circuit shapes, both
from the `stark-verifier` `compare` example (`--counts-only`, `--ungrouped`).
`OUTPUT` receives the policy and `OUTPUT` with extension `report.json` the
search report. This is a port of the former `tools/ixvm/tune-groups.py` and
makes the same moves in the same order.
-/

open Lean

namespace GroupingSearch

/-- One function chip's layout metrics. -/
structure Chip where
  name : String
  privateColumns : Nat
  lifted : Nat
  shared : Nat
  lookups : Array (Nat × Nat)
  constraintDegree : Nat
  deriving Inhabited

instance : FromJson Chip where
  fromJson? j := do
    let lookups : Array (Array Nat) ← j.getObjValAs? (Array (Array Nat)) "lookups"
    return {
      name := ← j.getObjValAs? String "name"
      privateColumns := ← j.getObjValAs? Nat "private"
      lifted := ← j.getObjValAs? Nat "lifted"
      shared := ← j.getObjValAs? Nat "shared"
      lookups := lookups.map fun p => (p[0]!, p[1]!)
      constraintDegree := ← j.getObjValAs? Nat "constraint_degree" }

/-- A measured singleton circuit: stage-one width, stage-two width, quotient
degree. -/
abbrev Shape := Nat × Nat × Nat

/-- Python's `int.bit_length`. -/
def bitLength (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- The padded trace height for `n` rows. -/
def padded (n : Nat) : Nat := if n == 0 then 0 else 2 ^ bitLength (n - 1)

def transform (n : Nat) : Nat := if n == 0 then 0 else n * max 1 (bitLength n - 1)

def fftCost (main auxiliary quotient height : Nat) : Nat :=
  3 * (main + auxiliary) * transform height + 2 * transform (quotient * height)
    + 2 * quotient * transform (2 * height)

def lookupDegree (lookups : Array (Nat × Nat)) (size : Nat) : Nat := Id.run do
  let mut result := 1
  let mut at_ := 0
  while at_ < lookups.size do
    let chunk := lookups.extract at_ (at_ + size)
    let degree := chunk.foldl (· + ·.1) 0
    let worst := chunk.foldl (fun m p => max m (p.2 + degree - p.1)) 0
    result := max result (max (degree + 1) worst)
    at_ := at_ + size
  return result

/-- Python's `math.ceil(a / b)` for positive `b`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Groups keyed by insertion order, as a Python dict iterates. -/
abbrev Groups := Array (Nat × Array Nat)

def Groups.get? (groups : Groups) (key : Nat) : Option (Array Nat) :=
  (groups.find? (·.1 == key)).map (·.2)

/-- Replace the members of `key` in place, or append a new key. -/
def Groups.set (groups : Groups) (key : Nat) (members : Array Nat) : Groups :=
  match groups.findIdx? (·.1 == key) with
  | some i => groups.set! i (key, members)
  | none => groups.push (key, members)

def Groups.erase (groups : Groups) (key : Nat) : Groups := groups.filter (·.1 != key)

def sorted (xs : Array Nat) : Array Nat := xs.qsort (· < ·)

structure Search where
  chips : Array Chip
  singleton : Std.HashMap String Shape
  counts : Array (Array Nat)
  shapes : IO.Ref (Std.HashMap (Array Nat) Shape)
  costs : IO.Ref (Std.HashMap (Array Nat) (Array Int))

def Search.shape (s : Search) (members : Array Nat) : IO Shape := do
  if let some cached := (← s.shapes.get)[members]? then return cached
  let result ← if members.size == 1 then do
      let name := s.chips[members[0]!]!.name
      let some shape := s.singleton[name]? | throw (IO.userError s!"no singleton shape for {name}")
      pure shape
    else do
      let selected := members.map (s.chips[·]!)
      let width := 1 + selected.foldl (fun n c => n + c.privateColumns + c.lifted) 0
        + selected.foldl (fun n c => max n c.shared) 0
      let count := selected.foldl (fun n c => max n c.lookups.size) 0
      let lookups := (Array.range count).map fun j =>
        (selected.foldl (fun n c => max n ((c.lookups[j]?.map (·.1)).getD 0)) 0,
         selected.foldl (fun n c => max n ((c.lookups[j]?.map (·.2)).getD 0)) 0)
      let constraints := selected.foldl (fun n c => max n c.constraintDegree) 2
      let quotient := padded (max 2 (max constraints (lookupDegree lookups 1)) - 1)
      let mut size := 1
      let mut candidate := min 8 lookups.size
      while candidate > 1 do
        if padded (max 2 (max constraints (lookupDegree lookups candidate)) - 1) ≤ quotient then
          size := candidate
          break
        candidate := candidate - 1
      pure (width, 2 * ceilDiv lookups.size size, quotient)
  s.shapes.modify (·.insert members result)
  return result

/-- `[main columns, 1, then per workload: cells, FFT cost]`. -/
def Search.cost (s : Search) (members : Array Nat) : IO (Array Int) := do
  if members.isEmpty then return Array.replicate (2 + 2 * s.counts.size) 0
  if let some cached := (← s.costs.get)[members]? then return cached
  let (main, auxiliary, quotient) ← s.shape members
  let mut values : Array Int := #[main, 1]
  for rows in s.counts do
    let height := padded (members.foldl (fun n i => n + rows[i]!) 0)
    values := values.push (height * main) |>.push (fftCost main auxiliary quotient height)
  s.costs.modify (·.insert members values)
  return values

def addAll (a b : Array Int) : Array Int := (a.zip b).map fun (x, y) => x + y

def Search.total (s : Search) (groups : Groups) : IO (Array Int) := do
  let mut sum := Array.replicate (2 + 2 * s.counts.size) 0
  for (_, g) in groups do sum := addAll sum (← s.cost g)
  return sum

def Search.delta (s : Search) (old new : Array (Array Nat)) : IO (Array Int) := do
  let mut result := Array.replicate (2 + 2 * s.counts.size) 0
  for g in new do result := addAll result (← s.cost g)
  for g in old do result := (result.zip (← s.cost g)).map fun (x, y) => x - y
  return result

def score (weights : Array Float) (delta : Array Int) : Float :=
  (delta.zip weights).foldl (fun acc (d, w) => acc + Float.ofInt d * w) 0

def fits (initial current delta : Array Int) : Bool :=
  (List.range (current.size - 2)).all fun k =>
    current[k + 2]! + delta[k + 2]! ≤ initial[k + 2]!

def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- `representatives` is a list of `[name, representative]` pairs. -/
def representatives (metrics : Json) : IO (Std.HashMap String String) := do
  let pairs ← IO.ofExcept (metrics.getObjValAs? (Array (String × String)) "representatives")
  return pairs.foldl (fun m (k, v) => m.insert k v) {}

structure Options where
  metrics : System.FilePath
  output : System.FilePath
  profiles : Array (System.FilePath × System.FilePath) := #[]
  prefix_ : String := ""
  maxMembers : Nat := 16
  sweeps : Nat := 4
  reportOnly : Bool := false

def parseArgs : List String → Options → Except String Options
  | [], o => if o.profiles.isEmpty || o.prefix_.isEmpty
      then .error "--prefix and at least one --profile are required" else .ok o
  | "--profile" :: counts :: shapes :: rest, o =>
    parseArgs rest { o with profiles := o.profiles.push (counts, shapes) }
  | "--prefix" :: p :: rest, o => parseArgs rest { o with prefix_ := p }
  | "--max-members" :: n :: rest, o => match n.toNat? with
    | some n => parseArgs rest { o with maxMembers := n }
    | none => .error "--max-members expects a number"
  | "--sweeps" :: n :: rest, o => match n.toNat? with
    | some n => parseArgs rest { o with sweeps := n }
    | none => .error "--sweeps expects a number"
  | "--report-only" :: rest, o => parseArgs rest { o with reportOnly := true }
  | arg :: _, _ => .error s!"unexpected argument {arg}"

def pad2 (i : Nat) : String := if i < 10 then s!"0{i}" else toString i

def run (o : Options) : IO Unit := do
  let metrics ← readJson o.metrics
  let chips ← IO.ofExcept (metrics.getObjValAs? (Array Chip) "chips")
  let indices : Std.HashMap String Nat :=
    chips.zipIdx.foldl (fun m (c, i) => m.insert c.name i) {}
  let reps ← representatives metrics
  let rep := fun (n : String) => (reps[n]?).getD n
  let index : String → IO Nat := fun n => match indices[rep n]? with
    | some i => pure i
    | none => throw (IO.userError s!"unknown chip {n}")
  let entries ← (← IO.ofExcept (metrics.getObjValAs? (Array String) "entries")).mapM index
  let mut counts : Array (Array Nat) := #[]
  let mut statistics : Array (Std.HashMap String Shape) := #[]
  for (countPath, shapePath) in o.profiles do
    let mut rows := Array.replicate chips.size 0
    for f in ← IO.ofExcept ((← readJson countPath).getObjValAs? (Array Json) "function_rows") do
      let i ← index (← IO.ofExcept (f.getObjValAs? String "chip"))
      rows := rows.modify i (· + (f.getObjValAs? Nat "rows").toOption.getD 0)
    counts := counts.push rows
    let mut shapes : Std.HashMap String Shape := {}
    for c in ← IO.ofExcept ((← readJson shapePath).getObjValAs? (Array Json) "circuits") do
      let stage1 ← IO.ofExcept (c.getObjValAs? Nat "stage1_width")
      let stage2 ← IO.ofExcept (c.getObjValAs? Nat "stage2_width")
      let quotient ← IO.ofExcept (c.getObjValAs? Nat "quotient_degree")
      shapes := shapes.insert (← IO.ofExcept (c.getObjValAs? String "name")) (stage1, stage2, quotient)
    statistics := statistics.push shapes
  -- Singleton shapes come from the actual Rust lowering, including lookup
  -- pairing; they do not depend on which workload produced the rows.
  let search : Search := {
    chips, counts, singleton := statistics[0]!
    shapes := ← IO.mkRef {}, costs := ← IO.mkRef {} }
  let mut groups : Groups := #[]
  let mut used : Array Nat := #[]
  for g in ← IO.ofExcept (metrics.getObjValAs? (Array (String × Array String)) "groups") do
    let mut members : Array Nat := #[]
    for n in g.2 do
      if let some i := indices[rep n]? then
        if !entries.contains i && !used.contains i && !members.contains i then
          members := members.push i
    if members.size ≥ 2 then
      groups := groups.push (groups.size, sorted members)
      used := used ++ members
  for i in [:chips.size] do
    if !used.contains i then groups := groups.push (groups.size, #[i])
  let initial ← search.total groups
  let n := counts.size.toFloat
  let mut weights : Array Float := #[0.05 / (Float.ofInt initial[0]!), 0.01 / (Float.ofInt initial[1]!)]
  for k in [:counts.size] do
    weights := weights.push (0.2 / n / Float.ofInt (max 1 initial[2 + 2 * k]!))
      |>.push (1.0 / n / Float.ofInt (max 1 initial[3 + 2 * k]!))
  let hasEntry := fun (g : Array Nat) => g.any entries.contains
  let mut current := initial
  if !o.reportOnly then
    for sweep in [:o.sweeps] do
      let mut moves := 0
      for member in [:chips.size] do
        if entries.contains member then continue
        let some (source, old) := groups.find? (·.2.contains member) | continue
        let remainder := old.filter (· != member)
        let destinations : Array (Option Nat) :=
          groups.map (some ·.1) ++ (if old.size > 1 then #[none] else #[])
        let mut best : Option (Float × Option Nat × Array Nat × Array Int) := none
        for target in destinations do
          if target == some source then continue
          let other := (target.bind groups.get?).getD #[]
          if hasEntry other || other.size ≥ o.maxMembers then continue
          let combined := sorted (other.push member)
          let delta ← search.delta #[old, other] #[remainder, combined]
          let gain := score weights delta
          if gain < -1e-10 && fits initial current delta &&
              (best.all fun (b, _) => gain < b) then
            best := some (gain, target, combined, delta)
        if let some (_, target, combined, delta) := best then
          let key := target.getD (groups.foldl (fun m (k, _) => max m k) 0 + 1)
          groups := groups.set key combined
          groups := if remainder.isEmpty then groups.erase source else groups.set source remainder
          current := addAll current delta
          moves := moves + 1
      -- Moving a whole group can cross a padding boundary that no single
      -- member move can improve on its own.
      for source in groups.map (·.1) do
        let some old := groups.get? source | continue
        if hasEntry old then continue
        let mut best : Option (Float × Nat × Array Nat × Array Int) := none
        for (target, other) in groups do
          if target == source || hasEntry other || old.size + other.size > o.maxMembers then
            continue
          let combined := sorted (old ++ other)
          let delta ← search.delta #[old, other] #[combined]
          let gain := score weights delta
          if gain < -1e-10 && fits initial current delta &&
              (best.all fun (b, _) => gain < b) then
            best := some (gain, target, combined, delta)
        if let some (_, target, combined, delta) := best then
          groups := (groups.set target combined).erase source
          current := addAll current delta
          moves := moves + 1
      IO.println s!"sweep {sweep}: {moves} moves, {groups.size} function circuits, \
        {current[0]!} columns, objective {score weights current}"
      if moves == 0 then break
  let ordered := (groups.map (·.2)).qsort fun a b => a[0]! < b[0]!
  let policy := (ordered.filter (·.size ≥ 2)).zipIdx.map fun (g, i) =>
    Json.arr #[toJson s!"{o.prefix_}_{pad2 i}", toJson (g.map (chips[·]!.name))]
  IO.FS.writeFile o.output ((Json.arr policy).pretty ++ "\n")
  let mut circuits : Array Json := #[]
  for g in ordered do
    let (main, auxiliary, quotient) ← search.shape g
    circuits := circuits.push <| Json.mkObj [("members", toJson (g.map (chips[·]!.name))),
      ("shape", toJson #[main, auxiliary, quotient]), ("cost", toJson (← search.cost g))]
  let dimensions := #["stage1_columns", "function_circuits"] ++
    (Array.range counts.size).flatMap fun i => #[s!"cells_{i}", s!"fft_{i}"]
  let report := Json.mkObj [("initial", toJson initial), ("optimized", toJson current),
    ("dimensions", toJson dimensions),
    ("profiles", toJson (o.profiles.map fun (c, s) => #[c.toString, s.toString])),
    ("circuits", Json.arr circuits)]
  IO.FS.writeFile (o.output.withExtension "report.json") (report.pretty ++ "\n")
  IO.println (Json.mkObj [("dimensions", toJson dimensions), ("initial", toJson initial),
    ("optimized", toJson current)]).compress

end GroupingSearch

def main (args : List String) : IO UInt32 := do
  let metrics :: output :: rest := args
    | IO.eprintln "usage: grouping_search METRICS OUTPUT --prefix P --profile COUNTS SHAPES \
        [--profile ...] [--max-members N] [--sweeps N] [--report-only]"
      return 2
  match GroupingSearch.parseArgs rest { metrics, output } with
  | .error e =>
    IO.eprintln e
    return 2
  | .ok options =>
    GroupingSearch.run options
    return 0
