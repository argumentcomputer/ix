import Tests.FormalChecks.Common

/-!
# `formal-checks refactor`

Compare a modularized artifact with its pre-refactor export.

Only declared global renames and no-op guards/assignments may differ. Removing
the legacy load/store syntax wrappers eliminates their empty binding guards;
jump targets and trace hint instruction offsets are relocated accordingly.
Every other instruction, constraint, table row, layout and grouping must match.
This is an artifact regression check, not a legacy-to-Aiur translation proof.
-/

namespace Tests.FormalChecks.Refactor

open Lean System Tests.FormalChecks

def usage : String := "usage: formal-checks refactor [--out OUT] before after names"

/-- `f` applied to every string value (not key) of `j`. -/
partial def mapStrings (f : String → String) : Json → Json
  | .str s => .str (f s)
  | .arr xs => .arr (xs.map (mapStrings f))
  | .obj kvs => .obj (kvs.foldl (init := kvs) fun acc k v => acc.insert k (mapStrings f v))
  | j => j

private def isWord (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Replace every `IxVM::name` and `MultiStark::name` that starts a word with
its entry in `names`, if it has one. -/
def rename (names : Std.HashMap String String) (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < cs.size do
    let boundary := i == 0 || !isWord cs[i - 1]!
    let rest := cs.extract i cs.size
    let lead? := ["IxVM::", "MultiStark::"].find? fun p =>
      boundary && (rest.extract 0 p.length).toList == p.toList
    match lead? with
    | some p =>
      let word := (cs.extract (i + p.length) cs.size).toList.takeWhile isWord
      if word.isEmpty then
        out := out.push cs[i]!
        i := i + 1
      else
        let token := p ++ String.ofList word
        out := out ++ (names.getD token token).toList.toArray
        i := i + p.length + word.length
    | none =>
      out := out.push cs[i]!
      i := i + 1
  return String.ofList out.toList

private def get (j : Json) (k : String) : Json := j.getObjValD k
private def arr (j : Json) : Array Json := (j.getArr?).toOption.getD #[]
private def nat (j : Json) : Nat := (j.getNat?).toOption.getD 0
private def str (j : Json) : String := (j.getStr?).toOption.getD ""

/-- `positions[i]` for a relocation table. -/
private def relocate (positions : Array Nat) (j : Json) : Json :=
  toJson (positions[nat j]?.getD (nat j))

/-- Relocate every hint's instruction offset in `j`. -/
private partial def relocateHints (positions : Array Nat) : Json → Json
  | .arr xs => .arr (xs.map (relocateHints positions))
  | .obj kvs =>
    let j := Json.obj kvs
    let j := if get j "op" == Json.str "hint" then j.setObjVal! "instruction"
        (relocate positions (get j "instruction")) else j
    match j with
    | .obj kvs => .obj (kvs.foldl (init := kvs) fun acc k v => acc.insert k (relocateHints positions v))
    | j => j
  | j => j

/-- Drop the empty guards, relocate jumps, branches and trace hints, and drop
the no-op assignments. Returns the package and the number of guards removed. -/
def normalizeGuards (package : Json) : Json × Nat := Id.run do
  let mut removed := 0
  let mut maps : Std.HashMap String (Array Nat) := {}
  let mut functions := #[]
  for function in arr (get (get package "program") "functions") do
    let ops := arr (get function "code")
    let mut code : Array Json := #[]
    let mut positions : Array Nat := #[]
    for op in ops do
      positions := positions.push code.size
      if get op "op" == Json.str "guard" && arr (get op "tests") == #[] then removed := removed + 1
      else code := code.push op
    positions := positions.push code.size
    code := code.map fun op =>
      if get op "op" == Json.str "jump" then op.setObjVal! "target" (relocate positions (get op "target"))
      else if get op "op" == Json.str "branch" then
        op.setObjVal! "otherwise" (relocate positions (get op "otherwise"))
      else op
    functions := functions.push (function.setObjVal! "code" (.arr code))
    maps := maps.insert (str (get function "name")) positions
  let program := (get package "program").setObjVal! "functions" (.arr functions)
  let mut traceFunctions := #[]
  for function in arr (get (get package "trace") "functions") do
    let positions := maps.getD (str (get function "name")) #[]
    let steps := arr (relocateHints positions (get function "steps"))
    let steps := steps.filter fun step =>
      let action := get step "action"
      !(get action "op" == Json.str "assign" &&
        arr (get action "values") == (arr (get action "dest")).map fun dest =>
          Json.mkObj [("var", dest)])
    traceFunctions := traceFunctions.push (function.setObjVal! "steps" (.arr steps))
  let trace := (get package "trace").setObjVal! "functions" (.arr traceFunctions)
  return ((package.setObjVal! "program" program).setObjVal! "trace" trace, removed)

private def kind : Json → Nat
  | .null => 0 | .bool _ => 1 | .num _ => 2 | .str _ => 3 | .arr _ => 4 | .obj _ => 5

/-- The path of the first difference between `a` and `b`, if any. -/
partial def firstDifference (a b : Json) (path : String := "") : Option String :=
  if kind a != kind b then some (path ++ ": different types") else
  match a, b with
  | .obj x, .obj y =>
    let keys (m : Std.TreeMap.Raw String Json compare) := m.foldl (init := #[]) fun ks k _ => ks.push k
    if keys x != keys y then some (path ++ ": different keys") else
    (keys x).findSome? fun k =>
      let (u, v) := (a.getObjValD k, b.getObjValD k)
      if u == v then none else firstDifference u v s!"{path}.{k}"
  | .arr xs, .arr ys =>
    if xs.size != ys.size then some s!"{path}: different lengths {xs.size} != {ys.size}" else
    (xs.zip ys).zipIdx.findSome? fun ((x, y), i) =>
      if x == y then none else firstDifference x y s!"{path}[{i}]"
  | _, _ => if a == b then none else some s!"{path}: {a.compress} != {b.compress}"

def main (argv : List String) : IO UInt32 := do
  let args ← match Args.parse [] argv with
    | .ok a => pure a
    | .error e => return ← usageError usage e
  let #[before, after, namesPath] := args.positional
    | return ← usageError usage "expected before, after and names"
  let names ← IO.ofExcept ((← readJson namesPath).getObj?)
  let names : Std.HashMap String String := names.foldl (init := {}) fun m k v =>
    match v.getStr? with
    | .ok s => m.insert k s
    | .error _ => m
  let beforeJson := mapStrings (rename names) (← readJson before)
  let (beforeJson, removedBefore) := normalizeGuards beforeJson
  let (afterJson, removedAfter) := normalizeGuards (← readJson after)
  if let some difference := firstDifference beforeJson afterJson then
    IO.eprintln s!"Refactor mismatch at {difference}"
    return 1
  let summary := Json.mkObj [
    ("equivalent_artifacts_modulo_names_and_noops", true),
    ("functions", toJson (arr (get (get afterJson "program") "functions")).size),
    ("maps", toJson (arr (get (get afterJson "program") "maps")).size),
    ("chips", toJson (arr (get (get afterJson "trace") "chips")).size),
    ("groups", toJson (arr (get (get afterJson "trace") "groups")).size),
    ("removed_empty_guards", toJson ((removedBefore : Int) - removedAfter)),
    ("before", toJson before), ("after", toJson after)]
  IO.println summary.pretty
  if let some out := args.flag? "out" then IO.FS.writeFile out (summary.pretty ++ "\n")
  return 0

end Tests.FormalChecks.Refactor
