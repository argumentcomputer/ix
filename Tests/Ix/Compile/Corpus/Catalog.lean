import Tests.Ix.Compile.Corpus.Single
import Tests.Ix.Compile.Corpus.Nested

namespace Tests.Ix.Compile.Corpus

open Lean

def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))

def writeJson [ToJson α] (path : System.FilePath) (value : α) : IO Unit :=
  IO.FS.writeFile path ((toJson value).pretty ++ "\n")

def loadCatalog (dataDir : System.FilePath) : IO (Array Shape) := do
  let templates : Array Shape ← readJson (dataDir / "templates.json")
  let round2 : Array Shape ← readJson (dataDir / "round2.json")
  unless singles.size == 834 && nestedShapes.size == 220 && templates.size == 271 && round2.size == 70 do
    throw <| IO.userError s!"catalog coverage changed: {singles.size}/{nestedShapes.size}/{templates.size}/{round2.size}"
  let shapes := (singles ++ nestedShapes ++ templates ++ round2).qsort (fun a b => a.id < b.id)
  let mut seen : Std.HashSet String := {}
  for shape in shapes do
    if shape.id.isEmpty || !(shape.id.toList.all fun c => c.isAlphanum || c == '_') then
      throw <| IO.userError s!"unsafe shape id {shape.id}"
    if seen.contains shape.id then throw <| IO.userError s!"duplicate shape {shape.id}"
    seen := seen.insert shape.id
    let names := shape.extras.map (·.1)
    if names.toList.eraseDups.length != names.size then
      throw <| IO.userError s!"duplicate extra in {shape.id}"
  return shapes

def axis (shape : Shape) (key : String) : String :=
  (shape.axes.toList.lookup key).getD ""

/-- Complete requested grid coverage takes more than the historical ~120 estimate:
36 sort/recursion cells,110 container/form cells, all44 mutual cases,70 round2
neighbours, plus at least one representative of each remaining family. -/
def curated (shapes : Array Shape) : Array Shape := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for s in shapes do
    let key := if s.family == "single" then s!"single/{axis s "sort"}/{axis s "rec"}"
      else if s.family == "nested" then s!"nested/{axis s "container"}/{axis s "form"}"
      else if s.family == "mutual" || s.family == "round2" then s!"case/{s.id}"
      else s!"family/{s.family}"
    if !seen.contains key then
      seen := seen.insert key
      out := out.push s
  return out

def smokeIds : Array String := #["S_T_0_0_dir", "M2_T_cyc", "N_List_plain", "E_enum3"]

def select (shapes : Array Shape) (selection : String) : Except String (Array Shape) :=
  match selection with
  | "all" => .ok shapes
  | "curated" => .ok (curated shapes)
  | "smoke" => .ok (shapes.filter fun s => smokeIds.contains s.id)
  | _ => do
    let ids := selection.splitOn ","
    for id in ids do
      unless shapes.any (·.id == id) do throw s!"unknown shape {id}"
    return shapes.filter fun s => ids.contains s.id

end Tests.Ix.Compile.Corpus
