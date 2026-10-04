import Tests.Ix.Compile.Corpus.Catalog

namespace Tests.Ix.Compile.Corpus

open Lean

structure Candidate where
  id : String
  shape : String
  extra : Option String
  file : String
  deriving FromJson, ToJson

structure Elaboration where
  id : String
  verdict : String
  exitCode : Nat
  log : String
  deriving FromJson, ToJson

structure Case where
  id : String
  shape : String
  family : String
  kind : String
  ns : String
  file : String
  includedExtras : Array String := #[]
  excludedExtras : Array (String × String) := #[]
  deriving FromJson, ToJson

/-- Writing a fresh output directory is deliberate: stale results must not satisfy
coverage checks, and earlier failed-case artifacts must not be overwritten. -/
def generate (shapes : Array Shape) (dir : System.FilePath) : IO Unit := do
  if ← (dir / "shapes.json").pathExists then
    throw <| IO.userError s!"{dir}: already has a shape manifest; choose a fresh output directory"
  IO.FS.createDirAll (dir / "candidates")
  -- compile-lean builds its input module. Give generated modules a dependency-free
  -- Lake project of their own, so arbitrary output paths work and concurrent runs
  -- cannot mutate the compiler checkout's build artifacts.
  IO.FS.writeFile (dir / "lakefile.lean")
    "import Lake\nopen Lake DSL\npackage auxShapeCorpus\nlean_lib candidates where\n  globs := #[.submodules `candidates]\nlean_lib sources where\n  globs := #[.submodules `sources]\nlean_lib aggregates where\n  globs := #[.submodules `aggregates]\n"
  IO.FS.writeFile (dir / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
  writeJson (dir / "lake-manifest.json") <| Json.mkObj [
    ("version", toJson "1.2.0"), ("packagesDir", toJson ".lake/packages"),
    ("packages", toJson (#[] : Array Json)), ("name", toJson "auxShapeCorpus"),
    ("lakeDir", toJson ".lake"), ("fixedToolchain", toJson false)]
  let mut candidates : Array Candidate := #[]
  for shape in shapes do
    let file := s!"candidates/{shape.id}.lean"
    IO.FS.writeFile (dir / file) shape.source
    candidates := candidates.push ⟨shape.id, shape.id, none, file⟩
    for (name, source) in shape.extras.qsort (fun a b => a.1 < b.1) do
      let id := s!"{shape.id}__x_{name}"
      let file := s!"candidates/{id}.lean"
      IO.FS.writeFile (dir / file) (shape.source #[source])
      candidates := candidates.push ⟨id, shape.id, some name, file⟩
  writeJson (dir / "shapes.json") shapes
  writeJson (dir / "candidates.json") candidates
  IO.println s!"[corpus] {shapes.size} shapes, {candidates.size} elaboration candidates"

def elaborateOne (dir : System.FilePath) (timeout : Nat) (candidate : Candidate) : IO Elaboration := do
  let file ← IO.FS.realPath (dir / candidate.file)
  let result ← IO.Process.output { cmd := "timeout", args := #[toString timeout, "lean", file.toString] }
  let log := s!"elaboration/{candidate.id}.log"
  IO.FS.writeFile (dir / log) (result.stdout ++ result.stderr)
  -- Lean's normal source rejection is explicit unsupported source; timeout,
  -- signals, launcher errors and any nonstandard exit remain infrastructure errors.
  let diagnostic := result.stdout ++ result.stderr
  let panic := #["PANIC", "panic", "Stack overflow", "out of memory"].any fun s =>
    (diagnostic.splitOn s).length > 1
  let verdict := if result.exitCode == 0 then "accepted"
    else if result.exitCode == 1 && !panic then "source-rejected" else "infrastructure-error"
  return ⟨candidate.id, verdict, result.exitCode.toNat, log⟩

def elaborate (dir : System.FilePath) (jobs timeout : Nat) : IO UInt32 := do
  if jobs == 0 || timeout == 0 then throw <| IO.userError "jobs and timeout must be positive"
  let candidates : Array Candidate ← readJson (dir / "candidates.json")
  if ← (dir / "elaboration.json").pathExists then
    throw <| IO.userError "elaboration results already exist; use a fresh generated directory"
  IO.FS.createDirAll (dir / "elaboration")
  let mut pending : Array (Task (Except IO.Error Elaboration)) := #[]
  let mut results := #[]
  for candidate in candidates do
    if pending.size ≥ jobs then
      if let some task := pending[0]? then results := results.push (← IO.ofExcept task.get)
      pending := pending.extract 1 pending.size
    pending := pending.push (← IO.asTask (elaborateOne dir timeout candidate))
  for task in pending do results := results.push (← IO.ofExcept (← IO.wait task))
  writeJson (dir / "elaboration.json") results
  let rejected := results.filter (·.verdict == "source-rejected")
  let errors := results.filter (·.verdict == "infrastructure-error")
  IO.println s!"[corpus] elaborated {results.size}: {results.size - rejected.size - errors.size} accepted, {rejected.size} source-rejected, {errors.size} infrastructure errors"
  return if errors.isEmpty then 0 else 1

def numberedAux (text : String) : Bool :=
  [".rec_", ".below_", ".brecOn_"].any fun marker =>
    ((text.splitOn marker).drop 1).any fun rest => rest.toList.head?.any Char.isDigit

def checkedElaborations (candidates : Array Candidate) (rows : Array Elaboration) :
    Except String (Std.HashMap String Elaboration) := do
  let mut out := {}
  for row in rows do
    if out.contains row.id then throw s!"duplicate elaboration row {row.id}"
    unless candidates.any (·.id == row.id) do throw s!"unexpected elaboration row {row.id}"
    unless (row.verdict == "accepted" && row.exitCode == 0) ||
        (row.verdict == "source-rejected" && row.exitCode == 1) do
      throw s!"{row.id}: unresolved elaboration outcome {row.verdict}, exit {row.exitCode}"
    out := out.insert row.id row
  for candidate in candidates do
    unless out.contains candidate.id do throw s!"missing elaboration row {candidate.id}"
  return out

def assemble (dir : System.FilePath) : IO Unit := do
  let shapes : Array Shape ← readJson (dir / "shapes.json")
  let candidates : Array Candidate ← readJson (dir / "candidates.json")
  let rows : Array Elaboration ← readJson (dir / "elaboration.json")
  let results ← IO.ofExcept (checkedElaborations candidates rows)
  if ← (dir / "cases.json").pathExists then
    throw <| IO.userError "assembled cases already exist; use a fresh generated directory"
  IO.FS.createDirAll (dir / "sources")
  let accepted (id : String) := (results.get? id).any (·.verdict == "accepted")
  let mut cases : Array Case := #[]
  let mut rejected : Array String := #[]
  for shape in shapes do
    unless accepted shape.id do
      rejected := rejected.push shape.id
      continue
    let srec := (shape.extras.toList.lookup "srec").getD ""
    let mut parts : Array (String × String) := #[]
    let mut excluded : Array (String × String) := #[]
    for (name, text) in shape.extras.qsort (fun a b => a.1 < b.1) do
      if !accepted s!"{shape.id}__x_{name}" then
        excluded := excluded.push (name, "source-rejected; see elaboration manifest")
        continue
      if name != "srec" && !srec.isEmpty && text.startsWith srec then
        unless accepted s!"{shape.id}__x_srec" do
          throw <| IO.userError s!"{shape.id}/{name}: accepted dependent extra but srec was rejected"
        parts := parts.push (name, (text.drop srec.length).toString)
      else parts := parts.push (name, text)
    for rename in #[false, true] do
      let id := shape.id ++ if rename then "__ren" else ""
      let file := s!"sources/{id}.lean"
      IO.FS.writeFile (dir / file) (shape.source (parts.map (·.2)) rename)
      cases := cases.push
        { id, shape := shape.id, family := shape.family,
          kind := if rename then "rename" else "base", ns := s!"{if rename then "AY" else "AX"}.{shape.id}",
          file, includedExtras := parts.map (·.1), excludedExtras := excluded }
    if !shape.members.isEmpty then
      let orders := (permutations (List.range shape.members.size)).mergeSort (fun a b => compare a b != .gt)
      let permParts := parts.filter fun (_, text) => !numberedAux text
      let permExcluded := excluded ++ ((parts.filter fun (_, text) => numberedAux text).map fun (name, _) =>
        (name, "source-numbered nested auxiliary follows the first mutual member"))
      for (order, k) in orders.drop 1 |>.zipIdx do
        let id := s!"{shape.id}__p{k+1}"
        let file := s!"sources/{id}.lean"
        IO.FS.writeFile (dir / file) (← IO.ofExcept <| shape.permuted order (permParts.map (·.2)))
        cases := cases.push
          { id, shape := shape.id, family := shape.family,
            kind := "permutation:" ++ String.intercalate "," (order.map toString), ns := s!"AX.{shape.id}",
            file, includedExtras := permParts.map (·.1), excludedExtras := permExcluded }
  writeJson (dir / "cases.json") cases
  writeJson (dir / "rejected-shapes.json") rejected
  IO.println s!"[corpus] assembled {cases.size} cases; {rejected.size} explicitly rejected base shapes"

end Tests.Ix.Compile.Corpus
