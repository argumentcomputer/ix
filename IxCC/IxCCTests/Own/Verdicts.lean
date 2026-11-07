import IxCCTests.Corpus.Build

/-! # The producer's verdicts on the annotated sources (MT.7)

`fixtures/ownership/verdicts.json`, format `ixcc/own-verdicts/1`: one
record per annotated source of the ownership suite (and per negative probe),
with ix's verdict under the pinned producer and the corpus fixture that
freezes the closure when ix accepts it. Required CI never runs ix: it checks
the file against the sources and the corpus manifest (`check`). The manual
`rebuild` re-runs the pinned ix with the corpus manifest's anonymous command
(`ix compile --no-build --consts ROOTS --equations --profile PROFILE --anon`,
under the family's pinned profile) and rewrites the derived fields, among
them the plain-data crossing diagnostics ix prints (`crossed`).

A verdict is `ok`, or a rejection with:
* `stage`: `resource` (ix's resource admission of the whole closure, run
  before any annotated constant is emitted), `elaboration` (a
  `SourceContractError` of ix's Lean elaborator), `profile` (the profile
  refuses an annotated recursive definition not bound to its equation,
  `annotated-recursion`, or an annotated native one, `native`) or `other`;
* `code`: the admission error (`Usage(1, Linear, Many)`, `Nonduplicable`,
  `UnrestrictedEscape(2)`, `Unsupported("…")`, …) or the
  `SourceContractError` constructor, never the message text;
* `constant`: for a resource error, the first 12 hex digits of the address
  of the constant ix names.

Fields are reviewed (`id`, `name`, `categories`, `source`, `consts`,
`probe`, `fixture`, `twin`, `note`) or derived (`sha256`, `producer`). -/

namespace IxCCTests.Own.Verdicts

open Lean System IxCC.Tools.Check
open IxCCTests.Corpus (OJson Family Tools proc fill)

def format : String := "ixcc/own-verdicts/1"

def path : FilePath := "fixtures/ownership/verdicts.json"

structure Producer where
  verdict : String
  stage : String := ""
  code : String := ""
  constant : String := ""
  deriving BEq, Inhabited, Repr

structure Entry where
  id : String
  name : String
  categories : List String
  source : String
  sha256 : String := ""
  consts : List String
  probe : Option String := none
  producer : Producer := { verdict := "" }
  fixture : Option String := none
  twin : Option String := none
  note : Option String := none
  /-- The plain-data crossing diagnostics `ix compile` printed (derived): a
  written `1`/`&` on a binder of plain-data type, which the profile does not
  enforce (`[compile] resource: plain-data crossing: …`). Expected data, not a
  failure. -/
  crossed : List String := []
  deriving BEq, Inhabited

structure File where
  description : String
  sourceRoot : String
  manifest : String
  ixRevision : String
  ixBinarySha256 : String
  entries : List Entry
  deriving BEq, Inhabited

/-! ## Reading and writing -/

private def optStr (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

def Producer.ofJson (j : Json) : IO Producer := do
  return { verdict := ← strField j "verdict", stage := (optStr j "stage").getD ""
           code := (optStr j "code").getD "", constant := (optStr j "constant").getD "" }

def Entry.ofJson (j : Json) : IO Entry := do
  let strs := fun (k : String) => do
    return ((← arrField j k).toList.mapM fun s => checked s.getStr?)
  return { id := ← strField j "id", name := ← strField j "name"
           categories := ← (← strs "categories"), source := ← strField j "source"
           sha256 := (optStr j "sha256").getD "", consts := ← (← strs "consts")
           probe := optStr j "probe"
           producer := ← (match j.getObjVal? "producer" with
             | .ok p => Producer.ofJson p
             | .error _ => pure { verdict := "" })
           fixture := optStr j "fixture", twin := optStr j "twin", note := optStr j "note"
           crossed := ((j.getObjValAs? (Array String) "crossed").toOption.getD #[]).toList }

def File.read (p : FilePath := path) : IO File := do
  let j ← readJson p
  need ((← strField j "format") == format) s!"{p}: not a {format} file"
  let prod ← field j "producer"
  return { description := ← strField j "description", sourceRoot := ← strField j "source_root"
           manifest := ← strField j "manifest"
           ixRevision := ← strField prod "ix_revision", ixBinarySha256 := ← strField prod "ix_binary_sha256"
           entries := ← (← arrField j "verdicts").toList.mapM Entry.ofJson }

def Producer.toOJson (p : Producer) : OJson :=
  .fields [("verdict", some (.str p.verdict)),
    ("stage", if p.stage.isEmpty then none else some (.str p.stage)),
    ("code", if p.code.isEmpty then none else some (.str p.code)),
    ("constant", if p.constant.isEmpty then none else some (.str p.constant))]

def Entry.toOJson (e : Entry) : OJson :=
  .fields [("id", some (.str e.id)), ("name", some (.str e.name)),
    ("categories", some (.strs e.categories)), ("source", some (.str e.source)),
    ("sha256", some (.str e.sha256)), ("consts", some (.strs e.consts)),
    ("probe", e.probe.map .str), ("producer", some e.producer.toOJson),
    ("fixture", e.fixture.map .str), ("twin", e.twin.map .str), ("note", e.note.map .str),
    ("crossed", if e.crossed.isEmpty then none else some (.strs e.crossed))]

/-- The file, with the producer's command (the manifest's anonymous one). -/
def File.toOJson (f : File) (command : List String) : OJson :=
  .fields [("format", some (.str format)), ("description", some (.str f.description)),
    ("source_root", some (.str f.sourceRoot)), ("manifest", some (.str f.manifest)),
    ("producer", some (.obj #[("ix_revision", .str f.ixRevision),
      ("ix_binary_sha256", .str f.ixBinarySha256), ("command", .strs command)])),
    ("verdicts", some (.arr (f.entries.map Entry.toOJson).toArray))]

/-! ## ix's log -/

/-- The text between `start` and the next `stop` after it. -/
def between (s start stop : String) : Option String :=
  match s.splitOn start with
  | _ :: rest :: _ => some ((rest.splitOn stop).headD "")
  | _ => none

/-- The verdict of a failed `ix compile` from its log (as
`plans/fixtures/ix-usage-ownership/verdict.sh` reads it). -/
def parseLog (log : String) : Producer :=
  if (log.splitOn "resource admission").length > 1 then
    let constant := ((between log "Hash(\\\"" "\\\"").getD "").take 12 |>.toString
    let code := ((between log "}): " "\" })").getD "").replace "\\\"" "\""
    { verdict := "reject", stage := "resource", code, constant }
  else if (log.splitOn "SourceContractError.").length > 1 then
    let rest := (between log "SourceContractError." " ").getD ""
    let code := String.ofList (rest.toList.takeWhile Char.isAlphanum)
    { verdict := "reject", stage := "elaboration", code }
  -- the profile's refusals before admission (ix's review restrictions R2-3, R2-2)
  else if (log.splitOn "is an annotated recursive definition").length > 1 then
    { verdict := "reject", stage := "profile", code := "annotated-recursion" }
  else if (log.splitOn "has a native implementation").length > 1 then
    { verdict := "reject", stage := "profile", code := "native" }
  else
    let line := ((log.splitOn "\n").find? fun l => (l.splitOn "rror").length > 1).getD "?"
    { verdict := "reject", stage := "other", code := (line.trimAscii.toString.take 160).toString }

private def containsText (text needle : String) : Bool := (text.splitOn needle).length > 1

/-- The final message of an ix log as one line: the last `uncaught exception:`
line with its indented continuation lines (a structured value Lean prints
across lines) joined by single spaces, and without the `FILE:LINE:COL: error: `
position Lean puts before an elaboration error. `none` when anything but
continuation lines follows that line. -/
def finalRejection (log : String) : Option String := do
  let marker := "uncaught exception: "
  let lines := (log.splitOn "\n").filter (!·.trimAscii.isEmpty)
  let start ← ((List.range lines.length).filter (fun i => lines[i]!.startsWith marker)).getLast?
  let continuation := lines.drop (start + 1)
  guard (continuation.all (·.startsWith " "))
  let message := (lines[start]!.drop marker.length).toString
  let message := match message.splitOn ": error: " with
    | position :: first :: rest =>
      if (position.splitOn ".lean:").length > 1 then ": error: ".intercalate (first :: rest) else message
    | _ => message
  return " ".intercalate ((marker ++ message) :: continuation.map (·.trimAscii.toString))

/-- Only completed, known CLI refusals are frozen. Exit 1 is ix's normal
failure status; signal/timeout statuses and resource-budget exhaustion are
infrastructure failures. Keep `parseLog` for legacy frozen records. -/
def completedRejection (status : UInt32) (log : String) : Except String Producer := do
  unless status == 1 do throw s!"unexpected ix exit status {status}"
  unless log.endsWith "\n" do throw "unterminated ix rejection output"
  let some line := finalRejection log | throw "missing completed ix rejection"
  let p := parseLog line
  unless !p.code.isEmpty do throw "empty ix rejection code"
  match p.stage with
  | "resource" =>
    unless containsText line "rs_compile_env: Rust compilation failed: UnsupportedExpr { desc: \"resource admission " &&
        line.endsWith "\" })" do throw "incomplete resource rejection"
    let constructor := String.ofList (p.code.toList.takeWhile Char.isAlphanum)
    unless ["Unbound", "BadReference", "UnresolvedSharing", "Unsupported", "TypeMismatch",
        "BinderMismatch", "Usage", "Moved", "SharedToUnique", "ActiveLoan", "Escape",
        "UnrestrictedEscape", "Nonduplicable", "InvalidBorrow", "InvalidPlace", "InvalidScope"].contains constructor do
      throw s!"unknown or exhausted resource rejection: {p.code}"
    unless isHex 12 p.constant do throw "resource rejection has no constant address"
  | "elaboration" =>
    unless line.startsWith "uncaught exception: source contract: Ix.Compile.SourceContractError." do
      throw "unrecognized source-contract rejection"
    unless ["missingDeclaration", "duplicateDeclaration", "declarationNameMismatch", "duplicateContract",
        "staleSource", "invalidSite", "expectedBinder", "resultOnNonArrow", "borrowOnNonLet",
        "invalidBorrowView", "duplicateSite", "argumentOutOfRange", "unknownBinder", "ambiguousBinder",
        "missingBodyBinder", "inconsistentTelescope", "inconsistentValue", "annotatedRecursorRule",
        "malformedAnnotation", "misplacedAnnotation", "annotationBinderMismatch", "duplicateAnnotation",
        "missingAnnotation", "conflictingAnnotation", "missingContract", "lostAnnotation",
        "duplicateMeasure", "zeroFixedStep"].contains p.code do
      throw s!"unknown source-contract rejection: {p.code}"
    unless containsText line (p.code ++ " `") do throw "source-contract rejection has no declaration"
  | "profile" =>
    unless line.startsWith "uncaught exception: resource profile: `" do throw "unrecognized profile rejection"
    if p.code == "annotated-recursion" then
      unless containsText line "admitted only when checked through its unfolding equation" &&
          line.endsWith "never through its kernel encoding" do throw "incomplete recursive-profile rejection"
    else if p.code == "native" then
      unless containsText line "its Lean body is only a model" &&
          containsText line "explicit profile assumption (assume " && line.endsWith ")" do
        throw "incomplete native-profile rejection"
    else throw "unknown profile rejection"
  | _ => throw "unrecognized ix failure (not a semantic rejection)"
  return p

/-- A successful compile must have emitted both complete files in the fresh
run directory. A census or exit-zero status is not a decoding check. -/
def compileResult (status : UInt32) (log : String) (closure sidecar : FilePath) : IO Producer := do
  if status != 0 then return ← checked (completedRejection status log)
  let bytes ← IO.FS.readBinFile closure
  let _ ← checked (IxCC.Ixon.V3.decodeAnonymousEnv bytes)
  let json ← readJson sidecar
  need ((← strField json "format") == "ix/compile-equations/1") "ix emitted an unknown equation sidecar"
  let _ ← arrField json "equations"
  let _ ← arrField json "failures"
  return { verdict := "ok" }

/-- Check all reviewed producer inputs before invoking ix. -/
def checkRebuildInputs (f : File) (m : Family) (ix : FilePath) : IO Unit := do
  need (f.ixRevision == m.producer.ixRevision && f.ixBinarySha256 == m.producer.ixBinarySha256)
    "verdict and family producer pins differ"
  need (f.sourceRoot == m.sourceRoot) "verdict and family source roots differ"
  need ((← sha256 ix) == f.ixBinarySha256) s!"{ix}: not the pinned ix {f.ixBinarySha256}"
  if let some profile := m.producer.profile then
    need ((← sha256 profile.path) == profile.sha256) s!"profile {profile.path} differs from the pinned digest"

/-! ## Check (offline) -/

/-- The annotated sources under the source root (`<ID>/Annotated.lean`). -/
def annotatedSources (root : FilePath) : IO (List String) := do
  let mut out := []
  for d in ← root.readDir do
    if ← (d.path / "Annotated.lean").pathExists then out := out ++ [s!"{d.fileName}/Annotated.lean"]
  return out.mergeSort (· ≤ ·)

/-- Check the verdicts against the sources and the corpus manifest; the
counts (entries, accepted, rejected). -/
def check (p : FilePath := path) : IO (Nat × Nat × Nat) := do
  let f ← File.read p
  let m ← Family.read f.manifest
  need ((← IO.FS.readFile p) == (f.toOJson m.producer.anonymous).render)
    s!"{p}: not in canonical form (rebuild rewrites it)"
  need (f.ixRevision == m.producer.ixRevision && f.ixBinarySha256 == m.producer.ixBinarySha256)
    s!"{p}: the producer pins differ from {f.manifest}'s"
  let root : FilePath := f.sourceRoot
  need (root.toString == m.sourceRoot) s!"{p}: source root {root}, the manifest's is {m.sourceRoot}"
  let ids := f.entries.map (·.id)
  need (ids.eraseDups.length == ids.length) s!"{p}: repeated ids"
  let sources := f.entries.map (·.source)
  need (sources.eraseDups.length == sources.length) s!"{p}: a source has two verdicts"
  need ((← annotatedSources root) == sources.mergeSort (· ≤ ·))
    s!"{p}: the verdicts do not cover exactly the annotated sources under {root}"
  let mut accepted := 0
  let mut rejected := 0
  for e in f.entries do
    let label := s!"{p} {e.id}"
    need ((← sha256 (root / e.source)) == e.sha256) s!"{label}: {e.source} changed since its verdict"
    need (!e.consts.isEmpty && !e.categories.isEmpty) s!"{label}: no consts or categories"
    match e.producer.verdict with
    | "ok" =>
      let some name := e.fixture | throw (IO.userError s!"{label}: accepted, but no corpus fixture")
      let some fx := m.fixtures.find? (·.name == name)
        | throw (IO.userError s!"{label}: no fixture {name} in {f.manifest}")
      need (fx.source.path == e.source && fx.consts == e.consts && fx.source.variant == "annotated")
        s!"{label}: fixture {name} has another source, consts or variant"
      need (m.producer.profile.isNone || fx.resource.isSome)
        s!"{label}: fixture {name} has no resource record although the family pins a profile"
      if let some t := e.twin then
        let some tw := m.fixtures.find? (·.name == t)
          | throw (IO.userError s!"{label}: no twin {t} in {f.manifest}")
        need (tw.source.variant == "plain" && tw.consts == e.consts && tw.roots.map (·.name) == fx.roots.map (·.name))
          s!"{label}: twin {t} is not a plain fixture with the same roots"
      accepted := accepted + 1
    | "reject" =>
      need (e.fixture.isNone && ["resource", "elaboration", "profile", "other"].contains e.producer.stage &&
        !e.producer.code.isEmpty) s!"{label}: a rejection needs a stage and a code, and no fixture"
      rejected := rejected + 1
    | v => throw (IO.userError s!"{label}: verdict {v}")
  -- every annotated corpus fixture has its verdict
  for fx in m.fixtures do
    if fx.source.variant == "annotated" then
      need (f.entries.any (·.fixture == some fx.name)) s!"{p}: corpus fixture {fx.name} has no verdict"
  return (f.entries.length, accepted, rejected)

/-! ## Rebuild (manual; needs the pinned ix) -/

def rebuild (t : Tools) (p : FilePath := path) : IO Unit := do
  let f ← File.read p
  let some ix := t.ix | throw (IO.userError "rebuild needs --ix PATH")
  let ix ← IO.FS.realPath ix
  let m ← Family.read f.manifest
  checkRebuildInputs f m ix
  let root : FilePath := f.sourceRoot
  let profile ← match m.producer.profile with
    | some p => do pure [("{profile}", (← IO.FS.realPath p.path).toString)]
    | none => pure []
  let mut entries := []
  for e in f.entries do
    let work ← IxCCTests.Corpus.freshWorkDir t.work
    let stem := e.source.replace "/" "_"
    let closure := work / s!"{stem}.ixe"
    let sidecar := work / s!"{stem}.equations.json"
    let subst := [("{consts}", ",".intercalate e.consts), ("{ixe}", closure.toString),
      ("{equations}", sidecar.toString), ("{src}", e.source)] ++ profile
    let (code, out, err) ← proc ix.toString (fill m.producer.anonymous subst) (some root) t.ixPath
    IO.FS.writeFile (work / s!"{stem}.log") (out ++ err)
    let producer ← try compileResult code (out ++ err) closure sidecar
      catch error => throw (IO.userError s!"{e.id}: {error}; log: {work / s!"{stem}.log"}")
    let crossed := ((out ++ err).splitOn "\n").filterMap fun l =>
      match l.splitOn "[compile] resource: plain-data crossing: " with
      | [_, rest] => some ("plain-data crossing: " ++ rest.trimAscii.toString)
      | _ => none
    IO.println s!"{e.id}\t{producer.verdict}\t{producer.stage}\t{producer.code}\t{crossed.length} crossing(s)"
    entries := entries ++ [{ e with producer, crossed, sha256 := ← sha256 (root / e.source) }]
  let text := ({ f with entries }.toOJson m.producer.anonymous).render
  if (← IO.FS.readFile p) == text then IO.println s!"{p}: unchanged"
  else
    IO.FS.writeFile p text
    IO.println s!"{p}: rewritten"

end IxCCTests.Own.Verdicts
