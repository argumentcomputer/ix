import Tests.Ix.Compile.Corpus.Run

namespace Tests.Ix.Compile.Corpus

open Lean

def failure (row : Verdict) : Bool :=
  #["fail", "infrastructure-error", "not-run"].contains row.status

def verdictStatuses : Array String := #["pass", "known-unsupported", "documented-decline",
  "fail", "infrastructure-error", "not-run", "not-selected", "not-applicable"]

/-- Reporting requires exactly one row for every case/mode/phase, even when a
phase was not selected or could not run. Optional infrastructure rows add context;
they never replace the required phase rows. -/
def checkLedger (cases : Array Case) (modes phases : Array String) (rows : Array Verdict) :
    Except String Unit := do
  if cases.isEmpty || modes.isEmpty || rows.isEmpty then throw "empty corpus execution ledger"
  unless modes.all (#["off", "on"].contains ·) && modes.toList.eraseDups.length == modes.size do
    throw "invalid or duplicate ledger modes"
  unless phases.all (phaseNames.contains ·) && phases.toList.eraseDups.length == phases.size &&
      phases.contains "elaborate" && phases.contains "compile" do
    throw "invalid requested ledger phases"
  if (cases.map (·.id)).toList.eraseDups.length != cases.size then throw "duplicate ledger case"
  let mut seen : Std.HashSet (String × String × String) := {}
  for row in rows do
    unless cases.any (·.id == row.caseId) && modes.contains row.mode do
      throw s!"unknown ledger case/mode {row.caseId}/{row.mode}"
    unless verdictStatuses.contains row.status do throw s!"unknown verdict status {row.status}"
    unless phaseNames.contains row.phase || row.phase == "infrastructure" do
      throw s!"unknown verdict phase {row.phase}"
    let key := (row.caseId, row.mode, row.phase)
    if seen.contains key then throw s!"duplicate verdict {row.caseId}/{row.mode}/{row.phase}"
    seen := seen.insert key
    if row.phase == "infrastructure" then
      unless row.status == "infrastructure-error" do throw "invalid infrastructure verdict"
    else if !phases.contains row.phase then
      unless row.status == "not-selected" do throw s!"unselected phase has a result: {row.phase}"
    else if row.status == "not-selected" then throw s!"requested phase marked not-selected: {row.phase}"
    if row.status == "not-applicable" && !(row.phase == "parity" && row.mode == "on") then
      throw s!"invalid not-applicable phase {row.phase}/{row.mode}"
  for case in cases do
    for mode in modes do
      for phase in phaseNames do
        unless seen.contains (case.id, mode, phase) do
          throw s!"missing verdict {case.id}/{mode}/{phase}"

def validateExpected (cases : Array Case) (expected : Array Expected) : Except String Unit := do
  let mut seen : Std.HashSet (String × String × String) := {}
  for e in expected do
    if seen.contains (e.caseId, e.mode, e.phase) then throw s!"duplicate expectation {e.caseId}/{e.mode}/{e.phase}"
    seen := seen.insert (e.caseId, e.mode, e.phase)
    unless cases.any (·.id == e.caseId) do throw s!"expectation names absent case {e.caseId}"
    unless #["off", "on"].contains e.mode && phaseNames.contains e.phase do
      throw s!"invalid expected mode/phase {e.mode}/{e.phase}"
    if e.diagnostic.isEmpty || e.cause.isEmpty then throw "expected unsupported case lacks diagnostic or cause"

def run (cfg : RunConfig) (cases : Array Case) (expected : Array Expected)
    (modes : Array String) (revision : String) : IO UInt32 := do
  if cfg.jobs == 0 || cfg.workers == 0 || cfg.timeout == 0 then
    throw <| IO.userError "jobs, workers and timeout must be positive"
  if revision.isEmpty then throw <| IO.userError "--revision is required for run provenance"
  if cases.isEmpty || modes.isEmpty then throw <| IO.userError "run requires nonempty cases and modes"
  if modes.toList.eraseDups.length != modes.size then throw <| IO.userError "duplicate switch mode"
  let mut caseIds : Std.HashSet String := {}
  for case in cases do
    if caseIds.contains case.id then throw <| IO.userError s!"duplicate case {case.id}"
    if case.id.isEmpty || case.ns.isEmpty then throw <| IO.userError "empty case ID or namespace"
    caseIds := caseIds.insert case.id
  for mode in modes do
    unless #["off", "on"].contains mode do throw <| IO.userError s!"invalid switch mode {mode}"
  for phase in cfg.phases do
    unless phaseNames.contains phase do throw <| IO.userError s!"unknown phase {phase}"
  unless cfg.phases.contains "elaborate" && cfg.phases.contains "compile" do
    throw <| IO.userError "run must include elaborate and compile; use filter for elaboration only"
  if (cfg.phases.contains "closure" || cfg.phases.contains "parity") && !cfg.phases.contains "rust" then
    throw <| IO.userError "closure/parity requires the explicit Rust baseline phase"
  IO.ofExcept (validateExpected cases expected)
  for e in expected do
    unless modes.contains e.mode && cfg.phases.contains e.phase do
      throw <| IO.userError s!"expectation is outside selected execution: {e.caseId}/{e.mode}/{e.phase}"
  if ← (cfg.dir / "run-config.json").pathExists then
    throw <| IO.userError "run provenance already exists; use a fresh generated directory"
  let setup ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--version"], cwd := cfg.dir }
  IO.FS.writeFile (cfg.dir / "lake-setup.log") (setup.stdout ++ setup.stderr)
  unless setup.exitCode == 0 do throw <| IO.userError "generated Lake project setup failed; see lake-setup.log"
  let version ← IO.Process.output { cmd := "lean", args := #["--version"] }
  let digests ← IO.Process.output { cmd := "sha256sum", args := #[cfg.ix.toString, cfg.cert.toString] }
  unless digests.exitCode == 0 do throw <| IO.userError s!"cannot fingerprint compiler/checker executables: {digests.stderr}"
  writeJson (cfg.dir / "run-config.json") <| Json.mkObj [
    ("revision", toJson revision), ("lean", toJson version.stdout),
    ("binaryDigests", toJson digests.stdout),
    ("modes", toJson modes), ("phases", toJson cfg.phases),
    ("scope", toJson (if cfg.localScope then "local" else "whole")),
    ("jobs", toJson cfg.jobs), ("workersPerCase", toJson cfg.workers),
    ("timeoutSeconds", toJson cfg.timeout), ("cases", toJson (cases.map (·.id))),
    ("closureBackend", toJson "rust --consts"), ("expected", toJson expected)]
  writeJson (cfg.dir / "run-cases.json") cases
  -- compile-lean always invokes Lake. Build each selected module once before
  -- parallel off/on cases; their later Lake calls then only verify cached inputs.
  let modules ← cases.mapM fun case => do
    unless case.file.endsWith ".lean" do throw <| IO.userError s!"non-Lean case source {case.file}"
    pure ((case.file.dropEnd 5).toString.replace "/" ".")
  let prepared ← IO.Process.output
    { cmd := "lake", args := #["build"] ++ modules, cwd := cfg.dir }
  IO.FS.writeFile (cfg.dir / "prepare.log") (prepared.stdout ++ prepared.stderr)
  -- One assembled source that Lean rejects must not hide every other case. After
  -- a failed shared build, each module without an olean is built alone, and the
  -- ones that fail are recorded; their cases still run, and their own elaborate
  -- phase records the rejection. Every module failing is a preparation failure.
  let mut rejectedModules : Array String := #[]
  if prepared.exitCode != 0 then
    IO.FS.createDirAll (cfg.dir / "prepare")
    for m in modules do
      let olean := cfg.dir / ".lake" / "build" / "lib" / "lean" / s!"{m.replace "." "/"}.olean"
      if ← olean.pathExists then continue
      let one ← IO.Process.output { cmd := "lake", args := #["build", m], cwd := cfg.dir }
      if one.exitCode != 0 then
        rejectedModules := rejectedModules.push m
        IO.FS.writeFile (cfg.dir / "prepare" / s!"{m}.log") (one.stdout ++ one.stderr)
  let rejectedSet : Std.HashSet String := rejectedModules.foldl (·.insert ·) {}
  let usable := prepared.exitCode == 0 || (rejectedModules.size < modules.size && !rejectedModules.isEmpty)
  -- Elaboration/search-path initialization is process-global. Inventory source
  -- ownership serially before launching parallel oracle tasks, retaining full
  -- private/numeric Lean.Name identities rather than reparsing displayed names.
  let mut ownershipError : Option String := none
  if usable then
    try
      IO.FS.createDirAll (cfg.dir / "source-ownership")
      for (case, m) in cases.zip modules do
        if rejectedSet.contains m then continue
        let owned ← prepareOwnership (cfg.dir / case.file) case.ns
        writeJson (cfg.dir / "source-ownership" / s!"{case.id}.json") owned
    catch e => ownershipError := some e.toString
  let ready := usable && ownershipError.isNone
  writeJson (cfg.dir / "preparation.json") <| Json.mkObj [
    ("modules", toJson modules), ("exitCode", toJson prepared.exitCode.toNat),
    ("rejectedModules", toJson rejectedModules),
    ("ownershipError", toJson ownershipError),
    ("status", toJson (if !ready then "fail" else if rejectedModules.isEmpty then "pass" else "partial"))]
  if !rejectedModules.isEmpty then
    IO.eprintln s!"[corpus] {rejectedModules.size} assembled source(s) rejected by Lean; their cases run and fail at elaborate: {rejectedModules}"
  if !ready then
    let mut rows : Array Verdict := #[]
    for case in cases do
      for mode in modes do
        for phase in phaseNames do
          rows := rows.push ⟨case.id, mode, phase,
            if cfg.phases.contains phase then "not-run" else "not-selected",
            "shared source/ownership preparation failed", "preparation.json"⟩
    writeJson (cfg.dir / "verdicts.json") rows
    IO.eprintln "[corpus] source preparation failed; see prepare.log and preparation.json"
    return 1
  let mut pending : Array (Task (Except IO.Error (Array Verdict))) := #[]
  let mut rows := #[]
  for case in cases do
    for mode in modes do
      if pending.size ≥ cfg.jobs then
        if let some task := pending[0]? then rows := rows ++ (← IO.ofExcept task.get)
        pending := pending.extract 1 pending.size
        writeJson (cfg.dir / "run-progress.json") rows
      pending := pending.push (← IO.asTask (runCaseSafe { cfg with mode } expected case))
  for task in pending do rows := rows ++ (← IO.ofExcept (← IO.wait task))
  writeJson (cfg.dir / "verdicts.json") rows
  IO.ofExcept (checkLedger cases modes cfg.phases rows)
  let failures := rows.filter failure
  let unsupported := rows.filter fun row => #["known-unsupported", "documented-decline"].contains row.status
  IO.println s!"[corpus] {cases.size} cases × {modes.size} modes; {rows.size} phase rows; {unsupported.size} unsupported/declined, {failures.size} failures or unrun required phases"
  return if failures.isEmpty then 0 else 1

/-- Component-wise inverse renaming, unlike the old substring substitution. -/
def unrename (name : String) : String :=
  String.intercalate "." ((name.splitOn ".").map fun part =>
    if part == "AY" then "AX" else
      ([ ("Zq", "T"), ("Kq", "A"), ("Lq", "B"), ("Mq", "C"), ("Nq", "D") ].lookup part).getD part)

structure Comparison where
  caseId : String
  base : String
  mode : String
  kind : String
  status : String
  differing : Array String
  onlyBase : Array String
  onlyVariant : Array String
  addressMultisetEqual : Bool
  /-- Permutations only: datatype/constructor roots and canonical auxiliaries
  compared by address, and every canonical disagreement. -/
  rootsCompared : Nat := 0
  auxiliariesCompared : Nat := 0
  canonicalDifferences : Array String := #[]
  /-- `_ix` records whose owner is not a datatype root (definition-clique
  encodings): outside the canonical comparison, listed so none is silent. -/
  outOfScope : Array String := #[]
  deriving ToJson, FromJson

/-- Lean spells nested auxiliaries `rec_N`, `below_N`, `brecOn_N` under the
first member of the source block, so the spelling follows the source order. -/
def numberedNested (component : String) : Bool :=
  ["rec_", "below_", "brecOn_"].any fun p =>
    component.startsWith p &&
      let rest := (component.drop p.length).toString
      !rest.isEmpty && rest.all Char.isDigit

/-- The family of a numbered nested auxiliary suffix: `brecOn_2.eq` ↦ `brecOn_*.eq`. -/
def nestedFamily (suffix : List String) : String :=
  match suffix with
  | first :: rest => ".".intercalate ((((first.splitOn "_").head?.getD first) ++ "_*") :: rest)
  | [] => ""

/-- A record of a numbered nested auxiliary of one owner. -/
structure NestedRecord where
  suffix : String
  family : String
  address : String
  image : Bool
  regenerated : Bool

/-- The canonical view of one permutation variant (see `docs/compiler-corpus.md`,
"Permutation comparison"):

* `roots`: every record whose constant is a datatype or constructor projection
  (`iprj`/`cprj`), by name;
* `canonical`: the canonical auxiliaries of the variant's datatypes, keyed by
  owner and suffix. A record `X._ix.S` (Pass 3's canonical auxiliary, D14) has
  key `X/S`; a record `X.S` whose longest datatype-root prefix is `X` has the
  same key, and `X._ix.S` wins when both exist;
* `nominated`: the keys this variant asserts to be canonical: every `_ix` key;
  with Pass 3 off every regenerated record (`Named.original` present); with
  Pass 3 on every Lean-named record whose original is its own address;
* `nested`: records whose suffix starts with a numbered nested auxiliary
  (`rec_N`, `below_N`, `brecOn_N`), by owner; the owner is the source block's
  first member, so owners are matched across variants by `comparePermutation`;
  only owners with a nominated nested record take part;
* `outOfScope`: `_ix` records with no datatype owner;
* `problems`: two different addresses under one key. -/
structure CanonicalView where
  roots : Std.HashMap String String := {}
  canonical : Std.HashMap String String := {}
  nominated : Array String := #[]
  nested : Std.HashMap String (Array NestedRecord) := {}
  outOfScope : Array String := #[]
  problems : Array String := #[]

def canonicalView (records : Array NamedRecord) (pass3 : Bool) : CanonicalView := Id.run do
  let datatypes : Std.HashSet String :=
    records.foldl (fun s r => if r.kind == "iprj" then s.insert r.name else s) {}
  let mut view : CanonicalView := {}
  for r in records do
    if r.kind == "iprj" || r.kind == "cprj" then view := { view with roots := view.roots.insert r.name r.address }
  let mut plain : Std.HashMap String String := {}
  let mut images : Std.HashMap String String := {}
  for r in records do
    let parts := r.name.splitOn "."
    let split : Option (List String × List String × Bool) := match parts.findIdx? (· == "_ix") with
      | some i => if 0 < i && i + 1 < parts.length then some (parts.take i, parts.drop (i + 1), true) else none
      | none => (List.range parts.length).reverse.findSome? fun i =>
          if 0 < i && datatypes.contains (".".intercalate (parts.take i)) then
            some (parts.take i, parts.drop i, false)
          else none
    let some (owner, suffix, isImage) := split | continue
    let ownerName := ".".intercalate owner
    unless datatypes.contains ownerName do
      if isImage then view := { view with outOfScope := view.outOfScope.push r.name }
      continue
    let suffixName := ".".intercalate suffix
    -- With Pass 3 off a regenerated auxiliary carries Lean's form as its original;
    -- with Pass 3 on a Lean-named record is canonical only when Lean's form is
    -- itself canonical (original = address); otherwise it is an image.
    let canonicalPlain := !isImage && (if pass3 then r.original == some r.address else r.original.isSome)
    if suffix.head?.any numberedNested then
      let entry : NestedRecord :=
        ⟨suffixName, nestedFamily suffix, r.address, isImage, canonicalPlain⟩
      let previous := view.nested.getD ownerName #[]
      if previous.any fun e => e.suffix == suffixName && e.image == isImage && e.address != r.address then
        view := { view with problems := view.problems.push s!"{ownerName}/{suffixName}: two addresses in one variant" }
      view := { view with nested := view.nested.insert ownerName (previous.push entry) }
      continue
    let key := s!"{ownerName}/{suffixName}"
    let table := if isImage then images else plain
    if let some previous := table[key]? then
      if previous != r.address then
        view := { view with problems := view.problems.push s!"{key}: two addresses in one variant ({r.name})" }
    if isImage then images := images.insert key r.address else plain := plain.insert key r.address
    if isImage || canonicalPlain then view := { view with nominated := view.nominated.push key }
  let canonical := images.fold (fun m k a => m.insert k a) plain
  return { view with canonical }

/-- The canonical record of a nested suffix: the `_ix` record, else the Lean-named one. -/
def nestedAt (records : Array NestedRecord) (suffix : String) : Option String :=
  match records.find? (fun r => r.image && r.suffix == suffix) with
  | some r => some r.address
  | none => (records.find? (fun r => !r.image && r.suffix == suffix)).map (·.address)

/-- Canonical agreement of a permutation with its base: equal root maps; every
canonical auxiliary nominated by either side present on both sides at one
address; nested auxiliaries of corresponding owners equal per canonical position
for nominated records with Pass 3 on (`_ix` first), and, with Pass 3 off, equal as an address multiset per family
for regenerated Lean-named records (Lean numbers those in the source's own
discovery order). Owners of nested auxiliaries correspond by name, and the one
owner left on each side (the source block's first member) correspond to each
other; any other leftover is a difference. Returns roots compared, auxiliaries
compared, differences, and the out-of-scope image names. Name-map differences
are measured elsewhere. -/
def comparePermutation (base variant : Array NamedRecord) (pass3 : Bool) :
    Nat × Nat × Array String × Array String := Id.run do
  let b := canonicalView base pass3
  let v := canonicalView variant pass3
  let mut differences := b.problems.map ("base: " ++ ·) ++ v.problems.map ("variant: " ++ ·)
  if b.roots.isEmpty then differences := differences.push "no datatype/constructor roots in base"
  for (n, a) in b.roots.toArray do
    match v.roots[n]? with
    | none => differences := differences.push s!"root {n}: missing in variant"
    | some x => if x != a then differences := differences.push s!"root {n}: {a} vs {x}"
  for (n, _) in v.roots.toArray do
    unless b.roots.contains n do differences := differences.push s!"root {n}: missing in base"
  let keys := (b.nominated ++ v.nominated).toList.eraseDups.toArray.qsort (· < ·)
  let mut compared := keys.size
  for k in keys do
    match b.canonical[k]?, v.canonical[k]? with
    | some x, some y => if x != y then differences := differences.push s!"auxiliary {k}: {x} vs {y}"
    | none, _ => differences := differences.push s!"auxiliary {k}: missing in base"
    | _, none => differences := differences.push s!"auxiliary {k}: missing in variant"
  let owners (view : CanonicalView) : Array String :=
    ((view.nested.toArray.filter fun (_, rs) => rs.any fun r => r.image || r.regenerated).map (·.1)).qsort (· < ·)
  let bo := owners b
  let vo := owners v
  let leftBase := bo.filter (!vo.contains ·)
  let leftVariant := vo.filter (!bo.contains ·)
  let mut pairs := (bo.filter (vo.contains ·)).map fun o => (o, o)
  match leftBase.toList, leftVariant.toList with
  | [], [] => pure ()
  | [x], [y] => pairs := pairs.push (x, y)
  | _, _ =>
    let message := s!"nested auxiliary owners do not correspond: base {leftBase} variant {leftVariant}"
    differences := differences.push message
  for (ob, ov) in pairs do
    let br := b.nested.getD ob #[]
    let vr := v.nested.getD ov #[]
    let imageSuffixes := ((br ++ vr).filter fun r => r.image || (pass3 && r.regenerated)).map (·.suffix) |>.toList.eraseDups
    for s in imageSuffixes do
      compared := compared + 1
      match nestedAt br s, nestedAt vr s with
      | some x, some y => if x != y then differences := differences.push s!"nested {ob}~{ov}/{s}: {x} vs {y}"
      | none, _ => differences := differences.push s!"nested {ob}~{ov}/{s}: missing in base"
      | _, none => differences := differences.push s!"nested {ob}~{ov}/{s}: missing in variant"
    unless pass3 do
      let families := ((br ++ vr).filter (·.regenerated)).map (·.family) |>.toList.eraseDups
      for f in families do
        let multiset (rs : Array NestedRecord) :=
          ((rs.filter fun r => !r.image && r.family == f).map (·.address)).qsort (· < ·)
        compared := compared + (multiset br).size
        unless multiset br == multiset vr do
          differences := differences.push s!"nested family {ob}~{ov}/{f}: {multiset br} vs {multiset vr}"
  let outOfScope := (b.outOfScope.map ("base: " ++ ·) ++ v.outOfScope.map ("variant: " ++ ·)).qsort (· < ·)
  return (b.roots.size, compared, differences.qsort (· < ·), outOfScope)

def compareNamed (base variant : Array (String × String)) (rename : Bool) :
    Array String × Array String × Array String × Bool := Id.run do
  let variant := variant.map fun (n, a) => (if rename then unrename n else n, a)
  let bm := Std.HashMap.ofList base.toList
  let vm := Std.HashMap.ofList variant.toList
  let differing := base.filterMap fun (n, a) =>
    if let some b := vm[n]? then if a != b then some n else none else none
  let onlyBase := base.filterMap fun (n, _) => if vm.contains n then none else some n
  let onlyVariant := variant.filterMap fun (n, _) => if bm.contains n then none else some n
  let ba := (base.map (·.2)).qsort (· < ·)
  let va := (variant.map (·.2)).qsort (· < ·)
  return (differing.qsort (· < ·), onlyBase.qsort (· < ·), onlyVariant.qsort (· < ·), ba == va)

/-- No `_N` or Repr regex exclusions: all differences are retained for exact
non-canonical cause accounting. Missing base/variant artifacts fail closed. -/
def compareVariants (dir : System.FilePath) (modes : Array String) : IO UInt32 := do
  let cases : Array Case ← readJson (dir / "cases.json")
  let mut rows : Array Comparison := #[]
  for case in cases do
    if case.kind == "base" || case.kind == "aggregate" then continue
    for mode in modes do
      let bp := dir / "runs" / case.shape / mode / "compile-names.json"
      let vp := dir / "runs" / case.id / mode / "compile-names.json"
      if !(← bp.pathExists) || !(← vp.pathExists) then
        rows := rows.push ⟨case.id, case.shape, mode, case.kind, "missing", #[], #[], #[], false, 0, 0, #[], #[]⟩
        continue
      let base : Array (String × String) ← readJson bp
      let variant : Array (String × String) ← readJson vp
      let (diff, onlyBase, onlyVariant, equal) := compareNamed base variant (case.kind == "rename")
      if case.kind.startsWith "permutation:" then
        -- The full name map is a measured difference (source recursor aliases
        -- follow the member order); the verdict is the canonical agreement.
        let brp := dir / "runs" / case.shape / mode / "compile-records.json"
        let vrp := dir / "runs" / case.id / mode / "compile-records.json"
        if !(← brp.pathExists) || !(← vrp.pathExists) then
          rows := rows.push ⟨case.id, case.shape, mode, case.kind, "missing", diff, onlyBase, onlyVariant, equal, 0, 0, #[], #[]⟩
          continue
        let baseRecords : Array NamedRecord ← readJson brp
        let variantRecords : Array NamedRecord ← readJson vrp
        let (roots, auxiliaries, canonical, outOfScope) :=
          comparePermutation baseRecords variantRecords (mode == "on")
        rows := rows.push ⟨case.id, case.shape, mode, case.kind,
          if canonical.isEmpty then "pass" else "canonical-mismatch",
          diff, onlyBase, onlyVariant, equal, roots, auxiliaries, canonical, outOfScope⟩
      else
        let ok := !base.isEmpty && !variant.isEmpty && diff.isEmpty && onlyBase.isEmpty && onlyVariant.isEmpty && equal
        rows := rows.push ⟨case.id, case.shape, mode, case.kind, if ok then "pass" else "difference",
          diff, onlyBase, onlyVariant, equal, 0, 0, #[], #[]⟩
  writeJson (dir / "comparisons.json") rows
  let failures := rows.filter (·.status != "pass")
  let perms := rows.filter (·.kind.startsWith "permutation:")
  let permPass := perms.filter (·.status == "pass")
  let permNameDiff := permPass.filter fun r =>
    !(r.differing.isEmpty && r.onlyBase.isEmpty && r.onlyVariant.isEmpty)
  IO.println s!"[corpus] {rows.size} variant comparisons, {failures.size} differences/missing/canonical mismatches; no blanket exclusions"
  IO.println s!"[corpus] permutations: {permPass.size}/{perms.size} canonical agreement ({permNameDiff.size} of them with measured name-map differences); roots compared {perms.foldl (· + ·.rootsCompared) 0}, canonical auxiliaries compared {perms.foldl (· + ·.auxiliariesCompared) 0}"
  return if failures.isEmpty then 0 else 1

def matrix (dir : System.FilePath) : IO UInt32 := do
  let config : Json ← readJson (dir / "run-config.json")
  let ids ← IO.ofExcept (config.getObjValAs? (Array String) "cases")
  let modes ← IO.ofExcept (config.getObjValAs? (Array String) "modes")
  let phases ← IO.ofExcept (config.getObjValAs? (Array String) "phases")
  let cases : Array Case ← readJson (dir / (if ← (dir / "run-cases.json").pathExists then "run-cases.json" else "cases.json"))
  unless (cases.map (·.id)).qsort (· < ·) == ids.qsort (· < ·) do
    throw <| IO.userError "case manifest does not match the executed cases"
  let rows : Array Verdict ← readJson (dir / "verdicts.json")
  IO.ofExcept (checkLedger cases modes phases rows)
  let family := fun id => ((cases.find? (·.id == id)).map (·.family)).getD "unknown"
  let families := (cases.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
  let statuses := verdictStatuses
  let mut lines := #["| family | phase | mode | " ++ String.intercalate " | " statuses.toList ++ " |",
    "|---|---|---|" ++ String.join (statuses.toList.map fun _ => "---|")]
  for f in families do
    for phase in phaseNames.push "infrastructure" do
      for mode in #["off", "on"] do
        let selected := rows.filter fun r => family r.caseId == f && r.phase == phase && r.mode == mode
        unless selected.isEmpty do
          let counts := statuses.map fun status => toString (selected.filter (·.status == status)).size
          lines := lines.push s!"| {f} | {phase} | {mode} | {String.intercalate " | " counts.toList} |"
  let output := String.intercalate "\n" lines.toList ++ "\n"
  IO.FS.writeFile (dir / "matrix.md") output
  IO.print output
  return if rows.any failure then 1 else 0

def aggregate (dir : System.FilePath) (size : Nat := 45) : IO Unit := do
  if size == 0 then throw <| IO.userError "aggregate size must be positive"
  let cases : Array Case ← readJson (dir / "cases.json")
  IO.FS.createDirAll (dir / "aggregates")
  let bases := cases.filter (·.kind == "base")
  let families := (bases.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
  let mut aggregates : Array Case := #[]
  let mut manifest : Array (String × Array String) := #[]
  for family in families do
    let selected := bases.filter (·.family == family)
    for index in [: (selected.size + size - 1) / size] do
      let part := selected.extract (index * size) ((index + 1) * size)
      let id := s!"Agg_{family.replace "-" "_"}_{index}"
      let file := s!"aggregates/{id}.lean"
      let mut source := ""
      for case in part do source := source ++ (← IO.FS.readFile (dir / case.file))
      IO.FS.writeFile (dir / file) source
      aggregates := aggregates.push { id, shape := id, family, kind := "aggregate", ns := "AX", file }
      manifest := manifest.push (id, part.map (·.id))
  writeJson (dir / "aggregates.json") aggregates
  writeJson (dir / "aggregate-members.json") manifest
  IO.println s!"[corpus] {aggregates.size} aggregates covering {bases.size} bases"

end Tests.Ix.Compile.Corpus
