import Tests.Ix.Compile.Corpus.Report

open Lean
open Tests.Ix.Compile.Corpus

private def usage : String :=
  "aux-shape-sweep <inventory|generate|filter|assemble|aggregate|run|ownership|compare|matrix|records|self-check|verify-legacy|verify-round2>\n" ++
  "  --dir PATH --select all|curated|smoke|id,... --data PATH\n" ++
  "  --jobs N --workers N --timeout SECONDS --mode off|on|both\n" ++
  "  --phases comma,list --revision COMMIT --expected FILE --cases FILE\n" ++
  "  --local --keep-envs --legacy FILE --size N --ix PATH --cert PATH --env FILE --ns PREFIX --file SRC --out FILE\n" ++
  "Run requires --revision. Outputs are immutable per run directory; no silent resume.\n"

private def options (args : List String) : Except String (Std.HashMap String String) := do
  let mut result := {}
  let mut pending : Option String := none
  for arg in args do
    if let some key := pending then
      if arg.startsWith "--" then throw s!"missing value for {key}"
      result := result.insert key arg
      pending := none
    else
      unless #["--dir", "--select", "--data", "--jobs", "--workers", "--timeout", "--mode",
        "--phases", "--revision", "--expected", "--cases", "--local", "--keep-envs", "--legacy", "--size", "--ix", "--cert", "--env", "--ns", "--file", "--out"].contains arg do
        throw s!"unknown option {arg}"
      if result.contains arg then throw s!"duplicate option {arg}"
      if #["--local", "--keep-envs"].contains arg then result := result.insert arg "true"
      else pending := some arg
  if let some key := pending then throw s!"missing value for {key}"
  return result

private def natOption (opts : Std.HashMap String String) (key : String) (default : Nat) : IO Nat :=
  match opts[key]? with
  | none => pure default
  | some value => match value.toNat? with
    | some n => pure n
    | none => throw <| IO.userError s!"invalid natural number for {key}: {value}"

private def record (name address kind : String) (original : Option String := none)
    (block : Option String := none) : NamedRecord :=
  { name, address, kind, original, block }

private def selfCheck (data : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let check (label : String) (ok : Bool) : IO Unit := do
    unless ok do throw <| IO.userError s!"self-check failed: {label}"
    IO.println s!"[corpus] PASS {label}"
  check "complete historical shape count plus70 round2 bases" (shapes.size == 1395)
  check "single grid792" ((singles.filter (·.family == "single")).size == 792)
  check "nested grid22×5" ((nestedShapes.filter (·.family == "nested")).size == 110)
  check "4-case smoke selection" ((← IO.ofExcept (select shapes "smoke")).size == 4)
  let selected := curated shapes
  check "curated sort/recursion cells36" ((selected.filter (·.family == "single")).size == 36)
  check "curated container/form cells110" ((selected.filter (·.family == "nested")).size == 110)
  check "curated all44 mutuals and70 round2 neighbors"
    ((selected.filter (·.family == "mutual")).size == 44 && (selected.filter (·.family == "round2")).size == 70)
  check "token-aware substitution" (substitute "$T $Tree $A.foo" renamedNames == "Zq $Tree Kq.foo")
  check "token-aware inverse names" (unrename "AY.Test.Zq.fooZq" == "AX.Test.T.fooZq")
  let privateName := (((`_private).str "SourceModule").num 0 ++ `CorpusOwnership.helper)
  let stringName := (((`_private).str "SourceModule").str "0" ++ `CorpusOwnership.helper)
  check "private numeric name identity round trips"
    (nameOfParts (nameParts privateName) == privateName && nameParts privateName != nameParts stringName)
  check "ambiguous displayed selector identities rejected"
    ((checkSelectorIdentities #[Ix.Name.fromLeanName privateName, Ix.Name.fromLeanName stringName]
      #[Ix.Name.fromLeanName privateName]).toOption.isNone)
  let ownedEnv ← getFileEnv "Tests/Ix/Compile/Corpus/OwnershipFixture.lean"
  let owned := sourceOwnership ownedEnv `CorpusOwnership
  let own := owned.originalNames
  check "actual source private theorem and helper are owned"
    (own.size == 4 && (own.filter (privateToUserName? · |>.isSome)).size == 2)
  check "imported declarations are not source owned" (!owned.sourceSet.contains (Ix.Name.fromLeanName ``Nat.add))
  let natOwned := sourceOwnership ownedEnv `Nat
  check "same-namespace imported declarations are not source owned"
    (natOwned.names.size == 1 && !natOwned.sourceSet.contains (Ix.Name.fromLeanName ``Nat.add))
  check "canonical auxiliary spelling is owned through its exact source owner"
    (ownedOutput owned.sourceSet (Ix.Name.fromLeanName `CorpusOwnership.exposed._ix.rec_7))
  check "unowned generated-looking name is excluded"
    (!ownedOutput owned.sourceSet (Ix.Name.fromLeanName `CorpusOwnership.absent._ix.rec_7))
  check "imported same-namespace image owner is excluded"
    (!ownedOutput natOwned.sourceSet (Ix.Name.fromLeanName `Nat.add._ix.rec_7))
  let privateOwned : Std.HashSet Ix.Name := ({} : Std.HashSet Ix.Name).insert (Ix.Name.fromLeanName privateName)
  check "canonical nested helper preserves private owner identity"
    (ownedOutput privateOwned (Ix.Name.fromLeanName (privateName ++ `_ix.rec_7)) &&
      !ownedOutput privateOwned (Ix.Name.fromLeanName (stringName ++ `_ix.rec_7)))
  -- The ownership inventory runs in a child process per case (the imported
  -- environment dies with the child); it must equal the in-process inventory.
  IO.FS.withTempDir fun tmp => do
    let self ← IO.appPath
    let child ← ownershipChild self "Tests/Ix/Compile/Corpus/OwnershipFixture.lean" "CorpusOwnership"
      (tmp / "owned.json") (tmp / "owned.log")
    let childOwned : Option Ownership ← if child.isNone then some <$> readJson (tmp / "owned.json") else pure none
    check "child-process ownership inventory equals the in-process inventory"
      (childOwned.any fun o => o.names.size == owned.names.size &&
        o.originalNames.all (owned.originalNames.contains ·))
    let missing ← ownershipChild self "Tests/Ix/Compile/Corpus/absent-source.lean" "CorpusOwnership"
      (tmp / "absent.json") (tmp / "absent.log")
    check "child-process ownership inventory of an absent source fails" missing.isSome
    let foreign ← ownershipChild self "Tests/Ix/Compile/Corpus/OwnershipFixture.lean" "NoSuchNamespace"
      (tmp / "foreign.json") (tmp / "foreign.log")
    check "child-process ownership inventory without owned declarations fails" foreign.isSome
  -- check-lean coverage per address (BB-F7: one name kept per collapsed address).
  let selection := #[("aa", #["AX.C.A", "AX.C.B"]), ("bb", #["AX.C.A.mk", "AX.C.B.mk"]), ("cc", #["AX.C.f"])]
  check "check-lean alias of a covered address counts as covered"
    ((leanAddressCoverage selection #["AX.C.B", "AX.C.B.mk"]).toOption == some #["AX.C.B", "AX.C.B.mk"])
  check "check-lean address with no matched name rejected"
    ((leanAddressCoverage selection #["AX.C.A", "AX.C.B"]).toOption.isNone)
  check "check-lean unrequested unmatched name rejected"
    ((leanAddressCoverage selection #["AX.C.g"]).toOption.isNone)
  check "check-lean empty per-address selection rejected" ((leanAddressCoverage #[] #[]).toOption.isNone)
  check "check-lean full match accepted" ((leanAddressCoverage selection #[]).toOption == some #[])
  -- Permuted sources omit parts that name recursor motives by member position.
  check "positional motive argument detected"
    (positionalMotive "u := A.brecOn (motive_1 := fun _ => Nat) a" && !positionalMotive "A.rec (motive := fun _ => Nat)" &&
      !positionalMotive "def motive_x := 1")
  check "all3-member permutations" ((permutations [0,1,2]).length == 6)
  let shape : Shape := { id := "x", family := "test", decl := "", members := #["a", "b"] }
  check "duplicate permutation rejected" ((shape.permuted [0,0] #[]).toOption.isNone)
  let candidates : Array Candidate := #[⟨"x", "x", none, "x.lean"⟩]
  check "missing elaboration result rejected" ((checkedElaborations candidates #[]).toOption.isNone)
  let row : Elaboration := ⟨"x", "accepted", 0, "x.log"⟩
  check "duplicate elaboration result rejected" ((checkedElaborations candidates #[row,row]).toOption.isNone)
  check "inconsistent elaboration result rejected"
    ((checkedElaborations candidates #[{ row with exitCode := 124 }]).toOption.isNone)
  let (differences, _, _, same) := compareNamed #[("AX.C.T", "aaa")] #[("AY.C.Zq", "bbb")] true
  check "wrong variant address detected" (!differences.isEmpty && !same)
  let (differences, onlyBase, onlyVariant, same) := compareNamed #[("AX.C.T", "aaa")] #[("AY.C.Zq", "aaa")] true
  check "renamed matching address accepted" (differences.isEmpty && onlyBase.isEmpty && onlyVariant.isEmpty && same)
  -- Permutation controls, shaped like the measured two-member block with nested
  -- auxiliaries (F2_twoaux): A first in the base, B first in the variant.
  let roots := #[record "AX.P.A" "ta" "iprj" none (some "blk"), record "AX.P.A.mk" "ca" "cprj" none (some "blk"),
    record "AX.P.B" "tb" "iprj" none (some "blk"), record "AX.P.B.leaf" "cb" "cprj" none (some "blk")]
  let offBase := roots ++ #[record "AX.P.A.rec" "ra" "recr" (some "leanA1"),
    record "AX.P.B.rec" "rb" "recr" (some "leanB1"), record "AX.P.A.rec_1" "n1" "recr" (some "leanN1"),
    record "AX.P.A.below_1" "lb1" "defn", record "AX.P.auxRec" "alias1" "defn"]
  let offPerm := roots ++ #[record "AX.P.A.rec" "ra" "recr" (some "leanA2"),
    record "AX.P.B.rec" "rb" "recr" (some "leanB2"), record "AX.P.B.rec_1" "n1" "recr" (some "leanN2"),
    record "AX.P.B.below_1" "lb2" "defn", record "AX.P.auxRec" "alias2" "defn"]
  let (rootsN, auxN, canonical, _) := comparePermutation offBase offPerm false
  let (nameDiff, onlyB, onlyV, _) := compareNamed (offBase.map fun r => (r.name, r.address))
    (offPerm.map fun r => (r.name, r.address)) false
  check "permutation with equal canonical roots/auxiliaries accepted despite measured alias differences"
    (canonical.isEmpty && rootsN == 4 && auxN == 3 && nameDiff == #["AX.P.auxRec"] && !onlyB.isEmpty && !onlyV.isEmpty)
  let (_, _, canonical, _) := comparePermutation offBase
    (offPerm.map fun r => if r.name == "AX.P.B.leaf" then { r with address := "other" } else r) false
  check "permutation with a different constructor root rejected" (canonical == #["root AX.P.B.leaf: cb vs other"])
  let (_, _, canonical, _) := comparePermutation offBase
    (offPerm.map fun r => if r.name == "AX.P.B.rec_1" then { r with address := "other" } else r) false
  check "permutation with a different canonical nested recursor rejected"
    (canonical == #["nested family AX.P.A~AX.P.B/rec_*: #[n1] vs #[other]"])
  -- Lean numbers nested auxiliaries in the source's discovery order: with Pass 3
  -- off the regenerated family is a multiset; `_ix` images are per position.
  let nestedOff (owner : String) (first second : String) : Array NamedRecord :=
    #[record s!"AX.P.{owner}.rec_1" first "recr" (some "lean1"), record s!"AX.P.{owner}.rec_2" second "recr" (some "lean2")]
  check "Lean-numbered nested auxiliaries in another order accepted with Pass 3 off"
    ((comparePermutation (roots ++ nestedOff "A" "n1" "n2") (roots ++ nestedOff "B" "n2" "n1") false).2.2.1.isEmpty)
  check "Lean-numbered nested auxiliary family with another member rejected with Pass 3 off"
    (!(comparePermutation (roots ++ nestedOff "A" "n1" "n2") (roots ++ nestedOff "B" "n2" "n3") false).2.2.1.isEmpty)
  let nestedOn (owner : String) (first second : String) : Array NamedRecord :=
    #[record s!"AX.P.{owner}._ix.rec_1" first "recr", record s!"AX.P.{owner}._ix.rec_2" second "recr"]
  check "canonical nested images at the same positions accepted with Pass 3 on"
    ((comparePermutation (roots ++ nestedOn "A" "n1" "n2") (roots ++ nestedOn "B" "n1" "n2") true).2.2.1.isEmpty)
  check "canonical nested images at swapped positions rejected with Pass 3 on"
    ((comparePermutation (roots ++ nestedOn "A" "n1" "n2") (roots ++ nestedOn "B" "n2" "n1") true).2.2.1.size == 2)
  let rootsD := roots.push (record "AX.P.D" "td" "iprj" none (some "blkD"))
  check "nested auxiliary owners without a correspondence rejected"
    ((comparePermutation (rootsD ++ nestedOff "A" "n1" "n2") (rootsD ++ nestedOff "B" "n1" "n2" ++ nestedOff "D" "n1" "n2")
      false).2.2.1 == #["nested auxiliary owners do not correspond: base #[AX.P.A] variant #[AX.P.B, AX.P.D]"])
  let (_, _, canonical, _) := comparePermutation offBase (offPerm.filter (·.name != "AX.P.B.rec")) false
  check "permutation missing a canonical auxiliary rejected"
    (canonical == #["auxiliary AX.P.B/rec: missing in variant"])
  -- Pass 3 on: the canonical auxiliaries are the `_ix` records; Lean names hold images.
  -- An unchanged block keeps canonical auxiliaries under Lean names (original = address).
  let onBase := roots ++ #[record "AX.P.A.rec" "ra" "recr" (some "ra") none, record "AX.P.A.rec_1" "n1" "recr" (some "n1") none]
  let onPerm := roots ++ #[record "AX.P.A._ix.rec" "ra" "recr" none none,
    record "AX.P.A.rec" "imageA" "defn" (some "leanA2") none, record "AX.P.B._ix.rec_1" "n1" "recr" none none,
    record "AX.P.B.rec_1" "imageN" "defn" (some "leanN2") none, record "AX.P.f._ix._mutual" "m" "defn" none none]
  let (_, auxN, canonical, outOfScope) := comparePermutation onBase onPerm true
  check "Pass 3 canonical images matched with the base's canonical auxiliaries"
    (canonical.isEmpty && auxN == 2 && outOfScope == #["variant: AX.P.f._ix._mutual"])
  let (_, _, canonical, _) := comparePermutation onBase
    (onPerm.map fun r => if r.name == "AX.P.A._ix.rec" then { r with address := "imageA" } else r) true
  check "Pass 3 Lean-named image without its canonical record rejected"
    ((comparePermutation onBase (onPerm.filter (·.name != "AX.P.A._ix.rec")) true).2.2.1 ==
      #["auxiliary AX.P.A/rec: ra vs imageA"])
  check "Pass 3 canonical image at another address rejected"
    (canonical == #["auxiliary AX.P.A/rec: ra vs imageA"])
  check "permutation without roots rejected"
    (!(comparePermutation (offBase.filter fun r => r.kind != "iprj" && r.kind != "cprj") offPerm false).2.2.1.isEmpty)
  let expected : Array Expected := #[⟨"x", "on", "compile", "known diagnostic", "documented defect"⟩]
  let infrastructure : Verdict := ⟨"x", "on", "compile", "infrastructure-error", "known diagnostic", ""⟩
  check "expectation cannot suppress infrastructure error"
    ((applyExpected expected infrastructure "known diagnostic").status == "infrastructure-error")
  check "expectation cannot hide unexpected pass"
    ((applyExpected expected { infrastructure with status := "pass" } "").status == "fail")
  check "exact documented failure classified"
    ((applyExpected expected { infrastructure with status := "fail" } "known diagnostic").status == "known-unsupported")
  check "known failure cannot hide an additional failure"
    ((applyExpected expected { infrastructure with status := "fail" } "known diagnostic\nunexpected failure").status == "fail")
  check "Rust zero-target success rejected"
    ((checkedRustTargets "[check] 0/0 passed\n" 0).toOption.isNone)
  check "Rust missing summary rejected" ((checkedRustTargets "success\n" 0).toOption.isNone)
  check "Rust inconsistent success rejected"
    ((checkedRustTargets "[check] 1/2 passed\n" 0).toOption.isNone)
  check "Rust real work accepted" ((checkedRustTargets "[check] 2/2 passed\n" 0).toOption == some 2)
  check "Lean zero-target success rejected"
    ((Tests.Ix.Compile.KernelReport.checkedLeanTargets "##check-lean## 1 0 0 0\n").toOption.isNone)
  check "Lean unmatched selection retained"
    (Tests.Ix.Compile.KernelReport.leanUnmatched "[check-lean] warning: --consts name matched nothing: AX.X.T\n" == #["AX.X.T"])
  IO.FS.withTempDir fun dir => do
    let case : Case := ⟨"missing", "missing", "test", "base", "AX.Missing", "missing-source.lean", #[], #[]⟩
    let progress := dir / "runs" / case.id / "on"
    IO.FS.createDirAll progress
    writeJson (progress / "progress.json")
      (#[⟨case.id, "on", "elaborate", "pass", "completed before injected infrastructure failure", ""⟩] : Array Verdict)
    let rows ← runCaseSafe { dir, phases := #["elaborate", "compile", "certified"] } #[] case
    check "infrastructure failure preserves completed phase"
      (rows.any fun r => r.phase == "elaborate" && r.status == "pass")
    check "infrastructure failure records every unrun requested phase"
      ((rows.filter (·.status == "not-run")).size == 2 && rows.size == phaseNames.size + 1)
    check "infrastructure failure remains a failure"
      (rows.any fun r => r.phase == "infrastructure" && failure r)
  let aggregateCase : Case := ⟨"Agg_test", "Agg_test", "aggregate-family", "aggregate", "AX", "aggregates/Agg_test.lean", #[], #[]⟩
  let ledger : Array Verdict := phaseNames.map fun phase =>
    ⟨aggregateCase.id, "off", phase, if #["elaborate", "compile"].contains phase then "pass" else "not-selected", "", ""⟩
  check "complete aggregate ledger accepted"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] ledger).toOption.isSome)
  check "missing phase ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] (ledger.extract 1 ledger.size)).toOption.isNone)
  check "duplicate phase ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] (ledger ++ ledger)).toOption.isNone)
  check "wrong executed case manifest rejected"
    ((checkLedger #[{ aggregateCase with id := "different" }] #["off"] #["elaborate", "compile"] ledger).toOption.isNone)
  check "empty ledger rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile"] #[]).toOption.isNone)
  check "unknown ledger phase selection rejected"
    ((checkLedger #[aggregateCase] #["off"] #["elaborate", "compile", "unknown"] ledger).toOption.isNone)
  IO.println s!"[corpus] curated {curated shapes |>.size} cases; smoke4; full{shapes.size}"
  return 0

/-- Development evidence against the read-only legacy catalog: exact declaration
and extra source equality, independent of order in JSON objects. No Python runs. -/
private def verifyLegacy (data path : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let legacy : Array Json ← readJson path
  let mut count := 0
  let mut problems : Array String := #[]
  for row in legacy do
    let id ← IO.ofExcept (row.getObjValAs? String "id")
    let some shape := shapes.find? (·.id == id)
      | problems := problems.push s!"missing shape {id}"
        continue
    let decl ← IO.ofExcept (row.getObjValAs? String "decl")
    if shape.decl != decl then problems := problems.push s!"{id}: declaration differs"
    let extraNames ← IO.ofExcept (row.getObjValAs? (Array String) "extras")
    if extraNames.size != shape.extras.size then problems := problems.push s!"{id}: extra count differs"
    let texts ← IO.ofExcept (row.getObjVal? "extra_text")
    for name in extraNames do
      let text ← IO.ofExcept (texts.getObjValAs? String name)
      if shape.extras.toList.lookup name != some text then problems := problems.push s!"{id}/{name}: extra differs"
    count := count + 1
  for p in problems do IO.println s!"[corpus] FAIL {p}"
  IO.println s!"[corpus] compared {count} legacy declarations and extras; {problems.size} differences"
  return if count == 1325 && problems.isEmpty then 0 else 1

/-- Verify all 70 round2 bases byte-for-byte, and all 82 historical permutations
up to blank separator lines introduced by the generic member assembler. -/
private def verifyRound2 (data path : System.FilePath) : IO UInt32 := do
  let shapes ← loadCatalog data
  let mut count := 0
  let mut failures := 0
  let lines (text : String) := (text.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  for entry in ← path.readDir do
    if entry.path.extension != some "lean" then continue
    let id := entry.path.fileStem.getD ""
    let parts := id.splitOn "__p"
    let base := parts.head!
    let some shape := shapes.find? (·.id == base)
      | throw <| IO.userError s!"unknown round2 fixture {id}"
    let actual ← if parts.length == 1 then pure shape.source
      else do
        let some index := (parts[1]!).toNat? | throw <| IO.userError s!"bad permutation ID {id}"
        let orders := (permutations (List.range shape.members.size)).mergeSort (fun a b => compare a b != .gt)
        let some order := orders[index]? | throw <| IO.userError s!"missing permutation {id}"
        IO.ofExcept (shape.permuted order #[])
    let expected ← IO.FS.readFile entry.path
    let equal := if parts.length == 1 then actual == expected else lines actual == lines expected
    unless equal do
      IO.println s!"[corpus] FAIL round2 {id}"
      failures := failures + 1
    count := count + 1
  IO.println s!"[corpus] compared {count} round2 sources; {failures} differences"
  return if count == 152 && failures == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    let some op := args.head? | IO.print usage; return 2
    if op == "--help" then IO.print usage; return 0
    let opts ← IO.ofExcept (options args.tail)
    let dir : System.FilePath := opts.getD "--dir" "out/aux-shape-sweep"
    let data : System.FilePath := opts.getD "--data" "Tests/Ix/Compile/Corpus/Data"
    let jobs ← natOption opts "--jobs" 4
    let timeout ← natOption opts "--timeout" 900
    let mode := opts.getD "--mode" "both"
    let modes := if mode == "both" then #["off", "on"] else #[mode]
    match op with
    | "inventory" =>
      let shapes ← loadCatalog data
      let families := (shapes.map (·.family)).toList.eraseDups.mergeSort (· ≤ ·)
      for family in families do
        IO.println s!"{family}\t{(shapes.filter (·.family == family)).size}"
      IO.println s!"total\t{shapes.size}\ncurated\t{curated shapes |>.size}"
      return 0
    | "generate" =>
      generate (← IO.ofExcept <| select (← loadCatalog data) (opts.getD "--select" "curated")) dir
      return 0
    | "filter" => elaborate dir jobs timeout
    | "assemble" => assemble dir; return 0
    | "aggregate" => aggregate dir (← natOption opts "--size" 45); return 0
    | "run" =>
      let cases : Array Case ← readJson (dir / opts.getD "--cases" "cases.json")
      let expected : Array Expected ← match opts["--expected"]? with
        | none => pure #[]
        | some path => readJson path
      run
        { dir, jobs, timeout, workers := ← natOption opts "--workers" 1,
          ix := opts.getD "--ix" ".lake/build/bin/ix", cert := opts.getD "--cert" ".lake/build/bin/kernel-check-ixe",
          localScope := opts.contains "--local", keepEnvs := opts.contains "--keep-envs",
          phases := ((opts.getD "--phases" (String.intercalate "," phaseNames.toList)).splitOn ",").toArray }
        cases expected modes (opts.getD "--revision" "")
    | "ownership" =>
      -- One source's ownership inventory, run by `run` as a child process per
      -- case so that the imported environment is released with the process.
      let some file := opts["--file"]? | throw <| IO.userError "ownership requires --file"
      let some ns := opts["--ns"]? | throw <| IO.userError "ownership requires --ns"
      let some out := opts["--out"]? | throw <| IO.userError "ownership requires --out"
      writeJson ⟨out⟩ (← prepareOwnership ⟨file⟩ ns)
      return 0
    | "compare" => compareVariants dir modes
    | "matrix" => matrix dir
    | "records" =>
      -- Investigation aid: every Named record whose displayed name starts with --ns.
      let some path := opts["--env"]? | throw <| IO.userError "records requires --env"
      let some ns := opts["--ns"]? | throw <| IO.userError "records requires --ns"
      let env ← loadEnv ⟨path⟩
      let names := (env.named.toArray.filter fun (n, _) => n.pretty.startsWith ns).qsort
        (fun a b => a.1.pretty < b.1.pretty)
      if names.isEmpty then throw <| IO.userError s!"no records under {ns}"
      IO.println (toJson (namedRecords env names)).pretty
      return 0
    | "self-check" => selfCheck data
    | "verify-legacy" =>
      let some path := opts["--legacy"]? | throw <| IO.userError "verify-legacy requires --legacy"
      verifyLegacy data path
    | "verify-round2" =>
      let some path := opts["--legacy"]? | throw <| IO.userError "verify-round2 requires --legacy directory"
      verifyRound2 data path
    | _ => IO.eprintln usage; throw <| IO.userError s!"unknown command {op}"
  catch e =>
    IO.eprintln s!"[corpus] ERROR {e}"
    return 2
