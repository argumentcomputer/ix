import IxCCTests.Corpus.Build
import IxCCTests.Src.Support
import IxCCTests.Own.Verdicts
import IxCCTests.Src.Resource

/-! Focused resource-provenance regressions, run by
`lake exe tests-own --only resource-records`. No ix installation is needed. -/

namespace IxCCTests.Corpus.ResourceChecks

open Lean System IxCCTests.Src

private def rootAddress := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
private def profileAddress := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
private def definitionAddress := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
private def equationAddress := "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"

-- Independent CLI samples, rather than output produced by the parser under test.
private def header : String :=
  s!"check-equations: resource claim (root {rootAddress}, profile {profileAddress}) holds\n"

private def pairLine : String := s!"  f {definitionAddress} ↦ f.eq_def {equationAddress}\n"
private def emptyOutput : String := header ++ "check-equations: 0 checked pair(s) verified\n"
private def pairOutput : String := header ++ pairLine ++ "check-equations: 1 checked pair(s) verified\n"

private def pair : CheckedPair :=
  { definition := "f", definitionAddress, equation := "f.eq_def", equationAddress }

private def pairJson : Json := Json.mkObj [
  ("definition", .str "f"), ("definitionAddress", .str definitionAddress),
  ("equation", .str "f.eq_def"), ("equationAddress", .str equationAddress)]

private def rejects (a : Assert) (label : String) (action : IO α) : IO Unit := do
  let rejected ← try
    let _ ← action
    pure false
  catch _ => pure true
  expect a rejected s!"resource-records: {label} unexpectedly succeeded"

private def protocol (a : Assert) : IO Unit := do
  expect a ((verifiedPairs emptyOutput profileAddress).toOption == some []) "resource-records: valid empty CLI result"
  expect a ((verifiedPairs pairOutput profileAddress).toOption == some [pair]) "resource-records: valid CLI pair"
  let invalid := [
    ("empty output", ""),
    ("missing header", "check-equations: 0 checked pair(s) verified\n"),
    ("missing completion", header ++ pairLine),
    ("garbage", header ++ "unexpected output\ncheck-equations: 0 checked pair(s) verified\n"),
    ("duplicate binding", header ++ pairLine ++ pairLine ++ "check-equations: 2 checked pair(s) verified\n"),
    ("wrong count", header ++ pairLine ++ "check-equations: 0 checked pair(s) verified\n"),
    ("invalid count", header ++ "check-equations: many checked pair(s) verified\n"),
    ("different profile", pairOutput.replace profileAddress equationAddress),
    ("truncated root", pairOutput.replace rootAddress "0123"),
    ("nonhex root", pairOutput.replace rootAddress (rootAddress.replace "f" "g")),
    ("missing root comma", pairOutput.replace (rootAddress ++ ",") rootAddress),
    ("truncated definition address", pairOutput.replace definitionAddress "bbbb"),
    ("nonhex equation address", pairOutput.replace equationAddress (equationAddress.replace "c" "z")),
    ("partial pair", header ++ s!"  f {definitionAddress} ↦ f.eq_def\ncheck-equations: 1 checked pair(s) verified\n"),
    ("output after completion", pairOutput ++ "unexpected trailing output\n")]
  for (label, output) in invalid do
    expect a (!(verifiedPairs output profileAddress).isOk) s!"resource-records: accepted {label}"

private def fixtureJson : Json := Json.mkObj [
  ("name", .str "sample"),
  ("source", Json.mkObj [("path", .str "Sample.lean"), ("license", .str "MIT"), ("variant", .str "plain")]),
  ("consts", .arr #[]), ("closure", Json.mkObj [("path", .str "sample.ixe")]),
  ("equations", Json.mkObj [("path", .str "sample.equations.json")]),
  ("census", Json.mkObj [("path", .str "sample.census.json")]), ("roots", .arr #[])]

private def producerJson : Json := Json.mkObj [
  ("ix", .str "ix"), ("ix_version", .str "version")]

private def familyJson : Json := Json.mkObj [
  ("format", .str "ixcc/corpus/1"), ("family", .str "sample"), ("tier", .str "test"),
  ("phase", toJson (1 : Nat)), ("directory", .str "fixtures"), ("source_root", .str "."),
  ("lean", Json.mkObj [("version", .str "4.34.0")]), ("producer", producerJson), ("fixtures", .arr #[])]

private def metadata (a : Assert) : IO Unit := do
  expect a (← Fixture.ofJson fixtureJson).resource.isNone "resource-records: absent resource is compatible"
  expect a (← Family.ofJson familyJson).producer.profile.isNone "resource-records: absent profile is compatible"
  let resource := Json.mkObj [("profile", .str profileAddress), ("check_equations", .str "pass"), ("pairs", .arr #[])]
  expect a (← Fixture.ofJson (fixtureJson.setObjVal! "resource" resource)).resource.isSome
    "resource-records: valid optional resource"
  let profile := Json.mkObj [("path", .str "p.profile"), ("sha256", .str "digest")]
  expect a (← Family.ofJson (familyJson.setObjVal! "producer"
    (producerJson.setObjVal! "profile" profile))).producer.profile.isSome "resource-records: valid optional profile"
  for bad in [Json.null, .bool false, .str "", .arr #[], Json.mkObj []] do
    rejects a s!"malformed resource {bad.compress}"
      (Fixture.ofJson (fixtureJson.setObjVal! "resource" bad))
    rejects a s!"malformed profile {bad.compress}"
      (Family.ofJson (familyJson.setObjVal! "producer" (producerJson.setObjVal! "profile" bad)))
  rejects a "resource with non-array pairs" (Fixture.ofJson (fixtureJson.setObjVal! "resource"
    (resource.setObjVal! "pairs" (.str "not an array"))))

private def subprocesses (a : Assert) (work : FilePath) : IO Unit := do
  -- timeout bounds a regression in EOF delivery instead of hanging the suite.
  let input := "first line\nsecond line without newline"
  let (code, out, err) ← proc "timeout" #["5", "cat"] (stdin := some input)
  expect a (code == 0 && out == input && err.isEmpty) "resource-records: piped stdin must reach EOF"
  let cwd ← IO.currentDir
  let logs := work / "resource-records"
  IO.FS.createDirAll logs
  let logs ← IO.FS.realPath logs
  rejects a "nonzero verification exit" (resourceOf "false" logs "nonzero" profileAddress [] #[] cwd [])
  rejects a "zero exit without verification output" (resourceOf "true" logs "empty" profileAddress [] #[] cwd [])
  let (r, _) ← resourceOf "printf" logs "valid" profileAddress [pairJson] #["%s", pairOutput] cwd []
  expect a (r.profile == profileAddress && r.checkEquations == "pass" && r.pairs == [pair])
    "resource-records: successful verification preserves the exact pair"
  rejects a "verified pair missing from sidecar"
    (resourceOf "printf" logs "mismatch" profileAddress [] #["%s", pairOutput] cwd [])
  rejects a "partial verification output"
    (resourceOf "printf" logs "partial" profileAddress [pairJson] #["%s", header ++ pairLine] cwd [])

private def executable (name : String) : IO FilePath := do
  for dir in ((← IO.getEnv "PATH").getD "").splitOn ":" do
    let candidate := (dir : FilePath) / name
    if ← candidate.pathExists then return ← IO.FS.realPath candidate
  throw (IO.userError s!"resource-records: missing test executable {name}")

private def staleOutputs (a : Assert) (work : FilePath) : IO Unit := do
  let base := work / "stale-resource-output"
  let oldWork := base / "producer"
  let target := base / "target"
  IO.FS.createDirAll oldWork
  IO.FS.createDirAll target
  let oldWork ← IO.FS.realPath oldWork
  let target ← IO.FS.realPath target
  let f ← Fixture.ofJson fixtureJson
  let m ← Family.ofJson familyJson
  let m := { m with directory := target.toString, sourceRoot := target.toString }
  IO.FS.writeFile (target / f.source.path) "-- synthetic source; the stand-in does not compile it\n"
  -- Real decodable bytes let the former predictable-path implementation get
  -- past decoding and publish stale outputs, even with an exit-zero no-op.
  let closure ← IO.FS.readBinFile "fixtures/ownership/OS01-plain.ixe"
  let oldSidecar := "{\"equations\":[],\"failures\":[]}\n"
  for p in [s!"{f.name}.ixe", s!"{f.name}.named.ixe"] do
    IO.FS.writeBinFile (oldWork / p) closure
  for p in [s!"{f.name}.anon.equations.json", s!"{f.name}.named.equations.json"] do
    IO.FS.writeFile (oldWork / p) oldSidecar
  let sentinel := "target must survive unsuccessful rebuild\n"
  for p in [f.closure.path, f.equations.path, f.census.path] do
    IO.FS.writeFile (target / p) sentinel
  let ix ← executable "true"
  let log ← IO.mkRef #[]
  let error ← try
    let _ ← rebuildFixture { ix := some ix, work := oldWork } m f log
    pure none
  catch e => pure (some e.toString)
  expect a (error.any fun e => (e.splitOn s!"{f.name}.anon.equations.json").length > 1)
    s!"resource-records: no-op producer should fail on missing fresh sidecar, got {error.getD "success"}"
  for p in [f.closure.path, f.equations.path, f.census.path] do
    expect a ((← IO.FS.readFile (target / p)) == sentinel)
      s!"resource-records: failed rebuild replaced {p}"
  expect a ((← IO.FS.readFile (oldWork / s!"{f.name}.anon.equations.json")) == oldSidecar)
    "resource-records: stale input should be isolated, not consumed or rewritten"

private def resourceFailure : String :=
  "uncaught exception: illegal operation (error code: 1, rs_compile_env: Rust compilation failed: " ++
  "UnsupportedExpr { desc: \"resource admission Some(Address { hash: Hash(\\\"" ++ definitionAddress ++
  "\\\") }): TypeMismatch\" })\n"

/-- The same refusals as ix's Lean admission prints them. -/
private def leanFailure (error : String) : String :=
  "uncaught exception: compile refused: resource admission (some " ++ definitionAddress ++
  "): Ix.Resource.Error." ++ error ++ "\n"

private def verdictResults (a : Assert) (work : FilePath) : IO Unit := do
  let sourceFailure := "uncaught exception: source contract: Ix.Compile.SourceContractError.duplicateAnnotation `f (Ix.Compile.SourceRoot.type) 42\n"
  let recursiveFailure := "uncaught exception: resource profile: `f` is an annotated recursive definition; it is admitted only when checked through its unfolding equation (ix compile --equations --profile FILE) or assumed by the profile (assume f), never through its kernel encoding\n"
  let nativeFailure := "uncaught exception: resource profile: `f` has a native implementation (@[extern], @[implemented_by], an opaque or partial definition) and a resource contract; its Lean body is only a model, so the contract must be an explicit profile assumption (assume f)\n"
  -- as ix prints an elaboration error: positioned, its value across indented lines
  let positionedFailure := "uncaught exception: /work/src/OS05/Annotated.lean:13:0: error: " ++
    "source contract: Ix.Compile.SourceContractError.misplacedAnnotation\n  `vhead\n" ++
    "  { root := Ix.Compile.SourceRoot.body,\n    path := [Ix.Compile.SourceStep.binderBody] }\n"
  expect a (!(Own.Verdicts.completedRejection 1 (positionedFailure ++ "segmentation fault\n")).isOk)
    "resource-records: output after a positioned rejection cannot authorize it"
  for (text, stage, code) in [(resourceFailure, "resource", "TypeMismatch"),
      (leanFailure "typeMismatch", "resource", "TypeMismatch"),
      (leanFailure "usage 1 (Ixon.Uses.erased) (Ixon.Uses.many)", "resource", "Usage(1, Erased, Many)"),
      (leanFailure "unrestrictedEscape 2", "resource", "UnrestrictedEscape(2)"),
      (leanFailure "unsupported \"projection has no checked field rule\"", "resource",
        "Unsupported(\"projection has no checked field rule\")"),
      (sourceFailure, "elaboration", "duplicateAnnotation"),
      (sourceFailure.replace "exception: source" "exception: compile refused: source", "elaboration",
        "duplicateAnnotation"),
      (positionedFailure, "elaboration", "misplacedAnnotation"),
      (recursiveFailure, "profile", "annotated-recursion"), (nativeFailure, "profile", "native")] do
    let parsed := Own.Verdicts.completedRejection 1 text
    expect a (parsed.toOption.any fun p => p.verdict == "reject" && p.stage == stage && p.code == code)
      s!"resource-records: completed {stage} rejection"
  for status in ([0, 2, 124, 137, 139] : List UInt32) do
    expect a (!(Own.Verdicts.completedRejection status resourceFailure).isOk)
      s!"resource-records: failure text cannot authorize status {status}"
  for text in ["", "error: broken executable\n", resourceFailure.trimAscii.toString,
      resourceFailure ++ "segmentation fault\n", resourceFailure.replace "TypeMismatch" "Budget",
      resourceFailure.replace "TypeMismatch" "FutureUnknownFailure",
      leanFailure "budget", leanFailure "futureUnknownFailure",
      (leanFailure "typeMismatch").replace "(some " "(none ",
      sourceFailure.replace "duplicateAnnotation" "futureUnknownFailure",
      "uncaught exception: source contract: Ix.Compile.SourceContractError.duplicateAnnotation\n",
      "uncaught exception: resource profile: `f` is an annotated recursive definition\n",
      "uncaught exception: resource profile: `f` has a native implementation\n"] do
    expect a (!(Own.Verdicts.completedRejection 1 text).isOk)
      s!"resource-records: incomplete or unknown verdict accepted: {text}"
  let dir ← freshWorkDir (work / "verdict-result")
  let closure := dir / "result.ixe"
  let sidecar := dir / "result.equations.json"
  rejects a "exit zero without verdict outputs" (Own.Verdicts.compileResult 0 "" closure sidecar)
  IO.FS.writeFile closure "incomplete closure"
  IO.FS.writeFile sidecar "{}"
  rejects a "exit zero with undecodable closure" (Own.Verdicts.compileResult 0 "" closure sidecar)
  IO.FS.writeBinFile closure (← IO.FS.readBinFile "fixtures/ownership/OS01-plain.ixe")
  IO.FS.writeFile sidecar "{"
  rejects a "exit zero with incomplete sidecar" (Own.Verdicts.compileResult 0 "" closure sidecar)
  IO.FS.writeFile sidecar "{\"format\":\"ix/compile-equations/1\",\"equations\":[],\"failures\":[]}"
  expect a ((← Own.Verdicts.compileResult 0 "" closure sidecar).verdict == "ok")
    "resource-records: complete exit-zero outputs accepted"
  -- A real child may print a complete rejection and still crash or time out.
  let (status, out, err) ← proc "sh"
    #["-c", "printf '%s' \"$1\" >&2; exit 137", "verdict-standin", resourceFailure]
  rejects a "crashed process after semantic diagnostic"
    (Own.Verdicts.compileResult status (out ++ err) closure sidecar)

private def verdictInputs (a : Assert) (work : FilePath) : IO Unit := do
  let dir ← freshWorkDir (work / "verdict-input")
  let profile := dir / "sample.profile"
  IO.FS.writeFile profile "reviewed profile\n"
  let profileDigest ← IxCC.Tools.Check.sha256 profile
  let m ← Family.ofJson familyJson
  let producer := { m.producer with
    profile := some { path := profile.toString, sha256 := profileDigest } }
  let m := { m with producer }
  let f : Own.Verdicts.File := {
    description := "test"
    sourceRoot := m.sourceRoot
    manifest := "unused"
    entries := [] }
  Own.Verdicts.checkRebuildInputs f m
  expect a true "resource-records: matching rebuild inputs"
  rejects a "mismatched source root" (Own.Verdicts.checkRebuildInputs { f with sourceRoot := "other" } m)
  IO.FS.writeFile profile "unreviewed profile\n"
  rejects a "changed pinned profile" (Own.Verdicts.checkRebuildInputs f m)

private def contextRecords (a : Assert) : IO Unit := do
  let closure ← IO.FS.readBinFile "fixtures/ownership/OS01-plain.ixe"
  let profile : IxCC.Src.Resource.Profile := {}
  let bytes := profile.bytes
  let address := IxCC.Ixon.Address.blake3Pure bytes
  let hex := bytes.data.foldl (fun s b => s ++ hexDigitRepr (b.toNat / 16) ++
    hexDigitRepr (b.toNat % 16)) ""
  let metadata := Json.mkObj [
    ("resource_profile", Json.mkObj [("address", .str (toString address)), ("bytes", .str hex)]),
    ("resource_checked", .arr #[])]
  checkResourceClosure closure metadata
  expect a true "resource-records: empty pair context validates without roots"
  let badBytes := bytes.push 0
  let badAddress := IxCC.Ixon.Address.blake3Pure badBytes
  let changed := metadata.setObjVal! "resource_profile" (Json.mkObj [
    ("address", .str (toString badAddress)), ("bytes", .str (hex ++ "00"))])
  rejects a "rehashed malformed context even without roots" (checkResourceClosure closure changed)
  for bad in [Json.null, .str "", .arr #[], Json.mkObj []] do
    rejects a "malformed present profile" (checkResourceClosure closure (metadata.setObjVal! "resource_profile" bad))
  rejects a "missing companion checked records" (checkResourceClosure closure
    (Json.mkObj [("resource_profile", ← IO.ofExcept (metadata.getObjVal? "resource_profile"))]))
  rejects a "missing companion profile" (checkResourceClosure closure
    (Json.mkObj [("resource_checked", .arr #[])]))
  IxCCTests.Src.Resource.run a

def run (a : Assert) (work : FilePath) : IO (Array String) := do
  protocol a
  metadata a
  subprocesses a work
  staleOutputs a work
  verdictResults a work
  verdictInputs a work
  contextRecords a
  return #["complete verification protocol, strict metadata, subprocess exits/EOF, isolated stale outputs and verdict provenance"]

end IxCCTests.Corpus.ResourceChecks
