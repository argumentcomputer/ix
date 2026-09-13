/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean

/-! Native command regressions ported from the frozen source and claim CLI drivers.
JSON is retained for the existing command protocol and differential evidence. -/

open Lean System

namespace Tests.Certified.CLI

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty ++ "\n")

private def field (value : Json) (key : String) : Json := value.getObjValD key
private def array (value : Json) : Array Json := value.getArr?.toOption.get!
private def string (value : Json) : String := value.getStr?.toOption.get!
private def set := Json.setObjVal!

private def directories (path : FilePath) : IO (Array FilePath) := do
  let entries ← path.readDir
  let mut result := #[]
  for entry in entries do
    if ← entry.path.isDir then result := result.push entry.path
  return result.qsort (fun a b => a.toString < b.toString)

private def name (path : FilePath) : String := path.fileName.get!
private def truncate (bytes : ByteArray) := bytes.extract 0 (bytes.size / 2)
private def corrupt (bytes : ByteArray) := bytes.set! 0 (bytes[0]! ^^^ 255)
private def zeros : Json := .str (String.ofList (List.replicate 64 '0'))

private def check (executable : String) (directory : FilePath) (source : ByteArray)
    (request : Json) (expected : Bool) (mode : Option String := none)
    (envelope : ByteArray := ByteArray.empty) : IO Json := do
  IO.FS.createDirAll directory
  let sourcePath := directory / "source.ixe"
  let requestPath := directory / "request.json"
  IO.FS.writeBinFile sourcePath source
  writeJson requestPath request
  let (args, success) ← match mode with
    | some mode => pure (#[mode, sourcePath.toString, requestPath.toString],
        Json.mkObj [("accepted", .bool true), ("mode", .str mode)])
    | none => do
      let envelopePath := directory / "envelope.bin"
      IO.FS.writeBinFile envelopePath envelope
      pure (#[sourcePath.toString, envelopePath.toString, requestPath.toString],
        Json.mkObj [("accepted", .bool true), ("address", field request "address")])
  let result ← IO.Process.output { cmd := "timeout", args := #["60", executable] ++ args }
  IO.FS.writeFile (directory / "stdout.txt") result.stdout
  IO.FS.writeFile (directory / "stderr.txt") result.stderr
  unless result.exitCode == 0 || result.exitCode == 1 do
    throw (IO.userError s!"abnormal exit {directory}: {result.exitCode}\n{result.stderr}")
  let accepted := result.exitCode == 0
  unless accepted == expected do
    throw (IO.userError s!"unexpected acceptance {directory}: {accepted}\n{result.stderr}")
  if accepted then
    unless (← IO.ofExcept (Json.parse result.stdout)) == success do
      throw (IO.userError s!"incorrect success output {directory}: {result.stdout}")
  else unless result.stdout.trimAscii.isEmpty do
    throw (IO.userError s!"rejected command printed a success result {directory}: {result.stdout}")
  return Json.mkObj [("accepted", .bool accepted), ("exitCode", toJson result.exitCode.toNat)]

private def acceptedCount (records : Array Json) : Nat :=
  (records.filter (fun record => field record "accepted" == .bool true)).size

private def finish (output : FilePath) (records : Array Json) (fields : List (String × Json)) : IO Unit := do
  writeJson (output / "results.json") (.arr records)
  let report := Json.mkObj (fields ++ [
    ("rejected", toJson (records.size - acceptedCount records)), ("unexpectedErrors", toJson (0 : Nat))])
  writeJson (output / "summary.json") report
  IO.println report.compress

private def sourceTests (executable : String) (inputs output : FilePath) : IO Unit := do
  let cases ← directories inputs
  unless cases.size == 42 do throw (IO.userError "expected the 42-case source corpus")
  let mut records := #[]
  for directory in cases do
    let bytes ← IO.FS.readBinFile (directory / "source.ixe")
    let request ← readJson (directory / "request.json")
    let objects := array (field request "objects")
    let mut variants := #[
      ("valid", bytes, request, true),
      ("missing-target", bytes, set request "objects" (.arr (objects.filter (· != field request "target"))), false),
      ("duplicate-object", bytes, set request "objects" (.arr (objects.push objects[0]!)), false),
      ("wrong-false-pin", bytes, set request "falseType" (field request "target"), false),
      ("malformed-address", bytes, set request "falseElim" (.str "01"), false),
      ("truncated-source", truncate bytes, request, false),
      ("invalid-header", corrupt bytes, request, false)]
    if field request "natType" != .null then
      variants := variants.push ("missing-nat-pin", bytes, set request "natType" .null, false)
    for (scenario, source, requested, expected) in variants do
      for mode in #["proof", "store"] do
        let record ← check executable (output / name directory / scenario / mode)
          source requested expected (some mode)
        records := records.push (set (set (set record "case" (.str (name directory)))
          "scenario" (.str scenario)) "mode" (.str mode))
    let record ← check executable (output / name directory / "unsupported-mode" / "infer-only")
      bytes request false (some "infer-only")
    records := records.push (set (set (set record "case" (.str (name directory)))
      "scenario" (.str "unsupported-mode")) "mode" (.str "infer-only"))
  unless acceptedCount records == 84 do throw (IO.userError "missing source success coverage")
  finish output records [("cases", toJson cases.size), ("proofAccepted", toJson (42 : Nat)),
    ("storesAccepted", toJson (42 : Nat))]

private def claimTests (executable : String) (inputs output : FilePath) : IO Unit := do
  let cases ← directories inputs
  let required := #["cycle-A-assuming-B", "cycle-B-assuming-A", "cycle-closed-AB", "cycle-closed-BA",
    "cycle-own-assumption", "contains-padding", "contains-as-logical"]
  unless cases.size ≥ 1500 && required.all (fun x => (cases.map name).contains x) do
    throw (IO.userError "expected complete claim, cycle, catalog and structural coverage")
  let mut records := #[]
  for directory in cases do
    let source ← IO.FS.readBinFile (directory / "source.ixe")
    let envelope ← IO.FS.readBinFile (directory / "envelope.bin")
    let request ← readJson (directory / "request.json")
    let expected := field (← readJson (directory / "expected.json")) "accepted" == .bool true
    let record ← check executable (output / name directory / "original") source request expected none envelope
    records := records.push (set (set (set record "case" (.str (name directory)))
      "scenario" (.str "original")) "kind" (field request "kind"))
    unless expected do continue
    let mut variants := #[
      ("wrong-digest", source, envelope, set request "address" zeros),
      ("short-address", source, envelope, set request "address" (.str "01")),
      ("unsupported-kind", source, envelope, set request "kind" (.str "infer-only")),
      ("changed-envelope", source, corrupt envelope, request),
      ("trailing-envelope", source, envelope.push 0, request),
      ("truncated-envelope", source, truncate envelope, request),
      ("truncated-source", truncate source, envelope, request)]
    if field request "kind" == .str "logical" then
      let objects := array (field request "objects")
      variants := variants.push ("duplicate-object", source, envelope,
        set request "objects" (.arr (objects.push objects[0]!)))
      variants := variants.push ("missing-leaves", source, envelope, set request "leaves" (.arr #[]))
      if field request "axioms" != .null then
        variants := variants.push ("omitted-logical-axioms", source, envelope, set request "axioms" .null)
      for key in #["subjects", "members", "frontier", "axioms"] do
        if field request key != .null then
          variants := variants.push (s!"trailing-{key}", source, envelope,
            set request key (.str (string (field request key) ++ "00")))
      let leaves := array (field request "leaves")
      let leaf := leaves[0]!
      variants := variants.push ("trailing-leaf-claim", source, envelope,
        set request "leaves" (.arr (leaves.set! 0
          (set leaf "claim" (.str (string (field leaf "claim") ++ "00"))))))
    for (scenario, changedSource, changedEnvelope, changedRequest) in variants do
      let record ← check executable (output / name directory / scenario)
        changedSource changedRequest false none changedEnvelope
      records := records.push (set (set (set record "case" (.str (name directory)))
        "scenario" (.str scenario)) "kind" (field changedRequest "kind"))
  unless acceptedCount records ≥ 500 do throw (IO.userError "missing claim nonvacuity coverage")
  finish output records [("cases", toJson cases.size), ("accepted", toJson (acceptedCount records))]

private def modelVariants (request : Json) : Array (String × Json) := Id.run do
  let models := array (field request "models")
  let model := models[0]!
  let recursors := array (field model "recursors")
  let targets := array (field model "targets")
  let withoutModels := match request with
    | .obj fields => Json.obj (fields.erase "models")
    | _ => request
  let mut variants := #[("missing-models", withoutModels),
    ("malformed-models", set request "models" (.bool true))]
  let edits := #[
    ("unknown-model-source", "source", zeros), ("short-model-address", "source", .str "01"),
    ("recursor-order", "recursors", .arr recursors.reverse),
    ("target-order", "targets", .arr targets.reverse),
    ("missing-target", "targets", .arr targets.pop),
    ("circular-target", "targets", .arr (targets.set! (targets.size - 1) recursors.back!)),
    ("unknown-target", "targets", .arr (targets.set! (targets.size - 1) zeros)),
    ("unknown-recursor", "recursors", .arr (recursors.set! (recursors.size - 1) zeros)),
    ("missing-recursor", "recursors", .arr (recursors.extract 1 recursors.size))]
  for (scenario, key, value) in edits do
    variants := variants.push (scenario, set request "models" (.arr (models.set! 0 (set model key value))))
  let rulesArray := array (field model "proofs")
  unless rulesArray.isEmpty do
    let rules := rulesArray[0]!
    let proofs := array (field rules "proofs")
    for scenario in #["wrong-equation-owner", "wrong-equation-proof", "wrong-equality-family",
        "wrong-reflexivity", "wrong-equality-eliminator", "malformed-proof-list"] do
      let changed := if scenario == "wrong-equation-owner" then set rules "owner" recursors.back!
        else if scenario == "malformed-proof-list" then set rules "proofs" (.bool true)
        else Id.run do
          let index := proofs.findIdx? (· != .null) |>.get!
          let key := if scenario == "wrong-equation-proof" then "proof"
            else if scenario == "wrong-equality-family" then "equality"
            else if scenario == "wrong-reflexivity" then "reflexivity" else "eliminator"
          return set rules "proofs" (.arr (proofs.set! index (set proofs[index]! key targets[0]!)))
      let changedModel := set model "proofs" (.arr (rulesArray.set! 0 changed))
      variants := variants.push (scenario, set request "models" (.arr (models.set! 0 changedModel)))
  return variants

private def positives := #["mutual-unequal", "mutual-permuted", "auxiliary-merged", "nested-parameter",
  "nested-recursive-Pi", "propositional-equations"]

private def modeledTests (sourceExe claimExe : String) (inputs output : FilePath) : IO Unit := do
  let sourceCases ← directories (inputs / "source")
  let claimCases ← directories (inputs / "claims")
  let mut records := #[]
  let mut acceptedSources := #[]
  for directory in sourceCases do
    let source ← IO.FS.readBinFile (directory / "source.ixe")
    let request ← readJson (directory / "request.json")
    let expected ← readJson (directory / "expected.json")
    if field expected "proof" == .bool true && field expected "store" == .bool true then
      acceptedSources := acceptedSources.push (name directory)
    for mode in #["proof", "store"] do
      let accept := field expected mode == .bool true
      let mut variants := #[("original", source, request, accept)]
      if accept then
        variants := variants ++ (modelVariants request).map (fun (scenario, changed) =>
          (scenario, source, changed, false))
        variants := variants.push ("truncated-source", truncate source, request, false)
      for (scenario, changedSource, changedRequest, accept) in variants do
        let record ← check sourceExe (output / "source" / name directory / scenario / mode)
          changedSource changedRequest accept (some mode)
        records := records.push (set (set (set (set record "kind" (.str "source"))
          "case" (.str (name directory))) "scenario" (.str scenario)) "mode" (.str mode))
  unless sourceCases.size == 44 && acceptedSources.qsort (· < ·) == positives.qsort (· < ·) do
    throw (IO.userError "missing complete modeled source controls")
  let mut acceptedClaims := #[]
  for directory in claimCases do
    let source ← IO.FS.readBinFile (directory / "source.ixe")
    let envelope ← IO.FS.readBinFile (directory / "envelope.bin")
    let request ← readJson (directory / "request.json")
    let expected := field (← readJson (directory / "expected.json")) "accepted" == .bool true
    let mut variants := #[("original", envelope, request, expected)]
    if expected then
      acceptedClaims := acceptedClaims.push (name directory)
      variants := variants ++ (modelVariants request).map (fun (scenario, changed) =>
        (scenario, envelope, changed, false))
      variants := variants.push ("changed-public-bytes", corrupt envelope, request, false)
      variants := variants.push ("trailing-public-bytes", envelope.push 0, request, false)
    for (scenario, changedEnvelope, changedRequest, accept) in variants do
      let record ← check claimExe (output / "claims" / name directory / scenario / "claim")
        source changedRequest accept none changedEnvelope
      records := records.push (set (set (set (set record "kind" (.str "claims"))
        "case" (.str (name directory))) "scenario" (.str scenario)) "mode" .null)
  let requiredClaims := positives.flatMap (fun caseName =>
    #["check", "environment", "shared-model"].map (fun kind => s!"{caseName}-{kind}"))
  unless claimCases.size == 74 && acceptedClaims.qsort (· < ·) == requiredClaims.qsort (· < ·) do
    throw (IO.userError "missing complete modeled claim controls")
  finish output records [("sourceCases", toJson sourceCases.size), ("claimCases", toJson claimCases.size),
    ("accepted", toJson (acceptedCount records))]

end Tests.Certified.CLI

def main (args : List String) : IO UInt32 := do
  match args with
  | [kind, sourceExe, claimExe, inputs, output] =>
    match kind with
    | "source" => Tests.Certified.CLI.sourceTests sourceExe inputs output
    | "claims" => Tests.Certified.CLI.claimTests claimExe inputs output
    | "modeled" => Tests.Certified.CLI.modeledTests sourceExe claimExe inputs output
    | _ => throw (IO.userError s!"unknown corpus: {kind}")
    return 0
  | _ =>
    IO.eprintln "usage: certified-cli-tests (source|claims|modeled) SOURCE_EXE CLAIM_EXE INPUTS OUTPUTS"
    return 2
