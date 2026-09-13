/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.CLI
import Tests.Certified.ImportManifest

/-! Binary/text roundtrips over the frozen source, claim, and modeled corpora,
plus process regressions for format selection and malformed transport inputs.
Equality compares all typed fields, independently of their encoded bytes.
-/

open Ix.Certified System Lean

deriving instance BEq for Profile, Protocol, InputSelection, ModelProofHint,
  ModelRuleHints, ModelHint, Command.Request, LeafHint, LogicalHint,
  RevealWitness, ClaimCommand.Hint, ClaimCommand.Request, Envelope

namespace Tests.Certified.Inputs

private def need (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def sourceRequest (directory : FilePath) : IO Command.Request := do
  IO.ofExcept (Command.readRequest (← readJson (directory / "request.json")))

private def claimRequest (directory : FilePath) : IO ClaimCommand.Request := do
  IO.ofExcept (ClaimCommand.readRequest (← readJson (directory / "request.json")))

private def directories (path : FilePath) : IO (Array FilePath) := do
  let mut result := #[]
  for entry in ← path.readDir do
    if ← entry.path.isDir then result := result.push entry.path
  return result.qsort (fun a b => a.toString < b.toString)

private def roundtrip [BEq α] (label : String) (expected : α) (actual : Except String α) : IO Unit := do
  let value ← IO.ofExcept (actual.mapError (fun error => s!"{label}: {error}"))
  need (value == expected) s!"{label}: decoded fields differ"

private def rejected (label : String) (actual : Except String α) : IO Unit :=
  need (!actual.isOk) s!"{label}: malformed input accepted"

private def sourceRoundtrip (directory : FilePath) : IO Unit := do
  let request ← sourceRequest directory
  roundtrip s!"{directory}: binary" request (Command.Request.ofIxon request.toIxon)
  roundtrip s!"{directory}: text" request (Command.Request.ofText request.toText)

private def claimRoundtrip (directory : FilePath) : IO Unit := do
  let request ← claimRequest directory
  roundtrip s!"{directory}: binary" request (ClaimCommand.Request.ofIxon request.toIxon)
  roundtrip s!"{directory}: text" request (ClaimCommand.Request.ofText request.toText)
  let bytes ← IO.FS.readBinFile (directory / "envelope.bin")
  let envelope ← IO.ofExcept (Envelope.ofIxon bytes)
  need (envelope.toIxon == bytes) s!"{directory}: public envelope bytes changed"
  roundtrip s!"{directory}: envelope" envelope (Envelope.ofText envelope.toText)
  let decoded ← IO.ofExcept (Envelope.ofText envelope.toText)
  need (decoded.toIxon == bytes) s!"{directory}: text changed the authenticated object"

private def malformedSource (request : Command.Request) : IO Unit := do
  let bytes := request.toIxon
  let header := RequestCodec.magic.size
  let optionOffset := header + 2 + 64
  let countOffset := optionOffset + 1 + (if request.profile.natType.isSome then 32 else 0) + 32
  let hugeCount := ByteArray.mk #[0x87, 255, 255, 255, 255, 255, 255, 255, 255]
  let variants := #[
    ("empty", ByteArray.empty), ("trailing", bytes.push 0),
    ("truncated", bytes.extract 0 (bytes.size - 1)),
    ("bad magic", bytes.set! 0 0), ("unsupported version", bytes.set! header 2),
    ("wrong kind", bytes.set! (header + 1) 1),
    ("noncanonical version", bytes.extract 0 header ++ ⟨#[0x80, 1]⟩ ++ bytes.extract (header + 1) bytes.size),
    ("invalid option", bytes.set! optionOffset 2),
    ("unbounded count", bytes.extract 0 countOffset ++ hugeCount ++ bytes.extract (countOffset + 1) bytes.size),
    ("oversize", ByteArray.mk (Array.replicate (RequestCodec.maxBytes + 1) 0))]
  for (label, changed) in variants do rejected label (Command.Request.ofIxon changed)
  let text := request.toText
  for (label, changed) in #[
      ("trailing definition", text ++ "\ndef extra : Nat := 0\n"),
      ("unsafe definition", text.replace "def request" "unsafe def request"),
      ("partial definition", text.replace "def request" "partial def request"),
      ("wrong type", text.replace "def request : Ix.Certified.Command.Request"
        "def request : Ix.Certified.ClaimCommand.Request"),
      ("unknown constructor", text.replace "Ix.Certified.Command.Request.mk" "Unknown.mk"),
      ("short address", text.replace (hexOfBytes request.profile.falseType.hash) "01"),
      ("import", "import #" ++ hexOfBytes request.target.hash ++ "\n" ++ text),
      ("unsupported grammar", "ixon 999\n" ++ text)] do
    rejected label (Command.Request.ofText changed)
  roundtrip "text comments" request
    (Command.Request.ofText ("/- input comment -/\n" ++ text ++ "\n-- trailing comment\n"))

private def malformedClaim (request : ClaimCommand.Request) (envelope : Envelope) : IO Unit := do
  let bytes := request.toIxon
  rejected "claim trailing bytes" (ClaimCommand.Request.ofIxon (bytes.push 0))
  rejected "claim truncation" (ClaimCommand.Request.ofIxon (bytes.extract 0 (bytes.size - 1)))
  rejected "claim kind confusion" (Command.Request.ofIxon bytes)
  rejected "claim invalid hint" (ClaimCommand.Request.ofIxon
    (bytes.set! (RequestCodec.magic.size + 2 + 32) 255))
  rejected "claim text type confusion" (Command.Request.ofText request.toText)
  rejected "envelope trailing bytes" (Envelope.ofIxon (envelope.toIxon.push 0))
  rejected "envelope truncated bytes"
    (Envelope.ofIxon (envelope.toIxon.extract 0 (envelope.toIxon.size - 1)))
  rejected "envelope integer overflow" (Envelope.ofText
    (envelope.toText.replace "UInt64.ofNat 1" "UInt64.ofNat 18446744073709551616"))

private def process (executable : String) (args : Array String) (expected : UInt32)
    (success : Option Json := none) : IO Unit := do
  let result ← IO.Process.output { cmd := "timeout", args := #["30", executable] ++ args }
  need (result.exitCode == expected)
    s!"{executable} {args}: expected exit {expected}, got {result.exitCode}\n{result.stderr}"
  if let some expected := success then
    need ((← IO.ofExcept (Json.parse result.stdout)) == expected) "incorrect acceptance record"
  else if expected != 0 then
    need result.stdout.trimAscii.isEmpty "rejected input printed an acceptance record"

private def writeSource (directory : FilePath) (source : ByteArray) (request : Command.Request) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "source.ixe") source
  IO.FS.writeBinFile (directory / "request.ix") request.toIxon
  IO.FS.writeFile (directory / "request.ixon") request.toText

private def writeClaim (directory : FilePath) (source : ByteArray)
    (request : ClaimCommand.Request) (envelope : Envelope) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "source.ixe") source
  IO.FS.writeBinFile (directory / "request.ix") request.toIxon
  IO.FS.writeFile (directory / "request.ixon") request.toText
  IO.FS.writeBinFile (directory / "envelope.ix") envelope.toIxon
  IO.FS.writeFile (directory / "envelope.ixon") envelope.toText

private def formats : Array (String × String) := #[("binary", "ix"), ("text", "ixon")]

private def sourceCLI (fixture output : FilePath) : IO Unit := do
  let source ← IO.FS.readBinFile (fixture / "source.ixe")
  let request ← sourceRequest fixture
  let good := output / "source"
  let bad := output / "bad-source"
  writeSource good source request
  writeSource bad source { request with profile := { request.profile with falseType := request.target } }
  malformedSource request
  for (format, extension) in formats do
    for mode in #["proof", "store"] do
      for (directory, accepted) in #[(good, true), (bad, false)] do
        let args := #[mode, (directory / "source.ixe").toString,
          (directory / s!"request.{extension}").toString, s!"--request-format={format}"]
        let success := if accepted then some (Json.mkObj [("accepted", .bool true), ("mode", .str mode)]) else none
        process ".lake/build/bin/certified-check" args (if accepted then 0 else 1) success
  let success := Json.mkObj [("accepted", .bool true), ("mode", .str "proof")]
  process ".lake/build/bin/certified-check"
    #["proof", (good / "source.ixe").toString, (good / "request.ix").toString] 0 (some success)
  process ".lake/build/bin/certified-check"
    #["proof", (good / "source.ixe").toString, (good / "request.ixon").toString] 1
  process ".lake/build/bin/certified-check"
    #["--request-format", "text", "proof", (good / "source.ixe").toString, (good / "request.ix").toString] 1

private def claimCLI (fixture output : FilePath) : IO Unit := do
  let source ← IO.FS.readBinFile (fixture / "source.ixe")
  let request ← claimRequest fixture
  let envelope ← IO.ofExcept (Envelope.ofIxon (← IO.FS.readBinFile (fixture / "envelope.bin")))
  let good := output / "good"
  let bad := output / "bad"
  let old := output / "unsupported-version"
  writeClaim good source request envelope
  writeClaim bad source { request with address := Address.blake3 "wrong digest".toUTF8 } envelope
  let oldEnvelope := { envelope with protocol := { envelope.protocol with checker := 1 } }
  writeClaim old source { request with address := Address.blake3 oldEnvelope.toIxon } oldEnvelope
  malformedClaim request envelope
  for (requestFormat, requestExtension) in formats do
    for (envelopeFormat, envelopeExtension) in formats do
      for (directory, accepted) in #[(good, true), (bad, false), (old, false)] do
        let args := #["--request-format", requestFormat, s!"--envelope-format={envelopeFormat}",
          (directory / "source.ixe").toString, (directory / s!"envelope.{envelopeExtension}").toString,
          (directory / s!"request.{requestExtension}").toString]
        let success := if accepted then some (Json.mkObj [("accepted", .bool true),
          ("address", .str (hexOfBytes request.address.hash))]) else none
        process ".lake/build/bin/certified-claim-check" args (if accepted then 0 else 1) success
  IO.FS.writeBinFile (good / "trailing.ix") (envelope.toIxon.push 0)
  process ".lake/build/bin/certified-claim-check" #[(good / "source.ixe").toString,
    (good / "trailing.ix").toString, (good / "request.ix").toString] 1
  let success := Json.mkObj [("accepted", .bool true), ("address", .str (hexOfBytes request.address.hash))]
  process ".lake/build/bin/certified-claim-check" #[(good / "source.ixe").toString,
    (good / "envelope.ix").toString, (good / "request.ix").toString] 0 (some success)

private def flagErrors : IO Unit := do
  for executable in #["certified-check", "certified-claim-check"] do
    let executable := s!".lake/build/bin/{executable}"
    process executable #["--help"] 0
    for args in #[#[], #["--unknown"], #["--request-format"],
        #["--request-format", "garbage"], #["--request-format=json", "--request-format", "text"]] do
      process executable args 2
  process ".lake/build/bin/certified-check" #["--envelope-format", "text"] 2
  process ".lake/build/bin/certified-claim-check" #["--envelope-format", "json"] 2

private def run (frozen output : FilePath) : IO Unit := do
  let sources ← directories (frozen / "evidence/c5/inputs")
  let modeledSources ← directories (frozen / "evidence/c7/modeled-inputs/source")
  let claims ← directories (frozen / "evidence/c7/claim-inputs")
  let modeledClaims ← directories (frozen / "evidence/c7/modeled-inputs/claims")
  need (sources.size == 42 && modeledSources.size == 44 && claims.size == 1578 && modeledClaims.size == 74)
    "incomplete transport fixture coverage"
  for directory in sources ++ modeledSources do sourceRoundtrip directory
  for directory in claims ++ modeledClaims do claimRoundtrip directory
  IO.println "Typed binary/text roundtrips passed: 86 source requests, 1,652 claim requests and envelopes."
  sourceCLI (frozen / "evidence/c5/inputs/identity") output
  let mut selected : Array String := #[]
  for directory in claims do
    let request ← claimRequest directory
    let kind := match request.hint with
      | .logical _ => "logical" | .contains _ => "contains" | .reveal _ => "reveal"
    if selected.contains kind then continue
    let expected ← readJson (directory / "expected.json")
    unless (← IO.ofExcept (expected.getObjValAs? Bool "accepted")) do continue
    claimCLI directory (output / kind)
    selected := selected.push kind
  need (selected.size == 3) "missing logical, membership, or revelation process coverage"
  flagErrors
  IO.println "Certified input format, malformed input, digest, version, and CLI regressions passed."

private def examples (frozen output : FilePath) : IO Unit := do
  let source := frozen / "evidence/c5/inputs/identity"
  writeSource (output / "source") (← IO.FS.readBinFile (source / "source.ixe")) (← sourceRequest source)
  for directory in ← directories (frozen / "evidence/c7/claim-inputs") do
    let request ← claimRequest directory
    let .logical _ := request.hint | continue
    let expected ← readJson (directory / "expected.json")
    unless (← IO.ofExcept (expected.getObjValAs? Bool "accepted")) do continue
    let envelope ← IO.ofExcept (Envelope.ofIxon (← IO.FS.readBinFile (directory / "envelope.bin")))
    writeClaim (output / "claim") (← IO.FS.readBinFile (directory / "source.ixe")) request envelope
    break
  IO.println s!"Wrote Lean-typed Ixon inputs in binary and text form to {output}."

private def withArchive (action : FilePath → IO Unit) : IO Unit := do
  let archive := Tests.Certified.ImportManifest.archive
  let digest ← IO.Process.output { cmd := "sha256sum", args := #["--", archive] }
  need (digest.exitCode == 0 && (digest.stdout.splitOn " ").headD "" ==
    Tests.Certified.ImportManifest.archiveSha256) "frozen adapter archive identity changed"
  IO.FS.withTempDir fun directory => do
    let unpack ← IO.Process.output {
      cmd := "tar", args := #["-xzf", archive, "--no-same-owner", "--no-same-permissions", "-C", directory.toString] }
    need (unpack.exitCode == 0) unpack.stderr
    action directory

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    withArchive fun frozen => IO.FS.withTempDir (run frozen)
    return 0
  | ["--examples", output] =>
    withArchive fun frozen => examples frozen output
    return 0
  | [frozen, output] =>
    run frozen output
    return 0
  | _ =>
    IO.eprintln "usage: certified-input-tests [FROZEN OUTPUT | --examples OUTPUT]"
    return 2

end Tests.Certified.Inputs

def main := Tests.Certified.Inputs.main
