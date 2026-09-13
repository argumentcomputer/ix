/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.InputText

/-! File input for the certified commands. Binary Ixon is the default;
readable `.ixon` data uses the same Lean request and envelope types. JSON
requests remain an explicit compatibility format for the frozen CLI corpus.
All input formats reach the same certified acceptance functions.
-/

namespace Ix.Certified.CLI

inductive Format where
  | binary
  | text
  | json
  deriving BEq, Repr

structure Options where
  requestFormat : Format := .binary
  envelopeFormat : Format := .binary
  positional : List String := []
  help : Bool := false
  deriving Repr

private def readFormat (envelope : Bool) : String → Except String Format
  | "binary" => .ok .binary
  | "text" => .ok .text
  | "json" => if envelope then .error "envelope format must be binary or text" else .ok .json
  | _ => .error (if envelope then "envelope format must be binary or text"
      else "request format must be binary, text or json")

def parseArgs (claim : Bool) (args : List String) : Except String Options :=
  go args {} false false
where
  go : List String → Options → Bool → Bool → Except String Options
    | [], options, _, _ => .ok options
    | "--" :: rest, options, _, _ => .ok { options with positional := options.positional ++ rest }
    | "--help" :: _, options, _, _
    | "-h" :: _, options, _, _ => .ok { options with help := true }
    | "--request-format" :: value :: rest, options, requestSeen, envelopeSeen => do
      if requestSeen then throw "duplicate --request-format"
      let format ← readFormat false value
      go rest { options with requestFormat := format } true envelopeSeen
    | ["--request-format"], _, _, _ => .error "--request-format requires a value"
    | "--envelope-format" :: value :: rest, options, requestSeen, envelopeSeen => do
      unless claim do throw "--envelope-format is only available for certified-claim-check"
      if envelopeSeen then throw "duplicate --envelope-format"
      let format ← readFormat true value
      go rest { options with envelopeFormat := format } requestSeen true
    | ["--envelope-format"], _, _, _ => .error "--envelope-format requires a value"
    | arg :: rest, options, requestSeen, envelopeSeen => do
      if arg.startsWith "--request-format=" then
        if requestSeen then throw "duplicate --request-format"
        let format ← readFormat false (arg.dropPrefix "--request-format=" |>.toString)
        go rest { options with requestFormat := format } true envelopeSeen
      else if arg.startsWith "--envelope-format=" then
        unless claim do throw "--envelope-format is only available for certified-claim-check"
        if envelopeSeen then throw "duplicate --envelope-format"
        let format ← readFormat true (arg.dropPrefix "--envelope-format=" |>.toString)
        go rest { options with envelopeFormat := format } requestSeen true
      else if arg.startsWith "-" then throw s!"unknown option: {arg}"
      else go rest { options with positional := options.positional ++ [arg] } requestSeen envelopeSeen

def sourceUsage : String :=
  "usage: certified-check [--request-format binary|text|json] proof|store SOURCE.ixe REQUEST\n" ++
  "  binary (default): Ixon request bytes; text: a typed .ixon data definition\n" ++
  "  json: legacy request compatibility"

def claimUsage : String :=
  "usage: certified-claim-check [--request-format binary|text|json] " ++
  "[--envelope-format binary|text] SOURCE.ixe ENVELOPE REQUEST\n" ++
  "  binary (default): Ixon bytes; text: a typed .ixon data definition\n" ++
  "  request and envelope formats are independent; json is legacy request compatibility"

def readSourceRequest (format : Format) (path : System.FilePath) : IO (Except String Command.Request) := do
  match format with
  | .binary => return Command.Request.ofIxon (← IO.FS.readBinFile path)
  | .text => return Command.Request.ofText (← IO.FS.readFile path)
  | .json =>
    let text ← IO.FS.readFile path
    return Lean.Json.parse text >>= Command.readRequest

def readClaimRequest (format : Format) (path : System.FilePath) : IO (Except String ClaimCommand.Request) := do
  match format with
  | .binary => return ClaimCommand.Request.ofIxon (← IO.FS.readBinFile path)
  | .text => return ClaimCommand.Request.ofText (← IO.FS.readFile path)
  | .json =>
    let text ← IO.FS.readFile path
    return Lean.Json.parse text >>= ClaimCommand.readRequest

/-- Binary input retains the original bytes for authentication. Text input
denotes an envelope whose canonical Ixon encoding is the authenticated object. -/
def readEnvelope (format : Format) (path : System.FilePath) : IO (Except String ByteArray) := do
  match format with
  | .binary => return .ok (← IO.FS.readBinFile path)
  | .text => return Envelope.toIxon <$> Envelope.ofText (← IO.FS.readFile path)
  | .json => return .error "envelope format must be binary or text"

end Ix.Certified.CLI

namespace Ix.Certified.Command

def main (args : List String) : IO UInt32 := do
  let parsed := CLI.parseArgs false args
  let .ok options := parsed | do
    match parsed with
    | .error error => IO.eprintln error
    | .ok _ => pure ()
    IO.eprintln CLI.sourceUsage
    return 2
  if options.help then IO.println CLI.sourceUsage; return 0
  let [mode, sourcePath, requestPath] := options.positional | do
    IO.eprintln CLI.sourceUsage
    return 2
  try
    let bytes ← IO.FS.readBinFile sourcePath
    let parsed ← CLI.readSourceRequest options.requestFormat requestPath
    let result := do
      let request ← parsed
      let parts ← Ixon.deEnvVerifiedLazy bytes
      run.{0} mode 6400 parts.env request
    match result with
    | .error error => IO.eprintln error; return 1
    | .ok () =>
      IO.println <| (Lean.Json.mkObj [("accepted", Lean.toJson true), ("mode", Lean.toJson mode)]).compress
      return 0
  catch error => IO.eprintln error; return 1

end Ix.Certified.Command

namespace Ix.Certified.ClaimCommand

def main (args : List String) : IO UInt32 := do
  let parsed := CLI.parseArgs true args
  let .ok options := parsed | do
    match parsed with
    | .error error => IO.eprintln error
    | .ok _ => pure ()
    IO.eprintln CLI.claimUsage
    return 2
  if options.help then IO.println CLI.claimUsage; return 0
  let [sourcePath, envelopePath, requestPath] := options.positional | do
    IO.eprintln CLI.claimUsage
    return 2
  try
    let sourceBytes ← IO.FS.readBinFile sourcePath
    let envelope ← CLI.readEnvelope options.envelopeFormat envelopePath
    let parsed ← CLI.readClaimRequest options.requestFormat requestPath
    let result := do
      let request ← parsed
      let envelope ← envelope
      let parts ← Ixon.deEnvVerifiedLazy sourceBytes
      run.{0} 6400 parts.env envelope request
      return request.address
    match result with
    | .error error => IO.eprintln error; return 1
    | .ok address =>
      IO.println <| (Lean.Json.mkObj [("accepted", Lean.toJson true),
        ("address", Lean.toJson (hexOfBytes address.hash))]).compress
      return 0
  catch error => IO.eprintln error; return 1

end Ix.Certified.ClaimCommand
