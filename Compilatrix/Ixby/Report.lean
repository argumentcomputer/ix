import Compilatrix.Ixby.Source
import Compilatrix.Ixby.Wire
import Compilatrix.IxIR0.Serialize
import Lean

namespace Compilatrix.Ixby

open Lean

def Data.json : Data → Json
  | .nat n => Json.mkObj [("nat", toJson (toString n))]
  | .str s => Json.mkObj [("str", toJson s)]
  | .ctor address tag fields => Json.mkObj [
      ("address", toJson address.toHex), ("tag", toJson tag),
      ("fields", Json.arr (fields.map Data.json).toArray)]
  | .erased => Json.mkObj [("erased", toJson true)]

def byteHex (bytes : Array UInt8) : String :=
  bytes.foldl (fun output byte => output ++ hexDigitRepr (byte.toNat / 16) ++
    hexDigitRepr (byte.toNat % 16)) ""

def Source.json (source : Source) : Json := Json.mkObj [
  ("format", toJson "compilatrix/ixby-source/1"),
  ("parameters", toJson source.parameters), ("main", toJson (byteHex source.main.bytes.data)),
  ("declarations", toJson (source.declarations.map fun (address, decl) =>
    Json.mkObj [("address", toJson address.toHex), ("bytes", toJson (byteHex decl.preimage.data))]))]

structure Bundle where
  profile : Array UInt8
  program : Array UInt8
  input : Array UInt8
  output : Array UInt8

def ByteCertificate.bundle {source config compiled profile exported input depth}
    (certificate : @ByteCertificate source config compiled profile exported input depth) : Bundle :=
  { profile := exported.profileBytes, program := exported.programBytes,
    input := certificate.inputBytes, output := certificate.execution.outputBytes }

structure ReportCase where
  name : String
  origin : String
  source : Json
  program : String
  result : Data
  functions : Nat
  blocks : Nat
  bundle : Option Bundle := none

def reportCase {source config compiled input depth}
    (certificate : @RunCertificate source config compiled input depth)
    (name origin : String) (bundle : Option Bundle := none) : ReportCase :=
  { name, origin, source := source.json, program := reprStr compiled.program,
    result := certificate.result, functions := compiled.program.functions.size,
    blocks := compiled.program.functions.foldl (fun n fn => n + fn.blocks.size) 0, bundle }

def ReportCase.row (result : ReportCase) : Json := Json.mkObj [
  ("name", toJson result.name), ("origin", toJson result.origin),
  ("result", result.result.json), ("functions", toJson result.functions),
  ("blocks", toJson result.blocks),
  ("wire", match result.bundle with
    | none => Json.null
    | some bundle => Json.mkObj [
        ("profile_bytes", toJson bundle.profile.size), ("program_bytes", toJson bundle.program.size),
        ("input_bytes", toJson bundle.input.size), ("output_bytes", toJson bundle.output.size),
        ("program_blake3", toJson (byteHex (Ix.Ixby.Blake3.hash bundle.program)))])]

def writeCase (directory : System.FilePath) (result : ReportCase) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "source.json") (result.source.pretty 100 ++ "\n")
  IO.FS.writeFile (directory / "program.txt") (result.program ++ "\n")
  IO.FS.writeFile (directory / "result.json") (result.row.pretty 100 ++ "\n")
  if let some bundle := result.bundle then
    for (name, bytes) in [("profile.ixfp", bundle.profile), ("program.ixby", bundle.program),
        ("input.ixbi", bundle.input), ("output.ixbo", bundle.output)] do
      IO.FS.writeBinFile (directory / name) ⟨bytes⟩

end Compilatrix.Ixby
