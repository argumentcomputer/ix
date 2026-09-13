import Compilatrix.Ixby.Catalog
import Compilatrix.Ixby.Report
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.Ixby Compilatrix.Tools.Check

private def address (hex : String) : Except String Ixon.Address := do
  let bytes ← unhex hex
  let some address := Ixon.Address.ofBytes? bytes | throw "expected a 32-byte source address"
  return address

def main (args : List String) : IO UInt32 := cli "ixon-to-ixby" do
  let catalog :: root :: output :: options := args |
    throw (IO.userError "usage: ixon-to-ixby <catalog.ixc-directory> <main-hex> <new-output-directory> [reference|proving] [runtime-arity] [nat-block-hex]")
  need (options.length ≤ 3) "too many compiler arguments"
  let mode := options[0]?.getD "reference"
  need (["reference", "proving"].contains mode) "mode must be reference or proving"
  let parameters ← present ((options[1]?.getD "0").toNat?) "invalid runtime arity"
  let natBlock ← match options[2]? with
    | none => pure none
    | some hex => pure (some (← checked (address hex)))
  let root ← checked (address root)
  let output : System.FilePath := output
  need (!(← output.pathExists)) "compiler requires a new output directory"
  let loaded ← checked ((← Ixon.CatalogIO.loadDir catalog).mapError reprStr)
  let blobs ← checked (catalogBlobs loaded)
  let sourceConfig : Pipeline.Config := { blobs := AddressEnv.lookup blobs, natBlock }
  let config := if mode == "proving" then Config.crypto else ({} : Config)
  let compiled ← checked (compileIxon loaded.constants root sourceConfig config parameters)
  let exported ← if mode == "proving" then pure (some (← checked compiled.target.export)) else pure none
  let source : Source := {
    declarations := compiled.erasure.erasure.result.raw
    main := entryExpression root parameters, parameters }
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "source.json") (source.json.pretty 100 ++ "\n")
  IO.FS.writeFile (output / "program.txt") (reprStr compiled.target.program ++ "\n")
  IO.FS.writeFile (output / "config.txt") (reprStr config ++ "\n")
  if let some exported := exported then
    IO.FS.writeBinFile (output / "profile.ixbp") ⟨exported.profileBytes⟩
    IO.FS.writeBinFile (output / "program.ixby") ⟨exported.programBytes⟩
  IO.println s!"ixon-to-ixby ok: {compiled.target.program.functions.size} functions, {parameters} runtime arguments, {mode}"
