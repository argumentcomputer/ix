import Compilatrix.Ixby.Catalog
import Compilatrix.Ixby.Report
import Compilatrix.Ixby.SymbolicReport
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.Ixby Compilatrix.Tools.Check

private def address (hex : String) : Except String Ixon.Address := do
  let bytes ← unhex hex
  let some address := Ixon.Address.ofBytes? bytes | throw "expected a 32-byte source address"
  return address

def main (args : List String) : IO UInt32 := cli "ixon-to-ixby" do
  let catalog :: root :: output :: options := args |
    throw (IO.userError "usage: ixon-to-ixby <catalog.ixc-directory> <main-hex> <new-output-directory> [runtime-arity] [nat-block-hex] [--symbolic]")
  need (options.count "--symbolic" ≤ 1) "--symbolic may be supplied once"
  let symbolic := options.contains "--symbolic"
  let options := options.filter (· != "--symbolic")
  need (options.length ≤ 2) "too many compiler arguments"
  let parameters ← present ((options[0]?.getD "0").toNat?) "invalid runtime arity"
  let natBlock ← match options[1]? with
    | none => pure none
    | some hex => pure (some (← checked (address hex)))
  let root ← checked (address root)
  let output : System.FilePath := output
  need (!(← output.pathExists)) "compiler requires a new output directory"
  let loaded ← checked ((← Ixon.CatalogIO.loadDir catalog).mapError reprStr)
  let blobs ← checked (catalogBlobs loaded)
  let sourceConfig : Pipeline.Config := { blobs := AddressEnv.lookup blobs, natBlock }
  let config := Config.profile
  let compiled ← checked (compileIxon loaded.constants root sourceConfig config parameters)
  let exported ← checked compiled.target.export
  let certificate ← if symbolic then pure (some (← checked compiled.target.certifySymbolic)) else pure none
  let source : Source := {
    declarations := compiled.erasure.erasure.result.raw
    main := entryExpression root parameters, parameters }
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "source.json") (source.json.pretty 100 ++ "\n")
  IO.FS.writeFile (output / "program.txt") (reprStr compiled.target.program ++ "\n")
  IO.FS.writeFile (output / "config.txt") (reprStr config ++ "\n")
  if let some certificate := certificate then
    IO.FS.writeFile (output / "symbolic.json") (certificate.json.pretty 100 ++ "\n")
  IO.FS.writeBinFile (output / "profile.ixfp") ⟨exported.profileBytes⟩
  IO.FS.writeBinFile (output / "program.ixby") ⟨exported.programBytes⟩
  IO.println s!"ixon-to-ixby ok: {compiled.target.program.functions.size} functions, {parameters} runtime arguments, semantics 2"
