/- Ignored end-to-end gates for the 19-project Palomar piece catalog. -/
module

public import LSpec
public import Benchmarks.PalomarSpec.Projection
public import Ix.Cli.CatalogCmd

public section

open LSpec
open PalomarSpec

namespace Tests.Ix.Palomar

private def driverExe : System.FilePath :=
  ".lake" / "build" / "bin" / "palomar"

private def runDriver (args : Array String) :
    IO (Bool × Nat × Nat × Option String) := do
  unless ← driverExe.pathExists do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build ix palomar` first")
  let exe ← IO.FS.realPath driverExe
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  return (exit == 0, 0, 0,
    if exit == 0 then none else some s!"palomar driver failed ({exit})")

private def buildCatalog : IO (Bool × Nat × Nat × Option String) := do
  let result ← runDriver #["build"]
  unless result.1 do return result
  let content ← Ix.Cli.CatalogCmd.rsCatalogInfoFFI "palomar.ixc"
  let verify ← Ix.Cli.CatalogCmd.rsCatalogVerifyFFI "palomar.ixc" false
  let parsed : Except String (Nat × Nat) := do
    let json ← Lean.Json.parse content
    let members ← (← json.getObjVal? "members").getArr?
    let mut labels := #[]
    for member in members do
      labels := labels.push (← (← member.getObjVal? "label").getStr?)
    let expected := catalog.map (·.qualifier.toString (escape := false))
    unless labels == expected do
      throw s!"manifest labels differ: got {labels}, expected {expected}"
    let verifyJson ← Lean.Json.parse verify
    let union ← (← verifyJson.getObjVal? "unionConsts").getNat?
    unless union > 0 do throw "catalog union is empty"
    return (members.size, union)
  match parsed with
  | .ok (members, union) => return (true, members, union, none)
  | .error error => return (false, 0, 0, some error)

def buildSuite : List TestSeq := [
  .individualIO "palomar: 19 isolated pieces + verified catalog"
    none buildCatalog .done
]

def checkSuite : List TestSeq := [
  .individualIO "palomar: per-piece anonymous kernel sweep"
    none (runDriver #["check"]) .done
]

def validateSuite : List TestSeq := [
  .individualIO "palomar: per-project metadata fidelity"
    none (runDriver #["validate"]) .done
]

end Tests.Ix.Palomar
