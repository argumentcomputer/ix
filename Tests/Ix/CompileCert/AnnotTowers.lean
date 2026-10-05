import Tests.Ix.CompileCert.SourceModels
import Tests.Ix.CompileCert.TowerDefs
import Ix.CompileCert.AnnotTowerEntry

namespace Tests.Ix.CompileCert.AnnotTowers
open _root_.Ix.CompileCert
open _root_.Ix.Kernel

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"tower control failed: {label}")
  IO.println s!"PASS: tower {label}"

def entryCount (env : Env) : Nat := env.consts.foldl (fun count entry =>
  match entry with | .projInfo table => count + table.numFields | _ => count) 0

private def installed (env : Lean.Environment) (roots : List Lean.Name) : IO Env := do
  let captured ← IO.ofExcept (captureCone env.find? roots 128)
  match installSourceModels captured.source roots with
  | .ok result => pure result.env
  | .error error => throw (IO.userError s!"tower source fold: {SourceModels.label error}")

def run (env : Lean.Environment) : IO Unit := do
  let owner := Compiled.prefixName ++ `Pair
  let twin := `Tests.Ix.CompileCert.TowerDefs.PairTwin
  let source ← installed env [owner]
  let extra ← installed env [owner, `PUnit]
  let aliases ← installed env [owner, twin]
  let ownerName := sourceName owner
  let twinName := sourceName twin
  let names := fun name : Name =>
    if name == twinName then ownerName
    else if name == twinName.str "mk" then ownerName.str "mk"
    else name
  require "actual source has two unused entries" (entryCount source == 2)
  require "actual alias source has four unused entries" (entryCount aliases == 4)
  require "actual identity tables" (checkInstalledTowers source source id == some true)
  require "actual admitted extra-support neighbor" (checkInstalledTowers source extra id == some true)
  require "actual many-to-one compatible family alias" (checkInstalledTowers aliases source names == some true)
  let some (.projInfo original) := source.find? (projTableName ownerName)
    | throw (IO.userError "actual source table missing")
  let replace := fun table : ProjTable => { source with consts := source.consts.map (fun entry =>
    if entry.name == (projTableName ownerName) then .projInfo table else entry) }
  let omitted := { source with consts := source.consts.filter (fun entry => entry.name != (projTableName ownerName)) }
  require "omitted unused table refuses" (checkInstalledTowers source omitted id != some true)
  require "unused offset tamper refuses"
    (checkInstalledTowers source (replace { original with off := original.off + 1 }) id != some true)
  require "unused field count tamper refuses"
    (checkInstalledTowers source (replace { original with numFields := original.numFields - 1 }) id != some true)
  require "unused constructor identity tamper refuses"
    (checkInstalledTowers source (replace { original with ctor := ownerName.str "unrelated" }) id != some true)
  require "unused body tamper refuses"
    (checkInstalledTowers source (replace { original with bodies := original.bodies.setIfInBounds 1 (.sort .zero) }) id != some true)
  require "unused guard tamper refuses"
    (checkInstalledTowers source (replace { original with guards := original.guards.map Level.succ }) id != some true)
  require "unused structure sort tamper refuses"
    (checkInstalledTowers source (replace { original with structSort := .succ original.structSort }) id != some true)
  require "wrong alias owner refuses"
    (checkInstalledTowers aliases source (fun name => if name == twinName then ownerName.str "missing" else names name) != some true)
  IO.println "tower association controls: 13/13; positive source/target folds are independent; mutated targets test comparison refusal only"

end Tests.Ix.CompileCert.AnnotTowers
