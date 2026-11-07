import Aiur.Artifact
import Lean.Data.Json
import Mathlib.Data.ZMod.Basic

namespace Aiur.Execution
open Lean

/-- The compiled package and prepared hints travel in Ixon (`Aiur.Artifact`);
the entry, its arguments and the result are JSON. -/
@[extern "aiur_lean_execute"]
private opaque executeRaw (package hints : @& ByteArray) (request : @& String) : IO String

structure Query where
  function : Nat
  name : String
  args : Array Nat
  output : Array Nat
  multiplicity : Nat
  deriving Repr, FromJson

structure MemoryEntry where
  address : Nat
  cell : Json
  multiplicity : Nat
  deriving Inhabited, FromJson

structure Result where
  output : Array Nat
  pretty_output : Option String
  queries : Array Query
  memory : Array MemoryEntry
  memory_types : Array (Json × Nat)
  instructions : Nat
  deriving FromJson

private def executeRequest (package hints : ByteArray) (entry : String) (key : String) (args : Json) :
    IO (Except String Result) := do
  let response ← executeRaw package hints (Json.mkObj [("entry", toJson entry), (key, args)]).compress
  return do
    let json ← Json.parse response
    if let .ok error := json.getObjValAs? String "error" then throw error
    fromJson? (← json.getObjVal? "ok")

/-- Structured JSON arguments are interpreted using the selected entry's source
types. Tuples/arrays use JSON arrays; structs use named objects; enum values use
single-constructor objects such as {"Some": [7]}. -/
def Export.run (exported : Export (ZMod p)) [NeZero p] (entry : String) (args : Array Json)
    (hints : Array (HintEntry (ZMod p)) := #[]) :
    IO (Except String Result) := do
  match (do
    let package ← Artifact.package exported p ZMod.val
    let hints ← Artifact.hints ZMod.val (← exported.prepareHints hints)
    return (package, hints)) with
  | .error error => return .error error
  | .ok (package, hints) => executeRequest package hints entry "args" (Lean.toJson args)

/-- Low-level entry IO still checks canonical fields, enum tags and padding. -/
def Export.runFlat (exported : Export (ZMod p)) [NeZero p] (entry : String) (args : Array Nat)
    (hints : Array (HintEntry (ZMod p)) := #[]) :
    IO (Except String Result) := do
  match (do
    let package ← Artifact.package exported p ZMod.val
    let hints ← Artifact.hints ZMod.val (← exported.prepareHints hints)
    return (package, hints)) with
  | .error error => return .error error
  | .ok (package, hints) => executeRequest package hints entry "flat_args" (Lean.toJson args)

end Aiur.Execution
