import Aiur.Execution.Encode
import Mathlib.Data.ZMod.Basic

namespace Aiur.Execution
open Lean

@[extern "aiur_lean_execute"]
private opaque executeJson (request : @& String) : IO String

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

private def executeRequest (program : Json) (entry : String) (key : String) (args hints : Json) :
    IO (Except String Result) := do
  let response ← executeJson (Json.mkObj [("program", program), ("entry", toJson entry),
    (key, args), ("hints", hints)]).compress
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
    let program ← exported.toJson p ZMod.val
    let hints ← exported.prepareHints hints
    return (program, hintsJson ZMod.val hints)) with
  | .error error => return .error error
  | .ok (program, hints) => executeRequest program entry "args" (Lean.toJson args) hints

/-- Low-level entry IO still checks canonical fields, enum tags and padding. -/
def Export.runFlat (exported : Export (ZMod p)) [NeZero p] (entry : String) (args : Array Nat)
    (hints : Array (HintEntry (ZMod p)) := #[]) :
    IO (Except String Result) := do
  match (do
    let program ← exported.toJson p ZMod.val
    let hints ← exported.prepareHints hints
    return (program, hintsJson ZMod.val hints)) with
  | .error error => return .error error
  | .ok (program, hints) => executeRequest program entry "flat_args" (Lean.toJson args) hints

end Aiur.Execution
