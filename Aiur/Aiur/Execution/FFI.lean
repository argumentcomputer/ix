import Aiur.Artifact
import Lean.Data.Json
import Mathlib.Data.ZMod.Basic

namespace Aiur.Execution
open Lean

/-- The compiled package and prepared hints travel in Ixon (`Aiur.Artifact`),
the entry and its arguments as JSON, and the result in Ixon (its grammar is
documented with the Rust encoder, `crates/aiur/src/ffi.rs`). -/
@[extern "aiur_lean_execute"]
private opaque executeRaw (package hints : @& ByteArray) (request : @& String) : IO ByteArray

structure Query where
  function : Nat
  name : String
  args : Array Nat
  output : Array Nat
  multiplicity : Nat
  deriving Repr

/-- A ROM cell: its address, the type it was stored under, its words and how
often it was read. -/
structure MemoryEntry where
  address : Nat
  type : Ty
  value : Array Nat
  multiplicity : Nat

instance : Inhabited MemoryEntry := ⟨⟨0, .field, #[], 0⟩⟩

structure Result where
  output : Array Nat
  pretty_output : Option String
  queries : Array Query
  memory : Array MemoryEntry
  memory_types : Array (Ty × Nat)
  instructions : Nat

open Aiur.Ixon in
private def getNats : GetM (Array Nat) := getArray getNat

open Aiur.Ixon in
private def getResult : GetM Result := do
  let output ← getNats
  let pretty_output ← getOption getString
  let queries ← getArray do
    let function ← getNat
    let name ← getString
    let args ← getNats
    let output ← getNats
    let multiplicity ← getNat
    return ({ function, name, args, output, multiplicity } : Query)
  let memory ← getArray do
    let address ← getNat
    let type ← getTy
    let value ← getNats
    let multiplicity ← getNat
    return ({ address, type, value, multiplicity } : MemoryEntry)
  let memory_types ← getArray do
    let type ← getTy
    return (type, ← getNat)
  let instructions ← getNat
  return { output, pretty_output, queries, memory, memory_types, instructions }

open Aiur.Ixon in
/-- An execution response: the record, then `rest` (the trace, when one was
requested). A refused execution is its error. -/
def decodeResponse (response : ByteArray) (rest : GetM α) : Except String (Result × α) :=
  Aiur.Ixon.decode (do
    if (← getTag "response" 2) == 0 then throw (← getString)
    let result ← getResult
    return (result, ← rest)) response

private def executeRequest (package hints : ByteArray) (entry : String) (key : String) (args : Json) :
    IO (Except String Result) := do
  let response ← executeRaw package hints (Json.mkObj [("entry", toJson entry), (key, args)]).compress
  return do
    -- No trace was requested: its option must be empty.
    let (result, _) ← decodeResponse response (Aiur.Ixon.getTag "trace option" 1)
    return result

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
