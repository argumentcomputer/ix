import Aiur.Execution.Hints
import Lean

namespace Aiur.Execution
open Lean

private def tagged (key tag : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ((key, Lean.toJson tag) :: fields)

def typeJson : Ty → Json
  | .field => tagged "kind" "field"
  | .ptr type => tagged "kind" "ptr" [("target", typeJson type)]
  | .tuple types => tagged "kind" "tuple" [("items", Lean.toJson (types.map typeJson))]
  | .enum name => tagged "kind" "enum" [("name", Lean.toJson name)]
termination_by type => sizeOf type

def ioTypeJson : IOType → Json
  | .field => tagged "kind" "field"
  | .tuple items => tagged "kind" "tuple" [("items", Lean.toJson (items.map ioTypeJson))]
  | .array element length => tagged "kind" "array" [("element", ioTypeJson element), ("length", Lean.toJson length)]
  | .record name fields => tagged "kind" "struct" [("name", Lean.toJson name),
      ("fields", Lean.toJson (fields.map fun entry => Lean.toJson [Lean.toJson entry.1, ioTypeJson entry.2]))]
  | .enum name constructors => tagged "kind" "enum" [("name", Lean.toJson name),
      ("constructors", Lean.toJson (constructors.map fun entry => Lean.toJson [Lean.toJson entry.1, Lean.toJson (entry.2.map ioTypeJson)]))]
termination_by type => sizeOf type
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      cases ‹String × IOType›
      simp_all only [Prod.mk.sizeOf_spec]
      omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      have hp : sizeOf entry < sizeOf constructors := List.sizeOf_lt_of_mem (by assumption)
      cases entry
      simp_all only [Prod.mk.sizeOf_spec]
      omega

def instructionJson (encode : F → Nat) : Instruction F → Json
  | .literal dest value => tagged "op" "literal" [("dest", Lean.toJson dest), ("value", Lean.toJson (encode value))]
  | .copy dest source => tagged "op" "copy" [("dest", Lean.toJson dest), ("source", Lean.toJson source)]
  | .neg dest source => tagged "op" "neg" [("dest", Lean.toJson dest), ("source", Lean.toJson source)]
  | .binary dest op left right => tagged "op" "binary" [("dest", Lean.toJson dest),
      ("operator", Lean.toJson (match op with | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div")),
      ("left", Lean.toJson left), ("right", Lean.toJson right)]
  | .guard tests message => tagged "op" "guard"
      [("tests", Lean.toJson (tests.map fun (r,v) => [r, encode v])), ("message", Lean.toJson message)]
  | .branch tests target => tagged "op" "branch"
      [("tests", Lean.toJson (tests.map fun (r,v) => [r, encode v])), ("otherwise", Lean.toJson target)]
  | .jump target => tagged "op" "jump" [("target", Lean.toJson target)]
  | .call function args dest => tagged "op" "call"
      [("function", Lean.toJson function), ("args", Lean.toJson args), ("dest", Lean.toJson dest)]
  | .store type value dest => tagged "op" "store"
      [("type", typeJson type), ("value", Lean.toJson value), ("dest", Lean.toJson dest)]
  | .load type pointer dest => tagged "op" "load"
      [("type", typeJson type), ("pointer", Lean.toJson pointer), ("dest", Lean.toJson dest)]
  | .hint type keyType key dest channel => tagged "op" "hint"
      [("channel", Lean.toJson channel), ("type", typeJson type), ("key_type", typeJson keyType), ("key", Lean.toJson key), ("dest", Lean.toJson dest)]
  | .assertEq left right assertion => tagged "op" "assert_eq"
      [("left", Lean.toJson left), ("right", Lean.toJson right),
       ("message", Lean.toJson assertion.message), ("runtime_check", Lean.toJson assertion.runtimeCheck)]
  | .ret value => tagged "op" "ret" [("value", Lean.toJson value)]
  | .fail message => tagged "op" "fail" [("message", Lean.toJson message)]

def FlatHintEntry.toJson (encode : F → Nat) (entry : FlatHintEntry F) : Json :=
  Json.mkObj [("channel", Lean.toJson entry.channel), ("type", typeJson entry.type), ("key_type", typeJson entry.keyType),
    ("key", Lean.toJson (entry.key.map encode)), ("output", Lean.toJson (entry.output.map encode))]

/-- Large witness datasets must not rely on specialization of Array.map's
generic monadic implementation. Build the JSON array with a direct fold. -/
def hintsJson (encode : F → Nat) (entries : Array (FlatHintEntry F)) : Json :=
  .arr (entries.foldl (fun out entry => out.push (entry.toJson encode)) #[])

/-- Versioned data transported by the FFI. The initial Rust field backend
supports primes fitting UInt64; the bytecode compiler itself is field-generic. -/
def Export.toJson (exported : Export F) (modulus : Nat) (encode : F → Nat) : Except String Json := do
  if modulus < 2 || modulus ≥ 2^64 then throw "execution requires a prime modulus fitting UInt64"
  let code := exported.bytecode
  let entries ← code.entries.mapM fun (name, function) => do
    let some interface := exported.interfaces.find? (·.name == name)
      | throw s!"missing entry IO interface {name}"
    return Json.mkObj [("name", Lean.toJson name), ("function", Lean.toJson function),
      ("inputs", Lean.toJson (interface.inputs.map ioTypeJson)),
      ("output", (interface.output.map ioTypeJson).getD Json.null)]
  return Json.mkObj [
    ("version", Lean.toJson (2 : Nat)), ("modulus", Lean.toJson modulus),
    ("functions", Lean.toJson (code.functions.map fun fn => Json.mkObj [
      ("name", Lean.toJson fn.name), ("params", Lean.toJson (fn.params.map typeJson)),
      ("result", typeJson fn.result), ("registers", Lean.toJson fn.registers),
      ("code", Lean.toJson (fn.code.map (instructionJson encode)))])),
    ("enums", Lean.toJson (code.enums.map fun decl => Json.mkObj [
      ("name", Lean.toJson decl.name), ("constructors", Lean.toJson (decl.constructors.map fun c =>
        Json.mkObj [("name", Lean.toJson c.name), ("fields", Lean.toJson (c.fields.map typeJson))]))])),
    ("tables", Lean.toJson (code.tables.map fun table => Json.mkObj [
      ("name", Lean.toJson table.name), ("type", typeJson table.type), ("rows", Lean.toJson (table.rows.map (List.map encode)))])),
    ("maps", Lean.toJson (code.maps.map fun map => Json.mkObj [
      ("name", Lean.toJson map.name), ("params", Lean.toJson (map.params.map typeJson)), ("result", typeJson map.result),
      ("input", Lean.toJson map.input), ("output", Lean.toJson map.output)])),
    ("entries", Lean.toJson entries)]

end Aiur.Execution
