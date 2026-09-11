import Ix.Compiler.Tools.ScalarNativeCheck

/-! Independent artifact checks for physical scalar selection. This module
imports no source compiler, selector, encoder, or machine evaluator. -/
namespace Ix.Compiler.Tools.PhysicalScalarNativeCheck
open Lean Check UniqueCheck UpstreamNativeCheck

def names : Array String := #["project", "tag", "pred", "choose", "helpers", "nested", "unary-pred"]

def expected (name : String) (a b : Nat) : Nat :=
  if name == "project" then a
  else if name == "tag" then (if a == 0 then 11 else 22)
  else if name == "pred" || name == "unary-pred" then a - 1
  else if name == "choose" then (if a == 0 then b else a - 1)
  else if name == "helpers" then (if a < 2 then 11 else 22)
  else if a < 3 then b else a - 3

def declared (program : Json) (address : String) : IO Json := do
  for declaration in (← arrField program "declarations") do
    let pair ← array declaration
    if pair.size == 2 && pair[0]! == toJson address then
      return ← field (← field pair[1]! "fn") "definition"
  throw (IO.userError "physical scalar selected declaration is missing")

def exportAddress (program : Json) (arity : Nat) : Nat → Json → IO String
  | 0, _ => throw (IO.userError "physical scalar module export exceeds its depth")
  | fuel + 1, definition => do
    let signature ← field definition "signature"
    need ((← arrField signature "params").isEmpty) "physical scalar module export wrapper has arguments"
    let blocks ← arrField definition "blocks"
    need (blocks.size == 1) "physical scalar module export has extra blocks"
    let block := blocks[0]!
    need ((← arrField block "valueParams").isEmpty && (← arrField block "creditParams").isEmpty)
      "physical scalar module export wrapper has capabilities"
    let instructions ← arrField block "instructions"
    let term ← field block "terminator"
    if let .ok tail := term.getObjVal? "tailCall" then
      need (instructions.isEmpty && (← arrField tail "args").isEmpty) "physical scalar module export alias changed"
      return ← exportAddress program arity fuel (← declared program (← strField tail "function"))
    else
      need (instructions.size == 1 && (← strField signature "result") == "shared") "physical scalar module export closure changed"
      let pap ← field instructions[0]! "papp"
      need ((← arrField pap "args").isEmpty &&
        (← number (← field (← field (← field term "ret") "value") "reg") "id") == 0)
        "physical scalar module export captures values or returns another register"
      let address ← strField pap "function"
      let target ← declared program address
      let signature ← field target "signature"
      need ((← field signature "papSafe") == toJson true && (← arrField signature "params").size == arity)
        "physical scalar module export target signature changed"
      return address

def inspect (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-native-physical-scalar/2" &&
    (← strField snapshot "policy") == "physical-scalar-cfg/1" && (← field snapshot "row") == row)
    "physical scalar snapshot policy/row disagrees"
  let name ← strField row "name"
  need (names.contains name) "unknown physical scalar source family"
  let arity ← number row "runtime_parameters"
  need (arity == if name == "unary-pred" then 1 else 2) "physical scalar runtime arity disagrees"
  let text ← byteField snapshot "text"
  need (text.size == (← number row "text_bytes") && digest text == (← strField row "text_hash") &&
    bytes.size == (← number row "object_bytes")) "physical scalar text hash/size disagrees"
  let root ← strField row "ir1_root"
  let entry ← strField row "physical_entry"
  need (isHex 64 root && isHex 64 entry && isHex 64 (← strField row "source_root")) "physical scalar root invalid"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root ++ " 06 00 00 00 01 00 00 00")))
  need ((← byteField snapshot "provenance") == provenance) "physical scalar snapshot provenance disagrees"
  ScalarNativeCheck.inspectObject bytes text (← number snapshot "entry_offset") root 6
  let source ← field snapshot "source_compilation"
  need ((← strField (← field source "source") "root") == (← strField row "source_root") &&
    (← strField (← field source "ixir1") "root") == root) "physical scalar source/IR binding disagrees"
  let program ← field (← field source "ixir2_diagnostic") "program"
  need ((← exportAddress program arity 32 (← field program "main")) == entry) "physical scalar module export binding disagrees"
  let entries ← arrField snapshot "selected_entries"
  let functions ← number row "functions"
  need (entries.size == functions && entries.back? == some (toJson entry) &&
    entries.toList.eraseDups.length == entries.size) "physical scalar selection map disagrees"
  let mut blocks := 0
  for address in entries do
    let definition ← declared program (← string address)
    blocks := blocks + (← arrField definition "blocks").size
  need (blocks == (← number row "physical_blocks")) "physical scalar selected block count disagrees"
  let depth ← number row "stack_depth"
  need (depth > 0 && depth ≤ 32 && depth == functions && (← number row "stack_bytes") == 272 * depth &&
    (← number row "below_entry_bytes") == 272 * depth - 8) "physical scalar stack reservation disagrees"
  let observations ← arrField snapshot "observations"
  let m := UInt64.size - 1
  let inputs : Array (Nat × Nat) := #[(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]
  need (observations.size == inputs.size) "physical scalar input inventory disagrees"
  for index in [:observations.size] do
    let observation := observations[index]!
    let a ← number observation "left"
    let b ← number observation "right"
    need ((a,b) == inputs[index]!) "physical scalar boundary input inventory disagrees"
    let args : Array Nat := if arity == 1 then #[a] else #[a, b]
    need ((← field observation "source_arguments") == toJson args) "physical scalar source application arguments disagree"
    need ((← field observation "application_heap") == Json.mkObj [("allocs", toJson (1 : Nat)), ("frees", toJson (1 : Nat)),
      ("rcops", toJson (1 : Nat)), ("reuses", toJson (0 : Nat)), ("slots", toJson (1 : Nat)), ("live", toJson (0 : Nat))])
      "physical scalar source application reclamation disagrees"
    need ((← number observation "value") == expected name a b && (← number observation "status") == 0 &&
      (← number observation "byte_steps") > 0 && (← number observation "physical_control") > 0 &&
      (← number observation "physical_heap_fuel") ≤ (← number observation "physical_control") &&
      (← field observation "source_evaluated") == toJson true) "physical scalar arithmetic/source observation disagrees"

def regressions (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  let changed ← replaceAt snapshot ["policy"] (toJson "unknown/1")
  rejects "physical policy" "policy/row" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["text"] (toJson "c3")
  rejects "physical text" "hash/size" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["entry_offset"] (toJson (999999 : Nat))
  rejects "physical entry" "export" (inspect row changed bytes)
  rejects "physical ELF byte" "ELF header" (inspect row snapshot (bytes.set! 0 0))
  let observations ← arrField snapshot "observations"
  let first ← replaceAt observations[0]! ["status"] (toJson (1 : Nat))
  let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
  rejects "physical observation" "arithmetic/source" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["source_compilation", "ixir1", "root"] (toJson (String.ofList (List.replicate 64 '0')))
  rejects "physical root" "source/IR binding" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["selected_entries"] (toJson ([] : List String))
  rejects "physical selection map" "selection map" (inspect row changed bytes)
  let changedRow ← replaceAt row ["runtime_parameters"] (toJson (3 : Nat))
  let changed ← replaceAt snapshot ["row"] changedRow
  rejects "physical runtime arity" "runtime arity" (inspect changedRow changed bytes)
  let first ← replaceAt observations[0]! ["source_arguments"] (toJson ([] : List Nat))
  let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
  rejects "physical application arguments" "application arguments" (inspect row changed bytes)
  let first ← replaceAt observations[0]! ["application_heap", "frees"] (toJson (0 : Nat))
  let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
  rejects "physical application reclamation" "application reclamation" (inspect row changed bytes)

end Ix.Compiler.Tools.PhysicalScalarNativeCheck
