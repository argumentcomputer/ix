import Ix.Compiler.Tools.PhysicalScalarNativeCheck

/-! Independent JSON, ELF and arithmetic checks. No source compiler,
instruction selector, encoder or machine evaluator is imported. -/
namespace Ix.Compiler.Tools.CapturedScalarNativeCheck
open Lean Check UniqueCheck UpstreamNativeCheck

def families : Array String := #["capture-project", "capture-choice", "capture-nested"]
def tags : Array String := #["zero", "seven", "max"]
def captures : Array Nat := #[0, 7, UInt64.size - 1]

def expected (family : String) (capture argument : Nat) : Nat :=
  if family == "capture-project" then capture
  else if family == "capture-choice" then (if argument == 0 then capture else argument - 1)
  else if argument < 3 then capture else argument - 3

def reg (index : Nat) : Json := Json.mkObj [("reg", Json.mkObj [("id", toJson index)])]
def owned : Json := Json.mkObj [("owned", Json.mkObj [("world", toJson "shared")])]
def parameter : Json := Json.mkObj [("world", toJson "shared"), ("passing", toJson "owned")]

def heap (freed rc live : Nat) : Json := Json.mkObj [
  ("allocs", toJson (2 : Nat)), ("frees", toJson freed), ("rcops", toJson rc),
  ("reuses", toJson (0 : Nat)), ("slots", toJson (2 : Nat)), ("live", toJson live)]

/-- Independently inspect the fixture's closed initializer, including its
literal helper and capture register. This is an artifact gate, not a proof. -/
def exportAddress (program : Json) (capture : Nat) : Nat → Json → IO String
  | 0, _ => throw (IO.userError "captured scalar initializer exceeds its depth")
  | fuel + 1, definition => do
    let signature ← field definition "signature"
    need ((← arrField signature "params").isEmpty && (← strField signature "result") == "shared")
      "captured scalar initializer signature changed"
    let blocks ← arrField definition "blocks"
    need (blocks.size == 1) "captured scalar initializer block count changed"
    let block := blocks[0]!
    need ((← arrField block "valueParams").isEmpty && (← arrField block "creditParams").isEmpty)
      "captured scalar initializer capabilities changed"
    let instructions ← arrField block "instructions"
    let term ← field block "terminator"
    if let .ok tail := term.getObjVal? "tailCall" then
      need (instructions.isEmpty && (← arrField tail "args").isEmpty) "captured scalar initializer alias changed"
      return ← exportAddress program capture fuel (← PhysicalScalarNativeCheck.declared program (← strField tail "function"))
    else
      need (instructions.size == 3 && (← field (← field term "ret") "value") == reg 2)
        "captured scalar initializer result changed"
      let first ← field instructions[0]! "papp"
      need ((← arrField first "args").isEmpty) "captured scalar literal helper captures arguments"
      let helper ← PhysicalScalarNativeCheck.declared program (← strField first "function")
      let helperSig ← field helper "signature"
      need ((← field helperSig "params") == toJson #[parameter] && (← strField helperSig "result") == "shared" &&
        (← field helperSig "papSafe") == toJson true) "captured scalar literal helper signature changed"
      let body ← arrField helper "blocks"
      need (body.size == 1 && (← field body[0]! "valueParams") == toJson #[owned] &&
        (← arrField body[0]! "creditParams").isEmpty &&
        (← field body[0]! "instructions") == toJson #[Json.mkObj [("releaseShared", Json.mkObj [("target", reg 0)])]])
        "captured scalar literal helper ownership changed"
      let literal ← field (← field (← field (← field (← field body[0]! "terminator") "ret") "value") "lit") "literal"
      need ((← number (← field literal "nat") "n") == capture) "captured scalar initializer literal disagrees"
      let applied ← field instructions[1]! "apply"
      need ((← field applied "function") == reg 0 && (← field applied "args") == toJson #[toJson "erased"])
        "captured scalar initializer literal application changed"
      let pap ← field instructions[2]! "papp"
      need ((← field pap "args") == toJson #[reg 1]) "captured scalar initializer capture register changed"
      let address ← strField pap "function"
      let target ← PhysicalScalarNativeCheck.declared program address
      let signature ← field target "signature"
      need ((← field signature "papSafe") == toJson true && (← field signature "params") == toJson #[parameter, parameter] &&
        (← strField signature "result") == "shared") "captured scalar target signature changed"
      return address

def inspect (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-native-captured-scalar/1" &&
    (← strField snapshot "policy") == "physical-scalar-capture/1" && (← field snapshot "row") == row)
    "captured scalar snapshot policy/row disagrees"
  let family ← strField row "family"
  let capture ← number row "capture"
  need (families.contains family && captures.contains capture) "unknown captured scalar source family/capture"
  need ((← number row "runtime_parameters") == 1 && (← number row "physical_parameters") == 2)
    "captured scalar runtime arity disagrees"
  let text ← byteField snapshot "text"
  need (text.size == (← number row "text_bytes") && digest text == (← strField row "text_hash") &&
    bytes.size == (← number row "object_bytes")) "captured scalar text hash/size disagrees"
  let root ← strField row "ir1_root"
  let entry ← strField row "physical_entry"
  need (isHex 64 root && isHex 64 entry && isHex 64 (← strField row "source_root")) "captured scalar root invalid"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root ++ " 07 00 00 00 01 00 00 00")))
  need ((← byteField snapshot "provenance") == provenance) "captured scalar provenance disagrees"
  ScalarNativeCheck.inspectObject bytes text (← number snapshot "entry_offset") root 7
  let source ← field snapshot "source_compilation"
  need ((← strField (← field source "source") "root") == (← strField row "source_root") &&
    (← strField (← field source "ixir1") "root") == root) "captured scalar source/IR binding disagrees"
  let program ← field (← field source "ixir2_diagnostic") "program"
  need ((← exportAddress program capture 32 (← field program "main")) == entry) "captured scalar export binding disagrees"
  let initialized ← field snapshot "initializer"
  need ((← number initialized "capture") == capture && (← number initialized "location") == 1 &&
    (← field initialized "heap") == heap 1 1 1 && (← number initialized "peak_live") == 1 &&
    (← number initialized "control_steps") == 8 && (← number initialized "heap_fuel") == 2)
    "captured scalar initializer observation disagrees"
  let entries ← arrField snapshot "selected_entries"
  let selected ← number row "selected_functions"
  let functions ← number row "functions"
  need (entries.size == selected && functions == selected + 1 && entries.back? == some (toJson entry) &&
    entries.toList.eraseDups.length == entries.size) "captured scalar selection map disagrees"
  let mut blocks := 0
  for address in entries do
    let definition ← PhysicalScalarNativeCheck.declared program (← string address)
    blocks := blocks + (← arrField definition "blocks").size
  need (blocks == (← number row "physical_blocks")) "captured scalar selected block count disagrees"
  let depth ← number row "stack_depth"
  need (depth > 1 && depth ≤ 32 && depth == functions && (← number row "stack_bytes") == 272 * depth &&
    (← number row "below_entry_bytes") == 272 * depth - 8) "captured scalar stack reservation disagrees"
  let observations ← arrField snapshot "observations"
  let m := UInt64.size - 1
  let inputs : Array (Nat × Nat) := #[(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]
  need (observations.size == inputs.size) "captured scalar input inventory disagrees"
  for index in [:observations.size] do
    let observation := observations[index]!
    let a ← number observation "argument"
    let b ← number observation "unused_rsi"
    need ((a,b) == inputs[index]!) "captured scalar boundary input inventory disagrees"
    need ((← field observation "source_arguments") == toJson #[a] &&
      (← field observation "physical_arguments") == toJson #[capture, a]) "captured scalar application arguments disagree"
    need ((← field observation "application_heap") == heap 2 2 0) "captured scalar application reclamation disagrees"
    need ((← number observation "value") == expected family capture a && (← number observation "status") == 0 &&
      (← number observation "byte_steps") > 0 && (← number observation "physical_control") > 0 &&
      (← number observation "physical_heap_fuel") ≤ (← number observation "physical_control") &&
      (← field observation "source_evaluated") == toJson true) "captured scalar arithmetic/source observation disagrees"

def regressions (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  for (path, value, message) in [
    (["policy"], toJson "unknown/1", "policy/row"),
    (["text"], toJson "c3", "hash/size"),
    (["entry_offset"], toJson (999999 : Nat), "export"),
    (["source_compilation", "ixir1", "root"], toJson (String.ofList (List.replicate 64 '0')), "source/IR binding"),
    (["selected_entries"], toJson ([] : List String), "selection map"),
    (["initializer", "capture"], toJson (UInt64.size : Nat), "initializer observation"),
    (["initializer", "heap", "frees"], toJson (0 : Nat), "initializer observation"),
    (["source_compilation", "ixir2_diagnostic", "program", "main", "signature", "params"], toJson #[parameter], "initializer signature")
  ] do
    let changed ← replaceAt snapshot path value
    rejects "captured snapshot corruption" message (inspect row changed bytes)
  rejects "captured ELF byte" "ELF header" (inspect row snapshot (bytes.set! 0 0))
  let changedRow ← replaceAt row ["runtime_parameters"] (toJson (2 : Nat))
  let changed ← replaceAt snapshot ["row"] changedRow
  rejects "captured runtime arity" "runtime arity" (inspect changedRow changed bytes)
  let changedRow ← replaceAt row ["capture"] (toJson (if (← number row "capture") == 0 then 7 else 0 : Nat))
  let changed ← replaceAt snapshot ["row"] changedRow
  rejects "captured initializer literal" "initializer literal" (inspect changedRow changed bytes)
  let observations ← arrField snapshot "observations"
  for (path, value, message) in [
    (["status"], toJson (1 : Nat), "arithmetic/source"),
    (["source_arguments"], toJson ([] : List Nat), "application arguments"),
    (["physical_arguments"], toJson ([1, 2] : List Nat), "application arguments"),
    (["application_heap", "frees"], toJson (0 : Nat), "application reclamation")
  ] do
    let first ← replaceAt observations[0]! path value
    let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
    rejects "captured application corruption" message (inspect row changed bytes)

end Ix.Compiler.Tools.CapturedScalarNativeCheck
