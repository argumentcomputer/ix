import Compilatrix.Tools.PhysicalScalarNativeCheck
import Compilatrix.Tools.IxIR2Check

/-! Independent checks for persisted allocating CFGs and their native objects.
The import closure contains no source compiler, IxIR₂ types, selector,
encoder, ELF writer, or machine evaluator. -/
namespace Compilatrix.Tools.HeapNativeCheck
open Lean Check UniqueCheck UpstreamNativeCheck

def names : Array String := #["leaf-call", "branch-call", "caller-live", "nested-alloc", "shared-pair",
  "unique-diamond", "hot-credit", "leaf-switch", "arena-limit"]

def expected (name : String) (a b : Nat) : Nat :=
  if name == "branch-call" || name == "unique-diamond" then (if a == 0 then b else a - 1)
  else if name == "caller-live" then a - 1
  else if name == "shared-pair" then b else a

def demand (name : String) : Nat :=
  if name == "arena-limit" then 64
  else if ["nested-alloc", "unique-diamond", "hot-credit"].contains name then 2 else 1

def sourceFamily (name : String) : Bool := (names.toList.take 5).contains name

def arity (name : String) : Nat :=
  if ["branch-call", "shared-pair", "unique-diamond"].contains name then 2 else 1

def declared (program : Json) (address : String) : IO Json := do
  let entries ← arrField program "declarations"
  let matching ← entries.filterM fun entry => return (← strField entry "address") == address
  need (matching.size == 1) "heap selected declaration is missing or duplicated"
  let declaration ← arrField matching[0]! "declaration"
  need (declaration.size == 2 && declaration[0]! == toJson "fn") "heap selected declaration is not a function"
  return declaration[1]!

def exportAddress (program : Json) (runtimeArity : Nat) : Nat → Json → IO String
  | 0, _ => throw (IO.userError "heap source export exceeds its depth")
  | fuel + 1, definition => do
    need ((← arrField (← field definition "signature") "params").isEmpty) "heap source export wrapper has parameters"
    let blocks ← arrField definition "blocks"
    need (blocks.size == 1) "heap source export wrapper has extra blocks"
    let block := blocks[0]!
    need ((← arrField block "valueParams").isEmpty && (← arrField block "creditParams").isEmpty)
      "heap source export wrapper has capabilities"
    let instructions ← arrField block "instructions"
    let term ← arrField block "terminator"
    if term[0]? == some (toJson "tailCall") then
      need (term.size == 3 && instructions.isEmpty && term[2]! == toJson ([] : List Nat)) "heap source export alias changed"
      return ← exportAddress program runtimeArity fuel (← declared program (← string term[1]!))
    else
      need (instructions.size == 1 && term == #[toJson "ret", toJson #[toJson "reg", toJson (0 : Nat)]])
        "heap source export closure changed"
      let pap ← array instructions[0]!
      need (pap.size == 3 && pap[0]! == toJson "papp" && pap[2]! == toJson ([] : List Nat))
        "heap source export captures values"
      let address ← string pap[1]!
      let signature ← field (← declared program address) "signature"
      need ((← field signature "papSafe") == toJson true && (← arrField signature "params").size == runtimeArity)
        "heap source export signature changed"
      return address

def inspectObject (bytes text provenance : ByteArray) (entry : Nat)
    (exportName : String := "compilatrix_heap_cfg") : IO Unit := do
  need (bytes.size ≥ 64 && bytes.extract 0 7 == (← checked (unhex "7f 45 4c 46 02 01 01"))) "heap ELF header disagrees"
  need ((← readLE bytes 16 2) == 1 && (← readLE bytes 18 2) == 62 && (← readLE bytes 20 4) == 1 &&
    (← readLE bytes 24 8) == 0 && (← readLE bytes 32 8) == 0 && (← readLE bytes 52 2) == 64 &&
    (← readLE bytes 56 2) == 0 && (← readLE bytes 58 2) == 64 && (← readLE bytes 60 2) == 8 &&
    (← readLE bytes 62 2) == 7) "heap ELF structure disagrees"
  let table ← readLE bytes 40 8
  need (table + 8 * 64 == bytes.size) "heap ELF table bounds disagree"
  let sectionOffset := fun index => table + 64 * index
  let payload (index : Nat) : IO ByteArray := do
    slice bytes (← readLE bytes (sectionOffset index + 24) 8) (← readLE bytes (sectionOffset index + 32) 8)
  need ((← payload 1) == text && (← readLE bytes (sectionOffset 1 + 4) 4) == 1 &&
    (← readLE bytes (sectionOffset 1 + 8) 8) == 6) "heap ELF text disagrees"
  need ((← payload 2).isEmpty && (← payload 6).isEmpty && (← readLE bytes (sectionOffset 6 + 8) 8) == 0)
    "heap ELF relocation/stack policy disagrees"
  let symbols ← payload 4
  let strings ← payload 5
  need (symbols.size == 72 && (← readLE bytes (sectionOffset 4 + 56) 8) == 24 &&
    (← readLE bytes (sectionOffset 4 + 40) 4) == 5) "heap ELF symbol table disagrees"
  let nameOffset ← readLE symbols 48 4
  let name := exportName.toUTF8.push 0
  need (strings.extract nameOffset (nameOffset + name.size) == name && entry < text.size &&
    (← readLE symbols 52 1) == 18 && (← readLE symbols 53 1) == 0 && (← readLE symbols 54 2) == 1 &&
    (← readLE symbols 56 8) == entry && (← readLE symbols 64 8) == text.size - entry) "heap ELF export disagrees"
  let note ← payload 3
  need ((← readLE note 0 4) == 12 && (← readLE note 4 4) == provenance.size &&
    (← readLE note 8 4) == 0x43495801 && note.extract 12 24 == "COMPILATRIX".toUTF8.push 0 &&
    note.extract 24 (24 + provenance.size) == provenance &&
    note.size == 24 + (provenance.size + 3) / 4 * 4) "heap ELF provenance disagrees"

def inspect (row snapshot : Json) (bytes wire : ByteArray) (shared : Bool := false) (graph : Bool := false) : IO Unit := do
  if shared then need ((← strField row "emission") == "heap-block-sharing/1") "heap shared emission policy disagrees"
  if graph then need ((← strField row "emission") == "heap-cfg-graph/1") "heap graph emission policy disagrees"
  need ((← strField snapshot "format") == "compilatrix/source-native-heap/1" &&
    (← strField snapshot "policy") == "physical-leaf-cfg/1" && (← field snapshot "row") == row)
    "heap snapshot policy/row disagrees"
  let name ← strField row "name"
  need (names.contains name) "unknown heap fixture family"
  let source := sourceFamily name
  need ((← strField row "origin") == (if source then "source" else "physical") &&
    (← number row "runtime_parameters") == arity name) "heap origin/runtime arity disagrees"
  let root ← strField row "root"
  let entry ← strField row "entry"
  need (isHex 64 root && isHex 64 entry) "heap content root is invalid"
  need (wire.size == (← number row "snapshot_bytes") && IxIR2Check.root wire == root) "heap snapshot root/size disagrees"
  let artifact ← checked (IxIR2Check.decode wire)
  need (artifact == (← field snapshot "artifact")) "complete decoded heap snapshot differs from its view"
  need ((← field artifact "policy") == Json.mkObj [
    ("credits", toJson [if source then "callLocalV0" else "suspendedCallsV1"]),
    ("allowExtern", toJson false), ("layout", toJson "baseline-constructor-world/0"),
    ("lowering", toJson (if source then "structured-ownership-lowering/1" else "physical-leaf-cfg-fixture/1")),
    ("passes", toJson ([] : List String)), ("semantics", toJson "ixir2-semantics/0"),
    ("validator", toJson "ixir2-ownership-flow/1")]) "heap artifact policy disagrees"
  let layouts ← arrField artifact "layouts"
  for layout in layouts do
    need (IxIR2Check.root (← byteField layout "preimage") == (← strField layout "identity")) "heap layout preimage disagrees"
  let schemas ← arrField artifact "schemas"
  need (schemas.size == 2 && (← arrField artifact "scalarLeaves").isEmpty) "heap schema inventory disagrees"
  for schema in schemas do
    let definition ← field schema "definition"
    need ((← arrField definition "fields").size ≤ 2) "heap schema is not a bounded leaf"
    let layout ← strField definition "layout"
    need (← layouts.anyM fun row => return (← strField row "identity") == layout) "heap schema layout is missing"
  let text ← byteField snapshot "text"
  need (text.size == (← number row "text_bytes") && digest text == (← strField row "text_hash") &&
    bytes.size == (← number row "object_bytes")) "heap text hash/size disagrees"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++ (← checked (unhex ("00 01 " ++ root)))
  need ((← byteField snapshot "provenance") == provenance) "heap snapshot provenance disagrees"
  inspectObject bytes text provenance (← number snapshot "entry_offset")
  let program ← field artifact "program"
  let dependencies ← arrField artifact "dependencies"
  if source then
    let compilation ← field snapshot "source_compilation"
    let sourceRoot ← strField row "source_root"
    need (isHex 64 sourceRoot && (← strField (← field compilation "source") "root") == sourceRoot)
      "heap source root binding disagrees"
    need (dependencies == #[Json.mkObj [("role", toJson "ixir1-graph"),
      ("root", ← field (← field compilation "ixir1") "root")]]) "heap source/IR binding disagrees"
    let sourceProgram ← field (← field compilation "ixir2_diagnostic") "program"
    need ((← PhysicalScalarNativeCheck.exportAddress sourceProgram (arity name) 32 (← field sourceProgram "main")) == entry &&
      (← exportAddress program (arity name) 32 (← field program "main")) == entry) "heap source export binding disagrees"
  else
    need ((← field snapshot "source_compilation") == Json.null && (← field row "source_root") == Json.null && dependencies.isEmpty)
      "heap physical fixture claims a source origin"
  let selected ← arrField snapshot "selected"
  let functions ← number row "functions"
  let index ← number row "entry_index"
  let depth ← number row "stack_depth"
  need (selected.size == functions && functions > 0 && functions ≤ 32 && index < functions &&
    depth == index + 1 && (← number row "workspace_words") == 272 + 34 * depth + 2) "heap selection/stack reservation disagrees"
  let rootProfile := selected[index]!
  need ((← strField rootProfile "address") == entry &&
    (← field rootProfile "parameters") == toJson (Array.replicate (arity name) "scalar") &&
    (← number rootProfile "allocations") == demand name && (← number row "allocation_demand") == demand name &&
    (← number rootProfile "controls") == (← number row "control_bound")) "heap entry profile disagrees"
  let mut identities : Array Json := #[]
  let mut operations : List String := []
  for profile in selected do
    let address ← strField profile "address"
    let parameters ← arrField profile "parameters"
    let identity := toJson #[toJson address, toJson parameters]
    need (!identities.contains identity) "heap duplicate selected profile"
    identities := identities.push identity
    for parameter in parameters do
      need (["scalar", "node", "erased"].contains (← string parameter)) "heap unknown parameter kind"
    let definition ← declared program address
    let blocks ← arrField definition "blocks"
    need (parameters.size == (← arrField (← field definition "signature") "params").size &&
      blocks.size == (← number profile "blocks") && blocks.size > 0 &&
      (← number profile "allocations") ≤ 64 && (← number profile "controls") > 0 &&
      (← number profile "controls") ≤ 1048576) "heap selected function bounds disagree"
    for block in blocks do
      operations := (← string (← arrField block "terminator")[0]!) :: operations
      for instruction in ← arrField block "instructions" do
        operations := (← string (← array instruction)[0]!) :: operations
  let required := if name == "unique-diamond" then ["alloc", "takeUnique", "call", "switchValue", "jump", "allocWith", "dropUnique"]
    else if name == "hot-credit" then ["alloc", "resetShared", "call", "branchCredit", "allocWith", "discardCredit"]
    else if name == "leaf-switch" then ["alloc", "switchValue", "takeUnique", "discardCredit"]
    else if name == "shared-pair" then ["alloc", "fetch", "retainShared", "releaseShared"]
    else if name == "branch-call" || name == "caller-live" then ["alloc", "call", "switchValue", "dropUnique"]
    else ["alloc", "call", "dropUnique"]
  need (required.all operations.contains) "heap fixture CFG features disappeared"
  let nativeBlocks ← number row "native_blocks"
  let certificateChecks ← if graph then do
      let nodes ← number row "graph_nodes"
      let nonterminal ← number row "graph_nonterminal_nodes"
      need (functions ≤ nodes && nodes ≤ 4096 * functions && nonterminal ≤ nodes - functions)
        "heap graph certificate node bounds disagree"
      pure (4 + 2 * (nodes + nonterminal + nativeBlocks) + 6 * functions)
    else pure (if shared then 4 + 2 * nativeBlocks else 3)
  need ((← number row "certificate_checks") == certificateChecks &&
    (← number row "capacity_checks") == (if ["shared-pair", "leaf-switch"].contains name then 4 else 5))
    "heap rejection inventory disagrees"
  let observations ← arrField snapshot "observations"
  let m := UInt64.size - 1
  let inputs : Array (Nat × Nat) := #[(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]
  need (observations.size == inputs.size) "heap observation inventory disagrees"
  let allocations := demand name + if source then 1 else 0
  let reuses := if ["unique-diamond", "hot-credit"].contains name then 1 else 0
  let rcops := (if source then 1 else 0) + if name == "shared-pair" then 1 else 0
  let resets := if name == "hot-credit" then 2 else 0
  let units := if name == "unique-diamond" then 2 else if name == "hot-credit" then 1 else 0
  let heap := toJson #[allocations, allocations, reuses, rcops, allocations, 0]
  let counters := toJson #[allocations, allocations, reuses, rcops, resets, resets, units]
  for index in [:observations.size] do
    let observation := observations[index]!
    let (a, b) := inputs[index]!
    need ((← number observation "left") == a && (← number observation "right") == b) "heap boundary input inventory disagrees"
    need ((← number observation "value") == expected name a b && (← number observation "status") == 0 &&
      (← number observation "byte_steps") > 0 && (← number observation "control_steps") > 0 &&
      (← number observation "control_steps") ≤ (← number row "control_bound") &&
      (← number observation "heap_fuel") ≤ (← number observation "control_steps")) "heap arithmetic/control observation disagrees"
    need ((← field observation "heap") == heap && (← field observation "counters") == counters) "heap counters/reclamation disagree"
    let sourceObservation := if source then Json.mkObj [("evaluated", toJson true),
      ("arguments", toJson (if arity name == 1 then #[a] else #[a,b])), ("heap", heap)] else Json.null
    need ((← field observation "source") == sourceObservation) "heap source application/reclamation disagrees"

def regressions (row snapshot : Json) (bytes wire : ByteArray) (shared : Bool := false) (graph : Bool := false) : IO Nat := do
  let inspect := fun row snapshot bytes wire => HeapNativeCheck.inspect row snapshot bytes wire shared graph
  let mut count := 0
  for (name, path, replacement, fragment) in [
      ("policy", ["policy"], toJson "unknown/1", "policy/row"),
      ("text", ["text"], toJson "c3", "hash/size"),
      ("entry", ["entry_offset"], toJson (999999 : Nat), "ELF export"),
      ("provenance", ["provenance"], toJson "00", "snapshot provenance"),
      ("selection", ["selected"], toJson ([] : List Json), "selection/stack"),
      ("credit policy", ["artifact", "policy", "credits"], toJson ["unknown"], "complete decoded"),
      ("passes", ["artifact", "policy", "passes"], toJson ["unknown"], "complete decoded"),
      ("schemas", ["artifact", "schemas"], toJson ([] : List Json), "complete decoded"),
      ("layouts", ["artifact", "layouts"], toJson ([] : List Json), "complete decoded"),
      ("declarations", ["artifact", "program", "declarations"], toJson ([] : List Json), "complete decoded")] do
    rejects s!"heap {name}" fragment (inspect row (← replaceAt snapshot path replacement) bytes wire)
    count := count + 1
  let observations ← arrField snapshot "observations"
  for (key, replacement, fragment) in [
      ("status", toJson (1 : Nat), "arithmetic/control"),
      ("heap", toJson ([0,0,0,0,0,1] : List Nat), "counters/reclamation"),
      ("counters", toJson ([] : List Nat), "counters/reclamation"),
      ("source", toJson false, "source application/reclamation")] do
    let first ← replaceAt observations[0]! [key] replacement
    let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
    rejects s!"heap {key}" fragment (inspect row changed bytes wire)
    count := count + 1
  let selected ← arrField snapshot "selected"
  let index ← number row "entry_index"
  let profile ← replaceAt selected[index]! ["parameters"] (toJson ([] : List String))
  let changed ← replaceAt snapshot ["selected"] (toJson (selected.set! index profile))
  rejects "heap entry profile" "entry profile" (inspect row changed bytes wire)
  let changedRow ← replaceAt row ["stack_depth"] (toJson (0 : Nat))
  let changed ← replaceAt snapshot ["row"] changedRow
  rejects "heap workspace" "selection/stack" (inspect changedRow changed bytes wire)
  rejects "heap ELF byte" "ELF header" (inspect row snapshot (bytes.set! 0 0) wire)
  rejects "heap snapshot byte" "snapshot root/size" (inspect row snapshot bytes (wire.set! (wire.size - 1) (wire[wire.size - 1]! ^^^ 1)))
  rejects "heap truncated snapshot" "snapshot root/size" (inspect row snapshot bytes (wire.extract 0 (wire.size - 1)))
  count := count + 5
  if sourceFamily (← strField row "name") then
    let changed ← replaceAt snapshot ["source_compilation", "source", "root"] (toJson (String.ofList (List.replicate 64 '0')))
    rejects "heap source root" "source root binding" (inspect row changed bytes wire)
    let changed ← replaceAt snapshot ["source_compilation", "ixir1", "root"] (toJson (String.ofList (List.replicate 64 '0')))
    rejects "heap source IR" "source/IR binding" (inspect row changed bytes wire)
    count := count + 2
  return count

end Compilatrix.Tools.HeapNativeCheck
