import Ix.Compiler.Tools.UpstreamNativeCheck

/-! Independent scalar artifact and arithmetic checks. This module imports
no source compiler, native selector, encoder, or machine evaluator. -/
namespace Ix.Compiler.Tools.ScalarNativeCheck
open Lean Check UniqueCheck UpstreamNativeCheck

def expected (name : String) (a b : Nat) : Nat × Nat :=
  let value :=
    if name == "sub" then some (a - b)
    else if name == "nested" && a == 0 then some 7
    else if name == "nested" && a > b then some (a - b)
    else if a + b ≥ UInt64.size then none
    else if name == "helpers" || name == "diamond" then some (a + b - 1)
    else some (a + b)
  (value.getD 0, if value.isSome then 0 else 1)

def inspectObject (bytes text : ByteArray) (entry : Nat) (root : String) (loweringVersion : UInt8 := 5) : IO Unit := do
  need (bytes.size ≥ 64 && bytes.extract 0 7 == (← checked (unhex "7f 45 4c 46 02 01 01"))) "scalar ELF header disagrees"
  need ((← readLE bytes 16 2) == 1 && (← readLE bytes 18 2) == 62 && (← readLE bytes 20 4) == 1 &&
    (← readLE bytes 24 8) == 0 && (← readLE bytes 32 8) == 0 && (← readLE bytes 52 2) == 64 &&
    (← readLE bytes 56 2) == 0 && (← readLE bytes 58 2) == 64 && (← readLE bytes 60 2) == 8 &&
    (← readLE bytes 62 2) == 7) "scalar ELF structure disagrees"
  let table ← readLE bytes 40 8
  need (table + 8 * 64 == bytes.size) "scalar ELF table bounds disagree"
  let sectionOffset := fun index => table + 64 * index
  let payload (index : Nat) : IO ByteArray := do
    slice bytes (← readLE bytes (sectionOffset index + 24) 8) (← readLE bytes (sectionOffset index + 32) 8)
  need ((← payload 1) == text && (← readLE bytes (sectionOffset 1 + 4) 4) == 1 &&
    (← readLE bytes (sectionOffset 1 + 8) 8) == 6) "scalar ELF text disagrees"
  need ((← payload 2).isEmpty && (← payload 6).isEmpty && (← readLE bytes (sectionOffset 6 + 8) 8) == 0)
    "scalar ELF relocation/stack policy disagrees"
  let symbols ← payload 4
  let strings ← payload 5
  need (symbols.size == 72 && (← readLE bytes (sectionOffset 4 + 56) 8) == 24 &&
    (← readLE bytes (sectionOffset 4 + 40) 4) == 5) "scalar ELF symbol table disagrees"
  let nameOffset ← readLE symbols 48 4
  need (strings.extract nameOffset (nameOffset + 19) == "compilatrix_scalar".toUTF8.push 0 &&
    (← readLE symbols 52 1) == 18 && (← readLE symbols 53 1) == 0 && (← readLE symbols 54 2) == 1 &&
    (← readLE symbols 56 8) == entry && (← readLE symbols 64 8) == text.size - entry)
    "scalar ELF export disagrees"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root))) ++ ByteArray.mk #[loweringVersion, 0, 0, 0, 1, 0, 0, 0]
  let note ← payload 3
  need (containsBytes note provenance) "scalar ELF provenance disagrees"

def inspect (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-native-scalar/1" &&
    (← strField snapshot "policy") == "source-scalar-runtime/1" && (← field snapshot "row") == row)
    "scalar snapshot policy/row disagrees"
  let name ← strField row "name"
  need (["add", "sub", "diamond", "helpers", "nested"].contains name) "unknown scalar source family"
  let text ← byteField snapshot "text"
  need (text.size == (← number row "text_bytes") && digest text == (← strField row "text_hash") &&
    bytes.size == (← number row "object_bytes")) "scalar text hash/size disagrees"
  let root ← strField row "ir1_root"
  need (isHex 64 root && isHex 64 (← strField row "source_root")) "scalar source/IR root invalid"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root ++ " 05 00 00 00 01 00 00 00")))
  need ((← byteField snapshot "provenance") == provenance) "scalar snapshot provenance disagrees"
  inspectObject bytes text (← number snapshot "entry_offset") root
  let depth ← number row "stack_depth"
  need (depth > 0 && depth ≤ 32 && depth == (← number row "functions") &&
    (← number row "stack_bytes") == 272 * depth && (← number row "below_entry_bytes") == 272 * depth - 8)
    "scalar stack reservation disagrees"
  let observations ← arrField snapshot "observations"
  need (observations.size == 19) "scalar runtime observation inventory disagrees"
  let m := UInt64.size - 1
  let inputs : Array (Nat × Nat) := #[(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]
  let mut sourceCount := 0
  for index in [:observations.size] do
    let observation := observations[index]!
    let a ← number observation "left"
    let b ← number observation "right"
    need ((a, b) == inputs[index]!) "scalar boundary input inventory disagrees"
    need (a < UInt64.size && b < UInt64.size) "scalar argument conversion overflow"
    let (value, status) := expected name a b
    need ((← number observation "value") == value && (← number observation "status") == status &&
      (← number observation "byte_steps") > 0) "scalar arithmetic observation disagrees"
    let sourceEvaluated := a < 32 && b < 32
    need ((← field observation "source_evaluated") == toJson sourceEvaluated) "scalar source evaluation claim disagrees"
    if sourceEvaluated then sourceCount := sourceCount + 1
  need (sourceCount == 9) "scalar source evaluation count disagrees"

def regressions (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  let changed ← replaceAt snapshot ["policy"] (toJson "unknown/1")
  rejects "scalar policy" "policy/row" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["text"] (toJson "c3")
  rejects "scalar text" "hash/size" (inspect row changed bytes)
  let changed ← replaceAt snapshot ["entry_offset"] (toJson (999999 : Nat))
  rejects "scalar entry" "export" (inspect row changed bytes)
  rejects "scalar object byte" "ELF header" (inspect row snapshot (bytes.set! 0 0))
  let observations ← arrField snapshot "observations"
  let first ← replaceAt observations[0]! ["status"] (toJson (7 : Nat))
  let changed ← replaceAt snapshot ["observations"] (toJson (observations.set! 0 first))
  rejects "scalar observation" "arithmetic" (inspect row changed bytes)

end Ix.Compiler.Tools.ScalarNativeCheck
