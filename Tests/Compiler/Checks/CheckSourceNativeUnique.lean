import Ix.Compiler.Tools.UniqueCheck
import Ix.Compiler.Tools.X86Check

/-! Independent Ixon-to-native artifact checker. Compiler, selector, encoder,
writer, and evaluator modules are absent. Canonical preimages are rebuilt;
binutils decodes the objects and the C harness observes actual machine runs. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.UniqueCheck Ix.Compiler.Tools.X86Check

private def fileName (name : String) : Bool :=
  !name.isEmpty && !name.startsWith "." && !name.contains ".." &&
    name.toList.all (fun char => char.isAlphanum || char == '-' || char == '.')

private def inspectHeap (heap : Json) (input : Array Json) (reclaimed : Bool) : IO Unit := do
  let count := input.size
  let header ← (← arrField heap "header").mapM nat
  need (header.size == 10) "native header shape disagreement"
  need (header[7]! == 0) "native RC disagreement"
  need (header[6]! == count + 2) "native peak disagreement"
  need (header[8]! == 2 * count) "native payload disagreement"
  need (header[9]! == 0) "native reservation leaked"
  let expected : Array Nat := #[32 * (count + 2), 32 * (count + 2), count + 2,
    if reclaimed then count + 2 else 1, count, if reclaimed then 0 else count + 1, count + 2, 0, 2 * count, 0]
  need (header == expected) "native allocation or reclamation disagreement"
  let cells ← arrField heap "cells"
  need (cells.size == count + 2) "native cell inventory disagreement"
  for index in [:cells.size] do
    let fields ← array cells[index]!
    need (fields.size == 4) "native cell arity disagreement"
    need ((← nat fields[3]!) == 0) "native padding disagreement"
    if reclaimed || index == 0 then
      need (fields == #[toJson (3 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]) "native cell not fully reclaimed"
    else if index == count + 1 then
      need (fields == #[toJson (0 : Nat), toJson (0 : Nat), Json.null, toJson (0 : Nat)]) "native nil disagreement"
    else
      need ((← nat fields[0]!) == 1 && fields[1]! == input[count - index]!) "native reversed payload disagreement"
      need (fields[2]! == toJson (index + 1)) "native pointer is cyclic, aliased, or outside its owned chain"

private def inspectPrefixes (observations : Json) (count : Nat) : IO Unit := do
  let prefixes ← arrField observations "prefixes"
  need (prefixes.size == 4 * count + 8) "native macro-boundary inventory disagreement"
  let mut previous := 0
  for index in [:prefixes.size] do
    let row := prefixes[index]!
    let step ← number row "step"
    need ((index == 0 && step == 0) || (index > 0 && previous < step)) "native prefix sequence gap"
    previous := step
    let block ← number row "block"
    let offset ← number row "offset"
    let halted := (← field row "halted") == toJson true
    need (offset == 0 || (block == 2 && offset % 20 == 0) || (block == 5 && offset == 10) || halted)
      "native observation is not a macro boundary"
    let header ← (← arrField row "header").mapM nat
    let tags ← (← arrField row "tags").mapM nat
    need (header.size == 10 && tags.all (· < 4)) "native prefix memory shape disagreement"
    let live := tags.countP (fun tag => tag == 0 || tag == 1)
    let reservations := tags.countP (· == 2)
    let freed := tags.countP (· == 3)
    need (header[0]! == 32 * tags.size && header[1]! == 32 * (count + 2) &&
      header[2]! == tags.size && header[3]! == freed && header[5]! == live && header[9]! == reservations &&
      reservations ≤ 1 && tags.size ≤ count + 2) "native prefix ownership accounting disagreement"
    need (header[7]! == 0 && live ≤ header[6]! && header[6]! ≤ count + 2) "native prefix RC or peak disagreement"
    need (halted == (index + 1 == prefixes.size)) "native prefix halt disagreement"
  need (previous == 51 * count + 62) "native control cost disagreement"
  need ((← field prefixes.back! "header") == (← field (← field observations "returned") "header"))
    "native terminal prefix disagrees"

private def inspectPolicy (row snapshot : Json) (role : String) : IO Unit := do
  let object ← field snapshot role
  let source ← field snapshot "source_pipeline"
  let schema ← field (← field (← field source "specialization") "plan") "schema"
  let input ← arrField row "input"
  let encodedInput ← input.mapM fun value => do return uleb (← nat value)
  let version := if role == "main" then 1 else 2
  need ((← strField object "role") == role && (← strField object "symbol") ==
    (if role == "main" then "compilatrix_main" else "compilatrix_unique_drop")) "native object role disagreement"
  need ((← number object "lowering_version") == 2 && (← number object "role_version") == version)
    "native object policy version disagreement"
  let expected := "compilatrix/native-unique-provenance/1\x00".toUTF8 ++
    (← byteField row "source_policy") ++ (← byteField row "ixir1_root") ++
    blob "unique-list-arena/1".toUTF8 ++ blob "unique-reverse-x86/1".toUTF8 ++ uleb 64 ++ uleb 10 ++ uleb 4 ++
    (← byteField schema "nil") ++ (← byteField schema "cons") ++ vector encodedInput ++
    blob role.toUTF8 ++ uleb 2 ++ uleb version
  need (expected == (← byteField object "policy_bytes")) "native policy preimage disagreement"
  hashField object "policy_bytes" "policy_identity" "native policy"
  need ((← field object "policy_identity") == (← field row s!"{role}_policy")) "native policy summary disagreement"
  let provenance := "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ (← strField row "ixir1_root") ++ " 02 00 00 00 " ++
      (if role == "main" then "01" else "02") ++ " 00 00 00")))
  need (provenance == (← byteField object "provenance")) "native ELF provenance disagreement"
  need ((← number object "relocations") == 0 && !(← strField object "typed_program_diagnostic").isEmpty)
    "native leaf artifact disagreement"
  need ((← strField object "file") == (← strField row s!"{role}_object") &&
    (← field object "identity") == (← field row s!"{role}_object_identity")) "native object summary disagreement"

private def inspectNative (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-native-unique-case/1" &&
    (← field snapshot "summary") == row) "native snapshot/report disagreement"
  let input ← arrField row "input"
  need (input.size ≤ 64) "native accepted excess length"
  for value in input do need ((← nat value) < 18446744073709551616) "native truncated a Nat"
  need ((← field row "value") == Json.arr input.reverse) "native source result disagreement"
  let source ← field snapshot "source_pipeline"
  let sourceRow ← field source "summary"
  inspectSnapshot sourceRow source
  need ((← field sourceRow "input") == Json.arr input && (← field sourceRow "optimized") == toJson true &&
    (← field sourceRow "source_identity") == (← field row "source_identity") &&
    (← field sourceRow "ixir1_root") == (← field row "ixir1_root") &&
    (← field sourceRow "provenance") == (← field row "source_policy")) "native/source compilation disagreement"
  let abi ← field snapshot "abi"
  need ((← strField abi "policy") == "unique-list-arena/1" && (← strField abi "selector") == "unique-reverse-x86/1" &&
    (← number abi "max_length") == 64 && (← number abi "header_words") == 10 && (← number abi "cell_words") == 4)
    "native ABI disagreement"
  for role in ["main", "release"] do inspectPolicy row snapshot role
  need ((← number row "main_steps") == 51 * input.size + 62 &&
    (← number row "release_steps") == 17 * input.size + 16) "native step budget disagreement"
  let observations ← field snapshot "observations"
  need ((← field observations "value") == (← field row "value") && (← number observations "root") == 1)
    "native result root disagreement"
  for (phase, reclaimed) in [("returned", false), ("reclaimed", true)] do
    let heap ← field observations phase
    inspectHeap heap input reclaimed
    need ((← field heap "header") == (← field (← field row "headers") phase)) "native summary counters disagree"
  need ((← field observations "capacity_rejections") == toJson ["one-byte-short", "zero-capacity", "nonzero-cursor", "cursor-overflow"])
    "native capacity rejection inventory disagreement"
  inspectPrefixes observations input.size

private def hexValue (value : String) : IO Nat := do
  let mut number := 0
  for char in value.toList do
    let some digit := hexDigit char | throw (IO.userError "invalid readelf hex offset")
    number := 16 * number + digit
  return number

private def inspectText (readelf : String) (path : FilePath) (expected : ByteArray) : IO Unit := do
  let dump ← run readelf #["-W", "-x", ".text", path.toString]
  let mut actual := ByteArray.empty
  for line in dump.splitOn "\n" do
    let parts := words line
    if !(parts.headD "").startsWith "0x" then continue
    let offset ← hexValue ((parts.headD "").drop 2).toString
    need (offset == actual.size && offset < expected.size) "readelf text offsets disagree"
    let count := min 16 (expected.size - offset)
    let groups := parts.drop 1 |>.take ((count + 3) / 4)
    let row ← checked (unhex (String.join groups))
    need (row.size == count) "readelf text row size disagrees"
    actual := actual ++ row
  need (actual == expected) "ELF text differs from selected encoding"

private def inspectObject (directory : FilePath) (row snapshot : Json) (role readelf objdump : String) : IO Unit := do
  let object ← field snapshot role
  let path := directory / (← strField object "file")
  let content ← IO.FS.readBinFile path
  need (content.size == (← number object "size") && digest content == (← strField object "identity"))
    "native object bytes disagree with identity"
  let elf ← inspectElf readelf path (← strField object "symbol")
  need (elf.contains "There are no relocations in this file.") "native object has external relocations"
  need (containsBytes content (← byteField object "provenance")) "native object lost exact provenance"
  inspectText readelf path (← byteField object "text")
  let disassembly ← disassemble objdump path (← strField object "symbol")
  for forbidden in ["call ", "push ", "pop ", "rsp", "rbx", "rbp", "r12", "r13", "r14", "r15"] do
    need (!disassembly.contains forbidden) s!"native leaf uses forbidden instruction or register: {forbidden}"
  need ((← strField row s!"{role}_object") == path.fileName.getD "") "native object path disagreement"

private def nativeRun (cc readelf : String) (harness directory executable : FilePath) (row snapshot : Json) : IO Unit := do
  let _ ← run cc #["-std=c11", "-O2", "-fomit-frame-pointer", "-Wall", "-Wextra", "-Werror",
    "-Wl,--fatal-warnings", "-no-pie", harness.toString,
    (directory / (← strField row "main_object")).toString, (directory / (← strField row "release_object")).toString,
    "-o", executable.toString]
  let input ← arrField row "input"
  let args ← input.mapM fun value => do return toString (← nat value)
  let observed ← checked (Json.parse (← run executable.toString args))
  let expected ← field snapshot "observations"
  for key in ["root", "value", "returned", "reclaimed", "capacity_rejections"] do
    need ((← field observed key) == (← field expected key)) s!"linked native observation differs from byte evaluator: {key}"
  let headers ← run readelf #["-W", "-l", executable.toString]
  let stacks := (headers.splitOn "\n").filter (·.contains "GNU_STACK")
  need (stacks.length == 1 && !stacks.any (·.contains "RWE")) "native executable stack is executable"

private def regressions (row snapshot : Json) : IO Unit := do
  for (name, path, replacement, fragment) in [
      ("ABI corruption", ["abi", "cell_words"], toJson (3 : Nat), "native ABI disagreement"),
      ("native policy corruption", ["main", "policy_bytes"], toJson "00", "native policy preimage"),
      ("ELF root corruption", ["release", "provenance"], toJson "00", "native ELF provenance"),
      ("role corruption", ["release", "symbol"], toJson "compilatrix_main", "native object role"),
      ("root corruption", ["observations", "root"], toJson (0 : Nat), "native result root")] do
    rejects name fragment (inspectNative row (← replaceAt snapshot path replacement))
  for (fieldIndex, replacement, fragment) in [(7, 1, "native RC"), (6, 99, "native peak"),
      (8, 0, "native payload"), (9, 1, "native reservation")] do
    let header ← arrField (← field (← field snapshot "observations") "returned") "header"
    let changed ← replaceAt snapshot ["observations", "returned", "header"] (Json.arr (header.set! fieldIndex (toJson replacement)))
    rejects "counter corruption" fragment (inspectNative row changed)
  let cells ← arrField (← field (← field snapshot "observations") "returned") "cells"
  let cell ← array cells[1]!
  for (fieldIndex, replacement, fragment) in [(2, toJson (1 : Nat), "native pointer"), (3, toJson (1 : Nat), "native padding")] do
    let changed ← replaceAt snapshot ["observations", "returned", "cells"]
      (Json.arr (cells.set! 1 (Json.arr (cell.set! fieldIndex replacement))))
    rejects "cell corruption" fragment (inspectNative row changed)
  let freed ← arrField (← field (← field snapshot "observations") "reclaimed") "cells"
  let changed ← replaceAt snapshot ["observations", "reclaimed", "cells"] (Json.arr (freed.set! 1 cells[1]!))
  rejects "reclamation corruption" "native cell not fully reclaimed" (inspectNative row changed)

def main (args : List String) : IO UInt32 := cli "source native unique check failed" do
  let args ← checked (parseArgs ["--fixture", "--expected", "--readelf", "--objdump", "--cc", "--harness"] args)
  let some fixture := optional args "--fixture" | throw (IO.userError "--fixture is required")
  let expected ← readJson (option args "--expected" "Tests/Fixtures/Compiler/source-native-unique/expected.json")
  let readelf := option args "--readelf" "readelf"
  let objdump := option args "--objdump" "objdump"
  let native ← nativeArgs args
  IO.FS.withTempDir fun directory => do
    let first := directory / "first"
    let second := directory / "second"
    for output in [first, second] do
      requireAll (← run fixture #[output.toString]) ["source-native-unique ok:"] "native producer"
    let report ← readJson (first / "report.json")
    need (report == expected) "reviewed native source, object, resource, or fallback matrix drifted"
    let rows ← arrField report "cases"
    need (rows.size == 8 && (← arrField report "selection_rejections").size == 6) "native matrix inventory disagreement"
    let mut inventory := ["report.json"]
    for row in rows do
      for key in ["snapshot", "main_object", "release_object"] do
        let name ← strField row key
        need (fileName name && !inventory.contains name) "invalid or duplicate native artifact path"
        inventory := name :: inventory
    inventory := inventory.mergeSort (· ≤ ·)
    for output in [first, second] do
      let files ← output.readDir
      need ((files.toList.map (·.fileName) |>.mergeSort (· ≤ ·)) == inventory) "native artifact inventory drifted"
      for file in files do need (!(← file.path.isDir)) "unexpected native artifact directory"
    for name in inventory do
      need ((← IO.FS.readBinFile (first / name)) == (← IO.FS.readBinFile (second / name))) s!"fresh native artifacts differ: {name}"
    for row in rows do
      let snapshot ← readJson (first / (← strField row "snapshot"))
      inspectNative row snapshot
      for role in ["main", "release"] do inspectObject first row snapshot role readelf objdump
      if let some (cc, harness) := native then nativeRun cc readelf harness first (directory / s!"{← strField row "name"}-native") row snapshot
    let some three := rows.find? (fun row => (row.getObjValAs? String "name").toOption == some "three")
      | throw (IO.userError "missing native three-element regression")
    regressions three (← readJson (first / (← strField three "snapshot")))
    let suffix := if native.isSome then ", all eight linked native runs agree" else ""
    IO.println s!"source native unique check ok: two fresh artifact sets, 16 ELF objects, canonical provenance, 12 native corruption regressions, complete reclamation{suffix}"
