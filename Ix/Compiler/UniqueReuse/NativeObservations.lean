import Ix.Compiler.UniqueReuse.NativeObject
import Ix.Compiler.UniqueReuse.NativeSim
import Ix.Compiler.UniqueReuse.Observations

/-! Reproducible compiler and byte-evaluator observations for the bounded
native witness. Native addresses are normalized to checked arena indices;
source, graph, policy, typed target, text, and ELF identities are exported. -/

namespace Ix.Compiler.UniqueReuse.Native.Examples

open Lean Ix.Compiler.Ixon Ix.Compiler.X86 Ix.Compiler.X86.UniqueABI
open Ix.Compiler.UniqueReuse.Examples (need)

def headerValues (layout : Layout) (memory : Memory) : Array Nat :=
  (List.range headerWords).toArray.map fun field => (memory.read64 (layout.address field)).toNat

def pointerIndex (layout : Layout) (pointer : Word) : Except String Json := do
  if pointer == 0 then return Json.null
  let base := layout.base.toNat + headerBytes
  need (base ≤ pointer.toNat && pointer.toNat < base + cellBytes * layout.capacity &&
    (pointer.toNat - base) % cellBytes == 0) "native pointer escaped or is misaligned"
  return toJson ((pointer.toNat - base) / cellBytes)

def heapSnapshot (layout : Layout) (memory : Memory) : Except String Json := do
  let cells ← (List.range layout.capacity).toArray.mapM fun index => do
    let words := (List.range 4).toArray.map fun field => memory.read64 (layout.address (cellSlot index field))
    return Json.arr #[toJson words[0]!.toNat, toJson words[1]!.toNat,
      ← pointerIndex layout words[2]!, toJson words[3]!.toNat]
  return Json.mkObj [("header", toJson (headerValues layout memory)), ("cells", Json.arr cells)]

def nativeList (layout : Layout) (memory : Memory) (length : Nat) (root : Word) : Except String (List Nat) := do
  let mut pointer := root
  let mut values := []
  let mut visited := []
  for index in [:length + 1] do
    let normalized ← pointerIndex layout pointer
    need (normalized != Json.null && !visited.contains normalized) "native graph is null or cyclic"
    visited := normalized :: visited
    let tag := memory.read64 pointer
    need (tag == (if index < length then consTag else nilTag) && memory.read64 (pointer + 24) == 0)
      "native graph tag or padding disagreement"
    if index < length then
      values := values ++ [(memory.read64 (pointer + 8)).toNat]
      pointer := memory.read64 (pointer + 16)
    else need (memory.read64 (pointer + 8) == 0 && memory.read64 (pointer + 16) == 0) "native nil fields not zero"
  return values

def boundary (machine : Machine) : Bool :=
  machine.status != .running || machine.pc.offset == 0 ||
    (machine.pc.block == 2 && machine.pc.offset.toNat % 20 == 0) ||
    (machine.pc.block == 5 && machine.pc.offset == 10)

def prefixSnapshot (layout : Layout) (machine : Machine) (step : Nat) : Except String Json := do
  let header := headerValues layout machine.core.memory
  need (header[0]! == cellBytes * header[2]! && header[2]! ≤ layout.capacity) "native prefix allocation cursor disagreement"
  let tags := (List.range header[2]!).toArray.map fun index =>
    (machine.core.memory.read64 (layout.cell index)).toNat
  let live := tags.countP (fun tag => tag == 0 || tag == 1)
  let reservations := tags.countP (· == 2)
  let freed := tags.countP (· == 3)
  need (live + reservations + freed == tags.size && live == header[5]! && freed == header[3]! &&
    reservations == header[9]! && reservations ≤ 1) "native prefix ownership accounting disagreement"
  need (header[7]! == 0 && live ≤ header[6]! && header[6]! ≤ layout.capacity) "native prefix RC or peak disagreement"
  return Json.mkObj [("step", toJson step), ("block", toJson machine.pc.block.toNat),
    ("offset", toJson machine.pc.offset.toNat), ("halted", toJson (machine.status != .running)),
    ("header", toJson header), ("tags", toJson tags)]

private def observe (layout : Layout) (values : List Word) (main release : Checked) : Except String Json := do
  let initial : Core :=
    { registers := (Registers.zero.set .rdi layout.base).set .rsp 0x8008
      memory := initialMemory layout Memory.unmapped }
  let mut machine := Machine.initial main initial
  let mut prefixes := #[]
  for count in [:UniqueTarget.controlCost values + 1] do
    need (machine.core.readReg .rsp == 0x8008 && machine.core.readReg .rdi == layout.base &&
      machine.core.calleeSavedSnapshot == initial.calleeSavedSnapshot) "native ABI register disagreement"
    match machine.status with
    | .trapped fault => throw s!"native byte evaluator trapped: {repr fault}"
    | _ => pure ()
    if boundary machine then prefixes := prefixes.push (← prefixSnapshot layout machine count)
    if count < UniqueTarget.controlCost values then
      need (machine.status == .running) "native entry halted before its control cost"
      machine := step Runtime.rejecting main machine
  need (machine.status == .halted (layout.cell 1)) "native entry did not return its owned root"
  let observed ← nativeList layout machine.core.memory values.length (machine.core.readReg .rax)
  need (observed == (values.map UInt64.toNat).reverse) "native reversal disagreement"
  let returned ← heapSnapshot layout machine.core.memory
  let dropped := runFrom Runtime.rejecting release (UniqueTarget.releaseCost values.length) machine.core
  need (dropped.status == .halted 0 && dropped.core.readReg .rsp == initial.readReg .rsp &&
    dropped.core.calleeSavedSnapshot == initial.calleeSavedSnapshot) "native release status or ABI disagreement"
  let reclaimed ← heapSnapshot layout dropped.core.memory
  let after := headerValues layout dropped.core.memory
  need (after[2]! == after[3]! && after[5]! == 0 && after[7]! == 0 && after[9]! == 0) "native release leaked"
  let mut failures := #[]
  for (label, cursor, capacity, fuel) in [
      ("one-byte-short", (0 : Word), UInt64.ofNat (UniqueTarget.requiredBytes values - 1), 7),
      ("zero-capacity", 0, 0, 7),
      ("nonzero-cursor", 1, UInt64.ofNat (UniqueTarget.requiredBytes values), 7),
      ("cursor-overflow", 0xffffffffffffffff, UInt64.ofNat (UniqueTarget.requiredBytes values), 5)] do
    let memory := (initial.memory.write64 (layout.address 0) cursor).write64 (layout.address 1) capacity
    let failed := runFrom Runtime.rejecting main fuel { initial with memory }
    need (failed.status == .halted 0 && failed.core.registers .rsp == initial.registers .rsp) "native capacity guard did not reject"
    for slot in [:layout.slots] do
      need (failed.core.memory.read64 (layout.address slot) == memory.read64 (layout.address slot))
        "native capacity rejection modified arena memory"
    failures := failures.push (toJson label)
  return Json.mkObj [("value", toJson observed), ("root", toJson (1 : Nat)),
    ("returned", returned), ("reclaimed", reclaimed), ("prefixes", Json.arr prefixes),
    ("capacity_rejections", Json.arr failures)]

structure CaseResult where
  name : String
  summary : Json
  snapshot : Json
  mainObject : ByteArray
  releaseObject : ByteArray

private def objectJson (name : String) (object : Object) (program : Program) : Json :=
  Json.mkObj [("file", toJson s!"{name}-{object.role.name}.o"), ("role", toJson object.role.name),
    ("symbol", toJson object.role.symbol), ("identity", toJson (Address.blake3 object.bytes)),
    ("size", toJson object.bytes.size), ("policy_identity", toJson object.policyIdentity),
    ("policy_bytes", Coverage.byteJson object.policyBytes), ("provenance", Coverage.byteJson object.provenance.bytes),
    ("lowering_version", toJson nativeLoweringVersion.toNat), ("role_version", toJson object.role.policyVersion.toNat),
    ("text", Coverage.byteJson object.encoded.text), ("blocks", toJson object.encoded.blockOffsets),
    ("relocations", toJson object.encoded.relocations.size), ("typed_program_diagnostic", toJson (reprStr program))]

def runCase (name : String) (values : List Nat) : Except String CaseResult := do
  let source ← UniqueReuse.Examples.source values
  let compilation ← (UniqueReuse.compile source.constants source.entry source.config).mapError reprStr
  let .native output := Native.select compilation | throw "eligible source skipped native selection"
  let sourceResult ← UniqueReuse.Examples.runCase name values
  let sourcePolicy ← sourceResult.summary.getObjVal? "provenance"
  need (sourcePolicy == toJson compilation.provenance.identity)
    "native and source snapshot compilation identities disagree"
  let main ← output.emit .main
  let release ← output.emit .release
  let observations ← observe output.canonicalLayout output.words output.main output.release
  let returnedHeader ← (← observations.getObjVal? "returned").getObjVal? "header"
  let reclaimedHeader ← (← observations.getObjVal? "reclaimed").getObjVal? "header"
  let summary := Json.mkObj [("name", toJson name), ("input", toJson values), ("value", toJson values.reverse),
    ("source_identity", toJson compilation.provenance.source), ("ixir1_root", toJson compilation.provenance.graph),
    ("source_policy", toJson compilation.provenance.identity), ("main_policy", toJson main.policyIdentity),
    ("release_policy", toJson release.policyIdentity), ("main_object", toJson s!"{name}-main.o"),
    ("release_object", toJson s!"{name}-release.o"), ("main_object_identity", toJson (Address.blake3 main.bytes)),
    ("release_object_identity", toJson (Address.blake3 release.bytes)), ("snapshot", toJson s!"{name}.json"),
    ("main_steps", toJson (UniqueTarget.controlCost output.words)),
    ("release_steps", toJson (UniqueTarget.releaseCost output.words.length)),
    ("headers", Json.mkObj [("returned", returnedHeader), ("reclaimed", reclaimedHeader)])]
  let snapshot := Json.mkObj [("format", toJson "compilatrix/source-native-unique-case/1"), ("summary", summary),
    ("source_pipeline", sourceResult.snapshot), ("abi", Json.mkObj [("policy", toJson UniqueABI.policyTag),
      ("selector", toJson UniqueTarget.policyTag), ("max_length", toJson maxLength),
      ("header_words", toJson headerWords), ("cell_words", toJson cellWords)]),
    ("main", objectJson name main output.main.program), ("release", objectJson name release output.release.program),
    ("observations", observations)]
  return { name, summary, snapshot, mainObject := main.bytes, releaseObject := release.bytes }

def cases : List (String × List Nat) :=
  [("empty", []), ("zero", [0]), ("singleton", [17]), ("three", [1, 2, 3]),
    ("mixed-words", [0, 18446744073709551615, 3, 3, 0, 18446744073709551608, 42]),
    ("word-max", [18446744073709551615]), ("repeated", [9, 9, 9, 9, 9]), ("sixty-four", List.range 64)]

def rejections : Except String (Array Json) := do
  let mut rows := #[]
  for (name, values, policy, limits, fragment) in [
      ("word-overflow", [UInt64.size], ({} : IxIR2.UniqueLower.ReusePolicy), IxIR2.Validate.defaultLimits, "64-bit Word"),
      ("word-overflow-mixed", [7, UInt64.size + 7], {}, IxIR2.Validate.defaultLimits, "64-bit Word"),
      ("length-sixty-five", List.range 65, {}, IxIR2.Validate.defaultLimits, "exceeds 64"),
      ("static-reuse-disabled", [1, 2, 3], { enabled := false }, IxIR2.Validate.defaultLimits, "selected static reuse"),
      ("rewrite-budget-zero", [1, 2, 3], { maxRewrites := 0 }, IxIR2.Validate.defaultLimits, "selected static reuse"),
      ("target-limit-zero", [1, 2, 3], {}, { IxIR2.Validate.defaultLimits with maxDeclarations := 0 }, "translated target")] do
    let source ← UniqueReuse.Examples.source values 65
    let compilation ← (UniqueReuse.compile source.constants source.entry source.config 1000 1000 1000 limits policy).mapError reprStr
    let .skipped reason := Native.select compilation | throw s!"{name}: native rejection unexpectedly selected"
    need (reason.contains fragment) s!"{name}: wrong native rejection: {reason}"
    let fallback := match compilation.backend with | .ownedOnly _ => "ixir1-consuming" | .translated _ => "ixir2-checked"
    rows := rows.push (Json.mkObj [("name", toJson name), ("reason", toJson reason), ("fallback", toJson fallback),
      ("input_length", toJson values.length), ("provenance", toJson compilation.provenance.identity)])
  return rows

def report (results : List CaseResult) (rejections : Array Json) : Json :=
  Json.mkObj [("format", toJson "compilatrix/source-native-unique-report/1"),
    ("cases", toJson (results.map (·.summary))), ("selection_rejections", Json.arr rejections)]

end Ix.Compiler.UniqueReuse.Native.Examples
