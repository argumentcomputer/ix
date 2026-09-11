import Ix.Compiler.Tools.Check
import Ix.Compiler.X86.StreamExamples
import Ix.Compiler.UniqueReuse.RuntimeObjectSim
import Ix.Compiler.UniqueReuse.NativeObservations
import Ix.Compiler.X86.RuntimeInput

/-! Complete-stream and serialized-object regressions. The universal laws
live in StreamTrace, ObjectExecution and RuntimeObjectSim. Mutations below
alter concrete instruction and ELF fields, independently of the writers. -/

open Ix.Compiler Ix.Compiler.X86
open Ix.Compiler.Tools.Check (checked cli)

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def registers : List GPR :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

private def sameRegisters (left right : Core) : Bool :=
  registers.all fun register => left.readReg register == right.readReg register

private def sameBytes (left right : Memory) (addresses : List Word) : Bool :=
  addresses.all fun address => left.bytes address == right.bytes address &&
    left.readable address == right.readable address && left.writable address == right.writable address

private def provenance : ELF.Provenance := .ixir1Policy (Ixon.Address.replicate 0x42) 3 7
private def sentinel : Word := 0xff00
private def textBase : Word := 0x100000

private def artifact (program : Program) (name := "stream_test") : Except String (Checked × ELF.Input × ByteArray) := do
  let target ← program.check.mapError reprStr
  let stream ← (Stream.encode target).mapError reprStr
  let input : ELF.Input := { encoded := stream.output, entryBlock := program.entry, exportName := name, provenance }
  let object ← (ELF.writeChecked input).mapError reprStr
  return (target, input, object.bytes)

private def runUntilReturn (text : ByteArray) (base : Word) : Nat → ByteEval.State → Except String (ByteEval.State × Nat)
  | 0, _ => .error "byte execution exhausted its bound"
  | fuel + 1, state => do
      let some decoded := Decode.decodeAt text (state.rip - base).toNat | throw "missing instruction boundary"
      let next ← (ByteEval.step text base state).mapError reprStr
      if next.rip == sentinel then
        need (decoded.operation == .ret) "harness exit was not RET"
        return (next, 1)
      let (result, count) ← runUntilReturn text base fuel next
      return (result, count + 1)

private def runObject (bytes : ByteArray) (name : String) (base : Word) (fuel : Nat) (core : Core) :
    Except String (ByteEval.State × Nat) := do
  let some text := ELFRead.text? bytes | throw "object text extraction failed"
  let some offset := ELF.entry? bytes name | throw "object entry extraction failed"
  let (after, count) ← runUntilReturn text base fuel ⟨core, base + UInt64.ofNat offset, {}⟩
  let replay ← (ObjectEval.run bytes name base count core).mapError reprStr
  need (replay.rip == after.rip && sameRegisters replay.core after.core) "whole-object execution disagrees"
  return (after, count)

private def programCase (program : Program) (base : Word) : Except String Unit := do
  let (target, input, bytes) ← artifact program
  let core := StreamExamples.core
  let typed := runFrom Runtime.rejecting target 100 core
  need (decide (Stream.SafeTrace Runtime.rejecting target 100 (fun _ => False) (Machine.initial target core)))
    "complete stream violates the concrete call/stack contract"
  let .halted expected := typed.status | throw "typed stream did not return"
  let (result, count) ← runObject bytes input.exportName base 300 core
  need (result.core.readReg .rax == expected && result.core.readReg .rsp == 0x8010 && count ≤ 300 &&
    sameRegisters typed.core (result.core.setReg .rsp 0x8008)) "complete stream register/return disagreement"
  need (sameBytes typed.core.memory result.core.memory [0x8000, 0x8008, 0x800f, 0x9000])
    "caller/saved-stack memory disagreement"

private def completePrograms : Except String Nat := do
  let programs := [Examples.arithmeticProgram, Examples.stackProgram, Examples.callProgram,
    StreamExamples.tailCall, StreamExamples.nestedCalls, StreamExamples.reusedCalls,
    { entry := 1, blocks := #[{ instructions := #[], terminator := .ret },
      { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }]
  for program in programs do
    programCase program textBase
    programCase program 0xfffffffffffffff0
  let (target, input, bytes) ← artifact StreamExamples.reusedCalls
  let typed := runFrom Runtime.rejecting target 11 StreamExamples.core
  let (result, _) ← runObject bytes input.exportName textBase 33 StreamExamples.core
  need (result.core.readReg .rcx == 42 && result.core.memory.read64 0x7ff8 == 42 &&
    sameBytes typed.core.memory result.core.memory ((List.range 32).map fun i => 0x7ff0 + UInt64.ofNat i))
    "ordinary store did not overwrite the reused return slot"
  return programs.length * 2

private def branchCases : Except String Nat := do
  let conditions : List Condition := [.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt, .unsignedGe,
    .signedLt, .signedLe, .signedGt, .signedGe]
  let pairs : List (Word × Word) := [(0, 0), (0, 1), (1, 0),
    (0x8000000000000000, 1), (0x7fffffffffffffff, 0xffffffffffffffff)]
  for condition in conditions do
    for (left, right) in pairs do
      let program : Program := {
        entry := 0
        blocks := #[
          { instructions := #[.mov .w64 .rax (.imm left), .mov .w64 .rcx (.imm right)]
            terminator := .branch { width := .w64, left := .rax, right := .reg .rcx } condition 1 2 },
          { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret },
          { instructions := #[.mov .w64 .rax (.imm 99)], terminator := .ret }] }
      programCase program textBase
  return conditions.length * pairs.length

private def streamCorruptions : Except String Nat := do
  let (target, input, _) ← artifact Examples.arithmeticProgram
  let encoded := input.encoded
  let mut corruptions : List (String × Encode.Output) := [
    ("truncated text", { encoded with text := encoded.text.extract 0 (encoded.text.size - 1) }),
    ("extra text", { encoded with text := encoded.text.push 0x90 }),
    ("changed immediate", { encoded with text := encoded.text.set! 2 41 }),
    ("unsupported opcode", { encoded with text := encoded.text.set! 0 0xf0 }),
    ("wrong entry offset", { encoded with blockOffsets := encoded.blockOffsets.set! 0 1 }),
    ("missing block offset", { encoded with blockOffsets := #[] }),
    ("unclaimed relocation", { encoded with relocations := #[{ offset := 2, symbol := "unexpected", addend := -4 }] })]
  let block := target.program.blocks[0]!
  let term := Stream.instructionOffset block block.instructions.size
  let .branch comparison _ _ _ := block.terminator | throw "branch fixture changed"
  let jcc := term + (Encode.encodeCompare comparison).size
  corruptions := corruptions ++ [
    ("wrong conditional target", { encoded with text := encoded.text.set! (jcc + 2) 1 }),
    ("wrong fallthrough target", { encoded with text := encoded.text.set! (jcc + 7) 0 }),
    ("changed unreachable block", { encoded with text := encoded.text.set! (encoded.text.size - 1) 0x90 })]
  for (name, changed) in corruptions do need (!Stream.check target.program changed) s!"stream accepted {name}"
  let (runtime, runtimeInput, _) ← artifact Examples.runtimeProgram
  let encoded := runtimeInput.encoded
  let relocation := encoded.relocations[0]!
  let runtimeCorruptions := [
    { encoded with relocations := #[] },
    { encoded with relocations := #[{ relocation with offset := relocation.offset + 1 }] },
    { encoded with relocations := #[{ relocation with symbol := "wrong_runtime" }] },
    { encoded with relocations := #[{ relocation with addend := 0 }] },
    { encoded with text := encoded.text.set! relocation.offset 1 }]
  for changed in runtimeCorruptions do need (!Stream.check runtime.program changed) "stream accepted corrupted external fixup"
  return corruptions.length + runtimeCorruptions.length

-- Mutate little-endian fields without calling the serializer or its helpers.
private def putNatural (bytes : ByteArray) (offset count value : Nat) : ByteArray :=
  (List.range count).foldl (fun bytes index => bytes.set! (offset + index) (UInt8.ofNat (value / 256 ^ index % 256))) bytes

private def objectCorruptions : Except String Nat := do
  let (_, input, bytes) ← artifact Examples.runtimeProgram
  let some view := ELFRead.parse bytes | throw "baseline object did not parse"
  need (ELF.check input bytes) "baseline object did not validate"
  let table := view.header.sectionOffset
  let text := view.sections[1]!.header.offset
  let rela := view.sections[2]!.header.offset
  let note := view.sections[3]!.header.offset
  let symbols := view.sections[4]!.header.offset
  let strings := view.sections[5]!.header
  let names := view.sections[7]!.header
  let descriptor := note + 24
  let domainSize := "compilatrix/x86-object-provenance/1".toUTF8.size
  let fieldMutations : List (String × Nat × Nat × Nat) := [
    ("magic", 0, 1, 0), ("class", 4, 1, 1), ("endianness", 5, 1, 2),
    ("ident padding", 15, 1, 1), ("object type", 16, 2, 2), ("machine", 18, 2, 3),
    ("ELF version", 20, 4, 0), ("executable entry", 24, 8, 1), ("program table", 32, 8, 64),
    ("section table bounds", 40, 8, bytes.size), ("section table overflow", 40, 8, 2^64-1),
    ("header size", 52, 2, 63), ("program count", 56, 2, 1), ("section entry size", 58, 2, 63),
    ("section count", 60, 2, 65535), ("section string index", 62, 2, 5),
    ("text section type", table + 64 + 4, 4, 8), ("writable text", table + 64 + 8, 8, 7),
    ("nonzero section address", table + 64 + 16, 8, 1), ("text alignment", table + 64 + 48, 8, 0),
    ("text bounds", table + 64 + 24, 8, bytes.size), ("text size", table + 64 + 32, 8, 2^64-1),
    ("overlapping sections", table + 128 + 24, 8, text),
    ("missing relocation", table + 128 + 32, 8, 0), ("relocation target section", table + 128 + 44, 4, 3),
    ("symbol strings link", table + 256 + 40, 4, 7), ("local symbol boundary", table + 256 + 44, 4, 3),
    ("executable stack", table + 384 + 8, 8, 4),
    ("instruction byte", text, 1, 0xf0), ("symbol name", symbols + 48, 4, 0),
    ("symbol binding", symbols + 52, 1, 2), ("symbol visibility", symbols + 53, 1, 1),
    ("symbol section", symbols + 54, 2, 0), ("export value", symbols + 56, 8, 1),
    ("export size", symbols + 64, 8, 0), ("runtime symbol defined", symbols + 78, 2, 1),
    ("relocation offset", rela, 8, view.text.size), ("relocation kind", rela + 8, 4, 1),
    ("relocation symbol", rela + 12, 4, 2), ("relocation symbol bounds", rela + 12, 4, 99),
    ("relocation addend", rela + 16, 8, 0), ("note name size", note, 4, 2^32-1),
    ("note descriptor size", note + 4, 4, 2^32-1), ("note type", note + 8, 4, 0),
    ("note name", note + 12, 1, 0), ("provenance domain", descriptor, 1, 0),
    ("provenance separator", descriptor + domainSize, 1, 1),
    ("provenance kind", descriptor + domainSize + 1, 1, 2),
    ("provenance root", descriptor + domainSize + 2, 1, 0x43),
    ("lowering version", descriptor + domainSize + 34, 4, 4),
    ("policy version", descriptor + domainSize + 38, 4, 8),
    ("string table initial NUL", strings.offset, 1, 1),
    ("unterminated symbol name", strings.offset + strings.size - 1, 1, 1),
    ("unterminated section name", names.offset + names.size - 1, 1, 1)]
  for (name, offset, count, value) in fieldMutations do
    let changed := putNatural bytes offset count value
    need (changed != bytes) s!"ineffective corruption: {name}"
    need (!ELF.check input changed) s!"object accepted {name}"
  for cut in [:bytes.size] do need (!ELF.check input (bytes.extract 0 cut)) s!"object accepted truncated prefix {cut}"
  need (!ELF.check input (bytes.push 0)) "object accepted trailing data"
  need ((ELF.entry? bytes "wrong_export").isNone) "wrong exported name resolved"
  need (!ELF.check { input with provenance := .ixir2 (Ixon.Address.replicate 0x42) } bytes) "wrong provenance family accepted"
  let (_, otherInput, otherBytes) ← artifact Examples.arithmeticProgram
  need (!ELF.check otherInput bytes && !ELF.check input otherBytes) "cross-object substitution accepted"
  return fieldMutations.length + bytes.size + 4

private def relocationCases : Except String Nat := do
  let target ← Examples.runtimeProgram.check.mapError reprStr
  let stream ← (Stream.encode target).mapError reprStr
  let input : ELF.Input := { encoded := stream.output, entryBlock := 0, exportName := "runtime_test", provenance }
  let object ← (ELF.writeChecked input).mapError reprStr
  let some view := ELFRead.parse object.bytes | throw "runtime ELF parse failed"
  let relocation := view.relocations[0]!
  let next := relocation.offset + 4
  let targets : List Int := [0x1000, -0x1000, (next : Int) - 2147483648, (next : Int) + 2147483647]
  for destination in targets do
    let symbols : ELFLink.Symbols := fun name => if name == "compilatrix_rt_allocate" then some destination else none
    let linked ← (ELFLink.resolve target input object symbols).mapError reprStr
    need (linked.view.relocations == view.relocations) "linker changed relocation interpretation"
    let state ← (ByteEval.run linked.output.text textBase 4 ⟨StreamExamples.core, textBase, {}⟩).mapError reprStr
    need (state.rip == ELFLink.address textBase destination && state.core.readReg .rsp == 0x7ff8 &&
      state.core.memory.read64 0x7ff8 == textBase + UInt64.ofNat next) "resolved runtime CALL target or return slot differs"
    for index in [:stream.output.text.size] do
      if index < relocation.offset || relocation.offset + 4 ≤ index then
        need (linked.output.text[index]? == stream.output.text[index]?) "relocation changed an unrelated byte"
    need (!Stream.check target.program { linked.output with text := linked.output.text.set! 0 0xf0 } (ELFLink.targets symbols))
      "linked stream accepted unrelated corruption"
  let .error (.missingSymbol _) := ELFLink.resolve target input object (fun _ => none) | throw "missing runtime symbol accepted"
  for displacement in ([-2147483649, 2147483648] : List Int) do
    let .error (.overflow _ _) := ELFLink.resolve target input object (fun _ => some ((next : Int) + displacement))
      | throw "overflowing runtime relocation accepted"
  let symbols : ELFLink.Symbols := fun _ => some 42
  for bad in [{ relocation with relocationType := 1 }, { relocation with offset := stream.output.text.size },
      { relocation with symbolName := ⟨#[0xff]⟩ }] do
    need (!(ELFLink.apply symbols [bad] stream.output.text).isOk) "malformed relocation accepted"
  return targets.length + 6

private def returnFault : Except String Unit := do
  let (_, input, bytes) ← artifact { entry := 0, blocks := #[{ instructions := #[], terminator := .ret }] }
  let .error (.machine (.memory ⟨.read, 0x8008, 8⟩)) :=
    ObjectEval.run bytes input.exportName textBase 1 { StreamExamples.core with memory := Memory.unmapped }
    | throw "top-level RET did not require a readable caller slot"

private def contractCases : Except String Nat := do
  for instruction in ([.load .w64 .rcx { base := some .rsp },
      .store .w64 { base := some .rsp } .rax, .mov .w64 .rbx (.imm 1)] : List Instr) do
    let program : Program := {
      entry := 0
      blocks := #[{ instructions := #[.push .rbp, .call 1, .pop .rbp], terminator := .ret },
        { instructions := #[instruction], terminator := .ret }] }
    let target ← program.check.mapError reprStr
    need (!decide (Stream.SafeTrace Runtime.rejecting target 10 (fun _ => False)
      (Machine.initial target StreamExamples.core))) "unsafe return-slot/callee-save behavior accepted"
  let target ← Examples.callProgram.check.mapError reprStr
  need (!decide (Stream.SafeTrace Runtime.rejecting target 10 (fun _ => False)
    (Machine.initial target (StreamExamples.core.setReg .rsp 0x8000)))) "misaligned call contract accepted"
  let program : Program := {
    entry := 0
    blocks := #[
      { instructions := #[.push .rbp, .call 1,
          .load .w64 .rcx { base := some .rsp, displacement := 0xfffffff8 }, .pop .rbp]
        terminator := .ret },
      { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }
  let target ← program.check.mapError reprStr
  need (!decide (Stream.SafeTrace Runtime.rejecting target 10 (fun _ => False)
    (Machine.initial target StreamExamples.core))) "read of a retired physical return address accepted"
  let holes := Stream.clearRange (Stream.addRange (fun _ => False) 0x7ff8 8) 0x7ff8 4
  need (decide (Stream.ReadableData holes 0x7ff8 4) && !decide (Stream.ReadableData holes 0x7ff8 8))
    "partial store cleared the wrong return-slot bytes"
  return 6

private def runtimeObjects : Except String Nat := do
  let source ← UniqueReuse.Runtime.source
  let compilation ← UniqueReuse.Runtime.compile source.constants source.entry
  let .native output := UniqueReuse.Runtime.Native.select compilation | throw "runtime native selection failed"
  let main ← output.emit .main
  let release ← output.emit .release
  let mut steps := 0
  for (name, values) in UniqueReuse.Native.Examples.cases do
    let words ← UniqueReuse.Runtime.Native.ofNats values
    let bound : PLift (words.length ≤ UniqueABI.maxLength) ←
      if h : words.length ≤ UniqueABI.maxLength then pure ⟨h⟩ else throw "runtime input exceeds ABI"
    let layout := RuntimeExecution.canonicalLayout words bound.down
    let stack : Memory := { Memory.unmapped with
      readable := fun address => 0x7f00 ≤ address && address < 0x8100
      writable := fun address => 0x7f00 ≤ address && address < 0x8100 }
    let core : Core := {
      registers := ((Registers.zero.set .rsp 0x8008).set .rdi layout.base).set .rsi (UInt64.ofNat words.length)
      memory := RuntimeExecution.inputMemory layout words (stack.write64 0x8008 sentinel) }
    let typed := runFrom Runtime.rejecting RuntimeTarget.checked (RuntimeTarget.controlCost words.length) core
    let (result, count) ← runObject main.bytes main.role.symbol textBase (3 * RuntimeTarget.controlCost words.length) core
    steps := steps + count
    need (typed.status == .halted (layout.cell 1) && result.core.readReg .rsp == 0x8010 &&
      sameRegisters typed.core (result.core.setReg .rsp 0x8008)) s!"runtime object return: {name}"
    let probes := (List.range (8 * layout.slots)).map fun index => layout.base + UInt64.ofNat index
    need (sameBytes typed.core.memory result.core.memory probes) s!"runtime object arena: {name}"
    let observed ← UniqueReuse.Native.Examples.nativeList layout result.core.memory words.length (result.core.readReg .rax)
    need (observed == values.reverse) s!"runtime object reversal: {name}"
    let typedDrop := runFrom Runtime.rejecting RuntimeTarget.releaseChecked (UniqueTarget.releaseCost words.length) typed.core
    let (dropped, count) ← runObject release.bytes release.role.symbol textBase (3 * UniqueTarget.releaseCost words.length)
      (result.core.setReg .rsp 0x8008)
    steps := steps + count
    need (typedDrop.status == .halted 0 && dropped.core.readReg .rsp == 0x8010 &&
      sameRegisters typedDrop.core (dropped.core.setReg .rsp 0x8008) && sameBytes typedDrop.core.memory dropped.core.memory probes)
      s!"runtime object release: {name}"
    let header := UniqueReuse.Native.Examples.headerValues layout dropped.core.memory
    need (header[2]! == header[3]! && header[5]! == 0 && header[7]! == 0 && header[9]! == 0) s!"runtime object leaked: {name}"
  return steps

def main : IO UInt32 := cli "x86 stream/object check failed" do
  let streams ← checked completePrograms
  let branches ← checked branchCases
  let streamNegatives ← checked streamCorruptions
  let objectNegatives ← checked objectCorruptions
  let relocations ← checked relocationCases
  checked returnFault
  let contracts ← checked contractCases
  let runtimeSteps ← checked runtimeObjects
  IO.println s!"x86 stream/object check ok: {streams} complete streams, {branches} branch objects, {streamNegatives} stream corruptions, {objectNegatives} object corruptions/truncations, {relocations} relocation cases, {contracts} stack contracts, caller-slot fault, eight actual runtime object pairs ({runtimeSteps} byte steps)"
