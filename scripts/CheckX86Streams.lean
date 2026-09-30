import Compilatrix.Tools.Check
import Compilatrix.X86.StreamExamples

/-! Complete-stream and serialized-object regressions. The universal laws
live in StreamTrace and ObjectExecution. Mutations below
alter concrete instruction and ELF fields, independently of the writers. -/

open Compilatrix Compilatrix.X86
open Compilatrix.Tools.Check (checked cli)

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def streamResult (program : Program) (output : Encode.Output) (expected : Bool)
    (externals : Stream.ExternalTargets := Stream.unresolved) : Except String Unit := do
  need (Stream.check program output externals == expected) "reference stream result differs"
  need (Stream.checkIndexed program output externals == expected) "indexed stream result differs"
  need (Stream.checkPrepared (Stream.prepareLayout program) output externals == expected) "prepared stream result differs"

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
  streamResult program stream.output true
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
            terminator := .compare { width := .w64, left := .rax, right := .reg .rcx } condition 1 2 },
          { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret },
          { instructions := #[.mov .w64 .rax (.imm 99)], terminator := .ret }] }
      programCase program textBase
      -- The same branch with its false edge falling through to the next
      -- block: the object has no `jmp`, and both edges agree.
      let comparison : Compare := { width := .w64, left := .rax, right := .reg .rcx }
      let fall : Program := {
        entry := 0
        blocks := #[
          { instructions := #[.mov .w64 .rax (.imm left), .mov .w64 .rcx (.imm right)]
            terminator := .branch comparison.row.1 comparison.row.2 condition 2 1 .fall },
          { instructions := #[.mov .w64 .rax (.imm 99)], terminator := .ret },
          { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }
      programCase fall textBase
  return 2 * conditions.length * pairs.length

/-- Branches whose producer is not a register `cmp`: a memory operand (the
prologue's `cmp r, [m]`), a tag `test`, an `add` whose carry decides `jc`
(rule 4) and keeps its sum, and an `add` into memory that a target reads. -/
private def producerCases : Except String Nat := do
  let conditions : List Condition := [.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt, .unsignedGe,
    .signedLt, .signedLe, .signedGt, .signedGe]
  let pairs : List (Word × Word) := [(0, 0), (0, 1), (1, 0),
    (0x8000000000000000, 1), (0x7fffffffffffffff, 0xffffffffffffffff)]
  let slot : MemAddr := { base := some .rsp, displacement := 0xfffffff0 }
  let targets : Array Block := #[
    { instructions := #[.mov .w64 .rdx (.imm 42)], terminator := .ret },
    { instructions := #[.mov .w64 .rdx (.imm 99)], terminator := .ret }]
  let mut count := 0
  for (left, right) in pairs do
    let setup : Array Instr := #[.mov .w64 .rax (.imm left), .mov .w64 .rcx (.imm right), .store .w64 slot .rcx]
    let producers : List (Op × List Arg × List Condition) := [
      ({ mn := .cmp, w := .w64, form := .RM }, [.reg .rax, .mem slot], conditions),
      ({ mn := .cmp, w := .w32, form := .MR }, [.mem slot, .reg .rax], conditions),
      ({ mn := .test, w := .w8, form := .MI }, [.reg .rax, .imm 1], [.eq, .ne]),
      ({ mn := .test, w := .w64, form := .MR }, [.mem slot, .reg .rax], [.eq, .ne, .signedLt]),
      ({ mn := .add, w := .w64, form := .MR }, [.reg .rax, .reg .rcx], [.unsignedLt, .eq]),
      ({ mn := .sub, w := .w64, form := .RM }, [.reg .rax, .mem slot], [.unsignedLt, .eq]),
      ({ mn := .add, w := .w64, form := .MR }, [.mem slot, .reg .rax], [.unsignedLt, .eq])]
    for (producer, args, branchConditions) in producers do
      for condition in branchConditions do
        let program : Program := {
          entry := 0
          blocks := #[{ instructions := setup, terminator := .branch producer args condition 1 2 },
            { targets[0]! with instructions := #[.load .w64 .rsi slot] ++ targets[0]!.instructions },
            targets[1]!] }
        programCase program textBase
        let fall : Program := {
          entry := 0
          blocks := #[{ instructions := setup, terminator := .branch producer args condition 2 1 .fall },
            targets[1]!,
            { targets[0]! with instructions := #[.load .w64 .rsi slot] ++ targets[0]!.instructions }] }
        programCase fall textBase
        count := count + 2
  return count

/-- Fused pairs in complete objects: `xor edx, edx; cmp; setcc dl` (rule
11's 0/1 word) and a `cmp`/`test` into `cmovcc` from memory (rule 10's
select), for every condition. -/
private def fusedCases : Except String Nat := do
  let conditions : List Condition := [.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt, .unsignedGe,
    .signedLt, .signedLe, .signedGt, .signedGe]
  let pairs : List (Word × Word) := [(0, 0), (0, 1), (1, 0),
    (0x8000000000000000, 1), (0x7fffffffffffffff, 0xffffffffffffffff)]
  let slot : MemAddr := { base := some .rsp, displacement := 0xfffffff0 }
  let mut count := 0
  for condition in conditions do
    for (left, right) in pairs do
      let program : Program := {
        entry := 0
        blocks := #[{
          instructions := #[.mov .w64 .rax (.imm left), .mov .w64 .rcx (.imm right), .store .w64 slot .rcx,
            .alu .xor .w32 .rdx (.reg .rdx),
            .fused { mn := .cmp, w := .w64, form := .RM } [.reg .rax, .mem slot] (Op.setccM condition) [.reg .rdx],
            .mov .w64 .rsi (.imm 7),
            .fused { mn := .test, w := .w64, form := .MR } [.reg .rax, .reg .rcx]
              (Op.cmovRM condition .w64) [.reg .rsi, .mem slot],
            .fused { mn := .cmp, w := .w32, form := .MR } [.reg .rcx, .reg .rax]
              (Op.cmovRM condition .w32) [.reg .rdi, .reg .rax]]
          terminator := .ret }] }
      programCase program textBase
      count := count + 1
  return count

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
  let .branch producer args _ _ _ := block.terminator | throw "branch fixture changed"
  let jcc := term + (Encode.encodeOp producer args).size
  corruptions := corruptions ++ [
    ("wrong conditional target", { encoded with text := encoded.text.set! (jcc + 2) 1 }),
    ("wrong fallthrough target", { encoded with text := encoded.text.set! (jcc + 7) 0 }),
    ("changed unreachable block", { encoded with text := encoded.text.set! (encoded.text.size - 1) 0x90 })]
  for (name, changed) in corruptions do
    (streamResult target.program changed false).mapError (fun error => s!"{name}: {error}")
  let (runtime, runtimeInput, _) ← artifact Examples.runtimeProgram
  let encoded := runtimeInput.encoded
  let relocation := encoded.relocations[0]!
  let runtimeCorruptions := [
    { encoded with relocations := #[] },
    { encoded with relocations := #[{ relocation with offset := relocation.offset + 1 }] },
    { encoded with relocations := #[{ relocation with symbol := "wrong_runtime" }] },
    { encoded with relocations := #[{ relocation with addend := 0 }] },
    { encoded with text := encoded.text.set! relocation.offset 1 }]
  for changed in runtimeCorruptions do streamResult runtime.program changed false
  -- A fall-through edge must start exactly where the `jcc` ends: the same
  -- bytes are rejected for a program whose false target is not the next
  -- block, or whose branch claims a `jmp` that is not there.
  let comparison : Compare := { width := .w64, left := .rdi, right := .imm 0 }
  let fallProgram : Program := {
    entry := 0
    blocks := #[
      { instructions := #[], terminator := .branch comparison.row.1 comparison.row.2 .eq 2 1 .fall },
      { instructions := #[.mov .w64 .rax (.imm 1)], terminator := .ret },
      { instructions := #[.mov .w64 .rax (.imm 2)], terminator := .ret }] }
  let (fallTarget, fallInput, _) ← artifact fallProgram
  let fallText := fallInput.encoded
  let jccEnd := (Encode.encodeOp comparison.row.1 comparison.row.2).size + 6
  need (fallText.blockOffsets[1]? == some jccEnd) "fall-through block does not start after the jcc"
  let retarget (terminator : Terminator) : Program :=
    { fallTarget.program with blocks := fallTarget.program.blocks.set! 0 { instructions := #[], terminator } }
  let fallNegatives : List Program := [
    retarget (.branch comparison.row.1 comparison.row.2 .eq 2 2 .fall),
    retarget (.branch comparison.row.1 comparison.row.2 .eq 1 2 .fall),
    retarget (.branch comparison.row.1 comparison.row.2 .eq 2 3 .fall),
    retarget (.branch comparison.row.1 comparison.row.2 .eq 2 1)]
  for program in fallNegatives do streamResult program fallText false
  return corruptions.length + runtimeCorruptions.length + fallNegatives.length

private def indexedLayouts : Except String Nat := do
  let mut cases := 0
  -- Direct typed-x86 fixtures exercise long instruction arrays independently
  -- of the unchanged limits on source/physical graph selection.
  for length in [0, 1, 2, 16, 128, 1024] do
    let body : Block := { instructions := ((List.range length).map fun index =>
      if index % 2 == 0 then Instr.mov .w64 .r9 (.imm (UInt64.ofNat index))
      else Instr.push .r12).toArray, terminator := .jump 1 }
    let program : Program := { entry := 0, blocks := #[body, { instructions := #[], terminator := .ret }] }
    let target ← program.check.mapError reprStr
    let output ← (Encode.encode target).mapError reprStr
    let layout := Stream.prepareLayout program
    streamResult program output true
    need (Stream.checkPrepared layout output) "layout reuse rejected"
    for changed in [
        { output with blockOffsets := output.blockOffsets.push output.text.size },
        { output with blockOffsets := output.blockOffsets.set! 1 (output.blockOffsets[1]! + 1) },
        { output with text := output.text.set! (output.text.size - 2) 0xff }] do
      streamResult program changed false
      need (!Stream.checkPrepared layout changed) "reused layout accepted corruption"
    let badJump := { program with blocks := program.blocks.set! 0 { body with terminator := .jump 2 } }
    streamResult badJump output false
    let badTail := { program with blocks := program.blocks.set! 0 { body with terminator := .tailCall 2 } }
    streamResult badTail output false
    cases := cases + 6
  let (target, input, _) ← artifact Examples.callProgram
  let first := target.program.blocks[0]!
  let badBlock := { first with instructions := first.instructions.map fun instruction =>
    match instruction with | .call _ => .call (UInt32.ofNat target.program.blocks.size) | _ => instruction }
  let badCall := { target.program with blocks := target.program.blocks.set! 0 badBlock }
  streamResult badCall input.encoded false
  streamResult { entry := 0, blocks := #[] } { text := ByteArray.empty, blockOffsets := #[], relocations := #[] } true
  return cases + 2

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

/-- A further export: `symbol?` resolves each exported name to its block,
and the validator pins the further symbol's name, binding, section, value
and size, and the input's list of exports. -/
private def exportCases : Except String Nat := do
  let target ← Examples.callProgram.check.mapError reprStr
  let stream ← (Stream.encode target).mapError reprStr
  let input : ELF.Input :=
    { encoded := stream.output, entryBlock := 0, exportName := "export_main", exports := [("export_forty", 1)],
      provenance }
  let object ← (ELF.writeChecked input).mapError reprStr
  let bytes := object.bytes
  need (ELF.symbol? bytes "export_forty" == stream.output.blockOffsets[1]? &&
      ELF.symbol? bytes "export_main" == stream.output.blockOffsets[0]? && (ELF.symbol? bytes "missing").isNone)
    "exported names do not resolve to their blocks"
  let some view := ELFRead.parse bytes | throw "exports object did not parse"
  let further := view.sections[4]!.header.offset + 3 * 24
  let mutations : List (String × Nat × Nat × Nat) := [("export name", further, 4, 0),
    ("export binding", further + 4, 1, 2), ("export section", further + 6, 2, 0),
    ("export value", further + 8, 8, 0), ("export size", further + 16, 8, 0)]
  for (name, offset, count, value) in mutations do
    let changed := putNatural bytes offset count value
    need (changed != bytes) s!"ineffective corruption: {name}"
    need (!ELF.check input changed) s!"object accepted {name}"
  let inputs : List ELF.Input := [{ input with exports := [] }, { input with exports := [("export_forty", 0)] },
    { input with exports := [("export_other", 1)] },
    { input with exports := [("export_forty", 1), ("export_forty", 1)] }]
  for other in inputs do need (!ELF.check other bytes) "object accepted for a different list of exports"
  return mutations.length + inputs.length

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
    streamResult target.program linked.output true (ELFLink.targets symbols)
    need (linked.view.relocations == view.relocations) "linker changed relocation interpretation"
    let state ← (ByteEval.run linked.output.text textBase 4 ⟨StreamExamples.core, textBase, {}⟩).mapError reprStr
    need (state.rip == ELFLink.address textBase destination && state.core.readReg .rsp == 0x7ff8 &&
      state.core.memory.read64 0x7ff8 == textBase + UInt64.ofNat next) "resolved runtime CALL target or return slot differs"
    for index in [:stream.output.text.size] do
      if index < relocation.offset || relocation.offset + 4 ≤ index then
        need (linked.output.text[index]? == stream.output.text[index]?) "relocation changed an unrelated byte"
    streamResult target.program { linked.output with text := linked.output.text.set! 0 0xf0 } false (ELFLink.targets symbols)
  let .error (.missingSymbol _) := ELFLink.resolve target input object (fun _ => none) | throw "missing runtime symbol accepted"
  for displacement in ([-2147483649, 2147483648] : List Int) do
    streamResult target.program stream.output false (fun _ => some ((next : Int) + displacement))
    let .error (.overflow _ _) := ELFLink.resolve target input object (fun _ => some ((next : Int) + displacement))
      | throw "overflowing runtime relocation accepted"
  let symbols : ELFLink.Symbols := fun _ => some 42
  for bad in [{ relocation with relocationType := 1 }, { relocation with offset := stream.output.text.size },
      { relocation with symbolName := ⟨#[0xff]⟩ }] do
    need (!(ELFLink.apply symbols [bad] stream.output.text).isOk) "malformed relocation accepted"
  return targets.length + 6

/-! ## The failure exit (note 05 §6.1) -/

/-- The caller's callee-saved registers hold sentinels; `rdi` points at the
context, so `entrySp` lives at `[0x100]`. -/
private def sentinelCore : Core :=
  let values : List (GPR × Word) := [(.rbx, 0x1111111111111111), (.rbp, 0x2222222222222222),
    (.r12, 0x3333333333333333), (.r13, 0x4444444444444444), (.r14, 0x5555555555555555),
    (.r15, 0x6666666666666666), (.rdi, 0xc0)]
  values.foldl (fun core (register, value) => core.setReg register value) StreamExamples.core

private def calleeSaved : List GPR := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- A failing export: the typed run halts with the status, meets the
concrete call/stack contract, and the parsed object returns the same status
with `rdx = 0`, the sentinels restored and `rsp` past the return address. -/
private def unwindCase (program : Program) (status : Word) : Except String Unit := do
  let (target, input, bytes) ← artifact program
  let typed := runFrom Runtime.rejecting target 300 sentinelCore
  need (typed.status == .halted status) s!"typed failure exit status: {repr typed.status}"
  need (decide (Stream.SafeTrace Runtime.rejecting target 300 (fun _ => False) (Machine.initial target sentinelCore)))
    "failing export violates the concrete call/stack contract"
  let (result, _) ← runObject bytes input.exportName textBase 900 sentinelCore
  need (result.core.readReg .rax == status && result.core.readReg .rdx == 0 &&
      result.core.readReg .rsp == 0x8010 &&
      calleeSaved.all (fun register => result.core.readReg register == sentinelCore.readReg register) &&
      sameRegisters typed.core (result.core.setReg .rsp 0x8008))
    s!"object failure exit differs: rax {result.core.readReg .rax}, rdx {result.core.readReg .rdx}"

/-- A wrapper whose function first completes a call (its released slot is in
the region the exit drops), then calls a function that fails. -/
private def unwindAfterCall : Program :=
  { entry := 0
    blocks := #[{ instructions := StreamExamples.wrapperPrologue ++ #[.call 4], terminator := .jump 3 }] ++
      StreamExamples.exitGroup ++ #[
        { instructions := #[.push .rbp, .call 5, .call 6, .pop .rbp], terminator := .ret },
        { instructions := #[.mov .w64 .rcx (.imm 5)], terminator := .ret },
        { instructions := #[], terminator := .jump 1 }] }

/-- Replace the failure exit's `unwind` in a program. -/
private def replaceExit (program : Program) (exit : Array Instr) : Program :=
  { program with blocks := program.blocks.set! 2 { program.blocks[2]! with instructions := exit } }

private def unwindCases : Except String Nat := do
  for depth in [0, 1, 3, 7] do
    unwindCase (StreamExamples.unwindCalls depth) 1
  unwindCase unwindAfterCall 1
  -- A corrupted `entrySp` matches no ghost frame: the typed machine traps.
  let innermost : Block :=
    { instructions := #[.mov .w64 .rcx (.imm 0x1234), .store .w64 StreamExamples.entrySlot .rcx]
      terminator := .jump 1 }
  let base := StreamExamples.unwindCalls 3
  let corrupt : Program := { base with blocks := base.blocks.set! 6 innermost }
  let target ← corrupt.check.mapError reprStr
  need ((runFrom Runtime.rejecting target 300 sentinelCore).status == .trapped (.unwindMismatch 0x1234))
    "corrupted entrySp did not trap"
  -- An `entrySp` cell on a live return slot is not ordinary data.
  let target ← (StreamExamples.unwindCalls 3).check.mapError reprStr
  let onSlot := sentinelCore.setReg .rdi 0x7fc8
  need (!decide (Stream.SafeTrace Runtime.rejecting target 300 (fun _ => False) (Machine.initial target onSlot)))
    "entrySp on a live return slot accepted"
  -- An unreadable cell faults identically on both machines.
  let memory : Memory := { sentinelCore.memory with readable := fun address => !(0xc0 ≤ address && address < 0xc8) }
  let unreadable : Core := { sentinelCore with memory }
  let (_, input, bytes) ← artifact (StreamExamples.unwindCalls 3)
  need ((runFrom Runtime.rejecting target 300 unreadable).status == .trapped (.memoryFault ⟨.read, 0xc0, 8⟩))
    "typed unreadable entrySp did not fault"
  let .error (.machine (.memory ⟨.read, 0xc0, 8⟩)) := ObjectEval.run bytes input.exportName textBase 900 unreadable
    | throw "object unreadable entrySp did not fault identically"
  -- A plain `mov rsp, [m]` keeps the ghost frames, so the epilogue's RET traps.
  let plain := replaceExit (StreamExamples.unwindCalls 3)
    #[.load .w64 .rsp StreamExamples.entrySlot, .alu .xor .w32 .rdx (.reg .rdx)]
  let target ← plain.check.mapError reprStr
  let .trapped (.stackMismatch _ _) := (runFrom Runtime.rejecting target 300 sentinelCore).status
    | throw "plain mov rsp before ret did not trap"
  return 9

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

def main : IO UInt32 := cli "x86 stream/object check failed" do
  let streams ← checked completePrograms
  let branches ← checked branchCases
  let producers ← checked producerCases
  let fused ← checked fusedCases
  let streamNegatives ← checked streamCorruptions
  let layouts ← checked indexedLayouts
  let objectNegatives ← checked objectCorruptions
  let exportNegatives ← checked exportCases
  let relocations ← checked relocationCases
  checked returnFault
  let unwinds ← checked unwindCases
  let contracts ← checked contractCases
  IO.println s!"x86 stream/object check ok: {streams} complete streams, {branches} branch objects, {producers} producer branch objects, {fused} fused-pair objects, {streamNegatives} stream corruptions, {layouts} indexed layout cases, {objectNegatives} object corruptions/truncations, {exportNegatives} further-export corruptions, {relocations} relocation cases, {contracts} stack contracts, {unwinds} failure-exit cases, caller-slot fault"
