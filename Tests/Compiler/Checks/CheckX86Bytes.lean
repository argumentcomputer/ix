import Ix.Compiler.Tools.Check
import Ix.Compiler.X86.ByteBranch
import Ix.Compiler.X86.ByteCall
import Ix.Compiler.X86.EvalExamples
import Ix.Compiler.UniqueReuse.RuntimeNative
import Ix.Compiler.UniqueReuse.NativeObservations
import Ix.Compiler.X86.RuntimeExecution
import Ix.Compiler.X86.RuntimeInput

/-! Finite regression evidence for the independent decoder and byte evaluator.
The universal local laws live in EncodeExecution/ByteBranch/ByteCall. This gate
also executes the actual source-selected runtime text; the separate GNU and
linked-native gates remain external oracles. -/

open Ix.Compiler Ix.Compiler.X86
open Ix.Compiler.Tools.Check (checked cli)

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def registers : List GPR :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

private def indices : List (Option IndexReg) :=
  [none, some .rax, some .rcx, some .rdx, some .rbx, some .rbp, some .rsi, some .rdi,
   some .r8, some .r9, some .r10, some .r11, some .r12, some .r13, some .r14, some .r15]

private def widths : List Width := [.w8, .w16, .w32, .w64]
private def operations : List AluOp := [.add, .sub, .and, .or, .xor]
private def conditions : List Condition :=
  [.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt, .unsignedGe,
   .signedLt, .signedLe, .signedGt, .signedGe]
private def immediates : List Word :=
  [0, 1, 0x7f, 0x80, 0xff, 0x8000, 0xffff, 0x7fffffff, 0x80000000,
   0xffffffff, 0x8000000000000000, 0xffffffffffffffff]

private def initial : Core :=
  { registers := fun register =>
      if register == .rsp then 0x8008 else if register == .rbp then 0x9000
      else 0xfedcba9876543210 + (Encode.gprCode register).toUInt64 * 0x102030405
    memory := { Memory.flat with bytes := fun address => (address ^^^ (address >>> 8)).toUInt8 } }

private def sameRegisters (left right : Core) : Bool :=
  registers.all fun register => left.readReg register == right.readReg register

private def sameBytes (left right : Memory) (addresses : List Word) : Bool :=
  addresses.all fun address => left.bytes address == right.bytes address &&
    left.readable address == right.readable address && left.writable address == right.writable address

private def touched (instruction : Instr) (core : Core) : Word :=
  match instruction with
  | .load _ _ address | .store _ address _ | .lea _ address => address.eval core
  | .push _ => core.readReg .rsp - 8
  | .pop _ => core.readReg .rsp
  | .spill slot _ | .reload _ slot => core.readReg .rbp - slot.displacement
  | _ => 0

private def instructionCase (target : Checked) (instruction : Instr) (core : Core) : Except String Unit := do
  let bytes := (Encode.encodeInstr instruction).bytes
  let text := Encode.bytes [0xaa, 0xbb] ++ bytes ++ Encode.bytes [0xc3, 0xff]
  need (Decode.decodeAt text 2 == some ⟨Encode.instructionOperation instruction, bytes.size⟩)
    s!"decode or length: {repr instruction}"
  for cut in [:bytes.size] do
    need ((Decode.decodeAt (bytes.extract 0 cut) 0).isNone) s!"accepted truncated form: {repr instruction}, {cut}"
  if Encode.linearInstruction instruction then
    let typed := executeInstr Runtime.rejecting target instruction (Machine.initial target core)
    match ByteEval.step text 0x1000 ⟨core, 0x1002, {}⟩ with
    | .error (.memory fault) =>
        need (typed.status == .trapped (.memoryFault fault)) s!"fault disagreement: {repr instruction}"
    | .error fault => throw s!"unexpected byte fault: {repr instruction}, {repr fault}"
    | .ok result =>
        need (typed.status == .running && sameRegisters typed.core result.core &&
          result.rip == 0x1002 + UInt64.ofNat bytes.size) s!"register or RIP disagreement: {repr instruction}"
        let address := touched instruction core
        let probes := (List.range 24).map fun index => address - 8 + UInt64.ofNat index
        need (sameBytes typed.core.memory result.core.memory probes) s!"memory disagreement: {repr instruction}"

private def instructionMatrix (target : Checked) : Except String Nat := do
  let mut cases : Array Instr := #[]
  for width in widths do
    for destination in registers do
      for source in registers do
        cases := cases.push (.mov width destination (.reg source))
        for operation in operations do cases := cases.push (.alu operation width destination (.reg source))
      for value in immediates do
        cases := cases.push (.mov width destination (.imm value))
        for operation in operations do cases := cases.push (.alu operation width destination (.imm value.toUInt32))
  for width in ([.w16, .w32, .w64] : List MulWidth) do
    for destination in registers do
      for source in registers do cases := cases.push (.imul width destination source)
  for register in registers do
    cases := cases.push (.push register) |>.push (.pop register)
    for index in ([0, 1, 0x7fff, 0xffff] : List UInt16) do
      cases := cases.push (.spill ⟨index⟩ register) |>.push (.reload register ⟨index⟩)
  for size in ([0, 1, 0x7fff, 0xffff] : List UInt16) do
    cases := cases.push (.allocFrame ⟨size⟩) |>.push (.freeFrame ⟨size⟩)
  -- Cross all base/index/scale combinations, including the RSP/R12 and
  -- RBP/R13 SIB holes, with both low and extended destination fields.
  for base in none :: registers.map some do
    for index in indices do
      for scale in ([.one, .two, .four, .eight] : List Scale) do
        for destination in ([.rdi, .r9] : List GPR) do
          let address : MemAddr := { base, index, scale, displacement := 0x80000000 }
          cases := cases.push (.lea destination address)
          for width in widths do
            cases := cases.push (.load width destination address) |>.push (.store width address destination)
  for displacement in ([0, 1, 0x7fffffff, 0x80000000, 0xffffffff] : List Imm32) do
    for register in registers do
      for width in widths do
        let address : MemAddr := { base := some .r13, index := some .r12, scale := .eight, displacement }
        cases := cases.push (.load width register address) |>.push (.store width address register)
  cases := cases.push (.call 0)
  for intrinsic in ([.allocate, .reserve, .reuse, .releaseReservation, .retainShared,
      .releaseShared, .memcpy, .unsignedDiv] : List Intrinsic) do
    cases := cases.push (.callRuntime intrinsic)
  for instruction in cases do instructionCase target instruction initial
  return cases.size

private def branchMatrix : Except String Nat := do
  let mut count := 0
  for width in widths do
    let values := [0, 1, width.mask, width.mask >>> 1, (width.mask >>> 1) + 1]
    for left in values do
      for right in values do
        for source in ([.reg .r12, .imm right.toUInt32] : List AluSource) do
          let core := (initial.setReg .r9 left).setReg .r12 right
          let comparison : Compare := { width, left := .r9, right := source }
          for condition in conditions do
            let raw := (Encode.encodeTerminator (.branch comparison condition 0 0)).bytes
            let comparisonSize := (Encode.encodeCompare comparison).size
            let bytes ← (Encode.patchSigned32 raw (comparisonSize + 2) 13).mapError reprStr
            let bytes ← (Encode.patchSigned32 bytes (comparisonSize + 7) (-19)).mapError reprStr
            let take := comparison.holds condition core
            let result ← (ByteEval.run bytes 0x2000 (if take then 2 else 3) ⟨core, 0x2000, {}⟩).mapError reprStr
            let expected := if take then 0x2000 + UInt64.ofNat (comparisonSize + 6) + 13
              else 0x2000 + UInt64.ofNat (comparisonSize + 11) - 19
            need (result.rip == expected && sameRegisters core result.core && result.flags.test condition == some take)
              s!"patched branch mismatch: {repr comparison}, {repr condition}, {left}, {right}"
            count := count + 1
  return count

private def failureCases (target : Checked) : Except String Unit := do
  for bytes in ([[], [0x90], [0x66, 0x66, 0x48, 0x89, 0xc0], [0x48, 0x48, 0x89, 0xc0],
      [0x66, 0x48, 0x89, 0xc0], [0x42, 0x89, 0xc0], [0x88, 0xe0],
      [0xf0, 0x48, 0x01, 0xc0], [0x0f, 0x0b]] : List (List UInt8)) do
    need ((Decode.decodeAt (Encode.bytes bytes) 0).isNone) s!"unsupported encoding accepted: {repr bytes}"
  for width in widths do
    for byte in [:width.bytes] do
      let memory : Memory := { initial.memory with
        readable := fun address => address != 0x5000 + UInt64.ofNat byte
        writable := fun address => address != 0x5000 + UInt64.ofNat byte }
      let core := { initial with memory }
      instructionCase target (.load width .rax { displacement := 0x5000 }) core
      instructionCase target (.store width { displacement := 0x5000 } .rax) core
  for instruction in ([.push .rsp, .pop .rsp, .spill ⟨0⟩ .r9, .reload .r9 ⟨0⟩] : List Instr) do
    instructionCase target instruction { initial with memory := Memory.unmapped }
  let denied : ByteEval.State := ⟨{ initial with memory := Memory.unmapped }, 0x1000, {}⟩
  for bytes in [Encode.byte 0xc3, (Encode.encodeInstr (.call 0)).bytes] do
    let .error (.memory _) := ByteEval.step bytes 0x1000 denied | throw "unmapped control stack access succeeded"
  let product ← (ByteEval.step (Encode.encodeInstr (.imul .w64 .rax .rax)).bytes 0x1000 ⟨initial, 0x1000, {}⟩).mapError reprStr
  need (product.flags.zero.isNone && product.flags.sign.isNone && product.flags.carry.isSome && product.flags.overflow.isSome)
    "IMUL undefined flag policy changed"
  let .error (.undefinedCondition .eq) := ByteEval.step (Encode.bytes [0x0f, 0x84, 0, 0, 0, 0]) product.rip product
    | throw "branch read an undefined IMUL flag"
  let .error (.invalidPatch _ _) := Encode.patchSigned32 (Encode.bytes [0xe9, 0, 0, 0, 0]) 2 0
    | throw "out-of-bounds relocation accepted"
  for value in ([-2147483648, 2147483647] : List Int) do
    need (Encode.fitsSigned32 value) "signed rel32 endpoint rejected"
    let bytes := Encode.byte 0xe9 ++ Encode.signed32Bytes value
    let result ← (ByteEval.step bytes 0x1000 ⟨initial, 0x1000, {}⟩).mapError reprStr
    need (result.rip == UInt64.ofInt (0x1005 + value)) "signed rel32 endpoint changed target"
  for value in ([-2147483649, 2147483648] : List Int) do
    need (!Encode.fitsSigned32 value) "out-of-range rel32 accepted"
  -- A one-byte corruption must change the decoded operand, and a branch
  -- relocation corruption must change its destination.
  let mov := (Encode.encodeInstr (.mov .w64 .rax (.imm 42))).bytes
  need (Decode.decodeAt (mov.set! 2 43) 0 != Decode.decodeAt mov 0) "immediate corruption was invisible"
  let jump := Encode.byte 0xe9 ++ Encode.imm32Bytes 0
  let changed ← (ByteEval.step (jump.set! 1 1) 0x1000 ⟨initial, 0x1000, {}⟩).mapError reprStr
  need (changed.rip == 0x1006) "relocation corruption was invisible"

private def sentinel : Word := 0xff00
private def textBase : Word := 0x100000

private def runUntilReturn (text : ByteArray) : Nat → ByteEval.State → Except String (ByteEval.State × Nat)
  | 0, _ => .error "byte execution exhausted fuel before returning to the harness"
  | fuel + 1, state => do
      let some decoded := Decode.decodeAt text (state.rip - textBase).toNat
        | throw s!"decode fault at {state.rip}"
      let next ← (ByteEval.step text textBase state).mapError reprStr
      if next.rip == sentinel then
        need (decoded.operation == .ret) "harness exit was not a return"
        return (next, 1)
      let (result, count) ← runUntilReturn text fuel next
      return (result, count + 1)

private def entry (encoded : Encode.Output) (target : Checked) (core : Core) : Except String ByteEval.State := do
  let some offset := encoded.blockOffsets[target.program.entry.toNat]? | throw "encoded entry offset missing"
  return ⟨core, textBase + UInt64.ofNat offset, {}⟩

private def smallPrograms : Except String Unit := do
  for program in [Examples.arithmeticProgram, Examples.stackProgram, Examples.callProgram,
      { entry := 0, blocks := #[{ instructions := #[], terminator := .tailCall 1 },
        { instructions := #[.mov .w64 .rax (.imm 42)], terminator := .ret }] }] do
    let target ← program.check.mapError reprStr
    let encoded ← (Encode.encode target).mapError reprStr
    let core := { (Core.empty 0x8008) with memory := Memory.flat.write64 0x8008 sentinel }
    let typed := runFrom Runtime.rejecting target 100 core
    let (result, _) ← runUntilReturn encoded.text 100 (← entry encoded target core)
    need (typed.status == .halted 42 && result.core.readReg .rax == 42 && result.core.readReg .rsp == 0x8010 &&
      sameRegisters typed.core (result.core.setReg .rsp 0x8008)) "complete arithmetic/stack/call/tail stream mismatch"

private def runtimePrograms : Except String Nat := do
  let source ← UniqueReuse.Runtime.source
  let compilation ← UniqueReuse.Runtime.compile source.constants source.entry
  let .native output := UniqueReuse.Runtime.Native.select compilation | throw "runtime native selection failed"
  let main ← output.emit .main
  let release ← output.emit .release
  need (main.encoded.relocations.isEmpty && release.encoded.relocations.isEmpty) "runtime text has unresolved externals"
  let mut steps := 0
  for (name, values) in UniqueReuse.Native.Examples.cases do
    let words ← UniqueReuse.Runtime.Native.ofNats values
    let bound : PLift (words.length ≤ UniqueABI.maxLength) ←
      if h : words.length ≤ UniqueABI.maxLength then pure ⟨h⟩ else throw "runtime input bound lost"
    let layout := RuntimeExecution.canonicalLayout words bound.down
    let stack : Memory := { Memory.unmapped with
      readable := fun address => 0x7f00 ≤ address && address < 0x8100
      writable := fun address => 0x7f00 ≤ address && address < 0x8100 }
    let core : Core := {
      registers := ((Registers.zero.set .rsp 0x8008).set .rdi layout.base).set .rsi (UInt64.ofNat words.length)
      memory := RuntimeExecution.inputMemory layout words (stack.write64 0x8008 sentinel) }
    let typed := runFrom Runtime.rejecting RuntimeTarget.checked (RuntimeTarget.controlCost words.length) core
    let (result, count) ← runUntilReturn main.encoded.text (3 * RuntimeTarget.controlCost words.length)
      (← entry main.encoded RuntimeTarget.checked core)
    steps := steps + count
    need (typed.status == .halted (layout.cell 1) && result.core.readReg .rsp == 0x8010 &&
      sameRegisters typed.core (result.core.setReg .rsp 0x8008)) s!"runtime return registers: {name}"
    let probes := (List.range (8 * layout.slots)).map fun index => layout.base + UInt64.ofNat index
    need (sameBytes typed.core.memory result.core.memory probes) s!"runtime returned arena: {name}"
    let observed ← UniqueReuse.Native.Examples.nativeList layout result.core.memory words.length (result.core.readReg .rax)
    need (observed == values.reverse) s!"runtime byte reversal: {name}"
    let typedDrop := runFrom Runtime.rejecting RuntimeTarget.releaseChecked (UniqueTarget.releaseCost words.length) typed.core
    let releaseCore := result.core.setReg .rsp 0x8008
    let (dropped, count) ← runUntilReturn release.encoded.text (3 * UniqueTarget.releaseCost words.length)
      (← entry release.encoded RuntimeTarget.releaseChecked releaseCore)
    steps := steps + count
    need (typedDrop.status == .halted 0 && dropped.core.readReg .rsp == 0x8010 &&
      sameRegisters typedDrop.core (dropped.core.setReg .rsp 0x8008) && sameBytes typedDrop.core.memory dropped.core.memory probes)
      s!"runtime release registers/arena: {name}"
    let header := UniqueReuse.Native.Examples.headerValues layout dropped.core.memory
    need (header[2]! == header[3]! && header[5]! == 0 && header[7]! == 0 && header[9]! == 0) s!"runtime byte release leaked: {name}"
  return steps

def main : IO UInt32 := cli "x86 byte execution check failed" do
  let target ← checked (Examples.arithmeticProgram.check.mapError reprStr)
  let forms ← checked (instructionMatrix target)
  let branches ← checked branchMatrix
  checked (failureCases target)
  checked smallPrograms
  let runtimeSteps ← checked runtimePrograms
  IO.println s!"x86 byte execution check ok: {forms} instruction cases, {branches} patched branches, truncation/fault/corruption checks, four complete streams, eight source-selected runtime main/release inputs ({runtimeSteps} byte steps)"
