import Ix.Compiler.X86.Basic

/-!
# Staged x86-64 v0 encoder

This module is intentionally downstream of the typed target AST and has no
dependency on IxIR₂ or instruction selection.  It emits fixed-shape encodings
with rel32 placeholders, resolves block-local relocations after layout, and
retains named runtime calls as explicit object-writer relocations.

The E1 modules prove local per-form decode/execution agreement with the
independent Decode/ByteEval model. Complete stream layout, symbolic-PC/byte-RIP
correspondence and object relocation composition remain E2 obligations;
agreement with an external ISA reference remains the separate S2 boundary.
-/

namespace Ix.Compiler.X86.Encode

open Ix.Compiler.X86

def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def byte (value : UInt8) : ByteArray := bytes [value]

def littleEndian (count : Nat) (value : Word) : ByteArray :=
  ByteArray.mk <| (List.range count).toArray.map fun index =>
    (value >>> UInt64.ofNat (8 * index)).toUInt8

def imm32Bytes (value : Imm32) : ByteArray :=
  littleEndian 4 value.toUInt64

def signed32Bytes (value : Int) : ByteArray :=
  imm32Bytes (Int32.ofInt value).toUInt32

def gprCode : GPR → UInt8
  | .rax => 0
  | .rcx => 1
  | .rdx => 2
  | .rbx => 3
  | .rsp => 4
  | .rbp => 5
  | .rsi => 6
  | .rdi => 7
  | .r8 => 8
  | .r9 => 9
  | .r10 => 10
  | .r11 => 11
  | .r12 => 12
  | .r13 => 13
  | .r14 => 14
  | .r15 => 15

def indexRegCode (register : IndexReg) : UInt8 :=
  gprCode register.gpr

def registerLow (code : UInt8) : Nat := code.toNat % 8
def registerExtended (code : UInt8) : Bool := decide (8 ≤ code.toNat)

def modRM (mode register rm : Nat) : UInt8 :=
  UInt8.ofNat (mode * 64 + (register % 8) * 8 + rm % 8)

def sib (scale index base : Nat) : UInt8 :=
  UInt8.ofNat ((scale % 4) * 64 + (index % 8) * 8 + base % 8)

def scaleBits : Scale → Nat
  | .one => 0
  | .two => 1
  | .four => 2
  | .eight => 3

/-- Legacy operand-size prefix followed by an always-present REX prefix.
Always emitting REX keeps byte-register selection structural (`spl`, `bpl`,
`sil`, `dil` rather than the legacy high-byte registers). -/
def prefixes (operand16 rexW rexR rexX rexB : Bool) : ByteArray :=
  let legacy := if operand16 then byte 0x66 else ByteArray.empty
  let rex : UInt8 := UInt8.ofNat <|
    0x40 + (if rexW then 8 else 0) + (if rexR then 4 else 0) +
      (if rexX then 2 else 0) + (if rexB then 1 else 0)
  legacy ++ byte rex

def widthPrefixes (width : Width) (rexR rexX rexB : Bool) : ByteArray :=
  prefixes (width == .w16) (width == .w64) rexR rexX rexB

structure MemoryTail where
  rexX : Bool
  rexB : Bool
  bytes : ByteArray

def memoryTail (regField : UInt8) (address : MemAddr) : MemoryTail :=
  let displacement := imm32Bytes address.displacement
  let regLow := registerLow regField
  let indexCode := address.index.map indexRegCode
  let indexLow := match indexCode with
    | none => 4
    | some code => registerLow code
  let rexX := match indexCode with
    | none => false
    | some code => registerExtended code
  match address.base with
  | none =>
      { rexX
        rexB := false
        bytes := bytes [modRM 0 regLow 4,
          sib (scaleBits address.scale) indexLow 5] ++ displacement }
  | some base =>
      let baseCode := gprCode base
      let baseLow := registerLow baseCode
      let useSib := address.index.isSome || baseLow == 4
      if useSib then
        { rexX
          rexB := registerExtended baseCode
          bytes := bytes [modRM 2 regLow 4,
            sib (scaleBits address.scale) indexLow baseLow] ++ displacement }
      else
        { rexX := false
          rexB := registerExtended baseCode
          bytes := byte (modRM 2 regLow baseLow) ++ displacement }

def encodeMemory (operand16 rexW : Bool) (opcode : ByteArray)
    (regField : UInt8) (address : MemAddr) : ByteArray :=
  let tail := memoryTail regField address
  prefixes operand16 rexW (registerExtended regField) tail.rexX tail.rexB ++
    opcode ++ tail.bytes

def encodeRegReg (width : Width) (opcode : UInt8)
    (regField rm : GPR) : ByteArray :=
  widthPrefixes width (registerExtended (gprCode regField)) false
      (registerExtended (gprCode rm)) ++
    bytes [opcode, modRM 3 (registerLow (gprCode regField))
      (registerLow (gprCode rm))]

def moveOpcode : Width → UInt8
  | .w8 => 0x88
  | .w16 | .w32 | .w64 => 0x89

def aluOpcode (operation : AluOp) (width : Width) : UInt8 :=
  let wide : UInt8 := match operation with
    | .add => 0x01
    | .or => 0x09
    | .and => 0x21
    | .sub => 0x29
    | .xor => 0x31
  if width == .w8 then wide - 1 else wide

def aluExtension : AluOp → Nat
  | .add => 0
  | .or => 1
  | .and => 4
  | .sub => 5
  | .xor => 6

def immediateBytes (width : Width) (value : Word) : ByteArray :=
  match width with
  | .w8 => littleEndian 1 value
  | .w16 => littleEndian 2 value
  | .w32 => littleEndian 4 value
  | .w64 => littleEndian 8 value

def groupImmediateBytes (width : Width) (value : Imm32) : ByteArray :=
  match width with
  | .w8 => littleEndian 1 value.toUInt64
  | .w16 => littleEndian 2 value.toUInt64
  | .w32 | .w64 => imm32Bytes value

def encodeMov (width : Width) (destination : GPR)
    (source : MoveSource) : ByteArray :=
  match source with
  | .reg source => encodeRegReg width (moveOpcode width) source destination
  | .imm value =>
      widthPrefixes width false false (registerExtended (gprCode destination)) ++
        byte (UInt8.ofNat (0xb8 + registerLow (gprCode destination) -
          (if width == .w8 then 8 else 0))) ++
        immediateBytes width value

def encodeLoad (width : Width) (destination : GPR)
    (source : MemAddr) : ByteArray :=
  match width with
  | .w8 => encodeMemory false true (bytes [0x0f, 0xb6])
      (gprCode destination) source
  | .w16 => encodeMemory false true (bytes [0x0f, 0xb7])
      (gprCode destination) source
  | .w32 => encodeMemory false false (byte 0x8b) (gprCode destination) source
  | .w64 => encodeMemory false true (byte 0x8b) (gprCode destination) source

def encodeStore (width : Width) (destination : MemAddr)
    (source : GPR) : ByteArray :=
  encodeMemory (width == .w16) (width == .w64)
    (byte (if width == .w8 then 0x88 else 0x89)) (gprCode source) destination

def encodeLea (destination : GPR) (source : MemAddr) : ByteArray :=
  encodeMemory false true (byte 0x8d) (gprCode destination) source

def encodeAlu (operation : AluOp) (width : Width) (destination : GPR)
    (source : AluSource) : ByteArray :=
  match source with
  | .reg source =>
      encodeRegReg width (aluOpcode operation width) source destination
  | .imm value =>
      widthPrefixes width false false
          (registerExtended (gprCode destination)) ++
        bytes [if width == .w8 then 0x80 else 0x81,
          modRM 3 (aluExtension operation)
            (registerLow (gprCode destination))] ++
        groupImmediateBytes width value

def encodeImul (width : MulWidth) (destination source : GPR) : ByteArray :=
  encodeRegReg width.width 0xaf destination source |>
    fun encoded =>
      -- `encodeRegReg` accepts one opcode byte; insert the mandatory 0x0f
      -- escape immediately before its final opcode/modRM pair.
      let prefixSize := encoded.size - 2
      encoded.extract 0 prefixSize ++ bytes [0x0f, 0xaf] ++
        encoded.extract (prefixSize + 1) encoded.size

def encodePush (source : GPR) : ByteArray :=
  let rexPrefix := if registerExtended (gprCode source) then byte 0x41
    else ByteArray.empty
  rexPrefix ++ byte (UInt8.ofNat (0x50 + registerLow (gprCode source)))

def encodePop (destination : GPR) : ByteArray :=
  let rexPrefix := if registerExtended (gprCode destination) then byte 0x41
    else ByteArray.empty
  rexPrefix ++ byte (UInt8.ofNat (0x58 + registerLow (gprCode destination)))

def frameBytes (subtract : Bool) (size : FrameSize) : ByteArray :=
  bytes [0x48, 0x81, if subtract then 0xec else 0xc4] ++
    littleEndian 4 size.bytes

def spillAddress (slot : StackSlot) : MemAddr :=
  { base := some .rbp
    displacement := (0 - slot.displacement).toUInt32 }

def encodeSpill (slot : StackSlot) (source : GPR) : ByteArray :=
  encodeStore .w64 (spillAddress slot) source

def encodeReload (destination : GPR) (slot : StackSlot) : ByteArray :=
  encodeLoad .w64 destination (spillAddress slot)

inductive FixupTarget where
  | block (target : BlockId)
  | intrinsic (target : Intrinsic)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Fixup where
  offset : Nat
  target : FixupTarget
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Chunk where
  bytes : ByteArray
  fixups : Array Fixup
  deriving Inhabited

def Chunk.empty : Chunk := { bytes := ByteArray.empty, fixups := #[] }

def Chunk.raw (encoded : ByteArray) : Chunk :=
  { bytes := encoded, fixups := #[] }

def Chunk.append (left right : Chunk) : Chunk :=
  { bytes := left.bytes ++ right.bytes
    fixups := left.fixups ++ right.fixups.map fun fixup =>
      { fixup with offset := left.bytes.size + fixup.offset } }

def rel32 (opcode : ByteArray) (target : FixupTarget) : Chunk :=
  { bytes := opcode ++ bytes [0, 0, 0, 0]
    fixups := #[{ offset := opcode.size, target }] }

def encodeInstr : Instr → Chunk
  | .mov width destination source => .raw (encodeMov width destination source)
  | .load width destination source => .raw (encodeLoad width destination source)
  | .store width destination source => .raw (encodeStore width destination source)
  | .lea destination source => .raw (encodeLea destination source)
  | .alu operation width destination source =>
      .raw (encodeAlu operation width destination source)
  | .imul width destination source => .raw (encodeImul width destination source)
  | .push source => .raw (encodePush source)
  | .pop destination => .raw (encodePop destination)
  | .allocFrame size => .raw (frameBytes true size)
  | .freeFrame size => .raw (frameBytes false size)
  | .spill slot source => .raw (encodeSpill slot source)
  | .reload destination slot => .raw (encodeReload destination slot)
  | .call target => rel32 (byte 0xe8) (.block target)
  | .callRuntime intrinsic => rel32 (byte 0xe8) (.intrinsic intrinsic)

def cmpOpcode : Width → UInt8
  | .w8 => 0x38
  | .w16 | .w32 | .w64 => 0x39

def encodeCompare (comparison : Compare) : ByteArray :=
  match comparison.right with
  | .reg right =>
      encodeRegReg comparison.width (cmpOpcode comparison.width)
        right comparison.left
  | .imm value =>
      widthPrefixes comparison.width false false
          (registerExtended (gprCode comparison.left)) ++
        bytes [if comparison.width == .w8 then 0x80 else 0x81,
          modRM 3 7 (registerLow (gprCode comparison.left))] ++
        groupImmediateBytes comparison.width value

def nearOpcode : Condition → UInt8
  | .eq => 0x84
  | .ne => 0x85
  | .unsignedLt => 0x82
  | .unsignedLe => 0x86
  | .unsignedGt => 0x87
  | .unsignedGe => 0x83
  | .signedLt => 0x8c
  | .signedLe => 0x8e
  | .signedGt => 0x8f
  | .signedGe => 0x8d

def encodeTerminator : Terminator → Chunk
  | .jump target => rel32 (byte 0xe9) (.block target)
  | .branch comparison condition ifTrue ifFalse =>
      (Chunk.raw (encodeCompare comparison)).append
        ((rel32 (bytes [0x0f, nearOpcode condition]) (.block ifTrue)).append
          (rel32 (byte 0xe9) (.block ifFalse)))
  | .tailCall target => rel32 (byte 0xe9) (.block target)
  | .ret => Chunk.raw (byte 0xc3)

def encodeBlock (block : Block) : Chunk :=
  let instructions := block.instructions.foldl
    (fun output instruction => output.append (encodeInstr instruction))
    Chunk.empty
  instructions.append (encodeTerminator block.terminator)

def intrinsicSymbol : Intrinsic → String
  | .allocate => "compilatrix_rt_allocate"
  | .reserve => "compilatrix_rt_reserve"
  | .reuse => "compilatrix_rt_reuse"
  | .releaseReservation => "compilatrix_rt_release_reservation"
  | .retainShared => "compilatrix_rt_retain_shared"
  | .releaseShared => "compilatrix_rt_release_shared"
  | .memcpy => "compilatrix_rt_memcpy"
  | .unsignedDiv => "compilatrix_rt_unsigned_div"

structure Relocation where
  offset : Nat
  symbol : String
  /-- ELF `R_X86_64_PC32` addend.  With P at the four-byte field, -4 makes
  the resolved displacement relative to the following instruction. -/
  addend : Int := -4
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Output where
  text : ByteArray
  blockOffsets : Array Nat
  relocations : Array Relocation
  deriving Inhabited

inductive Error where
  | malformedControl
  | missingBlock (target : BlockId)
  | displacementOutOfRange (source target : Nat)
  | invalidPatch (offset size : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def fitsSigned32 (value : Int) : Bool :=
  decide (-(2 ^ 31 : Int) ≤ value ∧ value < (2 ^ 31 : Int))

def patchSigned32 (input : ByteArray) (offset : Nat) (value : Int) :
    Except Error ByteArray :=
  if offset + 4 ≤ input.size then
    let patch := signed32Bytes value
    .ok <| (List.range 4).foldl (fun output index =>
      output.set! (offset + index) (patch.get! index)) input
  else
    .error (.invalidPatch offset input.size)

private def layout (chunks : Array Chunk) : Array Nat := Id.run do
  let mut offsets := #[]
  let mut cursor := 0
  for chunk in chunks do
    offsets := offsets.push cursor
    cursor := cursor + chunk.bytes.size
  return offsets

private def concatenate (chunks : Array Chunk) : ByteArray :=
  chunks.foldl (fun output chunk => output ++ chunk.bytes) ByteArray.empty

private def locatedFixups (chunks : Array Chunk)
    (offsets : Array Nat) : Array Fixup := Id.run do
  let mut output := #[]
  for index in List.range chunks.size do
    let base := offsets[index]!
    for fixup in chunks[index]!.fixups do
      output := output.push { fixup with offset := base + fixup.offset }
  return output

def encode (checked : Checked) : Except Error Output := do
  let chunks := checked.program.blocks.map encodeBlock
  let offsets := layout chunks
  let mut text := concatenate chunks
  let mut relocations := #[]
  for fixup in locatedFixups chunks offsets do
    match fixup.target with
    | .intrinsic intrinsic =>
        relocations := relocations.push
          { offset := fixup.offset, symbol := intrinsicSymbol intrinsic }
    | .block target =>
        let some targetOffset := offsets[target.toNat]?
          | throw (.missingBlock target)
        let afterPatch := fixup.offset + 4
        let displacement := Int.ofNat targetOffset - Int.ofNat afterPatch
        if fitsSigned32 displacement then
          text ← patchSigned32 text fixup.offset displacement
        else
          throw (Error.displacementOutOfRange afterPatch targetOffset)
  return { text, blockOffsets := offsets, relocations }

def Program.encode (program : Program) : Except Error Output := do
  let checked ← match program.check with
    | .ok checked => pure checked
    | .error _ => throw .malformedControl
  Ix.Compiler.X86.Encode.encode checked

end Ix.Compiler.X86.Encode
