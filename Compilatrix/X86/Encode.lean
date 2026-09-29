import Compilatrix.X86.Basic

/-!
# Table-driven x86-64 encoder

`encodeOp` encodes any table row from its encoding descriptor: an optional
operand-size prefix, a REX prefix only when a field needs it (W, an extended
register, or a byte register SPL–DIL), the opcode map and byte (with a
register in its low bits for `O`/`OI` rows), ModRM/SIB with the shortest
displacement (none, disp8 or disp32), and the immediate. The encoder never
enumerates instruction forms. Control transfers are emitted with rel32
placeholders; block-local relocations are resolved after layout, and named
runtime calls stay object-writer relocations.

The E1 modules prove per encoding class that the independent decoder
recovers the row and its operands, and that the byte machine executes them
as the typed machine does. Complete stream layout, symbolic-PC/byte-RIP
correspondence and relocation composition are E2 obligations; agreement
with the processor is tested by the hardware and LLVM gates.
-/

namespace Compilatrix.X86.Encode

open Compilatrix.X86

def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def byte (value : UInt8) : ByteArray := bytes [value]

/-- The low `count` little-endian bytes of a natural number. -/
def leNat : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofNat value :: leNat count (value / 256)

/-- The low `count` little-endian bytes of a word. -/
def le (count : Nat) (value : Word) : List UInt8 := leNat count value.toNat

def littleEndian (count : Nat) (value : Word) : ByteArray :=
  bytes (le count value)

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

def rexByte (w r x b : Bool) : UInt8 :=
  UInt8.ofNat (0x40 + (if w then 8 else 0) + (if r then 4 else 0) +
    (if x then 2 else 0) + (if b then 1 else 0))

/-! ## Operand fields -/

/-- Where a row's operands go: the ModRM.reg or opcode register, the
ModRM.rm operand and the immediate. -/
structure Fields where
  reg : Option GPR := none
  rm : Option Arg := none
  imm : Option Word := none

def fields (form : OpEn) (args : List Arg) : Fields :=
  match form, args with
  | .MR, [rm, .reg reg] => { reg := some reg, rm := some rm }
  | .RM, [.reg reg, rm] => { reg := some reg, rm := some rm }
  | .MI, [rm, .imm value] | .MI8, [rm, .imm value] => { rm := some rm, imm := some value }
  | .M, [rm] | .MC, [rm] => { rm := some rm }
  | .OI, [.reg reg, .imm value] => { reg := some reg, imm := some value }
  | .O, [.reg reg] => { reg := some reg }
  | .RMI, [.reg reg, rm, .imm value] | .RMI8, [.reg reg, rm, .imm value] =>
      { reg := some reg, rm := some rm, imm := some value }
  | .D32, [.imm value] => { imm := some value }
  | _, _ => {}

/-- Bytes after the opcode that address the r/m operand, with the REX bits
they need. -/
structure Tail where
  rexX : Bool := false
  rexB : Bool := false
  bytes : List UInt8 := []

/-- A displacement fits disp8 when it sign-extends from its low byte. -/
def fitsDisp8 (displacement : Imm32) : Bool :=
  (signExtend8 displacement.toUInt8).toUInt32 == displacement

/-- ModRM mode: no displacement when it is zero (RBP/R13 bases excepted,
whose mode-0 encodings mean something else), disp8 when it fits, else
disp32. -/
def dispMode (baseLow : Nat) (displacement : Imm32) : Nat :=
  if displacement == 0 && baseLow != 5 then 0
  else if fitsDisp8 displacement then 1
  else 2

def dispBytes (mode : Nat) (displacement : Imm32) : List UInt8 :=
  if mode == 0 then []
  else if mode == 1 then le 1 displacement.toUInt64
  else le 4 displacement.toUInt64

def memoryTail (regField : Nat) (address : MemAddr) : Tail :=
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
        bytes := [modRM 0 regField 4, sib (scaleBits address.scale) indexLow 5] ++
          le 4 address.displacement.toUInt64 }
  | some base =>
      let baseCode := gprCode base
      let baseLow := registerLow baseCode
      let mode := dispMode baseLow address.displacement
      if address.index.isSome || baseLow == 4 then
        { rexX
          rexB := registerExtended baseCode
          bytes := [modRM mode regField 4, sib (scaleBits address.scale) indexLow baseLow] ++
            dispBytes mode address.displacement }
      else
        { rexB := registerExtended baseCode
          bytes := modRM mode regField baseLow :: dispBytes mode address.displacement }

def rmTail (regField : Nat) : Arg → Tail
  | .reg register =>
      { rexB := registerExtended (gprCode register)
        bytes := [modRM 3 regField (registerLow (gprCode register))] }
  | .mem address => memoryTail regField address
  | .imm _ => {}

/-- The ModRM.reg field: the opcode extension or the register's low bits. -/
def regField (enc : EncDesc) (fields : Fields) : Nat :=
  match enc.modrm with
  | .digit value => value
  | .none | .reg => match fields.reg with
    | some register => registerLow (gprCode register)
    | none => 0

def tail (enc : EncDesc) (fields : Fields) : Tail :=
  match enc.modrm with
  | .none =>
      { rexB := enc.emb == .regLow3 && fields.reg.any fun register => registerExtended (gprCode register) }
  | .reg | .digit _ =>
      match fields.rm with
      | some rm => rmTail (regField enc fields) rm
      | none => {}

def rexR (enc : EncDesc) (fields : Fields) : Bool :=
  enc.modrm == .reg && fields.reg.any fun register => registerExtended (gprCode register)

/-- A byte-register operand with code 4–7 needs a REX prefix to mean
SPL–DIL rather than AH–BH. -/
def byteForce (enc : EncDesc) (fields : Fields) : Bool :=
  (enc.byteReg && fields.reg.any GPR.highByteCode) ||
    (enc.byteRM && match fields.rm with
      | some (.reg register) => register.highByteCode
      | _ => false)

def rexPrefix (enc : EncDesc) (fields : Fields) : List UInt8 :=
  let t := tail enc fields
  if enc.rexW || rexR enc fields || t.rexX || t.rexB || byteForce enc fields then
    [rexByte enc.rexW (rexR enc fields) t.rexX t.rexB]
  else []

def opcodeBytes (enc : EncDesc) (fields : Fields) : List UInt8 :=
  let opcode := match enc.emb with
    | .regLow3 => enc.opcode + UInt8.ofNat (match fields.reg with
        | some register => registerLow (gprCode register)
        | none => 0)
    | .none => enc.opcode
  (if enc.map == .x0F then [0x0f] else []) ++ [opcode]

def immBytes (kind : ImmKind) : Option Word → List UInt8
  | some value => le kind.bytes value
  | none => []

/-- The bytes of one row applied to its operands. -/
def encodeList (o : Op) (args : List Arg) : List UInt8 :=
  let enc := (desc o).enc
  let f := fields o.form args
  (if enc.p66 then [0x66] else []) ++ rexPrefix enc f ++ opcodeBytes enc f ++
    (tail enc f).bytes ++ immBytes enc.imm f.imm

def encodeOp (o : Op) (args : List Arg) : ByteArray := bytes (encodeList o args)

/-! ## Chunks and control -/

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


/-- A control row with a zero rel32 field and its fixup. -/
def rel32 (o : Op) (target : FixupTarget) : Chunk :=
  let encoded := encodeOp o [.imm 0]
  { bytes := encoded
    fixups := #[{ offset := encoded.size - 4, target }] }

def encodeInstr : Instr → Chunk
  | .op o args => .raw (encodeOp o args)
  | .call target => rel32 Op.callRel32 (.block target)
  | .callRuntime intrinsic => rel32 Op.callRel32 (.intrinsic intrinsic)

/-- The `cmp` row of a compare-and-branch. -/
def encodeCompare (comparison : Compare) : ByteArray :=
  encodeOp comparison.row.1 comparison.row.2

/-- The second opcode byte of `jcc rel32`. -/
def nearOpcode (condition : Condition) : UInt8 :=
  (desc (Op.jccRel32 condition)).enc.opcode

def encodeTerminator : Terminator → Chunk
  | .jump target => rel32 Op.jmpRel32 (.block target)
  | .branch comparison condition ifTrue ifFalse =>
      (Chunk.raw (encodeCompare comparison)).append
        ((rel32 (Op.jccRel32 condition) (.block ifTrue)).append
          (rel32 Op.jmpRel32 (.block ifFalse)))
  | .tailCall target => rel32 Op.jmpRel32 (.block target)
  | .ret => Chunk.raw (encodeOp Op.retZO [])

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
  Compilatrix.X86.Encode.encode checked

end Compilatrix.X86.Encode
