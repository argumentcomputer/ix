import IxCC.X86.Exe.Code
import IxCC.X86.ELFValidate

/-!
# The standalone executable writer

`Exe.write` lays out one static ELF64 executable (`ET_EXEC`, x86-64, System V)
from an object `ixcc compile` wrote and the root it runs. No linker,
assembler or C compiler takes part: the object's `.text` is copied byte for
byte (it has no relocations; a relocation is refused), the shell is encoded
here, and its two calls into the object are direct `call rel32`s whose
displacements are computed from the object's own symbol table.

The file, in order (offsets from the start of the file, which is mapped at
`fileBase`):

| Part | Offset | Contents |
| --- | --- | --- |
| ELF header | 0 | entry point at the shell's first byte |
| program headers | 64 | four: the file (`PT_LOAD`, read and execute), the stack and region (`PT_LOAD` at `dataBase`, read and write, no file bytes, so zero-filled), the provenance note (`PT_NOTE`), and `PT_GNU_STACK` (no executable stack) |
| note | 288 | the object's `.note.ixcc` section, unchanged |
| object text | next multiple of 64 | the object's `.text`, unchanged |
| data | next multiple of 8 | the seccomp filter and the messages (`dataBytes`) |
| shell | next multiple of 16 | `shell`, encoded |

There are no section headers. The gaps are zero bytes.
-/

namespace IxCC.X86.Exe

open IxCC.X86

/-- What the writer is given. -/
structure Input where
  /-- The ELF object, as `ixcc compile` wrote it. -/
  object : ByteArray
  /-- The root's export symbol (`cx_<root>`). -/
  root : String
  /-- The root's parameter count. -/
  arity : Nat
  result : ResultKind
  layout : Layout := {}
  deriving Inhabited

/-- Where each part of the file is. -/
structure Placement where
  noteOffset : Nat
  noteSize : Nat
  textOffset : Nat
  textSize : Nat
  dataOffset : Nat
  dataSize : Nat
  shellOffset : Nat
  shellSize : Nat
  deriving BEq, Repr, Inhabited

def Placement.fileSize (p : Placement) : Nat := p.shellOffset + p.shellSize

def alignUp (value alignment : Nat) : Nat := (value + alignment - 1) / alignment * alignment

/-- The ELF header and four program headers. -/
def headersSize : Nat := 64 + 4 * 56

/-- A shell call into the object. -/
structure Call where
  symbol : String
  /-- The file offset of the call's four-byte displacement. -/
  field : Nat
  /-- The address the call returns to. -/
  ret : Nat
  deriving BEq, Repr, Inhabited

/-- The program headers, as (type, flags, offset, address, file size, memory
size, alignment). -/
def programHeaders (L : Layout) (p : Placement) : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(1, 5, 0, fileBase, p.fileSize, p.fileSize, 0x1000),
   (1, 6, 0, dataBase, 0, L.dataSize, 0x1000),
   (4, 4, p.noteOffset, fileBase + p.noteOffset, p.noteSize, p.noteSize, 4),
   (0x6474e551, 6, 0, 0, 0, 0, 16)]

/-- The ELF header's bytes. -/
def headerBytes (p : Placement) : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    le16 2 ++ le16 62 ++ le32 1 ++ le64 (fileBase + p.shellOffset) ++ le64 64 ++ le64 0 ++
    le32 0 ++ le16 64 ++ le16 56 ++ le16 4 ++ le16 64 ++ le16 0 ++ le16 0

def programHeaderBytes (h : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : List UInt8 :=
  let (kind, flags, offset, address, fileSize, memorySize, alignment) := h
  le32 kind ++ le32 flags ++ le64 offset ++ le64 address ++ le64 address ++ le64 fileSize ++
    le64 memorySize ++ le64 alignment

inductive Error where
  | unreadableObject
  | relocations
  | missingExport (symbol : String)
  | arity (n : Nat)
  | enumeration
  | layout
  | shell (error : Shell.Error)
  | tooLarge (size : Nat)
  | contract
  | invalidExecutable
  deriving BEq, Repr, Inhabited

def Error.render : Error → String
  | .unreadableObject => "the object is not one ixcc wrote"
  | .relocations => "the object has relocations"
  | .missingExport s => s!"the object does not export {s}"
  | .arity n => s!"the root takes {n} parameters; the shell passes at most 5"
  | .enumeration => "an enumeration result needs at least one constructor"
  | .layout => "the stack must be a multiple of 16 of at least 8192 bytes, the region at least \
      4096 bytes, and the two together at most 2^40 bytes"
  | .shell _ => "the shell does not encode"
  | .tooLarge n => s!"the file ({n} bytes) does not fit below the stack and region"
  | .contract => "the layout does not keep the driver contract"
  | .invalidExecutable => "the written executable does not pass its check"

/-- What the object gives the executable: its text, its note, and the offsets
of `cx_init` and the root in its text. -/
structure ObjectParts where
  text : ByteArray
  note : ByteArray
  initOffset : Nat
  rootOffset : Nat

def objectParts (object : ByteArray) (root : String) : Except Error ObjectParts := do
  let some view := ELFRead.parse object | throw .unreadableObject
  unless view.relocations.isEmpty do throw .relocations
  let some noteSection := view.sections[3]? | throw .unreadableObject
  let some initOffset := ELF.symbol? object initSymbol | throw (.missingExport initSymbol)
  let some rootOffset := ELF.symbol? object root | throw (.missingExport root)
  return { text := view.text, note := noteSection.data, initOffset, rootOffset }

/-- The planned file: its placement, the shell's patched bytes and its calls. -/
structure Plan where
  placement : Placement
  shell : ByteArray
  calls : List Call
  /-- The file offsets of the shell's `syscall` instructions. -/
  syscalls : List Nat
  deriving Inhabited

/-- Lay out the executable for `input` (everything but the byte assembly). -/
def plan (input : Input) (parts : ObjectParts) : Except Error Plan := do
  unless input.arity ≤ 5 do throw (.arity input.arity)
  if input.result == .enum 0 then throw .enumeration
  unless input.layout.check do throw .layout
  let noteOffset := headersSize
  let textOffset := alignUp (noteOffset + parts.note.size) 64
  let dataOffset := alignUp (textOffset + parts.text.size) 8
  let data := dataBytes input.arity (fileBase + dataOffset)
  let shellOffset := alignUp (dataOffset + data.size) 16
  let spec : Spec :=
    { arity := input.arity, result := input.result, root := input.root, layout := input.layout
      data := fileBase + dataOffset }
  let program := shell spec
  let encoded ← (Shell.encode program).mapError Error.shell
  let placement : Placement :=
    { noteOffset, noteSize := parts.note.size, textOffset, textSize := parts.text.size, dataOffset
      dataSize := data.size, shellOffset, shellSize := encoded.text.size }
  unless fileBase + placement.fileSize ≤ dataBase do throw (.tooLarge placement.fileSize)
  let mut text := encoded.text
  let mut calls := []
  for (field, symbol) in encoded.exportCalls do
    let target := if symbol == initSymbol then parts.initOffset
      else if symbol == input.root then parts.rootOffset
      else 0
    unless symbol == initSymbol || symbol == input.root do throw (.missingExport symbol)
    let displacement := Int.ofNat (textOffset + target) - Int.ofNat (shellOffset + field + 4)
    unless Encode.fitsSigned32 displacement do throw .contract
    text ← (Encode.patchSigned32 text field displacement).mapError fun _ => .contract
    calls := calls ++ [{ symbol, field := shellOffset + field, ret := fileBase + shellOffset + field + 4 }]
  let syscalls := (Shell.syscallOffsets program encoded).map (shellOffset + ·)
  return { placement, shell := text, calls, syscalls }

/-- `bytes` padded with zeros to `size`. -/
def padTo (bytes : List UInt8) (size : Nat) : List UInt8 := bytes ++ List.replicate (size - bytes.length) 0

/-- The file's bytes. -/
def assemble (input : Input) (parts : ObjectParts) (pl : Plan) : ByteArray :=
  let p := pl.placement
  let headers := headerBytes p ++ (programHeaders input.layout p).flatMap programHeaderBytes
  let withNote := padTo headers p.noteOffset ++ parts.note.toList
  let withText := padTo withNote p.textOffset ++ parts.text.toList
  let withData := padTo withText p.dataOffset ++ (dataBytes input.arity (fileBase + p.dataOffset)).toList
  ⟨(padTo withData p.shellOffset ++ pl.shell.toList).toArray⟩

/-- An executable before its check: the bytes and the plan they follow. -/
structure Output where
  bytes : ByteArray
  plan : Plan
  deriving Inhabited

/-- Write the executable (unchecked; `writeChecked` checks it). -/
def write (input : Input) : Except Error Output := do
  let parts ← objectParts input.object input.root
  let pl ← plan input parts
  return { bytes := assemble input parts pl, plan := pl }

end IxCC.X86.Exe
