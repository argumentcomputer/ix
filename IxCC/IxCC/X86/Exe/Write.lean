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

**Frames.** The layout is written for any *frame*: the platform code an
executable embeds (its read-only data and its shell program), the exports
that code calls (one call site each, in order) and the zero-filled
read-and-write segments the loader maps for it (one program header each,
after the file's). The production executable is the frame `Input.frame`:
the shell of `Code.lean`, calling `cx_init` and then the root, over one
segment at `dataBase` holding the stack and the region. A test harness may
embed another frame (more exports, more segments); the writer and its check
(`checkFor`) treat every frame alike, and the production names (`plan`,
`assemble`, `checkWith`, `check`, `writeChecked`) are the production frame's
instances.
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

/-- The platform code an executable embeds, the exports it calls, and the
zero-filled memory the loader maps for it. -/
structure Frame where
  /-- The read-only data, placed at an absolute address. -/
  data : Nat → ByteArray
  /-- The shell, given the absolute address of its read-only data. -/
  code : Nat → Shell.Program
  /-- The exports the shell calls: one call site each, in the order of the
  call sites in the encoded shell. -/
  exports : List String
  /-- The zero-filled read-and-write segments, each as (address, size). -/
  segments : List (Nat × Nat)

/-- The production frame: the shell of `Code.lean` for `input`, calling
`cx_init` and then the root, over one zero-filled segment at `dataBase`
holding the stack and then the region. -/
def Input.frame (input : Input) : Frame where
  data := dataBytes input.arity
  code := fun data =>
    shell { arity := input.arity, result := input.result, root := input.root, layout := input.layout, data }
  exports := [initSymbol, input.root]
  segments := [(dataBase, input.layout.dataSize)]

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

/-- The number of program headers of a frame with `segments` zero-filled
segments: the file, the segments, the note and `PT_GNU_STACK`. -/
def programCount (segments : Nat) : Nat := 3 + segments

/-- The ELF header and the program headers of a frame with `segments`
zero-filled segments. -/
def headersSizeFor (segments : Nat) : Nat := 64 + programCount segments * 56

/-- The ELF header and four program headers (the production frame's). -/
def headersSize : Nat := 64 + 4 * 56

/-- A shell call into the object. -/
structure Call where
  symbol : String
  /-- The file offset of the call's four-byte displacement. -/
  field : Nat
  /-- The address the call returns to. -/
  ret : Nat
  deriving BEq, Repr, Inhabited

/-- The program headers of a frame with zero-filled `segments`, as (type,
flags, offset, address, file size, memory size, alignment). -/
def programHeadersFor (segments : List (Nat × Nat)) (p : Placement) :
    List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(1, 5, 0, fileBase, p.fileSize, p.fileSize, 0x1000)] ++
    segments.map (fun (address, size) => (1, 6, 0, address, 0, size, 0x1000)) ++
    [(4, 4, p.noteOffset, fileBase + p.noteOffset, p.noteSize, p.noteSize, 4),
     (0x6474e551, 6, 0, 0, 0, 0, 16)]

/-- The production frame's program headers. -/
def programHeaders (L : Layout) (p : Placement) : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  programHeadersFor [(dataBase, L.dataSize)] p

/-- The ELF header's bytes, for `count` program headers. -/
def headerBytesFor (count : Nat) (p : Placement) : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    le16 2 ++ le16 62 ++ le32 1 ++ le64 (fileBase + p.shellOffset) ++ le64 64 ++ le64 0 ++
    le32 0 ++ le16 64 ++ le16 56 ++ le16 count ++ le16 64 ++ le16 0 ++ le16 0

/-- The production frame's ELF header. -/
def headerBytes (p : Placement) : List UInt8 := headerBytesFor 4 p

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
  | segments
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
  | .segments => "the zero-filled segments must be page-aligned, nonempty, in increasing order \
      without overlap, and below 2^47"

/-- What the object gives the executable: its text, its note, and the offset
in its text of each export the shell calls. -/
structure ObjectParts where
  text : ByteArray
  note : ByteArray
  offsets : List (String × Nat)

/-- The object's parts for a frame calling `exports`. -/
def objectPartsFor (object : ByteArray) (exports : List String) : Except Error ObjectParts := do
  let some view := ELFRead.parse object | throw .unreadableObject
  unless view.relocations.isEmpty do throw .relocations
  let some noteSection := view.sections[3]? | throw .unreadableObject
  let offsets ← exports.mapM fun symbol =>
    match ELF.symbol? object symbol with
    | some offset => pure (symbol, offset)
    | none => throw (.missingExport symbol)
  return { text := view.text, note := noteSection.data, offsets }

/-- The object's parts for the production frame: `cx_init` and the root. -/
def objectParts (object : ByteArray) (root : String) : Except Error ObjectParts :=
  objectPartsFor object [initSymbol, root]

/-- The planned file: its placement, the shell's patched bytes and its calls. -/
structure Plan where
  placement : Placement
  shell : ByteArray
  calls : List Call
  /-- The file offsets of the shell's `syscall` instructions. -/
  syscalls : List Nat
  deriving Inhabited

/-- The file, `size` bytes mapped at `fileBase`, and the segment
`(address, n)` do not overlap. -/
def apart (size : Nat) (segment : Nat × Nat) : Bool :=
  decide (fileBase + size ≤ segment.1) || decide (segment.1 + segment.2 ≤ fileBase)

/-- The segments are page-aligned and nonempty, in increasing order without
overlap, and end below `2^47`. -/
def segmentsOk : List (Nat × Nat) → Bool
  | [] => true
  | [(a, n)] => a % 0x1000 == 0 && decide (0 < n) && decide (a + n ≤ 2 ^ 47)
  | (a, n) :: (b, m) :: rest =>
    a % 0x1000 == 0 && decide (0 < n) && decide (a + n ≤ b) && segmentsOk ((b, m) :: rest)

/-- Lay out the executable of frame `f` (everything but the byte assembly). -/
def planFor (f : Frame) (parts : ObjectParts) : Except Error Plan := do
  unless segmentsOk f.segments do throw .segments
  let noteOffset := headersSizeFor f.segments.length
  let textOffset := alignUp (noteOffset + parts.note.size) 64
  let dataOffset := alignUp (textOffset + parts.text.size) 8
  let data := f.data (fileBase + dataOffset)
  let shellOffset := alignUp (dataOffset + data.size) 16
  let program := f.code (fileBase + dataOffset)
  let encoded ← (Shell.encode program).mapError Error.shell
  let placement : Placement :=
    { noteOffset, noteSize := parts.note.size, textOffset, textSize := parts.text.size, dataOffset
      dataSize := data.size, shellOffset, shellSize := encoded.text.size }
  unless f.segments.all (apart placement.fileSize) do throw (.tooLarge placement.fileSize)
  let mut text := encoded.text
  let mut calls := []
  for (field, symbol) in encoded.exportCalls do
    let some target := parts.offsets.lookup symbol | throw (.missingExport symbol)
    let displacement := Int.ofNat (textOffset + target) - Int.ofNat (shellOffset + field + 4)
    unless Encode.fitsSigned32 displacement do throw .contract
    text ← (Encode.patchSigned32 text field displacement).mapError fun _ => .contract
    calls := calls ++ [{ symbol, field := shellOffset + field, ret := fileBase + shellOffset + field + 4 }]
  let syscalls := (Shell.syscallOffsets program encoded).map (shellOffset + ·)
  return { placement, shell := text, calls, syscalls }

/-- Lay out the production executable for `input`. -/
def plan (input : Input) (parts : ObjectParts) : Except Error Plan := do
  unless input.arity ≤ 5 do throw (.arity input.arity)
  if input.result == .enum 0 then throw .enumeration
  unless input.layout.check do throw .layout
  planFor input.frame parts

/-- `bytes` padded with zeros to `size`. -/
def padTo (bytes : List UInt8) (size : Nat) : List UInt8 := bytes ++ List.replicate (size - bytes.length) 0

/-- The file's bytes, for frame `f`. -/
def assembleFor (f : Frame) (parts : ObjectParts) (pl : Plan) : ByteArray :=
  let p := pl.placement
  let headers := headerBytesFor (programCount f.segments.length) p ++
    (programHeadersFor f.segments p).flatMap programHeaderBytes
  let withNote := padTo headers p.noteOffset ++ parts.note.toList
  let withText := padTo withNote p.textOffset ++ parts.text.toList
  let withData := padTo withText p.dataOffset ++ (f.data (fileBase + p.dataOffset)).toList
  ⟨(padTo withData p.shellOffset ++ pl.shell.toList).toArray⟩

/-- The production executable's bytes. -/
def assemble (input : Input) (parts : ObjectParts) (pl : Plan) : ByteArray :=
  assembleFor input.frame parts pl

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
