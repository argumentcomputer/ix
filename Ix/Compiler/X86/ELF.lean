import Ix.Compiler.X86.Encode
import Ix.Compiler.Ixon.Address

/-!
# Minimal ELF64 relocatable-object writer

The writer packages one encoded x86-64 text world, its named runtime PC32
relocations, one exported entry symbol, and a mandatory Compilatr.ix
provenance note.  It emits no program headers, dynamic-linking metadata, debug
surface, or arbitrary sections.

Like the E0 instruction encoder, this executable writer is not yet connected
to a kernel-checked ELF parser/linker theorem.  `readelf`, `objdump`, and a
native link/run fixture provide independent staging evidence.
-/

namespace Ix.Compiler.X86.ELF

open Ix.Compiler.X86
open Ix.Compiler.X86.Encode
open Ix.Compiler.Ixon

def zeros (count : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate count 0)

def naturalBytes (count value : Nat) : ByteArray :=
  littleEndian count (UInt64.ofNat value)

def u16 (value : Nat) : ByteArray := naturalBytes 2 value
def u32 (value : Nat) : ByteArray := naturalBytes 4 value
def u64 (value : Nat) : ByteArray := naturalBytes 8 value
def word64 (value : UInt64) : ByteArray := littleEndian 8 value

def alignUp (value alignment : Nat) : Nat :=
  if alignment == 0 then value
  else ((value + alignment - 1) / alignment) * alignment

def padTo (input : ByteArray) (size : Nat) : ByteArray :=
  input ++ zeros (size - input.size)

def padAlignment (input : ByteArray) (alignment : Nat) : ByteArray :=
  padTo input (alignUp input.size alignment)

inductive RootKind where
  /-- IxIR₁ root plus deterministic lowering/pass policy versions. -/
  | ixir1Policy
  /-- Canonically serialized IxIR₂ root, once that codec exists. -/
  | ixir2
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def RootKind.tag : RootKind → UInt8
  | .ixir1Policy => 0
  | .ixir2 => 1

/-- Mandatory object provenance. An IxIR₁ root must carry the policy fields
that prevent it from silently identifying different deterministic IxIR₂
lowerings. A directly addressed IxIR₂ root has no such extraneous fields. -/
inductive Provenance where
  | ixir1Policy (root : Address) (loweringVersion passPolicyVersion : UInt32)
  | ixir2 (root : Address)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Provenance.kind : Provenance → RootKind
  | .ixir1Policy .. => .ixir1Policy
  | .ixir2 .. => .ixir2

def Provenance.root : Provenance → Address
  | .ixir1Policy root .. => root
  | .ixir2 root => root

def provenanceDomain : ByteArray :=
  "compilatrix/x86-object-provenance/1".toUTF8 ++ byte 0

def Provenance.bytes : Provenance → ByteArray
  | .ixir1Policy root loweringVersion passPolicyVersion =>
      provenanceDomain ++ byte RootKind.ixir1Policy.tag ++ root.hash ++
        imm32Bytes loweringVersion ++ imm32Bytes passPolicyVersion
  | .ixir2 root =>
      provenanceDomain ++ byte RootKind.ixir2.tag ++ root.hash

def noteName : ByteArray := "COMPILATRIX".toUTF8 ++ byte 0

def provenanceNote (provenance : Provenance) : ByteArray :=
  let description := provenance.bytes
  u32 noteName.size ++ u32 description.size ++ u32 0x43495801 ++
    padAlignment noteName 4 ++ padAlignment description 4

structure Input where
  encoded : Encode.Output
  entryBlock : BlockId
  exportName : String := "compilatrix_main"
  provenance : Provenance

inductive Error where
  | invalidExportName
  | missingEntryBlock (block : BlockId)
  | invalidEntryOffset (offset textSize : Nat)
  | invalidRelocation (offset textSize : Nat)
  | invalidRelocationAddend (offset : Nat) (addend : Int)
  | duplicateSymbol (name : String)
  | missingString (name : String)
  | missingSymbol (name : String)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def validName (name : String) : Bool :=
  !name.isEmpty && !(name.toUTF8.data.contains 0)

structure StringTable where
  bytes : ByteArray
  offsets : List (String × Nat)

def buildStringTable (names : List String) : StringTable := Id.run do
  let mut output := byte 0
  let mut offsets := []
  for name in names do
    offsets := offsets ++ [(name, output.size)]
    output := output ++ name.toUTF8 ++ byte 0
  return { bytes := output, offsets }

def StringTable.offset? (table : StringTable) (name : String) : Option Nat :=
  (table.offsets.find? fun entry => entry.1 == name).map (fun entry => entry.2)

def symbol (name info sectionIndex : Nat) (value size : UInt64) : ByteArray :=
  u32 name ++ byte (UInt8.ofNat info) ++ byte 0 ++ u16 sectionIndex ++
    word64 value ++ word64 size

def nullSymbol : ByteArray := zeros 24

def textSectionSymbol : ByteArray :=
  symbol 0 0x03 1 0 0

def functionSymbol (name : Nat) (value size : UInt64) : ByteArray :=
  symbol name 0x12 1 value size

def undefinedFunctionSymbol (name : Nat) : ByteArray :=
  symbol name 0x12 0 0 0

private def runtimeSymbols (encoded : Encode.Output) : List String :=
  (encoded.relocations.toList.map (fun relocation => relocation.symbol)).eraseDups

private def listIndex? [BEq α] (target : α) : List α → Option Nat
  | [] => none
  | value :: values =>
      if value == target then some 0
      else (listIndex? target values).map (fun index => index + 1)

def relocationInfo (symbolIndex relocationType : Nat) : UInt64 :=
  (UInt64.ofNat symbolIndex <<< 32) ||| UInt64.ofNat relocationType

def relocationEntry (offset symbolIndex : Nat) (addend : Int) : ByteArray :=
  u64 offset ++ word64 (relocationInfo symbolIndex 2) ++
    word64 (Int64.ofInt addend).toUInt64

private def relocationBytes (encoded : Encode.Output)
    (symbols : List String) : Except Error ByteArray := do
  let mut output := ByteArray.empty
  for relocation in encoded.relocations do
    if encoded.text.size < relocation.offset + 4 then
      throw (.invalidRelocation relocation.offset encoded.text.size)
    if relocation.addend != -4 then
      throw (.invalidRelocationAddend relocation.offset relocation.addend)
    let some index := listIndex? relocation.symbol symbols
      | throw (.missingSymbol relocation.symbol)
    -- null, .text section, exported entry, then undefined runtime symbols
    output := output ++ relocationEntry relocation.offset (3 + index)
      relocation.addend
  return output

private def symbolBytes (encoded : Encode.Output) (entryOffset : Nat)
    (exportName : String) (symbols : List String)
    (strings : StringTable) : Except Error ByteArray := do
  let some exportOffset := strings.offset? exportName
    | throw (.missingString exportName)
  let mut output := nullSymbol ++ textSectionSymbol ++
    functionSymbol exportOffset (UInt64.ofNat entryOffset)
      (UInt64.ofNat (encoded.text.size - entryOffset))
  for name in symbols do
    let some nameOffset := strings.offset? name
      | throw (.missingString name)
    output := output ++ undefinedFunctionSymbol nameOffset
  return output

structure SectionHeader where
  name : Nat := 0
  sectionType : Nat := 0
  flags : UInt64 := 0
  offset : Nat := 0
  size : Nat := 0
  link : Nat := 0
  info : Nat := 0
  alignment : Nat := 0
  entrySize : Nat := 0

def SectionHeader.bytes (header : SectionHeader) : ByteArray :=
  u32 header.name ++ u32 header.sectionType ++ word64 header.flags ++ word64 0 ++
    u64 header.offset ++ u64 header.size ++ u32 header.link ++
    u32 header.info ++ u64 header.alignment ++ u64 header.entrySize

def nullSectionHeader : ByteArray := zeros 64

def elfHeader (sectionHeadersOffset sectionCount sectionNamesIndex : Nat) :
    ByteArray :=
  -- ELF magic, 64-bit class, little endian, current version, System V ABI.
  bytes [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    u16 1 ++              -- ET_REL
    u16 62 ++             -- EM_X86_64
    u32 1 ++              -- EV_CURRENT
    u64 0 ++              -- no entry address in a relocatable object
    u64 0 ++              -- no program-header table
    u64 sectionHeadersOffset ++
    u32 0 ++              -- architecture flags
    u16 64 ++             -- ELF header size
    u16 0 ++ u16 0 ++     -- no program headers
    u16 64 ++ u16 sectionCount ++ u16 sectionNamesIndex

private def sectionNames : List String :=
  [".text", ".rela.text", ".note.compilatrix", ".symtab", ".strtab",
    ".note.GNU-stack", ".shstrtab"]

private def requireOffset (table : StringTable) (name : String) :
    Except Error Nat :=
  match table.offset? name with
  | some offset => .ok offset
  | none => .error (.missingString name)

/-- Emit one ELF64 little-endian x86-64 relocatable object. -/
def write (input : Input) : Except Error ByteArray := do
  if !validName input.exportName then
    throw .invalidExportName
  let some entryOffset := input.encoded.blockOffsets[input.entryBlock.toNat]?
    | throw (.missingEntryBlock input.entryBlock)
  if input.encoded.text.size ≤ entryOffset then
    throw (.invalidEntryOffset entryOffset input.encoded.text.size)
  let symbols := runtimeSymbols input.encoded
  if !(symbols.all validName) then
    throw .invalidExportName
  if symbols.contains input.exportName then
    throw (.duplicateSymbol input.exportName)
  let strings := buildStringTable (input.exportName :: symbols)
  let symbolTable ← symbolBytes input.encoded entryOffset input.exportName
    symbols strings
  let relocations ← relocationBytes input.encoded symbols
  let note := provenanceNote input.provenance
  let sectionStrings := buildStringTable sectionNames

  let textOffset := alignUp 64 16
  let relocationOffset := alignUp (textOffset + input.encoded.text.size) 8
  let noteOffset := alignUp (relocationOffset + relocations.size) 4
  let symbolOffset := alignUp (noteOffset + note.size) 8
  let stringOffset := symbolOffset + symbolTable.size
  let sectionStringOffset := stringOffset + strings.bytes.size
  let sectionHeadersOffset := alignUp
    (sectionStringOffset + sectionStrings.bytes.size) 8

  let textName ← requireOffset sectionStrings ".text"
  let relocationName ← requireOffset sectionStrings ".rela.text"
  let noteSectionName ← requireOffset sectionStrings ".note.compilatrix"
  let symbolName ← requireOffset sectionStrings ".symtab"
  let stringName ← requireOffset sectionStrings ".strtab"
  let stackNoteName ← requireOffset sectionStrings ".note.GNU-stack"
  let sectionStringName ← requireOffset sectionStrings ".shstrtab"

  let headers := nullSectionHeader ++
    (SectionHeader.bytes
      { name := textName, sectionType := 1, flags := 0x6
        offset := textOffset, size := input.encoded.text.size
        alignment := 16 }) ++
    (SectionHeader.bytes
      { name := relocationName, sectionType := 4
        offset := relocationOffset, size := relocations.size
        link := 4, info := 1, alignment := 8, entrySize := 24 }) ++
    (SectionHeader.bytes
      { name := noteSectionName, sectionType := 7
        offset := noteOffset, size := note.size, alignment := 4 }) ++
    (SectionHeader.bytes
      { name := symbolName, sectionType := 2
        offset := symbolOffset, size := symbolTable.size
        link := 5, info := 2, alignment := 8, entrySize := 24 }) ++
    (SectionHeader.bytes
      { name := stringName, sectionType := 3
        offset := stringOffset, size := strings.bytes.size, alignment := 1 }) ++
    -- Empty and flag-free: tell ELF linkers that this object does not require
    -- an executable process stack.
    (SectionHeader.bytes
      { name := stackNoteName, sectionType := 1
        offset := sectionStringOffset, size := 0, alignment := 1 }) ++
    (SectionHeader.bytes
      { name := sectionStringName, sectionType := 3
        offset := sectionStringOffset, size := sectionStrings.bytes.size,
        alignment := 1 })

  let output := elfHeader sectionHeadersOffset 8 7
  let output := (padTo output textOffset) ++ input.encoded.text
  let output := (padTo output relocationOffset) ++ relocations
  let output := (padTo output noteOffset) ++ note
  let output := (padTo output symbolOffset) ++ symbolTable
  let output := (padTo output stringOffset) ++ strings.bytes
  let output := (padTo output sectionStringOffset) ++ sectionStrings.bytes
  return (padTo output sectionHeadersOffset) ++ headers

end Ix.Compiler.X86.ELF
