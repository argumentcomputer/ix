import Ix.Compiler.X86.Basic
import Init.Data.ByteArray.Lemmas

/-! Independent reader for the emitted ELF64 relocatable-object subset.
Unsigned fields are mathematical naturals; truncated or out-of-file reads
fail. This module imports neither the encoder nor the ELF writer. The note
reader implements the four-byte Linux/GNU note convention declared by the
section's alignment, rather than silently assuming generic ELF64 alignment.

Field layouts: System V gABI chapters 2--6; x86-64 psABI section 4.4.
GNU note convention: binutils commit 82ed9683ec099d8205dc499ac84febc975235af6.
-/

namespace Ix.Compiler.X86.ELFRead

instance byteArrayLawfulBEq : LawfulBEq ByteArray where
  eq_of_beq := by
    intro left right equal
    exact ByteArray.ext (eq_of_beq equal)
  rfl := by
    intro bytes
    change (bytes.data == bytes.data) = true
    simp

instance byteArrayRepr : Repr ByteArray where
  reprPrec bytes precedence := reprPrec bytes.data precedence

def require (condition : Bool) : Option Unit := if condition then some () else none

def natural (bytes : ByteArray) (offset : Nat) : Nat → Option Nat
  | 0 => some 0
  | count + 1 => do
      let lower ← natural bytes offset count
      let byte ← bytes[offset + count]?
      return lower + byte.toNat * 256 ^ count

def slice (bytes : ByteArray) (offset size : Nat) : Option ByteArray :=
  if offset + size ≤ bytes.size then some (bytes.extract offset (offset + size)) else none

private def stringBytes (bytes : ByteArray) (offset : Nat) : Nat → Option (List UInt8)
  | 0 => none
  | fuel + 1 => do
      let byte ← bytes[offset]?
      if byte == 0 then return []
      else return byte :: (← stringBytes bytes (offset + 1) fuel)

def cstring (bytes : ByteArray) (offset : Nat) : Option ByteArray := do
  return ⟨(← stringBytes bytes offset bytes.size).toArray⟩

structure Header where
  ident : ByteArray
  objectType : Nat
  machine : Nat
  version : Nat
  entry : Nat
  programOffset : Nat
  sectionOffset : Nat
  flags : Nat
  headerSize : Nat
  programEntrySize : Nat
  programCount : Nat
  sectionEntrySize : Nat
  sectionCount : Nat
  sectionNames : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def header (bytes : ByteArray) : Option Header := do
  return ⟨← slice bytes 0 16, ← natural bytes 16 2, ← natural bytes 18 2,
    ← natural bytes 20 4, ← natural bytes 24 8, ← natural bytes 32 8,
    ← natural bytes 40 8, ← natural bytes 48 4, ← natural bytes 52 2,
    ← natural bytes 54 2, ← natural bytes 56 2, ← natural bytes 58 2,
    ← natural bytes 60 2, ← natural bytes 62 2⟩

structure SectionHeader where
  nameOffset : Nat
  sectionType : Nat
  flags : Nat
  address : Nat
  offset : Nat
  size : Nat
  link : Nat
  info : Nat
  alignment : Nat
  entrySize : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def sectionHeader (bytes : ByteArray) (offset : Nat) : Option SectionHeader := do
  return ⟨← natural bytes offset 4, ← natural bytes (offset + 4) 4,
    ← natural bytes (offset + 8) 8, ← natural bytes (offset + 16) 8,
    ← natural bytes (offset + 24) 8, ← natural bytes (offset + 32) 8,
    ← natural bytes (offset + 40) 4, ← natural bytes (offset + 44) 4,
    ← natural bytes (offset + 48) 8, ← natural bytes (offset + 56) 8⟩

structure Section where
  header : SectionHeader
  name : ByteArray
  data : ByteArray
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Symbol where
  nameOffset : Nat
  name : ByteArray
  info : Nat
  other : Nat
  sectionIndex : Nat
  value : Nat
  size : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def symbol (bytes strings : ByteArray) (offset : Nat) : Option Symbol := do
  let nameOffset ← natural bytes offset 4
  return ⟨nameOffset, ← cstring strings nameOffset, ← natural bytes (offset + 4) 1,
    ← natural bytes (offset + 5) 1, ← natural bytes (offset + 6) 2,
    ← natural bytes (offset + 8) 8, ← natural bytes (offset + 16) 8⟩

structure Relocation where
  offset : Nat
  symbolIndex : Nat
  symbolName : ByteArray
  relocationType : Nat
  addend : Int
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def signed64 (natural : Nat) : Int :=
  if natural < 2 ^ 63 then natural else (natural : Int) - 2 ^ 64

def relocation (bytes : ByteArray) (symbols : Array Symbol) (offset : Nat) : Option Relocation := do
  let position ← natural bytes offset 8
  let info ← natural bytes (offset + 8) 8
  let symbolIndex := info / 2 ^ 32
  let target ← symbols[symbolIndex]?
  return ⟨position, symbolIndex, target.name, info % 2 ^ 32, signed64 (← natural bytes (offset + 16) 8)⟩

def aligned4 (size : Nat) : Nat := ((size + 3) / 4) * 4

structure Note where
  name : ByteArray
  noteType : Nat
  descriptor : ByteArray
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def note (bytes : ByteArray) : Option Note := do
  let nameSize ← natural bytes 0 4
  let descriptorSize ← natural bytes 4 4
  let noteType ← natural bytes 8 4
  let name ← slice bytes 12 nameSize
  let descriptor ← slice bytes (12 + aligned4 nameSize) descriptorSize
  require (12 + aligned4 nameSize + aligned4 descriptorSize == bytes.size)
  let namePadding ← slice bytes (12 + nameSize) (aligned4 nameSize - nameSize)
  let descriptorPadding ← slice bytes (12 + aligned4 nameSize + descriptorSize) (aligned4 descriptorSize - descriptorSize)
  require (namePadding.data.all (· == 0) && descriptorPadding.data.all (· == 0))
  return ⟨name, noteType, descriptor⟩

inductive Provenance where
  | ixir1Policy (root : ByteArray) (lowering passPolicy : Nat)
  | ixir2 (root : ByteArray)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Parse the domain, kind, fixed-size root and policy words individually. -/
def provenance (bytes : ByteArray) : Option Provenance := do
  let domain := "compilatrix/x86-object-provenance/1".toUTF8
  require ((← slice bytes 0 domain.size) == domain)
  require ((← natural bytes domain.size 1) == 0)
  let kind ← natural bytes (domain.size + 1) 1
  let root ← slice bytes (domain.size + 2) 32
  if kind == 0 then
    require (bytes.size == domain.size + 42)
    return .ixir1Policy root (← natural bytes (domain.size + 34) 4) (← natural bytes (domain.size + 38) 4)
  else if kind == 1 then
    require (bytes.size == domain.size + 34)
    return .ixir2 root
  else none

structure View where
  header : Header
  sections : Array Section
  text : ByteArray
  symbols : Array Symbol
  relocations : Array Relocation
  note : Note
  provenance : Provenance
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Fixed section count and table sizes are checked before allocating or
iterating. Other semantic obligations are stated by the object validator. -/
def parse (bytes : ByteArray) : Option View := do
  let header ← header bytes
  require (header.sectionCount == 8 && header.sectionEntrySize == 64 && header.sectionNames == 7)
  require (decide (header.sectionOffset + 8 * 64 ≤ bytes.size))
  let headers ← (List.range 8).mapM (fun index => sectionHeader bytes (header.sectionOffset + index * 64))
  let headers := headers.toArray
  let names ← headers[7]?
  let strings ← slice bytes names.offset names.size
  let sections ← headers.toList.mapM fun sectionInfo => do
    return (⟨sectionInfo, ← cstring strings sectionInfo.nameOffset, ← slice bytes sectionInfo.offset sectionInfo.size⟩ : Section)
  let sections := sections.toArray
  let text ← sections[1]?
  let symtab ← sections[4]?
  let symbolStrings ← sections[symtab.header.link]?
  require (symtab.data.size % 24 == 0)
  let symbols ← (List.range (symtab.data.size / 24)).mapM (fun index => symbol symtab.data symbolStrings.data (index * 24))
  let symbols := symbols.toArray
  let rela ← sections[2]?
  require (rela.data.size % 24 == 0)
  let relocations ← (List.range (rela.data.size / 24)).mapM (fun index => relocation rela.data symbols (index * 24))
  let noteSection ← sections[3]?
  let note ← note noteSection.data
  let provenance ← provenance note.descriptor
  return ⟨header, sections, text.data, symbols, relocations.toArray, note, provenance⟩

def text? (bytes : ByteArray) : Option ByteArray := (parse bytes).map View.text

end Ix.Compiler.X86.ELFRead
