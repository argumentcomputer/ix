import Ix.Compiler.X86.ELFRead
import Ix.Compiler.X86.ELF
import Ix.Compiler.X86.StreamTrace

/-! Fail-closed validation of actual serialized objects against independent
ELF interpretation. Successful emission certifies the text, exported entry,
symbol/relocation inventory, provenance and concrete section-layout policy. -/

namespace Ix.Compiler.X86.ELF

def expectedHeader (sectionOffset : Nat) : ELFRead.Header :=
  ⟨⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩,
    1, 62, 1, 0, 0, sectionOffset, 0, 64, 0, 0, 64, 8, 7⟩

def sectionShape (index : Nat) (part : ELFRead.Section) : Bool :=
  let h := part.header
  let expected (name : String) (kind flags link info alignment entrySize : Nat) (size := h.size) :=
    part.name == name.toUTF8 && h == (⟨h.nameOffset, kind, flags, 0, h.offset, size, link, info, alignment, entrySize⟩ : ELFRead.SectionHeader)
  match index with
  | 0 => part.name == ByteArray.empty && part.data == ByteArray.empty &&
      h == (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : ELFRead.SectionHeader)
  | 1 => expected ".text" 1 6 0 0 16 0
  | 2 => expected ".rela.text" 4 0 4 1 8 24
  | 3 => expected ".note.compilatrix" 7 0 0 0 4 0
  | 4 => expected ".symtab" 2 0 5 2 8 24
  | 5 => expected ".strtab" 3 0 0 0 1 0
  | 6 => expected ".note.GNU-stack" 1 0 0 0 1 0 0
  | 7 => expected ".shstrtab" 3 0 0 0 1 0
  | _ => false

def sectionLayout (bytes : ByteArray) (view : ELFRead.View) (index : Nat) : Bool :=
  match view.sections[index]? with
  | none => false
  | some part =>
      sectionShape index part && part.data.size == part.header.size &&
      ELFRead.slice bytes part.header.offset part.header.size == some part.data &&
      (index == 0 || (decide (64 ≤ part.header.offset) &&
        decide (part.header.offset + part.header.size ≤ view.header.sectionOffset) &&
        part.header.offset % part.header.alignment == 0)) &&
      (index == 0 || index == 7 || match view.sections[index + 1]? with
        | none => false
        | some next => decide (part.header.offset + part.header.size ≤ next.header.offset))

def layout (bytes : ByteArray) (view : ELFRead.View) : Bool :=
  decide (bytes.size < UInt64.size) && view.header == expectedHeader view.header.sectionOffset &&
    decide (64 ≤ view.header.sectionOffset) && view.header.sectionOffset % 8 == 0 &&
    view.header.sectionOffset + 512 == bytes.size && view.sections.size == 8 &&
    (List.range 8).all (sectionLayout bytes view) &&
    ((view.sections[1]?).map ELFRead.Section.data == some view.text) &&
    ((view.sections[4]?).map (fun part => part.data.size) == some (24 * view.symbols.size)) &&
    ((view.sections[2]?).map (fun part => part.data.size) == some (24 * view.relocations.size)) &&
    ((view.sections[5]?).map (fun part => part.data[0]? == some 0 && part.data[part.data.size - 1]? == some 0) == some true) &&
    ((view.sections[7]?).map (fun part => part.data[0]? == some 0 && part.data[part.data.size - 1]? == some 0) == some true) &&
    view.note.name == ("COMPILATRIX".toUTF8.push 0) && view.note.noteType == 0x43495801

structure SymbolMeaning where
  name : ByteArray
  info : Nat
  other : Nat
  sectionIndex : Nat
  value : Nat
  size : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def symbolMeaning (symbol : ELFRead.Symbol) : SymbolMeaning :=
  ⟨symbol.name, symbol.info, symbol.other, symbol.sectionIndex, symbol.value, symbol.size⟩

def entryMeaning (input : Input) (entryOffset : Nat) : SymbolMeaning :=
  ⟨input.exportName.toUTF8, 0x12, 0, 1, entryOffset, input.encoded.text.size - entryOffset⟩

def expectedSymbols (input : Input) (entryOffset : Nat) : Array SymbolMeaning :=
  (⟨ByteArray.empty, 0, 0, 0, 0, 0⟩ :: ⟨ByteArray.empty, 3, 0, 1, 0, 0⟩ :: entryMeaning input entryOffset ::
    ((input.encoded.relocations.toList.map (·.symbol)).eraseDups.map fun name => ⟨name.toUTF8, 0x12, 0, 0, 0, 0⟩)).toArray

structure RelocationMeaning where
  offset : Nat
  name : ByteArray
  relocationType : Nat
  addend : Int
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def relocationMeaning (relocation : ELFRead.Relocation) : RelocationMeaning :=
  ⟨relocation.offset, relocation.symbolName, relocation.relocationType, relocation.addend⟩

def expectedRelocations (input : Input) : Array RelocationMeaning :=
  input.encoded.relocations.map fun relocation => ⟨relocation.offset, relocation.symbol.toUTF8, 2, relocation.addend⟩

def relocationBounds (view : ELFRead.View) : Bool :=
  view.relocations.all fun relocation =>
    decide (relocation.offset + 4 ≤ view.text.size) && decide (3 ≤ relocation.symbolIndex) &&
    relocation.addend == -4 &&
    match view.symbols[relocation.symbolIndex]? with
    | none => false
    | some symbol => symbol.name == relocation.symbolName && symbol.sectionIndex == 0 && symbol.info == 0x12

def expectedProvenance : Provenance → ELFRead.Provenance
  | .ixir1Policy root lowering policy => .ixir1Policy root.hash lowering.toNat policy.toNat
  | .ixir2 root => .ixir2 root.hash

def checkView (input : Input) (bytes : ByteArray) (view : ELFRead.View) : Bool :=
  match input.encoded.blockOffsets[input.entryBlock.toNat]?, view.symbols[2]? with
  | some entryOffset, some entrySymbol =>
      layout bytes view && validName input.exportName && decide (entryOffset < input.encoded.text.size) &&
      view.text == input.encoded.text && symbolMeaning entrySymbol == entryMeaning input entryOffset &&
      view.symbols.map symbolMeaning == expectedSymbols input entryOffset &&
      view.relocations.map relocationMeaning == expectedRelocations input && relocationBounds view &&
      view.provenance == expectedProvenance input.provenance
  | _, _ => false

structure Fields (input : Input) (bytes : ByteArray) (view : ELFRead.View) : Prop where
  layout : layout bytes view = true
  exportName : validName input.exportName = true
  text : view.text = input.encoded.text
  entry : ∃ offset symbol, input.encoded.blockOffsets[input.entryBlock.toNat]? = some offset ∧
    offset < input.encoded.text.size ∧ view.symbols[2]? = some symbol ∧
    symbolMeaning symbol = entryMeaning input offset ∧ view.symbols.map symbolMeaning = expectedSymbols input offset
  relocations : view.relocations.map relocationMeaning = expectedRelocations input
  relocationBounds : relocationBounds view = true
  provenance : view.provenance = expectedProvenance input.provenance

theorem checkView_sound {input : Input} {bytes : ByteArray} {view : ELFRead.View}
    (accepted : checkView input bytes view = true) : Fields input bytes view := by
  cases entry : input.encoded.blockOffsets[input.entryBlock.toNat]? with
  | none => simp [checkView, entry] at accepted
  | some offset =>
      cases symbol : view.symbols[2]? with
      | none => simp [checkView, entry, symbol] at accepted
      | some symbolValue =>
          simp only [checkView, entry, symbol, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at accepted
          obtain ⟨shape, name, bound, text, meaning, symbols, relocations, relocationBounds, provenance⟩ := accepted
          exact ⟨shape, name, text, ⟨offset, symbolValue, entry, bound, symbol, meaning, symbols⟩,
            relocations, relocationBounds, provenance⟩

def check (input : Input) (bytes : ByteArray) : Bool :=
  match ELFRead.parse bytes with
  | none => false
  | some view => checkView input bytes view

def Valid (input : Input) (bytes : ByteArray) : Prop :=
  ∃ view, ELFRead.parse bytes = some view ∧ Fields input bytes view

theorem check_sound {input : Input} {bytes : ByteArray} (accepted : check input bytes = true) : Valid input bytes := by
  cases parsed : ELFRead.parse bytes with
  | none => simp [check, parsed] at accepted
  | some view => exact ⟨view, parsed, checkView_sound (by simpa [check, parsed] using accepted)⟩

theorem Valid.text {input : Input} {bytes : ByteArray} (valid : Valid input bytes) :
    ELFRead.text? bytes = some input.encoded.text := by
  obtain ⟨view, parsed, fields⟩ := valid
  simp [ELFRead.text?, parsed, fields.text]

def entry? (bytes : ByteArray) (name : String) : Option Nat := do
  let view ← ELFRead.parse bytes
  let symbol ← view.symbols[2]?
  ELFRead.require (symbol.name == name.toUTF8 && symbol.info == 0x12 && symbol.other == 0 && symbol.sectionIndex == 1)
  return symbol.value

theorem Valid.entry {input : Input} {bytes : ByteArray} (valid : Valid input bytes) :
    entry? bytes input.exportName = input.encoded.blockOffsets[input.entryBlock.toNat]? := by
  obtain ⟨view, parsed, fields⟩ := valid
  obtain ⟨offset, symbol, found, _, atEntry, meaning, _⟩ := fields.entry
  have name := congrArg SymbolMeaning.name meaning
  have info := congrArg SymbolMeaning.info meaning
  have other := congrArg SymbolMeaning.other meaning
  have sectionIndex := congrArg SymbolMeaning.sectionIndex meaning
  have value := congrArg SymbolMeaning.value meaning
  simp only [symbolMeaning, entryMeaning] at name info other sectionIndex value
  simp [entry?, parsed, atEntry, name, info, other, sectionIndex, value, ELFRead.require, found]

structure Certified (input : Input) where
  bytes : ByteArray
  valid : Valid input bytes

inductive CheckedError where
  | writer (error : Error)
  | invalidObject
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def writeChecked (input : Input) : Except CheckedError (Certified input) := do
  let bytes ← (write input).mapError CheckedError.writer
  if accepted : check input bytes = true then return ⟨bytes, check_sound accepted⟩
  else throw .invalidObject

end Ix.Compiler.X86.ELF
