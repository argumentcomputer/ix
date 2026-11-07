import IxCC.X86.ELFRead
import IxCC.X86.ELF
import IxCC.X86.StreamTrace

/-! Fail-closed validation of actual serialized objects against independent
ELF interpretation. Successful emission certifies the text, exported entry,
the further exports (`Valid.exported`: each is the defined function symbol
of its name, at its block's offset), symbol/relocation inventory,
provenance and concrete section-layout policy. -/

namespace IxCC.X86.ELF

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
  | 3 => expected ".note.ixcc" 7 0 0 0 4 0
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
    view.note.name == ("IXCC".toUTF8.push 0) && view.note.noteType == 0x43495801

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

/-- A further export's symbol: a global function in `.text` at its block's
offset, running to the end of the text as the entry symbol does. -/
def exportMeaning (input : Input) (name : String) (block : BlockId) : SymbolMeaning :=
  let offset := (input.encoded.blockOffsets[block.toNat]?).getD 0
  ⟨name.toUTF8, 0x12, 0, 1, offset, input.encoded.text.size - offset⟩

/-- Every exported name is valid and used once, and every further export's
block starts inside the text. -/
def exportsOk (input : Input) : Bool :=
  let names := input.exportName :: input.exports.map (·.1)
  decide names.Nodup && names.all validName &&
    input.exports.all fun (_, block) =>
      match input.encoded.blockOffsets[block.toNat]? with
      | some offset => decide (offset < input.encoded.text.size)
      | none => false

/-- The symbol table: null, the `.text` section, the entry export, the
further exports in order, then the undefined runtime symbols. -/
def expectedSymbols (input : Input) (entryOffset : Nat) : Array SymbolMeaning :=
  (⟨ByteArray.empty, 0, 0, 0, 0, 0⟩ :: ⟨ByteArray.empty, 3, 0, 1, 0, 0⟩ :: entryMeaning input entryOffset ::
    (input.exports.map (fun p => exportMeaning input p.1 p.2) ++
    ((input.encoded.relocations.toList.map (·.symbol)).eraseDups.map fun name => ⟨name.toUTF8, 0x12, 0, 0, 0, 0⟩))).toArray

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
      view.provenance == expectedProvenance input.provenance && exportsOk input
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
  exports : exportsOk input = true

theorem checkView_sound {input : Input} {bytes : ByteArray} {view : ELFRead.View}
    (accepted : checkView input bytes view = true) : Fields input bytes view := by
  cases entry : input.encoded.blockOffsets[input.entryBlock.toNat]? with
  | none => simp [checkView, entry] at accepted
  | some offset =>
      cases symbol : view.symbols[2]? with
      | none => simp [checkView, entry, symbol] at accepted
      | some symbolValue =>
          simp only [checkView, entry, symbol, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at accepted
          obtain ⟨shape, name, bound, text, meaning, symbols, relocations, relocationBounds, provenance, exports⟩ :=
            accepted
          exact ⟨shape, name, text, ⟨offset, symbolValue, entry, bound, symbol, meaning, symbols⟩,
            relocations, relocationBounds, provenance, exports⟩

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

/-- A symbol meaning that defines `name` as a global function in `.text`. -/
def definesName (name : String) (m : SymbolMeaning) : Bool :=
  m.name == name.toUTF8 && m.info == 0x12 && m.other == 0 && m.sectionIndex == 1

/-- The value of the first global function symbol named `name` that is
defined in `.text`. -/
def symbol? (bytes : ByteArray) (name : String) : Option Nat := do
  let view ← ELFRead.parse bytes
  let symbol ← view.symbols.find? fun s => definesName name (symbolMeaning s)
  return symbol.value

private theorem find_export (input : Input) {name : String} {block : BlockId} :
    ∀ (exports : List (String × BlockId)) (rest : List SymbolMeaning),
      (exports.map (·.1)).Nodup → (name, block) ∈ exports →
      (exports.map (fun p => exportMeaning input p.1 p.2) ++ rest).find? (definesName name) =
        some (exportMeaning input name block)
  | [], _, _, member => absurd member (List.not_mem_nil)
  | (n, b) :: exports, rest, nodup, member => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      by_cases same : n = name
      · subst same
        rcases List.mem_cons.mp member with equal | later
        · cases equal
          simp [definesName, exportMeaning]
        · exact absurd (List.mem_map.mpr ⟨_, later, rfl⟩) nodup.1
      · have later : (name, block) ∈ exports := by
          rcases List.mem_cons.mp member with equal | later
          · cases equal; exact absurd rfl same
          · exact later
        have skip : definesName name (exportMeaning input n b) = false := by
          simp [definesName, exportMeaning, String.toByteArray_inj, same]
        simp only [List.map_cons, List.cons_append, List.find?_cons, skip]
        exact find_export input exports rest nodup.2 later

/-- Every further export is a defined global function symbol at its
block's offset. -/
theorem Valid.exported {input : Input} {bytes : ByteArray} (valid : Valid input bytes) {name : String}
    {block : BlockId} (member : (name, block) ∈ input.exports) :
    symbol? bytes name = input.encoded.blockOffsets[block.toNat]? := by
  obtain ⟨view, parsed, fields⟩ := valid
  obtain ⟨offset, _, _, _, _, _, symbols⟩ := fields.entry
  have ok := fields.exports
  simp only [exportsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨nodup, _⟩, inText⟩ := ok
  rw [List.nodup_cons] at nodup
  have distinct : input.exportName ≠ name := fun equal =>
    nodup.1 (equal ▸ List.mem_map.mpr ⟨(name, block), member, rfl⟩)
  have found : (view.symbols.map symbolMeaning).find? (definesName name) =
      some (exportMeaning input name block) := by
    rw [symbols, expectedSymbols, List.find?_toArray,
      List.find?_cons_of_neg (by simp [definesName]), List.find?_cons_of_neg (by simp [definesName]),
      List.find?_cons_of_neg (by simp [definesName, entryMeaning, String.toByteArray_inj, distinct])]
    exact find_export input _ _ nodup.2 member
  rw [Array.find?_map] at found
  obtain ⟨symbol, lookup, meaning⟩ := Option.map_eq_some_iff.mp found
  have value := congrArg SymbolMeaning.value meaning
  have offsetFound := inText (name, block) member
  cases blockOffset : input.encoded.blockOffsets[block.toNat]? with
  | none => simp [blockOffset] at offsetFound
  | some offset =>
      simp only [symbolMeaning, exportMeaning, blockOffset, Option.getD_some] at value
      have same : (fun s => definesName name (symbolMeaning s)) = definesName name ∘ symbolMeaning := rfl
      simp only [symbol?, parsed, Option.bind_eq_bind, Option.bind_some, same, lookup]
      simp [value]

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

end IxCC.X86.ELF
