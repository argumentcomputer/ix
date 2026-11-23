import IxCC.X86.ELFRead
import IxCC.X86.ELF
import IxCC.X86.StreamTrace

/-! Fail-closed validation of actual serialized objects against independent
ELF interpretation. Successful emission certifies the text, exported entry,
the further exports (`Valid.exported`: each is the defined function symbol
of its name, at its block's offset), symbol/relocation inventory,
provenance and concrete section-layout policy. -/

namespace IxCC.X86.ELF

def expectedHeader (sectionOffset : Nat) (hasRodata : Bool := false) : ELFRead.Header :=
  ⟨⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩,
    1, 62, 1, 0, 0, sectionOffset, 0, 64, 0, 0, 64,
    if hasRodata then 9 else 8, if hasRodata then 8 else 7⟩

def sectionShape (hasRodata : Bool) (index : Nat) (part : ELFRead.Section) : Bool :=
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
  | 7 => if hasRodata then expected ".rodata" 1 2 0 0 8 0 else expected ".shstrtab" 3 0 0 0 1 0
  | 8 => if hasRodata then expected ".shstrtab" 3 0 0 0 1 0 else false
  | _ => false

def sectionLayout (bytes : ByteArray) (view : ELFRead.View) (index : Nat) : Bool :=
  let hasRodata := view.rodata.isSome
  let lastIndex := if hasRodata then 8 else 7
  match view.sections[index]? with
  | none => false
  | some part =>
      sectionShape hasRodata index part && part.data.size == part.header.size &&
      ELFRead.slice bytes part.header.offset part.header.size == some part.data &&
      (index == 0 || (decide (64 ≤ part.header.offset) &&
        decide (part.header.offset + part.header.size ≤ view.header.sectionOffset) &&
        part.header.offset % part.header.alignment == 0)) &&
      (index == 0 || index == lastIndex || match view.sections[index + 1]? with
        | none => false
        | some next => decide (part.header.offset + part.header.size ≤ next.header.offset))

def layout (bytes : ByteArray) (view : ELFRead.View) : Bool :=
  let hasRodata := view.rodata.isSome
  let sectionCount := if hasRodata then 9 else 8
  let lastIndex := if hasRodata then 8 else 7
  decide (bytes.size < UInt64.size) && view.header == expectedHeader view.header.sectionOffset hasRodata &&
    decide (64 ≤ view.header.sectionOffset) && view.header.sectionOffset % 8 == 0 &&
    view.header.sectionOffset + sectionCount * 64 == bytes.size && view.sections.size == sectionCount &&
    (List.range sectionCount).all (sectionLayout bytes view) &&
    ((view.sections[1]?).map ELFRead.Section.data == some view.text) &&
    (!hasRodata || ((view.sections[7]?).map ELFRead.Section.data == view.rodata)) &&
    ((view.sections[4]?).map (fun part => part.data.size) == some (24 * view.symbols.size)) &&
    ((view.sections[2]?).map (fun part => part.data.size) == some (24 * view.relocations.size)) &&
    ((view.sections[5]?).map (fun part => part.data[0]? == some 0 && part.data[part.data.size - 1]? == some 0) == some true) &&
    ((view.sections[lastIndex]?).map (fun part => part.data[0]? == some 0 && part.data[part.data.size - 1]? == some 0) == some true) &&
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

/-- A `.rodata` export's symbol: a global object (`0x11`) in `.rodata` (section 7). -/
def rodataMeaning (rs : RodataSymbol) : SymbolMeaning :=
  ⟨rs.name.toUTF8, 0x11, 0, 7, rs.offset, rs.size⟩

/-- Every exported name is valid and used once, and every further export's
block starts inside the text. -/
def exportsOk (input : Input) : Bool :=
  let names := input.exportName :: input.exports.map (·.1)
  decide names.Nodup && names.all validName &&
    input.exports.all fun (_, block) =>
      match input.encoded.blockOffsets[block.toNat]? with
      | some offset => decide (offset < input.encoded.text.size)
      | none => false

/-- Every `.rodata` export is valid, unique, and lies inside `.rodata`; when
there is no `.rodata` section there are no `.rodata` exports. -/
def rodataExportsOk (input : Input) : Bool :=
  match input.rodata with
  | none => input.rodataExports.isEmpty
  | some rodata =>
      let names := input.rodataExports.map (·.name)
      decide names.Nodup && names.all validName &&
        input.rodataExports.all fun rs => decide (rs.offset + rs.size ≤ rodata.size)

/-- The symbol table: null, the `.text` section, the entry export, the
further exports in order, the `.rodata` object exports in order, then the
undefined runtime symbols. -/
def expectedSymbols (input : Input) (entryOffset : Nat) : Array SymbolMeaning :=
  (⟨ByteArray.empty, 0, 0, 0, 0, 0⟩ :: ⟨ByteArray.empty, 3, 0, 1, 0, 0⟩ :: entryMeaning input entryOffset ::
    (input.exports.map (fun p => exportMeaning input p.1 p.2) ++
    (input.rodataExports.map rodataMeaning ++
    ((input.encoded.relocations.toList.map (·.symbol)).eraseDups.map fun name => ⟨name.toUTF8, 0x12, 0, 0, 0, 0⟩)))).toArray

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
      view.text == input.encoded.text && view.rodata == input.rodata &&
      symbolMeaning entrySymbol == entryMeaning input entryOffset &&
      view.symbols.map symbolMeaning == expectedSymbols input entryOffset &&
      view.relocations.map relocationMeaning == expectedRelocations input && relocationBounds view &&
      view.provenance == expectedProvenance input.provenance && exportsOk input && rodataExportsOk input
  | _, _ => false

structure Fields (input : Input) (bytes : ByteArray) (view : ELFRead.View) : Prop where
  layout : layout bytes view = true
  exportName : validName input.exportName = true
  text : view.text = input.encoded.text
  rodata : view.rodata = input.rodata
  entry : ∃ offset symbol, input.encoded.blockOffsets[input.entryBlock.toNat]? = some offset ∧
    offset < input.encoded.text.size ∧ view.symbols[2]? = some symbol ∧
    symbolMeaning symbol = entryMeaning input offset ∧ view.symbols.map symbolMeaning = expectedSymbols input offset
  relocations : view.relocations.map relocationMeaning = expectedRelocations input
  relocationBounds : relocationBounds view = true
  provenance : view.provenance = expectedProvenance input.provenance
  exports : exportsOk input = true
  rodataExports : rodataExportsOk input = true

theorem checkView_sound {input : Input} {bytes : ByteArray} {view : ELFRead.View}
    (accepted : checkView input bytes view = true) : Fields input bytes view := by
  cases entry : input.encoded.blockOffsets[input.entryBlock.toNat]? with
  | none => simp [checkView, entry] at accepted
  | some offset =>
      cases symbol : view.symbols[2]? with
      | none => simp [checkView, entry, symbol] at accepted
      | some symbolValue =>
          simp only [checkView, entry, symbol, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at accepted
          obtain ⟨shape, name, bound, text, rodata, meaning, symbols, relocations, relocationBounds, provenance,
            exports, rodataExports⟩ := accepted
          exact ⟨shape, name, text, rodata, ⟨offset, symbolValue, entry, bound, symbol, meaning, symbols⟩,
            relocations, relocationBounds, provenance, exports, rodataExports⟩

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

/-- Byte-level preservation of `.rodata`: parsing a certified object returns
the exact `.rodata` bytes of the input (or `none` when absent). -/
theorem Valid.rodata {input : Input} {bytes : ByteArray} (valid : Valid input bytes) :
    ELFRead.rodata? bytes = input.rodata := by
  obtain ⟨view, parsed, fields⟩ := valid
  simp [ELFRead.rodata?, parsed, fields.rodata]

/-- A certified object carrying `.rodata` places it in section 7 with
`SHT_PROGBITS` (1), read-only `SHF_ALLOC` flags (2: neither writable nor
executable), 8-byte alignment, and exact byte contents. -/
theorem Valid.rodata_readonly {input : Input} {bytes : ByteArray} (valid : Valid input bytes)
    {view : ELFRead.View} (parsed : ELFRead.parse bytes = some view)
    {data : ByteArray} (hro : input.rodata = some data) :
    ∃ sec, view.sections[7]? = some sec ∧ sec.name = ".rodata".toUTF8 ∧
      sec.header.sectionType = 1 ∧ sec.header.flags = 2 ∧
      sec.header.alignment = 8 ∧ sec.data = data := by
  obtain ⟨view₀, parsed₀, fields⟩ := valid
  rw [parsed] at parsed₀
  cases Option.some.inj parsed₀
  have hvro : view.rodata = some data := fields.rodata.trans hro
  have hlay := fields.layout
  simp only [layout, hvro, Option.isSome_some, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, List.all_eq_true, and_assoc] at hlay
  obtain ⟨_, _, _, _, _, _, hsecAll, _, hsec7data, _⟩ := hlay
  have h7lay := hsecAll 7 (by decide)
  cases hs7 : view.sections[7]? with
  | none => simp [sectionLayout, hs7] at h7lay
  | some sec =>
      simp only [sectionLayout, hvro, Option.isSome_some, hs7, sectionShape, ite_true, Bool.and_eq_true,
        beq_iff_eq, and_assoc] at h7lay
      simp only [hs7, Option.map_some, Option.some.injEq] at hsec7data
      obtain ⟨hname, hhdr, _⟩ := h7lay
      refine ⟨sec, rfl, hname, ?_, ?_, ?_, hsec7data⟩
      · exact congrArg ELFRead.SectionHeader.sectionType hhdr
      · exact congrArg ELFRead.SectionHeader.flags hhdr
      · exact congrArg ELFRead.SectionHeader.alignment hhdr

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

/-- A symbol meaning that defines `name` as a global object in `.rodata` (section 7). -/
def definesRodataName (name : String) (m : SymbolMeaning) : Bool :=
  m.name == name.toUTF8 && m.info == 0x11 && m.other == 0 && m.sectionIndex == 7

/-- The `(offset, size)` of the first global object symbol named `name` that is
defined in `.rodata`. -/
def rodataSymbol? (bytes : ByteArray) (name : String) : Option (Nat × Nat) := do
  let view ← ELFRead.parse bytes
  let symbol ← view.symbols.find? fun s => definesRodataName name (symbolMeaning s)
  return (symbol.value, symbol.size)

private theorem find_rodata_skip_exports (input : Input) (name : String) :
    ∀ (exports : List (String × BlockId)) (rest : List SymbolMeaning),
      (exports.map (fun p => exportMeaning input p.1 p.2) ++ rest).find? (definesRodataName name) =
        rest.find? (definesRodataName name)
  | [], _ => rfl
  | (n, b) :: exports, rest => by
      have skip : definesRodataName name (exportMeaning input n b) = false := by
        simp [definesRodataName, exportMeaning]
      simp only [List.map_cons, List.cons_append, List.find?_cons, skip]
      exact find_rodata_skip_exports input name exports rest

private theorem find_rodata_export {rs : RodataSymbol} :
    ∀ (rodataExports : List RodataSymbol) (rest : List SymbolMeaning),
      (rodataExports.map (·.name)).Nodup → rs ∈ rodataExports →
      (rodataExports.map rodataMeaning ++ rest).find? (definesRodataName rs.name) =
        some (rodataMeaning rs)
  | [], _, _, member => absurd member List.not_mem_nil
  | r :: rodataExports, rest, nodup, member => by
      simp only [List.map_cons, List.nodup_cons] at nodup
      by_cases same : r.name = rs.name
      · rcases List.mem_cons.mp member with equal | later
        · subst equal
          simp [definesRodataName, rodataMeaning]
        · exact absurd (same ▸ List.mem_map.mpr ⟨rs, later, rfl⟩) nodup.1
      · have later : rs ∈ rodataExports := by
          rcases List.mem_cons.mp member with equal | later
          · subst equal; exact absurd rfl same
          · exact later
        have skip : definesRodataName rs.name (rodataMeaning r) = false := by
          simp [definesRodataName, rodataMeaning, String.toByteArray_inj, same]
        simp only [List.map_cons, List.cons_append, List.find?_cons, skip]
        exact find_rodata_export rodataExports rest nodup.2 later

/-- Every `.rodata` export is a defined global object symbol in section 7 at its
declared `(offset, size)`. -/
theorem Valid.rodataExported {input : Input} {bytes : ByteArray} (valid : Valid input bytes)
    {rs : RodataSymbol} (member : rs ∈ input.rodataExports) :
    rodataSymbol? bytes rs.name = some (rs.offset, rs.size) := by
  obtain ⟨view, parsed, fields⟩ := valid
  obtain ⟨offset, _, _, _, _, _, symbols⟩ := fields.entry
  have hrok := fields.rodataExports
  cases hro : input.rodata with
  | none =>
      simp only [rodataExportsOk, hro] at hrok
      cases hre : input.rodataExports with
      | nil => rw [hre] at member; cases member
      | cons _ _ => simp [hre] at hrok
  | some rodata =>
      simp only [rodataExportsOk, hro, Bool.and_eq_true, decide_eq_true_eq] at hrok
      obtain ⟨⟨nodup, _⟩, _⟩ := hrok
      have found : (view.symbols.map symbolMeaning).find? (definesRodataName rs.name) =
          some (rodataMeaning rs) := by
        rw [symbols, expectedSymbols, List.find?_toArray,
          List.find?_cons_of_neg (by simp [definesRodataName]),
          List.find?_cons_of_neg (by simp [definesRodataName]),
          List.find?_cons_of_neg (by simp [definesRodataName, entryMeaning]),
          find_rodata_skip_exports]
        exact find_rodata_export input.rodataExports _ nodup member
      rw [Array.find?_map] at found
      obtain ⟨symbol, lookup, meaning⟩ := Option.map_eq_some_iff.mp found
      have value := congrArg SymbolMeaning.value meaning
      have size := congrArg SymbolMeaning.size meaning
      simp only [symbolMeaning, rodataMeaning] at value size
      have same : (fun s => definesRodataName rs.name (symbolMeaning s)) =
          definesRodataName rs.name ∘ symbolMeaning := rfl
      simp only [rodataSymbol?, parsed, Option.bind_eq_bind, Option.bind_some, same, lookup]
      simp [value, size]

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
