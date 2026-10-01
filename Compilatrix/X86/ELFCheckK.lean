import Compilatrix.X86.ELFValidate
import Compilatrix.X86.EncodeK

/-!
# The ELF validator in kernel-evaluable style

`ELF.checkK` is the object validator `ELF.check` evaluated on the object as
a list, read once. The reader (`ELFRead.parseK`) takes the header from a
64-byte window, the section-header table from one walk to its offset (each
header from its own 64-byte window) and every section with one walk
(`sliceL`), so it never indexes the object by position, and `ByteArray`'s
`extract` never runs. The validator compares byte strings as lists and runs
its `Array.all`/`Array.contains`/`Array.map` loops (well-founded recursion)
over lists. In the kernel a list is read by walking it, so `parse`'s
positional reads cost the object's length each, and `extract` copies it.

`parseK_eq` and `checkK_eq` prove the twins equal to `parse` and `check`,
so `ELF.writeCheckedK` certifies with `check_sound` as `writeChecked` does
(M1.K1, design note 00).
-/

namespace Compilatrix.X86.ELFRead

/-- The bytes of `list` (of length `total`) in `[offset, offset + size)`,
or none past the end: `slice` read as a list. -/
def sliceL (list : List UInt8) (total offset size : Nat) : Option ByteArray :=
  if offset + size ≤ total then some ⟨⟨(list.drop offset).take size⟩⟩ else none

/-- `slice` on a (small) byte array read as a list. -/
def sliceK (bytes : ByteArray) (offset size : Nat) : Option ByteArray :=
  sliceL bytes.data.toList bytes.size offset size

/-- The `width` bytes of `list` from `offset` on, as a byte array whose
fields `natural` reads at offsets relative to `offset`. -/
def window (list : List UInt8) (offset width : Nat) : ByteArray :=
  ⟨⟨(list.drop offset).take width⟩⟩

def headerK (bytes : ByteArray) : Option Header := do
  return ⟨← sliceK bytes 0 16, ← natural bytes 16 2, ← natural bytes 18 2,
    ← natural bytes 20 4, ← natural bytes 24 8, ← natural bytes 32 8,
    ← natural bytes 40 8, ← natural bytes 48 4, ← natural bytes 52 2,
    ← natural bytes 54 2, ← natural bytes 56 2, ← natural bytes 58 2,
    ← natural bytes 60 2, ← natural bytes 62 2⟩

def noteK (bytes : ByteArray) : Option Note := do
  let nameSize ← natural bytes 0 4
  let descriptorSize ← natural bytes 4 4
  let noteType ← natural bytes 8 4
  let name ← sliceK bytes 12 nameSize
  let descriptor ← sliceK bytes (12 + aligned4 nameSize) descriptorSize
  require (12 + aligned4 nameSize + aligned4 descriptorSize == bytes.size)
  let namePadding ← sliceK bytes (12 + nameSize) (aligned4 nameSize - nameSize)
  let descriptorPadding ← sliceK bytes (12 + aligned4 nameSize + descriptorSize)
    (aligned4 descriptorSize - descriptorSize)
  require (namePadding.data.toList.all (· == 0) && descriptorPadding.data.toList.all (· == 0))
  return ⟨name, noteType, descriptor⟩

def provenanceK (bytes : ByteArray) : Option Provenance := do
  let domain := "compilatrix/x86-object-provenance/1".toUTF8
  require ((← sliceK bytes 0 domain.size) == domain)
  require ((← natural bytes domain.size 1) == 0)
  let kind ← natural bytes (domain.size + 1) 1
  let root ← sliceK bytes (domain.size + 2) 32
  if kind == 0 then
    require (bytes.size == domain.size + 42)
    return .ixir1Policy root (← natural bytes (domain.size + 34) 4) (← natural bytes (domain.size + 38) 4)
  else if kind == 1 then
    require (bytes.size == domain.size + 34)
    return .ixir2 root
  else none

/-- `parse` on the object as a list of `total` bytes: the header read from
a 64-byte window, the section-header table from one walk to its offset
(each header from its own window), and every section cut out with one walk
(`parseK_eq`). The object is never indexed by position. -/
def parseL (list : List UInt8) (total : Nat) : Option View := do
  let header ← headerK (window list 0 64)
  require (header.sectionCount == 8 && header.sectionEntrySize == 64 && header.sectionNames == 7)
  require (decide (header.sectionOffset + 8 * 64 ≤ total))
  let table := list.drop header.sectionOffset
  let headers ← (List.range 8).mapM (fun index => sectionHeader (window table (index * 64) 64) 0)
  let headers := headers.toArray
  let names ← headers[7]?
  let strings ← sliceL list total names.offset names.size
  let sections ← headers.toList.mapM fun sectionInfo => do
    return (⟨sectionInfo, ← cstring strings sectionInfo.nameOffset,
      ← sliceL list total sectionInfo.offset sectionInfo.size⟩ : Section)
  let sections := sections.toArray
  let text ← sections[1]?
  let symtab ← sections[4]?
  let symbolStrings ← sections[symtab.header.link]?
  require (symtab.data.size % 24 == 0)
  let symbols ← (List.range (symtab.data.size / 24)).mapM (fun index =>
    symbol symtab.data symbolStrings.data (index * 24))
  let symbols := symbols.toArray
  let rela ← sections[2]?
  require (rela.data.size % 24 == 0)
  let relocations ← (List.range (rela.data.size / 24)).mapM (fun index =>
    relocation rela.data symbols (index * 24))
  let noteSection ← sections[3]?
  let note ← noteK noteSection.data
  let provenance ← provenanceK note.descriptor
  return ⟨header, sections, text.data, symbols, relocations.toArray, note, provenance⟩

/-- `parse` in kernel-evaluable style (`parseK_eq`). -/
def parseK (bytes : ByteArray) : Option View := parseL bytes.data.toList bytes.size


/-! ## `parseK = parse` -/

theorem getElem?_mk (l : List UInt8) (i : Nat) : (⟨⟨l⟩⟩ : ByteArray)[i]? = l[i]? := by
  by_cases h : i < l.length
  · rw [getElem?_pos (⟨⟨l⟩⟩ : ByteArray) i (by simpa [ByteArray.size] using h)]
    rw [List.getElem?_eq_getElem h]
    rfl
  · rw [getElem?_neg (⟨⟨l⟩⟩ : ByteArray) i (by simpa [ByteArray.size] using h)]
    rw [List.getElem?_eq_none (by omega)]

theorem size_mk (l : List UInt8) : (⟨⟨l⟩⟩ : ByteArray).size = l.length := rfl

/-- `natural` reads only its `count` bytes. -/
theorem natural_congr {a b : ByteArray} {oa ob : Nat} :
    ∀ {count : Nat}, (∀ i, i < count → a[oa + i]? = b[ob + i]?) → natural a oa count = natural b ob count
  | 0, _ => rfl
  | count + 1, same => by
    simp only [natural]
    rw [natural_congr (fun i hi => same i (by omega)), same count (by omega)]

theorem window_getElem? (l : List UInt8) (base width i : Nat) (h : i < width) :
    (window l base width)[i]? = (⟨⟨l⟩⟩ : ByteArray)[base + i]? := by
  simp only [window, getElem?_mk, List.getElem?_take_of_lt h, List.getElem?_drop]

theorem natural_window (l : List UInt8) (base width offset count : Nat) (h : offset + count ≤ width) :
    natural (window l base width) offset count = natural ⟨⟨l⟩⟩ (base + offset) count :=
  natural_congr fun i hi => by
    rw [window_getElem? l base width (offset + i) (by omega), Nat.add_assoc]

theorem sliceL_eq (bytes : ByteArray) (offset size : Nat) :
    sliceL bytes.data.toList bytes.size offset size = slice bytes offset size := by
  unfold sliceL slice
  split
  · congr 1
    apply ByteArray.ext
    rw [ByteArray.data_extract, ← Array.toList_inj]
    simp [List.extract_eq_take_drop]
  · rfl

theorem sliceK_eq (bytes : ByteArray) (offset size : Nat) : sliceK bytes offset size = slice bytes offset size :=
  sliceL_eq bytes offset size

theorem sliceK_window (l : List UInt8) (width offset size : Nat) (h : offset + size ≤ width) :
    sliceK (window l 0 width) offset size = slice ⟨⟨l⟩⟩ offset size := by
  rw [sliceK_eq]
  unfold slice
  have len : (window l 0 width).size = min width l.length := by
    simp [window, size_mk, List.length_take]
  by_cases fits : offset + size ≤ l.length
  · rw [ite_eq_left (by rw [len]; omega), ite_eq_left (by simpa [size_mk] using fits)]
    congr 1
    apply ByteArray.ext
    rw [ByteArray.data_extract, ByteArray.data_extract, ← Array.toList_inj]
    simp only [window, Array.toList_extract, List.extract_eq_take_drop, List.drop_take, List.take_take]
    congr 1
    omega
  · rw [ite_eq_right (by rw [len]; omega), ite_eq_right (by simpa [size_mk] using fits)]

theorem headerK_window (l : List UInt8) : headerK (window l 0 64) = header ⟨⟨l⟩⟩ := by
  simp (disch := omega) only [headerK, header, sliceK_window, natural_window, Nat.zero_add]

theorem sectionHeader_window (l : List UInt8) (base offset : Nat) :
    sectionHeader (window (l.drop base) offset 64) 0 = sectionHeader ⟨⟨l⟩⟩ (base + offset) := by
  have w : window (l.drop base) offset 64 = window l (base + offset) 64 := by
    simp [window, List.drop_drop]
  rw [w]
  simp (disch := omega) only [sectionHeader, natural_window, Nat.add_zero]

theorem noteK_eq (bytes : ByteArray) : noteK bytes = note bytes := by
  simp only [noteK, note, sliceK_eq, Array.all_toList]

theorem provenanceK_eq (bytes : ByteArray) : provenanceK bytes = provenance bytes := by
  simp only [provenanceK, provenance, sliceK_eq]

theorem sectionHeader_window' (bytes : ByteArray) (base offset : Nat) :
    sectionHeader (window (bytes.data.toList.drop base) offset 64) 0 = sectionHeader bytes (base + offset) :=
  sectionHeader_window bytes.data.toList base offset

/-- The windowed reader is the reader. -/
theorem parseK_eq (bytes : ByteArray) : parseK bytes = parse bytes := by
  have header : headerK (window bytes.data.toList 0 64) = ELFRead.header bytes := headerK_window _
  simp only [parseK, parseL, parse, header, sliceL_eq, noteK_eq, provenanceK_eq, sectionHeader_window']

end Compilatrix.X86.ELFRead

namespace Compilatrix.X86.ELF

open Compilatrix.X86.Encode

/-! ## The validator -/

/-- Byte strings compared as lists. -/
def bytesEq (a b : ByteArray) : Bool := a.data.toList == b.data.toList

def sectionShapeK (index : Nat) (part : ELFRead.Section) : Bool :=
  let h := part.header
  let expected (name : String) (kind flags link info alignment entrySize : Nat) (size := h.size) :=
    bytesEq part.name name.toUTF8 &&
      h == (⟨h.nameOffset, kind, flags, 0, h.offset, size, link, info, alignment, entrySize⟩ : ELFRead.SectionHeader)
  match index with
  | 0 => part.name.data.toList.isEmpty && part.data.data.toList.isEmpty &&
      h == (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : ELFRead.SectionHeader)
  | 1 => expected ".text" 1 6 0 0 16 0
  | 2 => expected ".rela.text" 4 0 4 1 8 24
  | 3 => expected ".note.compilatrix" 7 0 0 0 4 0
  | 4 => expected ".symtab" 2 0 5 2 8 24
  | 5 => expected ".strtab" 3 0 0 0 1 0
  | 6 => expected ".note.GNU-stack" 1 0 0 0 1 0 0
  | 7 => expected ".shstrtab" 3 0 0 0 1 0
  | _ => false

def sectionLayoutK (list : List UInt8) (total : Nat) (sections : List ELFRead.Section)
    (sectionOffset : Nat) (index : Nat) : Bool :=
  match sections[index]? with
  | none => false
  | some part =>
      sectionShapeK index part && part.data.size == part.header.size &&
      ((ELFRead.sliceL list total part.header.offset part.header.size).map (·.data.toList) ==
        some part.data.data.toList) &&
      (index == 0 || (decide (64 ≤ part.header.offset) &&
        decide (part.header.offset + part.header.size ≤ sectionOffset) &&
        part.header.offset % part.header.alignment == 0)) &&
      (index == 0 || index == 7 || match sections[index + 1]? with
        | none => false
        | some next => decide (part.header.offset + part.header.size ≤ next.header.offset))

/-- The first and last bytes of a string table are zero. -/
def terminated (part : ELFRead.Section) : Bool :=
  part.data[0]? == some 0 && part.data[part.data.size - 1]? == some 0

/-- `layout` on the object as a list of `total` bytes. -/
def layoutK (list : List UInt8) (total : Nat) (view : ELFRead.View) : Bool :=
  let sections := view.sections.toList
  decide (total < UInt64.size) && view.header == expectedHeader view.header.sectionOffset &&
    decide (64 ≤ view.header.sectionOffset) && view.header.sectionOffset % 8 == 0 &&
    view.header.sectionOffset + 512 == total && sections.length == 8 &&
    (List.range 8).all (sectionLayoutK list total sections view.header.sectionOffset) &&
    ((sections[1]?).map (·.data.data.toList) == some view.text.data.toList) &&
    ((sections[4]?).map (fun part => part.data.size) == some (24 * view.symbols.size)) &&
    ((sections[2]?).map (fun part => part.data.size) == some (24 * view.relocations.size)) &&
    ((sections[5]?).map terminated == some true) &&
    ((sections[7]?).map terminated == some true) &&
    view.note.name.data.toList == "COMPILATRIX".toUTF8.data.toList ++ [0] && view.note.noteType == 0x43495801

/-- `validName` over the name's bytes as a list. -/
def validNameK (name : String) : Bool :=
  !name.isEmpty && !(name.toUTF8.data.toList.contains 0)

def exportsOkK (input : Input) : Bool :=
  let names := input.exportName :: input.exports.map (·.1)
  decide names.Nodup && names.all validNameK &&
    input.exports.all fun (_, block) =>
      match input.encoded.blockOffsets[block.toNat]? with
      | some offset => decide (offset < input.encoded.text.size)
      | none => false

def relocationBoundsK (view : ELFRead.View) : Bool :=
  view.relocations.toList.all fun relocation =>
    decide (relocation.offset + 4 ≤ view.text.size) && decide (3 ≤ relocation.symbolIndex) &&
    relocation.addend == -4 &&
    match view.symbols[relocation.symbolIndex]? with
    | none => false
    | some symbol => bytesEq symbol.name relocation.symbolName && symbol.sectionIndex == 0 && symbol.info == 0x12

/-- `checkView` on the object as a list of `total` bytes. -/
def checkViewK (input : Input) (list : List UInt8) (total : Nat) (view : ELFRead.View) : Bool :=
  match input.encoded.blockOffsets[input.entryBlock.toNat]?, view.symbols[2]? with
  | some entryOffset, some entrySymbol =>
      layoutK list total view && validNameK input.exportName &&
      decide (entryOffset < input.encoded.text.size) &&
      bytesEq view.text input.encoded.text && symbolMeaning entrySymbol == entryMeaning input entryOffset &&
      view.symbols.toList.map symbolMeaning == (expectedSymbols input entryOffset).toList &&
      view.relocations.toList.map relocationMeaning ==
        input.encoded.relocations.toList.map (fun relocation =>
          (⟨relocation.offset, relocation.symbol.toUTF8, 2, relocation.addend⟩ : RelocationMeaning)) &&
      relocationBoundsK view &&
      view.provenance == expectedProvenance input.provenance && exportsOkK input
  | _, _ => false

/-- `check` in kernel-evaluable style (`checkK_eq`): the object read as a
list once, its length counted once. -/
def checkK (input : Input) (bytes : ByteArray) : Bool :=
  let list := bytes.data.toList
  let total := list.length
  match ELFRead.parseL list total with
  | none => false
  | some view => checkViewK input list total view

/-! ## `checkK = check` -/

theorem bytes_beq_toList (a b : ByteArray) : (a.data.toList == b.data.toList) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]
  exact ⟨fun h => ByteArray.ext h, fun h => h ▸ rfl⟩

theorem bytesEq_eq (a b : ByteArray) : bytesEq a b = (a == b) := bytes_beq_toList a b

theorem bytes_isEmpty (a : ByteArray) : a.data.toList.isEmpty = (a == ByteArray.empty) := by
  rw [← bytes_beq_toList]
  cases a.data.toList <;> rfl

theorem option_bytes_beq (x : Option ByteArray) (y : ByteArray) :
    (x.map (·.data.toList) == some y.data.toList) = (x == some y) := by
  cases x with
  | none => rfl
  | some x =>
    simp only [Option.map_some]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Option.some.injEq, Option.some.injEq, Array.toList_inj]
    exact ⟨fun h => ByteArray.ext h, fun h => h ▸ rfl⟩

theorem array_map_beq {α β : Type} [BEq β] [LawfulBEq β] (a : Array α) (b : Array β) (f : α → β) :
    (a.toList.map f == b.toList) = (a.map f == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← Array.toList_map, Array.toList_inj]

theorem sectionShapeK_eq (index : Nat) (part : ELFRead.Section) :
    sectionShapeK index part = sectionShape index part := by
  unfold sectionShapeK sectionShape
  simp only [bytesEq_eq, bytes_isEmpty]
  rfl

theorem sectionLayoutK_eq (bytes : ByteArray) (view : ELFRead.View) (index : Nat) :
    sectionLayoutK bytes.data.toList bytes.size view.sections.toList view.header.sectionOffset index =
      sectionLayout bytes view index := by
  unfold sectionLayoutK sectionLayout
  simp only [Array.getElem?_toList, sectionShapeK_eq, ELFRead.sliceL_eq, option_bytes_beq]
  rfl

theorem section_data_beq (o : Option ELFRead.Section) (y : ByteArray) :
    (o.map (fun x => x.data.data.toList) == some y.data.toList) = (o.map ELFRead.Section.data == some y) := by
  rw [← option_bytes_beq, Option.map_map]
  rfl

theorem layoutK_eq (bytes : ByteArray) (view : ELFRead.View) :
    layoutK bytes.data.toList bytes.size view = layout bytes view := by
  have sections : sectionLayoutK bytes.data.toList bytes.size view.sections.toList view.header.sectionOffset =
      sectionLayout bytes view := funext (sectionLayoutK_eq bytes view)
  have name : (view.note.name.data.toList == "COMPILATRIX".toUTF8.data.toList ++ [0]) =
      (view.note.name == "COMPILATRIX".toUTF8.push 0) := by
    rw [← bytes_beq_toList, ByteArray.data_push, Array.toList_push]
  unfold layoutK layout terminated
  simp only [sections, Array.getElem?_toList, Array.length_toList, bytesEq_eq, section_data_beq, name]

theorem validNameK_eq (name : String) : validNameK name = validName name := by
  simp only [validNameK, validName, Array.contains_toList]

theorem exportsOkK_eq (input : Input) : exportsOkK input = exportsOk input := by
  have names : validNameK = validName := funext validNameK_eq
  simp only [exportsOkK, exportsOk, names]
  rfl

theorem relocationBoundsK_eq (view : ELFRead.View) : relocationBoundsK view = relocationBounds view := by
  simp only [relocationBoundsK, relocationBounds, bytesEq_eq, Array.all_toList]
  rfl

theorem checkViewK_eq (input : Input) (bytes : ByteArray) (view : ELFRead.View) :
    checkViewK input bytes.data.toList bytes.size view = checkView input bytes view := by
  have relocations : (expectedRelocations input).toList = input.encoded.relocations.toList.map
      (fun relocation => (⟨relocation.offset, relocation.symbol.toUTF8, 2, relocation.addend⟩ : RelocationMeaning)) := by
    simp [expectedRelocations]
  unfold checkViewK checkView
  simp only [layoutK_eq, validNameK_eq, bytesEq_eq, exportsOkK_eq, relocationBoundsK_eq, ← relocations,
    array_map_beq]
  rfl

/-- The kernel-style validator is the validator. -/
theorem checkK_eq (input : Input) (bytes : ByteArray) : checkK input bytes = check input bytes := by
  unfold checkK check
  have p : ELFRead.parseL bytes.data.toList bytes.data.toList.length = ELFRead.parse bytes := ELFRead.parseK_eq bytes
  simp only [p]
  cases ELFRead.parse bytes with
  | none => rfl
  | some view => exact checkViewK_eq input bytes view

end Compilatrix.X86.ELF
