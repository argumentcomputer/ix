import IxCC.X86.ELFCheckK

/-!
# The ELF writer in kernel-evaluable style

`ELF.writeK` is `ELF.write` over lists: every field, section and table is a
`List UInt8` and the object is their concatenation, where `write` appends
`ByteArray`s (whose reference definitions copy the whole object through
`Array.extract` at every append in the kernel). Its `for` loops are
`concatMapK`. `writeK_eq` proves it writes `write`'s bytes, and
`writeCheckedK` (the list writer accepted by `ELF.checkK`) is
`writeChecked` (`writeCheckedK_eq`), so the recheck path's object carries
the same `ELF.Valid` certificate (M1.K1, design note 00).

The provenance note's root is the `Ixon.Address` the configuration names;
the writer reads its 32 bytes as `hash.data.toList`, two projections of the
address's byte literal in a kernel term, and runs no `ByteArray` operation
on it.
-/

namespace IxCC.X86.ELF

open IxCC.X86.Encode

/-! ## The writer -/

def zerosK (count : Nat) : List UInt8 := List.replicate count 0

def naturalBytesK (count value : Nat) : List UInt8 := le count (UInt64.ofNat value)

def u16K (value : Nat) : List UInt8 := naturalBytesK 2 value
def u32K (value : Nat) : List UInt8 := naturalBytesK 4 value
def u64K (value : Nat) : List UInt8 := naturalBytesK 8 value
def word64K (value : UInt64) : List UInt8 := le 8 value

def padToK (input : List UInt8) (size : Nat) : List UInt8 :=
  input ++ zerosK (size - input.length)

def padAlignmentK (input : List UInt8) (alignment : Nat) : List UInt8 :=
  padToK input (alignUp input.length alignment)

/-- A string's UTF-8 bytes. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

def provenanceDomainK : List UInt8 := utf8 "ixcc/x86-object-provenance/1" ++ [0]

def Provenance.bytesK : Provenance → List UInt8
  | .ixir1Policy root loweringVersion passPolicyVersion =>
      provenanceDomainK ++ [RootKind.ixir1Policy.tag] ++ root.hash.data.toList ++
        le 4 loweringVersion.toUInt64 ++ le 4 passPolicyVersion.toUInt64
  | .ixir2 root =>
      provenanceDomainK ++ [RootKind.ixir2.tag] ++ root.hash.data.toList

def noteNameK : List UInt8 := utf8 "IXCC" ++ [0]

def provenanceNoteK (provenance : Provenance) : List UInt8 :=
  let description := provenance.bytesK
  u32K noteNameK.length ++ u32K description.length ++ u32K 0x43495801 ++
    padAlignmentK noteNameK 4 ++ padAlignmentK description 4

structure StringTableK where
  bytes : List UInt8
  offsets : List (String × Nat)

def buildStringTableKAux : List String → List UInt8 → List (String × Nat) → StringTableK
  | [], output, offsets => ⟨output, offsets⟩
  | name :: names, output, offsets =>
    buildStringTableKAux names (output ++ utf8 name ++ [0]) (offsets ++ [(name, output.length)])

def buildStringTableK (names : List String) : StringTableK := buildStringTableKAux names [0] []

def StringTableK.offset? (table : StringTableK) (name : String) : Option Nat :=
  (table.offsets.find? fun entry => entry.1 == name).map (fun entry => entry.2)

def symbolK (name info sectionIndex : Nat) (value size : UInt64) : List UInt8 :=
  u32K name ++ [UInt8.ofNat info] ++ [0] ++ u16K sectionIndex ++ word64K value ++ word64K size

def functionSymbolK (name : Nat) (value size : UInt64) : List UInt8 := symbolK name 0x12 1 value size
def undefinedFunctionSymbolK (name : Nat) : List UInt8 := symbolK name 0x12 0 0 0

def listIndexK? [BEq α] (target : α) : List α → Option Nat
  | [] => none
  | value :: values =>
      if value == target then some 0
      else (listIndexK? target values).map (fun index => index + 1)

def relocationEntryK (offset symbolIndex : Nat) (addend : Int) : List UInt8 :=
  u64K offset ++ word64K (relocationInfo symbolIndex 2) ++ word64K (Int64.ofInt addend).toUInt64

def relocationBytesK (textSize first : Nat) (symbols : List String) :
    List Encode.Relocation → Except Error (List UInt8)
  | [] => .ok []
  | relocation :: relocations =>
    if textSize < relocation.offset + 4 then .error (.invalidRelocation relocation.offset textSize)
    else if relocation.addend != -4 then .error (.invalidRelocationAddend relocation.offset relocation.addend)
    else match listIndexK? relocation.symbol symbols with
      | none => .error (.missingSymbol relocation.symbol)
      | some index =>
        match relocationBytesK textSize first symbols relocations with
        | .ok rest => .ok (relocationEntryK relocation.offset (first + index) relocation.addend ++ rest)
        | .error e => .error e

/-- `step`'s outputs over a list, concatenated, or its first error: the
list form of `write`'s `for` loops that append to an accumulator. -/
def concatMapK {α β ε : Type} (step : α → Except ε (List β)) : List α → Except ε (List β)
  | [] => .ok []
  | a :: l =>
    match step a with
    | .error e => .error e
    | .ok x =>
      match concatMapK step l with
      | .ok rest => .ok (x ++ rest)
      | .error e => .error e

/-- The further exports' function symbols. -/
def exportSymbolsK (textSize : Nat) (strings : StringTableK) :
    List (String × Nat) → Except Error (List UInt8) :=
  concatMapK fun (name, offset) =>
    match strings.offset? name with
    | none => .error (.missingString name)
    | some nameOffset => .ok (functionSymbolK nameOffset (UInt64.ofNat offset) (UInt64.ofNat (textSize - offset)))

/-- The undefined runtime symbols. -/
def undefinedSymbolsK (strings : StringTableK) : List String → Except Error (List UInt8) :=
  concatMapK fun name =>
    match strings.offset? name with
    | none => .error (.missingString name)
    | some nameOffset => .ok (undefinedFunctionSymbolK nameOffset)

def symbolBytesK (textSize entryOffset : Nat) (exportName : String) (exports : List (String × Nat))
    (symbols : List String) (strings : StringTableK) : Except Error (List UInt8) := do
  let some exportOffset := strings.offset? exportName
    | throw (.missingString exportName)
  let first := zerosK 24 ++ symbolK 0 0x03 1 0 0 ++
    functionSymbolK exportOffset (UInt64.ofNat entryOffset) (UInt64.ofNat (textSize - entryOffset))
  let exported ← exportSymbolsK textSize strings exports
  let undefined ← undefinedSymbolsK strings symbols
  pure (first ++ exported ++ undefined)

/-- The further exports with their offsets, checked as `write` checks them. -/
def exportOffsetsK (encoded : Encode.Output) (symbols names : List String) :
    List (String × BlockId) → Except Error (List (String × Nat)) :=
  concatMapK fun (name, block) =>
    if !validNameK name then .error .invalidExportName
    else if symbols.contains name || names.count name != 1 then .error (.duplicateSymbol name)
    else match encoded.blockOffsets.toList[block.toNat]? with
      | none => .error (.missingEntryBlock block)
      | some offset =>
        if encoded.text.data.toList.length ≤ offset then
          .error (.invalidEntryOffset offset encoded.text.data.toList.length)
        else .ok [(name, offset)]

def sectionHeaderK (header : SectionHeader) : List UInt8 :=
  u32K header.name ++ u32K header.sectionType ++ word64K header.flags ++ word64K 0 ++
    u64K header.offset ++ u64K header.size ++ u32K header.link ++
    u32K header.info ++ u64K header.alignment ++ u64K header.entrySize

def elfHeaderK (sectionHeadersOffset sectionCount sectionNamesIndex : Nat) : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    u16K 1 ++ u16K 62 ++ u32K 1 ++ u64K 0 ++ u64K 0 ++ u64K sectionHeadersOffset ++ u32K 0 ++
    u16K 64 ++ u16K 0 ++ u16K 0 ++ u16K 64 ++ u16K sectionCount ++ u16K sectionNamesIndex

def sectionNamesK : List String :=
  [".text", ".rela.text", ".note.ixcc", ".symtab", ".strtab",
    ".note.GNU-stack", ".shstrtab"]

def requireOffsetK (table : StringTableK) (name : String) : Except Error Nat :=
  match table.offset? name with
  | some offset => .ok offset
  | none => .error (.missingString name)

/-- `write` in kernel-evaluable style (`writeK_eq`). -/
def writeK (input : Input) : Except Error (List UInt8) := do
  let text := input.encoded.text.data.toList
  let offsets := input.encoded.blockOffsets.toList
  if !validNameK input.exportName then
    throw .invalidExportName
  let some entryOffset := offsets[input.entryBlock.toNat]?
    | throw (.missingEntryBlock input.entryBlock)
  if text.length ≤ entryOffset then
    throw (.invalidEntryOffset entryOffset text.length)
  let symbols := (input.encoded.relocations.toList.map (fun relocation => relocation.symbol)).eraseDups
  if !(symbols.all validNameK) then
    throw .invalidExportName
  if symbols.contains input.exportName then
    throw (.duplicateSymbol input.exportName)
  let names := input.exportName :: input.exports.map (·.1)
  let exports ← exportOffsetsK input.encoded symbols names input.exports
  let strings := buildStringTableK (names ++ symbols)
  let symbolTable ← symbolBytesK text.length entryOffset input.exportName exports symbols strings
  let relocations ← relocationBytesK text.length (3 + exports.length) symbols input.encoded.relocations.toList
  let note := provenanceNoteK input.provenance
  let sectionStrings := buildStringTableK sectionNamesK

  let textOffset := alignUp 64 16
  let relocationOffset := alignUp (textOffset + text.length) 8
  let noteOffset := alignUp (relocationOffset + relocations.length) 4
  let symbolOffset := alignUp (noteOffset + note.length) 8
  let stringOffset := symbolOffset + symbolTable.length
  let sectionStringOffset := stringOffset + strings.bytes.length
  let sectionHeadersOffset := alignUp (sectionStringOffset + sectionStrings.bytes.length) 8

  let textName ← requireOffsetK sectionStrings ".text"
  let relocationName ← requireOffsetK sectionStrings ".rela.text"
  let noteSectionName ← requireOffsetK sectionStrings ".note.ixcc"
  let symbolName ← requireOffsetK sectionStrings ".symtab"
  let stringName ← requireOffsetK sectionStrings ".strtab"
  let stackNoteName ← requireOffsetK sectionStrings ".note.GNU-stack"
  let sectionStringName ← requireOffsetK sectionStrings ".shstrtab"

  let headers := zerosK 64 ++
    sectionHeaderK
      { name := textName, sectionType := 1, flags := 0x6,
        offset := textOffset, size := text.length, alignment := 16 } ++
    sectionHeaderK
      { name := relocationName, sectionType := 4,
        offset := relocationOffset, size := relocations.length,
        link := 4, info := 1, alignment := 8, entrySize := 24 } ++
    sectionHeaderK
      { name := noteSectionName, sectionType := 7,
        offset := noteOffset, size := note.length, alignment := 4 } ++
    sectionHeaderK
      { name := symbolName, sectionType := 2,
        offset := symbolOffset, size := symbolTable.length,
        link := 5, info := 2, alignment := 8, entrySize := 24 } ++
    sectionHeaderK
      { name := stringName, sectionType := 3,
        offset := stringOffset, size := strings.bytes.length, alignment := 1 } ++
    sectionHeaderK
      { name := stackNoteName, sectionType := 1,
        offset := sectionStringOffset, size := 0, alignment := 1 } ++
    sectionHeaderK
      { name := sectionStringName, sectionType := 3,
        offset := sectionStringOffset, size := sectionStrings.bytes.length, alignment := 1 }

  let output := elfHeaderK sectionHeadersOffset 8 7
  let output := (padToK output textOffset) ++ text
  let output := (padToK output relocationOffset) ++ relocations
  let output := (padToK output noteOffset) ++ note
  let output := (padToK output symbolOffset) ++ symbolTable
  let output := (padToK output stringOffset) ++ strings.bytes
  let output := (padToK output sectionStringOffset) ++ sectionStrings.bytes
  return (padToK output sectionHeadersOffset) ++ headers


/-! ## `writeK = write` -/


theorem zeros_toList (count : Nat) : (zeros count).data.toList = zerosK count := by
  simp [zeros, zerosK]

theorem padTo_toList (input : ByteArray) (size : Nat) :
    (padTo input size).data.toList = padToK input.data.toList size := by
  simp only [padTo, padToK, ByteArray.toList_data_append, zeros_toList, size_eq_length]

theorem padAlignment_toList (input : ByteArray) (alignment : Nat) :
    (padAlignment input alignment).data.toList = padAlignmentK input.data.toList alignment := by
  simp only [padAlignment, padAlignmentK, padTo_toList, size_eq_length]

theorem provenance_bytes_toList (provenance : Provenance) :
    provenance.bytes.data.toList = provenance.bytesK := by
  cases provenance <;> simp only [Provenance.bytes, Provenance.bytesK, provenanceDomain, provenanceDomainK,
    ByteArray.toList_data_append, utf8, byte, bytes, imm32Bytes, littleEndian] <;> rfl

theorem provenanceNote_toList (provenance : Provenance) :
    (provenanceNote provenance).data.toList = provenanceNoteK provenance := by
  simp only [provenanceNote, provenanceNoteK, ByteArray.toList_data_append, padAlignment_toList,
    provenance_bytes_toList, size_eq_length]
  rfl

/-- The string table of `buildStringTable` from a given state. -/
theorem buildStringTable_loop (names : List String) (output : ByteArray) (offsets : List (String × Nat)) :
    let r := names.foldl (fun b a => (b.fst ++ a.toUTF8 ++ byte 0, b.snd ++ [(a, b.fst.size)])) (output, offsets)
    r.1.data.toList = (buildStringTableKAux names output.data.toList offsets).bytes ∧
      r.2 = (buildStringTableKAux names output.data.toList offsets).offsets := by
  induction names generalizing output offsets with
  | nil => exact ⟨rfl, rfl⟩
  | cons name names ih =>
    simp only [List.foldl_cons, buildStringTableKAux]
    have := ih (output ++ name.toUTF8 ++ byte 0) (offsets ++ [(name, output.size)])
    simp only [ByteArray.toList_data_append] at this
    exact this

theorem buildStringTable_eq (names : List String) :
    (buildStringTable names).bytes.data.toList = (buildStringTableK names).bytes ∧
      (buildStringTable names).offsets = (buildStringTableK names).offsets := by
  unfold buildStringTable
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  exact buildStringTable_loop names (byte 0) []

theorem offset?_eq (names : List String) (name : String) :
    (buildStringTable names).offset? name = (buildStringTableK names).offset? name := by
  simp only [StringTable.offset?, StringTableK.offset?, (buildStringTable_eq names).2]

theorem symbol_toList (name info sectionIndex : Nat) (value size : UInt64) :
    (symbol name info sectionIndex value size).data.toList = symbolK name info sectionIndex value size := by
  simp only [symbol, symbolK, ByteArray.toList_data_append]
  rfl

theorem relocationEntry_toList (offset symbolIndex : Nat) (addend : Int) :
    (relocationEntry offset symbolIndex addend).data.toList = relocationEntryK offset symbolIndex addend := by
  simp only [relocationEntry, relocationEntryK, ByteArray.toList_data_append]
  rfl

theorem listIndex_eq {α : Type} [BEq α] (target : α) (values : List α) :
    listIndex? target values = listIndexK? target values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [listIndex?, listIndexK?, ih]

theorem relocationBytes_eq (encoded : Encode.Output) (first : Nat) (symbols : List String) :
    (relocationBytes encoded first symbols).map (·.data.toList) =
      relocationBytesK encoded.text.data.toList.length first symbols encoded.relocations.toList := by
  unfold relocationBytes
  dsimp only
  rw [← Array.forIn_toList]
  have start : relocationBytesK encoded.text.data.toList.length first symbols encoded.relocations.toList =
      (relocationBytesK encoded.text.data.toList.length first symbols encoded.relocations.toList).map
        (ByteArray.empty.data.toList ++ ·) := by
    cases relocationBytesK encoded.text.data.toList.length first symbols encoded.relocations.toList <;> rfl
  rw [start]
  generalize ByteArray.empty = output
  induction encoded.relocations.toList generalizing output with
  | nil => simp [relocationBytesK, Except.map]; rfl
  | cons relocation relocations ih =>
    simp only [List.forIn_cons, relocationBytesK, ← size_eq_length]
    by_cases bound : encoded.text.size < relocation.offset + 4
    · simp only [bound, if_true]
      rfl
    · simp only [bound, if_false]
      by_cases addend : (relocation.addend != -4) = true
      · simp only [addend, if_true]
        rfl
      · simp only [addend, if_false, Bool.false_eq_true]
        rw [← listIndex_eq]
        cases listIndex? relocation.symbol symbols with
        | none => rfl
        | some index =>
          simp only [pure_bind]
          rw [ih, ← size_eq_length]
          cases relocationBytesK encoded.text.size first symbols relocations with
          | error e => rfl
          | ok rest =>
            simp only [Except.map, ByteArray.toList_data_append, relocationEntry_toList, List.append_assoc]

theorem bytes_append_mk (b : ByteArray) (x y : List UInt8) :
    b ++ (⟨⟨x⟩⟩ : ByteArray) ++ ⟨⟨y⟩⟩ = b ++ ⟨⟨x ++ y⟩⟩ := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp only [ByteArray.toList_data_append, List.append_assoc]

theorem bytes_append_nil (b : ByteArray) : b ++ (⟨⟨[]⟩⟩ : ByteArray) = b := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp only [ByteArray.toList_data_append, List.append_nil]

/-- A `for` loop appending each element's bytes to a byte-array accumulator. -/
theorem forIn_bytes {α ε : Type} (step : α → Except ε (List UInt8))
    (f : α → ByteArray → Except ε (ForInStep ByteArray))
    (hf : ∀ a b, f a b = match step a with
      | .error e => .error e
      | .ok x => .ok (.yield (b ++ ⟨⟨x⟩⟩))) :
    ∀ (l : List α) (b : ByteArray), forIn l b f = (concatMapK step l).map (fun x => b ++ ⟨⟨x⟩⟩)
  | [], b => by simp [concatMapK, Except.map, bytes_append_nil]; rfl
  | a :: l, b => by
    rw [List.forIn_cons, hf]
    simp only [concatMapK]
    cases step a with
    | error e => rfl
    | ok x =>
      show forIn l (b ++ ⟨⟨x⟩⟩) f = _
      rw [forIn_bytes step f hf l]
      cases concatMapK step l with
      | error e => rfl
      | ok rest => simp only [Except.map, bytes_append_mk]

/-- A `for` loop appending each element's list to a list accumulator. -/
theorem forIn_list {α β ε : Type} (step : α → Except ε (List β)) (f : α → List β → Except ε (ForInStep (List β)))
    (hf : ∀ a acc, f a acc = match step a with
      | .error e => .error e
      | .ok x => .ok (.yield (acc ++ x))) :
    ∀ (l : List α) (acc : List β), forIn l acc f = (concatMapK step l).map (acc ++ ·)
  | [], acc => by simp [concatMapK, Except.map]; rfl
  | a :: l, acc => by
    rw [List.forIn_cons, hf]
    simp only [concatMapK]
    cases step a with
    | error e => rfl
    | ok x =>
      show forIn l (acc ++ x) f = _
      rw [forIn_list step f hf l]
      cases concatMapK step l with
      | error e => rfl
      | ok rest => simp only [Except.map, List.append_assoc]

theorem mk_toList (b : ByteArray) : (⟨⟨b.data.toList⟩⟩ : ByteArray) = b := rfl

theorem functionSymbol_mk (name : Nat) (value size : UInt64) :
    functionSymbol name value size = ⟨⟨functionSymbolK name value size⟩⟩ := by
  rw [← mk_toList (functionSymbol name value size)]
  exact congrArg (fun l => (⟨⟨l⟩⟩ : ByteArray)) (symbol_toList _ _ _ _ _)

theorem undefinedFunctionSymbol_mk (name : Nat) :
    undefinedFunctionSymbol name = ⟨⟨undefinedFunctionSymbolK name⟩⟩ := by
  rw [← mk_toList (undefinedFunctionSymbol name)]
  exact congrArg (fun l => (⟨⟨l⟩⟩ : ByteArray)) (symbol_toList _ _ _ _ _)

theorem symbolBytes_eq (encoded : Encode.Output) (entryOffset : Nat) (exportName : String)
    (exports : List (String × Nat)) (symbols names : List String) :
    (symbolBytes encoded entryOffset exportName exports symbols (buildStringTable names)).map (·.data.toList) =
      symbolBytesK encoded.text.data.toList.length entryOffset exportName exports symbols
        (buildStringTableK names) := by
  unfold symbolBytes symbolBytesK exportSymbolsK undefinedSymbolsK
  simp only [offset?_eq, ← size_eq_length]
  cases (buildStringTableK names).offset? exportName with
  | none => rfl
  | some exportOffset =>
    dsimp only
    rw [forIn_bytes (fun (p : String × Nat) => match (buildStringTableK names).offset? p.1 with
      | none => .error (.missingString p.1)
      | some nameOffset => .ok (functionSymbolK nameOffset (UInt64.ofNat p.2)
          (UInt64.ofNat (encoded.text.size - p.2))))]
    · cases concatMapK (fun (p : String × Nat) => match (buildStringTableK names).offset? p.1 with
          | none => (.error (Error.missingString p.1) : Except Error (List UInt8))
          | some nameOffset => .ok (functionSymbolK nameOffset (UInt64.ofNat p.2)
              (UInt64.ofNat (encoded.text.size - p.2)))) exports with
      | error e => rfl
      | ok exported =>
        simp only [bind, Except.bind, Except.map]
        rw [forIn_bytes (fun name => match (buildStringTableK names).offset? name with
          | none => .error (.missingString name)
          | some nameOffset => .ok (undefinedFunctionSymbolK nameOffset))]
        · cases concatMapK (fun name => match (buildStringTableK names).offset? name with
              | none => (.error (Error.missingString name) : Except Error (List UInt8))
              | some nameOffset => .ok (undefinedFunctionSymbolK nameOffset)) symbols with
          | error e => rfl
          | ok undefined =>
            simp only [Except.map, nullSymbol, textSectionSymbol,
              functionSymbol_mk, List.append_assoc]
            rfl
        · intro name b
          cases (buildStringTableK names).offset? name <;> simp only [undefinedFunctionSymbol_mk] <;> rfl
    · intro p b
      cases (buildStringTableK names).offset? p.1 <;> simp only [functionSymbol_mk] <;> rfl


theorem sectionHeader_toList (header : SectionHeader) : header.bytes.data.toList = sectionHeaderK header := by
  simp only [SectionHeader.bytes, sectionHeaderK, ByteArray.toList_data_append]
  rfl

theorem elfHeader_toList (sectionHeadersOffset sectionCount sectionNamesIndex : Nat) :
    (elfHeader sectionHeadersOffset sectionCount sectionNamesIndex).data.toList =
      elfHeaderK sectionHeadersOffset sectionCount sectionNamesIndex := by
  simp only [elfHeader, elfHeaderK, ByteArray.toList_data_append]
  rfl

theorem requireOffset_eq (names : List String) (name : String) :
    requireOffset (buildStringTable names) name = requireOffsetK (buildStringTableK names) name := by
  simp only [requireOffset, requireOffsetK, offset?_eq]

  rfl

theorem symbolBytes_eq' (encoded : Encode.Output) (entryOffset : Nat) (exportName : String)
    (exports : List (String × Nat)) (symbols names : List String) :
    (symbolBytes encoded entryOffset exportName exports symbols (buildStringTable names)).map (·.data.toList) =
      symbolBytesK encoded.text.size entryOffset exportName exports symbols (buildStringTableK names) :=
  symbolBytes_eq encoded entryOffset exportName exports symbols names

theorem relocationBytes_eq' (encoded : Encode.Output) (first : Nat) (symbols : List String) :
    (relocationBytes encoded first symbols).map (·.data.toList) =
      relocationBytesK encoded.text.size first symbols encoded.relocations.toList :=
  relocationBytes_eq encoded first symbols

theorem sectionNames_eq : sectionNames = sectionNamesK := rfl

/-- The list writer writes `write`'s bytes. -/
theorem writeK_eq (input : Input) : (write input).map (·.data.toList) = writeK input := by
  have names : validNameK = validName := funext validNameK_eq
  unfold write writeK
  simp only [names, Array.getElem?_toList, ← size_eq_length, runtimeSymbols]
  by_cases h1 : (!validName input.exportName) = true
  · simp only [h1, ite_true]
    rfl
  simp only [h1, ite_false, Bool.false_eq_true]
  cases h2 : input.encoded.blockOffsets[input.entryBlock.toNat]? with
  | none => rfl
  | some entryOffset =>
  simp only []
  by_cases h3 : input.encoded.text.size ≤ entryOffset
  · simp only [h3, ite_true]
    rfl
  simp only [h3, ite_false]
  generalize (input.encoded.relocations.toList.map (fun relocation => relocation.symbol)).eraseDups = symbols
  by_cases h4 : (!symbols.all validName) = true
  · simp only [h4, ite_true]
    rfl
  simp only [h4, ite_false, Bool.false_eq_true]
  by_cases h5 : symbols.contains input.exportName = true
  · simp only [h5, ite_true]
    rfl
  simp only [h5, ite_false, Bool.false_eq_true]
  unfold exportOffsetsK
  simp only [names, ← size_eq_length, Array.getElem?_toList]
  rw [forIn_list (fun (p : String × BlockId) =>
    if !validName p.1 then (.error .invalidExportName : Except Error (List (String × Nat)))
    else if symbols.contains p.1 || (input.exportName :: input.exports.map (·.1)).count p.1 != 1 then
      .error (.duplicateSymbol p.1)
    else match input.encoded.blockOffsets[p.2.toNat]? with
      | none => .error (.missingEntryBlock p.2)
      | some offset =>
        if input.encoded.text.size ≤ offset then .error (.invalidEntryOffset offset input.encoded.text.size)
        else .ok [(p.1, offset)])]
  · cases concatMapK (fun (p : String × BlockId) =>
        if !validName p.1 then (.error .invalidExportName : Except Error (List (String × Nat)))
        else if symbols.contains p.1 || (input.exportName :: input.exports.map (·.1)).count p.1 != 1 then
          .error (.duplicateSymbol p.1)
        else match input.encoded.blockOffsets[p.2.toNat]? with
          | none => .error (.missingEntryBlock p.2)
          | some offset =>
            if input.encoded.text.size ≤ offset then .error (.invalidEntryOffset offset input.encoded.text.size)
            else .ok [(p.1, offset)]) input.exports with
    | error e => rfl
    | ok exports =>
      simp only [Except.map, bind, Except.bind, List.nil_append]
      rw [← symbolBytes_eq']
      cases symbolBytes input.encoded entryOffset input.exportName exports symbols
          (buildStringTable (input.exportName :: List.map (fun x => x.fst) input.exports ++ symbols)) with
      | error e => rfl
      | ok symbolTable =>
        simp only []
        rw [← relocationBytes_eq']
        cases relocationBytes input.encoded (3 + exports.length) symbols with
        | error e => rfl
        | ok relocations =>
          simp only [requireOffset_eq, sectionNames_eq]
          cases requireOffsetK (buildStringTableK sectionNamesK) ".text" with
          | error e => rfl
          | ok textName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".rela.text" with
          | error e => rfl
          | ok relocationName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".note.ixcc" with
          | error e => rfl
          | ok noteSectionName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".symtab" with
          | error e => rfl
          | ok symbolName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".strtab" with
          | error e => rfl
          | ok stringName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".note.GNU-stack" with
          | error e => rfl
          | ok stackNoteName =>
          cases requireOffsetK (buildStringTableK sectionNamesK) ".shstrtab" with
          | error e => rfl
          | ok sectionStringName =>
          simp only [Except.map, pure, Except.pure, padTo_toList, ByteArray.toList_data_append, elfHeader_toList,
            sectionHeader_toList, nullSectionHeader, zeros_toList, provenanceNote_toList,
            (buildStringTable_eq _).1, size_eq_length]
  · intro p acc
    by_cases a : (!validName p.fst) = true
    · simp only [a, ite_true]
      rfl
    simp only [a, ite_false, Bool.false_eq_true]
    by_cases b : (symbols.contains p.fst ||
        List.count p.fst (input.exportName :: List.map (fun x => x.fst) input.exports) != 1) = true
    · simp only [b, ite_true]
      rfl
    simp only [b, ite_false, Bool.false_eq_true]
    cases input.encoded.blockOffsets[p.snd.toNat]? with
    | none => rfl
    | some offset =>
      by_cases c : input.encoded.text.size ≤ offset
      · simp only [c, ite_true]
        rfl
      · simp only [c, ite_false]
        rfl


/-- `writeChecked` in kernel-evaluable style: the list writer, accepted by
`checkK` (`writeCheckedK_eq`). -/
def writeCheckedK (input : Input) : Except CheckedError (Certified input) := do
  let list ← (writeK input).mapError CheckedError.writer
  let bytes : ByteArray := ⟨⟨list⟩⟩
  if accepted : checkK input bytes = true then
    return ⟨bytes, check_sound ((checkK_eq input bytes).symm.trans accepted)⟩
  else throw .invalidObject

/-- The kernel-style certified object is `writeChecked`'s. -/
theorem writeCheckedK_eq (input : Input) : writeCheckedK input = writeChecked input := by
  unfold writeCheckedK writeChecked
  rw [← writeK_eq]
  cases write input with
  | error e => rfl
  | ok bytes =>
    simp only [Except.map, Except.mapError, bind, Except.bind]
    by_cases accepted : check input bytes = true
    · rw [dif_pos (by rw [checkK_eq]; exact accepted), dif_pos accepted]
    · rw [dif_neg (by rw [checkK_eq]; exact accepted), dif_neg accepted]

end IxCC.X86.ELF
