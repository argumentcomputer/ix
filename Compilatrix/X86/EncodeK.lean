import Compilatrix.X86.Encode

/-!
# E1 encoding in kernel-evaluable style

`Encode.encodeK` is `Encode.encode` over lists: the chunks, the text, the
block offsets and the fixups are lists, the text is patched with
`List.set`, and the `ByteArray` and `Array`s of `Encode.Output` are built
only at the end (`Output.ofLists`), from lists the kernel then reads back
by projection. `encode` concatenates and patches `ByteArray`s, whose
reference definitions copy the whole text through `Array.extract` at every
append (quadratic in the kernel, and `Array` indexing is linear there too).
`encodeK_eq` proves the two equal (M1.K1, design note 00).
-/

namespace Compilatrix.X86.Encode

open Compilatrix.X86

/-- A chunk over lists. -/
structure ChunkK where
  bytes : List UInt8 := []
  fixups : List Fixup := []
  deriving Inhabited

def Chunk.toK (c : Chunk) : ChunkK := ⟨c.bytes.data.toList, c.fixups.toList⟩

def ChunkK.append (left right : ChunkK) : ChunkK :=
  { bytes := left.bytes ++ right.bytes
    fixups := left.fixups ++ right.fixups.map fun fixup =>
      { fixup with offset := left.bytes.length + fixup.offset } }

/-- A control row with a zero rel32 field and its fixup. -/
def rel32K (o : Op) (target : FixupTarget) : ChunkK :=
  let encoded := encodeList o [.imm 0]
  { bytes := encoded, fixups := [{ offset := encoded.length - 4, target }] }

def encodeInstrK : Instr → ChunkK
  | .op o args => ⟨encodeList o args, []⟩
  | .fused producer pargs consumer cargs => ⟨encodeList producer pargs ++ encodeList consumer cargs, []⟩
  | .unwind source => ⟨encodeList unwindRow [.reg .rsp, .mem source], []⟩
  | .call target => rel32K Op.callRel32 (.block target)
  | .callRuntime intrinsic => rel32K Op.callRel32 (.intrinsic intrinsic)

def encodeTerminatorK : Terminator → ChunkK
  | .jump target => rel32K Op.jmpRel32 (.block target)
  | .branch producer args condition ifTrue ifFalse .rel32 =>
      (ChunkK.mk (encodeList producer args) []).append
        ((rel32K (Op.jccRel32 condition) (.block ifTrue)).append (rel32K Op.jmpRel32 (.block ifFalse)))
  | .branch producer args condition ifTrue _ .fall =>
      (ChunkK.mk (encodeList producer args) []).append (rel32K (Op.jccRel32 condition) (.block ifTrue))
  | .tailCall target => rel32K Op.jmpRel32 (.block target)
  | .ret => ⟨encodeList Op.retZO [], []⟩

def encodeBlockK (block : Block) : ChunkK :=
  (block.instructions.toList.foldl (fun (output : ChunkK) instruction => output.append (encodeInstrK instruction))
    {}).append
    (encodeTerminatorK block.terminator)

/-- Each chunk's offset: the lengths of the chunks before it. -/
def layoutK : List ChunkK → Nat → List Nat
  | [], _ => []
  | chunk :: chunks, cursor => cursor :: layoutK chunks (cursor + chunk.bytes.length)

/-- The fixups at their text offsets, chunk by chunk. -/
def locatedFixupsK (chunks : List ChunkK) (offsets : List Nat) : List Fixup :=
  (List.range chunks.length).flatMap fun index =>
    let base := offsets[index]?.getD 0
    ((chunks[index]?.getD default).fixups).map fun fixup => { fixup with offset := base + fixup.offset }

/-- `signed32Bytes` as a list. -/
def signed32List (value : Int) : List UInt8 := le 4 (Int32.ofInt value).toUInt32.toUInt64

/-- `patchSigned32` over a list: the four bytes at `offset` replaced. -/
def patchK (input : List UInt8) (offset : Nat) (value : Int) : Except Error (List UInt8) :=
  if offset + 4 ≤ input.length then
    let patch := signed32List value
    .ok <| (List.range 4).foldl (fun output index => output.set (offset + index) (patch[index]?.getD 0)) input
  else
    .error (.invalidPatch offset input.length)

/-- The fixups resolved over the text: block targets patched, runtime calls
collected as relocations, in order. -/
def resolveK (offsets : List Nat) :
    List Fixup → List UInt8 → List Relocation → Except Error (List UInt8 × List Relocation)
  | [], text, relocations => .ok (text, relocations)
  | fixup :: fixups, text, relocations =>
    match fixup.target with
    | .intrinsic intrinsic =>
      resolveK offsets fixups text (relocations ++ [{ offset := fixup.offset, symbol := intrinsicSymbol intrinsic }])
    | .block target =>
      match offsets[target.toNat]? with
      | none => .error (.missingBlock target)
      | some targetOffset =>
        let afterPatch := fixup.offset + 4
        let displacement := Int.ofNat targetOffset - Int.ofNat afterPatch
        if fitsSigned32 displacement then
          match patchK text fixup.offset displacement with
          | .ok text => resolveK offsets fixups text relocations
          | .error e => .error e
        else .error (.displacementOutOfRange afterPatch targetOffset)

/-- An output from its lists. -/
def Output.ofLists (text : List UInt8) (offsets : List Nat) (relocations : List Relocation) : Output :=
  { text := ⟨⟨text⟩⟩, blockOffsets := ⟨offsets⟩, relocations := ⟨relocations⟩ }

/-- `encode` in kernel-evaluable style (`encodeK_eq`). -/
def encodeK (checked : Checked) : Except Error Output := do
  let chunks := checked.program.blocks.toList.map encodeBlockK
  let offsets := layoutK chunks 0
  let (text, relocations) ← resolveK offsets (locatedFixupsK chunks offsets) (chunks.flatMap (·.bytes)) []
  pure (Output.ofLists text offsets relocations)

/-! ## `encodeK = encode` -/

theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := rfl

theorem Chunk.toK_append (a b : Chunk) : (a.append b).toK = a.toK.append b.toK := by
  simp only [Chunk.append, ChunkK.append, Chunk.toK, ByteArray.toList_data_append, Array.toList_append,
    Array.toList_map, size_eq_length]

theorem rel32_toK (o : Op) (target : FixupTarget) : (rel32 o target).toK = rel32K o target := rfl

theorem raw_toK (bytes : List UInt8) : (Chunk.raw (Encode.bytes bytes)).toK = ⟨bytes, []⟩ := by
  simp [Chunk.raw, Chunk.toK, Encode.bytes]

theorem encodeInstr_toK (instruction : Instr) : (encodeInstr instruction).toK = encodeInstrK instruction := by
  cases instruction with
  | fused producer pargs consumer cargs => rfl
  | op o args => exact raw_toK _
  | unwind source => exact raw_toK _
  | call target => exact rel32_toK _ _
  | callRuntime intrinsic => exact rel32_toK _ _

theorem encodeTerminator_toK (terminator : Terminator) :
    (encodeTerminator terminator).toK = encodeTerminatorK terminator := by
  cases terminator with
  | branch producer args condition yes no reach =>
    cases reach <;> simp only [encodeTerminator, encodeTerminatorK, Chunk.toK_append, rel32_toK, encodeOp,
      raw_toK]
  | jump target => exact rel32_toK _ _
  | tailCall target => exact rel32_toK _ _
  | ret => exact raw_toK _

private theorem foldl_toK (instructions : List Instr) (acc : Chunk) :
    (instructions.foldl (fun output instruction => output.append (encodeInstr instruction)) acc).toK =
      instructions.foldl (fun output instruction => output.append (encodeInstrK instruction)) acc.toK := by
  induction instructions generalizing acc with
  | nil => rfl
  | cons instruction instructions ih =>
    simp only [List.foldl_cons, ih, Chunk.toK_append, encodeInstr_toK]

theorem encodeBlock_toK (block : Block) : (encodeBlock block).toK = encodeBlockK block := by
  unfold encodeBlock encodeBlockK
  rw [Chunk.toK_append, ← Array.foldl_toList, foldl_toK, encodeTerminator_toK]
  rfl

private theorem layout_foldl (chunks : List Chunk) (offsets : Array Nat) (cursor : Nat) :
    (chunks.foldl (fun b a => (b.fst.push b.snd, b.snd + a.bytes.size)) (offsets, cursor)).fst.toList =
      offsets.toList ++ layoutK (chunks.map Chunk.toK) cursor := by
  induction chunks generalizing offsets cursor with
  | nil => simp [layoutK]
  | cons chunk chunks ih =>
    rw [List.foldl_cons, ih]
    simp only [Array.toList_push, List.map_cons, layoutK, List.append_assoc, List.singleton_append]
    rfl

theorem layout_toList (chunks : Array Chunk) :
    (layout chunks).toList = layoutK (chunks.toList.map Chunk.toK) 0 := by
  unfold layout
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, pure_bind]
  rw [← Array.foldl_toList]
  exact layout_foldl chunks.toList #[] 0

theorem concatenate_toList (chunks : Array Chunk) :
    (concatenate chunks).data.toList = (chunks.toList.map Chunk.toK).flatMap (·.bytes) := by
  unfold concatenate
  rw [← Array.foldl_toList]
  suffices ∀ (l : List Chunk) (acc : ByteArray), (l.foldl (fun output chunk => output ++ chunk.bytes) acc).data.toList =
      acc.data.toList ++ (l.map Chunk.toK).flatMap (·.bytes) by
    simpa using this chunks.toList ByteArray.empty
  intro l
  induction l with
  | nil => simp
  | cons chunk chunks ih =>
    intro acc
    simp only [List.foldl_cons, ih, ByteArray.toList_data_append, List.map_cons, List.flatMap_cons,
      List.append_assoc, Chunk.toK]

private theorem push_foldl {α β : Type} (xs : List α) (g : α → β) (acc : Array β) :
    (xs.foldl (fun s f => s.push (g f)) acc).toList = acc.toList ++ xs.map g := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons]

private theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem nested_foldl (chunks : Array Chunk) (g : Nat → Fixup → Fixup) :
    ∀ (indices : List Nat) (acc : Array Fixup),
      (indices.foldl (fun b a => Array.foldl (fun b f => b.push (g a f)) b chunks[a]!.fixups) acc).toList =
        acc.toList ++ indices.flatMap (fun a => chunks[a]!.fixups.toList.map (g a))
  | [], acc => by simp
  | a :: indices, acc => by
    rw [List.foldl_cons, nested_foldl chunks g indices, ← Array.foldl_toList, push_foldl]
    simp

theorem locatedFixups_toList (chunks : Array Chunk) (offsets : Array Nat) :
    (locatedFixups chunks offsets).toList = locatedFixupsK (chunks.toList.map Chunk.toK) offsets.toList := by
  unfold locatedFixups locatedFixupsK
  simp only [Id.run, Array.forIn_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure]
  refine (nested_foldl chunks (fun a f => { offset := offsets[a]! + f.offset, target := f.target })
    (List.range chunks.size) #[]).trans ?_
  simp only [List.nil_append, List.length_map, Array.length_toList]
  apply flatMap_congr_mem
  intro index member
  have bound : index < chunks.size := List.mem_range.mp member
  simp only [getElem!_def, Array.getElem?_toList, List.getElem?_map, Array.getElem?_eq_getElem bound,
    Option.map_some, Option.getD_some, Chunk.toK]
  cases offsets[index]? <;> rfl

private theorem patch_foldl (patch : ByteArray) (offset : Nat) :
    ∀ (indices : List Nat) (input : ByteArray),
      (indices.foldl (fun output index => output.set! (offset + index) (patch.get! index)) input).data.toList =
        indices.foldl (fun output index => output.set (offset + index) (patch.data.toList[index]?.getD 0))
          input.data.toList
  | [], _ => rfl
  | index :: indices, input => by
    rw [List.foldl_cons, List.foldl_cons, patch_foldl patch offset indices]
    congr 1
    cases input
    simp only [ByteArray.set!, Array.toList_set!, ByteArray.get!, getElem!_def, Array.getElem?_toList]
    cases patch.data[index]? <;> rfl

theorem patchK_eq (input : ByteArray) (offset : Nat) (value : Int) :
    (patchSigned32 input offset value).map (·.data.toList) = patchK input.data.toList offset value := by
  unfold patchSigned32 patchK
  rw [← size_eq_length]
  split
  · simp only [Except.map, patch_foldl]
    rfl
  · rfl

/-- The list encoder is the encoder. -/
theorem encodeK_eq (checked : Checked) : encodeK checked = encode checked := by
  unfold encodeK encode
  dsimp only
  have blocks : checked.program.blocks.toList.map encodeBlockK =
      (checked.program.blocks.map encodeBlock).toList.map Chunk.toK := by
    simp [Array.toList_map, List.map_map, Function.comp_def, encodeBlock_toK]
  rw [blocks, ← layout_toList, ← locatedFixups_toList, ← concatenate_toList, ← Array.forIn_toList,
    show ([] : List Relocation) = (#[] : Array Relocation).toList from rfl]
  generalize checked.program.blocks.map encodeBlock = chunks
  generalize layout chunks = offsets
  generalize (locatedFixups chunks offsets).toList = fixups
  generalize concatenate chunks = text
  generalize (#[] : Array Relocation) = relocations
  induction fixups generalizing text relocations with
  | nil =>
    simp only [resolveK, List.forIn_nil]
    rfl
  | cons fixup fixups ih =>
    simp only [resolveK, List.forIn_cons]
    rcases fixup with ⟨offset, target⟩
    cases target with
    | intrinsic intrinsic =>
      simp only [pure_bind]
      rw [← Array.toList_push]
      exact ih text _
    | block target =>
      simp only [Array.getElem?_toList]
      cases offsets[target.toNat]? with
      | none => rfl
      | some targetOffset =>
        simp only []
        split
        · rw [← patchK_eq]
          cases patchSigned32 text offset (Int.ofNat targetOffset - Int.ofNat (offset + 4)) with
          | error e => rfl
          | ok patched =>
            simp only [Except.map, bind_pure_comp]
            exact ih patched relocations
        · rfl

end Compilatrix.X86.Encode
