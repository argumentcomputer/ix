import IxCC.X86.Exe.Machine

/-!
# Where a checked machine executable's parts are (X0-P, third part)

A file `Machine.writeChecked` wrote carries the plan `planFor` made
(`Checked.valid`). `planFor_facts` reads off what `planFor` establishes when
it succeeds: the frame's segments pass `segmentsOk`, the whole file is apart
from every segment, and the parts follow one another (note, text, data,
shell). `slice_getElem?` turns the check's `ELFRead.slice` facts
(`FieldsFor`) into byte-for-byte facts. `FileFacts` collects, for a machine
executable, the numbers the shell proof uses: the file lies below the
zero-filled segments, which lie below `2^47`; the text and the read-only data
are where the plan puts them.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe

/-- What `planFor` establishes about a plan it returns: the segments' check, the file apart from
every segment, and where each part is. -/
structure PlanFacts (f : Frame) (parts : ObjectParts) (pl : Plan) : Prop where
  segments : segmentsOk f.segments = true
  apart : f.segments.all (apart pl.placement.fileSize) = true
  noteOffset : pl.placement.noteOffset = headersSizeFor f.segments.length
  textOffset : pl.placement.textOffset = alignUp (pl.placement.noteOffset + parts.note.size) 64
  textSize : pl.placement.textSize = parts.text.size
  dataOffset : pl.placement.dataOffset = alignUp (pl.placement.textOffset + pl.placement.textSize) 8
  dataSize : pl.placement.dataSize = (f.data (fileBase + pl.placement.dataOffset)).size
  shellOffset : pl.placement.shellOffset = alignUp (pl.placement.dataOffset + pl.placement.dataSize) 16

theorem planFor_facts {f : Frame} {parts : ObjectParts} {pl : Plan} (h : planFor f parts = .ok pl) :
    PlanFacts f parts pl := by
  unfold planFor at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hseg
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i happ
        split at h
        · cases h
        · cases h
          exact ⟨hseg, happ, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
  · cases h

theorem byteArray_getElem? (a : ByteArray) (i : Nat) : a[i]? = a.data[i]? := by
  by_cases h : i < a.size
  · rw [getElem?_pos a i h, Array.getElem?_eq_getElem (show i < a.data.size from h),
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg a i h, Array.getElem?_eq_none (show a.data.size ≤ i from Nat.le_of_not_lt h)]

/-- A slice the reader returns is the file's bytes there. -/
theorem slice_getElem? {bytes x : ByteArray} {off n : Nat} (h : ELFRead.slice bytes off n = some x) :
    off + n ≤ bytes.size ∧ x.size = n ∧ ∀ i < n, bytes[off + i]? = x[i]? := by
  unfold ELFRead.slice at h
  split at h
  · rename_i hle
    cases h
    refine ⟨hle, ?_, fun i hi => ?_⟩
    · show (bytes.extract off (off + n)).data.size = n
      rw [ByteArray.data_extract, Array.size_extract]
      change off + n ≤ bytes.data.size at hle
      omega
    · rw [byteArray_getElem?, byteArray_getElem?, ByteArray.data_extract, Array.getElem?_extract]
      rw [ite_eq_left (by show i < min (off + n) bytes.data.size - off; change off + n ≤ bytes.data.size at hle; omega)]
  · cases h

/-- `alignUp` rounds up. -/
theorem le_alignUp (v a : Nat) (ha : 0 < a) : v ≤ alignUp v a := by
  unfold alignUp
  have := Nat.div_add_mod (v + a - 1) a
  have := Nat.mod_lt (v + a - 1) ha
  have : (v + a - 1) / a * a = a * ((v + a - 1) / a) := Nat.mul_comm _ _
  omega

namespace Machine

/-- **The numbers of a checked machine executable.** -/
structure FileFacts (L : Layout) (step : String) {object : ByteArray} (c : Checked (frame L step) object) : Prop where
  size : c.bytes.size = c.plan.placement.fileSize
  below : fileBase + c.plan.placement.fileSize ≤ dataBase
  textEnd : c.plan.placement.textOffset + c.plan.placement.textSize ≤ c.plan.placement.dataOffset
  dataEnd : c.plan.placement.dataOffset + c.plan.placement.dataSize ≤ c.plan.placement.shellOffset
  text : ∃ parsed, ELFRead.parse object = some parsed ∧ parsed.text.size = c.plan.placement.textSize ∧
    ∀ i < c.plan.placement.textSize, c.bytes[c.plan.placement.textOffset + i]? = parsed.text[i]?
  data : (dataBytes (fileBase + c.plan.placement.dataOffset)).size = c.plan.placement.dataSize ∧
    ∀ i < c.plan.placement.dataSize,
      c.bytes[c.plan.placement.dataOffset + i]? = (dataBytes (fileBase + c.plan.placement.dataOffset))[i]?
  stackArea : 0 < L.stackArea
  regionEnd : L.regionStart + alignUp L.region 0x1000 ≤ 2 ^ 47
  regionSize : 0 < alignUp L.region 0x1000

theorem fileFacts {L : Layout} {step : String} {object : ByteArray} (c : Checked (frame L step) object) :
    FileFacts L step c := by
  obtain ⟨parts, -, hplan, hf⟩ := c.valid
  have hp := planFor_facts hplan
  have hseg := hp.segments
  have happ := hp.apart
  simp only [frame, Layout.segments, segmentsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hseg
  simp only [frame, Layout.segments, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, apart,
    Bool.or_eq_true, decide_eq_true_eq] at happ
  obtain ⟨parsed, hparse, htext⟩ := hf.text
  obtain ⟨htle, htsize, htext⟩ := slice_getElem? htext
  obtain ⟨hdle, hdsize, hdata⟩ := slice_getElem? hf.data
  have hd : dataBase = 268435456 := rfl
  have hfb : fileBase = 4194304 := rfl
  have hsh : c.plan.placement.shellOffset + c.plan.placement.shellSize = c.plan.placement.fileSize := rfl
  have h1 := le_alignUp (c.plan.placement.textOffset + c.plan.placement.textSize) 8 (by decide)
  have h2 := le_alignUp (c.plan.placement.dataOffset + c.plan.placement.dataSize) 16 (by decide)
  rw [← hp.dataOffset] at h1
  rw [← hp.shellOffset] at h2
  refine ⟨hf.size, ?_, h1, h2, ⟨parsed, hparse, htsize, htext⟩, ⟨hdsize, hdata⟩, by omega, by omega, by omega⟩
  rcases happ.1 with h | h <;> omega

end Machine

end IxCC.X86.Exe
