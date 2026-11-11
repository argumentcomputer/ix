import IxCC.X86.Exe.Write
import IxCC.X86.Exe.Read

/-!
# The standalone executable's structural check

`Exe.check` reads a written executable back with the independent reader
(`Exe.Read`) and accepts it only if

* the ELF header is the expected one (an x86-64 `ET_EXEC` entered at the
  shell's first byte, four program headers, no section headers);
* the program headers are exactly the four the layout gives (the file read
  and execute at `fileBase`; the stack and region read and write at
  `dataBase`, zero-filled; the note; no executable stack);
* the file has exactly the planned size, every byte outside the parts is
  zero, and each part is what it should be: the note and the text are the
  object's (as the object reader `ELFRead` reads it), the data is
  `dataBytes`, the shell is the encoded shell;
* the shell makes exactly two calls into the object, `cx_init` and then the
  root, and each `call rel32`, decoded from the file's bytes, lands on that
  export's offset in the embedded text, the offset the object's own symbol
  table gives (`ELF.symbol?`).

`writeChecked` writes and checks, and returns the bytes with `Valid` and the
driver contract for each call (`Layout.driver_canonicalOk`).
-/

namespace IxCC.X86.Exe

open IxCC.X86

def expectedHeader (p : Placement) : ELFRead.Header :=
  ⟨⟨#[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩,
    2, 62, 1, fileBase + p.shellOffset, 64, 0, 0, 64, 56, 4, 64, 0, 0⟩

def expectedPrograms (L : Layout) (p : Placement) : List Read.ProgramHeader :=
  (programHeaders L p).map fun (kind, flags, offset, address, fileSize, memorySize, alignment) =>
    ⟨kind, flags, offset, address, address, fileSize, memorySize, alignment⟩

/-- The bytes `[lo, hi)` of the file are zero. -/
def zerosBetween (bytes : ByteArray) (lo hi : Nat) : Bool :=
  (List.range (hi - lo)).all fun i => bytes[lo + i]? == some 0

/-- Every gap between the parts is zero. -/
def gapsZero (bytes : ByteArray) (p : Placement) : Bool :=
  zerosBetween bytes (p.noteOffset + p.noteSize) p.textOffset &&
    zerosBetween bytes (p.textOffset + p.textSize) p.dataOffset &&
    zerosBetween bytes (p.dataOffset + p.dataSize) p.shellOffset

/-- Each call lands on its export's offset in the embedded text. -/
def callLands (object : ByteArray) (bytes : ByteArray) (p : Placement) (c : Call) : Bool :=
  match ELF.symbol? object c.symbol with
  | some offset => Read.callTarget bytes fileBase c.field == some ((fileBase + p.textOffset + offset : Nat) : Int)
  | none => false

/-- The check of a file against its plan. -/
def checkWith (input : Input) (pl : Plan) (bytes : ByteArray) : Bool :=
  let p := pl.placement
  match Read.parse bytes, ELFRead.parse input.object with
  | some view, some object =>
    view.header == expectedHeader p &&
      view.programs == expectedPrograms input.layout p &&
      bytes.size == p.fileSize &&
      gapsZero bytes p &&
      ((object.sections[3]?).map (·.data)).any (fun note => ELFRead.slice bytes p.noteOffset p.noteSize == some note) &&
      ELFRead.slice bytes p.textOffset p.textSize == some object.text &&
      ELFRead.slice bytes p.dataOffset p.dataSize == some (dataBytes input.arity (fileBase + p.dataOffset)) &&
      ELFRead.slice bytes p.shellOffset p.shellSize == some pl.shell &&
      pl.calls.map (·.symbol) == [initSymbol, input.root] &&
      pl.calls.all (callLands input.object bytes p)
  | _, _ => false

/-- The facts `checkWith` establishes. -/
structure Fields (input : Input) (pl : Plan) (bytes : ByteArray) : Prop where
  header : ∃ view, Read.parse bytes = some view ∧ view.header = expectedHeader pl.placement ∧
    view.programs = expectedPrograms input.layout pl.placement
  size : bytes.size = pl.placement.fileSize
  text : ∃ object, ELFRead.parse input.object = some object ∧
    ELFRead.slice bytes pl.placement.textOffset pl.placement.textSize = some object.text
  shell : ELFRead.slice bytes pl.placement.shellOffset pl.placement.shellSize = some pl.shell
  calls : pl.calls.map (·.symbol) = [initSymbol, input.root]
  lands : ∀ c ∈ pl.calls, ∃ offset, ELF.symbol? input.object c.symbol = some offset ∧
    Read.callTarget bytes fileBase c.field = some ((fileBase + pl.placement.textOffset + offset : Nat) : Int)

theorem checkWith_sound {input : Input} {pl : Plan} {bytes : ByteArray}
    (h : checkWith input pl bytes = true) : Fields input pl bytes := by
  unfold checkWith at h
  split at h
  · rename_i view object hv ho
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hp⟩, hs⟩, _⟩, _⟩, ht⟩, _⟩, hsh⟩, hc⟩, hl⟩ := h
    refine ⟨⟨view, hv, hh, hp⟩, hs, ⟨object, ho, ht⟩, hsh, hc, ?_⟩
    intro c hm
    have := hl c hm
    unfold callLands at this
    split at this
    · rename_i offset hsym
      exact ⟨offset, hsym, by simpa using this⟩
    · simp at this
  · simp at h

/-- The executable check: plan `input` again and check `bytes` against the plan. -/
def check (input : Input) (bytes : ByteArray) : Bool :=
  match objectParts input.object input.root with
  | .error _ => false
  | .ok parts =>
    match plan input parts with
    | .error _ => false
    | .ok pl => checkWith input pl bytes

def Valid (input : Input) (bytes : ByteArray) : Prop :=
  ∃ parts pl, objectParts input.object input.root = .ok parts ∧ plan input parts = .ok pl ∧
    Fields input pl bytes

theorem check_sound {input : Input} {bytes : ByteArray} (h : check input bytes = true) :
    Valid input bytes := by
  unfold check at h
  split at h
  · simp at h
  · rename_i parts hparts
    split at h
    · simp at h
    · rename_i pl hpl
      exact ⟨parts, pl, hparts, hpl, checkWith_sound h⟩

/-- A checked executable: its bytes, the plan they follow, the check's facts,
and the driver contract at each of the shell's calls into the object. -/
structure Certified (input : Input) where
  bytes : ByteArray
  plan : Plan
  valid : ∃ parts, objectParts input.object input.root = .ok parts ∧ X86.Exe.plan input parts = .ok plan ∧
    Fields input plan bytes
  contract : ∀ c ∈ plan.calls,
    (input.layout.driver plan.placement.textOffset c.ret).CanonicalOk plan.placement.textSize

theorem Certified.valid' {input : Input} (c : Certified input) : Valid input c.bytes := by
  obtain ⟨parts, hp, hq, hf⟩ := c.valid
  exact ⟨parts, c.plan, hp, hq, hf⟩

/-- Write the executable, check it, and establish the driver contract at its
calls; refuse if either fails. -/
def writeChecked (input : Input) : Except Error (Certified input) :=
  match hp : objectParts input.object input.root with
  | .error e => .error e
  | .ok parts =>
    match hq : X86.Exe.plan input parts with
    | .error e => .error e
    | .ok pl =>
      let bytes := assemble input parts pl
      if hv : checkWith input pl bytes = true then
        if hL : input.layout.check = true then
          if hc : ∀ c ∈ pl.calls, fileBase + pl.placement.textOffset + pl.placement.textSize ≤ c.ret ∧
              c.ret < dataBase then
            .ok { bytes, plan := pl, valid := ⟨parts, hp, hq, checkWith_sound hv⟩
                  contract := fun c hm => input.layout.driver_canonicalOk hL (hc c hm).1 (hc c hm).2 }
          else .error .contract
        else .error .layout
      else .error .invalidExecutable

end IxCC.X86.Exe
