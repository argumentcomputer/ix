import IxCC.X86.Exe.Write
import IxCC.X86.Exe.Read

/-! # Hardened `.ix.cert` v1 ELF64 Certificate Trailer (`BE-1`, `BE-3`)

Implements the red-team-hardened `.ix.cert` v1 ELF64 trailer format:

```text
0x0000 ┌────────────────────────────────────────────────────────────┐
       │ core[0..coreSz): ELF64 header (e_shoff/e_shnum/e_shstrndx  │
       │   patched), PHDRs, .note.ixcc, .text, .rodata, proved shell│
coreSz ├────────────────────────────────────────────────────────────┤
       │ [coreSz .. alignUp(coreSz, 4096)): strict 0xCC (int3) sled │
pageEnd├────────────────────────────────────────────────────────────┤
       │ .ix.cert (non-alloc SHT_PROGBITS, sh_offset == pageEnd):   │
       │   magic "IXCERT\0\1" | mode 0x01 | exeKind | stack | region│
       │   | rootNames | CompileClaim bytes | cert | env | equations│
certEnd├────────────────────────────────────────────────────────────┤
       │ .shstrtab ("\x00.ix.cert\x00.shstrtab\x00", 20 bytes)      │
       │ zero pad to 8-byte alignment (0..7 bytes of 0x00)          │
shoff  ├────────────────────────────────────────────────────────────┤
       │ Exact 3-entry ELF64 Section Header Table (192 bytes):      │
       │   [0] SHT_NULL  [1] .ix.cert  [2] .shstrtab (flush at EOF) │
       └────────────────────────────────────────────────────────────┘
```

Properties proved in this module:
- `checkTrailer_core_eq`: zeroing ONLY the 12 shdr bytes `[40..48)`, `[60..62)`,
  `[62..64)` of `image[0..core.size)` reproduces `core` byte-for-byte.
- `checkTrailer_sled_int3`: every byte in the RX page tail
  `[core.size .. alignUp core.size 4096)` is `0xCC` (`int3`), preventing Linux
  `fs/binfmt_elf.c` RX page-tail code smuggling.
- `checkTrailer_payload_eq`: `image[pageEnd .. pageEnd + payload.size)` equals
  `payload` verbatim, starting at a 4096-byte page boundary outside `PT_LOAD[0]`.
- `checkTrailer_flush_eof`: the 3-entry ELF64 section header table ends flush at
  EOF with zero trailing bytes.
- `Payload.decode_encode`: canonical roundtrip for `.ix.cert` v1 payload bytes. -/

set_option autoImplicit false

namespace IxCC.X86.Exe.Cert

open IxCC.X86

/-- Page boundary separating `PT_LOAD[0]` from non-alloc `.ix.cert` (4 KiB). -/
def certPageSize : Nat := 0x1000

/-- x86-64 `int3` breakpoint trap byte filling the RX page tail `[coreSz .. pageEnd)`. -/
def trapByte : UInt8 := 0xCC

/-- Exact 8-byte magic header `"IXCERT\0\1"` for `.ix.cert` v1. -/
def certMagic : ByteArray :=
  ByteArray.mk #[0x49, 0x58, 0x43, 0x45, 0x52, 0x54, 0x00, 0x01]

/-- Packaging mode byte `0x01`: direct `Recheck` witness. -/
def modeRecheck : UInt8 := 0x01

/-- Exact 20-byte `.shstrtab` contents: `"\x00.ix.cert\x00.shstrtab\x00"`. -/
def shstrtabBytes : ByteArray :=
  ByteArray.mk #[
    0x00,
    0x2e, 0x69, 0x78, 0x2e, 0x63, 0x65, 0x72, 0x74, 0x00,
    0x2e, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0x00
  ]

/-- ELF64 section header entry size (64 bytes), count (3), and table size (192 bytes). -/
def shdrEntrySize : Nat := 64
def shdrCount : Nat := 3
def shdrTableSize : Nat := shdrCount * shdrEntrySize

/-- Errors produced when attaching, extracting, or validating `.ix.cert` v1 trailers. -/
inductive CertError where
  | coreTooSmall
  | coreHasShdr
  | badShentsize
  | coreTooLarge
  | payloadTooLarge
  | badElf (reason : String)
  | badSled
  | badShstrtab
  | badPadding
  | badMagic
  | unsupportedMode (mode : UInt8)
  | badPayload (reason : String)
  | trailerMismatch
  deriving BEq, Repr, Inhabited

def CertError.render : CertError → String
  | .coreTooSmall => "executable core is smaller than the 64-byte ELF64 header"
  | .coreHasShdr => "executable core already carries ELF section headers"
  | .badShentsize => "executable core ELF header does not set e_shentsize = 64"
  | .coreTooLarge => "executable core exceeds maximum size"
  | .payloadTooLarge => "certificate payload exceeds 4 GiB limit"
  | .badElf r => s!"invalid ELF64 certificate trailer: {r}"
  | .badSled => "RX page tail [coreSz, pageEnd) contains a non-0xCC byte (code smuggling rejected)"
  | .badShstrtab => ".shstrtab bytes do not match exact v1 table"
  | .badPadding => "section header alignment padding contains a non-zero byte"
  | .badMagic => ".ix.cert magic header mismatch (expected IXCERT\\0\\1)"
  | .unsupportedMode m => s!"unsupported .ix.cert mode byte {m} (expected 0x01)"
  | .badPayload r => s!"malformed .ix.cert payload: {r}"
  | .trailerMismatch => "certified executable bytes do not match deterministic re-assembly"

/-- Zero ONLY the 12 ELF64 section-header pointer bytes `[40..48)` (`e_shoff`),
`[60..62)` (`e_shnum`), and `[62..64)` (`e_shstrndx`). -/
def zeroShdr (bytes : ByteArray) : ByteArray :=
  if bytes.size < 64 then bytes
  else
    bytes.extract 0 40 ++
      ByteArray.mk (Array.replicate 8 0) ++
      bytes.extract 48 60 ++
      ByteArray.mk (Array.replicate 4 0) ++
      bytes.extract 64 bytes.size

/-- Patch ONLY `[40..48)` (`e_shoff := shoff`), `[60..62)` (`e_shnum := 3`),
and `[62..64)` (`e_shstrndx := 2`) in `core`. -/
def patchShdr (core : ByteArray) (shoff : Nat) : ByteArray :=
  if core.size < 64 then core
  else
    core.extract 0 40 ++
      ByteArray.mk (le64 shoff).toArray ++
      core.extract 48 60 ++
      ByteArray.mk (le16 shdrCount ++ le16 2).toArray ++
      core.extract 64 core.size

/-- Serialize one 64-byte ELF64 section header (`Elf64_Shdr`). -/
def shdrBytes (nameOffset sectionType flags address offset size link info alignment entrySize : Nat) :
    List UInt8 :=
  le32 nameOffset ++ le32 sectionType ++ le64 flags ++ le64 address ++
    le64 offset ++ le64 size ++ le32 link ++ le32 info ++
    le64 alignment ++ le64 entrySize

/-- Exact 192-byte 3-entry ELF64 section header table:
`[0] SHT_NULL`, `[1] .ix.cert` (non-alloc `SHT_PROGBITS` at `pageEnd`),
`[2] .shstrtab` (non-alloc `SHT_STRTAB` at `shstrOff`). -/
def sectionTableBytes (pageEnd payloadSize shstrOff : Nat) : ByteArray :=
  let s0 := shdrBytes 0 0 0 0 0 0 0 0 0 0
  let s1 := shdrBytes 1 1 0 0 pageEnd payloadSize 0 0 8 0
  let s2 := shdrBytes 10 3 0 0 shstrOff shstrtabBytes.size 0 0 1 0
  ByteArray.mk (s0 ++ s1 ++ s2).toArray

/-- Raw assembly of a hardened `.ix.cert` v1 certified executable image from
`core` and `payload`. -/
def attachTrailerRaw (core payload : ByteArray) : ByteArray :=
  let coreSz := core.size
  let pageEnd := alignUp coreSz certPageSize
  let sled := ByteArray.mk (Array.replicate (pageEnd - coreSz) trapByte)
  let shstrOff := pageEnd + payload.size
  let shstrEnd := shstrOff + shstrtabBytes.size
  let shoff := alignUp shstrEnd 8
  let shPad := ByteArray.mk (Array.replicate (shoff - shstrEnd) 0)
  let sht := sectionTableBytes pageEnd payload.size shstrOff
  patchShdr core shoff ++ sled ++ payload ++ shstrtabBytes ++ shPad ++ sht

/-- Attach a hardened `.ix.cert` v1 trailer to a checked standalone executable `core`. -/
def attachTrailer (core payload : ByteArray) : Except CertError ByteArray := do
  unless 64 ≤ core.size do throw .coreTooSmall
  unless zeroShdr core == core do throw .coreHasShdr
  unless ELFRead.natural core 58 2 == some shdrEntrySize do throw .badShentsize
  unless core.size < 2 ^ 40 do throw .coreTooLarge
  unless payload.size < 2 ^ 32 do throw .payloadTooLarge
  pure (attachTrailerRaw core payload)

/-- Check that every byte in `bytes[lo .. hi)` equals `b`. -/
def allByteInRange (bytes : ByteArray) (lo hi : Nat) (b : UInt8) : Bool :=
  if hi ≤ bytes.size && lo ≤ hi then
    (List.range (hi - lo)).all fun k => bytes[lo + k]? == some b
  else false

/-- Strictly parse and extract `(coreSz, payload)` from a hardened `.ix.cert` v1
ELF64 executable image, rejecting any non-`0xCC` RX page-tail byte, non-zero
padding, unexpected section headers, `SHF_ALLOC` flag, unaligned `.ix.cert`, or
trailing bytes past the 3-entry section header table. -/
def extractTrailer (image : ByteArray) : Except CertError (Nat × ByteArray) := do
  let some v := Read.parse image | throw (.badElf "unreadable ELF64 header or program headers")
  let h := v.header
  unless h.sectionEntrySize == shdrEntrySize do
    throw (.badElf s!"e_shentsize = {h.sectionEntrySize}, expected 64")
  unless h.sectionCount == shdrCount do
    throw (.badElf s!"e_shnum = {h.sectionCount}, expected 3")
  unless h.sectionNames == 2 do
    throw (.badElf s!"e_shstrndx = {h.sectionNames}, expected 2")
  unless h.sectionOffset + shdrTableSize == image.size do
    throw (.badElf "section header table does not end flush at EOF")
  let some ph0 := v.programs[0]? | throw (.badElf "missing PT_LOAD[0]")
  unless ph0.kind == 1 && ph0.offset == 0 && ph0.fileSize == ph0.memorySize do
    throw (.badElf "invalid PT_LOAD[0] segment")
  let coreSz := ph0.fileSize
  unless 64 ≤ coreSz && coreSz ≤ image.size do
    throw (.badElf "PT_LOAD[0] fileSize out of range")
  let pageEnd := alignUp coreSz certPageSize
  unless pageEnd ≤ h.sectionOffset do
    throw (.badElf "section table starts before pageEnd")
  let some s0 := ELFRead.sectionHeader image h.sectionOffset
    | throw (.badElf "missing section header 0")
  let some s1 := ELFRead.sectionHeader image (h.sectionOffset + 64)
    | throw (.badElf "missing section header 1")
  let some s2 := ELFRead.sectionHeader image (h.sectionOffset + 128)
    | throw (.badElf "missing section header 2")
  let nullShdr : ELFRead.SectionHeader := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  unless s0 == nullShdr do
    throw (.badElf "section header 0 is not SHT_NULL")
  unless s1.nameOffset == 1 && s1.sectionType == 1 && s1.flags == 0 && s1.address == 0 &&
      s1.offset == pageEnd && s1.link == 0 && s1.info == 0 && s1.alignment == 8 &&
      s1.entrySize == 0 do
    throw (.badElf "section header 1 (.ix.cert) violates non-alloc page-aligned layout")
  let certEnd := pageEnd + s1.size
  unless certEnd ≤ h.sectionOffset do
    throw (.badElf ".ix.cert section extends past section header table")
  unless s2.nameOffset == 10 && s2.sectionType == 3 && s2.flags == 0 && s2.address == 0 &&
      s2.offset == certEnd && s2.size == shstrtabBytes.size && s2.link == 0 && s2.info == 0 &&
      s2.alignment == 1 && s2.entrySize == 0 do
    throw (.badElf "section header 2 (.shstrtab) violates exact v1 layout")
  let shstrEnd := certEnd + shstrtabBytes.size
  unless h.sectionOffset == alignUp shstrEnd 8 do
    throw (.badElf "e_shoff is not 8-byte aligned immediately after .shstrtab")
  unless allByteInRange image coreSz pageEnd trapByte do
    throw .badSled
  unless image.extract certEnd shstrEnd == shstrtabBytes do
    throw .badShstrtab
  unless allByteInRange image shstrEnd h.sectionOffset 0 do
    throw .badPadding
  pure (coreSz, image.extract pageEnd certEnd)

/-- Deterministic whole-image check: `image` equals `attachTrailer core payload`
bit-for-bit. -/
def checkTrailer (core payload image : ByteArray) : Bool :=
  match attachTrailer core payload with
  | .ok expected => expected == image
  | .error _ => false

/-! ## `.ix.cert` v1 Payload Codec -/

/-- Executable shell flavor stored in `.ix.cert` v1. -/
inductive ExeKind where
  | plain
  | machine
  deriving BEq, DecidableEq, Repr, Inhabited

namespace ExeKind

def toUInt8 : ExeKind → UInt8
  | .plain => 0
  | .machine => 1

def ofUInt8? : UInt8 → Option ExeKind
  | 0 => some .plain
  | 1 => some .machine
  | _ => none

@[simp] theorem ofUInt8?_toUInt8 (k : ExeKind) : ofUInt8? k.toUInt8 = some k := by
  cases k <;> rfl

end ExeKind

/-- Structured contents of the `.ix.cert` v1 section (`mode = 0x01`, direct `Recheck` witness). -/
structure Payload where
  exeKind : ExeKind
  stack : Nat
  region : Nat
  rootNames : List String
  claimBytes : ByteArray
  certBytes : ByteArray
  envBytes : ByteArray
  eqBytes : ByteArray
  deriving BEq, Repr, Inhabited

namespace Payload

/-- Well-formedness bounds for canonical encoding. -/
def WellFormed (p : Payload) : Prop :=
  p.stack < 2 ^ 64 ∧
  p.region < 2 ^ 64 ∧
  p.rootNames.length < 2 ^ 32 ∧
  (∀ s ∈ p.rootNames, s.toUTF8.size < 2 ^ 32) ∧
  p.claimBytes.size < 2 ^ 32 ∧
  p.certBytes.size < 2 ^ 32 ∧
  p.envBytes.size < 2 ^ 32 ∧
  p.eqBytes.size < 2 ^ 32

private def putBytes (b : ByteArray) : ByteArray :=
  ByteArray.mk (le32 b.size).toArray ++ b

private def putStrings : List String → ByteArray
  | [] => ByteArray.empty
  | s :: rest => putBytes s.toUTF8 ++ putStrings rest

/-- Canonically serialize a `.ix.cert` v1 payload (`mode = 0x01`). -/
def encode (p : Payload) : ByteArray :=
  certMagic ++
    ByteArray.mk #[modeRecheck, p.exeKind.toUInt8] ++
    ByteArray.mk (le64 p.stack ++ le64 p.region ++ le32 p.rootNames.length).toArray ++
    putStrings p.rootNames ++
    putBytes p.claimBytes ++
    putBytes p.certBytes ++
    putBytes p.envBytes ++
    putBytes p.eqBytes

private def getLenBytes (bs : ByteArray) (pos : Nat) : Except CertError (ByteArray × Nat) := do
  let some n := ELFRead.natural bs pos 4 | throw (.badPayload "truncated 32-bit length")
  let start := pos + 4
  let stop := start + n
  unless stop ≤ bs.size do throw (.badPayload "truncated length-prefixed field")
  pure (bs.extract start stop, stop)

private def getStrings (bs : ByteArray) : Nat → Nat → Except CertError (List String × Nat)
  | 0, pos => pure ([], pos)
  | n + 1, pos => do
    let (raw, pos') ← getLenBytes bs pos
    let some s := String.fromUTF8? raw | throw (.badPayload "invalid UTF-8 in root name")
    let (rest, pos'') ← getStrings bs n pos'
    pure (s :: rest, pos'')

/-- Strictly decode a `.ix.cert` v1 payload, rejecting bad magic, unsupported
mode, truncated fields, invalid UTF-8, or trailing bytes. -/
def decode (bs : ByteArray) : Except CertError Payload := do
  unless bs.size ≥ 30 do throw (.badPayload "payload shorter than 30-byte header")
  unless bs.extract 0 8 == certMagic do throw .badMagic
  let some mode := bs[8]? | throw .badMagic
  unless mode == modeRecheck do throw (.unsupportedMode mode)
  let some kindByte := bs[9]? | throw (.badPayload "missing exeKind byte")
  let some exeKind := ExeKind.ofUInt8? kindByte | throw (.badPayload "invalid exeKind byte")
  let some stack := ELFRead.natural bs 10 8 | throw (.badPayload "truncated stack field")
  let some region := ELFRead.natural bs 18 8 | throw (.badPayload "truncated region field")
  let some rootCount := ELFRead.natural bs 26 4 | throw (.badPayload "truncated root count")
  unless rootCount ≤ 1024 do throw (.badPayload "excessive root count")
  let (rootNames, p1) ← getStrings bs rootCount 30
  let (claimBytes, p2) ← getLenBytes bs p1
  let (certBytes, p3) ← getLenBytes bs p2
  let (envBytes, p4) ← getLenBytes bs p3
  let (eqBytes, p5) ← getLenBytes bs p4
  unless p5 == bs.size do throw (.badPayload "trailing bytes in .ix.cert payload")
  pure { exeKind, stack, region, rootNames, claimBytes, certBytes, envBytes, eqBytes }

end Payload

/-! ## Soundness Theorems for `.ix.cert` v1 Trailer Layout -/

private theorem size_le16 (n : Nat) : (le16 n).length = 2 := by
  simp [le16]

private theorem size_le32 (n : Nat) : (le32 n).length = 4 := by
  simp [le32]

private theorem size_le64 (n : Nat) : (le64 n).length = 8 := by
  simp [le64]

private theorem size_shdrBytes (a b c d e f g h i j : Nat) :
    (shdrBytes a b c d e f g h i j).length = 64 := by
  simp [shdrBytes, size_le32, size_le64]

theorem size_sectionTableBytes (pageEnd payloadSize shstrOff : Nat) :
    (sectionTableBytes pageEnd payloadSize shstrOff).size = shdrTableSize := by
  unfold sectionTableBytes shdrTableSize shdrCount shdrEntrySize
  show (shdrBytes 0 0 0 0 0 0 0 0 0 0 ++
    shdrBytes 1 1 0 0 pageEnd payloadSize 0 0 8 0 ++
    shdrBytes 10 3 0 0 shstrOff shstrtabBytes.size 0 0 1 0).toArray.size = 3 * 64
  simp only [List.size_toArray, List.length_append, size_shdrBytes]

private theorem byteArray_size_append (a b : ByteArray) : (a ++ b).size = a.size + b.size :=
  ByteArray.size_append

private theorem byteArray_mk_size (arr : Array UInt8) : (ByteArray.mk arr).size = arr.size := rfl

private theorem byteArray_extract_size (a : ByteArray) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (a.extract lo hi).size = hi - lo := by
  rw [ByteArray.size_extract]
  omega

theorem size_patchShdr {core : ByteArray} (h : 64 ≤ core.size) (shoff : Nat) :
    (patchShdr core shoff).size = core.size := by
  have hlt : ¬ core.size < 64 := by omega
  unfold patchShdr
  rw [ite_eq_right hlt]
  simp only [byteArray_size_append, byteArray_mk_size, List.size_toArray, List.length_append,
    size_le64, size_le16]
  rw [byteArray_extract_size core 0 40 (by omega) (by omega)]
  rw [byteArray_extract_size core 48 60 (by omega) (by omega)]
  rw [byteArray_extract_size core 64 core.size (by omega) (Nat.le_refl _)]
  omega

private theorem byteArray_getElem_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).data[i]? = a.data[i]? := by
  rw [ByteArray.data_append, Array.getElem?_append_left hi]

private theorem byteArray_getElem_append_right {a b : ByteArray} {i : Nat} (hi : a.size ≤ i) :
    (a ++ b).data[i]? = b.data[i - a.size]? := by
  rw [ByteArray.data_append, Array.getElem?_append_right hi]
  rfl

private theorem byteArray_getElem?_extract {a : ByteArray} {lo hi i : Nat}
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (hi' : i < hi - lo) :
    (a.extract lo hi).data[i]? = a.data[lo + i]? := by
  rw [ByteArray.data_extract, Array.getElem?_extract]
  have h1 : i < min hi a.data.size - lo := by
    change hi ≤ a.data.size at hhi
    omega
  rw [ite_eq_left h1]

private theorem byteArray_ext_getElem? {a b : ByteArray}
    (hsz : a.size = b.size) (hget : ∀ i < a.size, a.data[i]? = b.data[i]?) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · exact hsz
  · intro i hi1 hi2
    have h := hget i hi1
    rw [Array.getElem?_eq_getElem hi1, Array.getElem?_eq_getElem hi2] at h
    exact Option.some.inj h

theorem byteArray_extract_append_left (a b : ByteArray) :
    (a ++ b).extract 0 a.size = a := by
  have hsz : ((a ++ b).extract 0 a.size).size = a.size := by
    rw [byteArray_extract_size (a ++ b) 0 a.size (Nat.zero_le _) (by rw [byteArray_size_append]; omega)]
    omega
  apply byteArray_ext_getElem? hsz
  intro i hi
  have hi' : i < a.size := by rw [hsz] at hi; exact hi
  rw [byteArray_getElem?_extract (Nat.zero_le _) (by rw [byteArray_size_append]; omega) (by omega)]
  simp only [Nat.zero_add]
  exact byteArray_getElem_append_left hi'

theorem byteArray_extract_append_mid (a b c : ByteArray) :
    (a ++ b ++ c).extract a.size (a.size + b.size) = b := by
  have htot : a.size + b.size ≤ (a ++ b ++ c).size := by
    simp only [byteArray_size_append]; omega
  have hsz : ((a ++ b ++ c).extract a.size (a.size + b.size)).size = b.size := by
    rw [byteArray_extract_size _ _ _ (by omega) htot]; omega
  apply byteArray_ext_getElem? hsz
  intro i hi
  have hi' : i < b.size := by rw [hsz] at hi; exact hi
  rw [byteArray_getElem?_extract (by omega) htot (by omega)]
  rw [byteArray_getElem_append_left (by rw [byteArray_size_append]; omega)]
  rw [byteArray_getElem_append_right (by omega)]
  have : a.size + i - a.size = i := by omega
  rw [this]

/-- Zeroing the 12 shdr bytes of `patchShdr core shoff` recovers `core` identically
whenever `core` itself had zeroed shdr bytes (`zeroShdr core = core`). -/
theorem zeroShdr_patchShdr {core : ByteArray} (h64 : 64 ≤ core.size)
    (hz : zeroShdr core = core) (shoff : Nat) :
    zeroShdr (patchShdr core shoff) = core := by
  suffices h : zeroShdr (patchShdr core shoff) = zeroShdr core by rw [h, hz]
  have hlt : ¬ core.size < 64 := by omega
  have hpSz : (patchShdr core shoff).size = core.size := size_patchShdr h64 shoff
  have hzeroSz (x : ByteArray) (hx : 64 ≤ x.size) : (zeroShdr x).size = x.size := by
    unfold zeroShdr
    rw [ite_eq_right (by omega)]
    simp only [byteArray_size_append, byteArray_mk_size, Array.size_replicate]
    rw [byteArray_extract_size x 0 40 (by omega) (by omega)]
    rw [byteArray_extract_size x 48 60 (by omega) (by omega)]
    rw [byteArray_extract_size x 64 x.size (by omega) (Nat.le_refl _)]
    omega
  have hzSz : (zeroShdr (patchShdr core shoff)).size = core.size := by
    rw [hzeroSz _ (by omega), hpSz]
  have h1 : (ByteArray.mk (le64 shoff).toArray).size = 8 := by
    rw [byteArray_mk_size, List.size_toArray, size_le64]
  have h2 : (ByteArray.mk (le16 shdrCount ++ le16 2).toArray).size = 4 := by
    rw [byteArray_mk_size, List.size_toArray, List.length_append, size_le16, size_le16]
  have hz1 : (ByteArray.mk (Array.replicate 8 (0 : UInt8))).size = 8 := by
    rw [byteArray_mk_size, Array.size_replicate]
  have hz2 : (ByteArray.mk (Array.replicate 4 (0 : UInt8))).size = 4 := by
    rw [byteArray_mk_size, Array.size_replicate]
  apply byteArray_ext_getElem? (by rw [hzSz, hzeroSz core h64])
  intro i hi
  have hiCore : i < core.size := by rw [hzSz] at hi; exact hi
  have heq_region (x : ByteArray) (hx : 64 ≤ x.size) (j : Nat) (hj : j < x.size) :
      (zeroShdr x).data[j]? =
        if j < 40 then x.data[j]?
        else if j < 48 then some 0
        else if j < 60 then x.data[j]?
        else if j < 64 then some 0
        else x.data[j]? := by
    unfold zeroShdr
    rw [ite_eq_right (by omega)]
    have s1 : (x.extract 0 40).size = 40 := byteArray_extract_size x 0 40 (by omega) (by omega)
    have s2 : (x.extract 48 60).size = 12 := byteArray_extract_size x 48 60 (by omega) (by omega)
    by_cases c1 : j < 40
    · simp only [c1, ↓reduceIte]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2, hz2]; omega)]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2]; omega)]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1]; omega)]
      rw [byteArray_getElem_append_left (by omega)]
      rw [byteArray_getElem?_extract (by omega) (by omega) (by omega)]
      simp
    · by_cases c2 : j < 48
      · simp only [c1, c2, ↓reduceIte]
        rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2, hz2]; omega)]
        rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2]; omega)]
        rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1]; omega)]
        rw [byteArray_getElem_append_right (by omega)]
        rw [s1]; simp only [Array.getElem?_replicate]; rw [ite_eq_left (by omega)]
      · by_cases c3 : j < 60
        · simp only [c1, c2, c3, ↓reduceIte]
          rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2, hz2]; omega)]
          rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2]; omega)]
          rw [byteArray_getElem_append_right (by simp only [byteArray_size_append, s1, hz1]; omega)]
          rw [byteArray_size_append, s1, hz1]
          rw [byteArray_getElem?_extract (by omega) (by omega) (by omega)]
          have : 48 + (j - (40 + 8)) = j := by omega
          rw [this]
        · by_cases c4 : j < 64
          · simp only [c1, c2, c3, c4, ↓reduceIte]
            rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, hz1, s2, hz2]; omega)]
            rw [byteArray_getElem_append_right (by simp only [byteArray_size_append, s1, hz1, s2]; omega)]
            simp only [byteArray_size_append, s1, hz1, s2, Array.getElem?_replicate]
            rw [ite_eq_left (by omega)]
          · simp only [c1, c2, c3, c4, ↓reduceIte]
            rw [byteArray_getElem_append_right (by simp only [byteArray_size_append, s1, hz1, s2, hz2]; omega)]
            simp only [byteArray_size_append, s1, hz1, s2, hz2]
            rw [byteArray_getElem?_extract (by omega) (Nat.le_refl _) (by omega)]
            have : 64 + (j - (40 + 8 + 12 + 4)) = j := by omega
            rw [this]
  have hpatch_at (j : Nat) (hj : j < core.size)
      (hkeep : j < 40 ∨ (48 ≤ j ∧ j < 60) ∨ 64 ≤ j) :
      (patchShdr core shoff).data[j]? = core.data[j]? := by
    unfold patchShdr
    rw [ite_eq_right hlt]
    have s1 : (core.extract 0 40).size = 40 := byteArray_extract_size core 0 40 (by omega) (by omega)
    have s2 : (core.extract 48 60).size = 12 := byteArray_extract_size core 48 60 (by omega) (by omega)
    rcases hkeep with c1 | ⟨c2l, c2h⟩ | c3
    · rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, h1, s2, h2]; omega)]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, h1, s2]; omega)]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, h1]; omega)]
      rw [byteArray_getElem_append_left (by omega)]
      rw [byteArray_getElem?_extract (by omega) (by omega) (by omega)]
      simp
    · rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, h1, s2, h2]; omega)]
      rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, s1, h1, s2]; omega)]
      rw [byteArray_getElem_append_right (by simp only [byteArray_size_append, s1, h1]; omega)]
      rw [byteArray_size_append, s1, h1]
      rw [byteArray_getElem?_extract (by omega) (by omega) (by omega)]
      have : 48 + (j - (40 + 8)) = j := by omega
      rw [this]
    · rw [byteArray_getElem_append_right (by simp only [byteArray_size_append, s1, h1, s2, h2]; omega)]
      simp only [byteArray_size_append, s1, h1, s2, h2]
      rw [byteArray_getElem?_extract (by omega) (Nat.le_refl _) (by omega)]
      have : 64 + (j - (40 + 8 + 12 + 4)) = j := by omega
      rw [this]
  rw [heq_region (patchShdr core shoff) (by omega) i (by omega)]
  rw [heq_region core h64 i hiCore]
  by_cases c1 : i < 40
  · simp only [c1, ↓reduceIte]; exact hpatch_at i hiCore (Or.inl c1)
  · by_cases c2 : i < 48
    · simp only [c1, c2, ↓reduceIte]
    · by_cases c3 : i < 60
      · simp only [c1, c2, c3, ↓reduceIte]; exact hpatch_at i hiCore (Or.inr (Or.inl ⟨by omega, c3⟩))
      · by_cases c4 : i < 64
        · simp only [c1, c2, c3, c4, ↓reduceIte]
        · simp only [c1, c2, c3, c4, ↓reduceIte]; exact hpatch_at i hiCore (Or.inr (Or.inr (by omega)))

/-- `attachTrailer` always passes `checkTrailer`. -/
theorem checkTrailer_attachTrailer {core payload img : ByteArray}
    (h : attachTrailer core payload = .ok img) :
    checkTrailer core payload img = true := by
  simp [checkTrailer, h]

/-- `checkTrailer` implies `attachTrailer` produced `img` verbatim. -/
theorem checkTrailer_eq_attachTrailer {core payload img : ByteArray}
    (h : checkTrailer core payload img = true) :
    attachTrailer core payload = .ok img := by
  unfold checkTrailer at h
  cases ha : attachTrailer core payload with
  | error e => simp [ha] at h
  | ok expected =>
    simp only [ha, beq_iff_eq] at h
    subst h
    rfl

private theorem attachTrailer_parts {core payload img : ByteArray}
    (h : attachTrailer core payload = .ok img) :
    64 ≤ core.size ∧
    zeroShdr core = core ∧
    ELFRead.natural core 58 2 = some shdrEntrySize ∧
    core.size < 2 ^ 40 ∧
    payload.size < 2 ^ 32 ∧
    img = attachTrailerRaw core payload := by
  unfold attachTrailer at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      split at h
      · rename_i h3
        split at h
        · rename_i h4
          split at h
          · rename_i h5
            injection h with himg
            exact ⟨h1, eq_of_beq h2, eq_of_beq h3, h4, h5, himg.symm⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Core integrity theorem**: if `checkTrailer core payload img = true`, then
zeroing ONLY the 12 ELF64 shdr bytes of `img[0..core.size)` reproduces `core`
byte-for-byte. -/
theorem checkTrailer_core_eq {core payload img : ByteArray}
    (h : checkTrailer core payload img = true) :
    zeroShdr (img.extract 0 core.size) = core := by
  obtain ⟨h64, hz, _, _, _, rfl⟩ := attachTrailer_parts (checkTrailer_eq_attachTrailer h)
  unfold attachTrailerRaw
  dsimp only
  let shoff := alignUp (alignUp core.size certPageSize + payload.size + shstrtabBytes.size) 8
  let p := patchShdr core shoff
  have hpSz : p.size = core.size := size_patchShdr h64 shoff
  have hassoc :
      p ++ ByteArray.mk (Array.replicate (alignUp core.size certPageSize - core.size) trapByte) ++
        payload ++ shstrtabBytes ++
        ByteArray.mk (Array.replicate (shoff - (alignUp core.size certPageSize + payload.size + shstrtabBytes.size)) 0) ++
        sectionTableBytes (alignUp core.size certPageSize) payload.size (alignUp core.size certPageSize + payload.size) =
      p ++ (ByteArray.mk (Array.replicate (alignUp core.size certPageSize - core.size) trapByte) ++
        payload ++ shstrtabBytes ++
        ByteArray.mk (Array.replicate (shoff - (alignUp core.size certPageSize + payload.size + shstrtabBytes.size)) 0) ++
        sectionTableBytes (alignUp core.size certPageSize) payload.size (alignUp core.size certPageSize + payload.size)) := by
    simp [ByteArray.append_assoc]
  change zeroShdr ((p ++ _ ++ _ ++ _ ++ _ ++ _).extract 0 core.size) = core
  rw [hassoc, ← hpSz, byteArray_extract_append_left]
  exact zeroShdr_patchShdr h64 hz shoff

/-- **RX page-tail anti-smuggling theorem**: if `checkTrailer core payload img = true`,
then EVERY byte in `[core.size .. alignUp core.size 4096)` is strictly `0xCC` (`int3`),
so zero `.ix.cert` bytes can ever be mapped executable by Linux `binfmt_elf`. -/
theorem checkTrailer_sled_int3 {core payload img : ByteArray}
    (h : checkTrailer core payload img = true) :
    ∀ i, core.size ≤ i → i < alignUp core.size certPageSize →
      img.data[i]? = some trapByte := by
  obtain ⟨h64, _, _, _, _, rfl⟩ := attachTrailer_parts (checkTrailer_eq_attachTrailer h)
  intro i hlo hhi
  unfold attachTrailerRaw
  dsimp only
  let pageEnd := alignUp core.size certPageSize
  let shoff := alignUp (pageEnd + payload.size + shstrtabBytes.size) 8
  let p := patchShdr core shoff
  let sled := ByteArray.mk (Array.replicate (pageEnd - core.size) trapByte)
  have hpSz : p.size = core.size := size_patchShdr h64 shoff
  have hsledSz : sled.size = pageEnd - core.size := by rw [byteArray_mk_size, Array.size_replicate]
  change (p ++ sled ++ payload ++ shstrtabBytes ++ _ ++ _).data[i]? = some trapByte
  rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, hpSz, hsledSz]; omega)]
  rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, hpSz, hsledSz]; omega)]
  rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, hpSz, hsledSz]; omega)]
  rw [byteArray_getElem_append_left (by simp only [byteArray_size_append, hpSz, hsledSz]; omega)]
  rw [byteArray_getElem_append_right (by rw [hpSz]; exact hlo)]
  rw [hpSz]
  simp only [sled, Array.getElem?_replicate]
  rw [ite_eq_left (by omega)]

/-- **Page-aligned payload integrity theorem**: if `checkTrailer core payload img = true`,
then `img[pageEnd .. pageEnd + payload.size)` equals `payload` verbatim, and `pageEnd`
is 4096-byte aligned and `≥ core.size`. -/
theorem checkTrailer_payload_eq {core payload img : ByteArray}
    (h : checkTrailer core payload img = true) :
    let pageEnd := alignUp core.size certPageSize
    core.size ≤ pageEnd ∧ pageEnd % certPageSize = 0 ∧
    img.extract pageEnd (pageEnd + payload.size) = payload := by
  obtain ⟨h64, _, _, _, _, rfl⟩ := attachTrailer_parts (checkTrailer_eq_attachTrailer h)
  have hpe_ge : core.size ≤ alignUp core.size certPageSize := by
    simp only [alignUp, certPageSize]; omega
  have hpe_mod : alignUp core.size certPageSize % certPageSize = 0 := by
    simp only [alignUp, certPageSize]; omega
  refine ⟨hpe_ge, hpe_mod, ?_⟩
  unfold attachTrailerRaw
  dsimp only
  let pageEnd := alignUp core.size certPageSize
  let shoff := alignUp (pageEnd + payload.size + shstrtabBytes.size) 8
  let p := patchShdr core shoff
  let sled := ByteArray.mk (Array.replicate (pageEnd - core.size) trapByte)
  have hpSz : p.size = core.size := size_patchShdr h64 shoff
  have hsledSz : sled.size = pageEnd - core.size := by rw [byteArray_mk_size, Array.size_replicate]
  have hprefSz : (p ++ sled).size = pageEnd := by
    rw [byteArray_size_append, hpSz, hsledSz]; omega
  have hassoc :
      p ++ sled ++ payload ++ shstrtabBytes ++
        ByteArray.mk (Array.replicate (shoff - (pageEnd + payload.size + shstrtabBytes.size)) 0) ++
        sectionTableBytes pageEnd payload.size (pageEnd + payload.size) =
      (p ++ sled) ++ payload ++
        (shstrtabBytes ++
          ByteArray.mk (Array.replicate (shoff - (pageEnd + payload.size + shstrtabBytes.size)) 0) ++
          sectionTableBytes pageEnd payload.size (pageEnd + payload.size)) := by
    simp [ByteArray.append_assoc]
  change (p ++ sled ++ payload ++ shstrtabBytes ++ _ ++ _).extract pageEnd (pageEnd + payload.size) = payload
  rw [hassoc, ← hprefSz, byteArray_extract_append_mid]

/-- **Flush-EOF theorem**: if `checkTrailer core payload img = true`, the exact
3-entry ELF64 section header table ends flush at EOF with zero trailing bytes. -/
theorem checkTrailer_flush_eof {core payload img : ByteArray}
    (h : checkTrailer core payload img = true) :
    let pageEnd := alignUp core.size certPageSize
    let shoff := alignUp (pageEnd + payload.size + shstrtabBytes.size) 8
    img.size = shoff + shdrTableSize := by
  obtain ⟨h64, _, _, _, _, rfl⟩ := attachTrailer_parts (checkTrailer_eq_attachTrailer h)
  unfold attachTrailerRaw
  dsimp only
  let pageEnd := alignUp core.size certPageSize
  let shstrEnd := pageEnd + payload.size + shstrtabBytes.size
  let shoff := alignUp shstrEnd 8
  change (patchShdr core shoff ++ _ ++ payload ++ shstrtabBytes ++ _ ++ _).size = shoff + shdrTableSize
  simp only [byteArray_size_append, byteArray_mk_size, Array.size_replicate]
  rw [size_patchShdr h64 shoff, size_sectionTableBytes]
  have hpe_ge : core.size ≤ pageEnd := by simp only [pageEnd, alignUp, certPageSize]; omega
  have hsh_ge : pageEnd + payload.size + shstrtabBytes.size ≤ shoff := by
    simp only [shoff, shstrEnd, alignUp]; omega
  change core.size + (pageEnd - core.size) + payload.size + shstrtabBytes.size +
    (shoff - (pageEnd + payload.size + shstrtabBytes.size)) + shdrTableSize = shoff + shdrTableSize
  omega

end IxCC.X86.Exe.Cert
