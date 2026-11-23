import IxCC.X86.ELFWriteK
import IxCC.X86.Memory

/-!
# DR1 Read-Only `.rodata` Immortal Static Cells

Encodes immortal static cells into an ELF64 `.rodata` section (`SHF_ALLOC`,
non-writable, non-executable, 8-byte aligned) and proves byte-level readback
and read-only mapping invariants:

* Static closed constructor cells (`encodeStaticCtor`, e.g. `binarytrees`),
* Static `ByteArray` and UTF-8 `String` literals (`encodeStaticByteArray`,
  `encodeStaticString`, DR4),
* Static `Array UInt64` / `>= 2^63` `BigNat` limb cells (`encodeStaticLimbArray`,
  matching `bignum-design.md`: `header(scan=0, cls=0, tag, rc=INT32_MIN) | size | cap | limbs`),
* Static boxed `Array` cells (`encodeStaticBoxedArray`).

Every static cell carries `rc = 0x80000000` (`INT32_MIN`, negative as signed
32-bit `i32`) and `cls = 0`, so `Rt.Rc.Procs.inc`, `Rt.Rc.Gen.dec`,
`Rt.Rc.Gen.isUnique`, and `Rt.Rc.Array.arrDec` all treat static addresses as
immortal read-only values without ever writing to `.rodata`.
-/

namespace IxCC.X86.ELFRodata

open IxCC.X86
open IxCC.X86.ELF

/-- Immortal RC sentinel (`INT32_MIN`), matching `Rt.immortalRc`. -/
def immortalRc : Nat := 0x80000000

/-- Object-kind tags above `Rt.maxTag = 0x7EFF`. -/
def tagBoxedArray : Nat := 0x7F01
def tagByteArray : Nat := 0x7F02
def tagLimbArray : Nat := 0x7F03

/-- Header `scan` sentinel for boxed arrays whose element count lives in `+8`. -/
def scanBoxedArray : Nat := 0xFF

/-- Immortal 64-bit cell header: `scan:u8 | cls=0:u8 | tag:u16 | rc=INT32_MIN:i32`. -/
def staticHeader (scan tag : Nat) : Word :=
  UInt64.ofNat (scan + 65536 * tag + 2 ^ 32 * immortalRc)

/-! ## Header bitfield proofs -/

theorem staticHeader_toNat {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    (staticHeader scan tag).toNat = scan + 65536 * tag + 2 ^ 32 * immortalRc := by
  unfold staticHeader immortalRc
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

theorem staticHeader_scan {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    ((staticHeader scan tag) &&& 0xFF).toNat = scan := by
  rw [UInt64.toNat_and, staticHeader_toNat hs ht]
  rw [show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold immortalRc
  omega

theorem staticHeader_cls {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    (((staticHeader scan tag) >>> 8) &&& 0xFF).toNat = 0 := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, staticHeader_toNat hs ht]
  rw [show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  unfold immortalRc
  simp
  omega

theorem staticHeader_tag {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    (((staticHeader scan tag) >>> 16) &&& 0xFFFF).toNat = tag := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, staticHeader_toNat hs ht]
  rw [show (UInt64.toNat 0xFFFF) = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  unfold immortalRc
  simp
  omega

theorem staticHeader_rc {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    ((staticHeader scan tag) >>> 32).toNat = immortalRc := by
  rw [UInt64.toNat_shiftRight, staticHeader_toNat hs ht, Nat.shiftRight_eq_div_pow]
  unfold immortalRc
  simp
  omega

/-- The high 32-bit RC word of any static header is strictly negative as signed
`i32` (`INT32_MIN = -2^31 < 0`), so RC `inc`/`dec` treat static cells as no-ops
and `isUnique` returns `0`. -/
theorem staticHeader_rc_signed_neg {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    Width.signedValue .w32 ((staticHeader scan tag) >>> 32) < 0 := by
  have hrc : ((staticHeader scan tag) >>> 32).toNat = immortalRc := staticHeader_rc hs ht
  unfold Width.signedValue Width.truncate Width.mask Width.bits
  have htrunc : ((((staticHeader scan tag) >>> 32) &&& 0xffffffff).toNat) = immortalRc := by
    rw [UInt64.toNat_and, hrc]
    rw [show (UInt64.toNat 0xffffffff) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    unfold immortalRc
    omega
  rw [htrunc]
  unfold immortalRc
  decide

theorem staticHeader_rc_nonzero {scan tag : Nat} (hs : scan < 256) (ht : tag < 65536) :
    ((staticHeader scan tag) >>> 32) ≠ 0 := by
  intro h
  have hrc := staticHeader_rc hs ht
  rw [h] at hrc
  simp [immortalRc] at hrc

/-! ## Word-list serialization -/

/-- Little-endian concatenation of 64-bit words. -/
def encodeWords : List Word → ByteArray
  | [] => ByteArray.empty
  | w :: ws => word64 w ++ encodeWords ws

theorem encodeWords_size (ws : List Word) : (encodeWords ws).size = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [encodeWords, ByteArray.size_append, ih, List.length_cons]
      have hw : (word64 w).size = 8 := by rfl
      omega

theorem word64_size (w : Word) : (word64 w).size = 8 := rfl

theorem word64_getElem (w : Word) {j : Nat} (hj : j < 8) :
    (word64 w)[j]'(by rw [word64_size]; exact hj) = (w >>> UInt64.ofNat (8 * j)).toUInt8 := by
  have h8 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply UInt8.toNat_inj.mp
    simp [word64, Encode.littleEndian, Encode.bytes, Encode.le, Encode.leNat,
      UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      show ∀ (l : List UInt8) (k : Nat) (hk : k < ({ data := l.toArray } : ByteArray).size),
        ({ data := l.toArray } : ByteArray)[k]'hk = l[k]'(by simpa [ByteArray.size] using hk) from
        fun _ _ _ => rfl]

theorem encodeWords_getElem (ws : List Word) {idx j : Nat} (hi : idx < ws.length) (hj : j < 8) :
    (encodeWords ws)[8 * idx + j]'(by rw [encodeWords_size]; omega) =
      (ws[idx] >>> UInt64.ofNat (8 * j)).toUInt8 := by
  induction ws generalizing idx with
  | nil => simp at hi
  | cons w ws ih =>
      cases idx with
      | zero =>
          simp only [encodeWords, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
          rw [ByteArray.getElem_append_left (by rw [word64_size]; exact hj)]
          exact word64_getElem w hj
      | succ idx =>
          simp only [encodeWords, List.getElem_cons_succ]
          have hsz : (word64 w).size = 8 := word64_size w
          rw [ByteArray.getElem_append_right (by omega)]
          have hsub : 8 * (idx + 1) + j - (word64 w).size = 8 * idx + j := by omega
          simp only [hsub]
          exact ih (by simpa using hi)

/-! ## Immortal static cell encoders -/

/-- Static closed constructor cell: `header(scan=fields.length, cls=0, tag, INT32_MIN) | fields`. -/
def encodeStaticCtor (tag : Nat) (fields : List Word) : ByteArray :=
  encodeWords (staticHeader fields.length tag :: fields)

/-- Static `ByteArray` / UTF-8 `String` cell:
`header(scan=0, cls=0, tagByteArray, INT32_MIN) | size | cap | padded bytes`. -/
def encodeStaticByteArray (data : ByteArray) : ByteArray :=
  let cap := alignUp data.size 8
  encodeWords [staticHeader 0 tagByteArray, UInt64.ofNat data.size, UInt64.ofNat cap] ++
    padTo data cap

/-- Static UTF-8 `String` literal cell (DR4). -/
def encodeStaticString (s : String) : ByteArray :=
  encodeStaticByteArray s.toUTF8

/-- Static `Array UInt64` / `BigNat` limb cell (`bignum-design.md`):
`header(scan=0, cls=0, tagLimbArray, INT32_MIN) | size | cap | limbs`. -/
def encodeStaticLimbArray (limbs : List Word) : ByteArray :=
  encodeWords (staticHeader 0 tagLimbArray :: UInt64.ofNat limbs.length :: UInt64.ofNat limbs.length :: limbs)

/-- Static boxed `Array` cell:
`header(scan=0xFF, cls=0, tagBoxedArray, INT32_MIN) | size | cap | elems`. -/
def encodeStaticBoxedArray (elems : List Word) : ByteArray :=
  encodeWords (staticHeader scanBoxedArray tagBoxedArray :: UInt64.ofNat elems.length :: UInt64.ofNat elems.length :: elems)

theorem alignUp8_mod (n : Nat) : alignUp n 8 % 8 = 0 := by
  unfold alignUp
  simp only [show (8 == 0) = false from rfl, Bool.false_eq_true, ite_false]
  omega

theorem alignUp8_ge (n : Nat) : n ≤ alignUp n 8 := by
  unfold alignUp
  simp only [show (8 == 0) = false from rfl, Bool.false_eq_true, ite_false]
  omega

theorem zeros_size (n : Nat) : (zeros n).size = n := by
  change (Array.replicate n (0 : UInt8)).size = n
  exact Array.size_replicate

theorem padTo_size (b : ByteArray) (n : Nat) (h : b.size ≤ n) : (padTo b n).size = n := by
  simp only [padTo, ByteArray.size_append, zeros_size]
  omega

theorem encodeStaticCtor_size (tag : Nat) (fields : List Word) :
    (encodeStaticCtor tag fields).size = 8 * (1 + fields.length) := by
  simp [encodeStaticCtor, encodeWords_size, Nat.add_comm]

theorem encodeStaticByteArray_size (data : ByteArray) :
    (encodeStaticByteArray data).size = 24 + alignUp data.size 8 := by
  simp only [encodeStaticByteArray, ByteArray.size_append, encodeWords_size, List.length_cons,
    List.length_nil]
  rw [padTo_size data (alignUp data.size 8) (alignUp8_ge data.size)]

theorem encodeStaticByteArray_aligned (data : ByteArray) :
    (encodeStaticByteArray data).size % 8 = 0 := by
  rw [encodeStaticByteArray_size]
  have := alignUp8_mod data.size
  omega

theorem encodeStaticLimbArray_size (limbs : List Word) :
    (encodeStaticLimbArray limbs).size = 24 + 8 * limbs.length := by
  simp only [encodeStaticLimbArray, encodeWords_size, List.length_cons]
  omega

theorem encodeStaticBoxedArray_size (elems : List Word) :
    (encodeStaticBoxedArray elems).size = 24 + 8 * elems.length := by
  simp only [encodeStaticBoxedArray, encodeWords_size, List.length_cons]
  omega

/-! ## `.rodata` section table builder -/

/-- Incremental builder assembling multiple 8-byte-aligned immortal static cells
into one `.rodata` section with named `RodataSymbol` exports. -/
structure RodataTable where
  bytes : ByteArray := ByteArray.empty
  symbols : List RodataSymbol := []

namespace RodataTable

def empty : RodataTable := {}

/-- Append one cell at an 8-byte-aligned offset and record its symbol. -/
def addCell (t : RodataTable) (name : String) (cell : ByteArray) : RodataTable × Nat :=
  let off := alignUp t.bytes.size 8
  let padded := padTo t.bytes off
  let bytes' := padded ++ cell
  let sym : RodataSymbol := { name, offset := off, size := cell.size }
  ({ bytes := bytes', symbols := t.symbols ++ [sym] }, off)

def addCtor (t : RodataTable) (name : String) (tag : Nat) (fields : List Word) : RodataTable × Nat :=
  t.addCell name (encodeStaticCtor tag fields)

def addByteArray (t : RodataTable) (name : String) (data : ByteArray) : RodataTable × Nat :=
  t.addCell name (encodeStaticByteArray data)

def addString (t : RodataTable) (name : String) (s : String) : RodataTable × Nat :=
  t.addCell name (encodeStaticString s)

def addLimbArray (t : RodataTable) (name : String) (limbs : List Word) : RodataTable × Nat :=
  t.addCell name (encodeStaticLimbArray limbs)

def addBoxedArray (t : RodataTable) (name : String) (elems : List Word) : RodataTable × Nat :=
  t.addCell name (encodeStaticBoxedArray elems)

/-- Every cell appended by `addCell` is placed at an 8-byte-aligned offset and
its bytes are preserved verbatim in the resulting `.rodata` buffer. -/
theorem addCell_aligned (t : RodataTable) (name : String) (cell : ByteArray) :
    (t.addCell name cell).2 % 8 = 0 :=
  alignUp8_mod t.bytes.size

theorem addCell_bounds (t : RodataTable) (name : String) (cell : ByteArray) :
    (t.addCell name cell).2 + cell.size ≤ (t.addCell name cell).1.bytes.size := by
  simp only [addCell, ByteArray.size_append]
  rw [padTo_size t.bytes (alignUp t.bytes.size 8) (alignUp8_ge t.bytes.size)]
  exact Nat.le_refl _

theorem addCell_bytes_eq (t : RodataTable) (name : String) (cell : ByteArray)
    {i : Nat} (hi : i < cell.size) :
    (t.addCell name cell).1.bytes[(t.addCell name cell).2 + i]'(by
      have := addCell_bounds t name cell; omega) = cell[i] := by
  simp only [addCell]
  have hpad : (padTo t.bytes (alignUp t.bytes.size 8)).size = alignUp t.bytes.size 8 :=
    padTo_size t.bytes _ (alignUp8_ge t.bytes.size)
  rw [ByteArray.getElem_append_right (by omega)]
  simp [hpad]

/-- Appending a subsequent cell never modifies any byte already placed in `t.bytes`. -/
theorem addCell_preserves_prefix (t : RodataTable) (name : String) (cell : ByteArray)
    {i : Nat} (hi : i < t.bytes.size) :
    (t.addCell name cell).1.bytes[i]'(by
      have h1 := alignUp8_ge t.bytes.size
      have h2 := addCell_bounds t name cell
      simp only [addCell] at h2 ⊢
      omega) = t.bytes[i] := by
  simp only [addCell]
  have hpad : (padTo t.bytes (alignUp t.bytes.size 8)).size = alignUp t.bytes.size 8 :=
    padTo_size t.bytes _ (alignUp8_ge t.bytes.size)
  have h1 := alignUp8_ge t.bytes.size
  rw [ByteArray.getElem_append_left (by omega)]
  unfold padTo
  rw [ByteArray.getElem_append_left hi]

end RodataTable

/-! ## Read-only `.rodata` memory mapping and byte-level readback proofs -/

/-- Whether address `a` lies inside `[rodataBase, rodataBase + size)`. -/
def inRodata (rodataBase : Word) (size : Nat) (a : Word) : Bool :=
  decide (rodataBase.toNat ≤ a.toNat) && decide (a.toNat < rodataBase.toNat + size)

/-- Map `rodata` into `mem` at `rodataBase` as strictly read-only memory
(`readable = true`, `writable = false`). Bytes and permissions outside
`[rodataBase, rodataBase + rodata.size)` are inherited from `mem`. -/
def mapRodata (mem : Memory) (rodataBase : Word) (rodata : ByteArray) : Memory where
  bytes a :=
    if h : rodataBase.toNat ≤ a.toNat ∧ a.toNat < rodataBase.toNat + rodata.size then
      rodata[a.toNat - rodataBase.toNat]'(by omega)
    else mem.bytes a
  readable a := mem.readable a || inRodata rodataBase rodata.size a
  writable a := mem.writable a && !inRodata rodataBase rodata.size a

/-- Predicate asserting that `rodata` is loaded read-only at 8-byte-aligned
canonical address `rodataBase` inside `mem`. -/
structure RodataMapped (rodataBase : Word) (rodata : ByteArray) (mem : Memory) : Prop where
  nonzero : rodataBase ≠ 0
  aligned : rodataBase.toNat % 8 = 0
  fit : rodataBase.toNat + rodata.size < 2 ^ 63
  bytes_eq : ∀ i (hi : i < rodata.size), mem.bytes (rodataBase + UInt64.ofNat i) = rodata[i]
  readable : ∀ i (_ : i < rodata.size), mem.readable (rodataBase + UInt64.ofNat i) = true
  readonly : ∀ i (_ : i < rodata.size), mem.writable (rodataBase + UInt64.ofNat i) = false

theorem rodataAddr_toNat {rodataBase : Word} {size i : Nat}
    (hfit : rodataBase.toNat + size < 2 ^ 63) (hi : i < size) :
    (rodataBase + UInt64.ofNat i).toNat = rodataBase.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  have hi2 : i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hi2, Nat.mod_eq_of_lt (by omega)]

theorem mapRodata_mapped (mem : Memory) {rodataBase : Word} {rodata : ByteArray}
    (h0 : rodataBase ≠ 0) (hal : rodataBase.toNat % 8 = 0)
    (hfit : rodataBase.toNat + rodata.size < 2 ^ 63) :
    RodataMapped rodataBase rodata (mapRodata mem rodataBase rodata) where
  nonzero := h0
  aligned := hal
  fit := hfit
  bytes_eq i hi := by
    have hto := rodataAddr_toNat hfit hi
    simp only [mapRodata, hto]
    rw [dite_eq_left (by omega)]
    simp [Nat.add_sub_cancel_left]
  readable i hi := by
    have hto := rodataAddr_toNat hfit hi
    simp [mapRodata, inRodata, hto, hi]
  readonly i hi := by
    have hto := rodataAddr_toNat hfit hi
    simp [mapRodata, inRodata, hto, hi]

theorem mapRodata_outside (mem : Memory) (rodataBase : Word) (rodata : ByteArray) (a : Word)
    (hout : inRodata rodataBase rodata.size a = false) :
    (mapRodata mem rodataBase rodata).bytes a = mem.bytes a ∧
      (mapRodata mem rodataBase rodata).readable a = mem.readable a ∧
      (mapRodata mem rodataBase rodata).writable a = mem.writable a := by
  have hnot : ¬ (rodataBase.toNat ≤ a.toNat ∧ a.toNat < rodataBase.toNat + rodata.size) := by
    simp only [inRodata, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hout
    omega
  simp [mapRodata, hnot, hout]

/-- Reading a 64-bit word from a mapped `.rodata` buffer at offset `off`
recovers the exact little-endian word stored there. -/
theorem RodataMapped.read64_word {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} {w : Word}
    (hbound : off + 8 ≤ rodata.size)
    (hbytes : ∀ j (hj : j < 8), rodata[off + j]'(by omega) = (w >>> UInt64.ofNat (8 * j)).toUInt8) :
    mem.read64? (rodataBase + UInt64.ofNat off) = .ok w := by
  have haddr : ∀ j < 8, (rodataBase + UInt64.ofNat off) + UInt64.ofNat j =
      rodataBase + UInt64.ofNat (off + j) := by
    intro j hj
    rw [UInt64.add_assoc, UInt64.ofNat_add]
  have hread : Memory.rangeAllowed mem.readable (rodataBase + UInt64.ofNat off) 8 = true := by
    apply Memory.rangeAllowed_of_forall
    intro j hj
    rw [haddr j hj]
    exact hm.readable (off + j) (by omega)
  simp only [Memory.read64?, Memory.read?, Width.bytes, hread, ite_true, Memory.read, Except.ok.injEq]
  have hstep : ∀ j (hj : j < 8),
      mem.bytes ((rodataBase + UInt64.ofNat off) + UInt64.ofNat j) =
        (w >>> UInt64.ofNat (8 * j)).toUInt8 := by
    intro j hj
    rw [haddr j hj, hm.bytes_eq (off + j) (by omega), hbytes j hj]
  simp only [Memory.readLittle, hstep 0 (by omega), hstep 1 (by omega), hstep 2 (by omega),
    hstep 3 (by omega), hstep 4 (by omega), hstep 5 (by omega), hstep 6 (by omega), hstep 7 (by omega)]
  simpa using Memory.pack64 w

/-- Reading a single byte from a mapped `.rodata` buffer at offset `off`. -/
theorem RodataMapped.read8_byte {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} (hoff : off < rodata.size) :
    mem.read? .w8 (rodataBase + UInt64.ofNat off) = .ok (rodata[off].toUInt64) := by
  have hz : UInt64.ofNat 0 = (0 : Word) := rfl
  have hread : Memory.rangeAllowed mem.readable (rodataBase + UInt64.ofNat off) 1 = true := by
    simp only [Memory.rangeAllowed, Bool.true_and, hz, UInt64.add_zero]
    exact hm.readable off hoff
  simp only [Memory.read?, Width.bytes, hread, ite_true, Memory.read, Memory.readLittle,
    hz, UInt64.add_zero, Nat.mul_zero, UInt64.shiftLeft_zero, UInt64.zero_or]
  rw [hm.bytes_eq off hoff]

/-- Any sequence of encoded words placed at `off` inside a mapped `.rodata`
buffer reads back word-for-word via `mem.read64?`. -/
theorem RodataMapped.read64_encodedWord {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} {ws : List Word}
    (hfit : off + (encodeWords ws).size ≤ rodata.size)
    (hslice : ∀ k (hk : k < (encodeWords ws).size),
      rodata[off + k]'(by omega) = (encodeWords ws)[k]'hk)
    {idx : Nat} (hi : idx < ws.length) :
    mem.read64? (rodataBase + UInt64.ofNat (off + 8 * idx)) = .ok (ws[idx]'hi) := by
  have hsz := encodeWords_size ws
  apply hm.read64_word (by omega)
  intro j hj
  have h1 := hslice (8 * idx + j) (by omega)
  have h2 := encodeWords_getElem ws hi hj
  have hidx : off + 8 * idx + j = off + (8 * idx + j) := by omega
  have hget : rodata[off + 8 * idx + j]'(by omega) = rodata[off + (8 * idx + j)]'(by omega) := by
    congr 1
  exact hget.trans (h1.trans h2)

/-- A static `ByteArray` cell placed at `off` inside mapped `.rodata` reads back
its exact header, size, capacity, and every data byte. -/
theorem RodataMapped.staticByteArray_reads {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} {data : ByteArray}
    (hfit : off + (encodeStaticByteArray data).size ≤ rodata.size)
    (hslice : ∀ k (hk : k < (encodeStaticByteArray data).size),
      rodata[off + k]'(by omega) = (encodeStaticByteArray data)[k]'hk) :
    mem.read64? (rodataBase + UInt64.ofNat off) = .ok (staticHeader 0 tagByteArray) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 8)) = .ok (UInt64.ofNat data.size) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 16)) = .ok (UInt64.ofNat (alignUp data.size 8)) ∧
    ∀ j (hj : j < data.size),
      mem.read? .w8 (rodataBase + UInt64.ofNat (off + 24 + j)) = .ok (data[j].toUInt64) := by
  let hdrWords : List Word := [staticHeader 0 tagByteArray, UInt64.ofNat data.size, UInt64.ofNat (alignUp data.size 8)]
  have hhdrSize : (encodeWords hdrWords).size = 24 := by
    simp [hdrWords, encodeWords_size]
  have htot : (encodeStaticByteArray data).size = 24 + alignUp data.size 8 := encodeStaticByteArray_size data
  have hhdrSlice : ∀ k (hk : k < (encodeWords hdrWords).size),
      rodata[off + k]'(by omega) = (encodeWords hdrWords)[k]'hk := by
    intro k hk
    have h1 := hslice k (by omega)
    rw [h1]
    simp only [encodeStaticByteArray, hdrWords]
    rw [ByteArray.getElem_append_left (by simpa [hdrWords] using hk)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hm.read64_encodedWord (ws := hdrWords) (by omega) hhdrSlice (idx := 0) (by simp [hdrWords])
    simpa [hdrWords] using h
  · have h := hm.read64_encodedWord (ws := hdrWords) (by omega) hhdrSlice (idx := 1) (by simp [hdrWords])
    simpa [hdrWords] using h
  · have h := hm.read64_encodedWord (ws := hdrWords) (by omega) hhdrSlice (idx := 2) (by simp [hdrWords])
    simpa [hdrWords] using h
  · intro j hj
    have hge := alignUp8_ge data.size
    have hb := hm.read8_byte (off := off + 24 + j) (by omega)
    have h1 := hslice (24 + j) (by omega)
    have heq : off + 24 + j = off + (24 + j) := by omega
    rw [hb, show rodata[off + 24 + j]'(by omega) = data[j]'hj from by
      have h1' : rodata[off + 24 + j]'(by omega) = (encodeStaticByteArray data)[24 + j]'(by omega) := by
        simpa [heq] using h1
      rw [h1']
      simp only [encodeStaticByteArray]
      rw [ByteArray.getElem_append_right (by rw [show (encodeWords hdrWords).size = 24 from hhdrSize]; omega)]
      have hsub : 24 + j - (encodeWords hdrWords).size = j := by omega
      simp only [show 24 + j - (encodeWords [staticHeader 0 tagByteArray, UInt64.ofNat data.size,
        UInt64.ofNat (alignUp data.size 8)]).size = j from hsub]
      unfold padTo
      rw [ByteArray.getElem_append_left hj]]

/-- A static `LimbArray` / `BigNat` cell placed at `off` inside mapped `.rodata`
reads back its exact header, size, capacity, and every 64-bit limb. -/
theorem RodataMapped.staticLimbArray_reads {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} {limbs : List Word}
    (hfit : off + (encodeStaticLimbArray limbs).size ≤ rodata.size)
    (hslice : ∀ k (hk : k < (encodeStaticLimbArray limbs).size),
      rodata[off + k]'(by omega) = (encodeStaticLimbArray limbs)[k]'hk) :
    mem.read64? (rodataBase + UInt64.ofNat off) = .ok (staticHeader 0 tagLimbArray) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 8)) = .ok (UInt64.ofNat limbs.length) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 16)) = .ok (UInt64.ofNat limbs.length) ∧
    ∀ j (hj : j < limbs.length),
      mem.read64? (rodataBase + UInt64.ofNat (off + 24 + 8 * j)) = .ok (limbs[j]'hj) := by
  let ws := staticHeader 0 tagLimbArray :: UInt64.ofNat limbs.length :: UInt64.ofNat limbs.length :: limbs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 0) (by simp [ws])
    simpa [ws] using h
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 1) (by simp [ws])
    simpa [ws] using h
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 2) (by simp [ws])
    simpa [ws] using h
  · intro j hj
    have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := j + 3) (by simp [ws]; omega)
    have hidx : off + 8 * (j + 3) = off + 24 + 8 * j := by omega
    rw [hidx] at h
    simpa [ws] using h

/-- A static closed constructor cell placed at `off` inside mapped `.rodata`
reads back its exact immortal header and every field word. -/
theorem RodataMapped.staticCtor_reads {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off tag : Nat} {fields : List Word}
    (hfit : off + (encodeStaticCtor tag fields).size ≤ rodata.size)
    (hslice : ∀ k (hk : k < (encodeStaticCtor tag fields).size),
      rodata[off + k]'(by omega) = (encodeStaticCtor tag fields)[k]'hk) :
    mem.read64? (rodataBase + UInt64.ofNat off) = .ok (staticHeader fields.length tag) ∧
    ∀ j (hj : j < fields.length),
      mem.read64? (rodataBase + UInt64.ofNat (off + 8 + 8 * j)) = .ok (fields[j]'hj) := by
  let ws := staticHeader fields.length tag :: fields
  refine ⟨?_, ?_⟩
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 0) (by simp [ws])
    simpa [ws] using h
  · intro j hj
    have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := j + 1) (by simp [ws]; omega)
    have hidx : off + 8 * (j + 1) = off + 8 + 8 * j := by omega
    rw [hidx] at h
    simpa [ws] using h

/-- A static boxed `Array` cell placed at `off` inside mapped `.rodata` reads
back its exact immortal header (`scan = 0xFF`, `tag = 0x7F01`), size, capacity,
and every element word. -/
theorem RodataMapped.staticBoxedArray_reads {rodataBase : Word} {rodata : ByteArray} {mem : Memory}
    (hm : RodataMapped rodataBase rodata mem) {off : Nat} {elems : List Word}
    (hfit : off + (encodeStaticBoxedArray elems).size ≤ rodata.size)
    (hslice : ∀ k (hk : k < (encodeStaticBoxedArray elems).size),
      rodata[off + k]'(by omega) = (encodeStaticBoxedArray elems)[k]'hk) :
    mem.read64? (rodataBase + UInt64.ofNat off) = .ok (staticHeader scanBoxedArray tagBoxedArray) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 8)) = .ok (UInt64.ofNat elems.length) ∧
    mem.read64? (rodataBase + UInt64.ofNat (off + 16)) = .ok (UInt64.ofNat elems.length) ∧
    ∀ j (hj : j < elems.length),
      mem.read64? (rodataBase + UInt64.ofNat (off + 24 + 8 * j)) = .ok (elems[j]'hj) := by
  let ws := staticHeader scanBoxedArray tagBoxedArray :: UInt64.ofNat elems.length :: UInt64.ofNat elems.length :: elems
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 0) (by simp [ws])
    simpa [ws] using h
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 1) (by simp [ws])
    simpa [ws] using h
  · have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := 2) (by simp [ws])
    simpa [ws] using h
  · intro j hj
    have h := hm.read64_encodedWord (ws := ws) hfit hslice (idx := j + 3) (by simp [ws]; omega)
    have hidx : off + 8 * (j + 3) = off + 24 + 8 * j := by omega
    rw [hidx] at h
    simpa [ws] using h

end IxCC.X86.ELFRodata
