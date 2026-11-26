import IxCC.Rt.Rc.Array.Kind
import IxCC.Rt.Rc.Array.Proof.Frame
import IxCC.Lir.Proof.Opt.Mem

/-! # The array cell invariant, for every element kind

`ArrCell mem addr refs cls cap k xs`: at `addr` lives a dynamic array cell of size class `cls`,
with `refs` references, capacity `cap`, element kind `k` and elements `xs`, each a value of `k`'s
width (`ElemKind.Fits`). It is `Invariant.LiveArrayCell` with the kind a width: `ArrShell` is the
cell's header, size and capacity words and its bytes' permissions, `Elems` its elements
(`ValAt`: the little-endian bytes of a value of any width). `StaticArrCell` is the immortal
(`.rodata`) cell. The side path's cells are cells of their kind (`LiveArrayCell.toArrCell`,
`StaticArrayCell.toStatic`).

Every fact here is about memory: a cell's header, words and elements as bytes. Which abstract
value the elements denote is the business of the bridge to the abstract heap, which is not here.

The lemmas: the loads a procedure makes (`ArrShell.count_load`, `scan_load`, `class_load`,
`size_load`, `cap_load`, `ArrCell.elem_load`), the cell kept across a frame
(`MemFrame.arrShell`, `MemFrame.arrCell`), and the cell after each in-place mutation: an element
stored (`ArrCell.setElem`), one appended (`ArrCell.pushElem`), the size lowered
(`ArrCell.truncate`), the count word stored (`ArrShell.withCount`). -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open IxCC.Lir (Word loadWord Cond)
open IxCC.Rt.Proof (WordAt addr_toNat write?_ok read?_ok wordAt_write64 writeLittle_bytes_out
  byte_of_shift)
open IxCC.Rt.Rc (maxClass classBytes classWords maxCount)
open IxCC.Rt.Rc.Procs (storeCount countAddress storeCount_frame storeCount_bytes storeCount_word)
open IxCC.X86 (Memory Width)

/-! ## A value of any width -/

/-- The `w.bytes` little-endian bytes at `a` are `v`'s, and readable. -/
structure ValAt (m : Memory) (a : Word) (w : Width) (v : Word) : Prop where
  bytes : ∀ i < w.bytes, m.bytes (a + UInt64.ofNat i) = (v >>> UInt64.ofNat (8 * i)).toUInt8
  readable : ∀ i < w.bytes, m.readable (a + UInt64.ofNat i) = true

theorem truncate_of_lt {w : Width} {v : Word} (h : v.toNat < 2 ^ w.bits) : w.truncate v = v :=
  UInt64.toNat_inj.mp (by rw [X86.Encode.truncate_nat]; exact Nat.mod_eq_of_lt h)

theorem ValAt.read {m : Memory} {a : Word} {w : Width} {v : Word} (h : ValAt m a w v) :
    m.read? w a = .ok (w.truncate v) := by
  rw [read?_ok h.readable]
  congr 1
  have hle := Lir.Opt.width_bytes_le_8 w
  have : m.read w a = (m.write w a v).read w a := by
    simp only [Memory.read, Memory.write]
    apply X86.Memory.readLittle_congr
    intro i hi
    rw [h.bytes i hi, X86.Memory.writeLittle_bytes m a v hle hi]
  rw [this, Lir.Opt.read_write_same]

theorem ValAt.load {m : Memory} {a : Word} {w : Width} {v : Word} (h : ValAt m a w v)
    (hv : v.toNat < 2 ^ w.bits) : loadWord m w .zero a = some v := by
  simp [loadWord, h.read, truncate_of_lt hv]

theorem valAt_write {m : Memory} {a v : Word} {w : Width}
    (hr : ∀ i < w.bytes, m.readable (a + UInt64.ofNat i) = true) :
    ValAt (m.write w a v) a w v where
  bytes i hi := X86.Memory.writeLittle_bytes m a v (Lir.Opt.width_bytes_le_8 w) hi
  readable i hi := by simpa [Memory.write] using hr i hi

theorem ValAt.of_wordAt {m : Memory} {a v : Word} (h : WordAt m a v) : ValAt m a .w64 v :=
  ⟨fun i hi => h.bytes i hi, fun i hi => h.readable i hi⟩

theorem ValAt.toWordAt {m : Memory} {a v : Word} (h : ValAt m a .w64 v) : WordAt m a v :=
  ⟨fun i hi => h.bytes i hi, fun i hi => h.readable i hi⟩

theorem ValAt.of_byteAt {m : Memory} {a : Word} {b : UInt8} (h : ByteAt m a b) :
    ValAt m a .w8 b.toUInt64 where
  bytes i hi := by
    have hi0 : i = 0 := by simp [Width.bytes] at hi; omega
    subst hi0
    simp [h.byte]
  readable i hi := by
    have hi0 : i = 0 := by simp [Width.bytes] at hi; omega
    subst hi0
    simpa using h.readable

theorem ValAt.toByteAt {m : Memory} {a v : Word} (h : ValAt m a .w8 v) :
    ByteAt m a v.toUInt8 := by
  have hb := h.bytes 0 (by decide)
  have hr := h.readable 0 (by decide)
  simp at hb hr
  exact ⟨hb, hr⟩

namespace MemFrame

/-- A value whose bytes are untouched. -/
theorem valAt {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {b v : Word} {w : Width}
    (hv : ValAt m b w v) (hb : b.toNat + w.bytes ≤ 2 ^ 64)
    (hout : ∀ k, b.toNat ≤ k → k < b.toNat + w.bytes → ¬ t k) : ValAt m' b w v where
  bytes i hi := by
    have hi' : (b + UInt64.ofNat i).toNat = b.toNat + i := addr_toNat (by omega)
    rw [h.bytes _ (hout _ (by rw [hi']; omega) (by rw [hi']; omega))]
    exact hv.bytes i hi
  readable i hi := by rw [h.readable]; exact hv.readable i hi

end MemFrame

theorem ValAt.write_disjoint {m : Memory} {b a u v : Word} {w w' : Width} (h : ValAt m b w v)
    (ha : a.toNat + w'.bytes ≤ 2 ^ 64) (hb : b.toNat + w.bytes ≤ 2 ^ 64)
    (hd : b.toNat + w.bytes ≤ a.toNat ∨ a.toNat + w'.bytes ≤ b.toNat) :
    ValAt (m.write w' a u) b w v :=
  (MemFrame.write m w' a u ha).valAt h hb (fun k h1 h2 hk => by unfold Span at hk; omega)

/-! ## Cells -/

/-- The address of element `j`. -/
def elemAddr (addr : Word) (k : ElemKind) (j : Nat) : Word :=
  addr + UInt64.ofNat (arrayPayloadOffset + k.bytes * j)

/-- The elements `xs`, at their addresses. -/
def Elems (mem : Memory) (addr : Word) (k : ElemKind) (xs : List Word) : Prop :=
  ∀ (j : Nat) (hj : j < xs.length), ValAt mem (elemAddr addr k j) k.width xs[j]

/-- Every element is a value of the kind's width. -/
def ElemsFit (k : ElemKind) (xs : List Word) : Prop := ∀ x ∈ xs, k.Fits x

/-- A dynamic array cell's header, size and capacity words, and its permissions; `size` is the
value of its size word. -/
structure ArrShell (mem : Memory) (addr : Word) (refs cls cap : Nat) (k : ElemKind) (size : Nat) :
    Prop where
  aligned : addr.toNat % 8 = 0
  nonzero : addr ≠ 0
  cls_lo : minArrayClass ≤ cls
  cls_hi : cls ≤ maxClass
  refs_pos : 0 < refs
  refs_le : refs ≤ maxCount
  fit : addr.toNat + classBytes cls < 2 ^ 63
  size_le : size ≤ cap
  cap_fit : cap ≤ k.capOfClass cls
  access : ∀ j < classBytes cls,
    mem.readable (addr + UInt64.ofNat j) = true ∧ mem.writable (addr + UInt64.ofNat j) = true
  header_word : WordAt mem addr (k.header cls refs)
  size_word : WordAt mem (addr + 8) (UInt64.ofNat size)
  cap_word : WordAt mem (addr + 16) (UInt64.ofNat cap)

/-- A live dynamic array cell with elements `xs`. -/
structure ArrCell (mem : Memory) (addr : Word) (refs cls cap : Nat) (k : ElemKind) (xs : List Word) :
    Prop where
  shell : ArrShell mem addr refs cls cap k xs.length
  elems : Elems mem addr k xs
  fits : ElemsFit k xs

/-- An immortal (`.rodata`) array cell: read-only, never counted, never released. -/
structure StaticArrCell (mem : Memory) (addr : Word) (cap : Nat) (k : ElemKind) (xs : List Word) :
    Prop where
  aligned : addr.toNat % 8 = 0
  nonzero : addr ≠ 0
  size_le : xs.length ≤ cap
  fit : addr.toNat + (arrayPayloadOffset + k.bytes * cap) < 2 ^ 63
  header_word : WordAt mem addr k.staticHeader
  size_word : WordAt mem (addr + 8) (UInt64.ofNat xs.length)
  cap_word : WordAt mem (addr + 16) (UInt64.ofNat cap)
  elems : Elems mem addr k xs
  fits : ElemsFit k xs

/-! ## Geometry -/

namespace ArrShell

variable {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind} {size : Nat}

theorem classBytes_ge_24 (h : ArrShell mem addr refs cls cap k size) : 24 ≤ classBytes cls := by
  have h3 := classWords_ge_three h.cls_lo h.cls_hi
  unfold classBytes; omega

theorem payload_le (h : ArrShell mem addr refs cls cap k size) :
    arrayPayloadOffset + k.bytes * cap ≤ classBytes cls := by
  rw [← k.payload_eq_classBytes h.cls_lo h.cls_hi]
  have := Nat.mul_le_mul_left k.bytes h.cap_fit
  omega

theorem off8 (h : ArrShell mem addr refs cls cap k size) : (addr + 8).toNat = addr.toNat + 8 := by
  have := h.classBytes_ge_24; have := h.fit
  exact addr_toNat (a := addr) (i := 8) (by omega)

theorem off16 (h : ArrShell mem addr refs cls cap k size) :
    (addr + 16).toNat = addr.toNat + 16 := by
  have := h.classBytes_ge_24; have := h.fit
  exact addr_toNat (a := addr) (i := 16) (by omega)

/-- Element `j` of the capacity lies in the payload. -/
theorem elem_toNat (h : ArrShell mem addr refs cls cap k size) {j : Nat} (hj : j < cap) :
    (elemAddr addr k j).toNat = addr.toNat + (arrayPayloadOffset + k.bytes * j) ∧
      arrayPayloadOffset + k.bytes * j + k.bytes ≤ classBytes cls := by
  have hp := h.payload_le
  have hfit := h.fit
  have hm : k.bytes * (j + 1) ≤ k.bytes * cap := Nat.mul_le_mul_left _ hj
  rw [Nat.mul_succ] at hm
  refine ⟨addr_toNat (by omega), by omega⟩

theorem pointer_branch (h : ArrShell mem addr refs cls cap k size) :
    Cond.holds .tnz .w64 addr 1 = false := by
  have hbit : (addr &&& 1).toNat = 0 := by
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := h.aligned
    omega
  have hzero : addr &&& 1 = 0 := UInt64.toNat_inj.mp hbit
  simp [Cond.holds, Width.truncate, Width.mask, hzero]

theorem count_load (h : ArrShell mem addr refs cls cap k size) :
    loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat (refs - 1)) := by
  have h24 := h.classBytes_ge_24
  have hr := wordAt_read32_hi h.header_word (by have := h.fit; omega)
  have hrc : (k.header cls refs >>> 32).toNat = refs - 1 := by
    have hf := (k.header_fields h.cls_hi h.refs_pos h.refs_le).2.2.2
    omega
  have heq : k.header cls refs >>> 32 = UInt64.ofNat (refs - 1) := by
    apply UInt64.toNat_inj.mp
    rw [hrc, UInt64.toNat_ofNat']
    have hm := h.refs_le
    unfold maxCount at hm
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem scan_load (h : ArrShell mem addr refs cls cap k size) :
    loadWord mem .w8 .zero addr = some (UInt64.ofNat k.scan) := by
  have hr := wordAt_read8_low h.header_word
  have hs := (k.header_fields h.cls_hi h.refs_pos h.refs_le).1
  have heq : (k.header cls refs &&& 0xFF) = UInt64.ofNat k.scan := by
    apply UInt64.toNat_inj.mp
    rw [hs, UInt64.toNat_ofNat']
    have := k.scan_lt
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem class_load (h : ArrShell mem addr refs cls cap k size) :
    loadWord mem .w8 .zero (addr + 1) = some (UInt64.ofNat cls) := by
  have hr := wordAt_read8_byte1 h.header_word
  have hc := (k.header_fields h.cls_hi h.refs_pos h.refs_le).2.1
  have heq : ((k.header cls refs >>> 8) &&& 0xFF) = UInt64.ofNat cls := by
    apply UInt64.toNat_inj.mp
    rw [hc, UInt64.toNat_ofNat']
    have hm := h.cls_hi
    unfold maxClass at hm
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem size_load (h : ArrShell mem addr refs cls cap k size) :
    loadWord mem .w64 .zero (addr + 8) = some (UInt64.ofNat size) :=
  wordAt_load64 h.size_word

theorem cap_load (h : ArrShell mem addr refs cls cap k size) :
    loadWord mem .w64 .zero (addr + 16) = some (UInt64.ofNat cap) :=
  wordAt_load64 h.cap_word

theorem cap_lt (h : ArrShell mem addr refs cls cap k size) : cap < 2 ^ 63 := by
  have hp := h.payload_le
  have hfit := h.fit
  have := k.bytes_pos
  have : cap ≤ k.bytes * cap := Nat.le_mul_of_pos_left cap this
  omega

theorem rc_not_slt_zero (h : ArrShell mem addr refs cls cap k size) :
    Cond.holds .slt .w32 (UInt64.ofNat (refs - 1)) 0 = false := by
  have hmax := h.refs_le
  unfold maxCount at hmax
  have hr : (UInt64.ofNat (refs - 1)).toNat = refs - 1 := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have htr : Width.truncate .w32 (UInt64.ofNat (refs - 1)) = UInt64.ofNat (refs - 1) := by
    apply UInt64.toNat_inj.mp
    simp only [Width.truncate, Width.mask, UInt64.toNat_and, hr]
    rw [show (UInt64.toNat 0xffffffff) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hsv : Width.signedValue .w32 (UInt64.ofNat (refs - 1)) = Int.ofNat (refs - 1) := by
    unfold Width.signedValue Width.bits
    rw [htr, hr]
    have : ¬ (2 ^ (32 - 1) ≤ refs - 1) := by omega
    simp [this]
  have hzero : Width.signedValue .w32 0 = 0 := by decide
  simp [Cond.holds, hsv, hzero]

/-- A store into the cell's bytes succeeds. -/
theorem write_ok (h : ArrShell mem addr refs cls cap k size) {off : Nat} {w : Width}
    (hoff : off + w.bytes ≤ classBytes cls) (v : Word) :
    mem.write? w (addr + UInt64.ofNat off) v = .ok (mem.write w (addr + UInt64.ofNat off) v) :=
  write?_ok_of_access v (fun j hj => (h.access j hj).2) (by have := h.fit; omega) hoff

/-- The cell's bytes are readable at any offset range inside it. -/
theorem readable_at (h : ArrShell mem addr refs cls cap k size) {off n : Nat}
    (hoff : off + n ≤ classBytes cls) :
    ∀ i < n, mem.readable (addr + UInt64.ofNat off + UInt64.ofNat i) = true := by
  intro i hi
  have hfit := h.fit
  have ho : (addr + UInt64.ofNat off).toNat = addr.toNat + off := addr_toNat (by omega)
  have hka : (addr + UInt64.ofNat off) + UInt64.ofNat i = addr + UInt64.ofNat (off + i) := by
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by rw [ho]; omega), ho, addr_toNat (by omega)]
    omega
  rw [hka]
  exact (h.access (off + i) (by omega)).1

end ArrShell

theorem ArrCell.elem_load {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem addr refs cls cap k xs) {j : Nat} (hj : j < xs.length) :
    loadWord mem k.width .zero (elemAddr addr k j) = some xs[j] :=
  (h.elems j hj).load (h.fits _ (List.getElem_mem hj))

theorem StaticArrCell.pointer_branch {mem : Memory} {addr : Word} {cap : Nat} {k : ElemKind}
    {xs : List Word} (h : StaticArrCell mem addr cap k xs) :
    Cond.holds .tnz .w64 addr 1 = false := by
  have hbit : (addr &&& 1).toNat = 0 := by
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := h.aligned
    omega
  have hzero : addr &&& 1 = 0 := UInt64.toNat_inj.mp hbit
  simp [Cond.holds, Width.truncate, Width.mask, hzero]

theorem StaticArrCell.count_load {mem : Memory} {addr : Word} {cap : Nat} {k : ElemKind}
    {xs : List Word} (h : StaticArrCell mem addr cap k xs) :
    loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat Rt.immortalRc) := by
  have hfit8 : addr.toNat + 8 ≤ 2 ^ 64 := by have := h.fit; unfold arrayPayloadOffset at this; omega
  have hr := wordAt_read32_hi h.header_word hfit8
  have hrc := (k.staticHeader_fields).2.2.2
  have heq : k.staticHeader >>> 32 = UInt64.ofNat Rt.immortalRc := by
    apply UInt64.toNat_inj.mp
    rw [hrc, UInt64.toNat_ofNat']
    rfl
  simp [loadWord, hr, heq]

theorem StaticArrCell.size_load {mem : Memory} {addr : Word} {cap : Nat} {k : ElemKind}
    {xs : List Word} (h : StaticArrCell mem addr cap k xs) :
    loadWord mem .w64 .zero (addr + 8) = some (UInt64.ofNat xs.length) :=
  wordAt_load64 h.size_word

theorem StaticArrCell.elem_load {mem : Memory} {addr : Word} {cap : Nat} {k : ElemKind}
    {xs : List Word} (h : StaticArrCell mem addr cap k xs) {j : Nat} (hj : j < xs.length) :
    loadWord mem k.width .zero (elemAddr addr k j) = some xs[j] :=
  (h.elems j hj).load (h.fits _ (List.getElem_mem hj))

theorem immortal_slt_zero : Cond.holds .slt .w32 (UInt64.ofNat Rt.immortalRc) 0 = true := by
  decide

/-! ## Frames -/

namespace MemFrame

/-- A shell none of whose bytes is touched. -/
theorem arrShell {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {addr : Word}
    {refs cls cap : Nat} {k : ElemKind} {size : Nat} (hc : ArrShell m addr refs cls cap k size)
    (hout : ∀ x, addr.toNat ≤ x → x < addr.toNat + 24 → ¬ t x) :
    ArrShell m' addr refs cls cap k size := by
  have h24 := hc.classBytes_ge_24
  have hfit := hc.fit
  have h8 := hc.off8
  have h16 := hc.off16
  refine ⟨hc.aligned, hc.nonzero, hc.cls_lo, hc.cls_hi, hc.refs_pos, hc.refs_le, hc.fit,
    hc.size_le, hc.cap_fit, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [h.readable, h.writable]; exact hc.access j hj
  · exact h.wordAt hc.header_word (by omega) (fun x h1 h2 => hout x h1 (by omega))
  · exact h.wordAt hc.size_word (by rw [h8]; omega)
      (fun x h1 h2 => hout x (by rw [h8] at h1; omega) (by rw [h8] at h2; omega))
  · exact h.wordAt hc.cap_word (by rw [h16]; omega)
      (fun x h1 h2 => hout x (by rw [h16] at h1; omega) (by rw [h16] at h2; omega))

/-- Elements none of whose bytes is touched. -/
theorem elems {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {addr : Word}
    {refs cls cap : Nat} {k : ElemKind} {size : Nat} (hc : ArrShell m addr refs cls cap k size)
    {xs : List Word} (he : Elems m addr k xs) (hlen : xs.length ≤ cap)
    (hout : ∀ x, addr.toNat + arrayPayloadOffset ≤ x →
      x < addr.toNat + (arrayPayloadOffset + k.bytes * xs.length) → ¬ t x) :
    Elems m' addr k xs := by
  intro j hj
  obtain ⟨hja, hjb⟩ := hc.elem_toNat (j := j) (by omega)
  have hm : k.bytes * (j + 1) ≤ k.bytes * xs.length := Nat.mul_le_mul_left _ hj
  rw [Nat.mul_succ] at hm
  have hfit := hc.fit
  have hbw : k.width.bytes = k.bytes := rfl
  exact h.valAt (he j hj) (by rw [hja]; omega)
    (fun x h1 h2 => hout x (by rw [hja] at h1; omega) (by rw [hja] at h2; omega))

/-- A cell none of whose bytes is touched. -/
theorem arrCell {m m' : Memory} {t : Nat → Prop} (h : MemFrame m m' t) {addr : Word}
    {refs cls cap : Nat} {k : ElemKind} {xs : List Word} (hc : ArrCell m addr refs cls cap k xs)
    (hout : ∀ x, addr.toNat ≤ x → x < addr.toNat + classBytes cls → ¬ t x) :
    ArrCell m' addr refs cls cap k xs := by
  have hp := hc.shell.payload_le
  have hsz := hc.shell.size_le
  have hm : k.bytes * xs.length ≤ k.bytes * cap := Nat.mul_le_mul_left _ hsz
  have h24 := hc.shell.classBytes_ge_24
  unfold arrayPayloadOffset at hp
  exact ⟨h.arrShell hc.shell (fun x h1 h2 => hout x h1 (by omega)),
    h.elems hc.shell hc.elems hsz (fun x h1 h2 => hout x (by omega) (by unfold arrayPayloadOffset at h2; omega)), hc.fits⟩

end MemFrame

/-! ## Mutations in place -/

/-- Element `j`'s bytes are `[24 + b·j, 24 + b·(j+1))`; any other element, and the three header
words, are disjoint from them. -/
private theorem elem_disjoint {b i j : Nat} (_hb : 0 < b) (hij : i ≠ j) :
    arrayPayloadOffset + b * i + b ≤ arrayPayloadOffset + b * j ∨
      arrayPayloadOffset + b * j + b ≤ arrayPayloadOffset + b * i := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · left
    have := Nat.mul_le_mul_left b (show i + 1 ≤ j by omega)
    rw [Nat.mul_succ] at this; omega
  · right
    have := Nat.mul_le_mul_left b (show j + 1 ≤ i by omega)
    rw [Nat.mul_succ] at this; omega

/-- An element stored in place. -/
theorem ArrCell.setElem {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem addr refs cls cap k xs) {j : Nat} (hj : j < xs.length)
    {x : Word} (hx : k.Fits x) :
    ArrCell (mem.write k.width (elemAddr addr k j) x) addr refs cls cap k (xs.set j x) := by
  have hs := h.shell
  have hsz := hs.size_le
  obtain ⟨hja, hjb⟩ := hs.elem_toNat (j := j) (by omega)
  have hfit := hs.fit
  have hbw : k.width.bytes = k.bytes := rfl
  have hfr := MemFrame.write mem k.width (elemAddr addr k j) x
    (by rw [hja, hbw]; omega)
  refine ⟨by
      rw [List.length_set]
      exact hfr.arrShell hs (fun y h1 h2 hy => by
        unfold Span at hy; rw [hja] at hy; unfold arrayPayloadOffset at hy; omega), ?_, ?_⟩
  · intro i hi
    have hi' : i < xs.length := by simpa using hi
    by_cases hij : i = j
    · subst hij
      rw [List.getElem_set_self]
      apply valAt_write
      rw [hbw]
      exact hs.readable_at (by omega)
    · rw [List.getElem_set_ne (Ne.symm hij)]
      obtain ⟨hia, hib⟩ := hs.elem_toNat (j := i) (by omega)
      have hd := elem_disjoint k.bytes_pos hij
      exact hfr.valAt (h.elems i hi') (by rw [hia, hbw]; omega)
        (fun y h1 h2 hy => by
          unfold Span at hy; rw [hja] at hy; rw [hia] at h1 h2; omega)
  · intro y hy
    rcases List.mem_or_eq_of_mem_set hy with hy | rfl
    · exact h.fits y hy
    · exact hx

/-- An element appended in place: stored at index `size`, then the size word raised. -/
theorem ArrCell.pushElem {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem addr refs cls cap k xs) (hroom : xs.length < cap)
    {x : Word} (hx : k.Fits x) :
    ArrCell ((mem.write k.width (elemAddr addr k xs.length) x).write .w64 (addr + 8)
      (UInt64.ofNat (xs.length + 1))) addr refs cls cap k (xs ++ [x]) := by
  have hs := h.shell
  obtain ⟨hja, hjb⟩ := hs.elem_toNat hroom
  have hfit := hs.fit
  have h24 := hs.classBytes_ge_24
  have h8 := hs.off8
  have hbw : k.width.bytes = k.bytes := rfl
  let m1 := mem.write k.width (elemAddr addr k xs.length) x
  have hfr1 := MemFrame.write mem k.width (elemAddr addr k xs.length) x
    (by rw [hja, hbw]; omega)
  have hfr2 := MemFrame.write m1 .w64 (addr + 8) (UInt64.ofNat (xs.length + 1))
    (by rw [h8]; simp [Width.bytes]; omega)
  have hs1 : ArrShell m1 addr refs cls cap k xs.length := hfr1.arrShell hs
    (fun y h1 h2 hy => by unfold Span at hy; rw [hja] at hy; unfold arrayPayloadOffset at hy; omega)
  have hv1 : ValAt m1 (elemAddr addr k xs.length) k.width x := by
    apply valAt_write; rw [hbw]
    exact hs.readable_at (by omega)
  have he1 : Elems m1 addr k (xs ++ [x]) := by
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hix : i = xs.length
    · subst hix; rw [List.getElem_append_right (by omega)]; simpa using hv1
    · have hi' : i < xs.length := by omega
      rw [List.getElem_append_left hi']
      obtain ⟨hia, hib⟩ := hs.elem_toNat (j := i) (by omega)
      have hd := elem_disjoint k.bytes_pos hix
      exact hfr1.valAt (h.elems i hi') (by rw [hia, hbw]; omega)
        (fun y h1 h2 hy => by unfold Span at hy; rw [hja] at hy; rw [hia] at h1 h2; omega)
  refine ⟨⟨hs1.aligned, hs1.nonzero, hs1.cls_lo, hs1.cls_hi, hs1.refs_pos, hs1.refs_le, hs1.fit,
      by simp; omega, hs1.cap_fit, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj; simpa [m1, Memory.write] using hs1.access j hj
  · exact hfr2.wordAt hs1.header_word (by omega)
      (fun y h1 h2 hy => by unfold Span at hy; rw [h8] at hy; simp [Width.bytes] at hy; omega)
  · simp only [List.length_append, List.length_singleton]
    exact wordAt_write64 (fun i hi => (hs1.size_word).readable i hi)
  · exact hfr2.wordAt hs1.cap_word (by rw [hs1.off16]; omega)
      (fun y h1 h2 hy => by
        unfold Span at hy; rw [h8] at hy; rw [hs1.off16] at h1 h2; simp [Width.bytes] at hy; omega)
  · have hlen : (xs ++ [x]).length ≤ cap := by simp; omega
    exact hfr2.elems hs1 he1 hlen (fun y h1 h2 hy => by
      unfold Span at hy; rw [h8] at hy; simp [Width.bytes] at hy; unfold arrayPayloadOffset at h1; omega)
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact h.fits y hy
    · simp at hy; subst hy; exact hx

/-- The size word lowered to `n`: the cell keeps its first `n` elements. -/
theorem ArrCell.truncate {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem addr refs cls cap k xs) {n : Nat} (hn : n ≤ xs.length) :
    ArrCell (mem.write .w64 (addr + 8) (UInt64.ofNat n)) addr refs cls cap k (xs.take n) := by
  have hs := h.shell
  have hfit := hs.fit
  have h24 := hs.classBytes_ge_24
  have h8 := hs.off8
  have hfr := MemFrame.write mem .w64 (addr + 8) (UInt64.ofNat n)
    (by rw [h8]; simp [Width.bytes]; omega)
  have hlen : (xs.take n).length = n := by simp; omega
  refine ⟨⟨hs.aligned, hs.nonzero, hs.cls_lo, hs.cls_hi, hs.refs_pos, hs.refs_le, hs.fit,
      by rw [hlen]; have := hs.size_le; omega, hs.cap_fit, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj; simpa [Memory.write] using hs.access j hj
  · exact hfr.wordAt hs.header_word (by omega)
      (fun y h1 h2 hy => by unfold Span at hy; rw [h8] at hy; simp [Width.bytes] at hy; omega)
  · rw [hlen]; exact wordAt_write64 (fun i hi => hs.size_word.readable i hi)
  · exact hfr.wordAt hs.cap_word (by rw [hs.off16]; omega)
      (fun y h1 h2 hy => by
        unfold Span at hy; rw [h8] at hy; rw [hs.off16] at h1 h2; simp [Width.bytes] at hy; omega)
  · have he : Elems mem addr k (xs.take n) := by
      intro j hj
      have hj' : j < xs.length := by simp at hj; omega
      rw [List.getElem_take]
      exact h.elems j hj'
    exact hfr.elems hs he (by rw [hlen]; have := hs.size_le; omega) (fun y h1 h2 hy => by
      unfold Span at hy; rw [h8] at hy; simp [Width.bytes] at hy; unfold arrayPayloadOffset at h1
      omega)
  · intro y hy; exact h.fits y (List.mem_of_mem_take hy)

/-- The count word stored: `refs'` references. -/
theorem ArrShell.withCount {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {size : Nat} (h : ArrShell mem addr refs cls cap k size) {refs' : Nat} (hpos' : 0 < refs')
    (hmax' : refs' ≤ maxCount) :
    ArrShell (storeCount mem addr (UInt64.ofNat (refs' - 1))) addr refs' cls cap k size := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have h8 := h.off8
  have h16 := h.off16
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, hpos', hmax', h.fit, h.size_le, h.cap_fit,
    ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [storeCount, Memory.write] using h.access j hj
  · exact
    { bytes := fun i hi => by
        have h4 : (addr + 4).toNat = addr.toNat + 4 := countAddress (by omega)
        have hs := k.scan_lt
        have ht := k.tag_lt
        have hcls := h.cls_hi
        have hmax := h.refs_le
        have hpos := h.refs_pos
        have hc : cls < 256 := by unfold maxClass at hcls; omega
        have hr : refs - 1 < 2 ^ 32 := by unfold maxCount at hmax; omega
        have hr' : refs' - 1 < 2 ^ 32 := by unfold maxCount at hmax'; omega
        have hto := IxCC.Rt.Rc.header_toNat hs hc ht hr
        have hto' := IxCC.Rt.Rc.header_toNat hs hc ht hr'
        by_cases hlow : i < 4
        · have hout := (storeCount_frame mem addr (UInt64.ofNat (refs' - 1)) (by omega)).outside
            (addr + UInt64.ofNat i) (by rw [addr_toNat (by omega)]; omega)
          rw [hout, h.header_word.bytes i hi]
          apply UInt8.toNat_inj.mp
          rw [byte_of_shift _ _ (by omega), byte_of_shift _ _ (by omega)]
          simp only [ElemKind.header, IxCC.Rt.Rc.dynamicHeader, hto, hto']
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
        · have hai : addr + UInt64.ofNat i = (addr + 4) + UInt64.ofNat (i - 4) := by
            apply UInt64.toNat_inj.mp
            rw [addr_toNat (by omega), addr_toNat (by omega), h4]
            omega
          rw [hai, storeCount_bytes mem addr (UInt64.ofNat (refs' - 1)) (by omega)]
          apply UInt8.toNat_inj.mp
          rw [byte_of_shift _ _ (by omega), byte_of_shift _ _ (by omega)]
          have hrc' : (UInt64.ofNat (refs' - 1)).toNat = refs' - 1 := by
            rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
          rw [hrc']
          simp only [ElemKind.header, IxCC.Rt.Rc.dynamicHeader, hto']
          rcases (show i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl <;> omega
      readable := fun i hi => by simpa [storeCount, Memory.write] using h.header_word.readable i hi }
  · exact storeCount_word h.size_word (by omega) (by rw [h8]; omega) (by rw [h8]; omega)
  · exact storeCount_word h.cap_word (by omega) (by rw [h16]; omega) (by rw [h16]; omega)

/-- The count word stored, for a whole cell. -/
theorem ArrCell.withCount {mem : Memory} {addr : Word} {refs cls cap : Nat} {k : ElemKind}
    {xs : List Word} (h : ArrCell mem addr refs cls cap k xs) {refs' : Nat} (hpos' : 0 < refs')
    (hmax' : refs' ≤ maxCount) :
    ArrCell (storeCount mem addr (UInt64.ofNat (refs' - 1))) addr refs' cls cap k xs := by
  have h24 := h.shell.classBytes_ge_24
  have hfit := h.shell.fit
  have hfr := (storeCount_frame mem addr (UInt64.ofNat (refs' - 1)) (by omega))
  have hframe : MemFrame mem (storeCount mem addr (UInt64.ofNat (refs' - 1)))
      (Span (addr.toNat + 4) 4) :=
    ⟨hfr.readable, hfr.writable, fun a ha => hfr.outside a (by unfold Span at ha; omega)⟩
  have hsz := h.shell.size_le
  exact ⟨h.shell.withCount hpos' hmax',
    hframe.elems h.shell h.elems hsz (fun y h1 h2 hy => by
      unfold Span at hy; unfold arrayPayloadOffset at h1; omega), h.fits⟩

/-! ## The side path's cells -/

/-- The elements of a side-path array value, as words. -/
def ArrayVal.words : ArrayVal → List Word
  | .boxed xs => xs
  | .bytes bs => bs.map UInt8.toUInt64
  | .limbs xs => xs

theorem ArrayVal.words_length (v : ArrayVal) : v.words.length = v.size := by
  cases v <;> simp [ArrayVal.words, ArrayVal.size]

private theorem payload_words {mem : Memory} {addr : Word} (val : ArrayVal)
    (h : ArrayPayload mem addr val) : Elems mem addr val.kind.elem val.words ∧
      ElemsFit val.kind.elem val.words := by
  cases val with
  | boxed xs =>
    exact ⟨fun j hj => ValAt.of_wordAt (h j hj), fun x _ => ElemKind.boxed_fits x⟩
  | limbs xs =>
    exact ⟨fun j hj => ValAt.of_wordAt (h j hj), fun x _ => ElemKind.fits_w64 rfl x⟩
  | bytes bs =>
    refine ⟨fun j hj => ?_, fun x hx => ?_⟩
    · have hj' : j < bs.length := by simpa [ArrayVal.words] using hj
      have heq : (ArrayVal.bytes bs).words[j]'hj = bs[j].toUInt64 := by simp [ArrayVal.words]
      show ValAt mem (addr + UInt64.ofNat (arrayPayloadOffset + 1 * j)) .w8
        ((ArrayVal.bytes bs).words[j]'hj)
      rw [heq, Nat.one_mul]
      exact ValAt.of_byteAt (h j hj')
    · simp only [ArrayVal.words, List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      show (b.toUInt64).toNat < 2 ^ 8
      rw [UInt8.toNat_toUInt64]
      exact b.toNat_lt

/-- A side-path live array cell is a cell of its kind. -/
theorem LiveArrayCell.toArrCell {mem : Memory} {addr : Word} {refs cls cap : Nat}
    {val : ArrayVal} (h : LiveArrayCell mem addr refs cls cap val) :
    ArrCell mem addr refs cls cap val.kind.elem val.words := by
  obtain ⟨he, hf⟩ := payload_words val h.payload
  have hcap : cap ≤ val.kind.elem.capOfClass cls := by
    have hc := h.cap_fit
    cases val with
    | boxed _ => rw [show ArrayVal.kind (.boxed _) = .boxed from rfl, show ArrayKind.elem .boxed = .boxed from rfl, ElemKind.boxed_capOfClass]; exact hc
    | bytes _ => rw [show ArrayVal.kind (.bytes _) = .bytes from rfl, show ArrayKind.elem .bytes = .packed .w8 from rfl, ElemKind.bytes_capOfClass]; exact hc
    | limbs _ => rw [show ArrayVal.kind (.limbs _) = .limbs from rfl, show ArrayKind.elem .limbs = .packed .w64 from rfl, ElemKind.limbs_capOfClass]; exact hc
  refine ⟨⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by rw [ArrayVal.words_length]; exact h.size_le, hcap, h.access,
    by rw [ArrayKind.elem_header]; exact h.header_word,
    by rw [ArrayVal.words_length]; exact h.size_word, h.cap_word⟩, he, hf⟩

/-- A side-path static array cell is a static cell of its kind. -/
theorem StaticArrayCell.toStatic {mem : Memory} {addr : Word} {cap : Nat} {val : ArrayVal}
    (h : StaticArrayCell mem addr cap val) :
    StaticArrCell mem addr cap val.kind.elem val.words := by
  obtain ⟨he, hf⟩ := payload_words val h.payload
  have hfit := h.fit
  refine ⟨h.aligned, h.nonzero, by rw [ArrayVal.words_length]; exact h.size_le, ?_,
    by rw [ArrayKind.elem_staticHeader]; exact h.header_word,
    by rw [ArrayVal.words_length]; exact h.size_word, h.cap_word, he, hf⟩
  cases val with
  | boxed _ => show _ + (_ + 8 * cap) < _; simp only at hfit; omega
  | bytes _ => show _ + (_ + 1 * cap) < _; simp only at hfit; omega
  | limbs _ => show _ + (_ + 8 * cap) < _; simp only at hfit; omega

end IxCC.Rt.Rc.Array
