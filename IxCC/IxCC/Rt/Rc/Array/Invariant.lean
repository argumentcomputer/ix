import IxCC.Rt.Rc.Array.Layout
import IxCC.Rt.Rc.Gen.Proof.AllocatorReady
import IxCC.Rt.Rc.Proof.Memory
import IxCC.Rt.Rc.Proof.FreeList

/-! # Heap Invariant for Contiguous Arrays, ByteArrays, and LimbArrays

Defines the memory representation invariants for dynamic and static (`.rodata`)
contiguous arrays and connects them cleanly to both:
* `IxCC.Rt.Rc.Gen.AllocatorReady` (the 71-class counted-heap allocator), and
* `IxCC.X86.ELFRodata.RodataMapped` (immortal read-only ELF `.rodata` cells).

Also provides the fundamental cell-level framing and in-place mutation lemmas
(`setWord_boxed`, `setWord_limbs`, `setByte_inPlace`, `pushWord_boxed`,
`pushWord_limbs`, `pushByte_inPlace`, `pop_inPlace`, `dec_shared`, `inc_ref`)
consumed by the Lir operational proofs in `IxCC.Rt.Rc.Array.Proof.*` and the
readback proofs in `IxCC.Rt.Readback.Array`. -/

set_option autoImplicit false

namespace IxCC.Rt.Rc.Array

open IxCC.Lir (Word Cond loadWord)
open IxCC.Rt.Proof
open IxCC.Rt.Rc (maxClass maxCount classWords classBytes dynamicHeader)
open IxCC.Rt.Rc.Procs (FreeChain bumpAddress limitAddress freeHeadAddress storeCount
  countAddress storeCount_frame storeCount_word storeCount_bytes)
open IxCC.X86 (Memory Width)

/-! ## Single-byte predicate & narrow-read helpers -/

/-- The byte at `b` equals `v` and is readable. -/
structure ByteAt (m : Memory) (b : Word) (v : UInt8) : Prop where
  byte : m.bytes b = v
  readable : m.readable b = true

theorem ByteAt.read8 {m : Memory} {b : Word} {v : UInt8} (h : ByteAt m b v) :
    m.read? .w8 b = .ok v.toUInt64 := by
  rw [read?_ok (w := .w8) (fun i hi => by
    have hi0 : i = 0 := by simp [Width.bytes] at hi; omega
    subst hi0
    simpa using h.readable)]
  congr 1
  simp [Memory.read, Width.bytes, Memory.readLittle, h.byte]

theorem ByteAt.load8 {m : Memory} {b : Word} {v : UInt8} (h : ByteAt m b v) :
    loadWord m .w8 .zero b = some v.toUInt64 := by
  simp [loadWord, h.read8]

theorem byteAt_write8 {m : Memory} {b v : Word} (hr : m.readable b = true) :
    ByteAt (m.write .w8 b v) b v.toUInt8 where
  byte := by
    have h := Memory.writeLittle_bytes m b v (by decide : 1 ≤ 8) (by decide : 0 < 1)
    simpa [Memory.write, Width.bytes] using h
  readable := by simpa [Memory.write] using hr

theorem ByteAt.write_disjoint {m : Memory} {b a u : Word} {v : UInt8} {w : Width}
    (h : ByteAt m b v) (ha : a.toNat + w.bytes ≤ 2 ^ 64)
    (hd : b.toNat < a.toNat ∨ a.toNat + w.bytes ≤ b.toNat) :
    ByteAt (m.write w a u) b v where
  byte := by
    have hw : w.bytes ≤ 8 := by cases w <;> simp [Width.bytes]
    simp only [Memory.write]
    rw [writeLittle_bytes_out hw ha hd]
    exact h.byte
  readable := by simpa [Memory.write] using h.readable

theorem wordAt_load64 {m : Memory} {b v : Word} (h : WordAt m b v) :
    loadWord m .w64 .zero b = some v := by
  simp [loadWord, h.read64]

theorem wordAt_read8_at {m : Memory} {b v : Word} (h : WordAt m b v) {k : Nat} (hk : k < 8) :
    m.read? .w8 (b + UInt64.ofNat k) = .ok ((v >>> UInt64.ofNat (8 * k)).toUInt8).toUInt64 := by
  have hb : ByteAt m (b + UInt64.ofNat k) (v >>> UInt64.ofNat (8 * k)).toUInt8 :=
    ⟨h.bytes k hk, h.readable k hk⟩
  exact hb.read8

theorem wordAt_read8_low {m : Memory} {b v : Word} (h : WordAt m b v) :
    m.read? .w8 b = .ok (v &&& 0xFF) := by
  have hr := wordAt_read8_at h (k := 0) (by decide)
  rw [Nat.mul_zero, show (UInt64.ofNat 0) = 0 from rfl, UInt64.add_zero, UInt64.shiftRight_zero] at hr
  rw [hr]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, toUInt8_toNat, UInt64.toNat_and,
    show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem wordAt_read8_byte1 {m : Memory} {b v : Word} (h : WordAt m b v) :
    m.read? .w8 (b + 1) = .ok ((v >>> 8) &&& 0xFF) := by
  have hr := wordAt_read8_at h (k := 1) (by decide)
  simp only [Nat.mul_one] at hr
  rw [show (1 : Word) = UInt64.ofNat 1 from rfl, hr]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, toUInt8_toNat, UInt64.toNat_and,
    show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- The 32-bit read four bytes into a `WordAt` is bits 32–63 (`v >>> 32`). -/
theorem wordAt_read32_hi {m : Memory} {b v : Word} (h : WordAt m b v)
    (hb : b.toNat + 8 ≤ 2 ^ 64) :
    m.read? .w32 (b + 4) = .ok (v >>> 32) := by
  have h4 : (b + 4).toNat = b.toNat + 4 := countAddress hb
  have haddr : ∀ i < 4, (b + 4) + UInt64.ofNat i = b + UInt64.ofNat (4 + i) := by
    intro i hi
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by omega), addr_toNat (by omega), h4]
    omega
  rw [read?_ok (w := .w32) (fun i hi => by
    have hi' : i < 4 := by simpa [Width.bytes] using hi
    rw [haddr i hi']
    exact h.readable (4 + i) (by omega))]
  congr 1
  apply UInt64.toNat_inj.mp
  have e0 : m.bytes (b + 4 + UInt64.ofNat 0) = (v >>> UInt64.ofNat 32).toUInt8 := by
    rw [haddr 0 (by decide)]; exact h.bytes 4 (by decide)
  have e1 : m.bytes (b + 4 + UInt64.ofNat 1) = (v >>> UInt64.ofNat 40).toUInt8 := by
    rw [haddr 1 (by decide)]; exact h.bytes 5 (by decide)
  have e2 : m.bytes (b + 4 + UInt64.ofNat 2) = (v >>> UInt64.ofNat 48).toUInt8 := by
    rw [haddr 2 (by decide)]; exact h.bytes 6 (by decide)
  have e3 : m.bytes (b + 4 + UInt64.ofNat 3) = (v >>> UInt64.ofNat 56).toUInt8 := by
    rw [haddr 3 (by decide)]; exact h.bytes 7 (by decide)
  simp only [Memory.read, Width.bytes, Memory.readLittle, e0, e1, e2, e3]
  have b0 := byte_of_shift v 32 (by decide)
  have b1 := byte_of_shift v 40 (by decide)
  have b2 := byte_of_shift v 48 (by decide)
  have b3 := byte_of_shift v 56 (by decide)
  have hv := v.toNat_lt_size
  simp only [UInt64.size] at hv
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft,
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64,
    b0, b1, b2, b3, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show UInt64.toNat 0 = 0 from rfl, Nat.zero_or,
    show (UInt64.ofNat (8 * 0)).toNat % 64 = 0 from rfl,
    show (UInt64.ofNat (8 * 1)).toNat % 64 = 8 from rfl,
    show (UInt64.ofNat (8 * 2)).toNat % 64 = 16 from rfl,
    show (UInt64.ofNat (8 * 3)).toNat % 64 = 24 from rfl,
    show (UInt64.toNat 32) % 64 = 32 from rfl]
  simp only [Nat.shiftLeft_eq, Nat.pow_zero, Nat.mul_one]
  have hm0 : v.toNat / 2 ^ 32 % 256 % 2 ^ 64 = v.toNat / 2 ^ 32 % 256 := Nat.mod_eq_of_lt (by omega)
  have hm1 : v.toNat / 2 ^ 40 % 256 * 2 ^ 8 % 2 ^ 64 = v.toNat / 2 ^ 40 % 256 * 2 ^ 8 :=
    Nat.mod_eq_of_lt (by omega)
  have hm2 : v.toNat / 2 ^ 48 % 256 * 2 ^ 16 % 2 ^ 64 = v.toNat / 2 ^ 48 % 256 * 2 ^ 16 :=
    Nat.mod_eq_of_lt (by omega)
  have hm3 : v.toNat / 2 ^ 56 % 256 * 2 ^ 24 % 2 ^ 64 = v.toNat / 2 ^ 56 % 256 * 2 ^ 24 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hm0, hm1, hm2, hm3]
  have h12 : (v.toNat / 2 ^ 32 % 256) ||| (v.toNat / 2 ^ 40 % 256 * 2 ^ 8) =
      v.toNat / 2 ^ 32 % 256 + v.toNat / 2 ^ 40 % 256 * 2 ^ 8 := by
    rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
  rw [h12]
  have h123 : (v.toNat / 2 ^ 32 % 256 + v.toNat / 2 ^ 40 % 256 * 2 ^ 8) |||
      (v.toNat / 2 ^ 48 % 256 * 2 ^ 16) =
      (v.toNat / 2 ^ 32 % 256 + v.toNat / 2 ^ 40 % 256 * 2 ^ 8) +
        v.toNat / 2 ^ 48 % 256 * 2 ^ 16 := by
    rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 16), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
  rw [h123]
  have h1234 : (v.toNat / 2 ^ 32 % 256 + v.toNat / 2 ^ 40 % 256 * 2 ^ 8 +
      v.toNat / 2 ^ 48 % 256 * 2 ^ 16) ||| (v.toNat / 2 ^ 56 % 256 * 2 ^ 24) =
      (v.toNat / 2 ^ 32 % 256 + v.toNat / 2 ^ 40 % 256 * 2 ^ 8 +
        v.toNat / 2 ^ 48 % 256 * 2 ^ 16) + v.toNat / 2 ^ 56 % 256 * 2 ^ 24 := by
    rw [Nat.or_comm, Nat.mul_comm _ (2 ^ 24), ← Nat.two_pow_add_eq_or_of_lt (by omega)]; omega
  rw [h1234]
  omega

/-- Updating the high 32-bit count word at `addr + 4` replaces the RC field of a
`WordAt` holding an `arrayHeader` while leaving scan/class/tag untouched. -/
theorem wordAt_storeCount_arrayHeader {m : Memory} {addr : Word} {k : ArrayKind}
    {cls refs refs' : Nat}
    (h : WordAt m addr (arrayHeader k cls refs))
    (hfit : addr.toNat + 8 ≤ 2 ^ 64)
    (hcls : cls ≤ maxClass)
    (hpos : 0 < refs) (hmax : refs ≤ maxCount)
    (hpos' : 0 < refs') (hmax' : refs' ≤ maxCount) :
    WordAt (storeCount m addr (UInt64.ofNat (refs' - 1))) addr (arrayHeader k cls refs') where
  bytes i hi := by
    have h4 : (addr + 4).toNat = addr.toNat + 4 := countAddress hfit
    have hs := k.scan_lt
    have ht := k.tag_lt
    have hc : cls < 256 := by unfold maxClass at hcls; omega
    have hr : refs - 1 < 2 ^ 32 := by unfold maxCount at hmax; omega
    have hr' : refs' - 1 < 2 ^ 32 := by unfold maxCount at hmax'; omega
    have hto := IxCC.Rt.Rc.header_toNat hs hc ht hr
    have hto' := IxCC.Rt.Rc.header_toNat hs hc ht hr'
    by_cases hlow : i < 4
    · have hout := (storeCount_frame m addr (UInt64.ofNat (refs' - 1)) hfit).outside
        (addr + UInt64.ofNat i) (by rw [addr_toNat (by omega)]; omega)
      rw [hout, h.bytes i hi]
      apply UInt8.toNat_inj.mp
      rw [byte_of_shift _ _ (by omega), byte_of_shift _ _ (by omega)]
      simp only [arrayHeader, dynamicHeader, hto, hto']
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
    · have hai : addr + UInt64.ofNat i = (addr + 4) + UInt64.ofNat (i - 4) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by omega), addr_toNat (by omega), h4]
        omega
      rw [hai, storeCount_bytes m addr (UInt64.ofNat (refs' - 1)) (by omega)]
      apply UInt8.toNat_inj.mp
      rw [byte_of_shift _ _ (by omega), byte_of_shift _ _ (by omega)]
      have hrc' : (UInt64.ofNat (refs' - 1)).toNat = refs' - 1 := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [hrc']
      simp only [arrayHeader, dynamicHeader, hto']
      rcases (show i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl <;> omega
  readable i hi := by simpa [storeCount, Memory.write] using h.readable i hi

/-! ## Array value model -/

/-- Abstract payload of any contiguous array cell. -/
inductive ArrayVal where
  | boxed (elems : List Word)
  | bytes (data : List UInt8)
  | limbs (data : List Word)
  deriving DecidableEq, Repr

def ArrayVal.kind : ArrayVal → ArrayKind
  | .boxed _ => .boxed
  | .bytes _ => .bytes
  | .limbs _ => .limbs

def ArrayVal.size : ArrayVal → Nat
  | .boxed xs => xs.length
  | .bytes bs => bs.length
  | .limbs ls => ls.length

/-- Payload predicate at address `addr` in memory `mem`. -/
def ArrayPayload (mem : Memory) (addr : Word) : ArrayVal → Prop
  | .boxed elems => ∀ (j : Nat) (hj : j < elems.length),
      WordAt mem (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) elems[j]
  | .bytes data => ∀ (j : Nat) (hj : j < data.length),
      ByteAt mem (addr + UInt64.ofNat (arrayPayloadOffset + j)) data[j]
  | .limbs limbs => ∀ (j : Nat) (hj : j < limbs.length),
      WordAt mem (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)) limbs[j]

/-! ## Live dynamic array cells -/

/-- A live dynamically-allocated contiguous array cell in size class `cls`, with
`refs` abstract references (`rc = refs - 1`), stored capacity `cap`, and logical
payload `val`. -/
structure LiveArrayCell (mem : Memory) (addr : Word) (refs cls cap : Nat) (val : ArrayVal) : Prop where
  aligned : addr.toNat % 8 = 0
  nonzero : addr ≠ 0
  cls_lo : minArrayClass ≤ cls
  cls_hi : cls ≤ maxClass
  refs_pos : 0 < refs
  refs_le : refs ≤ maxCount
  fit : addr.toNat + classBytes cls < 2 ^ 63
  size_le : val.size ≤ cap
  cap_fit : match val with
    | .bytes _ => cap ≤ byteCapOfClass cls
    | .boxed _ | .limbs _ => cap ≤ wordCapOfClass cls
  access : ∀ j < classBytes cls,
    mem.readable (addr + UInt64.ofNat j) = true ∧ mem.writable (addr + UInt64.ofNat j) = true
  header_word : WordAt mem addr (arrayHeader val.kind cls refs)
  size_word : WordAt mem (addr + 8) (UInt64.ofNat val.size)
  cap_word : WordAt mem (addr + 16) (UInt64.ofNat cap)
  payload : ArrayPayload mem addr val

theorem LiveArrayCell.classBytes_ge_24 {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) : 24 ≤ classBytes cls := by
  have h3 := classWords_ge_three h.cls_lo h.cls_hi
  unfold classBytes; omega

theorem LiveArrayCell.pointer_branch {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) :
    Cond.holds .tnz .w64 addr 1 = false := by
  have hbit : (addr &&& 1).toNat = 0 := by
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := h.aligned
    omega
  have hzero : addr &&& 1 = 0 := UInt64.toNat_inj.mp hbit
  simp [Cond.holds, Width.truncate, Width.mask, hzero]

theorem LiveArrayCell.count_load {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) :
    loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat (refs - 1)) := by
  have h24 := h.classBytes_ge_24
  have hr := wordAt_read32_hi h.header_word (by have := h.fit; omega)
  have hrc : (arrayHeader val.kind cls refs >>> 32).toNat = refs - 1 := by
    have hf := (arrayHeader_fields (k := val.kind) h.cls_hi h.refs_pos h.refs_le).2.2.2
    omega
  have heq : arrayHeader val.kind cls refs >>> 32 = UInt64.ofNat (refs - 1) := by
    apply UInt64.toNat_inj.mp
    rw [hrc, UInt64.toNat_ofNat']
    have hm := h.refs_le
    unfold maxCount at hm
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem LiveArrayCell.scan_load {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) :
    loadWord mem .w8 .zero addr = some (UInt64.ofNat val.kind.scan) := by
  have hr := wordAt_read8_low h.header_word
  have hs := (arrayHeader_fields (k := val.kind) h.cls_hi h.refs_pos h.refs_le).1
  have heq : (arrayHeader val.kind cls refs &&& 0xFF) = UInt64.ofNat val.kind.scan := by
    apply UInt64.toNat_inj.mp
    rw [hs, UInt64.toNat_ofNat']
    have := val.kind.scan_lt
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem LiveArrayCell.class_load {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) :
    loadWord mem .w8 .zero (addr + 1) = some (UInt64.ofNat cls) := by
  have hr := wordAt_read8_byte1 h.header_word
  have hc := (arrayHeader_fields (k := val.kind) h.cls_hi h.refs_pos h.refs_le).2.1
  have heq : ((arrayHeader val.kind cls refs >>> 8) &&& 0xFF) = UInt64.ofNat cls := by
    apply UInt64.toNat_inj.mp
    rw [hc, UInt64.toNat_ofNat']
    have hm := h.cls_hi
    unfold maxClass at hm
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [loadWord, hr, heq]

theorem LiveArrayCell.rc_not_slt_zero {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) :
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

theorem LiveArrayCell.write_disjoint {mem addr refs cls cap val a u w}
    (h : LiveArrayCell mem addr refs cls cap val)
    (ha : a.toNat + w.bytes ≤ 2 ^ 64)
    (hdisj : addr.toNat + classBytes cls ≤ a.toNat ∨ a.toNat + w.bytes ≤ addr.toNat) :
    LiveArrayCell (mem.write w a u) addr refs cls cap val := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  have hbytes := arrayBytes_eq_classBytes h.cls_lo h.cls_hi
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    h.size_le, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [Memory.write] using h.access j hj
  · exact h.header_word.write_disjoint ha (by omega) (by omega)
  · exact h.size_word.write_disjoint ha (by rw [h8]; omega) (by rw [h8]; omega)
  · exact h.cap_word.write_disjoint ha (by rw [h16]; omega) (by rw [h16]; omega)
  · cases val with
    | boxed elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact (h.payload j hj).write_disjoint ha (by rw [hja]; omega) (by rw [hja]; omega)
    | limbs elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact (h.payload j hj).write_disjoint ha (by rw [hja]; omega) (by rw [hja]; omega)
    | bytes data =>
      intro j hj
      have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
      have hsz : data.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
          addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by omega)
      exact (h.payload j hj).write_disjoint ha (by rw [hja]; omega)

/-! ## In-place cell mutation lemmas -/

/-- Helper: updating the RC count at `addr + 4` preserves `LiveArrayCell` with new refcount `refs'`. -/
theorem LiveArrayCell.with_count {mem addr refs refs' cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val)
    (hpos' : 0 < refs') (hmax' : refs' ≤ maxCount) :
    LiveArrayCell (storeCount mem addr (UInt64.ofNat (refs' - 1))) addr refs' cls cap val := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  have hbytes := arrayBytes_eq_classBytes h.cls_lo h.cls_hi
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, hpos', hmax', h.fit,
    h.size_le, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [storeCount, Memory.write] using h.access j hj
  · exact wordAt_storeCount_arrayHeader h.header_word (by omega) h.cls_hi h.refs_pos h.refs_le
      hpos' hmax'
  · exact storeCount_word h.size_word (by omega) (by rw [h8]; omega) (by rw [h8]; omega)
  · exact storeCount_word h.cap_word (by omega) (by rw [h16]; omega) (by rw [h16]; omega)
  · cases val with
    | boxed elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact storeCount_word (h.payload j hj) (by omega) (by rw [hja]; omega)
        (by rw [hja]; unfold arrayPayloadOffset; omega)
    | limbs elems =>
      intro j hj
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact storeCount_word (h.payload j hj) (by omega) (by rw [hja]; omega)
        (by rw [hja]; unfold arrayPayloadOffset; omega)
    | bytes data =>
      intro j hj
      have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
      have hsz : data.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
          addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by omega)
      have h4 : (addr + 4).toNat = addr.toNat + 4 := countAddress (by omega)
      exact (h.payload j hj).write_disjoint (by rw [h4]; simp [Width.bytes]; omega)
        (by rw [hja, h4]; simp [Width.bytes, arrayPayloadOffset]; omega)

/-- Shared RC decrement updates `refs` to `refs - 1` while framing size, cap, and payload. -/
theorem LiveArrayCell.dec_shared {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (hshared : 1 < refs) :
    LiveArrayCell (storeCount mem addr (UInt64.ofNat (refs - 2))) addr (refs - 1) cls cap val := by
  have hsub : refs - 2 = (refs - 1) - 1 := by omega
  rw [hsub]
  exact h.with_count (by omega) (Nat.le_trans (Nat.sub_le refs 1) h.refs_le)

/-- RC increment updates `refs` to `refs + 1` while framing size, cap, and payload. -/
theorem LiveArrayCell.inc_ref {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (hlt : refs < maxCount) :
    LiveArrayCell (storeCount mem addr (UInt64.ofNat refs)) addr (refs + 1) cls cap val := by
  have hsub : refs = (refs + 1) - 1 := by omega
  rw [hsub]
  exact h.with_count (Nat.succ_pos refs) (Nat.succ_le_of_lt hlt)

/-- In-place word store at slot `idx` for a boxed array. -/
theorem LiveArrayCell.setWord_boxed {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.boxed elems))
    {idx : Nat} (hidx : idx < elems.length) (v : Word) :
    LiveArrayCell (mem.write .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)) v)
      addr refs cls cap (.boxed (elems.set idx v)) := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hsz : elems.length ≤ cap := h.size_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)).toNat =
      addr.toNat + (arrayPayloadOffset + 8 * idx) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp only [ArrayVal.size, List.length_set]; exact hsz, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [Memory.write] using h.access j hj
  · exact h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · simp only [ArrayVal.size, List.length_set]
    exact h.size_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h8]; omega) (by rw [hia, h8]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · exact h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h16]; omega) (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · intro j hj
    have hj' : j < elems.length := by simpa using hj
    by_cases hje : j = idx
    · subst hje
      rw [List.getElem_set_self]
      apply wordAt_write64
      intro k hk
      have hka : addr + UInt64.ofNat (arrayPayloadOffset + 8 * j) + UInt64.ofNat k =
          addr + UInt64.ofNat (arrayPayloadOffset + 8 * j + k) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [hia]; omega), hia, addr_toNat (by omega)]
        omega
      rw [hka]
      exact (h.access (arrayPayloadOffset + 8 * j + k) (by omega)).1
    · rw [List.getElem_set_ne (Ne.symm hje)]
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact (h.payload j hj').write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [hia, hja]; simp [Width.bytes]; omega)

/-- In-place word store at slot `idx` for a limb array (`Array UInt64`). -/
theorem LiveArrayCell.setWord_limbs {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.limbs elems))
    {idx : Nat} (hidx : idx < elems.length) (v : Word) :
    LiveArrayCell (mem.write .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)) v)
      addr refs cls cap (.limbs (elems.set idx v)) := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hsz : elems.length ≤ cap := h.size_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * idx)).toNat =
      addr.toNat + (arrayPayloadOffset + 8 * idx) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp only [ArrayVal.size, List.length_set]; exact hsz, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [Memory.write] using h.access j hj
  · exact h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · simp only [ArrayVal.size, List.length_set]
    exact h.size_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h8]; omega) (by rw [hia, h8]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · exact h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h16]; omega) (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · intro j hj
    have hj' : j < elems.length := by simpa using hj
    by_cases hje : j = idx
    · subst hje
      rw [List.getElem_set_self]
      apply wordAt_write64
      intro k hk
      have hka : addr + UInt64.ofNat (arrayPayloadOffset + 8 * j) + UInt64.ofNat k =
          addr + UInt64.ofNat (arrayPayloadOffset + 8 * j + k) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by rw [hia]; omega), hia, addr_toNat (by omega)]
        omega
      rw [hka]
      exact (h.access (arrayPayloadOffset + 8 * j + k) (by omega)).1
    · rw [List.getElem_set_ne (Ne.symm hje)]
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      exact (h.payload j hj').write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [hia, hja]; simp [Width.bytes]; omega)

/-- In-place byte store at slot `idx` for `ByteArray`. -/
theorem LiveArrayCell.setByte_inPlace {mem addr refs cls cap data}
    (h : LiveArrayCell mem addr refs cls cap (.bytes data))
    {idx : Nat} (hidx : idx < data.length) (v : Word) :
    LiveArrayCell (mem.write .w8 (addr + UInt64.ofNat (arrayPayloadOffset + idx)) v)
      addr refs cls cap (.bytes (data.set idx v.toUInt8)) := by
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
  have hsz : data.length ≤ cap := h.size_le
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + idx)).toNat =
      addr.toNat + (arrayPayloadOffset + idx) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp only [ArrayVal.size, List.length_set]; exact hsz, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [Memory.write] using h.access j hj
  · exact h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · simp only [ArrayVal.size, List.length_set]
    exact h.size_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h8]; omega) (by rw [hia, h8]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · exact h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
      (by rw [h16]; omega) (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)
  · intro j hj
    have hj' : j < data.length := by simpa using hj
    by_cases hje : j = idx
    · subst hje
      rw [List.getElem_set_self]
      exact byteAt_write8 (h.access (arrayPayloadOffset + j) (by omega)).1
    · rw [List.getElem_set_ne (Ne.symm hje)]
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
          addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by omega)
      exact (h.payload j hj').write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hia, hja]; simp [Width.bytes]; omega)

/-- In-place push into a boxed array with slack capacity (`elems.length < cap`). -/
theorem LiveArrayCell.pushWord_boxed {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.boxed elems))
    (hroom : elems.length < cap) (v : Word) :
    let m1 := mem.write .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)) v
    let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (elems.length + 1))
    LiveArrayCell m2 addr refs cls cap (.boxed (elems ++ [v])) := by
  intro m1 m2
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)).toNat =
      addr.toNat + (arrayPayloadOffset + 8 * elems.length) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp [ArrayVal.size]; omega, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [m2, m1, Memory.write] using h.access j hj
  · exact (h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp only [Width.bytes]; omega) (by omega) (by rw [h8]; simp only [Width.bytes]; omega)
  · simp only [ArrayVal.size, List.length_append, List.length_singleton]
    apply wordAt_write64
    intro k hk
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]
      omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).1
  · exact (h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [h8, h16]; simp only [Width.bytes]; omega)
  · intro j hj
    have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
        addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by simp at hj; omega)
    by_cases hlt : j < elems.length
    · rw [List.getElem_append_left hlt]
      exact ((h.payload j hlt).write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [hia, hja]; simp [Width.bytes]; omega)).write_disjoint
        (by rw [h8]; simp [Width.bytes]; omega) (by rw [hja]; omega)
        (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)
    · have hje : j = elems.length := by simp at hj; omega
      subst hje
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      have hw1 : WordAt m1 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)) v := by
        apply wordAt_write64
        intro k hk
        have hka : addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length) + UInt64.ofNat k =
            addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length + k) := by
          apply UInt64.toNat_inj.mp
          rw [addr_toNat (by rw [hia]; omega), hia, addr_toNat (by omega)]
          omega
        rw [hka]
        exact (h.access (arrayPayloadOffset + 8 * elems.length + k) (by omega)).1
      exact hw1.write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [hia]; omega) (by rw [h8, hia]; simp [Width.bytes, arrayPayloadOffset]; omega)

/-- In-place push into a limb array with slack capacity (`elems.length < cap`). -/
theorem LiveArrayCell.pushWord_limbs {mem addr refs cls cap elems}
    (h : LiveArrayCell mem addr refs cls cap (.limbs elems))
    (hroom : elems.length < cap) (v : Word) :
    let m1 := mem.write .w64 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)) v
    let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (elems.length + 1))
    LiveArrayCell m2 addr refs cls cap (.limbs (elems ++ [v])) := by
  intro m1 m2
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).1
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)).toNat =
      addr.toNat + (arrayPayloadOffset + 8 * elems.length) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp [ArrayVal.size]; omega, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [m2, m1, Memory.write] using h.access j hj
  · exact (h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp only [Width.bytes]; omega) (by omega) (by rw [h8]; simp only [Width.bytes]; omega)
  · simp only [ArrayVal.size, List.length_append, List.length_singleton]
    apply wordAt_write64
    intro k hk
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]
      omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).1
  · exact (h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [h8, h16]; simp only [Width.bytes]; omega)
  · intro j hj
    have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
        addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by simp at hj; omega)
    by_cases hlt : j < elems.length
    · rw [List.getElem_append_left hlt]
      exact ((h.payload j hlt).write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [hia, hja]; simp [Width.bytes]; omega)).write_disjoint
        (by rw [h8]; simp [Width.bytes]; omega) (by rw [hja]; omega)
        (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)
    · have hje : j = elems.length := by simp at hj; omega
      subst hje
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      have hw1 : WordAt m1 (addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length)) v := by
        apply wordAt_write64
        intro k hk
        have hka : addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length) + UInt64.ofNat k =
            addr + UInt64.ofNat (arrayPayloadOffset + 8 * elems.length + k) := by
          apply UInt64.toNat_inj.mp
          rw [addr_toNat (by rw [hia]; omega), hia, addr_toNat (by omega)]
          omega
        rw [hka]
        exact (h.access (arrayPayloadOffset + 8 * elems.length + k) (by omega)).1
      exact hw1.write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [hia]; omega) (by rw [h8, hia]; simp [Width.bytes, arrayPayloadOffset]; omega)

/-- In-place push into a `ByteArray` with slack capacity (`data.length < cap`). -/
theorem LiveArrayCell.pushByte_inPlace {mem addr refs cls cap data}
    (h : LiveArrayCell mem addr refs cls cap (.bytes data))
    (hroom : data.length < cap) (v : Word) :
    let m1 := mem.write .w8 (addr + UInt64.ofNat (arrayPayloadOffset + data.length)) v
    let m2 := m1.write .w64 (addr + 8) (UInt64.ofNat (data.length + 1))
    LiveArrayCell m2 addr refs cls cap (.bytes (data ++ [v.toUInt8])) := by
  intro m1 m2
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
  have hbytes := (arrayBytes_eq_classBytes h.cls_lo h.cls_hi).2
  have hia : (addr + UInt64.ofNat (arrayPayloadOffset + data.length)).toNat =
      addr.toNat + (arrayPayloadOffset + data.length) := addr_toNat (by omega)
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by simp [ArrayVal.size]; omega, h.cap_fit, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa [m2, m1, Memory.write] using h.access j hj
  · exact (h.header_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by omega)
      (by rw [hia]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp only [Width.bytes]; omega) (by omega) (by rw [h8]; simp only [Width.bytes]; omega)
  · simp only [ArrayVal.size, List.length_append, List.length_singleton]
    apply wordAt_write64
    intro k hk
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]
      omega
    rw [hka]
    simpa [m1, Memory.write] using (h.access (8 + k) (by omega)).1
  · exact (h.cap_word.write_disjoint (by rw [hia]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [hia, h16]; simp [Width.bytes, arrayPayloadOffset]; omega)).write_disjoint
      (by rw [h8]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [h8, h16]; simp only [Width.bytes]; omega)
  · intro j hj
    have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
        addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by simp at hj; omega)
    by_cases hlt : j < data.length
    · rw [List.getElem_append_left hlt]
      exact ((h.payload j hlt).write_disjoint (by rw [hia]; simp [Width.bytes]; omega)
        (by rw [hia, hja]; simp [Width.bytes]; omega)).write_disjoint
        (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)
    · have hje : j = data.length := by simp at hj; omega
      subst hje
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      have hb1 : ByteAt m1 (addr + UInt64.ofNat (arrayPayloadOffset + data.length)) v.toUInt8 :=
        byteAt_write8 (h.access (arrayPayloadOffset + data.length) (by omega)).1
      exact hb1.write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [h8, hia]; simp [Width.bytes, arrayPayloadOffset]; omega)

/-- In-place pop (size decrement by 1) for any non-empty array cell. -/
theorem LiveArrayCell.pop_inPlace {mem addr refs cls cap val}
    (h : LiveArrayCell mem addr refs cls cap val) (_hne : 0 < val.size) :
    let val' : ArrayVal := match val with
      | .boxed xs => .boxed xs.dropLast
      | .bytes bs => .bytes bs.dropLast
      | .limbs ls => .limbs ls.dropLast
    LiveArrayCell (mem.write .w64 (addr + 8) (UInt64.ofNat (val.size - 1)))
      addr refs cls cap val' := by
  intro val'
  have h24 := h.classBytes_ge_24
  have hfit := h.fit
  have h8 : (addr + 8).toNat = addr.toNat + 8 := by
    have := addr_toNat (a := addr) (i := 8) (by omega); simpa using this
  have h16 : (addr + 16).toNat = addr.toNat + 16 := by
    have := addr_toNat (a := addr) (i := 16) (by omega); simpa using this
  have hbytes := arrayBytes_eq_classBytes h.cls_lo h.cls_hi
  have hkind : val'.kind = val.kind := by cases val <;> rfl
  have hsz' : val'.size = val.size - 1 := by
    cases val <;> simp [val', ArrayVal.size]
  refine ⟨h.aligned, h.nonzero, h.cls_lo, h.cls_hi, h.refs_pos, h.refs_le, h.fit,
    by rw [hsz']; have := h.size_le; omega,
    by cases val <;> exact h.cap_fit,
    fun j hj => by simpa [Memory.write] using h.access j hj,
    ?_, ?_, ?_, ?_⟩
  · rw [hkind]
    exact h.header_word.write_disjoint (by rw [h8]; simp only [Width.bytes]; omega) (by omega)
      (by rw [h8]; simp only [Width.bytes]; omega)
  · rw [hsz']
    apply wordAt_write64
    intro k hk
    have hka : (addr + 8) + UInt64.ofNat k = addr + UInt64.ofNat (8 + k) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [h8]; omega), h8, addr_toNat (by omega)]
      omega
    rw [hka]
    exact (h.access (8 + k) (by omega)).1
  · exact h.cap_word.write_disjoint (by rw [h8]; simp [Width.bytes]; omega) (by rw [h16]; omega)
      (by rw [h8, h16]; simp only [Width.bytes]; omega)
  · cases val with
    | boxed elems =>
      intro j hj
      have hj' : j < elems.length := by simp at hj; omega
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      rw [List.getElem_dropLast]
      exact (h.payload j hj').write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)
    | limbs elems =>
      intro j hj
      have hj' : j < elems.length := by simp at hj; omega
      have hcap : cap ≤ wordCapOfClass cls := h.cap_fit
      have hsz : elems.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + 8 * j)).toNat =
          addr.toNat + (arrayPayloadOffset + 8 * j) := addr_toNat (by omega)
      rw [List.getElem_dropLast]
      exact (h.payload j hj').write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [hja]; omega) (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)
    | bytes data =>
      intro j hj
      have hj' : j < data.length := by simp at hj; omega
      have hcap : cap ≤ byteCapOfClass cls := h.cap_fit
      have hsz : data.length ≤ cap := h.size_le
      have hja : (addr + UInt64.ofNat (arrayPayloadOffset + j)).toNat =
          addr.toNat + (arrayPayloadOffset + j) := addr_toNat (by omega)
      rw [List.getElem_dropLast]
      exact (h.payload j hj').write_disjoint (by rw [h8]; simp [Width.bytes]; omega)
        (by rw [h8, hja]; simp [Width.bytes, arrayPayloadOffset]; omega)

/-! ## Immortal static `.rodata` array cells -/

/-- A read-only immortal array cell (such as one emitted into ELF `.rodata` by
`IxCC.X86.ELFRodata`). Notice NO `writable` permission is required. -/
structure StaticArrayCell (mem : Memory) (addr : Word) (cap : Nat) (val : ArrayVal) : Prop where
  aligned : addr.toNat % 8 = 0
  nonzero : addr ≠ 0
  size_le : val.size ≤ cap
  fit : addr.toNat + (match val with
    | .bytes _ => arrayPayloadOffset + cap
    | .boxed _ | .limbs _ => arrayPayloadOffset + 8 * cap) < 2 ^ 63
  header_word : WordAt mem addr (staticArrayHeader val.kind)
  size_word : WordAt mem (addr + 8) (UInt64.ofNat val.size)
  cap_word : WordAt mem (addr + 16) (UInt64.ofNat cap)
  payload : ArrayPayload mem addr val

theorem StaticArrayCell.pointer_branch {mem addr cap val}
    (h : StaticArrayCell mem addr cap val) :
    Cond.holds .tnz .w64 addr 1 = false := by
  have hbit : (addr &&& 1).toNat = 0 := by
    rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := h.aligned
    omega
  have hzero : addr &&& 1 = 0 := UInt64.toNat_inj.mp hbit
  simp [Cond.holds, Width.truncate, Width.mask, hzero]

theorem StaticArrayCell.count_load {mem addr cap val}
    (h : StaticArrayCell mem addr cap val) :
    loadWord mem .w32 .zero (addr + 4) = some (UInt64.ofNat Rt.immortalRc) := by
  have hfit8 : addr.toNat + 8 ≤ 2 ^ 64 := by
    have hf := h.fit
    cases val <;> simp [arrayPayloadOffset] at hf <;> omega
  have hr := wordAt_read32_hi h.header_word hfit8
  have hrc := (staticArrayHeader_fields val.kind).2.2.2
  have heq : staticArrayHeader val.kind >>> 32 = UInt64.ofNat Rt.immortalRc := by
    apply UInt64.toNat_inj.mp
    rw [hrc, UInt64.toNat_ofNat']
    rfl
  simp [loadWord, hr, heq]

theorem StaticArrayCell.rc_slt_zero :
    Cond.holds .slt .w32 (UInt64.ofNat Rt.immortalRc) 0 = true := by
  decide

theorem StaticArrayCell.rc_ne_zero :
    Cond.holds .eq .w32 (UInt64.ofNat Rt.immortalRc) 0 = false := by
  decide

/-! ### Bridges from `X86.ELFRodata.RodataMapped` to `StaticArrayCell` -/

private theorem wordAt_of_rodata_read64 {mem : Memory} {base : Word} {rodata : ByteArray}
    (hm : X86.ELFRodata.RodataMapped base rodata mem) {off : Nat} {w : Word}
    (hoff : off + 8 ≤ rodata.size)
    (hbytes : ∀ (j : Nat) (_hj : j < 8), rodata[off + j]'(by omega) = (w >>> UInt64.ofNat (8 * j)).toUInt8) :
    WordAt mem (base + UInt64.ofNat off) w where
  bytes j hj := by
    have hfit := hm.fit
    have haddr : base + UInt64.ofNat off + UInt64.ofNat j = base + UInt64.ofNat (off + j) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega),
        addr_toNat (by omega)]
      omega
    rw [haddr, hm.bytes_eq (off + j) (by omega), hbytes j hj]
  readable j hj := by
    have hfit := hm.fit
    have haddr : base + UInt64.ofNat off + UInt64.ofNat j = base + UInt64.ofNat (off + j) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega),
        addr_toNat (by omega)]
      omega
    rw [haddr]
    exact hm.readable (off + j) (by omega)

/-- Any static `ByteArray` emitted by `ELFRodata.encodeStaticByteArray` in a
`RodataMapped` ELF `.rodata` section satisfies `StaticArrayCell`. -/
theorem StaticArrayCell.ofRodataByteArray {mem : Memory} {base : Word} {rodata : ByteArray}
    {off : Nat} {bs : ByteArray}
    (hm : X86.ELFRodata.RodataMapped base rodata mem)
    (hoff_align : off % 8 = 0)
    (hnonzero : base + UInt64.ofNat off ≠ 0)
    (hbound : off + (X86.ELFRodata.encodeStaticByteArray bs).size ≤ rodata.size)
    (hslice : ∀ j (hj : j < (X86.ELFRodata.encodeStaticByteArray bs).size),
      rodata[off + j]'(by omega) = (X86.ELFRodata.encodeStaticByteArray bs)[j]'hj) :
    StaticArrayCell mem (base + UInt64.ofNat off) (X86.ELF.alignUp bs.size 8)
      (.bytes bs.data.toList) := by
  have hfit63 := hm.fit
  have haligned := hm.aligned
  let cap := X86.ELF.alignUp bs.size 8
  have henc_sz : (X86.ELFRodata.encodeStaticByteArray bs).size = 24 + cap :=
    X86.ELFRodata.encodeStaticByteArray_size bs
  have hpad_ge : bs.size ≤ cap := X86.ELFRodata.alignUp8_ge bs.size
  have hlen : bs.data.toList.length = bs.size := by
    change bs.data.size = bs.size; rfl
  have hbase_off : (base + UInt64.ofNat off).toNat = base.toNat + off := addr_toNat (by omega)
  have hword_at : ∀ (idx : Nat) (w : Word) (_hidx : idx < 3),
      (∀ (j : Nat) (_hj : j < 8), (X86.ELFRodata.encodeStaticByteArray bs)[8 * idx + j]'(by omega) =
        (w >>> UInt64.ofNat (8 * j)).toUInt8) →
      WordAt mem (base + UInt64.ofNat off + UInt64.ofNat (8 * idx)) w := by
    intro idx w hidx hbw
    have haddr : base + UInt64.ofNat off + UInt64.ofNat (8 * idx) =
        base + UInt64.ofNat (off + 8 * idx) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hbase_off]; omega), hbase_off, addr_toNat (by omega)]
      omega
    rw [haddr]
    apply wordAt_of_rodata_read64 hm (by omega)
    intro j hj
    have h1 := hslice (8 * idx + j) (by omega)
    simp only [Nat.add_assoc]
    rw [h1]
    exact hbw j hj
  let hdrs : List Word :=
    [X86.ELFRodata.staticHeader 0 X86.ELFRodata.tagByteArray,
      UInt64.ofNat bs.size, UInt64.ofNat cap]
  have hhdr_len : hdrs.length = 3 := rfl
  have hhdr_bytes : ∀ (idx : Nat) (hidx : idx < 3) (j : Nat) (hj : j < 8),
      (X86.ELFRodata.encodeStaticByteArray bs)[8 * idx + j]'(by omega) =
        ((hdrs[idx]'(by omega)) >>> UInt64.ofNat (8 * j)).toUInt8 := by
    intro idx hidx j hj
    unfold X86.ELFRodata.encodeStaticByteArray
    have hleft : 8 * idx + j < (X86.ELFRodata.encodeWords hdrs).size := by
      rw [X86.ELFRodata.encodeWords_size, hhdr_len]; omega
    rw [ByteArray.getElem_append_left hleft]
    exact X86.ELFRodata.encodeWords_getElem hdrs (by omega) hj
  refine ⟨by rw [hbase_off]; omega, hnonzero, by change bs.data.toList.length ≤ cap; rw [hlen]; exact hpad_ge,
    by dsimp only; rw [hbase_off]; unfold arrayPayloadOffset; omega, ?_, ?_, ?_, ?_⟩
  · have h0 := hword_at 0 (hdrs[0]'(by omega)) (by decide) (hhdr_bytes 0 (by decide))
    have hv0 : hdrs[0]'(by omega) = staticArrayHeader .bytes := rfl
    rw [hv0] at h0
    simpa [ArrayVal.kind] using h0
  · have h1 := hword_at 1 (hdrs[1]'(by omega)) (by decide) (hhdr_bytes 1 (by decide))
    have hv1 : hdrs[1]'(by omega) = UInt64.ofNat bs.size := rfl
    rw [hv1] at h1
    change WordAt mem (base + UInt64.ofNat off + 8) (UInt64.ofNat bs.data.toList.length)
    rw [hlen]
    exact h1
  · have h2 := hword_at 2 (hdrs[2]'(by omega)) (by decide) (hhdr_bytes 2 (by decide))
    have hv2 : hdrs[2]'(by omega) = UInt64.ofNat cap := rfl
    rw [hv2] at h2
    exact h2
  · intro j hj
    have hj' : j < bs.size := by omega
    have haddr : base + UInt64.ofNat off + UInt64.ofNat (arrayPayloadOffset + j) =
        base + UInt64.ofNat (off + (24 + j)) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hbase_off]; unfold arrayPayloadOffset; omega), hbase_off,
        addr_toNat (by omega)]
      unfold arrayPayloadOffset; omega
    rw [haddr]
    refine ⟨?_, hm.readable (off + (24 + j)) (by omega)⟩
    rw [hm.bytes_eq (off + (24 + j)) (by omega), hslice (24 + j) (by omega)]
    unfold X86.ELFRodata.encodeStaticByteArray
    have hws : (X86.ELFRodata.encodeWords hdrs).size = 24 := by
      rw [X86.ELFRodata.encodeWords_size, hhdr_len]
    rw [ByteArray.getElem_append_right (by change (X86.ELFRodata.encodeWords hdrs).size ≤ 24 + j; omega)]
    have hsub : 24 + j - (X86.ELFRodata.encodeWords hdrs).size = j := by rw [hws]; omega
    unfold X86.ELF.padTo
    have hidx_bs : 24 + j - (X86.ELFRodata.encodeWords
        [X86.ELFRodata.staticHeader 0 X86.ELFRodata.tagByteArray,
          UInt64.ofNat bs.size, UInt64.ofNat (X86.ELF.alignUp bs.size 8)]).size < bs.size := by
      change 24 + j - (X86.ELFRodata.encodeWords hdrs).size < bs.size
      omega
    rw [ByteArray.getElem_append_left hidx_bs]
    change bs[24 + j - (X86.ELFRodata.encodeWords hdrs).size]'(by omega) = bs.data.toList[j]'hj
    simp only [hsub]
    rfl

/-- Any static `Array UInt64` / `BigNat` limb cell emitted by
`ELFRodata.encodeStaticLimbArray` in a `RodataMapped` ELF `.rodata` section
satisfies `StaticArrayCell`. -/
theorem StaticArrayCell.ofRodataLimbArray {mem : Memory} {base : Word} {rodata : ByteArray}
    {off : Nat} {limbs : List Word}
    (hm : X86.ELFRodata.RodataMapped base rodata mem)
    (hoff_align : off % 8 = 0)
    (hnonzero : base + UInt64.ofNat off ≠ 0)
    (hbound : off + (X86.ELFRodata.encodeStaticLimbArray limbs).size ≤ rodata.size)
    (hslice : ∀ j (hj : j < (X86.ELFRodata.encodeStaticLimbArray limbs).size),
      rodata[off + j]'(by omega) = (X86.ELFRodata.encodeStaticLimbArray limbs)[j]'hj) :
    StaticArrayCell mem (base + UInt64.ofNat off) limbs.length (.limbs limbs) := by
  have hfit63 := hm.fit
  have haligned := hm.aligned
  let ws : List Word :=
    X86.ELFRodata.staticHeader 0 X86.ELFRodata.tagLimbArray ::
      UInt64.ofNat limbs.length :: UInt64.ofNat limbs.length :: limbs
  have henc_sz : (X86.ELFRodata.encodeStaticLimbArray limbs).size = 8 * ws.length := by
    unfold X86.ELFRodata.encodeStaticLimbArray
    exact X86.ELFRodata.encodeWords_size ws
  have hws_len : ws.length = 3 + limbs.length := by simp [ws]; omega
  have hbase_off : (base + UInt64.ofNat off).toNat = base.toNat + off := addr_toNat (by omega)
  have hword_at : ∀ (idx : Nat) (hidx : idx < ws.length),
      WordAt mem (base + UInt64.ofNat off + UInt64.ofNat (8 * idx)) (ws[idx]'hidx) := by
    intro idx hidx
    have haddr : base + UInt64.ofNat off + UInt64.ofNat (8 * idx) =
        base + UInt64.ofNat (off + 8 * idx) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hbase_off]; omega), hbase_off, addr_toNat (by omega)]
      omega
    rw [haddr]
    apply wordAt_of_rodata_read64 hm (by omega)
    intro j hj
    have h1 := hslice (8 * idx + j) (by omega)
    simp only [Nat.add_assoc]
    rw [h1]
    exact X86.ELFRodata.encodeWords_getElem ws hidx hj
  refine ⟨by rw [hbase_off]; omega, hnonzero, by simp [ArrayVal.size],
    by dsimp only; rw [hbase_off]; unfold arrayPayloadOffset; omega, ?_, ?_, ?_, ?_⟩
  · have h0 := hword_at 0 (by omega)
    have hv0 : ws[0]'(by omega) = staticArrayHeader .limbs := rfl
    rw [hv0] at h0
    simpa [ArrayVal.kind] using h0
  · have h1 := hword_at 1 (by omega)
    have hv1 : ws[1]'(by omega) = UInt64.ofNat limbs.length := rfl
    rw [hv1] at h1
    simpa [ArrayVal.size] using h1
  · have h2 := hword_at 2 (by omega)
    have hv2 : ws[2]'(by omega) = UInt64.ofNat limbs.length := rfl
    rw [hv2] at h2
    simpa using h2
  · intro j hj
    have h := hword_at (3 + j) (by omega)
    have hoff24 : 8 * (3 + j) = arrayPayloadOffset + 8 * j := by unfold arrayPayloadOffset; omega
    have hvj : ws[3 + j]'(by omega) = limbs[j]'hj := by
      simp [ws, Nat.add_comm 3 j]
    rw [hoff24, hvj] at h
    exact h

/-- Any static boxed array cell emitted by `ELFRodata.encodeStaticBoxedArray`
satisfies `StaticArrayCell`. -/
theorem StaticArrayCell.ofRodataBoxedArray {mem : Memory} {base : Word} {rodata : ByteArray}
    {off : Nat} {elems : List Word}
    (hm : X86.ELFRodata.RodataMapped base rodata mem)
    (hoff_align : off % 8 = 0)
    (hnonzero : base + UInt64.ofNat off ≠ 0)
    (hbound : off + (X86.ELFRodata.encodeStaticBoxedArray elems).size ≤ rodata.size)
    (hslice : ∀ j (hj : j < (X86.ELFRodata.encodeStaticBoxedArray elems).size),
      rodata[off + j]'(by omega) = (X86.ELFRodata.encodeStaticBoxedArray elems)[j]'hj) :
    StaticArrayCell mem (base + UInt64.ofNat off) elems.length (.boxed elems) := by
  have hfit63 := hm.fit
  have haligned := hm.aligned
  let ws : List Word :=
    X86.ELFRodata.staticHeader X86.ELFRodata.scanBoxedArray X86.ELFRodata.tagBoxedArray ::
      UInt64.ofNat elems.length :: UInt64.ofNat elems.length :: elems
  have henc_sz : (X86.ELFRodata.encodeStaticBoxedArray elems).size = 8 * ws.length := by
    unfold X86.ELFRodata.encodeStaticBoxedArray
    exact X86.ELFRodata.encodeWords_size ws
  have hws_len : ws.length = 3 + elems.length := by simp [ws]; omega
  have hbase_off : (base + UInt64.ofNat off).toNat = base.toNat + off := addr_toNat (by omega)
  have hword_at : ∀ (idx : Nat) (hidx : idx < ws.length),
      WordAt mem (base + UInt64.ofNat off + UInt64.ofNat (8 * idx)) (ws[idx]'hidx) := by
    intro idx hidx
    have haddr : base + UInt64.ofNat off + UInt64.ofNat (8 * idx) =
        base + UInt64.ofNat (off + 8 * idx) := by
      apply UInt64.toNat_inj.mp
      rw [addr_toNat (by rw [hbase_off]; omega), hbase_off, addr_toNat (by omega)]
      omega
    rw [haddr]
    apply wordAt_of_rodata_read64 hm (by omega)
    intro j hj
    have h1 := hslice (8 * idx + j) (by omega)
    simp only [Nat.add_assoc]
    rw [h1]
    exact X86.ELFRodata.encodeWords_getElem ws hidx hj
  refine ⟨by rw [hbase_off]; omega, hnonzero, by simp [ArrayVal.size],
    by dsimp only; rw [hbase_off]; unfold arrayPayloadOffset; omega, ?_, ?_, ?_, ?_⟩
  · have h0 := hword_at 0 (by omega)
    have hv0 : ws[0]'(by omega) = staticArrayHeader .boxed := rfl
    rw [hv0] at h0
    simpa [ArrayVal.kind] using h0
  · have h1 := hword_at 1 (by omega)
    have hv1 : ws[1]'(by omega) = UInt64.ofNat elems.length := rfl
    rw [hv1] at h1
    simpa [ArrayVal.size] using h1
  · have h2 := hword_at 2 (by omega)
    have hv2 : ws[2]'(by omega) = UInt64.ofNat elems.length := rfl
    rw [hv2] at h2
    simpa using h2
  · intro j hj
    have h := hword_at (3 + j) (by omega)
    have hoff24 : 8 * (3 + j) = arrayPayloadOffset + 8 * j := by unfold arrayPayloadOffset; omega
    have hvj : ws[3 + j]'(by omega) = elems[j]'hj := by
      simp [ws, Nat.add_comm 3 j]
    rw [hoff24, hvj] at h
    exact h

/-! ## Array allocator invariant (compatible with `Rt.Rc.Gen.AllocatorReady`) -/

/-- Physical allocator state for the 71-class counted heap used by contiguous
arrays and general constructor cells alike. -/
structure ArrayAllocator (mem : Memory) (context base bump limit : Word)
    (freeLists : Nat → List Word) : Prop where
  context_lower : 40 ≤ context.toNat
  context_fit : context.toNat + 8 * (maxClass + 1) < 2 ^ 63
  context_before : context.toNat + 8 * (maxClass + 1) ≤ base.toNat
  base_le_bump : base.toNat ≤ bump.toNat
  bump_le_limit : bump.toNat ≤ limit.toNat
  limit_fit : limit.toNat < 2 ^ 63
  bump_aligned : bump.toNat % 8 = 0
  bump_word : WordAt mem (bumpAddress context) bump
  limit_word : WordAt mem (limitAddress context) limit
  bump_writable : ∀ j < 8, mem.writable (bumpAddress context + UInt64.ofNat j) = true
  arena_access : ∀ addr : Word, base.toNat ≤ addr.toNat → addr.toNat < limit.toNat →
    mem.readable addr = true ∧ mem.writable addr = true
  free_heads : ∀ cls, 1 ≤ cls → cls ≤ maxClass →
    WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) ((freeLists cls).headD 0)
  head_writable : ∀ cls, 1 ≤ cls → cls ≤ maxClass → ∀ j < 8,
    mem.writable (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat j) = true
  free_chains : ∀ cls, FreeChain mem (freeLists cls)
  free_distinct : ∀ cls, (freeLists cls).Nodup
  free_cls_pos : ∀ cls a, a ∈ freeLists cls → 1 ≤ cls ∧ cls ≤ maxClass
  free_in_arena : ∀ cls a, a ∈ freeLists cls →
    base.toNat ≤ a.toNat ∧ a.toNat + classBytes cls ≤ bump.toNat ∧ a.toNat % 8 = 0 ∧ a ≠ 0
  free_disjoint : ∀ c₁ c₂ a₁ a₂, a₁ ∈ freeLists c₁ → a₂ ∈ freeLists c₂ →
    (c₁ = c₂ ∧ a₁ = a₂) ∨
      a₁.toNat + classBytes c₁ ≤ a₂.toNat ∨
      a₂.toNat + classBytes c₂ ≤ a₁.toNat

private theorem slot_in_arena_of_partition {cmax heap addresses base bump limit slots}
    (hp : IxCC.Rt.Rc.Gen.ArenaPartition cmax heap addresses base bump limit slots)
    (hctx : 40 ≤ base.toNat)
    {slot : IxCC.Rt.Rc.Procs.Slot} (hmem : slot ∈ slots) :
    base.toNat ≤ slot.address.toNat ∧ slot.address.toNat + classBytes slot.cls ≤ bump.toNat ∧
      slot.address.toNat % 8 = 0 ∧ slot.address ≠ 0 := by
  have hv := hp.valid slot hmem
  have hnz : slot.address ≠ 0 := by
    intro h0; rw [h0] at hv; simp at hv; omega
  exact ⟨hv.2.2.2.1, by simpa [classBytes] using hv.2.2.2.2.1, hv.2.2.1, hnz⟩

/-- Compatibility bridge: any `Rt.Rc.Gen.AllocatorReady` heap state immediately
satisfies `ArrayAllocator` with the exact same context, arena, and 71 free lists. -/
theorem allocatorReady_toArrayAllocator
    {cmax heap addresses mem external context base bump limit slots lists}
    (h : IxCC.Rt.Rc.Gen.AllocatorReady cmax heap addresses mem external context base bump limit slots lists) :
    ArrayAllocator mem context base bump limit lists := by
  have hp := h.idle.partition
  have hbase40 : 40 ≤ base.toNat := by
    have := h.context_lower
    have := h.context_before
    omega
  refine ⟨h.context_lower, h.idle.context_fit, h.context_before,
    hp.bounds.1, hp.bounds.2.1, hp.bounds.2.2, h.bump_aligned,
    h.bump_word, h.limit_word, h.bump_writable, h.arena_access,
    h.idle.free_heads, h.idle.head_writable, h.idle.free_chains,
    h.idle.free_distinct, ?_, ?_, ?_⟩
  · intro cls a ha
    obtain ⟨slot, hmem, _, hcls, _⟩ := h.idle.free_placed cls a ha
    subst hcls
    have hv := hp.valid slot hmem
    exact ⟨hv.1, hv.2.1⟩
  · intro cls a ha
    obtain ⟨slot, hmem, haddr, hcls, _⟩ := h.idle.free_placed cls a ha
    subst haddr; subst hcls
    exact slot_in_arena_of_partition hp hbase40 hmem
  · intro c₁ c₂ a₁ a₂ ha₁ ha₂
    obtain ⟨s₁, hm₁, haddr₁, hc₁, _⟩ := h.idle.free_placed c₁ a₁ ha₁
    obtain ⟨s₂, hm₂, haddr₂, hc₂, _⟩ := h.idle.free_placed c₂ a₂ ha₂
    obtain ⟨i, hi, hsi⟩ := List.getElem_of_mem hm₁
    obtain ⟨j, hj, hsj⟩ := List.getElem_of_mem hm₂
    by_cases hij : i = j
    · subst hij
      have heq : s₁ = s₂ := hsi.symm.trans hsj
      subst heq
      exact Or.inl ⟨hc₁.symm.trans hc₂, haddr₁.symm.trans haddr₂⟩
    · have hsep := hp.disjoint i j s₁ s₂
        (by rw [List.getElem?_eq_getElem hi, hsi])
        (by rw [List.getElem?_eq_getElem hj, hsj]) hij
      rw [haddr₁, haddr₂, hc₁, hc₂] at hsep
      exact Or.inr (by simpa [classBytes] using hsep)

end IxCC.Rt.Rc.Array
