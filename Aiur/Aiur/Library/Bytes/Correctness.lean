import Aiur.Library.Bytes
import Aiur.Library.List.Correctness

/-!
# Mathematical and Heap Specifications of `Aiur.Library.Bytes` and Byte Streams

This module establishes:
1. Canonical `SourceValue F` representation predicates `RepAddress` (`[UInt8::U8; 32]`),
   `RepAddressRef` (`&[UInt8::U8; 32]`), and `RepByteStream` (`Lists::List<UInt8::U8>`)
   along with their `HeapMono` / `HeapMono₂` proofs.
2. Soundness and completeness of `Bytes::address_eq_tail` and `Bytes::address_eq`
   under `[Field F] [DecidableEq F] (large : U64.Compatible F)`:
   `addressEq F a b = if a = b then 1 else 0` (`1` iff `a = b`, `0` iff `a ≠ b`).
3. Mathematical and heap specifications of `read_byte_stream` and
   `read_finite_byte_stream`: reading `len` bytes from an I/O stream starting at
   `idx` produces a heap-extended `RepByteStream` of length `len` (with
   `len < 2^32` enforced by `WordLists::depth_checked`).
-/

namespace Aiur.Library.Bytes

open Aiur

variable {F : Type}

/-! ### 1. Representation Predicates (`RepAddress`, `RepAddressRef`, `RepByteStream`) and `HeapMono` -/

/-- A 32-byte address (`Bytes::Address = [UInt8::U8; 32]`). -/
abbrev Address := Vector UInt8 32

/-- Canonical `SourceValue F` representation of `Bytes::Address = [UInt8::U8; 32]`. -/
def RepAddress [NatCast F] (_h : Heap F) (addr : Address) (v : SourceValue F) : Prop :=
  v = .tuple (addr.toList.map fun b => .field (b.toNat : F))

theorem repAddress_heapMono₂ [NatCast F] : HeapMono₂ (RepAddress (F := F)) :=
  fun _ _ _ _ _ h => h

theorem repAddress_heapMono [NatCast F] (addr : Address) :
    HeapMono (fun h v => RepAddress (F := F) h addr v) :=
  HeapMono.of_heapMono₂ repAddress_heapMono₂ addr

/-- Canonical `SourceValue F` representation of `Bytes::AddressRef = &Bytes::Address`. -/
def RepAddressRef [NatCast F] (ty : Ty) (h : Heap F) (addr : Address) (ptr : SourceValue F) : Prop :=
  DerefTyped ty (fun h v => RepAddress h addr v) h ptr

theorem repAddressRef_heapMono₂ [NatCast F] (ty : Ty) :
    HeapMono₂ (RepAddressRef (F := F) ty) :=
  fun _ _ addr _ ext h => HeapMono.derefTyped (repAddress_heapMono addr) ext h

theorem repAddressRef_heapMono [NatCast F] (ty : Ty) (addr : Address) :
    HeapMono (fun h ptr => RepAddressRef (F := F) ty h addr ptr) :=
  HeapMono.derefTyped (repAddress_heapMono addr)

/-- Canonical `SourceValue F` representation of `Bytes::Stream = Lists::List<UInt8::U8>`. -/
abbrev RepByteStream [NatCast F] (enumName : String) (h : Heap F)
    (bytes : _root_.List UInt8) (ptr : SourceValue F) : Prop :=
  List.RepList enumName RepU8 h bytes ptr

theorem repByteStream_heapMono₂ [NatCast F] (enumName : String) :
    HeapMono₂ (RepByteStream (F := F) enumName) :=
  List.repList_heapMono₂ enumName repU8_heapMono₂

theorem repByteStream_heapMono [NatCast F] (enumName : String) (bytes : _root_.List UInt8) :
    HeapMono (fun h ptr => RepByteStream (F := F) enumName h bytes ptr) :=
  List.repList_heapMono enumName repU8_heapMono₂ bytes

/-! ### 2. `Bytes::address_eq_tail` and `Bytes::address_eq` Correctness -/

/-- Packed 7-byte field limb `pa1` (`Bytes::address_eq_tail`, lines 27-29). -/
def limb1 (F : Type) [Field F] (a : Address) : F :=
  ((((((a[7].toNat : F) * 256 + (a[6].toNat : F)) * 256 +
       (a[5].toNat : F)) * 256 + (a[4].toNat : F)) * 256 +
       (a[3].toNat : F)) * 256 + (a[2].toNat : F)) * 256 + (a[1].toNat : F)

/-- Packed 7-byte field limb `pa2` (`Bytes::address_eq_tail`, lines 35-37). -/
def limb2 (F : Type) [Field F] (a : Address) : F :=
  ((((((a[14].toNat : F) * 256 + (a[13].toNat : F)) * 256 +
       (a[12].toNat : F)) * 256 + (a[11].toNat : F)) * 256 +
       (a[10].toNat : F)) * 256 + (a[9].toNat : F)) * 256 + (a[8].toNat : F)

/-- Packed 7-byte field limb `pa3` (`Bytes::address_eq_tail`, lines 43-46). -/
def limb3 (F : Type) [Field F] (a : Address) : F :=
  ((((((a[21].toNat : F) * 256 + (a[20].toNat : F)) * 256 +
       (a[19].toNat : F)) * 256 + (a[18].toNat : F)) * 256 +
       (a[17].toNat : F)) * 256 + (a[16].toNat : F)) * 256 + (a[15].toNat : F)

/-- Packed 7-byte field limb `pa4` (`Bytes::address_eq_tail`, lines 53-56). -/
def limb4 (F : Type) [Field F] (a : Address) : F :=
  ((((((a[28].toNat : F) * 256 + (a[27].toNat : F)) * 256 +
       (a[26].toNat : F)) * 256 + (a[25].toNat : F)) * 256 +
       (a[24].toNat : F)) * 256 + (a[23].toNat : F)) * 256 + (a[22].toNat : F)

/-- Packed 3-byte field limb `pa5` (`Bytes::address_eq_tail`, lines 63-64). -/
def limb5 (F : Type) [Field F] (a : Address) : F :=
  ((a[31].toNat : F) * 256 + (a[30].toNat : F)) * 256 + (a[29].toNat : F)

/-- Exact field-level mirror of `Bytes::address_eq_tail(a, b)`. -/
def addressEqTail (F : Type) [Field F] [DecidableEq F] (a b : Address) : F :=
  if limb1 F a - limb1 F b = 0 then
    if limb2 F a - limb2 F b = 0 then
      if limb3 F a - limb3 F b = 0 then
        if limb4 F a - limb4 F b = 0 then
          if limb5 F a - limb5 F b = 0 then 1 else 0
        else 0
      else 0
    else 0
  else 0

/-- Exact field-level mirror of `Bytes::address_eq(a, b)`. -/
def addressEq (F : Type) [Field F] [DecidableEq F] (a b : Address) : F :=
  if (a[0].toNat : F) - (b[0].toNat : F) = 0 then
    addressEqTail F a b
  else 0

private theorem limb_pack56_eq [Field F] (x0 x1 x2 x3 x4 x5 x6 : UInt8) :
    ((((((x6.toNat : F) * 256 + (x5.toNat : F)) * 256 +
         (x4.toNat : F)) * 256 + (x3.toNat : F)) * 256 +
         (x2.toNat : F)) * 256 + (x1.toNat : F)) * 256 + (x0.toNat : F) =
      ((U64.pack56 x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat x5.toNat x6.toNat : Nat) : F) := by
  unfold U64.pack56
  push_cast
  ring

private theorem limb7_sub_eq_zero_iff [Field F] (large : U64.Compatible F)
    (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : UInt8) :
    (((((((a6.toNat : F) * 256 + (a5.toNat : F)) * 256 +
          (a4.toNat : F)) * 256 + (a3.toNat : F)) * 256 +
          (a2.toNat : F)) * 256 + (a1.toNat : F)) * 256 + (a0.toNat : F)) -
    (((((((b6.toNat : F) * 256 + (b5.toNat : F)) * 256 +
          (b4.toNat : F)) * 256 + (b3.toNat : F)) * 256 +
          (b2.toNat : F)) * 256 + (b1.toNat : F)) * 256 + (b0.toNat : F)) = 0 ↔
      a0.toNat = b0.toNat ∧ a1.toNat = b1.toNat ∧ a2.toNat = b2.toNat ∧
      a3.toNat = b3.toNat ∧ a4.toNat = b4.toNat ∧ a5.toNat = b5.toNat ∧
      a6.toNat = b6.toNat := by
  rw [limb_pack56_eq, limb_pack56_eq, sub_eq_zero]
  constructor
  · intro h
    have hl := U64.natCast_inj large
      (U64.pack56_lt a0.toNat_lt a1.toNat_lt a2.toNat_lt a3.toNat_lt a4.toNat_lt a5.toNat_lt a6.toNat_lt)
      (U64.pack56_lt b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt b4.toNat_lt b5.toNat_lt b6.toNat_lt) h
    exact (U64.pack56_inj
      a0.toNat_lt a1.toNat_lt a2.toNat_lt a3.toNat_lt a4.toNat_lt a5.toNat_lt a6.toNat_lt
      b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt b4.toNat_lt b5.toNat_lt b6.toNat_lt).mp hl
  · rintro ⟨e0, e1, e2, e3, e4, e5, e6⟩
    rw [e0, e1, e2, e3, e4, e5, e6]

private theorem limb3_sub_eq_zero_iff [Field F] (large : U64.Compatible F)
    (a0 a1 a2 b0 b1 b2 : UInt8) :
    (((a2.toNat : F) * 256 + (a1.toNat : F)) * 256 + (a0.toNat : F)) -
    (((b2.toNat : F) * 256 + (b1.toNat : F)) * 256 + (b0.toNat : F)) = 0 ↔
      a0.toNat = b0.toNat ∧ a1.toNat = b1.toNat ∧ a2.toNat = b2.toNat := by
  have ha : ((a2.toNat : F) * 256 + (a1.toNat : F)) * 256 + (a0.toNat : F) =
      ((U32.pack a0.toNat a1.toNat a2.toNat 0 : Nat) : F) := by
    unfold U32.pack; push_cast; ring
  have hb : ((b2.toNat : F) * 256 + (b1.toNat : F)) * 256 + (b0.toNat : F) =
      ((U32.pack b0.toNat b1.toNat b2.toNat 0 : Nat) : F) := by
    unfold U32.pack; push_cast; ring
  rw [ha, hb, sub_eq_zero]
  constructor
  · intro h
    have ha0 := a0.toNat_lt; have ha1 := a1.toNat_lt; have ha2 := a2.toNat_lt
    have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt
    have hl := U64.natCast_inj large
      (by unfold U32.pack U64.fieldBound; omega)
      (by unfold U32.pack U64.fieldBound; omega) h
    unfold U32.pack at hl
    omega
  · rintro ⟨e0, e1, e2⟩
    rw [e0, e1, e2]

private theorem byte0_sub_eq_zero_iff [Field F] (large : U64.Compatible F)
    (a0 b0 : UInt8) :
    (a0.toNat : F) - (b0.toNat : F) = 0 ↔ a0.toNat = b0.toNat := by
  rw [sub_eq_zero]
  constructor
  · intro h
    exact U64.natCast_inj large
      (by have := a0.toNat_lt; unfold U64.fieldBound; omega)
      (by have := b0.toNat_lt; unfold U64.fieldBound; omega) h
  · intro h
    rw [h]

/-- `Bytes::address_eq(a, b)` returns `1` if `a = b` and `0` if `a ≠ b`. -/
theorem address_eq_spec [Field F] [DecidableEq F] (large : U64.Compatible F)
    (a b : Address) :
    addressEq F a b = if a = b then 1 else 0 := by
  unfold addressEq addressEqTail
  by_cases hab : a = b
  · subst hab
    simp
  · simp only [hab, ↓reduceIte]
    split_ifs with h0 h1 h2 h3 h4 h5
    · exfalso
      apply hab
      replace h0 := (byte0_sub_eq_zero_iff large _ _).mp h0
      replace h1 := (limb7_sub_eq_zero_iff large _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h1
      replace h2 := (limb7_sub_eq_zero_iff large _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h2
      replace h3 := (limb7_sub_eq_zero_iff large _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h3
      replace h4 := (limb7_sub_eq_zero_iff large _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h4
      replace h5 := (limb3_sub_eq_zero_iff large _ _ _ _ _ _).mp h5
      ext i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
             i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
             i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
             i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2.1
      · exact h1.2.2.2.2.1
      · exact h1.2.2.2.2.2.1
      · exact h1.2.2.2.2.2.2
      · exact h2.1
      · exact h2.2.1
      · exact h2.2.2.1
      · exact h2.2.2.2.1
      · exact h2.2.2.2.2.1
      · exact h2.2.2.2.2.2.1
      · exact h2.2.2.2.2.2.2
      · exact h3.1
      · exact h3.2.1
      · exact h3.2.2.1
      · exact h3.2.2.2.1
      · exact h3.2.2.2.2.1
      · exact h3.2.2.2.2.2.1
      · exact h3.2.2.2.2.2.2
      · exact h4.1
      · exact h4.2.1
      · exact h4.2.2.1
      · exact h4.2.2.2.1
      · exact h4.2.2.2.2.1
      · exact h4.2.2.2.2.2.1
      · exact h4.2.2.2.2.2.2
      · exact h5.1
      · exact h5.2.1
      · exact h5.2.2
    all_goals rfl

theorem address_eq_one_iff [Field F] [DecidableEq F] (large : U64.Compatible F)
    (a b : Address) :
    addressEq F a b = 1 ↔ a = b := by
  rw [address_eq_spec large]
  by_cases h : a = b <;> simp [h]

theorem address_eq_zero_iff [Field F] [DecidableEq F] (large : U64.Compatible F)
    (a b : Address) :
    addressEq F a b = 0 ↔ a ≠ b := by
  rw [address_eq_spec large]
  by_cases h : a = b <;> simp [h]

/-! ### 3. `read_byte_stream` and `read_finite_byte_stream` Specifications -/

/-- Pure specification of `read_byte_stream(channel, idx, len)`: reads `len`
consecutive bytes starting at `idx` from the channel's byte stream `stream`. -/
def readByteStream (stream : Nat → UInt8) (idx : Nat) : Nat → _root_.List UInt8
  | 0 => []
  | len + 1 => stream idx :: readByteStream stream (idx + 1) len

theorem read_byte_stream_length (stream : Nat → UInt8) (idx len : Nat) :
    (readByteStream stream idx len).length = len := by
  induction len generalizing idx with
  | zero => rfl
  | succ len ih => simp [readByteStream, ih]

theorem read_byte_stream_getElem (stream : Nat → UInt8) (idx len i : Nat) (hi : i < len) :
    (readByteStream stream idx len)[i]'(by rw [read_byte_stream_length]; exact hi) =
      stream (idx + i) := by
  induction len generalizing idx i with
  | zero => omega
  | succ len ih =>
      cases i with
      | zero => simp [readByteStream]
      | succ i =>
          simp only [readByteStream, _root_.List.getElem_cons_succ]
          rw [ih (idx + 1) i (by omega)]
          congr 1
          omega

/-- Allocate a `Bytes::Stream` (`Lists::List<UInt8::U8>`) in `h : Heap F`. -/
def allocByteStream [NatCast F] (enumName : String) (h : Heap F)
    (bytes : _root_.List UInt8) : SourceValue F × Heap F :=
  List.allocValues enumName h (bytes.map fun b => .field (b.toNat : F))

theorem alloc_byte_stream_extends [NatCast F] (enumName : String)
    (h : Heap F) (bytes : _root_.List UInt8) :
    Heap.Extends h (allocByteStream (F := F) enumName h bytes).2 :=
  List.allocValues_extends enumName h _

theorem alloc_byte_stream_rep [NatCast F] (enumName : String)
    (h : Heap F) (bytes : _root_.List UInt8) :
    RepByteStream enumName (allocByteStream (F := F) enumName h bytes).2
      bytes (allocByteStream (F := F) enumName h bytes).1 := by
  apply List.allocValues_rep enumName repU8_heapMono₂ h
  rw [_root_.List.forall₂_map_right_iff]
  exact _root_.List.forall₂_same.mpr (fun _ _ => rfl)

/-- Specification of `read_byte_stream`: reading `len` bytes from `stream` at `idx`
and allocating the resulting `Lists::Node` chain extends the heap and produces a
valid `RepByteStream` of length `len`. -/
theorem read_byte_stream_spec [NatCast F] (enumName : String)
    (stream : Nat → UInt8) (idx len : Nat) (h : Heap F) :
    let bytes := readByteStream stream idx len
    let allocated := allocByteStream (F := F) enumName h bytes
    Heap.Extends h allocated.2 ∧
      RepByteStream enumName allocated.2 bytes allocated.1 ∧
      bytes.length = len :=
  ⟨alloc_byte_stream_extends enumName h _,
   alloc_byte_stream_rep enumName h _,
   read_byte_stream_length stream idx len⟩

/-- Specification of `read_finite_byte_stream`: `read_byte_stream` followed by
`WordLists::depth_checked` succeeds iff `len < 2^32`, producing a heap-extended
`RepByteStream` of length `len < 2^32`. -/
theorem read_finite_byte_stream_spec [NatCast F] (enumName : String)
    (stream : Nat → UInt8) (idx len : Nat) (h : Heap F) :
    let bytes := readByteStream stream idx len
    let allocated := allocByteStream (F := F) enumName h bytes
    (List.Word.depthChecked bytes = some len ↔ len < U32.base) ∧
      Heap.Extends h allocated.2 ∧
      RepByteStream enumName allocated.2 bytes allocated.1 ∧
      bytes.length = len := by
  refine ⟨?_, read_byte_stream_spec enumName stream idx len h⟩
  rw [List.Word.depth_checked_some_iff, read_byte_stream_length]
  simp

end Aiur.Library.Bytes
