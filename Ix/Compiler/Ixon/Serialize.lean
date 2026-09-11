import Std

/-!
# Ixon serialization primitives

Byte-level plumbing for the Ixon v2 codec, mirroring ix's format family
(`ix/Ix/Ixon.lean`): `PutM`/`GetM`, minimal little-endian u64s, and the
`Tag0`/`Tag2`/`Tag4` headers.

v2 decoders are **strict**: non-minimal size encodings, large-form sizes
that fit the small form, and trailing bytes are all rejected. They are
designed so byte-equality and value-equality coincide — content addressing
demands exactly one spelling per value — with the global `RoundtripLaw` and
`CanonicalLaw` proofs still tracked explicitly below.
-/

namespace Ix.Compiler.Ixon

/-- External store/protocol identifier for these bytes. Individual Merkle-DAG
objects deliberately carry no redundant in-band version prefix. -/
def wireFormatId : String := "ixon-v2"

/-- Serialization writer monad: accumulate bytes. -/
abbrev PutM := StateM ByteArray

/-- Deserialization state: input bytes and cursor. -/
structure GetState where
  bytes : ByteArray
  idx : Nat

/-- Deserialization monad: cursor over bytes, `String` errors. -/
abbrev GetM := StateT GetState (Except String)

def runPut (m : PutM Unit) : ByteArray :=
  (m.run .empty).2

/-- Run a decoder, requiring full consumption of the input. -/
def runGet (m : GetM α) (bytes : ByteArray) : Except String α := do
  let (a, st) ← m.run ⟨bytes, 0⟩
  if st.idx != st.bytes.size then
    throw s!"trailing bytes: consumed {st.idx} of {st.bytes.size}"
  return a

class Serialize (α : Type) where
  put : α → PutM Unit
  get : GetM α

def ser [Serialize α] (a : α) : ByteArray :=
  runPut (Serialize.put a)

def de [Serialize α] (bytes : ByteArray) : Except String α :=
  runGet Serialize.get bytes

/-! ## Codec laws

These propositions separate the two global proof obligations. Total codec
definitions make them ordinary kernel statements rather than claims about
opaque `partial` implementations. -/

/-- Encoding followed by strict decoding returns the original value. -/
def RoundtripLaw (α : Type) [Serialize α] : Prop :=
  ∀ a : α, de (ser a) = .ok a

/-- Every accepted byte string is exactly the encoder's canonical spelling
of its decoded value. Full consumption is already part of `de`. -/
def CanonicalLaw (α : Type) [Serialize α] : Prop :=
  ∀ (bytes : ByteArray) (a : α), de bytes = .ok a → ser a = bytes

/-! Cursor-relative specifications are the compositional proof layer beneath
the global laws. A writer appends exactly `output`; a reader consumes exactly
`input` while leaving arbitrary surrounding bytes untouched. -/

/-- A successful unit writer appends exactly `output`. -/
def PutSpec (put : PutM Unit) (output : ByteArray) : Prop :=
  ∀ pre, put.run pre = ((), pre ++ output)

/-- A reader consumes exactly `input`, from an arbitrary cursor, and returns
`value` without changing either the preceding or following bytes. -/
def GetSpec (get : GetM α) (input : ByteArray) (value : α) : Prop :=
  ∀ pre suffix,
    get.run ⟨pre ++ input ++ suffix, pre.size⟩ =
      .ok (value,
        ⟨pre ++ input ++ suffix, pre.size + input.size⟩)

/-- Converse reader specification: every successful parse consumes the
canonical encoding of its result and leaves an arbitrary suffix untouched. -/
def GetCanonical (get : GetM α) (encode : α → ByteArray) : Prop :=
  ∀ (pre rest : ByteArray) {value : α} {st' : GetState},
    get.run ⟨pre ++ rest, pre.size⟩ = .ok (value, st') →
    ∃ suffix,
      rest = encode value ++ suffix ∧
      st' = ⟨pre ++ rest, pre.size + (encode value).size⟩

/-- Sequential writer specifications compose by byte-array append. -/
theorem PutSpec.seq {left right : PutM Unit} {leftBytes rightBytes : ByteArray}
    (hleft : PutSpec left leftBytes) (hright : PutSpec right rightBytes) :
    PutSpec (left >>= fun _ => right) (leftBytes ++ rightBytes) := by
  intro pre
  simp only [StateT.run_bind]
  rw [hleft pre]
  change right.run (pre ++ leftBytes) = _
  rw [hright (pre ++ leftBytes)]
  simp [ByteArray.append_assoc]

/-- Sequential reader specifications compose by byte-array append. -/
theorem GetSpec.bind {get : GetM α} {next : α → GetM β}
    {left right : ByteArray} {value : α} {result : β}
    (hget : GetSpec get left value)
    (hnext : GetSpec (next value) right result) :
    GetSpec (get >>= next) (left ++ right) result := by
  intro pre suffix
  simp only [StateT.run_bind]
  have hbytes : pre ++ (left ++ right) ++ suffix =
      pre ++ left ++ (right ++ suffix) := by
    simp [ByteArray.append_assoc]
  rw [hbytes, hget pre (right ++ suffix)]
  change (next value).run
    ⟨pre ++ left ++ (right ++ suffix), pre.size + left.size⟩ = _
  have hpre : (pre ++ left).size = pre.size + left.size :=
    ByteArray.size_append
  rw [← hpre]
  simpa [ByteArray.append_assoc, ByteArray.size_append, Nat.add_assoc] using
    hnext (pre ++ left) suffix

/-- A pure reader returns its value without consuming bytes. -/
theorem GetSpec.pure (value : α) :
    GetSpec (pure value) ByteArray.empty value := by
  intro pre suffix
  simp
  rfl

/-- A writer specification determines its top-level output. -/
theorem runPut_eq_of_spec {put : PutM Unit} {bytes : ByteArray}
    (h : PutSpec put bytes) : runPut put = bytes := by
  simpa [runPut] using congrArg Prod.snd (h .empty)

/-- A reader specification determines strict decoding of its exact input. -/
theorem runGet_eq_ok_of_spec {get : GetM α} {bytes : ByteArray} {value : α}
    (h : GetSpec get bytes value) : runGet get bytes = .ok value := by
  simp only [runGet]
  have hrun := h .empty .empty
  simp only [ByteArray.empty_append, ByteArray.append_empty, ByteArray.size_empty,
    Nat.zero_add] at hrun
  rw [hrun]
  simp only [bind, Except.bind]
  simp
  rfl

/-- A roundtrip proof immediately makes content serialization injective. -/
theorem ser_injective_of_roundtrip [Serialize α] (h : RoundtripLaw α) :
    Function.Injective (ser (α := α)) := by
  intro a b hab
  have ha := h a
  have hb := h b
  rw [hab, hb] at ha
  cases ha
  rfl

/-- Canonical decoding permits at most one accepted byte spelling per value. -/
theorem accepted_bytes_unique_of_canonical [Serialize α]
    (h : CanonicalLaw α) {a : α} {left right : ByteArray}
    (hl : de left = .ok a) (hr : de right = .ok a) : left = right :=
  (h left a hl).symm.trans (h right a hr)

/-! ## Primitives -/

def putU8 (x : UInt8) : PutM Unit :=
  modify fun s => s.push x

/-- The one-byte output used by the primitive byte codec. -/
def u8Bytes (x : UInt8) : ByteArray :=
  [x].toByteArray

def getU8 : GetM UInt8 := do
  let st ← get
  if h : st.idx < st.bytes.size then
    let b := st.bytes[st.idx]
    set { st with idx := st.idx + 1 }
    return b
  else
    throw "EOF"

theorem putU8_spec (x : UInt8) : PutSpec (putU8 x) (u8Bytes x) := by
  intro pre
  change ((), pre.push x) = ((), pre ++ u8Bytes x)
  congr 1
  rw [u8Bytes, ByteArray.append_toByteArray_singleton]

theorem getU8_spec (x : UInt8) : GetSpec getU8 (u8Bytes x) x := by
  intro pre suffix
  have hidx : pre.size < pre.size + 1 + suffix.size := by omega
  simp [getU8, u8Bytes, hidx]
  have hget (h : pre.size < (pre.push x).size) :
      (pre.push x)[pre.size]'h = x := by
    rcases pre with ⟨data⟩
    exact Array.getElem_push_eq
  rw [hget]
  rfl

/-- Count bytes needed to represent a u64 in minimal little-endian form. -/
def u64ByteCount (x : UInt64) : UInt8 :=
  if x == 0 then 0
  else if x < 0x100 then 1
  else if x < 0x10000 then 2
  else if x < 0x1000000 then 3
  else if x < 0x100000000 then 4
  else if x < 0x10000000000 then 5
  else if x < 0x1000000000000 then 6
  else if x < 0x100000000000000 then 7
  else 8

/-- The low `n` bytes of a u64, least significant byte first. -/
def u64LEList : Nat → UInt64 → List UInt8
  | 0, _ => []
  | n + 1, x => x.toUInt8 :: u64LEList n (x >>> 8)

/-- Interpret a least-significant-byte-first list as a u64. Callers reject
lists longer than eight before invoking this function. -/
def u64OfLEList : List UInt8 → UInt64
  | [] => 0
  | b :: rest => b.toUInt64 ||| (u64OfLEList rest <<< 8)

/-- The low `n` little-endian bytes of a u64. -/
def u64LEBytes (x : UInt64) (n : Nat) : ByteArray :=
  (u64LEList n x).toByteArray

/-- Interpret at most eight little-endian bytes as a u64. -/
def u64OfLEBytes (bytes : ByteArray) : UInt64 :=
  u64OfLEList bytes.data.toList

theorem u64LEList_length (n : Nat) (x : UInt64) :
    (u64LEList n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [u64LEList, ih]

@[simp] theorem u64LEBytes_size (n : Nat) (x : UInt64) :
    (u64LEBytes x n).size = n := by
  simp [u64LEBytes, u64LEList_length]

private theorem u64OfLEList_zero_above (bytes : List UInt8) (i : Nat)
    (h : 8 * bytes.length ≤ i) :
    (u64OfLEList bytes).toBitVec.getLsbD i = false := by
  induction bytes generalizing i with
  | nil => simp [u64OfLEList]
  | cons b rest ih =>
    simp only [u64OfLEList, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]
    simp
    constructor
    · intro _
      exact BitVec.getLsbD_of_ge b.toBitVec i (by
        simp only [List.length_cons, Nat.mul_add] at h
        omega)
    · intro _ hi
      apply ih
      simp only [List.length_cons, Nat.mul_add] at h
      omega

private theorem u64OfLEList_cons_shift (b : UInt8) (rest : List UInt8)
    (hle : rest.length ≤ 7) :
    (b.toUInt64 ||| (u64OfLEList rest <<< 8)) >>> 8 =
      u64OfLEList rest := by
  apply UInt64.toBitVec_inj.1
  ext i hi
  simp only [UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft]
  simp
  by_cases hlow : i < 56
  · have hsum : 8 + i < 64 := by omega
    have h8 : ¬8 + i < 8 := by omega
    simp [hsum, h8, BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat]
  · have hz := u64OfLEList_zero_above rest i (by omega)
    have hz' : (u64OfLEList rest).toBitVec[i] = false := by
      simpa [BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat] using hz
    have hsum : ¬8 + i < 64 := by omega
    simp [hsum, hz']

/-- Re-encoding any list of at most eight little-endian bytes recovers the
list. The proof reduces the word operations to kernel-checked bit extensionality. -/
theorem u64LEList_of_decode (bytes : List UInt8) (hle : bytes.length ≤ 8) :
    u64LEList bytes.length (u64OfLEList bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.length_cons] at hle
    simp only [List.length_cons, u64LEList, u64OfLEList]
    rw [show (b.toUInt64 ||| u64OfLEList rest <<< 8).toUInt8 = b by
      apply UInt8.toBitVec_inj.1
      simp]
    rw [u64OfLEList_cons_shift b rest (by omega)]
    congr 1
    exact ih (by omega)

/-- Re-encoding any byte array of length at most eight recovers it exactly. -/
theorem u64LEBytes_of_decode (bytes : ByteArray) (hle : bytes.size ≤ 8) :
    u64LEBytes (u64OfLEBytes bytes) bytes.size = bytes := by
  rcases bytes with ⟨data⟩
  change data.size ≤ 8 at hle
  simp only [u64LEBytes, u64OfLEBytes, ByteArray.size]
  rw [show data.size = data.toList.length by simp]
  rw [u64LEList_of_decode data.toList (by simpa using hle)]
  apply ByteArray.ext
  exact Array.toList_inj.mp (by simp)

/-- Minimal byte counts are always representable by a u64 payload. -/
theorem u64ByteCount_le_eight (x : UInt64) : (u64ByteCount x).toNat ≤ 8 := by
  simp only [u64ByteCount]
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split <;> simp

private theorem u64_byte_shift_reconstruct (x : UInt64) :
    x.toUInt8.toUInt64 ||| ((x >>> 8) <<< 8) = x := by
  apply UInt64.toBitVec_inj.1
  ext i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight]
  simp
  by_cases hlow : i < 8
  · simp [hlow, BitVec.getLsbD, BitVec.getElem_eq_testBit_toNat,
      BitVec.toNat_umod]
    have hmod := Nat.testBit_mod_two_pow x.toNat 8 i
    rw [show 2 ^ 8 = 256 by decide] at hmod
    simpa [hlow] using hmod
  · have hsum : 8 + (i - 8) = i := by omega
    simp [hlow, hsum, BitVec.getLsbD,
      BitVec.getElem_eq_testBit_toNat, BitVec.toNat_umod]
    have hmod := Nat.testBit_mod_two_pow x.toNat 8 i
    rw [show 2 ^ 8 = 256 by decide] at hmod
    rw [hmod]
    simp [hlow]

private theorem u64OfLEList_u64LEList_of_lt (n : Nat) (x : UInt64)
    (h : x.toNat < 2 ^ (8 * n)) :
    u64OfLEList (u64LEList n x) = x := by
  induction n generalizing x with
  | zero =>
    simp only [Nat.mul_zero, Nat.pow_zero] at h
    simp only [u64LEList, u64OfLEList]
    apply UInt64.toNat_inj.1
    simp
    omega
  | succ n ih =>
    simp only [u64LEList, u64OfLEList]
    rw [ih]
    · exact u64_byte_shift_reconstruct x
    · change x.toNat >>> 8 < 2 ^ (8 * n)
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by decide)]
      calc
        x.toNat < 2 ^ (8 * (n + 1)) := h
        _ = 2 ^ (8 * n) * 2 ^ 8 := by
          rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]

private theorem u64ByteCount_toNat_bound (x : UInt64) :
    x.toNat < 2 ^ (8 * (u64ByteCount x).toNat) := by
  simp only [u64ByteCount]
  split
  · simp_all
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  split
  · simp_all [UInt64.lt_iff_toNat_lt]
  · simpa using x.toNat_lt

/-- Decoding the minimal little-endian encoding returns the original u64. -/
theorem u64OfLEBytes_encoded (x : UInt64) :
    u64OfLEBytes (u64LEBytes x (u64ByteCount x).toNat) = x := by
  simpa [u64OfLEBytes, u64LEBytes] using
    u64OfLEList_u64LEList_of_lt (u64ByteCount x).toNat x
      (u64ByteCount_toNat_bound x)

def putBytes (x : ByteArray) : PutM Unit :=
  modify fun s => s.append x

def getBytes (len : Nat) : GetM ByteArray := do
  let st ← get
  if st.idx + len ≤ st.bytes.size then
    let chunk := st.bytes.extract st.idx (st.idx + len)
    set { st with idx := st.idx + len }
    return chunk
  else
    throw s!"EOF: need {len} bytes at index {st.idx}, size {st.bytes.size}"

theorem putBytes_spec (bytes : ByteArray) : PutSpec (putBytes bytes) bytes := by
  intro pre
  rfl

theorem getBytes_spec (bytes : ByteArray) :
    GetSpec (getBytes bytes.size) bytes bytes := by
  intro pre suffix
  have hextract :
      (pre ++ bytes ++ suffix).extract pre.size
        (pre.size + bytes.size) = bytes := by
    rw [ByteArray.extract_append]
    simp [ByteArray.size_append]
    exact ByteArray.extract_append_eq_right rfl rfl
  simp [getBytes, hextract]
  rfl

/-- Write a u64 in its minimal little-endian bytes. -/
def putU64TrimmedLE (x : UInt64) : PutM Unit :=
  putBytes (u64LEBytes x (u64ByteCount x).toNat)

/-- Read a u64 from `n` little-endian bytes, rejecting impossible widths
before consuming any payload byte. -/
def getU64TrimmedLE (n : Nat) : GetM UInt64 := do
  if n > 8 then
    throw s!"getU64TrimmedLE: byte length {n} exceeds 8"
  return u64OfLEBytes (← getBytes n)

theorem putU64TrimmedLE_spec (x : UInt64) :
    PutSpec (putU64TrimmedLE x)
      (u64LEBytes x (u64ByteCount x).toNat) := by
  exact putBytes_spec _

/-- Any payload of width at most eight is read exactly and interpreted as a
little-endian u64. -/
theorem getU64TrimmedLE_spec (bytes : ByteArray) (hle : bytes.size ≤ 8) :
    GetSpec (getU64TrimmedLE bytes.size) bytes (u64OfLEBytes bytes) := by
  intro pre suffix
  unfold getU64TrimmedLE
  simp only [show ¬bytes.size > 8 by omega, ↓reduceIte, StateT.run_bind]
  rw [getBytes_spec bytes pre suffix]
  rfl

/-- The strict reader consumes the writer's minimal output and returns the
original u64. -/
theorem getU64TrimmedLE_encoded_spec (x : UInt64) :
    GetSpec (getU64TrimmedLE (u64ByteCount x).toNat)
      (u64LEBytes x (u64ByteCount x).toNat) x := by
  have h := getU64TrimmedLE_spec
    (u64LEBytes x (u64ByteCount x).toNat)
    (by rw [u64LEBytes_size]; exact u64ByteCount_le_eight x)
  rw [u64LEBytes_size, u64OfLEBytes_encoded] at h
  exact h

/-! ## Tag headers

`TagN`: an N-bit flag plus a size. Header byte layout (high to low):
`[flag:N][large:1][small: 7-N]`. If `large = 0`, the size is the small
field; otherwise the small field holds `byteCount - 1` and the size
follows in minimal little-endian bytes. -/

namespace HeaderBits

private theorem nat_lt_eight_cases {i : Nat} (h : i < 8) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  omega

private theorem u8_getElem_false_of_lt_pow (x : UInt8) {k i : Nat}
    (hi : i < 8) (hlt : x.toNat < 2 ^ k) (hki : k ≤ i) :
    x.toBitVec[i] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le hlt
    (Nat.pow_le_pow_of_le (by decide : 1 < 2) hki)

private theorem tag0_small_and_low (b : UInt8) (h : b < 128) :
    b &&& 0x7F = b := by
  apply UInt8.toNat_inj.1
  simp only [UInt8.toNat_and]
  have hb : b.toNat < 2 ^ 7 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  simpa using Nat.and_two_pow_sub_one_of_lt_two_pow hb

private theorem tag0_small_and_high (b : UInt8) (h : b < 128) :
    b &&& 0x80 = 0 := by
  have hb : b.toNat < 2 ^ 7 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, BitVec.getElem_and, UInt8.toBitVec_ofNat,
    BitVec.getElem_zero]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  exact u8_getElem_false_of_lt_pow b (by omega) hb (by omega)

theorem tag0_small (b : UInt8) (h : b < 128) :
    b &&& 0x80 == 0 ∧ b &&& 0x7F = b := by
  rw [show b &&& 0x80 = 0 from tag0_small_and_high b h]
  simp [tag0_small_and_low b h]

theorem tag2_flag (flag payload : UInt8) (hf : flag < 4)
    (hp : payload < 64) :
    ((flag <<< 6) ||| payload) >>> 6 = flag := by
  have hfn : flag.toNat < 2 ^ 2 := by
    simpa [UInt8.lt_iff_toNat_lt] using hf
  have hpn : payload.toNat < 2 ^ 6 := by
    simpa [UInt8.lt_iff_toNat_lt] using hp
  have hf2 := u8_getElem_false_of_lt_pow flag (i := 2) (by omega) hfn (by omega)
  have hf3 := u8_getElem_false_of_lt_pow flag (i := 3) (by omega) hfn (by omega)
  have hf4 := u8_getElem_false_of_lt_pow flag (i := 4) (by omega) hfn (by omega)
  have hf5 := u8_getElem_false_of_lt_pow flag (i := 5) (by omega) hfn (by omega)
  have hf6 := u8_getElem_false_of_lt_pow flag (i := 6) (by omega) hfn (by omega)
  have hf7 := u8_getElem_false_of_lt_pow flag (i := 7) (by omega) hfn (by omega)
  have hp6 := u8_getElem_false_of_lt_pow payload (i := 6) (by omega) hpn (by omega)
  have hp7 := u8_getElem_false_of_lt_pow payload (i := 7) (by omega) hpn (by omega)
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_shiftRight, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hf2, hf3, hf4, hf5, hf6, hf7, hp6, hp7]

theorem tag2_small_header (flag size : UInt8) (hf : flag < 4)
    (hs : size < 32) :
    ((flag <<< 6) ||| size) &&& 0x20 = 0 := by
  have hfn : flag.toNat < 2 ^ 2 := by
    simpa [UInt8.lt_iff_toNat_lt] using hf
  have hsn : size.toNat < 2 ^ 5 := by
    simpa [UInt8.lt_iff_toNat_lt] using hs
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat, BitVec.getElem_zero]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  exact u8_getElem_false_of_lt_pow size (by omega) hsn (by omega)

theorem tag2_small_size (flag size : UInt8) (hf : flag < 4)
    (hs : size < 32) :
    ((flag <<< 6) ||| size) &&& 0x1F = size := by
  have hfn : flag.toNat < 2 ^ 2 := by
    simpa [UInt8.lt_iff_toNat_lt] using hf
  have hsn : size.toNat < 2 ^ 5 := by
    simpa [UInt8.lt_iff_toNat_lt] using hs
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  all_goals exact u8_getElem_false_of_lt_pow size (by omega) hsn (by omega)

private theorem tag0_large_low (low : UInt8) (h : low < 128) :
    (0x80 ||| low) &&& 0x7F = low := by
  have hlow : low.toNat < 2 ^ 7 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    BitVec.getElem_and, BitVec.getElem_or, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  exact u8_getElem_false_of_lt_pow low (by omega) hlow (by omega)

private theorem tag0_large_bit (low : UInt8) :
    (0x80 ||| low) &&& 0x80 = 0x80 := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    BitVec.getElem_and, BitVec.getElem_or, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem tag0_large (n : UInt8) (hlo : 0 < n) (hhi : n ≤ 8) :
    ((0x80 ||| (n - 1)) &&& 0x7F) + 1 = n ∧
      ¬((0x80 ||| (n - 1)) &&& 0x80 == 0) := by
  have hone : (1 : UInt8) ≤ n := by
    rw [UInt8.le_iff_toNat_le]
    have := UInt8.lt_iff_toNat_lt.1 hlo
    simp only [UInt8.reduceToNat] at this ⊢
    omega
  have hn : n - 1 < 128 :=
    UInt8.lt_of_le_of_lt (UInt8.sub_le hone)
      (UInt8.lt_of_le_of_lt hhi (by decide))
  rw [tag0_large_low (n - 1) hn, UInt8.sub_add_cancel,
    tag0_large_bit]
  simp

private theorem tag2_large_low (flag low : UInt8) (h : low < 32) :
    ((flag <<< 6) ||| 0x20 ||| low) &&& 0x1F = low := by
  have hlow : low.toNat < 2 ^ 5 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  all_goals exact u8_getElem_false_of_lt_pow low (by omega) hlow (by omega)

private theorem tag2_large_bit (flag low : UInt8) :
    ((flag <<< 6) ||| 0x20 ||| low) &&& 0x20 = 0x20 := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem tag2_large (flag n : UInt8) (hf : flag < 4)
    (hlo : 0 < n) (hhi : n ≤ 8) :
    ((((flag <<< 6) ||| 0x20 ||| (n - 1)) >>> 6) = flag) ∧
    ((((flag <<< 6) ||| 0x20 ||| (n - 1)) &&& 0x1F) + 1 = n) ∧
    ¬((((flag <<< 6) ||| 0x20 ||| (n - 1)) &&& 0x20) == 0) := by
  have hone : (1 : UInt8) ≤ n := by
    rw [UInt8.le_iff_toNat_le]
    have := UInt8.lt_iff_toNat_lt.1 hlo
    simp only [UInt8.reduceToNat] at this ⊢
    omega
  have hn32 : n - 1 < 32 :=
    UInt8.lt_of_le_of_lt (UInt8.sub_le hone)
      (UInt8.lt_of_le_of_lt hhi (by decide))
  have hp64 : 0x20 ||| (n - 1) < (64 : UInt8) := by
    rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_or]
    simp only [UInt8.reduceToNat]
    apply Nat.or_lt_two_pow (n := 6) (by decide)
    have hn : (n - 1).toNat < 32 := by
      simpa [UInt8.lt_iff_toNat_lt] using hn32
    omega
  rw [UInt8.or_assoc, tag2_flag flag (0x20 ||| (n - 1)) hf hp64,
    ← UInt8.or_assoc, tag2_large_low flag (n - 1) hn32,
    UInt8.sub_add_cancel, tag2_large_bit]
  simp

theorem tag4_flag (flag payload : UInt8) (hf : flag < 16)
    (hp : payload < 16) :
    ((flag <<< 4) ||| payload) >>> 4 = flag := by
  have hfn : flag.toNat < 2 ^ 4 := by
    simpa [UInt8.lt_iff_toNat_lt] using hf
  have hpn : payload.toNat < 2 ^ 4 := by
    simpa [UInt8.lt_iff_toNat_lt] using hp
  have hf4 := u8_getElem_false_of_lt_pow flag (i := 4) (by omega) hfn (by omega)
  have hf5 := u8_getElem_false_of_lt_pow flag (i := 5) (by omega) hfn (by omega)
  have hf6 := u8_getElem_false_of_lt_pow flag (i := 6) (by omega) hfn (by omega)
  have hf7 := u8_getElem_false_of_lt_pow flag (i := 7) (by omega) hfn (by omega)
  have hp4 := u8_getElem_false_of_lt_pow payload (i := 4) (by omega) hpn (by omega)
  have hp5 := u8_getElem_false_of_lt_pow payload (i := 5) (by omega) hpn (by omega)
  have hp6 := u8_getElem_false_of_lt_pow payload (i := 6) (by omega) hpn (by omega)
  have hp7 := u8_getElem_false_of_lt_pow payload (i := 7) (by omega) hpn (by omega)
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_shiftRight, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [hf4, hf5, hf6, hf7, hp4, hp5, hp6, hp7]

theorem tag4_small_header (flag size : UInt8) (hs : size < 8) :
    ((flag <<< 4) ||| size) &&& 0x08 = 0 := by
  have hsn : size.toNat < 2 ^ 3 := by
    simpa [UInt8.lt_iff_toNat_lt] using hs
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat, BitVec.getElem_zero]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  exact u8_getElem_false_of_lt_pow size (by omega) hsn (by omega)

theorem tag4_small_size (flag size : UInt8) (hs : size < 8) :
    ((flag <<< 4) ||| size) &&& 0x07 = size := by
  have hsn : size.toNat < 2 ^ 3 := by
    simpa [UInt8.lt_iff_toNat_lt] using hs
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  all_goals exact u8_getElem_false_of_lt_pow size (by omega) hsn (by omega)

private theorem tag4_large_low (flag low : UInt8) (h : low < 8) :
    ((flag <<< 4) ||| 0x08 ||| low) &&& 0x07 = low := by
  have hlow : low.toNat < 2 ^ 3 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  all_goals exact u8_getElem_false_of_lt_pow low (by omega) hlow (by omega)

private theorem tag4_large_bit (flag low : UInt8) :
    ((flag <<< 4) ||| 0x08 ||| low) &&& 0x08 = 0x08 := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_or,
    UInt8.toBitVec_shiftLeft, BitVec.getElem_and, BitVec.getElem_or,
    UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem tag4_large (flag n : UInt8) (hf : flag < 16)
    (hlo : 0 < n) (hhi : n ≤ 8) :
    ((((flag <<< 4) ||| 0x08 ||| (n - 1)) >>> 4) = flag) ∧
    ((((flag <<< 4) ||| 0x08 ||| (n - 1)) &&& 0x07) + 1 = n) ∧
    ¬((((flag <<< 4) ||| 0x08 ||| (n - 1)) &&& 0x08) == 0) := by
  have hone : (1 : UInt8) ≤ n := by
    rw [UInt8.le_iff_toNat_le]
    have := UInt8.lt_iff_toNat_lt.1 hlo
    simp only [UInt8.reduceToNat] at this ⊢
    omega
  have hn8 : n - 1 < 8 :=
    UInt8.lt_of_lt_of_le (UInt8.sub_lt (by decide) hone) hhi
  have hp16 : 0x08 ||| (n - 1) < (16 : UInt8) := by
    rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_or]
    simp only [UInt8.reduceToNat]
    apply Nat.or_lt_two_pow (n := 4) (by decide)
    have hn := UInt8.lt_iff_toNat_lt.1 hn8
    simp only [UInt8.reduceToNat] at hn ⊢
    omega
  rw [UInt8.or_assoc, tag4_flag flag (0x08 ||| (n - 1)) hf hp16,
    ← UInt8.or_assoc, tag4_large_low flag (n - 1) hn8,
    UInt8.sub_add_cancel, tag4_large_bit]
  simp

theorem u64_to_u8_to_u64_of_lt (x : UInt64) (h : x < 256) :
    x.toUInt8.toUInt64 = x := by
  apply UInt64.toNat_inj.1
  simp only [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  apply Nat.mod_eq_of_lt
  simpa [UInt64.lt_iff_toNat_lt] using h

theorem u64_to_u8_lt (x : UInt64) (bound : UInt8)
    (h : x < bound.toUInt64) : x.toUInt8 < bound := by
  rw [UInt8.lt_iff_toNat_lt]
  simp only [UInt64.toNat_toUInt8]
  have hxBound : x.toNat < bound.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using h
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hxBound bound.toNat_lt)]
  exact hxBound

theorem byteCount_pos_of_ne_zero (x : UInt64) (h : x ≠ 0) :
    0 < u64ByteCount x := by
  simp only [u64ByteCount]
  split
  · simp_all
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split <;> simp

private theorem tag0_split (header : UInt8) :
    (header &&& 0x80) ||| (header &&& 0x7F) = header := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem tag2_split (header : UInt8) :
    ((header >>> 6) <<< 6) ||| (header &&& 0x20) |||
      (header &&& 0x1F) = header := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    UInt8.toBitVec_shiftLeft, UInt8.toBitVec_shiftRight,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem tag4_split (header : UInt8) :
    ((header >>> 4) <<< 4) ||| (header &&& 0x08) |||
      (header &&& 0x07) = header := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    UInt8.toBitVec_shiftLeft, UInt8.toBitVec_shiftRight,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem tag0_high_cases (header : UInt8) :
    header &&& 0x80 = 0 ∨ header &&& 0x80 = 0x80 := by
  by_cases hb : header.toBitVec[7] = true
  · right
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb]
  · left
    have hb' : header.toBitVec[7] = false := by
      cases hbit : header.toBitVec[7] <;> simp_all
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb']

private theorem tag2_high_cases (header : UInt8) :
    header &&& 0x20 = 0 ∨ header &&& 0x20 = 0x20 := by
  by_cases hb : header.toBitVec[5] = true
  · right
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb]
  · left
    have hb' : header.toBitVec[5] = false := by
      cases hbit : header.toBitVec[5] <;> simp_all
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb']

private theorem tag4_high_cases (header : UInt8) :
    header &&& 0x08 = 0 ∨ header &&& 0x08 = 0x08 := by
  by_cases hb : header.toBitVec[3] = true
  · right
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb]
  · left
    have hb' : header.toBitVec[3] = false := by
      cases hbit : header.toBitVec[3] <;> simp_all
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb']

private theorem tag0_mask_bound (header : UInt8) :
    header.toUInt64 &&& 0x7F < 128 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat]
  exact Nat.and_lt_two_pow (n := 7) header.toNat (by decide)

private theorem tag2_mask_bound (header : UInt8) :
    header.toUInt64 &&& 0x1F < 32 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat]
  exact Nat.and_lt_two_pow (n := 5) header.toNat (by decide)

private theorem tag4_mask_bound (header : UInt8) :
    header.toUInt64 &&& 0x07 < 8 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat]
  exact Nat.and_lt_two_pow (n := 3) header.toNat (by decide)

theorem tag0_canonical (header : UInt8) :
    (header &&& 0x80 == 0 →
      (header.toUInt64 &&& 0x7F) < 128 ∧
      (header.toUInt64 &&& 0x7F).toUInt8 = header) ∧
    (¬(header &&& 0x80 == 0) → 0x80 ||| (header &&& 0x7F) = header) := by
  constructor
  · intro hsmall
    have hm : header &&& 0x80 = 0 := by simpa using hsmall
    have hlow : header &&& 0x7F = header := by
      have hsplit := tag0_split header
      rw [hm] at hsplit
      simpa using hsplit
    exact ⟨tag0_mask_bound header, by simpa using hlow⟩
  · intro hlarge
    have hne : header &&& 0x80 ≠ 0 := by simpa using hlarge
    have hm : header &&& 0x80 = 0x80 :=
      (tag0_high_cases header).resolve_left hne
    have hsplit := tag0_split header
    rw [hm] at hsplit
    exact hsplit

theorem tag2_canonical (header : UInt8) :
    (header &&& 0x20 == 0 →
      (header.toUInt64 &&& 0x1F) < 32 ∧
      ((header >>> 6) <<< 6) ||| (header &&& 0x1F) = header) ∧
    (¬(header &&& 0x20 == 0) →
      ((header >>> 6) <<< 6) ||| 0x20 ||| (header &&& 0x1F) = header) := by
  constructor
  · intro hsmall
    have hm : header &&& 0x20 = 0 := by simpa using hsmall
    have hsplit := tag2_split header
    rw [hm] at hsplit
    exact ⟨tag2_mask_bound header, by simpa using hsplit⟩
  · intro hlarge
    have hne : header &&& 0x20 ≠ 0 := by simpa using hlarge
    have hm : header &&& 0x20 = 0x20 :=
      (tag2_high_cases header).resolve_left hne
    have hsplit := tag2_split header
    rw [hm] at hsplit
    exact hsplit

theorem tag4_canonical (header : UInt8) :
    (header &&& 0x08 == 0 →
      (header.toUInt64 &&& 0x07) < 8 ∧
      ((header >>> 4) <<< 4) ||| (header &&& 0x07) = header) ∧
    (¬(header &&& 0x08 == 0) →
      ((header >>> 4) <<< 4) ||| 0x08 ||| (header &&& 0x07) = header) := by
  constructor
  · intro hsmall
    have hm : header &&& 0x08 = 0 := by simpa using hsmall
    have hsplit := tag4_split header
    rw [hm] at hsplit
    exact ⟨tag4_mask_bound header, by simpa using hsplit⟩
  · intro hlarge
    have hne : header &&& 0x08 ≠ 0 := by simpa using hlarge
    have hm : header &&& 0x08 = 0x08 :=
      (tag4_high_cases header).resolve_left hne
    have hsplit := tag4_split header
    rw [hm] at hsplit
    exact hsplit

end HeaderBits

structure Tag0 where
  size : UInt64
  deriving BEq, Repr

structure Tag2 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr

structure Tag4 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr

/-- Canonical bytes for a no-flag size header. -/
def tag0Bytes (t : Tag0) : ByteArray :=
  if t.size < 128 then
    u8Bytes t.size.toUInt8
  else
    let n := u64ByteCount t.size
    u8Bytes (0x80 ||| (n - 1)) ++ u64LEBytes t.size n.toNat

def putTag0 (t : Tag0) : PutM Unit :=
  putBytes (tag0Bytes t)

theorem putTag0_spec (t : Tag0) : PutSpec (putTag0 t) (tag0Bytes t) := by
  exact putBytes_spec _

def getTag0 : GetM Tag0 := do
  let b ← getU8
  if b &&& 0x80 == 0 then
    return ⟨(b &&& 0x7F).toUInt64⟩
  else
    let n := (b &&& 0x7F) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag0: non-minimal size"
    if size < 128 then throw "getTag0: size must use small form"
    return ⟨size⟩

/-- The strict Tag0 reader consumes exactly the canonical bytes emitted for
every size. -/
theorem getTag0_encoded_spec (t : Tag0) : GetSpec getTag0 (tag0Bytes t) t := by
  rcases t with ⟨size⟩
  intro pre suffix
  by_cases hs : size < 128
  · simp only [tag0Bytes, hs, if_pos]
    simp only [getTag0, StateT.run_bind]
    rw [getU8_spec size.toUInt8 pre suffix]
    simp only [bind, Except.bind]
    have hs8 : size.toUInt8 < 128 :=
      HeaderBits.u64_to_u8_lt size 128 (by simpa using hs)
    obtain ⟨hheader, hlow⟩ := HeaderBits.tag0_small size.toUInt8 hs8
    have hheader : size.toUInt8 &&& 0x80 == 0 := by
      exact hheader
    rw [if_pos hheader]
    have hvalue : (size.toUInt8 &&& 0x7F).toUInt64 = size := by
      rw [hlow]
      exact HeaderBits.u64_to_u8_to_u64_of_lt size
        (UInt64.lt_trans hs (by decide))
    simp [hvalue, u8Bytes]
    rfl
  · simp only [tag0Bytes, hs, if_false]
    let n := u64ByteCount size
    let header : UInt8 := 0x80 ||| (n - 1)
    change getTag0.run
      ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
        pre.size⟩ =
      .ok (⟨size⟩,
        ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
          pre.size + (u8Bytes header ++ u64LEBytes size n.toNat).size⟩)
    have hbytes : pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix =
        pre ++ u8Bytes header ++ (u64LEBytes size n.toNat ++ suffix) := by
      simp [ByteArray.append_assoc]
    rw [hbytes]
    have hhead := getU8_spec header pre
      (u64LEBytes size n.toNat ++ suffix)
    simp only [getTag0, StateT.run_bind]
    rw [hhead]
    simp only [bind, Except.bind]
    have hne : size ≠ 0 := by
      intro hzero
      subst size
      simp at hs
    have hnle : n ≤ 8 := by
      rw [UInt8.le_iff_toNat_le]
      exact u64ByteCount_le_eight size
    obtain ⟨hn, hlarge⟩ := HeaderBits.tag0_large n
      (by simpa [n] using HeaderBits.byteCount_pos_of_ne_zero size hne) hnle
    change (header &&& 0x7F) + 1 = n at hn
    change ¬(header &&& 0x80 == 0) at hlarge
    rw [if_neg hlarge]
    rw [hn]
    dsimp only [n]
    let next : UInt64 → GetM Tag0 := fun decoded => do
      if u64ByteCount decoded != u64ByteCount size then
        throw "getTag0: non-minimal size"
      if decoded < 128 then throw "getTag0: size must use small form"
      return Tag0.mk decoded
    change (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
      ⟨pre ++ u8Bytes header ++
          (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
        pre.size + (u8Bytes header).size⟩ = _
    have hcont : GetSpec (next size) ByteArray.empty (Tag0.mk size) := by
      intro innerPre innerSuffix
      simp [next, hs]
      rfl
    have hpayload := GetSpec.bind
      (next := next) (getU64TrimmedLE_encoded_spec size) hcont
    simp only [ByteArray.append_empty] at hpayload
    have hpayload' :
        (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
          ⟨pre ++ u8Bytes header ++
              (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
            pre.size + (u8Bytes header).size⟩ =
          .ok (Tag0.mk size,
            ⟨pre ++ u8Bytes header ++
                (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
              pre.size + (u8Bytes header).size +
                (u64LEBytes size (u64ByteCount size).toNat).size⟩) := by
      simpa only [ByteArray.append_assoc, ByteArray.size_append] using
        hpayload (pre ++ u8Bytes header) suffix
    rw [hpayload']
    simp [u8Bytes, ByteArray.size_append]
    omega

/-- Canonical bytes for a two-flag-bit size header. Values outside the
two-bit flag range are not valid in-memory tags. -/
def tag2Bytes (t : Tag2) : ByteArray :=
  if t.size < 32 then
    u8Bytes ((t.flag <<< 6) ||| t.size.toUInt8)
  else
    let n := u64ByteCount t.size
    u8Bytes ((t.flag <<< 6) ||| 0x20 ||| (n - 1)) ++
      u64LEBytes t.size n.toNat

def putTag2 (t : Tag2) : PutM Unit :=
  putBytes (tag2Bytes t)

theorem putTag2_spec (t : Tag2) : PutSpec (putTag2 t) (tag2Bytes t) := by
  exact putBytes_spec _

def getTag2 : GetM Tag2 := do
  let b ← getU8
  let flag := b >>> 6
  if b &&& 0x20 == 0 then
    return ⟨flag, (b &&& 0x1F).toUInt64⟩
  else
    let n := (b &&& 0x1F) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag2: non-minimal size"
    if size < 32 then throw "getTag2: size must use small form"
    return ⟨flag, size⟩

/-- The strict Tag2 reader consumes the canonical encoding whenever the
in-memory flag fits its declared two-bit field. -/
theorem getTag2_encoded_spec (t : Tag2) (hflag : t.flag < 4) :
    GetSpec getTag2 (tag2Bytes t) t := by
  rcases t with ⟨flag, size⟩
  intro pre suffix
  by_cases hs : size < 32
  · simp only [tag2Bytes, hs, if_pos]
    let header : UInt8 := (flag <<< 6) ||| size.toUInt8
    change getTag2.run ⟨pre ++ u8Bytes header ++ suffix, pre.size⟩ = _
    simp only [getTag2, StateT.run_bind]
    rw [getU8_spec header pre suffix]
    simp only [bind, Except.bind]
    have hs8 : size.toUInt8 < 32 :=
      HeaderBits.u64_to_u8_lt size 32 (by simpa using hs)
    have hdecodedFlag : header >>> 6 = flag := by
      dsimp [header]
      exact HeaderBits.tag2_flag flag size.toUInt8 hflag
        (UInt8.lt_trans hs8 (by decide))
    have hheader : header &&& 0x20 == 0 := by
      dsimp [header]
      rw [HeaderBits.tag2_small_header flag size.toUInt8 hflag hs8]
      decide
    have hvalue : (header &&& 0x1F).toUInt64 = size := by
      dsimp [header]
      rw [HeaderBits.tag2_small_size flag size.toUInt8 hflag hs8]
      exact HeaderBits.u64_to_u8_to_u64_of_lt size
        (UInt64.lt_trans hs (by decide))
    rw [hdecodedFlag, if_pos hheader, hvalue]
    simp [u8Bytes]
    rfl
  · simp only [tag2Bytes, hs, if_false]
    let n := u64ByteCount size
    let header : UInt8 := (flag <<< 6) ||| 0x20 ||| (n - 1)
    change getTag2.run
      ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
        pre.size⟩ =
      .ok (⟨flag, size⟩,
        ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
          pre.size + (u8Bytes header ++ u64LEBytes size n.toNat).size⟩)
    have hbytes : pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix =
        pre ++ u8Bytes header ++ (u64LEBytes size n.toNat ++ suffix) := by
      simp [ByteArray.append_assoc]
    rw [hbytes]
    have hhead := getU8_spec header pre
      (u64LEBytes size n.toNat ++ suffix)
    simp only [getTag2, StateT.run_bind]
    rw [hhead]
    simp only [bind, Except.bind]
    have hne : size ≠ 0 := by
      intro hzero
      subst size
      simp at hs
    have hnle : n ≤ 8 := by
      rw [UInt8.le_iff_toNat_le]
      exact u64ByteCount_le_eight size
    obtain ⟨hdecodedFlag, hn, hlarge⟩ := HeaderBits.tag2_large flag n hflag
      (by simpa [n] using HeaderBits.byteCount_pos_of_ne_zero size hne) hnle
    change header >>> 6 = flag at hdecodedFlag
    change (header &&& 0x1F) + 1 = n at hn
    change ¬(header &&& 0x20 == 0) at hlarge
    rw [hdecodedFlag]
    rw [if_neg hlarge, hn]
    dsimp only [n]
    let next : UInt64 → GetM Tag2 := fun decoded => do
      if u64ByteCount decoded != u64ByteCount size then
        throw "getTag2: non-minimal size"
      if decoded < 32 then throw "getTag2: size must use small form"
      return ⟨flag, decoded⟩
    change (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
      ⟨pre ++ u8Bytes header ++
          (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
        pre.size + (u8Bytes header).size⟩ = _
    have hcont : GetSpec (next size) ByteArray.empty (Tag2.mk flag size) := by
      intro innerPre innerSuffix
      simp [next, hs]
      rfl
    have hpayload := GetSpec.bind
      (next := next) (getU64TrimmedLE_encoded_spec size) hcont
    simp only [ByteArray.append_empty] at hpayload
    have hpayload' :
        (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
          ⟨pre ++ u8Bytes header ++
              (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
            pre.size + (u8Bytes header).size⟩ =
          .ok (Tag2.mk flag size,
            ⟨pre ++ u8Bytes header ++
                (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
              pre.size + (u8Bytes header).size +
                (u64LEBytes size (u64ByteCount size).toNat).size⟩) := by
      simpa only [ByteArray.append_assoc, ByteArray.size_append] using
        hpayload (pre ++ u8Bytes header) suffix
    rw [hpayload']
    simp [u8Bytes, ByteArray.size_append]
    omega

/-- Canonical bytes for a four-flag-bit size header. Values outside the
four-bit flag range are not valid in-memory tags. -/
def tag4Bytes (t : Tag4) : ByteArray :=
  if t.size < 8 then
    u8Bytes ((t.flag <<< 4) ||| t.size.toUInt8)
  else
    let n := u64ByteCount t.size
    u8Bytes ((t.flag <<< 4) ||| 0x08 ||| (n - 1)) ++
      u64LEBytes t.size n.toNat

def putTag4 (t : Tag4) : PutM Unit :=
  putBytes (tag4Bytes t)

theorem putTag4_spec (t : Tag4) : PutSpec (putTag4 t) (tag4Bytes t) := by
  exact putBytes_spec _

def getTag4 : GetM Tag4 := do
  let b ← getU8
  let flag := b >>> 4
  if b &&& 0x08 == 0 then
    return ⟨flag, (b &&& 0x07).toUInt64⟩
  else
    let n := (b &&& 0x07) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag4: non-minimal size"
    if size < 8 then throw "getTag4: size must use small form"
    return ⟨flag, size⟩

/-- The strict Tag4 reader consumes the canonical encoding whenever the
in-memory flag fits its declared four-bit field. -/
theorem getTag4_encoded_spec (t : Tag4) (hflag : t.flag < 16) :
    GetSpec getTag4 (tag4Bytes t) t := by
  rcases t with ⟨flag, size⟩
  intro pre suffix
  by_cases hs : size < 8
  · simp only [tag4Bytes, hs, if_pos]
    let header : UInt8 := (flag <<< 4) ||| size.toUInt8
    change getTag4.run ⟨pre ++ u8Bytes header ++ suffix, pre.size⟩ = _
    simp only [getTag4, StateT.run_bind]
    rw [getU8_spec header pre suffix]
    simp only [bind, Except.bind]
    have hs8 : size.toUInt8 < 8 :=
      HeaderBits.u64_to_u8_lt size 8 (by simpa using hs)
    have hdecodedFlag : header >>> 4 = flag := by
      dsimp [header]
      exact HeaderBits.tag4_flag flag size.toUInt8 hflag
        (UInt8.lt_trans hs8 (by decide))
    have hheader : header &&& 0x08 == 0 := by
      dsimp [header]
      rw [HeaderBits.tag4_small_header flag size.toUInt8 hs8]
      decide
    have hvalue : (header &&& 0x07).toUInt64 = size := by
      dsimp [header]
      rw [HeaderBits.tag4_small_size flag size.toUInt8 hs8]
      exact HeaderBits.u64_to_u8_to_u64_of_lt size
        (UInt64.lt_trans hs (by decide))
    rw [hdecodedFlag, if_pos hheader, hvalue]
    simp [u8Bytes]
    rfl
  · simp only [tag4Bytes, hs, if_false]
    let n := u64ByteCount size
    let header : UInt8 := (flag <<< 4) ||| 0x08 ||| (n - 1)
    change getTag4.run
      ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
        pre.size⟩ =
      .ok (⟨flag, size⟩,
        ⟨pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix,
          pre.size + (u8Bytes header ++ u64LEBytes size n.toNat).size⟩)
    have hbytes : pre ++ (u8Bytes header ++ u64LEBytes size n.toNat) ++ suffix =
        pre ++ u8Bytes header ++ (u64LEBytes size n.toNat ++ suffix) := by
      simp [ByteArray.append_assoc]
    rw [hbytes]
    have hhead := getU8_spec header pre
      (u64LEBytes size n.toNat ++ suffix)
    simp only [getTag4, StateT.run_bind]
    rw [hhead]
    simp only [bind, Except.bind]
    have hne : size ≠ 0 := by
      intro hzero
      subst size
      simp at hs
    have hnle : n ≤ 8 := by
      rw [UInt8.le_iff_toNat_le]
      exact u64ByteCount_le_eight size
    obtain ⟨hdecodedFlag, hn, hlarge⟩ := HeaderBits.tag4_large flag n hflag
      (by simpa [n] using HeaderBits.byteCount_pos_of_ne_zero size hne) hnle
    change header >>> 4 = flag at hdecodedFlag
    change (header &&& 0x07) + 1 = n at hn
    change ¬(header &&& 0x08 == 0) at hlarge
    rw [hdecodedFlag]
    rw [if_neg hlarge, hn]
    dsimp only [n]
    let next : UInt64 → GetM Tag4 := fun decoded => do
      if u64ByteCount decoded != u64ByteCount size then
        throw "getTag4: non-minimal size"
      if decoded < 8 then throw "getTag4: size must use small form"
      return ⟨flag, decoded⟩
    change (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
      ⟨pre ++ u8Bytes header ++
          (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
        pre.size + (u8Bytes header).size⟩ = _
    have hcont : GetSpec (next size) ByteArray.empty (Tag4.mk flag size) := by
      intro innerPre innerSuffix
      simp [next, hs]
      rfl
    have hpayload := GetSpec.bind
      (next := next) (getU64TrimmedLE_encoded_spec size) hcont
    simp only [ByteArray.append_empty] at hpayload
    have hpayload' :
        (getU64TrimmedLE (u64ByteCount size).toNat >>= next).run
          ⟨pre ++ u8Bytes header ++
              (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
            pre.size + (u8Bytes header).size⟩ =
          .ok (Tag4.mk flag size,
            ⟨pre ++ u8Bytes header ++
                (u64LEBytes size (u64ByteCount size).toNat ++ suffix),
              pre.size + (u8Bytes header).size +
                (u64LEBytes size (u64ByteCount size).toNat).size⟩) := by
      simpa only [ByteArray.append_assoc, ByteArray.size_append] using
        hpayload (pre ++ u8Bytes header) suffix
    rw [hpayload']
    simp [u8Bytes, ByteArray.size_append]
    omega

/-! ## Canonical reader inversions

These converses complement `GetSpec`: they recover the exact canonical prefix
from an arbitrary successful parse rather than starting from known bytes. -/

theorem getU8_canonical : GetCanonical getU8 u8Bytes := by
  intro pre rest value st' h
  rcases rest with ⟨⟨data⟩⟩
  cases data with
  | nil =>
    have hrest : (ByteArray.mk ⟨[]⟩) = ByteArray.empty := rfl
    rw [hrest] at h
    simp [getU8] at h
    change (Except.error "EOF") = Except.ok (value, st') at h
    contradiction
  | cons b bs =>
    let tail : ByteArray := ⟨⟨bs⟩⟩
    have hrest : (ByteArray.mk ⟨b :: bs⟩) = u8Bytes b ++ tail := by
      rfl
    rw [hrest] at h
    rw [← ByteArray.append_assoc] at h
    rw [getU8_spec b pre tail] at h
    cases h
    exact ⟨tail, hrest, by simp [hrest, ByteArray.append_assoc]⟩

theorem getBytes_canonical (n : Nat) :
    GetCanonical (getBytes n) (fun bytes => bytes) := by
  intro pre rest value st' h
  by_cases hn : n ≤ rest.size
  · simp [getBytes, ByteArray.size_append, hn] at h
    cases h
    let chunk := rest.extract 0 n
    let suffix := rest.extract n rest.size
    have hchunk :
        (pre ++ rest).extract pre.size (pre.size + n) = chunk := by
      simpa [chunk] using
        (ByteArray.extract_append_size_add (a := pre) (b := rest)
          (i := 0) (j := n))
    have hsplit : rest = chunk ++ suffix := by
      rw [show rest = rest.extract 0 rest.size by simp]
      exact ByteArray.extract_eq_extract_append_extract n (by omega) hn
    have hchunkSize : chunk.size = n := by
      simp [chunk, ByteArray.size_extract, hn]
    refine ⟨suffix, ?_, ?_⟩
    · simpa [hchunk] using hsplit
    · simp [hchunk, hchunkSize]
  · simp [getBytes, ByteArray.size_append, hn] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getU64TrimmedLE_canonical (n : Nat) :
    GetCanonical (getU64TrimmedLE n) (fun value => u64LEBytes value n) := by
  intro pre rest value st' h
  by_cases hn : n ≤ 8
  · simp only [getU64TrimmedLE, show ¬n > 8 by omega, if_false,
      StateT.run_bind] at h
    cases hc : (getBytes n).run ⟨pre ++ rest, pre.size⟩ with
    | error err =>
      rw [hc] at h
      contradiction
    | ok result =>
      rcases result with ⟨chunk, mid⟩
      rw [hc] at h
      simp at h
      cases h
      obtain ⟨suffix, hrest, hmid⟩ := getBytes_canonical n pre rest hc
      have hsize : chunk.size = n := by
        by_cases hnrest : n ≤ rest.size
        · have hc' := hc
          simp [getBytes, ByteArray.size_append, hnrest] at hc'
          cases hc'
          simp [ByteArray.size_extract, hnrest]
        · have hc' := hc
          simp [getBytes, ByteArray.size_append, hnrest] at hc'
          change (Except.error _) = Except.ok (chunk, mid) at hc'
          contradiction
      have hcanonical : u64LEBytes (u64OfLEBytes chunk) n = chunk := by
        rw [← hsize]
        exact u64LEBytes_of_decode chunk (by omega)
      refine ⟨suffix, ?_, ?_⟩
      · simpa [hcanonical] using hrest
      · simpa [hcanonical] using hmid
  · simp only [getU64TrimmedLE, show n > 8 by omega, if_true] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getTag0_canonical : GetCanonical getTag0 tag0Bytes := by
  intro pre rest tag st' h
  simp only [getTag0, StateT.run_bind] at h
  cases hh : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hh] at h
    contradiction
  | ok result =>
    rcases result with ⟨header, mid⟩
    rw [hh] at h
    simp only [bind, Except.bind] at h
    obtain ⟨afterHead, hrest, hmid⟩ := getU8_canonical pre rest hh
    let headPre := pre ++ u8Bytes header
    have hmid' : mid = ⟨headPre ++ afterHead, headPre.size⟩ := by
      rw [hmid]
      simp [headPre, hrest, ByteArray.append_assoc]
    rw [hmid'] at h
    by_cases hsmall : header &&& 0x80 == 0
    · simp [hsmall] at h
      cases h
      obtain ⟨hsize, hheader8⟩ :=
        (HeaderBits.tag0_canonical header).1 hsmall
      have hcanonical :
          tag0Bytes ⟨header.toUInt64 &&& 0x7F⟩ = u8Bytes header := by
        simp only [tag0Bytes, hsize, if_pos]
        rw [hheader8]
      refine ⟨afterHead, ?_, ?_⟩
      · simpa [hcanonical] using hrest
      · simp [headPre, hrest, hcanonical, ByteArray.append_assoc]
    · simp only [hsmall, Bool.false_eq_true, if_false] at h
      let next : UInt64 → GetM Tag0 := fun size => do
        if u64ByteCount size != (header &&& 0x7F) + 1 then
          throw "getTag0: non-minimal size"
        if size < 128 then throw "getTag0: size must use small form"
        return ⟨size⟩
      change (getU64TrimmedLE ((header &&& 0x7F) + 1).toNat >>= next).run
        ⟨headPre ++ afterHead, headPre.size⟩ = .ok (tag, st') at h
      simp only [StateT.run_bind] at h
      cases hp : (getU64TrimmedLE ((header &&& 0x7F) + 1).toNat).run
          ⟨headPre ++ afterHead, headPre.size⟩ with
      | error err =>
        rw [hp] at h
        simp only [bind, Except.bind] at h
        contradiction
      | ok payloadResult =>
        rcases payloadResult with ⟨size, afterPayload⟩
        rw [hp] at h
        simp only [bind, Except.bind] at h
        by_cases hcountEq :
            u64ByteCount size = (header &&& 0x7F) + 1
        · simp only [next, hcountEq] at h
          by_cases hsize : size < 128
          · simp [hsize] at h
            change (Except.error _) = Except.ok (tag, st') at h
            contradiction
          · simp only [hsize, if_false] at h
            simp at h
            cases h
            obtain ⟨suffix, hafterHead, hafterPayload⟩ :=
              getU64TrimmedLE_canonical ((header &&& 0x7F) + 1).toNat
                headPre afterHead hp
            have hheader8 := (HeaderBits.tag0_canonical header).2 hsmall
            refine ⟨suffix, ?_, ?_⟩
            · rw [hrest, hafterHead]
              simp [tag0Bytes, hsize, hcountEq, hheader8,
                ByteArray.append_assoc]
            · simpa [headPre, hrest, hafterHead, tag0Bytes, hsize,
                hcountEq, hheader8, ByteArray.append_assoc,
                Nat.add_assoc] using hafterPayload
        · simp [next, hcountEq] at h
          change (Except.error _) = Except.ok (tag, st') at h
          contradiction

theorem getTag2_canonical : GetCanonical getTag2 tag2Bytes := by
  intro pre rest tag st' h
  simp only [getTag2, StateT.run_bind] at h
  cases hh : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hh] at h
    contradiction
  | ok result =>
    rcases result with ⟨header, mid⟩
    rw [hh] at h
    simp only [bind, Except.bind] at h
    obtain ⟨afterHead, hrest, hmid⟩ := getU8_canonical pre rest hh
    let headPre := pre ++ u8Bytes header
    have hmid' : mid = ⟨headPre ++ afterHead, headPre.size⟩ := by
      rw [hmid]
      simp [headPre, hrest, ByteArray.append_assoc]
    rw [hmid'] at h
    by_cases hsmall : header &&& 0x20 == 0
    · simp [hsmall] at h
      cases h
      obtain ⟨hsize, hheader8⟩ :=
        (HeaderBits.tag2_canonical header).1 hsmall
      refine ⟨afterHead, ?_, ?_⟩
      · rw [hrest]
        simp [tag2Bytes, hsize, hheader8]
      · simp [headPre, hrest, tag2Bytes, hsize, hheader8,
          ByteArray.append_assoc]
    · simp only [hsmall, Bool.false_eq_true, if_false,
        ] at h
      let next : UInt64 → GetM Tag2 := fun size => do
        if u64ByteCount size != (header &&& 0x1F) + 1 then
          throw "getTag2: non-minimal size"
        if size < 32 then throw "getTag2: size must use small form"
        return ⟨header >>> 6, size⟩
      change (getU64TrimmedLE ((header &&& 0x1F) + 1).toNat >>= next).run
        ⟨headPre ++ afterHead, headPre.size⟩ = .ok (tag, st') at h
      simp only [StateT.run_bind] at h
      cases hp : (getU64TrimmedLE ((header &&& 0x1F) + 1).toNat).run
          ⟨headPre ++ afterHead, headPre.size⟩ with
      | error err =>
        rw [hp] at h
        simp only [bind, Except.bind] at h
        contradiction
      | ok payloadResult =>
        rcases payloadResult with ⟨size, afterPayload⟩
        rw [hp] at h
        simp only [bind, Except.bind] at h
        by_cases hcountEq :
            u64ByteCount size = (header &&& 0x1F) + 1
        · simp only [next, hcountEq] at h
          by_cases hsize : size < 32
          · simp [hsize] at h
            change (Except.error _) = Except.ok (tag, st') at h
            contradiction
          · simp only [hsize, if_false] at h
            simp at h
            cases h
            obtain ⟨suffix, hafterHead, hafterPayload⟩ :=
              getU64TrimmedLE_canonical ((header &&& 0x1F) + 1).toNat
                headPre afterHead hp
            have hheader8 := (HeaderBits.tag2_canonical header).2 hsmall
            refine ⟨suffix, ?_, ?_⟩
            · rw [hrest, hafterHead]
              simp [tag2Bytes, hsize, hcountEq, hheader8,
                ByteArray.append_assoc]
            · simpa [headPre, hrest, hafterHead, tag2Bytes, hsize,
                hcountEq, hheader8, ByteArray.append_assoc,
                Nat.add_assoc] using
                  hafterPayload
        · simp [next, hcountEq] at h
          change (Except.error _) = Except.ok (tag, st') at h
          contradiction

theorem getTag4_canonical : GetCanonical getTag4 tag4Bytes := by
  intro pre rest tag st' h
  simp only [getTag4, StateT.run_bind] at h
  cases hh : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err =>
    rw [hh] at h
    contradiction
  | ok result =>
    rcases result with ⟨header, mid⟩
    rw [hh] at h
    simp only [bind, Except.bind] at h
    obtain ⟨afterHead, hrest, hmid⟩ := getU8_canonical pre rest hh
    let headPre := pre ++ u8Bytes header
    have hmid' : mid = ⟨headPre ++ afterHead, headPre.size⟩ := by
      rw [hmid]
      simp [headPre, hrest, ByteArray.append_assoc]
    rw [hmid'] at h
    by_cases hsmall : header &&& 0x08 == 0
    · simp [hsmall] at h
      cases h
      obtain ⟨hsize, hheader8⟩ :=
        (HeaderBits.tag4_canonical header).1 hsmall
      refine ⟨afterHead, ?_, ?_⟩
      · rw [hrest]
        simp [tag4Bytes, hsize, hheader8]
      · simp [headPre, hrest, tag4Bytes, hsize, hheader8,
          ByteArray.append_assoc]
    · simp only [hsmall, Bool.false_eq_true, if_false] at h
      let next : UInt64 → GetM Tag4 := fun size => do
        if u64ByteCount size != (header &&& 0x07) + 1 then
          throw "getTag4: non-minimal size"
        if size < 8 then throw "getTag4: size must use small form"
        return ⟨header >>> 4, size⟩
      change (getU64TrimmedLE ((header &&& 0x07) + 1).toNat >>= next).run
        ⟨headPre ++ afterHead, headPre.size⟩ = .ok (tag, st') at h
      simp only [StateT.run_bind] at h
      cases hp : (getU64TrimmedLE ((header &&& 0x07) + 1).toNat).run
          ⟨headPre ++ afterHead, headPre.size⟩ with
      | error err =>
        rw [hp] at h
        simp only [bind, Except.bind] at h
        contradiction
      | ok payloadResult =>
        rcases payloadResult with ⟨size, afterPayload⟩
        rw [hp] at h
        simp only [bind, Except.bind] at h
        by_cases hcountEq :
            u64ByteCount size = (header &&& 0x07) + 1
        · simp only [next, hcountEq] at h
          by_cases hsize : size < 8
          · simp [hsize] at h
            change (Except.error _) = Except.ok (tag, st') at h
            contradiction
          · simp only [hsize, if_false] at h
            simp at h
            cases h
            obtain ⟨suffix, hafterHead, hafterPayload⟩ :=
              getU64TrimmedLE_canonical ((header &&& 0x07) + 1).toNat
                headPre afterHead hp
            have hheader8 := (HeaderBits.tag4_canonical header).2 hsmall
            refine ⟨suffix, ?_, ?_⟩
            · rw [hrest, hafterHead]
              simp [tag4Bytes, hsize, hcountEq, hheader8,
                ByteArray.append_assoc]
            · simpa [headPre, hrest, hafterHead, tag4Bytes, hsize,
                hcountEq, hheader8, ByteArray.append_assoc,
                Nat.add_assoc] using hafterPayload
        · simp [next, hcountEq] at h
          change (Except.error _) = Except.ok (tag, st') at h
          contradiction

/-! Top-level consequences used by structural codec proofs and regression
tests. These are intentionally restricted to the representable flag ranges. -/

theorem tag0_roundtrip (t : Tag0) :
    runGet getTag0 (runPut (putTag0 t)) = .ok t := by
  rw [runPut_eq_of_spec (putTag0_spec t)]
  exact runGet_eq_ok_of_spec (getTag0_encoded_spec t)

theorem tag2_roundtrip (t : Tag2) (hflag : t.flag < 4) :
    runGet getTag2 (runPut (putTag2 t)) = .ok t := by
  rw [runPut_eq_of_spec (putTag2_spec t)]
  exact runGet_eq_ok_of_spec (getTag2_encoded_spec t hflag)

theorem tag4_roundtrip (t : Tag4) (hflag : t.flag < 16) :
    runGet getTag4 (runPut (putTag4 t)) = .ok t := by
  rw [runPut_eq_of_spec (putTag4_spec t)]
  exact runGet_eq_ok_of_spec (getTag4_encoded_spec t hflag)

end Ix.Compiler.Ixon
