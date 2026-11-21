import Blake3.C
import Blake3.Pure

/-!
# BLAKE3 digests and canonical encodings

Every address, root and commitment in the pipeline is a 32-byte BLAKE3 digest of a canonical byte
encoding, as in Ix. Each kind of object is hashed under its own domain tag, so equal bytes of
different kinds never share an address.

`blake3` uses the native C implementation. `Blake3.Pure.digest` is the total Lean specification
of the same function; the tests check that the two agree.
-/

namespace IxAI

structure Digest where
  bytes : ByteArray

/-- Equality of the bytes, compared in place (`ByteArray.decEq`). -/
instance : DecidableEq Digest := fun a b =>
  match ByteArray.decEq a.bytes b.bytes with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun e => h (congrArg Digest.bytes e))

/-- `hash` of the bytes as an `Array UInt8` from index `i` on, folded into `h`, read in place
(`hashBytesFrom_eq`). -/
def hashBytesFrom (b : ByteArray) (i : Nat) (h : UInt64) : UInt64 :=
  if hi : i < b.size then hashBytesFrom b (i + 1) (mixHash h (hash b[i])) else h
termination_by b.size - i

theorem hashBytesFrom_eq (b : ByteArray) (i : Nat) (h : UInt64) :
    hashBytesFrom b i h = (b.data.toList.drop i).foldl (fun r a => mixHash r (hash a)) h := by
  fun_induction hashBytesFrom b i h with
  | case1 i h hi ih =>
    have hd : i < b.data.toList.length := by simpa [ByteArray.size_data] using hi
    rw [ih, List.drop_eq_getElem_cons hd]
    simp [ByteArray.getElem_eq_getElem_data]
  | case2 i h hi =>
    rw [List.drop_eq_nil_of_le (by simpa [ByteArray.size_data] using hi)]
    rfl

/-- The hash of the bytes as an `Array UInt8` (`hash_digest`), so hash tables keyed by digests keep
their layout and iteration order. -/
instance : Hashable Digest := ⟨fun d => hashBytesFrom d.bytes 0 7⟩

theorem hash_digest (d : Digest) : hash d = hash d.bytes.data := by
  show hashBytesFrom d.bytes 0 7 = _
  rw [hashBytesFrom_eq, List.drop_zero, Array.foldl_toList]
  rfl

def hexByte (b : UInt8) : String :=
  let d := Nat.toDigits 16 b.toNat
  String.join ((if d.length < 2 then '0' :: d else d).map toString)

def Digest.hex (d : Digest) : String := String.join (d.bytes.data.toList.map hexByte)

instance : ToString Digest := ⟨Digest.hex⟩
instance : Repr Digest := ⟨fun d _ => d.hex⟩
instance : Inhabited Digest := ⟨⟨ByteArray.mk (Array.replicate 32 0)⟩⟩

def Digest.short (d : Digest) : String := String.ofList (d.hex.toList.take 12)

/-- Digests are BLAKE3 outputs: 32 bytes. `Enc Digest` writes the bytes with no length prefix, so
every digest that is parsed or constructed from outside must have exactly this length. -/
def Digest.size : Nat := 32

def Digest.wellFormed (d : Digest) : Bool := d.bytes.size == Digest.size

/-- A digest from raw bytes, if there are exactly 32. -/
def Digest.ofBytes? (b : ByteArray) : Option Digest :=
  if b.size == Digest.size then some ⟨b⟩ else none

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A digest from 64 hexadecimal digits, either case, through lists: the specification of
`Digest.ofHex?` (`ofHex?_eq`). -/
def Digest.ofHexList? (s : String) : Option Digest := do
  let cs := s.toList
  unless cs.length == 64 do none
  let rec go : List Char → Option (List UInt8)
    | a :: b :: rest => do
      let hi ← hexVal a
      let lo ← hexVal b
      pure ((hi * 16 + lo).toUInt8 :: (← go rest))
    | _ => some []
  let bs ← go cs
  Digest.ofBytes? (ByteArray.mk bs.toArray)

/-- Reading hexadecimal digits: the bytes so far, a pending high digit, and whether every
character so far was a digit. -/
structure HexState where
  bytes : ByteArray
  hi : Nat
  pending : Bool
  ok : Bool

def HexState.step (st : HexState) (c : Char) : HexState :=
  if st.ok then
    match hexVal c with
    | none => { st with ok := false }
    | some v =>
      if st.pending then { st with bytes := st.bytes.push (st.hi * 16 + v).toUInt8, pending := false }
      else { st with hi := v, pending := true }
  else st

/-- A digest from 64 hexadecimal digits, either case, read straight into its bytes. -/
def Digest.ofHex? (s : String) : Option Digest :=
  if s.length == 64 then
    let st := s.foldl HexState.step ⟨ByteArray.emptyWithCapacity 32, 0, false, true⟩
    if st.ok then Digest.ofBytes? st.bytes else none
  else none

private theorem HexState.foldl_failed (cs : List Char) (b : ByteArray) (hi : Nat) (p : Bool) :
    cs.foldl HexState.step ⟨b, hi, p, false⟩ = ⟨b, hi, p, false⟩ := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [List.foldl_cons, HexState.step] using ih

private theorem HexState.foldl_go : ∀ (cs : List Char) (b : ByteArray) (hi : Nat), cs.length % 2 = 0 →
    (let st := cs.foldl HexState.step ⟨b, hi, false, true⟩; if st.ok then some st.bytes.data else none) =
      (Digest.ofHexList?.go cs).map fun bs => b.data ++ bs.toArray
  | [], b, hi, _ => by simp [Digest.ofHexList?.go]
  | [_], _, _, h => by simp at h
  | a :: c :: rest, b, hi, h => by
    have hr : rest.length % 2 = 0 := by simp at h; omega
    cases ha : hexVal a with
    | none => simp [HexState.step, ha, HexState.foldl_failed, Digest.ofHexList?.go]
    | some x =>
      cases hc : hexVal c with
      | none => simp [HexState.step, ha, hc, HexState.foldl_failed, Digest.ofHexList?.go]
      | some y =>
        have ih := HexState.foldl_go rest (b.push (x * 16 + y).toUInt8) x hr
        simp only [List.foldl_cons, HexState.step, ha, hc, Digest.ofHexList?.go] at ih ⊢
        simp only [ite_true, Bool.false_eq_true, ite_false] at ih ⊢
        rw [ih]
        cases Digest.ofHexList?.go rest <;> simp [ByteArray.data_push]

theorem Digest.ofHex?_eq (s : String) : Digest.ofHex? s = Digest.ofHexList? s := by
  unfold Digest.ofHex? Digest.ofHexList?
  rw [String.foldl_eq_foldl_toList]
  by_cases hl : s.length = 64
  · have h2 : s.toList.length % 2 = 0 := by rw [String.length_toList, hl]
    have key := HexState.foldl_go s.toList (ByteArray.emptyWithCapacity 32) 0 h2
    simp only [String.length_toList, hl, beq_self_eq_true, ite_true] at key ⊢
    revert key
    generalize s.toList.foldl HexState.step _ = st
    cases hst : st.ok <;> cases hgo : Digest.ofHexList?.go s.toList <;> simp_all [Digest.ofBytes?]
    intro hd
    have hb : st.bytes = ⟨_⟩ := ByteArray.ext (hd.trans Array.empty_append)
    rw [hb]
  · simp [String.length_toList, hl]

def blake3 (b : ByteArray) : Digest := ⟨(Blake3.C.hash b).val⟩

/-! ## Canonical encoding -/

class Enc (α : Type) where
  /-- Append the encoding of a value. -/
  enc : ByteArray → α → ByteArray

/-- Unsigned LEB128. -/
partial def encNat (b : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then b.push n.toUInt8 else encNat (b.push ((n % 128) + 128).toUInt8) (n / 128)

instance : Enc Nat := ⟨encNat⟩
instance : Enc Int := ⟨fun b i => encNat b (if i ≥ 0 then 2 * i.toNat else 2 * (-i).toNat - 1)⟩
instance : Enc Bool := ⟨fun b x => b.push (if x then 1 else 0)⟩
instance : Enc UInt64 := ⟨fun b x => encNat b x.toNat⟩
instance : Enc String := ⟨fun b s => let u := s.toUTF8; encNat b u.size ++ u⟩
instance : Enc Digest := ⟨fun b d => b ++ d.bytes⟩

instance {α : Type} [Enc α] : Enc (List α) :=
  ⟨fun b xs => xs.foldl Enc.enc (encNat b xs.length)⟩

instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun b (x, y) => Enc.enc (Enc.enc b x) y⟩

/-- The BLAKE3 digest of a value's encoding under a domain tag. -/
def digestOf {α : Type} [Enc α] (tag : String) (x : α) : Digest :=
  blake3 (Enc.enc (Enc.enc ByteArray.empty ("ixai/" ++ tag)) x)

end IxAI
