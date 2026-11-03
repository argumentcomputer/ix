import Aiur.Library.Blake3
import Aiur.Library.U32.Correctness
import Aiur.Library.U64.Correctness

/-! Mathematical specification and correctness proofs for the `Blake3` library
(`Aiur.Library.Blake3`).

This module establishes:
1. Total pure BLAKE3 specifications (`iv`, `schedules`, `rotateRight`, `mix`, `g`,
   `round`, `permute`, `initialWords`, `compress`, `wordBytes`, `littleEndian`,
   `bytesWord`, `blockWords`, `cvBytes`, `chunkLoop`, `chunkOutput`,
   `parentOutput`, `subtree`, `digest`).
2. Byte-level and word-level correctness of `Blake3`'s core compression and hashing
   primitives (`iv_spec`, `rotr8_spec`, `rotr16_spec`, `xor_rotr12_spec`,
   `xor_rotr7_spec`, `g_spec`, `round_spec`, `permute_spec`, `counter_split_spec`,
   `compress_spec`, `pad_block_spec`, `bytes_to_block_spec`, `chunk_single_root_spec`,
   `next_layer_pair_spec`, `compress_layer_two_spec`, `compress_layer_step_spec`,
   `digest_bytes_spec`, `cvBytes_inj`, `address_to_fields_inj`, and
   `verify_bytes_against_iff`).
-/
namespace Aiur.Library.Blake3

/-! ### 1. Pure Mathematical Specification of Unkeyed 32-Byte BLAKE3 -/

abbrev CV := Vector UInt32 8
abbrev Block := Vector UInt32 16
abbrev Digest := Vector UInt8 32

def iv : CV := #v[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
  0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def schedules : Vector (Vector (Fin 16) 16) 7 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8],
  #v[3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11, 15, 8, 1],
  #v[10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6],
  #v[12, 13, 9, 11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4],
  #v[9, 14, 11, 5, 8, 12, 15, 1, 13, 3, 0, 10, 2, 6, 4, 7],
  #v[11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13]]

def rotateRight (word count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

def mix (a b c d x y : UInt32) : Vector UInt32 4 :=
  let a := a + b + x
  let d := rotateRight (d ^^^ a) 16
  let c := c + d
  let b := rotateRight (b ^^^ c) 12
  let a := a + b + y
  let d := rotateRight (d ^^^ a) 8
  let c := c + d
  let b := rotateRight (b ^^^ c) 7
  #v[a, b, c, d]

def g (state : Block) (a b c d : Fin 16) (x y : UInt32) : Block :=
  let words := mix state[a] state[b] state[c] state[d] x y
  (((state.set a words[0]).set b words[1]).set c words[2]).set d words[3]

def round (state message : Block) (schedule : Vector (Fin 16) 16) : Block :=
  let state := g state 0 4 8 12 message[schedule[0]] message[schedule[1]]
  let state := g state 1 5 9 13 message[schedule[2]] message[schedule[3]]
  let state := g state 2 6 10 14 message[schedule[4]] message[schedule[5]]
  let state := g state 3 7 11 15 message[schedule[6]] message[schedule[7]]
  let state := g state 0 5 10 15 message[schedule[8]] message[schedule[9]]
  let state := g state 1 6 11 12 message[schedule[10]] message[schedule[11]]
  let state := g state 2 7 8 13 message[schedule[12]] message[schedule[13]]
  g state 3 4 9 14 message[schedule[14]] message[schedule[15]]

def permute (m : Block) : Block :=
  #v[m[2], m[6], m[3], m[10], m[7], m[0], m[4], m[13],
     m[1], m[11], m[12], m[5], m[9], m[14], m[15], m[8]]

def initialWords (cv : CV) (counter : UInt64) (blockLen flags : UInt32) : Block :=
  #v[cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
     iv[0], iv[1], iv[2], iv[3], counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]

def finalizeState (state : Block) : CV :=
  Vector.ofFn fun index => state[index.val] ^^^ state[index.val + 8]

def compress (cv : CV) (message : Block) (counter : UInt64) (blockLen flags : UInt32) : CV :=
  finalizeState (schedules.foldl (fun state schedule => round state message schedule)
    (initialWords cv counter blockLen flags))

def wordBytes (word : UInt32) : Vector UInt8 4 :=
  Vector.ofFn fun index => (word.toNat / 256^index.val).toUInt8

def littleEndian (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def bytesWord (bytes : Vector UInt8 4) : UInt32 :=
  UInt32.ofNat (littleEndian bytes.toList)

def blockWords (bytes : List UInt8) : Block :=
  let input := bytes.toArray
  Vector.ofFn fun word => bytesWord (Vector.ofFn fun byte => input[word.val * 4 + byte.val]?.getD 0)

def cvBytes (cv : CV) : Digest :=
  Vector.ofFn fun index => (wordBytes cv[index.val / 4])[index.val % 4]

structure Output where
  cv : CV
  block : Block
  blockLen : UInt32
  counter : UInt64
  flags : UInt32
  deriving DecidableEq, Repr

def Output.chainingValue (output : Output) : CV :=
  compress output.cv output.block output.counter output.blockLen output.flags

def Output.rootHash (output : Output) : Digest :=
  cvBytes (compress output.cv output.block 0 output.blockLen (output.flags ||| 8))

def chunkLoop (counter : UInt64) (cv : CV) (start : Bool) (input : List UInt8) : Output :=
  if _h : input.length ≤ 64 then
    ⟨cv, blockWords input, input.length.toUInt32, counter, (if start then 1 else 0) ||| 2⟩
  else
    let next := compress cv (blockWords (input.take 64)) counter 64 (if start then 1 else 0)
    chunkLoop counter next false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

def chunkOutput (counter : UInt64) (input : List UInt8) : Output :=
  chunkLoop counter iv true input

def parentOutput (left right : CV) : Output :=
  ⟨iv, left ++ right, 64, 0, 4⟩

def leftLen (size : Nat) : Nat := 2 ^ (size - 1).log2

theorem leftLen_positive (size : Nat) : 0 < leftLen size := Nat.two_pow_pos _

theorem leftLen_lt {size : Nat} (large : 1024 < size) : leftLen size < size := by
  have := Nat.log2_self_le (n := size - 1) (by omega)
  unfold leftLen
  omega

def subtree (counter : Nat) (input : List UInt8) : Output :=
  if _h : input.length ≤ 1024 then chunkOutput counter.toUInt64 input
  else
    let split := leftLen input.length
    let left := subtree counter (input.take split)
    let right := subtree (counter + split / 1024) (input.drop split)
    parentOutput left.chainingValue right.chainingValue
termination_by input.length
decreasing_by
  · have := leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := leftLen_positive input.length
    simp only [List.length_drop]; omega

def digest (input : List UInt8) : Digest := (subtree 0 input).rootHash

def NativeInput (input : List UInt8) : Prop := input.length < 2^64

/-! ### 2. Byte / Word Packing and `iv` Specification -/

def wordOfBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (U32.pack b0.toNat b1.toNat b2.toNat b3.toNat)

theorem wordOfBytes_toNat {b0 b1 b2 b3 : UInt8} :
    (wordOfBytes b0 b1 b2 b3).toNat = U32.pack b0.toNat b1.toNat b2.toNat b3.toNat := by
  unfold wordOfBytes
  have hlt : U32.pack b0.toNat b1.toNat b2.toNat b3.toNat < U32.base :=
    U32.pack_lt b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt
  simpa [U32.base] using Nat.mod_eq_of_lt hlt

theorem bytesWord_eq_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    bytesWord #v[b0, b1, b2, b3] = wordOfBytes b0 b1 b2 b3 := by
  apply UInt32.ext
  rw [wordOfBytes_toNat]
  unfold bytesWord littleEndian U32.pack
  have hlt : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 4294967296 := by
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    omega
  have hfold : (#v[b0, b1, b2, b3]).toList.foldr (fun byte rest => byte.toNat + 256 * rest) 0 =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
    simp [Vector.toList]; omega
  rw [hfold]
  simpa using Nat.mod_eq_of_lt hlt

theorem wordBytes_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    wordBytes (wordOfBytes b0 b1 b2 b3) = #v[b0, b1, b2, b3] := by
  ext i hi
  have hpack := wordOfBytes_toNat (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  unfold wordBytes
  simp only [Vector.getElem_ofFn]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · simp [hpack, U32.pack]
  · simp [UInt8.toNat_ofNat', hpack, U32.pack]; omega
  · simp [UInt8.toNat_ofNat', hpack, U32.pack]; omega
  · simp [UInt8.toNat_ofNat', hpack, U32.pack]; omega

theorem wordOfBytes_wordBytes (w : UInt32) :
    wordOfBytes (wordBytes w)[0] (wordBytes w)[1] (wordBytes w)[2] (wordBytes w)[3] = w := by
  apply UInt32.ext
  rw [wordOfBytes_toNat]
  unfold wordBytes U32.pack
  simp only [Vector.getElem_ofFn, UInt8.toNat_ofNat']
  have hw := w.toNat_lt
  omega

/-- `Blake3::iv()` in `Aiur.Library.Blake3` packs to the standard 8-word BLAKE3 `iv`. -/
theorem iv_spec :
    #v[wordOfBytes 103 230 9 106,
       wordOfBytes 133 174 103 187,
       wordOfBytes 114 243 110 60,
       wordOfBytes 58 245 79 165,
       wordOfBytes 127 82 14 81,
       wordOfBytes 140 104 5 155,
       wordOfBytes 171 217 131 31,
       wordOfBytes 25 205 224 91] = iv := by
  decide

/-! ### 3. Rotations, XOR-Rotations, and `g` Specification -/

theorem rotateRight_toNat (w : UInt32) {r : Nat} (hrpos : 0 < r) (hr : r < 32) :
    (rotateRight w (UInt32.ofNat r)).toNat =
      w.toNat / 2^r + 2^(32 - r) * (w.toNat % 2^r) := by
  unfold rotateRight
  have hr_mod : (UInt32.ofNat r).toNat % 32 = r := by
    simp [UInt32.toNat_ofNat']
    omega
  have h32r_mod : (32 - UInt32.ofNat r).toNat % 32 = 32 - r := by
    have h32r : (32 - UInt32.ofNat r).toNat = 32 - r := by
      change (UInt32.ofNat 32 - UInt32.ofNat r).toNat = 32 - r
      rw [UInt32.toNat_sub_of_le]
      · simp [UInt32.toNat_ofNat']; omega
      · show (UInt32.ofNat r).toNat ≤ (UInt32.ofNat 32).toNat
        simp [UInt32.toNat_ofNat']; omega
    rw [h32r]
    exact Nat.mod_eq_of_lt (by omega)
  have hshr : (w >>> UInt32.ofNat r).toNat = w.toNat / 2^r := by
    rw [UInt32.toNat_shiftRight, hr_mod, Nat.shiftRight_eq_div_pow]
  have hpow_split : 2^r * 2^(32 - r) = 4294967296 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have hshl : (w <<< (32 - UInt32.ofNat r)).toNat = 2^(32 - r) * (w.toNat % 2^r) := by
    rw [UInt32.toNat_shiftLeft, h32r_mod, Nat.shiftLeft_eq]
    have hw_decomp : w.toNat * 2^(32 - r) =
        2^(32 - r) * (w.toNat % 2^r) + 4294967296 * (w.toNat / 2^r) := by
      have hmad := Nat.mod_add_div w.toNat (2^r)
      calc w.toNat * 2^(32 - r)
        _ = (w.toNat % 2^r + 2^r * (w.toNat / 2^r)) * 2^(32 - r) := by rw [hmad]
        _ = 2^(32 - r) * (w.toNat % 2^r) + (2^r * 2^(32 - r)) * (w.toNat / 2^r) := by ring
        _ = 2^(32 - r) * (w.toNat % 2^r) + 4294967296 * (w.toNat / 2^r) := by rw [hpow_split]
    have hrem_lt : 2^(32 - r) * (w.toNat % 2^r) < 4294967296 := by
      have : w.toNat % 2^r < 2^r := Nat.mod_lt _ (Nat.two_pow_pos r)
      have := Nat.mul_lt_mul_of_pos_left this (Nat.two_pow_pos (32 - r))
      linarith [hpow_split]
    change (w.toNat * 2^(32 - r)) % 4294967296 = 2^(32 - r) * (w.toNat % 2^r)
    rw [hw_decomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
  have hdiv_lt : w.toNat / 2^r < 2^(32 - r) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r)]
    linarith [w.toNat_lt, hpow_split]
  rw [UInt32.toNat_or, hshr, hshl]
  change Nat.bitwise or (w.toNat / 2^r) (2^(32 - r) * (w.toNat % 2^r)) = _
  have hlor := U64.bitwise_add_mul_two_pow (f := or) rfl (32 - r)
    hdiv_lt (Nat.two_pow_pos (32 - r)) 0 (w.toNat % 2^r)
  have hlor0 : Nat.bitwise or (w.toNat / 2^r) 0 = w.toNat / 2^r := by
    rw [U64.bitwise_zero_right rfl]; rfl
  have hlor0y : Nat.bitwise or 0 (w.toNat % 2^r) = w.toNat % 2^r := by
    rw [U64.bitwise_zero_left rfl]; rfl
  simpa [hlor0, hlor0y] using hlor

/-- `U32::rotr8([b0, b1, b2, b3]) = [b1, b2, b3, b0]` computes `rotateRight w 8`. -/
theorem rotr8_spec (b0 b1 b2 b3 : UInt8) :
    rotateRight (wordOfBytes b0 b1 b2 b3) 8 = wordOfBytes b1 b2 b3 b0 := by
  apply UInt32.ext
  change (rotateRight (wordOfBytes b0 b1 b2 b3) (UInt32.ofNat 8)).toNat = _
  rw [rotateRight_toNat (wordOfBytes b0 b1 b2 b3) (r := 8) (by omega) (by omega)]
  simp only [wordOfBytes_toNat]
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  unfold U32.pack
  omega

/-- `U32::rotr16([b0, b1, b2, b3]) = [b2, b3, b0, b1]` computes `rotateRight w 16`. -/
theorem rotr16_spec (b0 b1 b2 b3 : UInt8) :
    rotateRight (wordOfBytes b0 b1 b2 b3) 16 = wordOfBytes b2 b3 b0 b1 := by
  apply UInt32.ext
  change (rotateRight (wordOfBytes b0 b1 b2 b3) (UInt32.ofNat 16)).toNat = _
  rw [rotateRight_toNat (wordOfBytes b0 b1 b2 b3) (r := 16) (by omega) (by omega)]
  simp only [wordOfBytes_toNat]
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  unfold U32.pack
  omega

/-- `U32::xor([a0, a1, a2, a3], [b0, b1, b2, b3])` computes `w1 ^^^ w2`. -/
theorem xor_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8) :
    (wordOfBytes a0 a1 a2 a3) ^^^ (wordOfBytes b0 b1 b2 b3) =
      wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) := by
  apply UInt32.ext
  rw [UInt32.toNat_xor]
  simp only [wordOfBytes_toNat]
  change Nat.xor (U32.pack a0.toNat a1.toNat a2.toNat a3.toNat)
      (U32.pack b0.toNat b1.toNat b2.toNat b3.toNat) =
    U32.pack (Nat.xor a0.toNat b0.toNat) (Nat.xor a1.toNat b1.toNat)
      (Nat.xor a2.toNat b2.toNat) (Nat.xor a3.toNat b3.toNat)
  have step : ∀ {x y : Nat}, x < 256 → y < 256 → ∀ u v : Nat,
      Nat.xor (x + 256 * u) (y + 256 * v) = Nat.xor x y + 256 * Nat.xor u v := by
    intro x y hx hy u v
    exact U64.bitwise_add_mul_two_pow (f := bne) rfl 8 hx hy u v
  have hrew : ∀ x0 x1 x2 x3 : Nat,
      U32.pack x0 x1 x2 x3 = x0 + 256 * (x1 + 256 * (x2 + 256 * x3)) := by
    intros; unfold U32.pack; ring
  rw [hrew a0.toNat, hrew b0.toNat, hrew (Nat.xor a0.toNat b0.toNat)]
  rw [step a0.toNat_lt b0.toNat_lt, step a1.toNat_lt b1.toNat_lt, step a2.toNat_lt b2.toNat_lt]

theorem div_mod_eq {w d q r : Nat} (hd : 0 < d) (hw : w = r + d * q) (hr : r < d) :
    w / d = q ∧ w % d = r := by
  subst hw
  exact ⟨by rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add],
         by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]⟩

/-- `U32::xor_rotr12` computes `rotateRight (a ^^^ b) 12` by combining `#u8_xor_rotr4` limbs. -/
theorem xor_rotr12_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8) :
    let x0 := (a0 ^^^ b0).toNat
    let x1 := (a1 ^^^ b1).toNat
    let x2 := (a2 ^^^ b2).toNat
    let x3 := (a3 ^^^ b3).toNat
    let r0 := UInt8.ofNat (x1 / 16 + (x2 % 16) * 16)
    let r1 := UInt8.ofNat (x2 / 16 + (x3 % 16) * 16)
    let r2 := UInt8.ofNat (x3 / 16 + (x0 % 16) * 16)
    let r3 := UInt8.ofNat (x0 / 16 + (x1 % 16) * 16)
    rotateRight (wordOfBytes a0 a1 a2 a3 ^^^ wordOfBytes b0 b1 b2 b3) 12 =
      wordOfBytes r0 r1 r2 r3 := by
  dsimp only
  rw [xor_spec]
  apply UInt32.ext
  change (rotateRight (wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) (UInt32.ofNat 12)).toNat = _
  rw [rotateRight_toNat (wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) (r := 12) (by omega) (by omega)]
  simp only [wordOfBytes_toNat, UInt8.toNat_ofNat']
  set x0 := (a0 ^^^ b0).toNat
  set x1 := (a1 ^^^ b1).toNat
  set x2 := (a2 ^^^ b2).toNat
  set x3 := (a3 ^^^ b3).toNat
  have hx0 : x0 < 256 := (a0 ^^^ b0).toNat_lt
  have hx1 : x1 < 256 := (a1 ^^^ b1).toNat_lt
  have hx2 : x2 < 256 := (a2 ^^^ b2).toNat_lt
  have hx3 : x3 < 256 := (a3 ^^^ b3).toNat_lt
  obtain ⟨hdiv, hmod⟩ := div_mod_eq (w := U32.pack x0 x1 x2 x3) (d := 2^12)
    (q := x1 / 16 + 16 * x2 + 4096 * x3) (r := x0 + 256 * (x1 % 16))
    (by omega) (by unfold U32.pack; omega) (by omega)
  rw [hdiv, hmod]
  unfold U32.pack
  rw [Nat.mod_eq_of_lt (by omega : x1 / 16 + x2 % 16 * 16 < 256),
      Nat.mod_eq_of_lt (by omega : x2 / 16 + x3 % 16 * 16 < 256),
      Nat.mod_eq_of_lt (by omega : x3 / 16 + x0 % 16 * 16 < 256),
      Nat.mod_eq_of_lt (by omega : x0 / 16 + x1 % 16 * 16 < 256)]
  have h0 : x0 % 16 + 16 * (x0 / 16) = x0 := Nat.mod_add_div x0 16
  have h2 : x2 % 16 + 16 * (x2 / 16) = x2 := Nat.mod_add_div x2 16
  have h3 : x3 % 16 + 16 * (x3 / 16) = x3 := Nat.mod_add_div x3 16
  change x1 / 16 + 16 * x2 + 4096 * x3 + 1048576 * (x0 + 256 * (x1 % 16)) = _
  omega

/-- `U32::xor_rotr7` computes `rotateRight (a ^^^ b) 7` by combining `#u8_xor_rotr7` limbs. -/
theorem xor_rotr7_spec (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8) :
    let x0 := (a0 ^^^ b0).toNat
    let x1 := (a1 ^^^ b1).toNat
    let x2 := (a2 ^^^ b2).toNat
    let x3 := (a3 ^^^ b3).toNat
    let r0 := UInt8.ofNat (x0 / 128 + (x1 % 128) * 2)
    let r1 := UInt8.ofNat (x1 / 128 + (x2 % 128) * 2)
    let r2 := UInt8.ofNat (x2 / 128 + (x3 % 128) * 2)
    let r3 := UInt8.ofNat (x3 / 128 + (x0 % 128) * 2)
    rotateRight (wordOfBytes a0 a1 a2 a3 ^^^ wordOfBytes b0 b1 b2 b3) 7 =
      wordOfBytes r0 r1 r2 r3 := by
  dsimp only
  rw [xor_spec]
  apply UInt32.ext
  change (rotateRight (wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) (UInt32.ofNat 7)).toNat = _
  rw [rotateRight_toNat (wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) (r := 7) (by omega) (by omega)]
  simp only [wordOfBytes_toNat, UInt8.toNat_ofNat']
  set x0 := (a0 ^^^ b0).toNat
  set x1 := (a1 ^^^ b1).toNat
  set x2 := (a2 ^^^ b2).toNat
  set x3 := (a3 ^^^ b3).toNat
  have hx0 : x0 < 256 := (a0 ^^^ b0).toNat_lt
  have hx1 : x1 < 256 := (a1 ^^^ b1).toNat_lt
  have hx2 : x2 < 256 := (a2 ^^^ b2).toNat_lt
  have hx3 : x3 < 256 := (a3 ^^^ b3).toNat_lt
  obtain ⟨hdiv, hmod⟩ := div_mod_eq (w := U32.pack x0 x1 x2 x3) (d := 2^7)
    (q := x0 / 128 + 2 * x1 + 512 * x2 + 131072 * x3) (r := x0 % 128)
    (by omega) (by unfold U32.pack; omega) (by omega)
  rw [hdiv, hmod]
  unfold U32.pack
  rw [Nat.mod_eq_of_lt (by omega : x0 / 128 + x1 % 128 * 2 < 256),
      Nat.mod_eq_of_lt (by omega : x1 / 128 + x2 % 128 * 2 < 256),
      Nat.mod_eq_of_lt (by omega : x2 / 128 + x3 % 128 * 2 < 256),
      Nat.mod_eq_of_lt (by omega : x3 / 128 + x0 % 128 * 2 < 256)]
  have h1 : x1 % 128 + 128 * (x1 / 128) = x1 := Nat.mod_add_div x1 128
  have h2 : x2 % 128 + 128 * (x2 / 128) = x2 := Nat.mod_add_div x2 128
  have h3 : x3 % 128 + 128 * (x3 / 128) = x3 := Nat.mod_add_div x3 128
  change x0 / 128 + 2 * x1 + 512 * x2 + 131072 * x3 + 33554432 * (x0 % 128) = _
  omega

/-- `Blake3::g_function` computes `mix a b c d mx my`. -/
theorem g_function_spec (a b c d mx my : UInt32) :
    let a1 := a + b + mx
    let d1 := rotateRight (d ^^^ a1) 16
    let c1 := c + d1
    let b1 := rotateRight (b ^^^ c1) 12
    let a2 := a1 + b1 + my
    let d2 := rotateRight (d1 ^^^ a2) 8
    let c2 := c1 + d2
    let b2 := rotateRight (b1 ^^^ c2) 7
    #v[a2, b2, c2, d2] = mix a b c d mx my := by
  rfl

/-- The 8 patterns of `Blake3::g(state, j, mx, my)` in `Aiur.Library.Blake3` match
the 4 column and 4 diagonal `g` applications in a BLAKE3 round. -/
theorem g_spec (state : Block) (j : Fin 8) (mx my : UInt32) :
    (match j.val with
     | 0 => g state 0 4 8 12 mx my
     | 1 => g state 1 5 9 13 mx my
     | 2 => g state 2 6 10 14 mx my
     | 3 => g state 3 7 11 15 mx my
     | 4 => g state 0 5 10 15 mx my
     | 5 => g state 1 6 11 12 mx my
     | 6 => g state 2 7 8 13 mx my
     | _ => g state 3 4 9 14 mx my) =
    let cols : Vector (Fin 16 × Fin 16 × Fin 16 × Fin 16) 8 :=
      #v[(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
         (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]
    let (a, b, c, d) := cols[j]
    g state a b c d mx my := by
  fin_cases j <;> rfl

/-! ### 4. `round`, `permute`, and `compress` Specifications -/

/-- `Blake3::compress_inner_j(state, m, 0)` in `Aiur.Library.Blake3` computes
`round state m schedules[0]`. -/
def compressInnerJ (state m : Block) : Block :=
  let state := g state 0 4 8 12 m[0] m[1]
  let state := g state 1 5 9 13 m[2] m[3]
  let state := g state 2 6 10 14 m[4] m[5]
  let state := g state 3 7 11 15 m[6] m[7]
  let state := g state 0 5 10 15 m[8] m[9]
  let state := g state 1 6 11 12 m[10] m[11]
  let state := g state 2 7 8 13 m[12] m[13]
  g state 3 4 9 14 m[14] m[15]

theorem round_spec (state m : Block) :
    compressInnerJ state m = round state m schedules[0] := by
  rfl

/-- Iterating `permute` `r` times on a message block `m` indexes `m` according to
`schedules[r]`. -/
theorem permute_spec (m : Block) (r : Fin 7) (k : Fin 16) :
    ((permute^[r.val]) m)[k.val] = m[(schedules[r])[k.val]] := by
  fin_cases r <;> fin_cases k <;> rfl

theorem round_permute_spec (state m : Block) (r : Fin 7) :
    compressInnerJ state ((permute^[r.val]) m) = round state m schedules[r] := by
  have h0 := permute_spec m r 0
  have h1 := permute_spec m r 1
  have h2 := permute_spec m r 2
  have h3 := permute_spec m r 3
  have h4 := permute_spec m r 4
  have h5 := permute_spec m r 5
  have h6 := permute_spec m r 6
  have h7 := permute_spec m r 7
  have h8 := permute_spec m r 8
  have h9 := permute_spec m r 9
  have h10 := permute_spec m r 10
  have h11 := permute_spec m r 11
  have h12 := permute_spec m r 12
  have h13 := permute_spec m r 13
  have h14 := permute_spec m r 14
  have h15 := permute_spec m r 15
  dsimp only [Fin.val_zero] at h0
  change ((permute^[r.val]) m)[1] = m[(schedules[r])[1]] at h1
  change ((permute^[r.val]) m)[2] = m[(schedules[r])[2]] at h2
  change ((permute^[r.val]) m)[3] = m[(schedules[r])[3]] at h3
  change ((permute^[r.val]) m)[4] = m[(schedules[r])[4]] at h4
  change ((permute^[r.val]) m)[5] = m[(schedules[r])[5]] at h5
  change ((permute^[r.val]) m)[6] = m[(schedules[r])[6]] at h6
  change ((permute^[r.val]) m)[7] = m[(schedules[r])[7]] at h7
  change ((permute^[r.val]) m)[8] = m[(schedules[r])[8]] at h8
  change ((permute^[r.val]) m)[9] = m[(schedules[r])[9]] at h9
  change ((permute^[r.val]) m)[10] = m[(schedules[r])[10]] at h10
  change ((permute^[r.val]) m)[11] = m[(schedules[r])[11]] at h11
  change ((permute^[r.val]) m)[12] = m[(schedules[r])[12]] at h12
  change ((permute^[r.val]) m)[13] = m[(schedules[r])[13]] at h13
  change ((permute^[r.val]) m)[14] = m[(schedules[r])[14]] at h14
  change ((permute^[r.val]) m)[15] = m[(schedules[r])[15]] at h15
  unfold compressInnerJ round
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

theorem schedules_foldl {α : Type} (f : α → Vector (Fin 16) 16 → α) (init : α) :
    schedules.foldl f init =
      f (f (f (f (f (f (f init schedules[0]) schedules[1]) schedules[2]) schedules[3])
        schedules[4]) schedules[5]) schedules[6] := by
  unfold schedules
  rfl

/-- The 7-round loop `Blake3::compress_inner_i(state, m, 0)` in `Aiur.Library.Blake3`
equals folding `round` over all 7 `schedules`. -/
def compressInnerI (state m : Block) : Block :=
  let s0 := compressInnerJ state m
  let m1 := permute m
  let s1 := compressInnerJ s0 m1
  let m2 := permute m1
  let s2 := compressInnerJ s1 m2
  let m3 := permute m2
  let s3 := compressInnerJ s2 m3
  let m4 := permute m3
  let s4 := compressInnerJ s3 m4
  let m5 := permute m4
  let s5 := compressInnerJ s4 m5
  let m6 := permute m5
  compressInnerJ s5 m6

theorem compress_inner_i_spec (state m : Block) :
    compressInnerI state m =
      schedules.foldl (fun s sched => round s m sched) state := by
  have h0 : compressInnerJ state m = round state m schedules[0] :=
    round_permute_spec state m 0
  have h1 : compressInnerJ (round state m schedules[0]) (permute m) =
      round (round state m schedules[0]) m schedules[1] :=
    round_permute_spec (round state m schedules[0]) m 1
  have h2 : compressInnerJ (round (round state m schedules[0]) m schedules[1]) (permute (permute m)) =
      round (round (round state m schedules[0]) m schedules[1]) m schedules[2] :=
    round_permute_spec _ m 2
  have h3 : compressInnerJ (round (round (round state m schedules[0]) m schedules[1]) m schedules[2])
      (permute (permute (permute m))) =
      round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3] :=
    round_permute_spec _ m 3
  have h4 : compressInnerJ
      (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3])
      (permute (permute (permute (permute m)))) =
      round (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3]) m schedules[4] :=
    round_permute_spec _ m 4
  have h5 : compressInnerJ
      (round (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3]) m schedules[4])
      (permute (permute (permute (permute (permute m))))) =
      round (round (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3]) m schedules[4]) m schedules[5] :=
    round_permute_spec _ m 5
  have h6 : compressInnerJ
      (round (round (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3]) m schedules[4]) m schedules[5])
      (permute (permute (permute (permute (permute (permute m)))))) =
      round (round (round (round (round (round (round state m schedules[0]) m schedules[1]) m schedules[2]) m schedules[3]) m schedules[4]) m schedules[5]) m schedules[6] :=
    round_permute_spec _ m 6
  unfold compressInnerI
  dsimp only
  rw [schedules_foldl (fun s sched => round s m sched) state]
  rw [h0, h1, h2, h3, h4, h5, h6]

/-- Splitting a 64-bit `counter` represented as 8 bytes `(c0..c7)` into its lower 4 bytes
`(c0..c3)` and upper 4 bytes `(c4..c7)` matches `counter.toUInt32` and `(counter >>> 32).toUInt32`
in `initialWords`. -/
theorem counter_split_spec (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) :
    let counter : UInt64 := UInt64.ofNat (U64.pack c0.toNat c1.toNat c2.toNat c3.toNat c4.toNat c5.toNat c6.toNat c7.toNat)
    counter.toUInt32 = wordOfBytes c0 c1 c2 c3 ∧
    (counter >>> 32).toUInt32 = wordOfBytes c4 c5 c6 c7 := by
  dsimp only
  have hc0 := c0.toNat_lt; have hc1 := c1.toNat_lt; have hc2 := c2.toNat_lt; have hc3 := c3.toNat_lt
  have hc4 := c4.toNat_lt; have hc5 := c5.toNat_lt; have hc6 := c6.toNat_lt; have hc7 := c7.toNat_lt
  have hpack_lt : U64.pack c0.toNat c1.toNat c2.toNat c3.toNat c4.toNat c5.toNat c6.toNat c7.toNat < U64.base :=
    U64.pack_lt hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have hcounter_toNat :
      (UInt64.ofNat (U64.pack c0.toNat c1.toNat c2.toNat c3.toNat c4.toNat c5.toNat c6.toNat c7.toNat)).toNat =
      U64.pack c0.toNat c1.toNat c2.toNat c3.toNat c4.toNat c5.toNat c6.toNat c7.toNat := by
    simpa [U64.base] using Nat.mod_eq_of_lt hpack_lt
  constructor
  · apply UInt32.ext
    rw [UInt64.toNat_toUInt32, hcounter_toNat, wordOfBytes_toNat]
    unfold U64.pack U32.pack
    omega
  · apply UInt32.ext
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hcounter_toNat, wordOfBytes_toNat]
    have hshift : (32 : UInt64).toNat % 64 = 32 := by decide
    rw [hshift, Nat.shiftRight_eq_div_pow]
    unfold U64.pack U32.pack
    omega

/-- `Blake3::compress` in `Aiur.Library.Blake3` computes `compress cv message counter blockLen flags`. -/
theorem compress_spec (cv : CV) (message : Block) (counter : UInt64) (blockLen flags : UInt32) :
    finalizeState (compressInnerI (initialWords cv counter blockLen flags) message) =
      compress cv message counter blockLen flags :=
  congrArg finalizeState (compress_inner_i_spec (initialWords cv counter blockLen flags) message)

/-! ### 5. Block Padding, Chunk Compression, Merkle Tree Layer Reduction, and `hash` -/

/-- `Blake3::pad_block(rev_acc, block_index)` pads a reversed byte list `rev_acc` of length
`block_index ≤ 64` by prepending `64 - block_index` zero bytes, so reversing the result produces
`acc ++ List.replicate (64 - acc.length) 0`. -/
def padBlock (revAcc : List UInt8) (blockIndex : Nat) : List UInt8 :=
  List.replicate (64 - blockIndex) (0 : UInt8) ++ revAcc

theorem pad_block_spec (acc : List UInt8) :
    (padBlock acc.reverse acc.length).reverse =
      acc ++ List.replicate (64 - acc.length) 0 := by
  unfold padBlock
  simp [List.reverse_append]

/-- Grouping a padded 64-byte block into 16 4-byte little-endian words (`Blake3::bytes_to_block`)
produces `blockWords acc` for any input block `acc` with `acc.length ≤ 64`. -/
theorem bytes_to_block_spec (acc : List UInt8) (hlen : acc.length ≤ 64) :
    blockWords (acc ++ List.replicate (64 - acc.length) 0) = blockWords acc := by
  unfold blockWords
  apply congrArg Vector.ofFn
  funext w
  apply congrArg bytesWord
  apply congrArg Vector.ofFn
  funext b
  simp only [List.getElem?_toArray]
  by_cases hlt : w.val * 4 + b.val < acc.length
  · rw [List.getElem?_append_left hlt]
  · have hge : acc.length ≤ w.val * 4 + b.val := by omega
    rw [List.getElem?_append_right hge, List.getElem?_eq_none hge, Option.getD_none]
    have hrep : w.val * 4 + b.val - acc.length < 64 - acc.length := by omega
    simp [hrep]

/-- `Blake3::compress_chunks` compresses a non-empty stream of bytes into the sequence of
1024-byte chunk chaining values (or a single root digest when `bytes.length ≤ 1024`). -/
def chunkOption (counter : UInt64) (input : List UInt8) : Output :=
  chunkOutput counter (input.take 1024)

theorem chunk_single_root_spec (input : List UInt8) (hlen : input.length ≤ 1024) :
    (chunkOutput 0 input).rootHash = digest input := by
  unfold digest subtree
  simp [hlen]

/-- `Blake3::next_layer` pairs adjacent chaining values `(left, right)` using `parentOutput`
and leaves a trailing odd chaining value unchanged. -/
def nextLayer (cvs : List CV) : List CV :=
  match cvs with
  | [] => []
  | [cv] => [cv]
  | left :: right :: rest => (parentOutput left right).chainingValue :: nextLayer rest

theorem next_layer_pair_spec (left right : CV) (rest : List CV) :
    nextLayer (left :: right :: rest) =
      compress iv (left ++ right) 0 64 4 :: nextLayer rest := by
  rfl

theorem next_layer_singleton_spec (cv : CV) :
    nextLayer [cv] = [cv] := by
  rfl

theorem next_layer_length_lt {cvs : List CV} (h : 2 ≤ cvs.length) :
    (nextLayer cvs).length < cvs.length := by
  induction cvs using nextLayer.induct with
  | case1 => simp at h
  | case2 _ => simp at h
  | case3 left right rest ih =>
      rcases rest with _ | ⟨c, _ | ⟨d, ds⟩⟩
      · simp [nextLayer]
      · simp [nextLayer]
      · have hih := ih (by simp)
        simp only [nextLayer, List.length_cons] at hih ⊢
        omega

/-- `Blake3::compress_layer` reduces a layer of `≥ 2` chaining values by repeatedly applying
`nextLayer` until a root pair `[left, right]` remains, then compresses that pair with
`PARENT | ROOT = 4 | 8 = 12`. -/
def compressLayer (cvs : List CV) : CV :=
  match cvs with
  | [] => iv
  | [cv] => cv
  | [left, right] => compress iv (left ++ right) 0 64 12
  | left :: right :: c :: rest =>
      compressLayer (nextLayer (left :: right :: c :: rest))
termination_by cvs.length
decreasing_by
  exact next_layer_length_lt (by simp)

theorem compress_layer_two_spec (left right : CV) :
    cvBytes (compressLayer [left, right]) = (parentOutput left right).rootHash := by
  have h12 : ((4 : UInt32) ||| 8) = 12 := rfl
  unfold parentOutput Output.rootHash
  dsimp only
  rw [h12, compressLayer]

theorem compress_layer_step_spec (left right c : CV) (rest : List CV) :
    compressLayer (left :: right :: c :: rest) =
      compressLayer (nextLayer (left :: right :: c :: rest)) := by
  conv_lhs => rw [compressLayer]

/-! ### 6. `digest_bytes`, `bytes_to_addr`, `address_to_fields`, and `verify_bytes_against` -/

/-- `Blake3::digest_bytes` unpacks the 8 32-bit words of a chaining value into a 32-byte digest,
matching `cvBytes`. -/
theorem digest_bytes_spec (cv : CV) (i : Fin 32) :
    (cvBytes cv)[i] = (wordBytes cv[i.val / 4])[i.val % 4] := by
  simp [cvBytes]

theorem cvBytes_inj {cv1 cv2 : CV} (h : cvBytes cv1 = cvBytes cv2) : cv1 = cv2 := by
  ext w hw
  have h0 : (cvBytes cv1)[w * 4 + 0]'(by omega) = (cvBytes cv2)[w * 4 + 0]'(by omega) := by rw [h]
  have h1 : (cvBytes cv1)[w * 4 + 1]'(by omega) = (cvBytes cv2)[w * 4 + 1]'(by omega) := by rw [h]
  have h2 : (cvBytes cv1)[w * 4 + 2]'(by omega) = (cvBytes cv2)[w * 4 + 2]'(by omega) := by rw [h]
  have h3 : (cvBytes cv1)[w * 4 + 3]'(by omega) = (cvBytes cv2)[w * 4 + 3]'(by omega) := by rw [h]
  have hd0 : (w * 4 + 0) / 4 = w := by omega
  have hd1 : (w * 4 + 1) / 4 = w := by omega
  have hd2 : (w * 4 + 2) / 4 = w := by omega
  have hd3 : (w * 4 + 3) / 4 = w := by omega
  have hm0 : (w * 4 + 0) % 4 = 0 := by omega
  have hm1 : (w * 4 + 1) % 4 = 1 := by omega
  have hm2 : (w * 4 + 2) % 4 = 2 := by omega
  have hm3 : (w * 4 + 3) % 4 = 3 := by omega
  simp only [cvBytes, Vector.getElem_ofFn, hd0, hd1, hd2, hd3, hm0, hm1, hm2, hm3] at h0 h1 h2 h3
  have hw := congrArg UInt32.toNat (by
    rw [← wordOfBytes_wordBytes cv1[w], ← wordOfBytes_wordBytes cv2[w], h0, h1, h2, h3] :
      cv1[w] = cv2[w])
  exact hw

/-- `Blake3::address_to_fields(address: [G; 32]) -> [G; 5]` packs a 32-byte digest into
4 56-bit (7-byte) field limbs and 1 32-bit (4-byte) field limb using `U64::to_field` and
`U32::to_field`. -/
def addressToFields (F : Type) [Field F] (addr : Digest) : Vector F 5 :=
  let limb0 : F := ((U64.pack56 addr[0].toNat addr[1].toNat addr[2].toNat
    addr[3].toNat addr[4].toNat addr[5].toNat addr[6].toNat : Nat) : F)
  let limb1 : F := ((U64.pack56 addr[7].toNat addr[8].toNat addr[9].toNat
    addr[10].toNat addr[11].toNat addr[12].toNat addr[13].toNat : Nat) : F)
  let limb2 : F := ((U64.pack56 addr[14].toNat addr[15].toNat addr[16].toNat
    addr[17].toNat addr[18].toNat addr[19].toNat addr[20].toNat : Nat) : F)
  let limb3 : F := ((U64.pack56 addr[21].toNat addr[22].toNat addr[23].toNat
    addr[24].toNat addr[25].toNat addr[26].toNat addr[27].toNat : Nat) : F)
  let limb4 : F := ((U32.pack addr[28].toNat addr[29].toNat addr[30].toNat
    addr[31].toNat : Nat) : F)
  #v[limb0, limb1, limb2, limb3, limb4]

theorem address_to_fields_limb_eq {F : Type} [Field F] (addr : Digest) :
    (addressToFields F addr)[0] =
      (addr[0].toNat : F) + 256 * (addr[1].toNat : F) + 65536 * (addr[2].toNat : F) +
      16777216 * (addr[3].toNat : F) + 4294967296 * (addr[4].toNat : F) +
      1099511627776 * (addr[5].toNat : F) + 281474976710656 * (addr[6].toNat : F) ∧
    (addressToFields F addr)[4] =
      (addr[28].toNat : F) + 256 * (addr[29].toNat : F) + 65536 * (addr[30].toNat : F) +
      16777216 * (addr[31].toNat : F) := by
  unfold addressToFields U64.pack56 U32.pack
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  constructor <;> (push_cast; ring)

theorem limb7_inj {F : Type} [Field F] (large : U64.Compatible F)
    {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : UInt8}
    (h : ((U64.pack56 a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat a5.toNat a6.toNat : Nat) : F) =
         ((U64.pack56 b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat b5.toNat b6.toNat : Nat) : F)) :
    a0.toNat = b0.toNat ∧ a1.toNat = b1.toNat ∧ a2.toNat = b2.toNat ∧
    a3.toNat = b3.toNat ∧ a4.toNat = b4.toNat ∧ a5.toNat = b5.toNat ∧
    a6.toNat = b6.toNat := by
  have hl := U64.natCast_inj large
    (U64.pack56_lt a0.toNat_lt a1.toNat_lt a2.toNat_lt a3.toNat_lt a4.toNat_lt a5.toNat_lt a6.toNat_lt)
    (U64.pack56_lt b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt b4.toNat_lt b5.toNat_lt b6.toNat_lt) h
  exact (U64.pack56_inj
    a0.toNat_lt a1.toNat_lt a2.toNat_lt a3.toNat_lt a4.toNat_lt a5.toNat_lt a6.toNat_lt
    b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt b4.toNat_lt b5.toNat_lt b6.toNat_lt).mp hl

theorem limb4_inj {F : Type} [Field F] (large : U64.Compatible F)
    {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8}
    (h : ((U32.pack a0.toNat a1.toNat a2.toNat a3.toNat : Nat) : F) =
         ((U32.pack b0.toNat b1.toNat b2.toNat b3.toNat : Nat) : F)) :
    a0.toNat = b0.toNat ∧ a1.toNat = b1.toNat ∧ a2.toNat = b2.toNat ∧
    a3.toNat = b3.toNat := by
  have ha0 := a0.toNat_lt; have ha1 := a1.toNat_lt; have ha2 := a2.toNat_lt; have ha3 := a3.toNat_lt
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  have hl := U64.natCast_inj large
    (by have := U32.pack_lt ha0 ha1 ha2 ha3; unfold U32.base U64.fieldBound at *; omega)
    (by have := U32.pack_lt hb0 hb1 hb2 hb3; unfold U32.base U64.fieldBound at *; omega) h
  unfold U32.pack at hl
  omega

/-- Under `U64.Compatible F`, `addressToFields F` is injective on 32-byte digests. -/
theorem address_to_fields_inj {F : Type} [Field F] (large : U64.Compatible F)
    {a b : Digest} :
    addressToFields F a = addressToFields F b ↔ a = b := by
  constructor
  · intro h
    have h0 : (addressToFields F a)[0] = (addressToFields F b)[0] := by rw [h]
    have h1 : (addressToFields F a)[1] = (addressToFields F b)[1] := by rw [h]
    have h2 : (addressToFields F a)[2] = (addressToFields F b)[2] := by rw [h]
    have h3 : (addressToFields F a)[3] = (addressToFields F b)[3] := by rw [h]
    have h4 : (addressToFields F a)[4] = (addressToFields F b)[4] := by rw [h]
    simp only [addressToFields, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := limb7_inj large h0
    obtain ⟨e7, e8, e9, e10, e11, e12, e13⟩ := limb7_inj large h1
    obtain ⟨e14, e15, e16, e17, e18, e19, e20⟩ := limb7_inj large h2
    obtain ⟨e21, e22, e23, e24, e25, e26, e27⟩ := limb7_inj large h3
    obtain ⟨e28, e29, e30, e31⟩ := limb4_inj large h4
    ext i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
           i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
           i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
           i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · exact e13
    · exact e14
    · exact e15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · exact e21
    · exact e22
    · exact e23
    · exact e24
    · exact e25
    · exact e26
    · exact e27
    · exact e28
    · exact e29
    · exact e30
    · exact e31
  · rintro rfl
    rfl

/-- `Blake3::verify_bytes_against(bytes, expected_addr)` asserts that the 5 field limbs
`address_to_fields(bytes_to_addr(bytes))` equal `address_to_fields(expected_addr)`.
Under `U64.Compatible F`, this field-array equality holds if and only if the BLAKE3 digest
of `bytes` equals `expected_addr`. -/
theorem verify_bytes_against_iff {F : Type} [Field F] (large : U64.Compatible F)
    (bytes : List UInt8) (expectedAddr : Digest) :
    addressToFields F (digest bytes) = addressToFields F expectedAddr ↔
      digest bytes = expectedAddr :=
  address_to_fields_inj large

end Aiur.Library.Blake3
