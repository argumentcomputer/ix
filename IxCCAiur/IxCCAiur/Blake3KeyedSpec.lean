import IxCCAiur.Blake3Spec
import Aiur.Library.Field.BN254
import Aiur.Library.Field.BLS12381.Prime

/-! # Field-Polymorphic Keyed & `derive_key` BLAKE3 Operational Contracts (`IxCCAiur.Blake3KeyedSpec`)

Extends `IxCCAiur.Blake3Spec` with standalone, field-polymorphic operational `EvalFn` contracts
for keyed (`KEYED_HASH = 16`), two-pass `derive_key` (`DERIVE_KEY_CONTEXT = 32` +
`DERIVE_KEY_MATERIAL = 64`), and custom-IV / custom-flags BLAKE3 compression over ANY
`[Field F] [DecidableEq F]` satisfying `Aiur.Library.U32.Compatible F`, explicitly instantiated
for:
* **Goldilocks** (`Aiur.Library.U32.Goldilocks.F`, `p = 2^64 - 2^32 + 1`),
* **BN254 `Fr`** (`Aiur.Library.Field.BN254.F`),
* **BLS12-381 `Fr`** (`Aiur.Library.Field.BLS12381.F`).

This module provides:
1. **Pure parameterized BLAKE3 specification (`digestCVWith`, `digestWith`, `digestKeyed`,
   `deriveKeyContextCV`, `digestDeriveKey`)** together with canonical level-by-level tree
   equivalence (`mergeLevelsWith_chunkOutputs`, `digestWith_eq_mergeLevelsWith`,
   `compressLayerWith_spec`) and exact plain-mode specialization (`digestWith_plain`).
2. **All 11 Protocol `v6` and `v6-zk` domains (`ProtocolDomain`)**: kernel-checked equality
   between every pinned 8-word context chaining value and `deriveKeyContextCV` (zero
   `native_decide`), plus pairwise domain separation (`ProtocolDomain.pinnedCV_injective`,
   `ProtocolDomain.mode_injective`).
3. **Custom-IV / custom-flags `EvalFn` contracts** for `Blake3::compress` and
   `Blake3::compress_init` (both bitwise `dFlags ||| bFlags` and field-additive
   `dFlags + bFlags` forms): single-block keyed hash, single-block two-pass `derive_key`,
   2-to-1 Merkle pair compression across all 11 protocol domains, and internal/root parent
   node compression.
4. **Multi-block and multi-chunk operational composition contracts** (`EvalChunkChain`,
   `EvalLayerPair`, `EvalTreeReduce`, `EvalMultiChunkWith`) over `Blake3::compress_init` for
   arbitrary `NativeInput` byte streams in plain, keyed, two-pass `derive_key`, and all 11
   protocol domains, plus direct custom-IV single-chunk contracts for `Blake3::hash_blocks`
   and exact links from `Blake3Spec`'s `Blake3::hash` / `verify_bytes_against` / `bytes_to_addr`
   to `digestWith`.
5. **Bundled `Blake3KeyedContracts`** with `ofCheck`, `ofCheck64`, `ofCheckZMod`,
   `ofCheckGoldilocks`, `ofCheckBN254`, `ofCheckBLS12381`, and concrete multi-field smoke
   theorems, fenced with `#guard_msgs in #print axioms`.

Zero `sorry`, zero `admit`, zero `native_decide`, zero `bv_decide`, standard axioms only. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Blake3KeyedSpec

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Gadgets IxCC.AiurBackend.World IxCC.AiurBackend.TypedGadgets
open IxCC.AiurBackend.Blake3Spec

/-! ## Section 1: Pure Parameterized BLAKE3 Specification & Tree Equivalence -/

/-- BLAKE3 `CHUNK_START` flag (`1 << 0`). -/
def flagChunkStart : UInt32 := 1

/-- BLAKE3 `CHUNK_END` flag (`1 << 1`). -/
def flagChunkEnd : UInt32 := 2

/-- BLAKE3 `PARENT` flag (`1 << 2`). -/
def flagParent : UInt32 := 4

/-- BLAKE3 `ROOT` flag (`1 << 3`). -/
def flagRoot : UInt32 := 8

/-- BLAKE3 `KEYED_HASH` domain flag (`1 << 4`). -/
def flagKeyedHash : UInt32 := 16

/-- BLAKE3 `DERIVE_KEY_CONTEXT` domain flag (`1 << 5`). -/
def flagDeriveKeyContext : UInt32 := 32

/-- BLAKE3 `DERIVE_KEY_MATERIAL` domain flag (`1 << 6`). -/
def flagDeriveKeyMaterial : UInt32 := 64

/-- Domain flags usable with `Blake3::compress_init`: strictly occupy high flag bits `4..7`
(`dFlags < 240` and `dFlags &&& 15 = 0`), disjoint from the four structural bits
`CHUNK_START | CHUNK_END | PARENT | ROOT = 15`. -/
def ValidDomainFlags (dFlags : UInt32) : Prop :=
  dFlags.toNat < 240 ∧ dFlags &&& 15 = 0

theorem validDomainFlags_plain : ValidDomainFlags 0 := ⟨by decide, by decide⟩
theorem validDomainFlags_keyed : ValidDomainFlags flagKeyedHash := ⟨by decide, by decide⟩
theorem validDomainFlags_deriveKeyContext : ValidDomainFlags flagDeriveKeyContext := ⟨by decide, by decide⟩
theorem validDomainFlags_deriveKeyMaterial : ValidDomainFlags flagDeriveKeyMaterial := ⟨by decide, by decide⟩

private theorem uint32_zero_or (a : UInt32) : (0 : UInt32) ||| a = a :=
  UInt32.toNat_inj.mp (by rw [UInt32.toNat_or]; simp)

private theorem uint32_or_assoc (a b c : UInt32) : (a ||| b) ||| c = a ||| (b ||| c) :=
  UInt32.toNat_inj.mp (by simp only [UInt32.toNat_or, Nat.or_assoc])

private theorem mod16_eq_zero_of_and15 {d : UInt32} (h : d &&& 15 = 0) : d.toNat % 16 = 0 := by
  have h0 : (d &&& 15).toNat = 0 := by rw [h]; rfl
  rw [UInt32.toNat_and] at h0
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit, show (16 : Nat) = 2 ^ 4 by rfl, Nat.testBit_mod_two_pow]
  by_cases hi : i < 4
  · simp only [hi, decide_true, Bool.true_and]
    have hbit := congrArg (fun n => n.testBit i) h0
    rw [Nat.testBit_and, Nat.zero_testBit] at hbit
    have h15 : (15 : UInt32).toNat.testBit i = true := by
      interval_cases i <;> decide
    rw [h15, Bool.and_true] at hbit
    exact hbit
  · simp [hi]

/-- Combining valid domain flags with any structural block mask (`< 16`) by bitwise OR agrees
identically with integer addition (matching Aiur circuits that add `base_flag + block_flags`). -/
theorem or_toNat_eq_add_of_validDomainFlags {dFlags bFlags : UInt32}
    (hd : ValidDomainFlags dFlags) (hb : bFlags.toNat < 16) :
    (dFlags ||| bFlags).toNat = dFlags.toNat + bFlags.toNat := by
  have hmod : dFlags.toNat % 16 = 0 := mod16_eq_zero_of_and15 hd.2
  have hd_eq : dFlags.toNat = 0 + 2 ^ 4 * (dFlags.toNat / 16) := by omega
  have hb_eq : bFlags.toNat = bFlags.toNat + 2 ^ 4 * 0 := by omega
  rw [UInt32.toNat_or]
  change Nat.bitwise or dFlags.toNat bFlags.toNat = dFlags.toNat + bFlags.toNat
  conv_lhs => rw [hd_eq, hb_eq]
  rw [Aiur.Library.U64.bitwise_add_mul_two_pow (f := or) rfl 4 (by omega) (by omega)
        (dFlags.toNat / 16) 0]
  have h1 : Nat.bitwise or 0 bFlags.toNat = bFlags.toNat := by
    rw [Aiur.Library.U64.bitwise_zero_left rfl]; rfl
  have h2 : Nat.bitwise or (dFlags.toNat / 16) 0 = dFlags.toNat / 16 := by
    rw [Aiur.Library.U64.bitwise_zero_right rfl]; rfl
  rw [h1, h2]
  omega

theorem or_lt_256_of_validDomainFlags {dFlags bFlags : UInt32}
    (hd : ValidDomainFlags dFlags) (hb : bFlags.toNat < 16) :
    (dFlags ||| bFlags).toNat < 256 := by
  rw [or_toNat_eq_add_of_validDomainFlags hd hb]
  have := hd.1
  omega

/-- Generalized BLAKE3 chunk block loop with explicit domain `flags` OR'd into every block. -/
def chunkLoopWith (flags : UInt32) (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) : Blake3.Pure.Output :=
  if _h : input.length ≤ 64 then
    ⟨cv, Blake3.Pure.blockWords input, input.length.toUInt32, counter,
      flags ||| ((if start then 1 else 0) ||| 2)⟩
  else
    let next := Blake3.Pure.compress cv (Blake3.Pure.blockWords (input.take 64))
      counter 64 (flags ||| if start then 1 else 0)
    chunkLoopWith flags counter next false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem chunkLoopWith_of_le (flags : UInt32) (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) (small : input.length ≤ 64) :
    chunkLoopWith flags counter cv start input =
      ⟨cv, Blake3.Pure.blockWords input, input.length.toUInt32, counter,
        flags ||| ((if start then 1 else 0) ||| 2)⟩ := by
  rw [chunkLoopWith, dite_eq_left small]

theorem chunkLoopWith_of_gt (flags : UInt32) (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) (large : 64 < input.length) :
    chunkLoopWith flags counter cv start input =
      chunkLoopWith flags counter
        (Blake3.Pure.compress cv (Blake3.Pure.blockWords (input.take 64))
          counter 64 (flags ||| if start then 1 else 0))
        false (input.drop 64) := by
  rw [chunkLoopWith, dite_eq_right (by omega)]

/-- Generalized chunk output starting from explicit initial chaining value `key` and domain `flags`. -/
def chunkOutputWith (key : Blake3.Pure.CV) (flags : UInt32) (counter : UInt64)
    (input : List UInt8) : Blake3.Pure.Output :=
  chunkLoopWith flags counter key true input

/-- Generalized internal parent output under explicit `key` and domain `flags`. -/
def parentOutputWith (key : Blake3.Pure.CV) (flags : UInt32)
    (left right : Blake3.Pure.CV) : Blake3.Pure.Output :=
  ⟨key, left ++ right, 64, 0, flags ||| 4⟩

/-- Generalized canonical BLAKE3 subtree under explicit `key` and domain `flags`. -/
def subtreeWith (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) : Blake3.Pure.Output :=
  if _h : input.length ≤ 1024 then chunkOutputWith key flags counter.toUInt64 input
  else
    let split := Blake3.Pure.leftLen input.length
    let left := subtreeWith key flags counter (input.take split)
    let right := subtreeWith key flags (counter + split / 1024) (input.drop split)
    parentOutputWith key flags left.chainingValue right.chainingValue
termination_by input.length
decreasing_by
  · have := Blake3.Pure.leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := Blake3.Pure.leftLen_positive input.length
    simp only [List.length_drop]; omega

theorem subtreeWith_of_le (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) (small : input.length ≤ 1024) :
    subtreeWith key flags counter input = chunkOutputWith key flags counter.toUInt64 input := by
  rw [subtreeWith, dite_eq_left small]

theorem subtreeWith_of_gt (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) (large : 1024 < input.length) :
    subtreeWith key flags counter input = parentOutputWith key flags
      (subtreeWith key flags counter (input.take (Blake3.Pure.leftLen input.length))).chainingValue
      (subtreeWith key flags (counter + Blake3.Pure.leftLen input.length / 1024)
        (input.drop (Blake3.Pure.leftLen input.length))).chainingValue := by
  rw [subtreeWith, dite_eq_right (by omega)]

/-- 8-word root chaining value under explicit initial chaining value `key` and domain `flags`. -/
def digestCVWith (key : Blake3.Pure.CV) (flags : UInt32) (input : List UInt8) : Blake3.Pure.CV :=
  let out := subtreeWith key flags 0 input
  Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8)

/-- 32-byte BLAKE3 digest under explicit initial chaining value `key` and domain `flags`. -/
def digestWith (key : Blake3.Pure.CV) (flags : UInt32) (input : List UInt8) : Blake3.Pure.Digest :=
  (subtreeWith key flags 0 input).rootHash

theorem digestWith_eq_cvBytes_digestCVWith (key : Blake3.Pure.CV) (flags : UInt32)
    (input : List UInt8) :
    digestWith key flags input = Blake3.Pure.cvBytes (digestCVWith key flags input) :=
  rfl

/-- 8-word root chaining value in keyed mode (`KEYED_HASH = 16`). -/
def digestCVKeyed (key : Blake3.Pure.CV) (input : List UInt8) : Blake3.Pure.CV :=
  digestCVWith key flagKeyedHash input

/-- 32-byte digest in keyed mode (`KEYED_HASH = 16`). -/
def digestKeyed (key : Blake3.Pure.CV) (input : List UInt8) : Blake3.Pure.Digest :=
  digestWith key flagKeyedHash input

/-- Pass 1 of BLAKE3 `derive_key`: 8-word context chaining value under `(iv, 32)`. -/
def deriveKeyContextCV (ctxBytes : List UInt8) : Blake3.Pure.CV :=
  digestCVWith Blake3.Pure.iv flagDeriveKeyContext ctxBytes

/-- Pass 2 of BLAKE3 `derive_key` (8-word root CV): hash `input` under `(ctxCv, 64)`. -/
def digestCVDeriveKey (ctx : String) (input : List UInt8) : Blake3.Pure.CV :=
  digestCVWith (deriveKeyContextCV ctx.toUTF8.data.toList) flagDeriveKeyMaterial input

/-- Two-pass pure BLAKE3 `derive_key` (32-byte digest). -/
def digestDeriveKey (ctx : String) (input : List UInt8) : Blake3.Pure.Digest :=
  digestWith (deriveKeyContextCV ctx.toUTF8.data.toList) flagDeriveKeyMaterial input

theorem chunkLoopWith_zero (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) :
    chunkLoopWith 0 counter cv start input = Blake3.Pure.chunkLoop counter cv start input := by
  by_cases small : input.length ≤ 64
  · rw [chunkLoopWith_of_le 0 counter cv start input small,
        Blake3.Pure.chunkLoop_of_le counter cv start input small, uint32_zero_or]
  · have large : 64 < input.length := by omega
    rw [chunkLoopWith_of_gt 0 counter cv start input large,
        Blake3.Pure.chunkLoop_of_gt counter cv start input large, uint32_zero_or]
    exact chunkLoopWith_zero counter _ false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem chunkOutputWith_plain (counter : UInt64) (input : List UInt8) :
    chunkOutputWith Blake3.Pure.iv 0 counter input = Blake3.Pure.chunkOutput counter input :=
  chunkLoopWith_zero counter Blake3.Pure.iv true input

theorem parentOutputWith_plain (left right : Blake3.Pure.CV) :
    parentOutputWith Blake3.Pure.iv 0 left right = Blake3.Pure.parentOutput left right :=
  rfl

theorem subtreeWith_plain (counter : Nat) (input : List UInt8) :
    subtreeWith Blake3.Pure.iv 0 counter input = Blake3.Pure.subtree counter input := by
  by_cases small : input.length ≤ 1024
  · rw [subtreeWith_of_le Blake3.Pure.iv 0 counter input small,
        Blake3.Pure.subtree_of_le counter input small, chunkOutputWith_plain]
  · have large : 1024 < input.length := by omega
    rw [subtreeWith_of_gt Blake3.Pure.iv 0 counter input large,
        Blake3.Pure.subtree_of_gt counter input large, parentOutputWith_plain,
        subtreeWith_plain counter (input.take (Blake3.Pure.leftLen input.length)),
        subtreeWith_plain (counter + Blake3.Pure.leftLen input.length / 1024)
          (input.drop (Blake3.Pure.leftLen input.length))]
termination_by input.length
decreasing_by
  · have := Blake3.Pure.leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := Blake3.Pure.leftLen_positive input.length
    simp only [List.length_drop]; omega

/-- Plain-mode specialization: `digestWith Blake3.Pure.iv 0` is identically `Blake3.Pure.digest`. -/
theorem digestWith_plain (input : List UInt8) :
    digestWith Blake3.Pure.iv 0 input = Blake3.Pure.digest input := by
  unfold digestWith Blake3.Pure.digest
  rw [subtreeWith_plain]

/-- Plain-mode CV specialization. -/
theorem digestCVWith_plain (input : List UInt8) :
    Blake3.Pure.cvBytes (digestCVWith Blake3.Pure.iv 0 input) = Blake3.Pure.digest input :=
  digestWith_plain input

/-- Single-block closed form (`bytes.length ≤ 64`): `digestCVWith` is one compression with
flags `dFlags ||| 11` (`CHUNK_START | CHUNK_END | ROOT`). -/
theorem digestCVWith_single_block (key : Blake3.Pure.CV) (dFlags : UInt32) (bytes : List UInt8)
    (hlen : bytes.length ≤ 64) :
    digestCVWith key dFlags bytes =
      Blake3.Pure.compress key (Blake3.Pure.blockWords bytes) 0 bytes.length.toUInt32
        (dFlags ||| 11) := by
  unfold digestCVWith
  rw [subtreeWith_of_le key dFlags 0 bytes (by omega), chunkOutputWith,
      chunkLoopWith_of_le dFlags (0 : Nat).toUInt64 key true bytes hlen]
  simp only [↓reduceIte, uint32_or_assoc]
  rfl

/-- Packing the 64 little-endian bytes of two 8-word CVs reproduces their 16-word concatenation. -/
theorem blockWords_cvBytes_append (left right : Blake3.Pure.CV) :
    Blake3.Pure.blockWords ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList) =
      left ++ right := by
  ext w hw
  unfold Blake3.Pure.blockWords
  simp only [Vector.getElem_ofFn]
  have hlenL : (Blake3.Pure.cvBytes left).toList.length = 32 := by simp
  have hlenR : (Blake3.Pure.cvBytes right).toList.length = 32 := by simp
  by_cases hw8 : w < 8
  · rw [Vector.getElem_append_left hw8]
    have hbytes :
        (Vector.ofFn fun b : Fin 4 =>
          ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList).toArray[w * 4 + b.val]?.getD 0) =
        #v[(Blake3.Pure.wordBytes left[w])[0], (Blake3.Pure.wordBytes left[w])[1],
           (Blake3.Pure.wordBytes left[w])[2], (Blake3.Pure.wordBytes left[w])[3]] := by
      apply Vector.ext
      intro b hb
      simp only [Vector.getElem_ofFn, List.getElem?_toArray]
      have hlt : w * 4 + b < 32 := by omega
      rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some,
          Vector.getElem_toList]
      simp only [Blake3.Pure.cvBytes, Vector.getElem_ofFn,
        show (w * 4 + b) / 4 = w by omega, show (w * 4 + b) % 4 = b by omega]
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [hbytes, Aiur.Library.Blake3.bytesWord_eq_wordOfBytes,
        Aiur.Library.Blake3.wordOfBytes_wordBytes]
  · rw [Vector.getElem_append_right (by omega) (by omega)]
    have hbytes :
        (Vector.ofFn fun b : Fin 4 =>
          ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList).toArray[w * 4 + b.val]?.getD 0) =
        #v[(Blake3.Pure.wordBytes right[w - 8])[0], (Blake3.Pure.wordBytes right[w - 8])[1],
           (Blake3.Pure.wordBytes right[w - 8])[2], (Blake3.Pure.wordBytes right[w - 8])[3]] := by
      apply Vector.ext
      intro b hb
      simp only [Vector.getElem_ofFn, List.getElem?_toArray]
      have hge32 : 32 ≤ w * 4 + b := by omega
      have hlt32 : w * 4 + b - 32 < 32 := by omega
      rw [List.getElem?_append_right (by omega), hlenL,
          List.getElem?_eq_getElem (by omega), Option.getD_some,
          Vector.getElem_toList]
      simp only [Blake3.Pure.cvBytes, Vector.getElem_ofFn,
        show (w * 4 + b - 32) / 4 = w - 8 by omega,
        show (w * 4 + b - 32) % 4 = b by omega]
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [hbytes, Aiur.Library.Blake3.bytesWord_eq_wordOfBytes,
        Aiur.Library.Blake3.wordOfBytes_wordBytes]

/-- 2-to-1 pair closed form: hashing the 64 concatenated bytes of `(left, right)` under
`(key, dFlags)` is a single compression of `left ++ right` with `len = 64` and `dFlags ||| 11`. -/
theorem digestCVWith_pair (key : Blake3.Pure.CV) (dFlags : UInt32) (left right : Blake3.Pure.CV) :
    digestCVWith key dFlags
      ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList) =
      Blake3.Pure.compress key (left ++ right) 0 64 (dFlags ||| 11) := by
  have hlen : ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList).length = 64 := by
    simp
  rw [digestCVWith_single_block key dFlags _ (by omega), blockWords_cvBytes_append, hlen]
  rfl

/-! ### Level-by-Level Canonical Tree Equivalence for Parameterized Modes -/

def chunkOutputsWith (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) : List Blake3.Pure.Output :=
  if _h : input.length ≤ 1024 then [chunkOutputWith key flags counter.toUInt64 input]
  else
    chunkOutputWith key flags counter.toUInt64 (input.take 1024) ::
      chunkOutputsWith key flags (counter + 1) (input.drop 1024)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

theorem chunkOutputsWith_small (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) (small : input.length ≤ 1024) :
    chunkOutputsWith key flags counter input = [chunkOutputWith key flags counter.toUInt64 input] := by
  rw [chunkOutputsWith, dite_eq_left small]

theorem chunkOutputsWith_large (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) (large : 1024 < input.length) :
    chunkOutputsWith key flags counter input =
      chunkOutputWith key flags counter.toUInt64 (input.take 1024) ::
        chunkOutputsWith key flags (counter + 1) (input.drop 1024) := by
  rw [chunkOutputsWith, dite_eq_right (by omega)]

theorem chunkOutputsWith_length (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) :
    (chunkOutputsWith key flags counter input).length =
      if input.length ≤ 1024 then 1 else (input.length + 1023) / 1024 := by
  by_cases small : input.length ≤ 1024
  · rw [chunkOutputsWith_small key flags counter input small, ite_eq_left small, List.length_singleton]
  · rw [chunkOutputsWith_large key flags counter input (by omega), ite_eq_right small, List.length_cons,
        chunkOutputsWith_length key flags (counter + 1) (input.drop 1024), List.length_drop]
    split <;> omega
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

private theorem chunkOutputsWith_append (key : Blake3.Pure.CV) (flags : UInt32)
    (counter count : Nat) (left right : List UInt8)
    (full : left.length = 1024 * count) (positive : 0 < count) (nonempty : 0 < right.length) :
    chunkOutputsWith key flags counter (left ++ right) =
      chunkOutputsWith key flags counter left ++ chunkOutputsWith key flags (counter + count) right := by
  have long : 1024 < (left ++ right).length := by rw [List.length_append]; omega
  rw [chunkOutputsWith_large key flags counter (left ++ right) long]
  by_cases one : count = 1
  · subst one
    rw [chunkOutputsWith_small key flags counter left (by omega), List.take_left' (by omega),
        List.drop_left' (by omega), List.singleton_append]
  · rw [chunkOutputsWith_large key flags counter left (by omega),
        List.take_append_of_le_length (by omega),
        List.drop_append_of_le_length (by omega),
        chunkOutputsWith_append key flags (counter + 1) (count - 1) (left.drop 1024) right
          (by rw [List.length_drop]; omega) (by omega) nonempty,
        List.cons_append, show counter + 1 + (count - 1) = counter + count by omega]
termination_by left.length
decreasing_by rw [List.length_drop]; omega

def pairOutputsWith (key : Blake3.Pure.CV) (flags : UInt32) :
    List Blake3.Pure.Output → List Blake3.Pure.Output
  | [] => []
  | [output] => [output]
  | left :: right :: rest =>
      parentOutputWith key flags left.chainingValue right.chainingValue ::
        pairOutputsWith key flags rest

theorem pairOutputsWith_length (key : Blake3.Pure.CV) (flags : UInt32) :
    (outputs : List Blake3.Pure.Output) →
      (pairOutputsWith key flags outputs).length = (outputs.length + 1) / 2
  | [] => by simp [pairOutputsWith]
  | [_] => by simp [pairOutputsWith]
  | _ :: _ :: rest => by
      simp only [pairOutputsWith, List.length_cons, pairOutputsWith_length key flags rest]
      omega

private theorem pairOutputsWith_length_lt {key : Blake3.Pure.CV} {flags : UInt32}
    {outputs : List Blake3.Pure.Output} (two : 2 ≤ outputs.length) :
    (pairOutputsWith key flags outputs).length < outputs.length := by
  rw [pairOutputsWith_length]; omega

private theorem pairOutputsWith_append (key : Blake3.Pure.CV) (flags : UInt32) :
    (left right : List Blake3.Pure.Output) → left.length % 2 = 0 →
      pairOutputsWith key flags (left ++ right) =
        pairOutputsWith key flags left ++ pairOutputsWith key flags right
  | [], _, _ => rfl
  | [_], _, even => by simp at even
  | _ :: _ :: rest, right, even => by
      have restEven : rest.length % 2 = 0 := by simp only [List.length_cons] at even; omega
      simp only [List.cons_append, pairOutputsWith,
        pairOutputsWith_append key flags rest right restEven]

def mergeLevelsWith (key : Blake3.Pure.CV) (flags : UInt32)
    (outputs : List Blake3.Pure.Output) : Blake3.Pure.Output :=
  match outputs with
  | [] => chunkOutputWith key flags 0 []
  | [output] => output
  | left :: right :: rest =>
      mergeLevelsWith key flags (pairOutputsWith key flags (left :: right :: rest))
termination_by outputs.length
decreasing_by exact pairOutputsWith_length_lt (by rw [List.length_cons, List.length_cons]; omega)

theorem mergeLevelsWith_singleton (key : Blake3.Pure.CV) (flags : UInt32)
    (output : Blake3.Pure.Output) : mergeLevelsWith key flags [output] = output := by
  rw [mergeLevelsWith]

theorem mergeLevelsWith_step (key : Blake3.Pure.CV) (flags : UInt32)
    (left right : Blake3.Pure.Output) (rest : List Blake3.Pure.Output) :
    mergeLevelsWith key flags (left :: right :: rest) =
      mergeLevelsWith key flags (pairOutputsWith key flags (left :: right :: rest)) := by
  conv => lhs; rw [mergeLevelsWith]

private theorem mergeLevelsWith_pairOutputs (key : Blake3.Pure.CV) (flags : UInt32) :
    (outputs : List Blake3.Pure.Output) →
      mergeLevelsWith key flags (pairOutputsWith key flags outputs) =
        mergeLevelsWith key flags outputs
  | [] => rfl
  | [_] => rfl
  | left :: right :: rest => (mergeLevelsWith_step key flags left right rest).symm

private theorem mergeLevelsWith_append (key : Blake3.Pure.CV) (flags : UInt32) (exponent : Nat) :
    (left right : List Blake3.Pure.Output) →
      left.length = 2 ^ exponent → 0 < right.length → right.length ≤ 2 ^ exponent →
      mergeLevelsWith key flags (left ++ right) =
        parentOutputWith key flags
          (mergeLevelsWith key flags left).chainingValue
          (mergeLevelsWith key flags right).chainingValue := by
  induction exponent with
  | zero =>
    intro left right leftLength rightPositive rightLength
    rw [Nat.pow_zero] at leftLength rightLength
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp leftLength
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp (by omega : right.length = 1)
    rw [List.singleton_append, mergeLevelsWith_step,
      show pairOutputsWith key flags [x, y] =
        [parentOutputWith key flags x.chainingValue y.chainingValue] from rfl,
      mergeLevelsWith_singleton, mergeLevelsWith_singleton, mergeLevelsWith_singleton]
  | succ exponent ih =>
    intro left right leftLength rightPositive rightLength
    have double : 2 ^ (exponent + 1) = 2 * 2 ^ exponent := by rw [Nat.pow_succ, Nat.mul_comm]
    have leftPairs := pairOutputsWith_length key flags left
    have rightPairs := pairOutputsWith_length key flags right
    rw [← mergeLevelsWith_pairOutputs key flags (left ++ right),
      pairOutputsWith_append key flags left right (by omega),
      ih (pairOutputsWith key flags left) (pairOutputsWith key flags right)
        (by omega) (by omega) (by omega),
      mergeLevelsWith_pairOutputs, mergeLevelsWith_pairOutputs]

theorem mergeLevelsWith_chunkOutputs (key : Blake3.Pure.CV) (flags : UInt32)
    (counter : Nat) (input : List UInt8) :
    mergeLevelsWith key flags (chunkOutputsWith key flags counter input) =
      subtreeWith key flags counter input := by
  by_cases small : input.length ≤ 1024
  · rw [chunkOutputsWith_small key flags counter input small, mergeLevelsWith_singleton,
        subtreeWith_of_le key flags counter input small]
  · have large : 1024 < input.length := by omega
    obtain ⟨exponent, full⟩ := Blake3.Pure.leftLen_eq_pow large
    obtain ⟨below, atMost⟩ := Blake3.Pure.leftLen_half large
    have positive := Nat.two_pow_pos exponent
    have takeLength : (input.take (Blake3.Pure.leftLen input.length)).length =
        Blake3.Pure.leftLen input.length := by
      rw [List.length_take]; omega
    have dropLength : (input.drop (Blake3.Pure.leftLen input.length)).length =
        input.length - Blake3.Pure.leftLen input.length := List.length_drop
    have halves := chunkOutputsWith_append key flags counter (2 ^ exponent)
      (input.take (Blake3.Pure.leftLen input.length))
      (input.drop (Blake3.Pure.leftLen input.length))
      (takeLength.trans full) positive (by rw [dropLength]; omega)
    rw [List.take_append_drop] at halves
    rw [subtreeWith_of_gt key flags counter input large,
      show Blake3.Pure.leftLen input.length / 1024 = 2 ^ exponent by omega, halves,
      mergeLevelsWith_append key flags exponent _ _
        (by rw [chunkOutputsWith_length, takeLength]; split <;> omega)
        (by rw [chunkOutputsWith_length]; split <;> omega)
        (by rw [chunkOutputsWith_length, dropLength]; split <;> omega),
      mergeLevelsWith_chunkOutputs key flags counter
        (input.take (Blake3.Pure.leftLen input.length)),
      mergeLevelsWith_chunkOutputs key flags (counter + 2 ^ exponent)
        (input.drop (Blake3.Pure.leftLen input.length))]
termination_by input.length
decreasing_by
  · have := Blake3.Pure.leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := Blake3.Pure.leftLen_positive input.length
    simp only [List.length_drop]; omega

theorem digestCVWith_eq_mergeLevelsWith (key : Blake3.Pure.CV) (flags : UInt32)
    (input : List UInt8) :
    digestCVWith key flags input =
      let out := mergeLevelsWith key flags (chunkOutputsWith key flags 0 input)
      Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8) := by
  unfold digestCVWith
  rw [mergeLevelsWith_chunkOutputs]

theorem digestWith_eq_mergeLevelsWith (key : Blake3.Pure.CV) (flags : UInt32)
    (input : List UInt8) :
    digestWith key flags input =
      (mergeLevelsWith key flags (chunkOutputsWith key flags 0 input)).rootHash := by
  unfold digestWith
  rw [mergeLevelsWith_chunkOutputs]

/-- Chaining-value pairing for one internal Merkle layer under `(key, flags)`. -/
def pairChainingValuesWith (key : Blake3.Pure.CV) (flags : UInt32) :
    List Blake3.Pure.CV → List Blake3.Pure.CV
  | [] => []
  | [cv] => [cv]
  | left :: right :: rest =>
      Blake3.Pure.compress key (left ++ right) 0 64 (flags ||| 4) ::
        pairChainingValuesWith key flags rest

theorem pairOutputsWith_chainingValues (key : Blake3.Pure.CV) (flags : UInt32) :
    (outputs : List Blake3.Pure.Output) →
      (pairOutputsWith key flags outputs).map Blake3.Pure.Output.chainingValue =
        pairChainingValuesWith key flags (outputs.map Blake3.Pure.Output.chainingValue)
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => by
      simp only [pairOutputsWith, List.map_cons, pairChainingValuesWith,
        pairOutputsWith_chainingValues key flags rest]
      rfl

theorem pairChainingValuesWith_length (key : Blake3.Pure.CV) (flags : UInt32) :
    (cvs : List Blake3.Pure.CV) →
      (pairChainingValuesWith key flags cvs).length = (cvs.length + 1) / 2
  | [] => by simp [pairChainingValuesWith]
  | [_] => by simp [pairChainingValuesWith]
  | _ :: _ :: rest => by
      simp only [pairChainingValuesWith, List.length_cons,
        pairChainingValuesWith_length key flags rest]
      omega

/-- Level-by-level chaining-value tree reducer under `(key, flags)`: compresses adjacent pairs
with `flags ||| 4` until a final pair `[left, right]` remains, then compresses the root pair
with `flags ||| 12` (`PARENT | ROOT`). -/
def compressLayerWith (key : Blake3.Pure.CV) (flags : UInt32) (cvs : List Blake3.Pure.CV) :
    Blake3.Pure.CV :=
  match cvs with
  | [] => key
  | [cv] => cv
  | [left, right] => Blake3.Pure.compress key (left ++ right) 0 64 (flags ||| 12)
  | left :: right :: third :: rest =>
      compressLayerWith key flags (pairChainingValuesWith key flags (left :: right :: third :: rest))
termination_by cvs.length
decreasing_by
  rw [pairChainingValuesWith_length]
  simp only [List.length_cons]
  omega

private theorem compressLayerWith_spec_le (key : Blake3.Pure.CV) (flags : UInt32) :
    ∀ (limit : Nat) (outputs : List Blake3.Pure.Output),
      outputs.length ≤ limit → 2 ≤ outputs.length →
      compressLayerWith key flags (outputs.map Blake3.Pure.Output.chainingValue) =
        let out := mergeLevelsWith key flags outputs
        Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8)
  | 0, _, hle, htwo => by omega
  | limit + 1, outputs, hle, htwo => by
      match outputs, hle, htwo with
      | [], _, htwo => simp at htwo
      | [_], _, htwo => simp at htwo
      | [left, right], _, _ =>
        simp only [List.map_cons, List.map_nil]
        rw [mergeLevelsWith_step,
            show pairOutputsWith key flags [left, right] =
              [parentOutputWith key flags left.chainingValue right.chainingValue] from rfl,
            mergeLevelsWith_singleton]
        unfold compressLayerWith parentOutputWith
        simp only [uint32_or_assoc]
        rfl
      | left :: right :: third :: rest, hle, _ =>
        have hpairs := pairOutputsWith_length key flags (left :: right :: third :: rest)
        simp only [List.length_cons] at hpairs hle
        have hstep :
            compressLayerWith key flags
              ((left :: right :: third :: rest).map Blake3.Pure.Output.chainingValue) =
            compressLayerWith key flags
              (pairChainingValuesWith key flags
                ((left :: right :: third :: rest).map Blake3.Pure.Output.chainingValue)) := by
          conv_lhs => simp only [List.map_cons]; rw [compressLayerWith]
          rfl
        rw [hstep, ← pairOutputsWith_chainingValues key flags (left :: right :: third :: rest),
            ← mergeLevelsWith_pairOutputs key flags (left :: right :: third :: rest)]
        exact compressLayerWith_spec_le key flags limit
          (pairOutputsWith key flags (left :: right :: third :: rest))
          (by omega) (by omega)

/-- For any `≥ 2` chunk outputs, `compressLayerWith` computes the exact 8-word root chaining
value of `mergeLevelsWith`. -/
theorem compressLayerWith_spec (key : Blake3.Pure.CV) (flags : UInt32)
    (outputs : List Blake3.Pure.Output) (two : 2 ≤ outputs.length) :
    compressLayerWith key flags (outputs.map Blake3.Pure.Output.chainingValue) =
      let out := mergeLevelsWith key flags outputs
      Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8) :=
  compressLayerWith_spec_le key flags outputs.length outputs (Nat.le_refl _) two

/-! ## Section 2: All 11 Protocol `v6` and `v6-zk` Domains & Kernel-Checked Context CVs -/

/-- All 11 BLAKE3 domain-separation modes used across Protocol `v6` and `v6-zk`:
plain unkeyed mode plus the 5 `v6` and 5 `v6-zk` native `derive_key` domains. -/
inductive ProtocolDomain where
  | plain
  | v6MerkleLeaf
  | v6MerkleCompress
  | v6TranscriptSingle
  | v6TranscriptBatch
  | v6Vk
  | v6ZkMerkleLeaf
  | v6ZkMerkleCompress
  | v6ZkTranscriptSingle
  | v6ZkTranscriptBatch
  | v6ZkVk
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Context string for each of the 10 keyed `derive_key` domains (`none` for `.plain`). -/
def ProtocolDomain.context? : ProtocolDomain → Option String
  | .plain                => none
  | .v6MerkleLeaf         => some "multi-stark/v6/merkle/leaf"
  | .v6MerkleCompress     => some "multi-stark/v6/merkle/compress"
  | .v6TranscriptSingle   => some "multi-stark/v6/transcript/single"
  | .v6TranscriptBatch    => some "multi-stark/v6/transcript/batch"
  | .v6Vk                 => some "multi-stark/v6/vk"
  | .v6ZkMerkleLeaf       => some "multi-stark/v6-zk/merkle/leaf"
  | .v6ZkMerkleCompress   => some "multi-stark/v6-zk/merkle/compress"
  | .v6ZkTranscriptSingle => some "multi-stark/v6-zk/transcript/single"
  | .v6ZkTranscriptBatch  => some "multi-stark/v6-zk/transcript/batch"
  | .v6ZkVk               => some "multi-stark/v6-zk/vk"

/-- Domain flag mask for each protocol domain (`0` for `.plain`, `64` for `DERIVE_KEY_MATERIAL`). -/
def ProtocolDomain.domainFlags : ProtocolDomain → UInt32
  | .plain => 0
  | _      => flagDeriveKeyMaterial

theorem ProtocolDomain.validDomainFlags (d : ProtocolDomain) : ValidDomainFlags d.domainFlags := by
  cases d <;> first | exact validDomainFlags_plain | exact validDomainFlags_deriveKeyMaterial

/-- Precomputed 8-word BLAKE3 context chaining values for all 11 domains (`Blake3.Pure.iv`
for `.plain`, exact `deriveKeyContextCV` outputs for the 5 `v6` and 5 `v6-zk` domains). -/
def ProtocolDomain.pinnedCV : ProtocolDomain → Blake3.Pure.CV
  | .plain => Blake3.Pure.iv
  | .v6MerkleLeaf =>
      #v[0x77042819, 0x5A1DD04F, 0x2F8D0BB8, 0x39D27832,
         0x552A30F6, 0x546C9899, 0x8510A8EF, 0x83ECCD66]
  | .v6MerkleCompress =>
      #v[0xCC4D7633, 0xF8492FEC, 0x5704B1FD, 0x2D69A6B5,
         0xA871EBB5, 0x6439610D, 0x89E86BE6, 0x02E22A34]
  | .v6TranscriptSingle =>
      #v[0x943C1E0F, 0x12B98B0B, 0x1FDA3556, 0x96ECBE49,
         0xF5D6684E, 0xBABD2C79, 0x7E6FD057, 0x4BF1113F]
  | .v6TranscriptBatch =>
      #v[0x56945548, 0x0BAEB2C2, 0xB0BC28DD, 0x9EBE2699,
         0xD7B24F82, 0x35470F4D, 0x065F18D3, 0xF3B2994F]
  | .v6Vk =>
      #v[0xD7089665, 0x2D51B3C7, 0x1E371C33, 0x324E12A1,
         0xB355FBFF, 0x402B8A4A, 0xD8256C89, 0xB1F439C2]
  | .v6ZkMerkleLeaf =>
      #v[0x8A663924, 0x051A410E, 0xB5929C7A, 0x52E6E08C,
         0x51D3B0FA, 0x1D1687C6, 0x472E9E06, 0x5A324ECA]
  | .v6ZkMerkleCompress =>
      #v[0x6E9B081E, 0xBAEEB5DA, 0x18652A0D, 0xA2D1B4E1,
         0x9E40FB01, 0xE905254D, 0x451628D5, 0x3D606842]
  | .v6ZkTranscriptSingle =>
      #v[0x89D8BDA2, 0xBDAE2046, 0x9274DB73, 0x13010FD9,
         0xC59663AB, 0x1A374FE0, 0x9FA807DF, 0xA485833F]
  | .v6ZkTranscriptBatch =>
      #v[0x761A4520, 0x275E7AD5, 0xAF9417AE, 0x5177E5AE,
         0x0E64CF93, 0x68F8718A, 0x15874B68, 0x9F503445]
  | .v6ZkVk =>
      #v[0x486C73BD, 0x64F0F532, 0xF4D92A23, 0xAE0C2406,
         0x097D11FF, 0x4783BEC5, 0x55B051EF, 0x118424A1]

/-- Pure 8-word root chaining value specification for each of the 11 `ProtocolDomain`s. -/
def ProtocolDomain.digestCVPure (d : ProtocolDomain) (input : List UInt8) : Blake3.Pure.CV :=
  match d.context? with
  | none => digestCVWith Blake3.Pure.iv 0 input
  | some ctx => digestCVDeriveKey ctx input

/-- Pure 32-byte digest specification for each of the 11 `ProtocolDomain`s. -/
def ProtocolDomain.digestPure (d : ProtocolDomain) (input : List UInt8) : Blake3.Pure.Digest :=
  match d.context? with
  | none => Blake3.Pure.digest input
  | some ctx => digestDeriveKey ctx input

/-! ### Kernel-Checked Half-Round Trace Verification for All 10 Context CVs -/

private def pureRoundCol (s m : Blake3.Pure.Block) (sched : Vector (Fin 16) 16) : Blake3.Pure.Block :=
  let s := Blake3.Pure.g s 0 4 8 12 m[sched[0]] m[sched[1]]
  let s := Blake3.Pure.g s 1 5 9 13 m[sched[2]] m[sched[3]]
  let s := Blake3.Pure.g s 2 6 10 14 m[sched[4]] m[sched[5]]
  Blake3.Pure.g s 3 7 11 15 m[sched[6]] m[sched[7]]

private def pureRoundDiag (s m : Blake3.Pure.Block) (sched : Vector (Fin 16) 16) : Blake3.Pure.Block :=
  let s := Blake3.Pure.g s 0 5 10 15 m[sched[8]] m[sched[9]]
  let s := Blake3.Pure.g s 1 6 11 12 m[sched[10]] m[sched[11]]
  let s := Blake3.Pure.g s 2 7 8 13 m[sched[12]] m[sched[13]]
  Blake3.Pure.g s 3 4 9 14 m[sched[14]] m[sched[15]]

private def checkPureRound (s m : Blake3.Pure.Block) (sched : Vector (Fin 16) 16)
    (sc sd : Blake3.Pure.Block) : Bool :=
  pureRoundCol s m sched == sc && pureRoundDiag sc m sched == sd

private theorem pureRound_of_check {s m : Blake3.Pure.Block} {sched : Vector (Fin 16) 16}
    {sc sd : Blake3.Pure.Block} (h : checkPureRound s m sched sc sd = true) :
    Blake3.Pure.round s m sched = sd := by
  simp only [checkPureRound, Bool.and_eq_true, beq_iff_eq] at h
  show pureRoundDiag (pureRoundCol s m sched) m sched = sd
  rw [h.1, h.2]

private def checkPureCompress (cv : Blake3.Pure.CV) (m : Blake3.Pure.Block)
    (ctr : UInt64) (len fl : UInt32) (t : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7)
    (out : Blake3.Pure.CV) : Bool :=
  let s0 := Blake3.Pure.initialWords cv ctr len fl
  checkPureRound s0 m Blake3.Pure.schedules[0] t[0].1 t[0].2 &&
  checkPureRound t[0].2 m Blake3.Pure.schedules[1] t[1].1 t[1].2 &&
  checkPureRound t[1].2 m Blake3.Pure.schedules[2] t[2].1 t[2].2 &&
  checkPureRound t[2].2 m Blake3.Pure.schedules[3] t[3].1 t[3].2 &&
  checkPureRound t[3].2 m Blake3.Pure.schedules[4] t[4].1 t[4].2 &&
  checkPureRound t[4].2 m Blake3.Pure.schedules[5] t[5].1 t[5].2 &&
  checkPureRound t[5].2 m Blake3.Pure.schedules[6] t[6].1 t[6].2 &&
  (Vector.ofFn (fun i : Fin 8 => t[6].2[i.val] ^^^ t[6].2[i.val + 8]) == out)

private theorem compress_of_checkPureCompress {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len fl : UInt32} {t : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7}
    {out : Blake3.Pure.CV} (h : checkPureCompress cv m ctr len fl t out = true) :
    Blake3.Pure.compress cv m ctr len fl = out := by
  simp only [checkPureCompress, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hout⟩ := h
  unfold Blake3.Pure.compress
  have hfold :
      Blake3.Pure.schedules.foldl (fun state schedule => Blake3.Pure.round state m schedule)
        (Blake3.Pure.initialWords cv ctr len fl) = t[6].2 := by
    change Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round
      (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round
        (Blake3.Pure.initialWords cv ctr len fl) m Blake3.Pure.schedules[0])
        m Blake3.Pure.schedules[1]) m Blake3.Pure.schedules[2])
        m Blake3.Pure.schedules[3]) m Blake3.Pure.schedules[4])
        m Blake3.Pure.schedules[5]) m Blake3.Pure.schedules[6] = t[6].2
    rw [pureRound_of_check h0, pureRound_of_check h1, pureRound_of_check h2,
        pureRound_of_check h3, pureRound_of_check h4, pureRound_of_check h5,
        pureRound_of_check h6]
  rw [hfold, ← hout]

private theorem deriveKeyContextCV_of_trace (ctx : String) (m : Blake3.Pure.Block)
    (t : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7) (out : Blake3.Pure.CV)
    (hlen : ctx.toUTF8.data.toList.length ≤ 64)
    (hm : Blake3.Pure.blockWords ctx.toUTF8.data.toList = m)
    (ht : checkPureCompress Blake3.Pure.iv m 0 ctx.toUTF8.data.toList.length.toUInt32 43 t out = true) :
    deriveKeyContextCV ctx.toUTF8.data.toList = out := by
  unfold deriveKeyContextCV
  rw [digestCVWith_single_block Blake3.Pure.iv flagDeriveKeyContext _ hlen, hm]
  exact compress_of_checkPureCompress ht

private def blk_v6Leaf : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 1831810678, 1818980965, 1701588837, 26209, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6Leaf : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3223698909, 1434494765, 3092941207, 4259883040, 3238952172, 4086403032, 562474422, 2366670154, 1243843477, 4017214527, 1954528243, 1957916511, 88692536, 1936332911, 2794505608], #v[4255668831, 2259524965, 435317688, 1076630278, 3059031369, 1896186443, 3260543243, 3360414316, 2265325745, 2741388692, 2644265275, 4178496081, 1638156122, 4128909593, 795473110, 2245393442]),
  (#v[3333517621, 290951211, 638537868, 2476258509, 2006784845, 380945141, 3124768850, 1963786488, 767919728, 4128522382, 4114634497, 2553620684, 4184597235, 3547228162, 2945325731, 4214254917], #v[2211097551, 3936614424, 2092791280, 3951117609, 1264928982, 2922557103, 1212962563, 3859832924, 3918596639, 1391402538, 681975275, 2676722066, 3838324170, 2185575229, 2451650785, 646913025]),
  (#v[1322667514, 4194079872, 360353430, 3764229523, 1677148852, 3838497189, 1576352037, 970015572, 1571482187, 72171339, 3684294124, 3865729554, 1833437077, 325322382, 3202443481, 2371475810], #v[1831573705, 2873956876, 2720833482, 1142257511, 1947818856, 3715130890, 594945422, 3130050693, 444895037, 2279654797, 1815012874, 1711018475, 3043065120, 3849668803, 3539241869, 825379110]),
  (#v[1643277564, 3736493179, 3250291499, 2655823182, 2751178620, 3333187733, 1399649753, 374346245, 2105460378, 63739526, 949185524, 3081725929, 3655918392, 3004588849, 2106551956, 3672671850], #v[1034585504, 3361893311, 2908421065, 589797776, 3785457845, 974270581, 2104921482, 2303040200, 3442365296, 3165381132, 1026290336, 3717554740, 1954090624, 2819292789, 2755100754, 1123825354]),
  (#v[5210232, 3529960495, 3952426755, 1296288564, 1736711751, 1467932664, 265922375, 1816878446, 588011920, 1889383376, 739251767, 2239242730, 1292409579, 1370498886, 3856831665, 2773471525], #v[4215436382, 1903763561, 4008943169, 3439754034, 2879383441, 1737584899, 1076664485, 3580927096, 377315984, 1679912996, 3165659198, 2865853880, 3442034986, 3168299779, 404122410, 3746174854]),
  (#v[1133152705, 2378846443, 741727218, 4290919913, 3747510375, 1672394710, 3628595176, 3341702195, 865345085, 2550692651, 3740160352, 2147344693, 173101026, 964142389, 3295803884, 3573542464], #v[1131892420, 1128881332, 4282371965, 2156366972, 3653013781, 2843572583, 147534341, 3216678912, 20956873, 3937659179, 2444387683, 223583472, 2612194188, 3321400532, 2169626115, 49061949]),
  (#v[3811746422, 1606242892, 2247545840, 975500740, 3889243373, 3368387963, 2329333835, 1710969423, 762098798, 4225723067, 1645248704, 72041813, 4158088996, 2279008709, 3748994606, 1790338487], #v[592376093, 1298580710, 3627368838, 4281636245, 2610203356, 620879110, 2481652612, 3498952022, 1414191364, 393942185, 4156049982, 3337022887, 3468605994, 1902986655, 385592171, 1398868016])
]
private def blk_v6Comp : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 1831810678, 1818980965, 1868771173, 1701998701, 29555, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6Comp : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3223698909, 1601677165, 3538674668, 4259883040, 3238952172, 1930540351, 3062408899, 2366670154, 1243843477, 2943133503, 672881762, 1957916511, 88692536, 861989743, 1340080261], #v[513854048, 2697652237, 4211169075, 1198084872, 171337598, 2152718301, 3376877746, 2844522321, 553296343, 1839692281, 1740255812, 3457887637, 2310834607, 2061633860, 3156216496, 3404986715]),
  (#v[141123709, 2783463067, 3668205344, 2231145841, 2939554380, 3674538726, 272664049, 866300941, 3518066054, 2501851990, 2175661779, 4139900458, 2200304049, 810732722, 1208699943, 3804305666], #v[3913193574, 2448406506, 128926286, 275716280, 275547048, 1971388727, 2164228284, 1843954150, 220781591, 3934104819, 1373477920, 329508281, 3886338690, 1540894844, 2177103204, 1180758061]),
  (#v[3072301350, 2452692673, 187351213, 1070583450, 537755461, 4205603872, 674705602, 3706432418, 3848697517, 3707139549, 1216932438, 3030520295, 1480005912, 1763404866, 3225240777, 2730619894], #v[1307896644, 1997993372, 2845443540, 2212289358, 242628352, 1050382895, 3809229667, 1996307501, 3206385470, 2492981249, 2325369267, 3462365533, 3273755927, 3651770244, 2928331332, 3150688606]),
  (#v[4109473320, 2565615512, 2242168769, 3741990682, 3230700961, 630631569, 2702288439, 3879181228, 3503083665, 678424415, 52186052, 2147348972, 1650172425, 2206769987, 3977172965, 192491390], #v[1499183410, 599700878, 2592991596, 1499749544, 653441736, 1243051828, 3174341463, 3368062516, 3725151486, 2797506052, 1447040130, 538494592, 676624622, 3685424310, 2827789733, 3099802420]),
  (#v[2103145198, 2838494981, 3762236923, 391681786, 205599092, 317270683, 894052745, 3690329978, 3717481714, 1338810314, 761818530, 264769907, 4101394394, 2023316297, 3049347538, 499560460], #v[3684585082, 3833444903, 1243157746, 3551753358, 576022207, 3954733893, 1060847209, 1134141158, 1774927750, 4102592223, 3352586728, 3035504417, 2365346819, 3398152796, 1135786568, 4185616067]),
  (#v[1620724294, 1831918813, 869093515, 3336000726, 3152823179, 3719461476, 2976479196, 3494964475, 2491896016, 4104827490, 516100968, 325152273, 1233231931, 1626472646, 1843060378, 3770376378], #v[791540024, 2270399369, 604331992, 1559670000, 1699123682, 740548019, 351289519, 2799203823, 3878930519, 3465535365, 2455711630, 2355926761, 250433105, 2743804940, 92842542, 3482008879]),
  (#v[3315701433, 1839300601, 965196489, 3579984797, 3351988926, 2143594552, 3009349050, 3956543164, 3565702396, 873360852, 597438848, 2250765860, 537455116, 2832272638, 694049042, 3653931767], #v[2796635479, 2218699274, 2645112824, 750726100, 3253194095, 3344420096, 778307705, 4192771565, 1794913124, 2088207846, 3400369669, 30838113, 1771448026, 2741939213, 2810995615, 4211783641])
]
private def blk_v6TrSingle : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 1949251190, 1936613746, 1885958755, 1769156468, 1701603182, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6TrSingle : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3341139421, 4149340867, 4233963262, 4259883040, 3238947564, 1400176402, 3249540537, 2366670154, 1244171157, 234406136, 4098494761, 1957916511, 89020216, 2732195365, 1561178444], #v[3414586446, 514065879, 2064766672, 3143514066, 672263234, 2296259462, 2877660598, 2923187346, 3693713155, 3387836832, 2183813942, 3334968253, 4274852971, 2681492842, 1317692783, 161552119]),
  (#v[363835326, 4092012401, 17761689, 743072552, 892689934, 1818438102, 2091005453, 2666074962, 328706627, 3919654056, 1367716486, 1003017245, 1892889970, 351887011, 280990919, 2178902967], #v[4146278957, 144754511, 23366013, 1742760882, 4251928587, 677900144, 2705141996, 2842596899, 3592905030, 2982457218, 862622500, 3107291454, 358657223, 2085039106, 1915883802, 1956276549]),
  (#v[1257312793, 1797195040, 130362111, 3464261268, 1602768657, 4044147618, 150763977, 879858161, 2867296086, 3161693977, 1267407537, 1862925771, 3092682863, 1878106696, 1823258362, 3050207852], #v[587054016, 631098145, 3943078869, 2407624888, 2993339508, 1788740012, 2852031591, 14988462, 3700787685, 3629629427, 1109649947, 3260278047, 1824725767, 318095048, 277143090, 2136325803]),
  (#v[958249441, 3339573505, 1223523200, 2687242684, 1592317783, 1348042894, 2819395742, 231026868, 2317578640, 437406492, 972116890, 3982341712, 1247424000, 3484747867, 29287422, 2403066366], #v[4039136738, 1332718340, 1878454587, 2102418870, 2388693296, 354413508, 898881542, 758605007, 862500146, 2417856385, 4036732574, 2030423070, 1141436558, 2457418489, 2156450351, 1015734054]),
  (#v[2513255768, 1069689806, 3756942050, 416513125, 1297765934, 2774508510, 2376948644, 3944860373, 3146203488, 1961065044, 3972942823, 4272870165, 1887588614, 949220317, 3770974279, 1745187050], #v[1172094768, 1857737538, 3986573989, 1015745304, 2233152422, 2739438917, 4110021713, 148711317, 1463660700, 1960998109, 3516573434, 3225979405, 415656350, 1253926733, 2109655844, 2893910647]),
  (#v[3786370225, 273565998, 162232385, 89260027, 2697686054, 3516037727, 2551248370, 3121183939, 1929472651, 1155289516, 795459591, 1338572344, 2155538366, 2419033105, 1744599527, 4003826454], #v[2729823148, 243229523, 1915903652, 1062063804, 3490255648, 1329526015, 1558828178, 942617512, 34018263, 3302754771, 3829322113, 2237261800, 3797765375, 2878424637, 3414899120, 1221505942]),
  (#v[3965919751, 4193658315, 352680215, 606152713, 2919381356, 3237179408, 486775096, 124101145, 2025387372, 3470388681, 1354400886, 4058118834, 3833483442, 2104852032, 323758833, 3130381079], #v[1877714613, 2780437780, 406041276, 4119967685, 4195484913, 3918199078, 2021151684, 1038088846, 4225218746, 3070465567, 132745194, 1669138828, 264531135, 1396168031, 102204307, 1982786481])
]
private def blk_v6TrBatch : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 1949251190, 1936613746, 1885958755, 1633824628, 6841204, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6TrBatch : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3341139421, 4149344435, 274211588, 4259883040, 3238947564, 2534718887, 2298905987, 2366670154, 1244171157, 1037665290, 773721101, 1957916511, 89020216, 3537486135, 2531374145], #v[1138860902, 290970204, 2123132878, 254503024, 1551586939, 1413376796, 3175728954, 2766179065, 2390134090, 1027711202, 2057521568, 402572166, 3573910768, 3629613802, 3909433524, 3442244843]),
  (#v[401461493, 1884005290, 1321538118, 2581111245, 3164456549, 1441829291, 4262102109, 2874376117, 2820671457, 1859056150, 2606247074, 3688994343, 955736010, 948522914, 2112622023, 2612127819], #v[1424357036, 1746564272, 1451975846, 332197327, 3610171813, 1683662417, 1507534899, 1740955807, 3187842328, 708466550, 1606897169, 1691272170, 287299362, 931713702, 1433811398, 1277994895]),
  (#v[2434266274, 513709712, 2432094971, 838074835, 2749929881, 3731300846, 862081951, 258618550, 2301182136, 1639550176, 859224, 14914806, 4181783109, 1842821485, 3945130295, 94869814], #v[1212861940, 16777821, 1307410036, 1851213978, 338063183, 1999482616, 1008331280, 3293571693, 2323202081, 925947983, 2446813622, 912763615, 488204969, 3262329267, 1662782582, 2996271128]),
  (#v[1229522197, 1032496376, 2320714805, 1221300115, 661117569, 3510046746, 2605926578, 610622791, 1602364621, 1591017163, 632878198, 613089054, 2099159876, 2797431838, 787390885, 2734937103], #v[971800849, 3448234681, 1373720135, 2134111122, 3668818225, 602220518, 206669593, 389787034, 2942959459, 1878504524, 3305268754, 3992784424, 2055432519, 3626377463, 3662277433, 4238033583]),
  (#v[1501021807, 2559092302, 930334214, 3738963177, 309938392, 302912075, 3534900168, 2135794534, 2021253156, 2685582886, 2154108111, 4005419138, 1980396200, 95608975, 2097752642, 490561382], #v[972605640, 794889931, 2046666268, 434881969, 2283342507, 2999135820, 527075466, 599823943, 974633547, 1598065358, 4278729824, 1791571667, 1698279587, 2202512264, 263625962, 458928318]),
  (#v[2140353161, 2053251398, 1421021835, 1795614301, 1023740916, 2054697265, 1333322338, 3950170500, 1057269000, 466413937, 121361090, 26189449, 2702984085, 636288320, 1441202052, 2877309120], #v[3321866001, 917417890, 2969803335, 1535248458, 2168531288, 1160033101, 865793717, 1837678190, 609166165, 2668363091, 3315378755, 891055124, 4178325040, 974795728, 3606562118, 2598798838]),
  (#v[3604680453, 1677022565, 584643601, 290346067, 2647168693, 3046420608, 300136960, 1101183804, 1808884818, 3373550332, 941241764, 935116807, 1227391665, 1132820355, 4149869435, 3209822215], #v[310632466, 209137463, 2549432937, 150834095, 2361216833, 1933752980, 2414010880, 3693058204, 1142404442, 131702261, 659122868, 2521017654, 1527709891, 1174779353, 2310929107, 799867347])
]
private def blk_v6Vk : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 1982805622, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6Vk : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3374693853, 3370395201, 3093595334, 4259883040, 3238924012, 2980313384, 970122145, 2366670154, 1243253653, 3171798241, 1581388527, 1957916511, 88102712, 3003481469, 4135197829], #v[2653460075, 4276235010, 4039388520, 1176736441, 1309029977, 2173138144, 3864376660, 3670747921, 2342038379, 2362263924, 2086954703, 2932005262, 2015803429, 2678988330, 4044863639, 1543336382]),
  (#v[3011512600, 1531322852, 3826869708, 469304972, 3292680332, 4236705626, 100908389, 2479509790, 3066924945, 668133106, 2572009248, 505595678, 2754904170, 3532862536, 3267244611, 2681500285], #v[2109472003, 2167509916, 3118359184, 2146430429, 116783185, 2041503422, 1149339221, 3702563380, 430682568, 3846749766, 2385418260, 1596235505, 3789427286, 3761994951, 1478145231, 2906266950]),
  (#v[1346799448, 1960384266, 2929084625, 2291375316, 31435257, 1031352691, 2583626285, 1981997744, 3132204963, 3311410478, 2135685959, 981619960, 1734990492, 3514450957, 2498936046, 1309000813], #v[1961632131, 1267403727, 572452168, 609376767, 2117473426, 3081219778, 1097459524, 1922159581, 3045863294, 1046588662, 888867299, 2092293899, 2122850402, 2337116696, 2128507207, 956844770]),
  (#v[2395822447, 3199192922, 3784427006, 1770865713, 1276407465, 3933206686, 3674842737, 1848071337, 2442950652, 2357287868, 2198503953, 3238216418, 3315120852, 630597191, 2823051992, 3708728299], #v[3679631106, 1615436511, 3085115490, 879071438, 736098009, 2498813968, 4097043086, 2632473537, 470279541, 3853245470, 2514020183, 2396124617, 4272903878, 1300955978, 2660171282, 825934099]),
  (#v[2749791613, 1127691526, 3825136511, 2841638135, 1758960170, 2528567610, 2089708476, 2043265826, 4152285846, 378283868, 1892824753, 1022597460, 3763927940, 3074069133, 3860274369, 2156184340], #v[2299682121, 1792221873, 254105142, 665041716, 3344210666, 8586845, 803302282, 3461324338, 4021544408, 3206635211, 1586143921, 3295383150, 741447037, 967943731, 347358031, 1343533543]),
  (#v[3703610786, 3930789609, 2644750666, 282898681, 4290630824, 1514430868, 4010756138, 2161846134, 1387524368, 1556359158, 3644390141, 3420819818, 4122054369, 241530436, 4162792602, 519593237], #v[67520304, 1786996992, 2356893506, 1574573176, 915463078, 3325927607, 1694730608, 617002685, 1573540531, 89283959, 1208109671, 2641898674, 1999692497, 3450936852, 4260842748, 3433440622]),
  (#v[4200191725, 1245391843, 398527681, 1123794065, 3316617877, 69909694, 1308484591, 3989288405, 1745616629, 2958291901, 1329531136, 595598250, 1245339291, 2472384726, 3293914772, 2544673010], #v[3891068631, 1914265479, 2623159180, 731466171, 2868595245, 651561625, 2640791308, 1310755925, 820275378, 1598614592, 2188191679, 433543962, 430879186, 1727889619, 1161964421, 4292130199])
]
private def blk_v6ZkLeaf : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 2049783414, 1701654379, 1701604210, 1634036783, 102, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6ZkLeaf : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3441671645, 4268675184, 254718081, 4259883040, 3238921968, 696208271, 1989084348, 2366670154, 1243514261, 1745334242, 3944406946, 1957916511, 88363320, 788724497, 388073426], #v[3659795239, 2591722622, 2968801259, 95968001, 2281024356, 2428467718, 2764520019, 4239482715, 1666832193, 41201699, 2758053903, 3226118848, 1862027534, 1379196990, 346425465, 1277826754]),
  (#v[3503210930, 2087466343, 2183149695, 105589167, 3734639708, 2877930832, 2524804589, 2904193590, 2431517432, 333074488, 2302856869, 323560638, 3417386046, 882944194, 1644232057, 1408847362], #v[3108482759, 939975598, 2038110891, 418765687, 750547334, 1901262651, 1885177677, 3408728218, 3704105619, 1781030522, 1627889636, 2440260176, 4139740218, 828574721, 2463860573, 4116393485]),
  (#v[3490856457, 3259817737, 4092826466, 2572974205, 623623734, 3067718973, 2355517981, 1775952476, 2678893769, 1948621563, 3917640143, 1481155122, 2280319912, 856990791, 1641371368, 73082473], #v[1544324950, 3700038054, 4257217933, 2045411016, 2858346594, 1467024724, 2422283830, 4071507915, 3369230902, 1771777017, 3066850884, 702902363, 4279108816, 1462519443, 2501489057, 1546457195]),
  (#v[1174754937, 2353296979, 2096981810, 3663195601, 585097822, 1983718357, 36787320, 2786241263, 1349044554, 1188609506, 1812277496, 1693077741, 472739247, 2228497682, 181837692, 1678553053], #v[1794925674, 833758503, 2051861834, 2199461876, 3741658881, 4057885831, 267414204, 3370486168, 2199167955, 849295042, 1003882172, 2347088380, 2140591799, 3794456033, 2296511844, 3379337249]),
  (#v[2964525770, 1934132407, 3163309196, 2640707831, 2625678959, 2443662361, 2953199158, 4142157502, 652626065, 2619211713, 827455454, 591398928, 1576365863, 221185861, 1343876678, 1705823106], #v[781899086, 964014275, 1881946595, 1481253398, 3540262759, 3293878036, 1535736642, 2872510628, 1213747606, 3583993087, 2527031750, 4063292099, 2373455205, 293592595, 1135450601, 3095548402]),
  (#v[324536193, 3443615317, 4118758221, 1310768397, 2541180139, 1682662600, 39917639, 1297811154, 2853398279, 1337513790, 423996841, 2075069900, 1743423627, 3763635594, 1440330699, 238381062], #v[826818723, 3817773323, 3495300382, 2049086275, 3147688355, 953908071, 3505479478, 2954845027, 4077344183, 3790176423, 1388981880, 3889184362, 4020178106, 266951839, 2676525709, 892667705]),
  (#v[4129309745, 1314312504, 2407918203, 4152193493, 953670745, 1151960015, 1772927101, 2553458862, 1658074487, 215104581, 2945936906, 1921925196, 1221647431, 124595551, 1235006816, 2703155822], #v[3719541496, 1861137226, 3161422704, 3586674602, 2778533862, 3847628827, 604021296, 1975882723, 1473612764, 1811214916, 167634698, 2267983654, 4098801436, 4164988893, 1663974454, 804773161])
]
private def blk_v6ZkComp : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 2049783414, 1701654379, 1701604210, 1836016431, 1936028272, 115, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6ZkComp : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3441671645, 4268675504, 3460213132, 4259883040, 3238921968, 2952753700, 1983364052, 2366670154, 1243514261, 672889825, 4158978977, 1957916511, 88363320, 4009936656, 753637319], #v[1702356025, 4001545160, 1143508280, 3586729164, 3280437149, 4235078772, 1237145300, 957860071, 1147505704, 3390971329, 2956677528, 2952061411, 1488051378, 3667432700, 3913512199, 2559238934]),
  (#v[4022538309, 2019073761, 1828809871, 3629607870, 2575846923, 2405353702, 89692201, 479746753, 3989820179, 3160339304, 1527100452, 673459758, 2665825808, 1743918625, 2270067332, 2049335175], #v[1185463059, 2111269108, 1167328489, 4044233862, 1406395039, 3960362650, 3947357234, 3824441653, 1104586600, 2531208675, 1413019913, 961273613, 2685193611, 2190796266, 389170154, 2686434098]),
  (#v[1664585262, 1724355634, 2890441304, 862904644, 3089082613, 4019241680, 1475896121, 776438159, 3874811975, 880852179, 2955991671, 3368435342, 2340066362, 1128047487, 2970007941, 1012954889], #v[1737354224, 2849254345, 1649721479, 1525658480, 1060502602, 1756768103, 10259599, 3626592661, 2473612876, 1611914820, 452624357, 954333553, 214598942, 736283737, 4167681769, 2812586263]),
  (#v[3692909753, 524537827, 1279846901, 2932632291, 3101780864, 588023932, 855103343, 3831593025, 2974169683, 2331853474, 348246512, 1259302188, 2964404734, 2340432630, 1841805171, 1578819326], #v[421512405, 256167532, 2426313325, 974707924, 1493534684, 1728048665, 3065751302, 1155348392, 2484869232, 1917557749, 1072385659, 3494787042, 3868321836, 4218929287, 848209773, 1489715710]),
  (#v[564881523, 3915204513, 2079542425, 443295173, 3311366655, 3722966535, 1552842101, 3909790905, 4121632, 2162395378, 1940369800, 505433122, 3347396348, 2459262922, 1302195513, 4165987843], #v[1173043895, 2116872362, 407578641, 957221261, 445215525, 102831507, 1602835744, 3618333130, 534605442, 3269217698, 3003924207, 2618102147, 2004375684, 3995680355, 707707913, 8061616]),
  (#v[3408243115, 3272784745, 342339760, 3190406836, 128813553, 3667053738, 3025660073, 243821994, 3161719628, 2419983575, 3077007318, 2093740275, 2805890494, 218320081, 1252903661, 1993854638], #v[2665503722, 1126987564, 2964609354, 2445161454, 4185036230, 2769741811, 1977860333, 2495038539, 2873835690, 1247717906, 4119418573, 2796890903, 3307728187, 309124614, 119751506, 2233867144]),
  (#v[1441192944, 2760637964, 3163832611, 905884355, 3420547011, 4053373744, 2723117376, 644895485, 1293945765, 782640758, 104094162, 2586880123, 2236181894, 3484425377, 196634333, 2421611025], #v[1896161050, 2733812459, 2421116029, 2689777666, 2053513816, 356736403, 3126612331, 4054080650, 530454276, 404496177, 2284480112, 42169571, 3827751257, 4232476894, 4283070910, 3435410632])
]
private def blk_v6ZkTrSingle : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 2049783414, 1920216939, 1668509281, 1953524082, 1852404527, 6646887, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6ZkTrSingle : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3441671645, 3104625786, 1613974750, 4259883040, 3238921968, 3349455874, 4233709003, 2366670154, 1243514261, 1432381682, 1351239700, 1957916511, 88363320, 474326810, 2135678265], #v[2702500183, 1570893015, 3218630588, 1532113828, 2227862145, 218113808, 3347517318, 1761337644, 2005064515, 2550890084, 1115125014, 190728603, 2891129100, 2666833367, 4194874993, 3013110336]),
  (#v[3080281813, 3720868794, 523960038, 878138973, 1404936012, 3957350878, 2665709121, 3581595091, 856785155, 147342888, 3300573127, 1089731528, 3428363431, 2167557513, 641940209, 119155923], #v[774091959, 264694681, 2857099372, 1001593830, 3295828659, 4122902775, 1464669848, 1482028739, 2674749983, 2316689460, 3380002145, 2300790550, 1792186971, 3945495445, 2985618357, 1106046116]),
  (#v[124988141, 3873093348, 3865018300, 3387765375, 4238898667, 3692736968, 2516906133, 69629281, 2080456796, 3960319546, 3072547996, 3560971301, 4242065452, 1257365336, 3506106063, 3785396593], #v[4002863762, 3169416700, 1168120614, 1483729525, 412065596, 3637718506, 1877600256, 88562113, 4172727947, 1523463735, 1521734502, 1063868705, 4224957685, 1383065019, 1956803068, 3426336876]),
  (#v[1096434898, 3552854899, 4171325459, 2493754497, 3663559397, 117410832, 2978211436, 1338536215, 3849790776, 1103206286, 152637487, 3537167340, 662987192, 2694158724, 998931361, 252770621], #v[3507141918, 3254667318, 3317625046, 4269765905, 3549378153, 3804677134, 2821789974, 1046555469, 703193723, 1627488825, 3266461717, 365306018, 4203321834, 2657333755, 4023456173, 3223878152]),
  (#v[314470670, 837078187, 536294937, 2680353928, 2075781340, 1698866609, 2403465385, 1654930605, 2999980986, 743250133, 318470378, 811774322, 511234863, 227302390, 940029620, 1078301704], #v[3227211354, 4003554812, 2583386303, 2291656612, 3654958446, 68711694, 3301025208, 2305327135, 2596293863, 1797834255, 2797591817, 789260211, 504249183, 875183778, 1316549968, 1977466352]),
  (#v[1593785510, 4042429962, 484086690, 2137758348, 139136802, 3672524628, 1124520660, 3678681051, 3780000218, 3924223730, 1053901541, 1524885645, 2650171576, 2568313424, 4169356418, 1369790717], #v[2066673246, 2007698279, 2518933724, 3559672054, 2541394104, 2348730830, 2241051318, 3069038392, 2362353111, 3604717797, 947442859, 110655070, 4106311742, 1139912030, 1599715146, 513812870]),
  (#v[1529434087, 2642321107, 2058265740, 809517603, 1936066698, 3079259954, 817584176, 285225576, 4219178472, 85425291, 3073360777, 2957598740, 2407793065, 1064548026, 4278525803, 4238169047], #v[2064113296, 2650276924, 675979668, 604833906, 3630388957, 564450683, 3878599994, 448416271, 4074726194, 542516346, 3124656871, 923535275, 502609270, 999529115, 2022095589, 3191851312])
]
private def blk_v6ZkTrBatch : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 2049783414, 1920216939, 1668509281, 1953524082, 1952539183, 26723, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6ZkTrBatch : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3441671645, 3104625802, 1714109406, 4259883040, 3238921968, 2806307356, 2253998395, 2366670154, 1243514261, 627009522, 1351364649, 1957916511, 88363320, 3963987482, 2135803214], #v[3202586227, 636976999, 2765873940, 3234513592, 507805125, 12525698, 3681485515, 350945350, 284550725, 2122857525, 3205035824, 101679747, 3168620927, 921183961, 4001705546, 1956376119]),
  (#v[913529241, 3440038270, 2722668444, 1063082708, 3840647819, 831575371, 4291067391, 3774826325, 3233688700, 3830210183, 3675332062, 2291188379, 3621885417, 1966967879, 3049524357, 1713570662], #v[3020429069, 866946024, 3716456343, 1305252503, 2276507733, 1049063042, 2790444976, 4068876763, 422335839, 4058187286, 2485648351, 705566297, 3337173136, 3988206185, 465311235, 1508582317]),
  (#v[2887178627, 599552134, 1928172941, 3673092211, 2964415862, 706393127, 1687790877, 257187960, 3675137816, 3167905161, 4084743511, 2349524437, 2358861482, 49004527, 3859523853, 753918493], #v[641174446, 4166894516, 4259623121, 1681536480, 1324827145, 1193352697, 2672998415, 2109086750, 2695673330, 528961164, 3903642258, 1388789611, 2075350215, 2075397680, 1265859416, 3761452781]),
  (#v[1375174302, 712204805, 2767901382, 3036453059, 2393572362, 1214790658, 1441076611, 80954604, 1038437375, 3739910524, 2132603610, 3131977927, 63473520, 3485855270, 2193048068, 13889433], #v[2932681700, 3440627235, 3023837946, 2932461347, 3404659270, 3666455844, 1015502583, 3204717161, 620173403, 4114855966, 1767529985, 1592041380, 3007179597, 2128349656, 2384919541, 3836436263]),
  (#v[56602923, 1868124650, 2447404937, 2752052018, 2888375584, 2309584130, 3757886586, 2126459082, 2636979031, 318855143, 1601880311, 1772276860, 2865641595, 2870855304, 1813767185, 1410507634], #v[1738943171, 3163741437, 2476748752, 254017808, 1374984571, 3504753501, 187689489, 2639736251, 834023785, 574747209, 1173724910, 409538887, 4194839748, 3242256385, 2842358185, 3142355071]),
  (#v[2443147404, 1323286130, 1785442071, 2101379284, 4056046300, 2263331273, 660262627, 1811764851, 959044150, 774620020, 1727814976, 2734234901, 511272251, 1267631346, 2904131224, 3822843031], #v[672175705, 3685342559, 1752784196, 2847740959, 3741216721, 264098877, 50027377, 2303317478, 1256097955, 752045626, 1270229769, 2360304156, 2176602153, 513499155, 1898200664, 100061805]),
  (#v[260499440, 1740754222, 196736662, 1982864302, 3822622954, 2810005491, 3097757074, 3712230691, 3829109943, 450481687, 2043730212, 1823133242, 1129940321, 1847078813, 1439956824, 1609970989], #v[358051339, 1155172878, 574311474, 3793260774, 2296403221, 1772615883, 1250741347, 1717546435, 1666001707, 1669656795, 2377079708, 3010426184, 2256837254, 23038273, 1594590987, 4178549126])
]
private def blk_v6ZkVk : Blake3.Pure.Block := #v[1953265005, 1953705321, 795570785, 2049783414, 1802907499, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def tr_v6ZkVk : Vector (Blake3.Pure.Block × Blake3.Pure.Block) 7 := #v[
  (#v[490500336, 3441671645, 4269499662, 3093595334, 4259883040, 3238921968, 4115675541, 970122145, 2366670154, 1243514261, 2668536444, 1581388527, 1957916511, 88363320, 1711466402, 4135197829], #v[2752982972, 3323210609, 1470644225, 2459678117, 3964135291, 3735363350, 1732828257, 123559917, 2985689553, 4290590025, 2537766067, 2815296332, 2975742365, 189677437, 3931758437, 2362405383]),
  (#v[833840487, 2103220866, 117531123, 898424410, 1044981818, 191425660, 1758157455, 1037148980, 1434240720, 3925878656, 3054409616, 3637248835, 4085364331, 717413519, 1539573301, 4194530903], #v[2811937628, 210714085, 3257152624, 3999487258, 319961785, 1760798273, 2331239053, 3856278492, 2420162875, 4086305295, 2413323428, 1603669521, 1129313576, 1629195354, 149865085, 3501097352]),
  (#v[3336868694, 2216047646, 4261573650, 3955836377, 2825191263, 1641732030, 4287888268, 225008138, 350978228, 3824718024, 1216556235, 2737228261, 3272034276, 2280417824, 3827991089, 1242740545], #v[3039017785, 168162182, 2122781233, 30517520, 2492330463, 3899280556, 1414426672, 2550543129, 1879230681, 3217611173, 3108111953, 920081989, 727862195, 3067788190, 348575961, 2489939673]),
  (#v[4042116949, 547713575, 306656290, 192903230, 3371692192, 3771648556, 989859694, 3660029662, 3703861849, 1229989765, 1162071126, 1651045240, 2249606829, 2379942198, 826867698, 2158071669], #v[3992321933, 1868701203, 2574622932, 1633834348, 3979539342, 1060086382, 3864802819, 929722804, 406722511, 2165209171, 2877814315, 3393858542, 2695387843, 1631798209, 3456685868, 514485314]),
  (#v[3879462241, 1397061263, 1615238352, 3604018060, 1465839369, 2710395383, 2695701425, 1253858449, 2741335789, 1646218718, 3068486953, 1613391049, 3780043678, 1573914041, 157400357, 3934106229], #v[2598570930, 2976348939, 3887553093, 1006598937, 594990427, 2136017311, 2007313717, 2493868927, 23165380, 422823048, 1244304966, 2446405870, 3083385193, 4203003928, 1466191708, 102223465]),
  (#v[524389442, 2792009762, 2484266709, 318437991, 3734754823, 2350053016, 1872114968, 1451638761, 755804378, 2093573950, 4289516396, 2398950093, 3544655237, 518183034, 3982243054, 3560573740], #v[1772229738, 2036560700, 1016604824, 1973840261, 2517257601, 3214231544, 1771415403, 731707467, 3975129836, 499100007, 2390992709, 606448929, 369508650, 2122186028, 3586036185, 81810539]),
  (#v[2435194280, 783480011, 724183097, 1245350314, 1862415758, 1751521981, 241438841, 1435971560, 274955402, 2990578334, 578885194, 1667290096, 45213684, 1315482290, 659005415, 159351084], #v[3516363574, 2452772106, 1441452003, 2193129816, 813658820, 586314174, 1980905200, 3572300322, 2583363723, 4139950136, 2704532928, 750036318, 956457787, 1701957499, 597845791, 3311984259])
]

/-- Kernel-checked proof that every keyed `ProtocolDomain`'s pinned 8-word chaining value equals
`deriveKeyContextCV` of its canonical UTF-8 context string (zero `native_decide`). -/
theorem ProtocolDomain.pinnedCV_eq_deriveKeyContextCV (d : ProtocolDomain) (ctx : String)
    (hctx : d.context? = some ctx) :
    d.pinnedCV = deriveKeyContextCV ctx.toUTF8.data.toList := by
  cases d <;> simp only [ProtocolDomain.context?, Option.some.injEq] at hctx
  · cases hctx
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6Leaf tr_v6Leaf _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6Comp tr_v6Comp _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6TrSingle tr_v6TrSingle _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6TrBatch tr_v6TrBatch _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6Vk tr_v6Vk _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6ZkLeaf tr_v6ZkLeaf _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6ZkComp tr_v6ZkComp _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6ZkTrSingle tr_v6ZkTrSingle _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6ZkTrBatch tr_v6ZkTrBatch _ (by decide) (by decide) (by decide)).symm
  · subst hctx; exact (deriveKeyContextCV_of_trace _ blk_v6ZkVk tr_v6ZkVk _ (by decide) (by decide) (by decide)).symm

/-- Every `ProtocolDomain`'s 8-word root CV specification agrees with `digestCVWith` under its
`(pinnedCV, domainFlags)` compression parameters. -/
theorem ProtocolDomain.digestCVPure_eq_digestCVWith (d : ProtocolDomain) (input : List UInt8) :
    d.digestCVPure input = digestCVWith d.pinnedCV d.domainFlags input := by
  cases hctx : d.context? with
  | none =>
    have hd : d = .plain := by cases d <;> simp [ProtocolDomain.context?] at hctx ⊢
    subst hd; rfl
  | some ctx =>
    have hcv := d.pinnedCV_eq_deriveKeyContextCV ctx hctx
    have hfl : d.domainFlags = flagDeriveKeyMaterial := by
      cases d <;> simp [ProtocolDomain.context?] at hctx <;> rfl
    simp only [ProtocolDomain.digestCVPure, hctx, digestCVDeriveKey, hcv, hfl]

/-- Every `ProtocolDomain`'s 32-byte digest specification agrees with `digestWith` under its
`(pinnedCV, domainFlags)` compression parameters. -/
theorem ProtocolDomain.digestPure_eq_digestWith (d : ProtocolDomain) (input : List UInt8) :
    d.digestPure input = digestWith d.pinnedCV d.domainFlags input := by
  cases hctx : d.context? with
  | none =>
    have hd : d = .plain := by cases d <;> simp [ProtocolDomain.context?] at hctx ⊢
    subst hd
    simp only [ProtocolDomain.digestPure, ProtocolDomain.context?, ProtocolDomain.pinnedCV,
      ProtocolDomain.domainFlags, digestWith_plain]
  | some ctx =>
    have hcv := d.pinnedCV_eq_deriveKeyContextCV ctx hctx
    have hfl : d.domainFlags = flagDeriveKeyMaterial := by
      cases d <;> simp [ProtocolDomain.context?] at hctx <;> rfl
    simp only [ProtocolDomain.digestPure, hctx, digestDeriveKey, hcv, hfl]

/-- All 11 `ProtocolDomain`s (`plain`, 5 `v6`, 5 `v6-zk`) have pairwise distinct initial chaining values. -/
theorem ProtocolDomain.pinnedCV_injective {d₁ d₂ : ProtocolDomain}
    (h : d₁.pinnedCV = d₂.pinnedCV) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> first | rfl | exact absurd h (by decide)

/-- All 11 `ProtocolDomain`s have pairwise distinct `(pinnedCV, domainFlags)` compression modes. -/
theorem ProtocolDomain.mode_injective {d₁ d₂ : ProtocolDomain}
    (h : (d₁.pinnedCV, d₁.domainFlags) = (d₂.pinnedCV, d₂.domainFlags)) : d₁ = d₂ :=
  pinnedCV_injective (Prod.mk.inj h).1

/-! ## Section 3: Field-Polymorphic `EvalFn` Contracts for Custom-IV & Custom-Flags Compression -/

section CompressionContracts

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F}

/-- **`Blake3::compress` with arbitrary initial state**: running `Blake3::compress(0, state)` on
`initialWords cv ctr len fl` and message block `m` computes `Blake3.Pure.compress cv m ctr len fl`
for ANY chaining value `cv`, counter `ctr`, length `len`, and flags `fl`. -/
theorem eval_compress_custom_state (c : Blake3Contracts world)
    {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len fl : UInt32} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress"
      [.field 0, stateV (Blake3.Pure.initialWords cv ctr len fl) m] h r h') :
    r = vecV (Blake3.Pure.compress cv m ctr len fl) ∧ h' = h := by
  have h0 : (0 : F) = ((0 : Nat) : F) := by simp
  rw [h0] at ev
  obtain ⟨rfl, rfl⟩ := c.compress 3 (k := 0) (by rfl) ev
  rw [compressRounds_seven, Aiur.Library.Blake3.compress_spec]
  exact ⟨rfl, rfl⟩

/-- **`Blake3::compress_init` with arbitrary domain + block flags (bitwise form):**
for any valid domain flag mask (`0`, `16`, `32`, `64`), any structural block mask (`< 16`),
and any `len < 256`, `Blake3::compress_init` computes `Blake3.Pure.compress cv m ctr len (dFlags ||| bFlags)`. -/
theorem eval_compress_init_domain_flags (c : Blake3Contracts world)
    {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len : Nat} {dFlags bFlags : UInt32}
    (hlen : len < 256) (hd : ValidDomainFlags dFlags) (hb : bFlags.toNat < 16)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v ctr, .field (len : F), .field ((dFlags ||| bFlags).toNat : F)] h r h') :
    r = vecV (Blake3.Pure.compress cv m ctr len.toUInt32 (dFlags ||| bFlags)) ∧ h' = h :=
  c.compress_init' hlen (or_lt_256_of_validDomainFlags hd hb) ev

/-- **`Blake3::compress_init` with arbitrary domain + block flags (field-additive form):**
accepts `((dFlags.toNat : F) + (bFlags.toNat : F))` as computed by Aiur arithmetic. -/
theorem eval_compress_init_domain_flags_add (c : Blake3Contracts world)
    {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len : Nat} {dFlags bFlags : UInt32}
    (hlen : len < 256) (hd : ValidDomainFlags dFlags) (hb : bFlags.toNat < 16)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v ctr, .field (len : F), .field ((dFlags.toNat : F) + (bFlags.toNat : F))]
      h r h') :
    r = vecV (Blake3.Pure.compress cv m ctr len.toUInt32 (dFlags ||| bFlags)) ∧ h' = h := by
  have hcast : ((dFlags.toNat : F) + (bFlags.toNat : F)) = ((dFlags ||| bFlags).toNat : F) := by
    rw [or_toNat_eq_add_of_validDomainFlags hd hb, Nat.cast_add]
  rw [hcast] at ev
  exact eval_compress_init_domain_flags c hlen hd hb ev

/-- **Single-block (`≤ 64` bytes) parameterized hash via `Blake3::compress_init`:**
computes `digestCVWith key dFlags bytes` for any `(key, dFlags)` with `ValidDomainFlags dFlags`. -/
theorem eval_compress_init_single_block (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32}
    {bytes : List UInt8} (hd : ValidDomainFlags dFlags) (hlen : bytes.length ≤ 64)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field ((dFlags ||| 11).toNat : F)] h r h') :
    r = vecV (digestCVWith key dFlags bytes) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init_domain_flags c (by omega) hd (bFlags := 11) (by decide) ev
  rw [digestCVWith_single_block key dFlags bytes hlen]
  exact ⟨rfl, rfl⟩

/-- **Single-block keyed BLAKE3 (`KEYED_HASH = 16`, flags `27`) via `Blake3::compress_init`.** -/
theorem eval_compress_init_keyed_single_block (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {bytes : List UInt8}
    (hlen : bytes.length ≤ 64) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (27 : F)] h r h') :
    r = vecV (digestCVKeyed key bytes) ∧ h' = h := by
  have h27 : (27 : F) = ((flagKeyedHash ||| 11).toNat : F) := by
    change (27 : F) = ((27 : Nat) : F); simp
  rw [h27] at ev
  exact eval_compress_init_single_block c validDomainFlags_keyed hlen ev

/-- **Single-block keyed BLAKE3 + `Blake3::digest_bytes`:** produces `digestV (digestKeyed key bytes)`. -/
theorem eval_keyed_single_block_digest (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {bytes : List UInt8}
    (hlen : bytes.length ≤ 64) {rCV rDig : SourceValue F} {h h1 h2 : Heap F}
    (evComp : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (27 : F)] h rCV h1)
    (evDig : EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2) :
    rCV = vecV (digestCVKeyed key bytes) ∧ rDig = digestV (digestKeyed key bytes) ∧ h2 = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init_keyed_single_block c hlen evComp
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  exact ⟨rfl, rfl, rfl⟩

/-- **Pass 1 of `derive_key` (`DERIVE_KEY_CONTEXT = 32`, flags `43`) via `Blake3::compress_init`:**
for any context of `≤ 64` bytes (including every Protocol `v6` and `v6-zk` domain string),
computes `vecV (deriveKeyContextCV ctxBytes)`. -/
theorem eval_compress_init_derive_key_context_single_block (c : Blake3Contracts world)
    {ctxBytes : List UInt8}
    (hlen : ctxBytes.length ≤ 64) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV Blake3.Pure.iv, vecV (Blake3.Pure.blockWords ctxBytes), u64v 0,
       .field (ctxBytes.length : F), .field (43 : F)] h r h') :
    r = vecV (deriveKeyContextCV ctxBytes) ∧ h' = h := by
  have h43 : (43 : F) = ((flagDeriveKeyContext ||| 11).toNat : F) := by
    change (43 : F) = ((43 : Nat) : F); simp
  rw [h43] at ev
  exact eval_compress_init_single_block c validDomainFlags_deriveKeyContext hlen ev

/-- **Pass 2 of `derive_key` (`DERIVE_KEY_MATERIAL = 64`, flags `75`) via `Blake3::compress_init`:**
for any payload of `≤ 64` bytes under context chaining value `ctxCV`, computes
`vecV (digestCVWith ctxCV 64 bytes)`. -/
theorem eval_compress_init_derive_key_material_single_block (c : Blake3Contracts world)
    {ctxCV : Blake3.Pure.CV}
    {bytes : List UInt8} (hlen : bytes.length ≤ 64) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV ctxCV, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (75 : F)] h r h') :
    r = vecV (digestCVWith ctxCV flagDeriveKeyMaterial bytes) ∧ h' = h := by
  have h75 : (75 : F) = ((flagDeriveKeyMaterial ||| 11).toNat : F) := by
    change (75 : F) = ((75 : Nat) : F); simp
  rw [h75] at ev
  exact eval_compress_init_single_block c validDomainFlags_deriveKeyMaterial hlen ev

/-- **End-to-end single-block two-pass `derive_key` via `Blake3::compress_init`:**
Pass 1 hashes `ctx` under `(iv, 43)` to `rCtx`, and Pass 2 hashes `bytes` under `(rCtx, 75)` to
`rOut`, yielding exact `digestCVDeriveKey ctx bytes`. -/
theorem eval_two_pass_derive_key_single_block (c : Blake3Contracts world)
    {ctx : String} {bytes : List UInt8}
    (hctx : ctx.toUTF8.data.toList.length ≤ 64) (hlen : bytes.length ≤ 64)
    {rCtx rOut : SourceValue F} {h h1 h2 : Heap F}
    (evCtx : EvalFn world "Blake3::compress_init"
      [vecV Blake3.Pure.iv, vecV (Blake3.Pure.blockWords ctx.toUTF8.data.toList), u64v 0,
       .field (ctx.toUTF8.data.toList.length : F), .field (43 : F)] h rCtx h1)
    (evMat : EvalFn world "Blake3::compress_init"
      [rCtx, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (75 : F)] h1 rOut h2) :
    rCtx = vecV (deriveKeyContextCV ctx.toUTF8.data.toList) ∧
    rOut = vecV (digestCVDeriveKey ctx bytes) ∧ h2 = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init_derive_key_context_single_block c hctx evCtx
  obtain ⟨rfl, rfl⟩ := eval_compress_init_derive_key_material_single_block c hlen evMat
  exact ⟨rfl, rfl, rfl⟩

/-- **Single-block Protocol `v6` / `v6-zk` domain hash via `Blake3::compress_init`:**
holds uniformly for all 11 `ProtocolDomain`s using their pinned context CVs. -/
theorem eval_compress_init_domain_single_block (c : Blake3Contracts world)
    (d : ProtocolDomain) {bytes : List UInt8}
    (hlen : bytes.length ≤ 64) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV d.pinnedCV, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field ((d.domainFlags ||| 11).toNat : F)] h r h') :
    r = vecV (d.digestCVPure bytes) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init_single_block c d.validDomainFlags hlen ev
  rw [d.digestCVPure_eq_digestCVWith]
  exact ⟨rfl, rfl⟩

/-- **2-to-1 pair compression via `Blake3::compress_init` under any `(key, dFlags)`:**
compressing `left ++ right` with `len = 64` and `flags = dFlags ||| 11` computes
`digestCVWith key dFlags (cvBytes left ++ cvBytes right)`. -/
theorem eval_compress_init_pair (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32}
    (hd : ValidDomainFlags dFlags) (left right : Blake3.Pure.CV)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (left ++ right), u64v 0, .field (64 : F),
       .field ((dFlags ||| 11).toNat : F)] h r h') :
    r = vecV (digestCVWith key dFlags
      ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList)) ∧ h' = h := by
  have h64 : (64 : F) = ((64 : Nat) : F) := by simp
  rw [h64] at ev
  obtain ⟨rfl, rfl⟩ := eval_compress_init_domain_flags c (by omega) hd (bFlags := 11) (by decide) ev
  rw [digestCVWith_pair key dFlags left right]
  exact ⟨rfl, rfl⟩

/-- **All 11 `ProtocolDomain` 2-to-1 Merkle pair compression via `Blake3::compress_init`:**
covers plain (`11`) and all 10 `v6` / `v6-zk` domains (`75`), including `v6MerkleCompress` and
`v6ZkMerkleCompress`. -/
theorem eval_compress_init_domain_pair (c : Blake3Contracts world)
    (d : ProtocolDomain) (left right : Blake3.Pure.CV)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV d.pinnedCV, vecV (left ++ right), u64v 0, .field (64 : F),
       .field ((d.domainFlags ||| 11).toNat : F)] h r h') :
    r = vecV (d.digestCVPure
      ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList)) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := eval_compress_init_pair c d.validDomainFlags left right ev
  rw [d.digestCVPure_eq_digestCVWith]
  exact ⟨rfl, rfl⟩

/-- **Internal Merkle parent compression via `Blake3::compress_init`** (`flags = dFlags ||| 4`). -/
theorem eval_compress_init_parent (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32}
    (hd : ValidDomainFlags dFlags) (left right : Blake3.Pure.CV)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (left ++ right), u64v 0, .field (64 : F),
       .field ((dFlags ||| 4).toNat : F)] h r h') :
    r = vecV (parentOutputWith key dFlags left right).chainingValue ∧ h' = h := by
  have h64 : (64 : F) = ((64 : Nat) : F) := by simp
  rw [h64] at ev
  exact eval_compress_init_domain_flags c (len := 64) (by decide) hd (bFlags := 4) (by decide) ev

/-- **Root Merkle parent compression via `Blake3::compress_init`** (`flags = dFlags ||| 12`). -/
theorem eval_compress_init_parent_root (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32}
    (hd : ValidDomainFlags dFlags) (left right : Blake3.Pure.CV)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Blake3::compress_init"
      [vecV key, vecV (left ++ right), u64v 0, .field (64 : F),
       .field ((dFlags ||| 12).toNat : F)] h r h') :
    r = vecV (Blake3.Pure.compress key (left ++ right) 0 64 (dFlags ||| 12)) ∧
    Blake3.Pure.cvBytes (Blake3.Pure.compress key (left ++ right) 0 64 (dFlags ||| 12)) =
      (parentOutputWith key dFlags left right).rootHash ∧ h' = h := by
  have h64 : (64 : F) = ((64 : Nat) : F) := by simp
  rw [h64] at ev
  obtain ⟨rfl, rfl⟩ := eval_compress_init_domain_flags c (by omega) hd (bFlags := 12) (by decide) ev
  refine ⟨rfl, ?_, rfl⟩
  unfold parentOutputWith Blake3.Pure.Output.rootHash
  simp only [uint32_or_assoc]
  rfl

end CompressionContracts

/-! ## Section 4: Multi-Block, Multi-Chunk, and `Blake3::hash_blocks` Operational Contracts -/

section MultiBlockAndChunk

variable {F : Type} [Field F] [DecidableEq F]
variable {world : World F}

/-- Operational multi-block chunk execution via sequential `EvalFn world "Blake3::compress_init"`
calls, parameterized by domain flags `dFlags`, chunk counter `ctr`, start bit `start`, and
root bit `isRoot`. -/
inductive EvalChunkChain (world : World F) (dFlags : UInt32) (ctr : UInt64) :
    Bool → SourceValue F → List UInt8 → Bool → Heap F → SourceValue F → Heap F → Prop where
  | last {start isRoot : Bool} {cvV r : SourceValue F} {bytes : List UInt8} {h h' : Heap F}
      (hlen : bytes.length ≤ 64)
      (hctr : isRoot = true → ctr = 0)
      (ev : EvalFn world "Blake3::compress_init"
        [cvV, vecV (Blake3.Pure.blockWords bytes), u64v ctr, .field (bytes.length : F),
         .field ((dFlags ||| (((if start then 1 else 0) ||| 2) ||| (if isRoot then 8 else 0))).toNat : F)]
        h r h') :
      EvalChunkChain world dFlags ctr start cvV bytes isRoot h r h'
  | step {start isRoot : Bool} {cvV rMid rOut : SourceValue F} {bytes : List UInt8}
      {h h1 h2 : Heap F}
      (hgt : 64 < bytes.length)
      (evBlk : EvalFn world "Blake3::compress_init"
        [cvV, vecV (Blake3.Pure.blockWords (bytes.take 64)), u64v ctr, .field (64 : F),
         .field ((dFlags ||| (if start then 1 else 0)).toNat : F)] h rMid h1)
      (rest : EvalChunkChain world dFlags ctr false rMid (bytes.drop 64) isRoot h1 rOut h2) :
      EvalChunkChain world dFlags ctr start cvV bytes isRoot h rOut h2

private theorem chunkEndFlags_lt (start isRoot : Bool) :
    ((((if start then (1 : UInt32) else 0) ||| 2) ||| (if isRoot then 8 else 0))).toNat < 16 := by
  cases start <;> cases isRoot <;> decide

private theorem chunkStartFlags_lt (start : Bool) :
    (if start then (1 : UInt32) else 0).toNat < 16 := by
  cases start <;> decide

/-- Soundness of multi-block chunk chaining (`EvalChunkChain`) via `Blake3::compress_init`:
every terminating multi-block chain computes the exact `chunkLoopWith` chaining value
(non-root) or root chaining value (`isRoot = true`, `ctr = 0`). -/
theorem evalChunkChain_spec (c : Blake3Contracts world) {dFlags : UInt32}
    (hd : ValidDomainFlags dFlags) {ctr : UInt64} {start isRoot : Bool}
    {cv : Blake3.Pure.CV} {bytes : List UInt8} {r : SourceValue F} {h h' : Heap F}
    (ev : EvalChunkChain world dFlags ctr start (vecV cv) bytes isRoot h r h') :
    let out := chunkLoopWith dFlags ctr cv start bytes
    r = vecV (if isRoot then Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8)
              else out.chainingValue) ∧ h' = h := by
  generalize hcv : (vecV cv : SourceValue F) = cvV at ev
  induction ev generalizing cv with
  | @last st ir _ _ _ _ _ hlen hctr evLast =>
    subst hcv
    obtain ⟨rfl, rfl⟩ :=
      eval_compress_init_domain_flags c (by omega) hd (chunkEndFlags_lt st ir) evLast
    rw [chunkLoopWith_of_le dFlags ctr cv st _ hlen]
    cases ir with
    | false =>
      have h0 : (((if st then (1 : UInt32) else 0) ||| 2) ||| 0) =
          ((if st then (1 : UInt32) else 0) ||| 2) := by
        cases st <;> decide
      refine ⟨?_, rfl⟩
      simp only [Bool.false_eq_true, ↓reduceIte, h0]
      rfl
    | true =>
      have h0 := hctr rfl
      subst h0
      refine ⟨?_, rfl⟩
      simp only [↓reduceIte, uint32_or_assoc]
  | @step st _ _ _ _ _ _ _ _ hgt evBlk _ ih =>
    subst hcv
    have h64 : (64 : F) = ((64 : Nat) : F) := by simp
    rw [h64] at evBlk
    obtain ⟨rfl, rfl⟩ :=
      eval_compress_init_domain_flags c (len := 64) (by decide) hd (chunkStartFlags_lt st) evBlk
    obtain ⟨rfl, rfl⟩ := ih rfl
    rw [chunkLoopWith_of_gt dFlags ctr cv st _ hgt]
    exact ⟨rfl, rfl⟩

/-- **Multi-block single-chunk (`≤ 1024` bytes) hash via `Blake3::compress_init`:**
covers arbitrary keyed (`KEYED_HASH`), long `derive_key` context (`DERIVE_KEY_CONTEXT`),
and `derive_key` material (`DERIVE_KEY_MATERIAL`) inputs up to 16 blocks (1024 bytes). -/
theorem evalChunkChain_single_chunk_root (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32} (hd : ValidDomainFlags dFlags)
    {bytes : List UInt8} (hlen : bytes.length ≤ 1024) {r : SourceValue F} {h h' : Heap F}
    (ev : EvalChunkChain world dFlags 0 true (vecV key) bytes true h r h') :
    r = vecV (digestCVWith key dFlags bytes) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := evalChunkChain_spec c hd ev
  unfold digestCVWith
  rw [subtreeWith_of_le key dFlags 0 bytes hlen, chunkOutputWith]
  exact ⟨rfl, rfl⟩

/-- Operational chunk-by-chunk evaluation of a multi-chunk stream (`1024`-byte chunks numbered
from `ctr`) into a list of represented chunk chaining values via `EvalChunkChain`. -/
inductive EvalChunkSeq (world : World F) (key : Blake3.Pure.CV) (dFlags : UInt32) :
    Nat → List UInt8 → Heap F → List (SourceValue F) → Heap F → Prop where
  | single {ctr : Nat} {bytes : List UInt8} {r : SourceValue F} {h h' : Heap F}
      (hlen : bytes.length ≤ 1024)
      (ev : EvalChunkChain world dFlags ctr.toUInt64 true (vecV key) bytes false h r h') :
      EvalChunkSeq world key dFlags ctr bytes h [r] h'
  | cons {ctr : Nat} {bytes : List UInt8} {rHead : SourceValue F}
      {rTail : List (SourceValue F)} {h h1 h2 : Heap F}
      (hgt : 1024 < bytes.length)
      (evHead : EvalChunkChain world dFlags ctr.toUInt64 true (vecV key) (bytes.take 1024) false h rHead h1)
      (evTail : EvalChunkSeq world key dFlags (ctr + 1) (bytes.drop 1024) h1 rTail h2) :
      EvalChunkSeq world key dFlags ctr bytes h (rHead :: rTail) h2

theorem evalChunkSeq_spec (c : Blake3Contracts world) {key : Blake3.Pure.CV} {dFlags : UInt32}
    (hd : ValidDomainFlags dFlags) {ctr : Nat} {bytes : List UInt8}
    {rs : List (SourceValue F)} {h h' : Heap F}
    (ev : EvalChunkSeq world key dFlags ctr bytes h rs h') :
    rs = (chunkOutputsWith key dFlags ctr bytes).map (fun o => vecV o.chainingValue) ∧ h' = h := by
  induction ev with
  | single hlen evC =>
    obtain ⟨rfl, rfl⟩ := evalChunkChain_spec c hd evC
    rw [chunkOutputsWith_small key dFlags _ _ hlen]
    simp [chunkOutputWith]
  | cons hgt evH _ ih =>
    obtain ⟨rfl, rfl⟩ := evalChunkChain_spec c hd evH
    obtain ⟨rfl, rfl⟩ := ih
    rw [chunkOutputsWith_large key dFlags _ _ hgt]
    simp [chunkOutputWith]

/-- Operational internal layer-pairing via `Blake3::compress_init` (`flags = dFlags ||| 4`):
pairs adjacent chaining values left-to-right and carries an odd trailing element unchanged. -/
inductive EvalLayerPair (world : World F) (key : Blake3.Pure.CV) (dFlags : UInt32) :
    List (SourceValue F) → Heap F → List (SourceValue F) → Heap F → Prop where
  | nil {h : Heap F} : EvalLayerPair world key dFlags [] h [] h
  | singleton {v : SourceValue F} {h : Heap F} :
      EvalLayerPair world key dFlags [v] h [v] h
  | pair {vl vr : Blake3.Pure.CV} {vPar : SourceValue F}
      {rest restOut : List (SourceValue F)} {h h1 h2 : Heap F}
      (evPar : EvalFn world "Blake3::compress_init"
        [vecV key, vecV (vl ++ vr), u64v 0, .field (64 : F),
         .field ((dFlags ||| 4).toNat : F)] h vPar h1)
      (evRest : EvalLayerPair world key dFlags rest h1 restOut h2) :
      EvalLayerPair world key dFlags (vecV vl :: vecV vr :: rest) h (vPar :: restOut) h2

omit [DecidableEq F] in
/-- `wv` is injective on `UInt32` words under `U32.Compatible F`. -/
theorem wv_inj (hc : U32.Compatible F) {a b : UInt32} (h : (wv a : SourceValue F) = wv b) :
    a = b := by
  simp only [wv, w4, Value.tuple.injEq, List.cons.injEq, and_true] at h
  have h0 := bv_inj hc h.1
  have h1 := bv_inj hc h.2.1
  have h2 := bv_inj hc h.2.2.1
  have h3 := bv_inj hc h.2.2.2
  rw [← wv_bytes a, ← wv_bytes b, h0, h1, h2, h3]

omit [DecidableEq F] in
/-- `vecV` is injective on `Vector UInt32 n` under `U32.Compatible F`. -/
theorem vecV_inj (hc : U32.Compatible F) {n : Nat} {a b : Vector UInt32 n}
    (h : (vecV a : SourceValue F) = vecV b) : a = b := by
  simp only [vecV, Value.tuple.injEq] at h
  apply Vector.ext
  intro i hi
  have hi' := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_ofFn, hi, ↓reduceDIte, Option.some.injEq] at hi'
  exact wv_inj hc hi'

theorem evalLayerPair_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32} (hd : ValidDomainFlags dFlags)
    {cvs : List Blake3.Pure.CV} {out : List (SourceValue F)} {h h' : Heap F}
    (ev : EvalLayerPair world key dFlags (cvs.map (vecV (F := F))) h out h') :
    out = (pairChainingValuesWith key dFlags cvs).map (vecV (F := F)) ∧ h' = h := by
  generalize hm : cvs.map (vecV (F := F)) = vs at ev
  induction ev generalizing cvs with
  | nil =>
    cases cvs with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hm
  | singleton =>
    cases cvs with
    | nil => simp at hm
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
        subst hm
        exact ⟨rfl, rfl⟩
      | cons _ _ => simp at hm
  | pair evPar _ ih =>
    cases cvs with
    | nil => simp at hm
    | cons x xs =>
      cases xs with
      | nil => simp at hm
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at hm
        obtain ⟨hx, hy, hys⟩ := hm
        have hx' : x = _ := vecV_inj hc hx
        have hy' : y = _ := vecV_inj hc hy
        subst hx'; subst hy'
        obtain ⟨rfl, rfl⟩ := eval_compress_init_parent c hd _ _ evPar
        obtain ⟨rfl, rfl⟩ := ih hys
        exact ⟨rfl, rfl⟩

/-- Operational level-by-level tree reduction via `Blake3::compress_init`:
reduces `≥ 1` represented chaining values to a single root chaining value, using
`flags = dFlags ||| 4` for internal layers and `flags = dFlags ||| 12` for the final root pair. -/
inductive EvalTreeReduce (world : World F) (key : Blake3.Pure.CV) (dFlags : UInt32) :
    List (SourceValue F) → Heap F → SourceValue F → Heap F → Prop where
  | single {v : SourceValue F} {h : Heap F} :
      EvalTreeReduce world key dFlags [v] h v h
  | rootPair {vl vr : Blake3.Pure.CV} {rRoot : SourceValue F} {h h' : Heap F}
      (evRoot : EvalFn world "Blake3::compress_init"
        [vecV key, vecV (vl ++ vr), u64v 0, .field (64 : F),
         .field ((dFlags ||| 12).toNat : F)] h rRoot h') :
      EvalTreeReduce world key dFlags [vecV vl, vecV vr] h rRoot h'
  | step {v1 v2 v3 : SourceValue F} {rest nextLayer : List (SourceValue F)}
      {rRoot : SourceValue F} {h h1 h2 : Heap F}
      (evLayer : EvalLayerPair world key dFlags (v1 :: v2 :: v3 :: rest) h nextLayer h1)
      (evRec : EvalTreeReduce world key dFlags nextLayer h1 rRoot h2) :
      EvalTreeReduce world key dFlags (v1 :: v2 :: v3 :: rest) h rRoot h2

theorem evalTreeReduce_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32} (hd : ValidDomainFlags dFlags)
    {cvs : List Blake3.Pure.CV} {rRoot : SourceValue F} {h h' : Heap F}
    (ev : EvalTreeReduce world key dFlags (cvs.map (vecV (F := F))) h rRoot h') :
    rRoot = vecV (compressLayerWith key dFlags cvs) ∧ h' = h := by
  generalize hm : cvs.map (vecV (F := F)) = vs at ev
  induction ev generalizing cvs with
  | single =>
    cases cvs with
    | nil => simp at hm
    | cons x xs =>
      cases xs with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
        subst hm
        rw [compressLayerWith]
        exact ⟨rfl, rfl⟩
      | cons _ _ => simp at hm
  | rootPair evRoot =>
    cases cvs with
    | nil => simp at hm
    | cons x xs =>
      cases xs with
      | nil => simp at hm
      | cons y ys =>
        cases ys with
        | nil =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
          have hx := vecV_inj hc hm.1
          have hy := vecV_inj hc hm.2
          subst hx; subst hy
          obtain ⟨rfl, _, rfl⟩ := eval_compress_init_parent_root c hd _ _ evRoot
          rw [compressLayerWith]
          exact ⟨rfl, rfl⟩
        | cons _ _ => simp at hm
  | step evLayer _ ih =>
    cases cvs with
    | nil => simp at hm
    | cons x xs =>
      cases xs with
      | nil => simp at hm
      | cons y ys =>
        cases ys with
        | nil => simp at hm
        | cons z zs =>
          rw [← hm] at evLayer
          obtain ⟨rfl, rfl⟩ := evalLayerPair_spec hc c hd evLayer
          obtain ⟨rfl, rfl⟩ := ih rfl
          refine ⟨?_, rfl⟩
          conv_rhs => rw [compressLayerWith]

/-- Operational multi-block / multi-chunk BLAKE3 execution under arbitrary `(key, dFlags)`,
composed exclusively from `EvalFn world "Blake3::compress_init"` calls. -/
inductive EvalMultiChunkWith (world : World F) (key : Blake3.Pure.CV) (dFlags : UInt32) :
    List UInt8 → Heap F → SourceValue F → Heap F → Prop where
  | singleChunk {bytes : List UInt8} {rRoot : SourceValue F} {h h' : Heap F}
      (hlen : bytes.length ≤ 1024)
      (ev : EvalChunkChain world dFlags 0 true (vecV key) bytes true h rRoot h') :
      EvalMultiChunkWith world key dFlags bytes h rRoot h'
  | multiChunk {bytes : List UInt8} {cvs : List (SourceValue F)} {rRoot : SourceValue F}
      {h h1 h2 : Heap F}
      (hgt : 1024 < bytes.length)
      (evChunks : EvalChunkSeq world key dFlags 0 bytes h cvs h1)
      (evTree : EvalTreeReduce world key dFlags cvs h1 rRoot h2) :
      EvalMultiChunkWith world key dFlags bytes h rRoot h2

/-- **Multi-chunk parameterized BLAKE3 soundness via `Blake3::compress_init`:**
holds for arbitrary `(key, dFlags)` with `ValidDomainFlags dFlags` and arbitrary byte streams. -/
theorem evalMultiChunkWith_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {dFlags : UInt32} (hd : ValidDomainFlags dFlags)
    {bytes : List UInt8} {rRoot : SourceValue F} {h h' : Heap F}
    (ev : EvalMultiChunkWith world key dFlags bytes h rRoot h') :
    rRoot = vecV (digestCVWith key dFlags bytes) ∧ h' = h := by
  cases ev with
  | singleChunk hlen evC =>
    exact evalChunkChain_single_chunk_root c hd hlen evC
  | multiChunk hgt evSeq evTree =>
    obtain ⟨rfl, rfl⟩ := evalChunkSeq_spec c hd evSeq
    have hmap :
        (chunkOutputsWith key dFlags 0 bytes).map (fun o => vecV (F := F) o.chainingValue) =
          ((chunkOutputsWith key dFlags 0 bytes).map Blake3.Pure.Output.chainingValue).map vecV := by
      simp [List.map_map, Function.comp_def]
    rw [hmap] at evTree
    obtain ⟨rfl, rfl⟩ := evalTreeReduce_spec hc c hd evTree
    have htwo : 2 ≤ (chunkOutputsWith key dFlags 0 bytes).length := by
      rw [chunkOutputsWith_length, ite_eq_right (by omega)]
      omega
    rw [compressLayerWith_spec key dFlags _ htwo, ← digestCVWith_eq_mergeLevelsWith]
    exact ⟨rfl, rfl⟩

/-- **Multi-chunk keyed BLAKE3 (`KEYED_HASH = 16`) + `Blake3::digest_bytes`:**
computes exact `digestKeyed key bytes` for arbitrary input lengths. -/
theorem evalMultiChunkKeyed_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    {key : Blake3.Pure.CV} {bytes : List UInt8} {rCV rDig : SourceValue F} {h h1 h2 : Heap F}
    (evHash : EvalMultiChunkWith world key flagKeyedHash bytes h rCV h1)
    (evDig : EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2) :
    rCV = vecV (digestCVKeyed key bytes) ∧ rDig = digestV (digestKeyed key bytes) ∧ h2 = h := by
  obtain ⟨rfl, rfl⟩ := evalMultiChunkWith_spec hc c validDomainFlags_keyed evHash
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  exact ⟨rfl, rfl, rfl⟩

/-- **Arbitrary-length two-pass `derive_key` via `Blake3::compress_init` + `Blake3::digest_bytes`:**
Pass 1 hashes `ctx` under `(iv, DERIVE_KEY_CONTEXT = 32)` into `ctxCV`, and Pass 2 hashes `bytes`
under `(ctxCV, DERIVE_KEY_MATERIAL = 64)` into `digestDeriveKey ctx bytes`. -/
theorem evalTwoPassDeriveKey_multiChunk_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    {ctx : String} {bytes : List UInt8} {ctxCV : Blake3.Pure.CV}
    {rOut rDig : SourceValue F} {h h1 h2 h3 : Heap F}
    (evCtx : EvalMultiChunkWith world Blake3.Pure.iv flagDeriveKeyContext
      ctx.toUTF8.data.toList h (vecV ctxCV) h1)
    (evMat : EvalMultiChunkWith world ctxCV flagDeriveKeyMaterial bytes h1 rOut h2)
    (evDig : EvalFn world "Blake3::digest_bytes" [rOut] h2 rDig h3) :
    ctxCV = deriveKeyContextCV ctx.toUTF8.data.toList ∧
    rOut = vecV (digestCVDeriveKey ctx bytes) ∧
    rDig = digestV (digestDeriveKey ctx bytes) ∧ h3 = h := by
  obtain ⟨hctxV, rfl⟩ := evalMultiChunkWith_spec hc c validDomainFlags_deriveKeyContext evCtx
  have hctx : ctxCV = deriveKeyContextCV ctx.toUTF8.data.toList := vecV_inj hc hctxV
  subst hctx
  obtain ⟨rfl, rfl⟩ := evalMultiChunkWith_spec hc c validDomainFlags_deriveKeyMaterial evMat
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **All 11 `ProtocolDomain`s multi-chunk soundness via `Blake3::compress_init` + `Blake3::digest_bytes`.** -/
theorem evalProtocolDomain_multiChunk_spec (hc : U32.Compatible F) (c : Blake3Contracts world)
    (d : ProtocolDomain) {bytes : List UInt8} {rCV rDig : SourceValue F} {h h1 h2 : Heap F}
    (evHash : EvalMultiChunkWith world d.pinnedCV d.domainFlags bytes h rCV h1)
    (evDig : EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2) :
    rCV = vecV (d.digestCVPure bytes) ∧ rDig = digestV (d.digestPure bytes) ∧ h2 = h := by
  obtain ⟨rfl, rfl⟩ := evalMultiChunkWith_spec hc c d.validDomainFlags evHash
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  rw [d.digestCVPure_eq_digestCVWith, d.digestPure_eq_digestWith]
  exact ⟨rfl, rfl, rfl⟩

/-! ### Custom-IV Single-Chunk `Blake3::hash_blocks` & Plain-Mode `Blake3Spec` Links -/

private theorem hashBlocks_custom_cv_single_chunk (cv : Blake3.Pure.CV) (bytes : List UInt8)
    (hlen : bytes.length ≤ 1024) :
    Aiur.Library.Blake3.hashBlocks bytes 0 0 cv [] = [digestCVWith cv 0 bytes] := by
  have hout :
      Aiur.Library.Blake3.outputCV true (Blake3.Pure.chunkLoop 0 cv true bytes) =
        digestCVWith cv 0 bytes := by
    unfold Aiur.Library.Blake3.outputCV digestCVWith
    rw [subtreeWith_of_le cv 0 0 bytes hlen, chunkOutputWith, chunkLoopWith_zero]
    rfl
  by_cases hempty : bytes = []
  · subst hempty
    rw [Aiur.Library.Blake3.hashBlocks_nil, List.nil_append, hout]
  · rw [Aiur.Library.Blake3.hashBlocks_last bytes 0 0 cv [] (List.length_pos_iff.mpr hempty)
          (by omega), List.nil_append]
    exact congrArg (fun x => [x]) hout

/-- **Custom-IV single-chunk `Blake3::hash_blocks` + `Blake3::compress_layer`:**
calling `Blake3::hash_blocks` with an arbitrary initial chaining value `cv` on any byte stream
of `≤ 1024` bytes (with `block_no = 0`, `chunk_count = 0`, empty layer) pushes `[digestCVWith cv 0 bytes]`,
and `Blake3::compress_layer` returns `vecV (digestCVWith cv 0 bytes)`. -/
theorem eval_hash_blocks_custom_cv_single_chunk (c : Blake3Contracts world)
    {cv : Blake3.Pure.CV} {bytes : List UInt8} (hlen : bytes.length ≤ 1024)
    {inp ccp cvp lp rLayer rCV : SourceValue F} {h h1 h2 : Heap F}
    (hs : Stream h bytes inp)
    (hcc : loadValue h ccp = .ok (u64v 0))
    (hcv : loadValue h cvp = .ok (vecV cv))
    (hl : Stack h [] lp)
    (evHB : EvalFn world "Blake3::hash_blocks" [inp, .field (0 : F), ccp, cvp, lp] h rLayer h1)
    (evCL : EvalFn world "Blake3::compress_layer" [rLayer] h1 rCV h2) :
    Heap.Extends h h2 ∧ rCV = vecV (digestCVWith cv 0 bytes) := by
  have h0 : (0 : F) = ((0 : Nat) : F) := by simp
  rw [h0] at evHB
  obtain ⟨ext1, hst⟩ := c.hash_blocks bytes (n := 0) (c := 0) (cv := cv) (layer := [])
    (by omega) hs hcc hcv (by simpa using hl) evHB
  obtain ⟨ext2, rfl⟩ := c.compress_layer _ hst evCL
  rw [List.reverse_reverse, hashBlocks_custom_cv_single_chunk cv bytes hlen,
      Aiur.Library.Blake3.compress_layer_singleton]
  exact ⟨ext1.trans ext2, rfl⟩

/-- **Link from `Blake3::hash` (`Blake3Spec`) to `digestWith` / `ProtocolDomain.plain`:**
on any native input (`bytes.length < 2^64`), `Blake3::hash` followed by `Blake3::digest_bytes`
produces `digestV (digestWith Blake3.Pure.iv 0 bytes) = digestV (ProtocolDomain.plain.digestPure bytes)`. -/
theorem eval_hash_eq_digestWith_plain (c : Blake3Contracts world)
    {bytes : List UInt8} {inp rCV rDig : SourceValue F} {h h1 h2 : Heap F}
    (hs : Stream h bytes inp) (native : Blake3.Pure.NativeInput bytes)
    (evHash : EvalFn world "Blake3::hash" [inp] h rCV h1)
    (evDig : EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2) :
    Heap.Extends h h2 ∧
    rDig = digestV (digestWith Blake3.Pure.iv 0 bytes) ∧
    rDig = digestV (ProtocolDomain.plain.digestPure bytes) := by
  obtain ⟨ext, rfl, hdig⟩ := c.hash_digest hs native evHash
  obtain ⟨rfl, rfl⟩ := c.digest_bytes evDig
  rw [hdig, ← digestWith_plain bytes]
  exact ⟨ext, rfl, by rw [ProtocolDomain.digestPure_eq_digestWith]; rfl⟩

/-- **Link from `Blake3::verify_bytes_against` (`Blake3Spec`) to `digestWith` / `ProtocolDomain.plain`.** -/
theorem eval_verify_bytes_against_eq_digestWith_plain (c : Blake3Contracts world)
    {bytes : List UInt8} {addr : Blake3.Pure.Digest} {inp expected r : SourceValue F}
    {h h' : Heap F} (hs : Stream h bytes inp)
    (ha : Aiur.Library.Bytes.RepAddress h addr expected)
    (native : Blake3.Pure.NativeInput bytes)
    (ev : EvalFn world "Blake3::verify_bytes_against" [inp, expected] h r h') :
    Heap.Extends h h' ∧ r = .tuple [] ∧
    digestWith Blake3.Pure.iv 0 bytes = addr ∧
    ProtocolDomain.plain.digestPure bytes = addr := by
  obtain ⟨ext, rfl, hdig⟩ := c.verify_bytes_against hs ha native ev
  exact ⟨ext, rfl, by rw [digestWith_plain]; exact hdig,
    by rw [ProtocolDomain.digestPure_eq_digestWith, ProtocolDomain.pinnedCV,
           ProtocolDomain.domainFlags, digestWith_plain]; exact hdig⟩

/-- **Link from `Blake3::bytes_to_addr` (`Blake3Spec`) to `digestWith` / `ProtocolDomain.plain`.** -/
theorem eval_bytes_to_addr_eq_digestWith_plain (c : Blake3Contracts world)
    {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    (hs : Stream h bytes inp) (native : Blake3.Pure.NativeInput bytes)
    (ev : EvalFn world "Blake3::bytes_to_addr" [inp] h r h') :
    Heap.Extends h h' ∧
    loadValue h' r = .ok (digestV (digestWith Blake3.Pure.iv 0 bytes)) := by
  obtain ⟨ext, hld⟩ := c.bytes_to_addr_digest hs native ev
  rw [← digestWith_plain bytes] at hld
  exact ⟨ext, hld⟩

end MultiBlockAndChunk

/-! ## Section 5: Bundled `Blake3KeyedContracts` & Multi-Field Instantiations -/

section BundledKeyedContracts

variable {F : Type} [Field F] [DecidableEq F]

/-- **Field-polymorphic operational `EvalFn` contract bundle for keyed, `derive_key`, and
custom-IV / custom-flags BLAKE3 over `Aiur.Library.Blake3`.**

Derived directly from `Blake3Spec.checkBlake3World s = true` plus `Aiur.Library.U32.Compatible F`
(covering Goldilocks, BN254 `Fr`, BLS12-381 `Fr`, and every prime field `ZMod p` with
`3 * 2^32 ≤ p`). -/
structure Blake3KeyedContracts (world : World F) : Prop where
  base : Blake3Contracts world
  compress_custom_state : ∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len fl : UInt32} {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress"
      [.field 0, stateV (Blake3.Pure.initialWords cv ctr len fl) m] h r h' →
    r = vecV (Blake3.Pure.compress cv m ctr len fl) ∧ h' = h
  compress_init_domain_flags : ∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len : Nat} {dFlags bFlags : UInt32},
    len < 256 → ValidDomainFlags dFlags → bFlags.toNat < 16 →
    ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v ctr, .field (len : F), .field ((dFlags ||| bFlags).toNat : F)] h r h' →
    r = vecV (Blake3.Pure.compress cv m ctr len.toUInt32 (dFlags ||| bFlags)) ∧ h' = h
  compress_init_domain_flags_add : ∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block}
    {ctr : UInt64} {len : Nat} {dFlags bFlags : UInt32},
    len < 256 → ValidDomainFlags dFlags → bFlags.toNat < 16 →
    ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV cv, vecV m, u64v ctr, .field (len : F), .field ((dFlags.toNat : F) + (bFlags.toNat : F))]
      h r h' →
    r = vecV (Blake3.Pure.compress cv m ctr len.toUInt32 (dFlags ||| bFlags)) ∧ h' = h
  keyed_single_block : ∀ {key : Blake3.Pure.CV} {bytes : List UInt8},
    bytes.length ≤ 64 → ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV key, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (27 : F)] h r h' →
    r = vecV (digestCVKeyed key bytes) ∧ h' = h
  derive_key_context_single_block : ∀ {ctxBytes : List UInt8},
    ctxBytes.length ≤ 64 → ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV Blake3.Pure.iv, vecV (Blake3.Pure.blockWords ctxBytes), u64v 0,
       .field (ctxBytes.length : F), .field (43 : F)] h r h' →
    r = vecV (deriveKeyContextCV ctxBytes) ∧ h' = h
  derive_key_material_single_block : ∀ {ctxCV : Blake3.Pure.CV} {bytes : List UInt8},
    bytes.length ≤ 64 → ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV ctxCV, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (75 : F)] h r h' →
    r = vecV (digestCVWith ctxCV flagDeriveKeyMaterial bytes) ∧ h' = h
  two_pass_derive_key_single_block : ∀ {ctx : String} {bytes : List UInt8},
    ctx.toUTF8.data.toList.length ≤ 64 → bytes.length ≤ 64 →
    ∀ {rCtx rOut : SourceValue F} {h h1 h2 : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV Blake3.Pure.iv, vecV (Blake3.Pure.blockWords ctx.toUTF8.data.toList), u64v 0,
       .field (ctx.toUTF8.data.toList.length : F), .field (43 : F)] h rCtx h1 →
    EvalFn world "Blake3::compress_init"
      [rCtx, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field (75 : F)] h1 rOut h2 →
    rCtx = vecV (deriveKeyContextCV ctx.toUTF8.data.toList) ∧
    rOut = vecV (digestCVDeriveKey ctx bytes) ∧ h2 = h
  domain_single_block : ∀ (d : ProtocolDomain) {bytes : List UInt8},
    bytes.length ≤ 64 → ∀ {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV d.pinnedCV, vecV (Blake3.Pure.blockWords bytes), u64v 0,
       .field (bytes.length : F), .field ((d.domainFlags ||| 11).toNat : F)] h r h' →
    r = vecV (d.digestCVPure bytes) ∧ h' = h
  domain_pair : ∀ (d : ProtocolDomain) (left right : Blake3.Pure.CV)
    {r : SourceValue F} {h h' : Heap F},
    EvalFn world "Blake3::compress_init"
      [vecV d.pinnedCV, vecV (left ++ right), u64v 0, .field (64 : F),
       .field ((d.domainFlags ||| 11).toNat : F)] h r h' →
    r = vecV (d.digestCVPure
      ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList)) ∧ h' = h
  chunk_chain_root : ∀ {key : Blake3.Pure.CV} {dFlags : UInt32},
    ValidDomainFlags dFlags → ∀ {bytes : List UInt8}, bytes.length ≤ 1024 →
    ∀ {r : SourceValue F} {h h' : Heap F},
    EvalChunkChain world dFlags 0 true (vecV key) bytes true h r h' →
    r = vecV (digestCVWith key dFlags bytes) ∧ h' = h
  multi_chunk_with : ∀ {key : Blake3.Pure.CV} {dFlags : UInt32},
    ValidDomainFlags dFlags → ∀ {bytes : List UInt8} {rRoot : SourceValue F} {h h' : Heap F},
    EvalMultiChunkWith world key dFlags bytes h rRoot h' →
    rRoot = vecV (digestCVWith key dFlags bytes) ∧ h' = h
  multi_chunk_keyed : ∀ {key : Blake3.Pure.CV} {bytes : List UInt8}
    {rCV rDig : SourceValue F} {h h1 h2 : Heap F},
    EvalMultiChunkWith world key flagKeyedHash bytes h rCV h1 →
    EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2 →
    rCV = vecV (digestCVKeyed key bytes) ∧ rDig = digestV (digestKeyed key bytes) ∧ h2 = h
  multi_chunk_two_pass_derive_key : ∀ {ctx : String} {bytes : List UInt8} {ctxCV : Blake3.Pure.CV}
    {rOut rDig : SourceValue F} {h h1 h2 h3 : Heap F},
    EvalMultiChunkWith world Blake3.Pure.iv flagDeriveKeyContext
      ctx.toUTF8.data.toList h (vecV ctxCV) h1 →
    EvalMultiChunkWith world ctxCV flagDeriveKeyMaterial bytes h1 rOut h2 →
    EvalFn world "Blake3::digest_bytes" [rOut] h2 rDig h3 →
    ctxCV = deriveKeyContextCV ctx.toUTF8.data.toList ∧
    rOut = vecV (digestCVDeriveKey ctx bytes) ∧
    rDig = digestV (digestDeriveKey ctx bytes) ∧ h3 = h
  multi_chunk_domain : ∀ (d : ProtocolDomain) {bytes : List UInt8}
    {rCV rDig : SourceValue F} {h h1 h2 : Heap F},
    EvalMultiChunkWith world d.pinnedCV d.domainFlags bytes h rCV h1 →
    EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2 →
    rCV = vecV (d.digestCVPure bytes) ∧ rDig = digestV (d.digestPure bytes) ∧ h2 = h
  hash_blocks_custom_cv_single_chunk : ∀ {cv : Blake3.Pure.CV} {bytes : List UInt8},
    bytes.length ≤ 1024 →
    ∀ {inp ccp cvp lp rLayer rCV : SourceValue F} {h h1 h2 : Heap F},
    Stream h bytes inp →
    loadValue h ccp = .ok (u64v 0) →
    loadValue h cvp = .ok (vecV cv) →
    Stack h [] lp →
    EvalFn world "Blake3::hash_blocks" [inp, .field (0 : F), ccp, cvp, lp] h rLayer h1 →
    EvalFn world "Blake3::compress_layer" [rLayer] h1 rCV h2 →
    Heap.Extends h h2 ∧ rCV = vecV (digestCVWith cv 0 bytes)
  hash_eq_digestWith_plain : ∀ {bytes : List UInt8} {inp rCV rDig : SourceValue F}
    {h h1 h2 : Heap F},
    Stream h bytes inp → Blake3.Pure.NativeInput bytes →
    EvalFn world "Blake3::hash" [inp] h rCV h1 →
    EvalFn world "Blake3::digest_bytes" [rCV] h1 rDig h2 →
    Heap.Extends h h2 ∧
    rDig = digestV (digestWith Blake3.Pure.iv 0 bytes) ∧
    rDig = digestV (ProtocolDomain.plain.digestPure bytes)

/-- Construct `Blake3KeyedContracts world` from `U32.Compatible F` and `Blake3Contracts world`. -/
theorem Blake3KeyedContracts.ofBlake3Contracts {world : World F}
    (hc : U32.Compatible F) (c : Blake3Contracts world) : Blake3KeyedContracts world where
  base := c
  compress_custom_state := eval_compress_custom_state c
  compress_init_domain_flags := eval_compress_init_domain_flags c
  compress_init_domain_flags_add := eval_compress_init_domain_flags_add c
  keyed_single_block := eval_compress_init_keyed_single_block c
  derive_key_context_single_block := eval_compress_init_derive_key_context_single_block c
  derive_key_material_single_block := eval_compress_init_derive_key_material_single_block c
  two_pass_derive_key_single_block := eval_two_pass_derive_key_single_block c
  domain_single_block := eval_compress_init_domain_single_block c
  domain_pair := eval_compress_init_domain_pair c
  chunk_chain_root := evalChunkChain_single_chunk_root c
  multi_chunk_with := evalMultiChunkWith_spec hc c
  multi_chunk_keyed := evalMultiChunkKeyed_spec hc c
  multi_chunk_two_pass_derive_key := evalTwoPassDeriveKey_multiChunk_spec hc c
  multi_chunk_domain := evalProtocolDomain_multiChunk_spec hc c
  hash_blocks_custom_cv_single_chunk := eval_hash_blocks_custom_cv_single_chunk c
  hash_eq_digestWith_plain := eval_hash_eq_digestWith_plain c

/-- Construct `Blake3KeyedContracts world` from `U32.Compatible F` and `Blake3LibraryWorld world`. -/
theorem Blake3KeyedContracts.ofLibraryWorld {world : World F}
    (hc : U32.Compatible F) (lib : Blake3LibraryWorld world) : Blake3KeyedContracts world :=
  Blake3KeyedContracts.ofBlake3Contracts hc (Blake3Contracts.ofLibraryWorld hc lib)

/-- Construct `Blake3KeyedContracts s.world` directly from `checkBlake3World s = true` over
ANY `[Field F] [DecidableEq F]` satisfying `U32.Compatible F`. -/
theorem Blake3KeyedContracts.ofCheck (hc : U32.Compatible F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofBlake3Contracts hc (Blake3Contracts.ofCheck hc h)

/-- Construct `Blake3KeyedContracts s.world` from `FieldCompatible64 F` (matching `TypedWorld`). -/
theorem Blake3KeyedContracts.ofCheck64 (fc : FieldCompatible64 F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck fc.toU32Compatible h

/-- Construct `Blake3KeyedContracts s.world` from `FieldCompatible F` (matching `World`). -/
theorem Blake3KeyedContracts.ofCheckFieldCompatible (fc : FieldCompatible F) {s : Generic.Source F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck (u32Compat_of_fieldCompatible fc) h

/-- Construct `Blake3KeyedContracts s.world` over any prime field `ZMod p` with `3 * 2^32 ≤ p`. -/
theorem Blake3KeyedContracts.ofCheckZMod (p : Nat) [Fact (Nat.Prime p)] (hp : 3 * U32.base ≤ p)
    {s : Generic.Source (ZMod p)} (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck (u32Compat_of_zmod p hp) h

/-! ### Concrete Field Instantiations: Goldilocks, BN254 `Fr`, and BLS12-381 `Fr` -/

/-- **Goldilocks instantiation** (`ZMod (2^64 - 2^32 + 1)`). -/
theorem Blake3KeyedContracts.ofCheckGoldilocks
    {s : Generic.Source Aiur.Library.U32.Goldilocks.F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck Aiur.Library.U32.Goldilocks.compatible h

/-- **BN254 `Fr` instantiation** (`Aiur.Library.Field.BN254.F`). -/
theorem Blake3KeyedContracts.ofCheckBN254
    {s : Generic.Source Aiur.Library.Field.BN254.F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck Aiur.Library.Field.BN254.u32_compatible h

/-- **BLS12-381 `Fr` instantiation** (`Aiur.Library.Field.BLS12381.F`). -/
theorem Blake3KeyedContracts.ofCheckBLS12381
    {s : Generic.Source Aiur.Library.Field.BLS12381.F}
    (h : checkBlake3World s = true) : Blake3KeyedContracts s.world :=
  Blake3KeyedContracts.ofCheck Aiur.Library.Field.BLS12381.u32_compatible h

/-! ### End-to-End Multi-Field Smoke Theorems -/

/-- **Goldilocks smoke theorem:** Protocol `v6` 2-to-1 Merkle node compression + `digest_bytes` +
`pack_digest` matches `digestDeriveKey "multi-stark/v6/merkle/compress"`. -/
theorem goldilocks_blake3_v6_merkle_compress_smoke
    (s : Generic.Source Aiur.Library.U32.Goldilocks.F)
    (hchk : checkBlake3World s = true)
    (left right : Blake3.Pure.CV)
    (rCV rDig rPack : SourceValue Aiur.Library.U32.Goldilocks.F)
    (h h1 h2 h3 : Heap Aiur.Library.U32.Goldilocks.F)
    (evComp : EvalFn s.world "Blake3::compress_init"
      [vecV ProtocolDomain.v6MerkleCompress.pinnedCV, vecV (left ++ right),
       u64v 0, .field (64 : Aiur.Library.U32.Goldilocks.F),
       .field (75 : Aiur.Library.U32.Goldilocks.F)] h rCV h1)
    (evDig : EvalFn s.world "Blake3::digest_bytes" [rCV] h1 rDig h2)
    (evPack : EvalFn s.world "Blake3::pack_digest" [rCV] h2 rPack h3) :
    rDig = digestV (digestDeriveKey "multi-stark/v6/merkle/compress"
      ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList)) ∧
    rPack = .tuple ((Aiur.Library.Blake3.packDigest Aiur.Library.U32.Goldilocks.F
      (digestCVDeriveKey "multi-stark/v6/merkle/compress"
        ((Blake3.Pure.cvBytes left).toList ++ (Blake3.Pure.cvBytes right).toList))).toList.map .field) ∧
    h3 = h := by
  have kc := Blake3KeyedContracts.ofCheckGoldilocks hchk
  have h75 : (75 : Aiur.Library.U32.Goldilocks.F) =
      ((ProtocolDomain.v6MerkleCompress.domainFlags ||| 11).toNat : Aiur.Library.U32.Goldilocks.F) := by
    change (75 : Aiur.Library.U32.Goldilocks.F) = ((75 : Nat) : Aiur.Library.U32.Goldilocks.F)
    simp
  rw [h75] at evComp
  obtain ⟨rfl, rfl⟩ := kc.domain_pair .v6MerkleCompress left right evComp
  obtain ⟨rfl, rfl⟩ := kc.base.digest_bytes evDig
  obtain ⟨rfl, rfl⟩ := kc.base.pack_digest evPack
  exact ⟨rfl, rfl, rfl⟩

/-- **BN254 `Fr` smoke theorem:** arbitrary-length multi-chunk keyed (`KEYED_HASH = 16`) and
two-pass `derive_key` execution over `Aiur.Library.Field.BN254.F`. -/
theorem bn254_blake3_keyed_and_derive_key_smoke
    (s : Generic.Source Aiur.Library.Field.BN254.F)
    (hchk : checkBlake3World s = true)
    (key : Blake3.Pure.CV) (ctx : String) (bytes : List UInt8) (ctxCV : Blake3.Pure.CV)
    (rKeyCV rKeyDig rDkCV rDkDig : SourceValue Aiur.Library.Field.BN254.F)
    (h h1 h2 h3 h4 h5 : Heap Aiur.Library.Field.BN254.F)
    (evKey : EvalMultiChunkWith s.world key flagKeyedHash bytes h rKeyCV h1)
    (evKeyDig : EvalFn s.world "Blake3::digest_bytes" [rKeyCV] h1 rKeyDig h2)
    (evCtx : EvalMultiChunkWith s.world Blake3.Pure.iv flagDeriveKeyContext
      ctx.toUTF8.data.toList h2 (vecV ctxCV) h3)
    (evMat : EvalMultiChunkWith s.world ctxCV flagDeriveKeyMaterial bytes h3 rDkCV h4)
    (evDkDig : EvalFn s.world "Blake3::digest_bytes" [rDkCV] h4 rDkDig h5) :
    rKeyDig = digestV (digestKeyed key bytes) ∧
    rDkDig = digestV (digestDeriveKey ctx bytes) ∧
    h5 = h := by
  have kc := Blake3KeyedContracts.ofCheckBN254 hchk
  obtain ⟨_, rfl, rfl⟩ := kc.multi_chunk_keyed evKey evKeyDig
  obtain ⟨_, _, rfl, rfl⟩ := kc.multi_chunk_two_pass_derive_key evCtx evMat evDkDig
  exact ⟨rfl, rfl, rfl⟩

/-- **BLS12-381 `Fr` smoke theorem:** arbitrary-length multi-chunk domain-separated hashing across
all 11 `ProtocolDomain`s (`plain`, 5 `v6`, 5 `v6-zk`) + `digest_bytes` + `pack_digest` over
`Aiur.Library.Field.BLS12381.F`. -/
theorem bls12381_blake3_domain_smoke
    (s : Generic.Source Aiur.Library.Field.BLS12381.F)
    (hchk : checkBlake3World s = true)
    (d : ProtocolDomain) (bytes : List UInt8)
    (rCV rDig rPack : SourceValue Aiur.Library.Field.BLS12381.F)
    (h h1 h2 h3 : Heap Aiur.Library.Field.BLS12381.F)
    (evHash : EvalMultiChunkWith s.world d.pinnedCV d.domainFlags bytes h rCV h1)
    (evDig : EvalFn s.world "Blake3::digest_bytes" [rCV] h1 rDig h2)
    (evPack : EvalFn s.world "Blake3::pack_digest" [rCV] h2 rPack h3) :
    rDig = digestV (d.digestPure bytes) ∧
    rPack = .tuple ((Aiur.Library.Blake3.packDigest Aiur.Library.Field.BLS12381.F
      (d.digestCVPure bytes)).toList.map .field) ∧
    h3 = h := by
  have kc := Blake3KeyedContracts.ofCheckBLS12381 hchk
  obtain ⟨rfl, rfl, rfl⟩ := kc.multi_chunk_domain d evHash evDig
  obtain ⟨rfl, rfl⟩ := kc.base.pack_digest evPack
  exact ⟨rfl, rfl, rfl⟩

end BundledKeyedContracts

/-! ## Section 6: Axiom Audit Fences -/

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.digestWith_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms digestWith_plain

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.mergeLevelsWith_chunkOutputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mergeLevelsWith_chunkOutputs

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressLayerWith_spec

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.pinnedCV_eq_deriveKeyContextCV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProtocolDomain.pinnedCV_eq_deriveKeyContextCV

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.digestPure_eq_digestWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProtocolDomain.digestPure_eq_digestWith

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.pinnedCV_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProtocolDomain.pinnedCV_injective

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.mode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProtocolDomain.mode_injective

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_custom_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_custom_state

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_init_domain_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_init_domain_flags

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_init_domain_flags_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_init_domain_flags_add

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_init_keyed_single_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_init_keyed_single_block

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_keyed_single_block_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_keyed_single_block_digest

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_two_pass_derive_key_single_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_two_pass_derive_key_single_block

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_init_domain_single_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_init_domain_single_block

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_compress_init_domain_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_compress_init_domain_pair

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.evalChunkChain_single_chunk_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalChunkChain_single_chunk_root

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.evalMultiChunkWith_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalMultiChunkWith_spec

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.evalMultiChunkKeyed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalMultiChunkKeyed_spec

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.evalTwoPassDeriveKey_multiChunk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalTwoPassDeriveKey_multiChunk_spec

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.evalProtocolDomain_multiChunk_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalProtocolDomain_multiChunk_spec

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_hash_blocks_custom_cv_single_chunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_hash_blocks_custom_cv_single_chunk

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_hash_eq_digestWith_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_hash_eq_digestWith_plain

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_verify_bytes_against_eq_digestWith_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_verify_bytes_against_eq_digestWith_plain

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.eval_bytes_to_addr_eq_digestWith_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eval_bytes_to_addr_eq_digestWith_plain

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.Blake3KeyedContracts.ofCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Blake3KeyedContracts.ofCheck

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.Blake3KeyedContracts.ofCheckGoldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Blake3KeyedContracts.ofCheckGoldilocks

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.Blake3KeyedContracts.ofCheckBN254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Blake3KeyedContracts.ofCheckBN254

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.Blake3KeyedContracts.ofCheckBLS12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Blake3KeyedContracts.ofCheckBLS12381

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.goldilocks_blake3_v6_merkle_compress_smoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocks_blake3_v6_merkle_compress_smoke

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.bn254_blake3_keyed_and_derive_key_smoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bn254_blake3_keyed_and_derive_key_smoke

/-- info: 'IxCC.AiurBackend.Blake3KeyedSpec.bls12381_blake3_domain_smoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bls12381_blake3_domain_smoke

end IxCC.AiurBackend.Blake3KeyedSpec
