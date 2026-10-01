import Compilatrix.X86.Memory
import Compilatrix.Lir.Proof.Eval

/-!
# Words in byte memory

The heap invariant of `Rt.lower_correct` describes the context block and
the cells by the bytes of their words: `WordAt m b v` says the eight bytes
at `b` are `v`'s, little-endian, and readable. This module gives what the
allocator and the projections need of it:

* a 64-bit read of a `WordAt` is its word (`WordAt.read64`), and a 16-bit
  read two bytes in is the word's tag half-word (`WordAt.read16_tag`);
* a 64-bit store makes a `WordAt` (`wordAt_write64`), and two 32-bit stores
  make the word of `lo + 2^32·hi` (`wordAt_write32_pair`);
* a store elsewhere keeps a `WordAt` (`WordAt.write_disjoint`), and stores
  never change permissions.

Addresses are words; ranges are compared on `toNat` and never wrap (every
address the lowering touches is below `2^63` plus a few kilobytes).
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.X86 (Memory)
open Compilatrix.Lir (Word)

/-! ## Addresses -/

theorem addr_toNat {a : Word} {i : Nat} (h : a.toNat + i < 2 ^ 64) : (a + UInt64.ofNat i).toNat = a.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [this]
  exact Nat.mod_eq_of_lt h

theorem addr_ne {a b : Word} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (by rw [e])

theorem rangeAllowed_iff (perm : Word → Bool) (a : Word) (n : Nat) :
    Memory.rangeAllowed perm a n = true ↔ ∀ i < n, perm (a + UInt64.ofNat i) = true := by
  constructor
  · intro h
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      simp only [Memory.rangeAllowed, Bool.and_eq_true] at h
      intro i hi
      by_cases hin : i < n
      · exact ih h.1 i hin
      · have : i = n := by omega
        subst this; exact h.2
  · exact X86.Memory.rangeAllowed_of_forall perm a n

/-! ## Permissions -/

@[simp] theorem writeLittle_readable (m : Memory) (a v : Word) (n : Nat) :
    (m.writeLittle a v n).readable = m.readable := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Memory.writeLittle, Memory.writeByte, ih]

@[simp] theorem writeLittle_writable (m : Memory) (a v : Word) (n : Nat) :
    (m.writeLittle a v n).writable = m.writable := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Memory.writeLittle, Memory.writeByte, ih]

/-- A store succeeds on writable bytes, and is the plain write. -/
theorem write?_ok {m : Memory} {w : X86.Width} {a v : Word}
    (h : ∀ i < w.bytes, m.writable (a + UInt64.ofNat i) = true) :
    m.write? w a v = .ok (m.write w a v) := by
  simp [Memory.write?, (rangeAllowed_iff _ _ _).2 h]

theorem read?_ok {m : Memory} {w : X86.Width} {a : Word}
    (h : ∀ i < w.bytes, m.readable (a + UInt64.ofNat i) = true) :
    m.read? w a = .ok (m.read w a) := by
  simp [Memory.read?, (rangeAllowed_iff _ _ _).2 h]

/-! ## Words -/

/-- The eight bytes at `b` are `v`'s, little-endian, and readable. -/
structure WordAt (m : Memory) (b v : Word) : Prop where
  bytes : ∀ i < 8, m.bytes (b + UInt64.ofNat i) = (v >>> UInt64.ofNat (8 * i)).toUInt8
  readable : ∀ i < 8, m.readable (b + UInt64.ofNat i) = true

/-- A `WordAt` reads back as its word. -/
theorem WordAt.read64 {m : Memory} {b v : Word} (h : WordAt m b v) : m.read? .w64 b = .ok v := by
  rw [read?_ok (w := .w64) (fun i hi => h.readable i (by simpa [X86.Width.bytes] using hi))]
  congr 1
  have : m.readLittle b 8 = (m.write64 b v).readLittle b 8 := by
    apply X86.Memory.readLittle_congr
    intro i hi
    rw [h.bytes i hi]
    exact (X86.Memory.writeLittle_bytes m b v (by omega) hi).symm
  change m.readLittle b 8 = v
  rw [this]
  exact X86.Memory.read64_write64 m b v

/-- A 64-bit store makes a `WordAt` on readable bytes. -/
theorem wordAt_write64 {m : Memory} {b v : Word} (hr : ∀ i < 8, m.readable (b + UInt64.ofNat i) = true) :
    WordAt (m.write .w64 b v) b v where
  bytes i hi := X86.Memory.writeLittle_bytes m b v (by simp [X86.Width.bytes]) (by simpa [X86.Width.bytes] using hi)
  readable i hi := by simpa [Memory.write] using hr i hi

/-- Bytes outside a store are untouched (no wrap: `b` lies outside
`[a, a + n)` as numbers). -/
theorem writeLittle_bytes_out {m : Memory} {a b v : Word} {n : Nat} (hn : n ≤ 8)
    (ha : a.toNat + n ≤ 2 ^ 64) (hb : b.toNat < a.toNat ∨ a.toNat + n ≤ b.toNat) :
    (m.writeLittle a v n).bytes b = m.bytes b := by
  apply X86.Memory.writeLittle_bytes_outside
  intro i hi
  apply addr_ne
  rw [addr_toNat (by omega)]
  omega

/-- A store elsewhere keeps a `WordAt`. -/
theorem WordAt.write_disjoint {m : Memory} {b v a u : Word} {w : X86.Width} (h : WordAt m b v)
    (ha : a.toNat + w.bytes ≤ 2 ^ 64) (hb : b.toNat + 8 ≤ 2 ^ 64)
    (hd : b.toNat + 8 ≤ a.toNat ∨ a.toNat + w.bytes ≤ b.toNat) :
    WordAt (m.write w a u) b v where
  bytes i hi := by
    have hw : w.bytes ≤ 8 := by cases w <;> simp [X86.Width.bytes]
    simp only [Memory.write]
    rw [writeLittle_bytes_out hw ha (by rw [addr_toNat (by omega)]; omega)]
    exact h.bytes i hi
  readable i hi := by simpa [Memory.write] using h.readable i hi

/-! ## Two 32-bit halves -/

theorem toUInt8_toNat (x : Word) : x.toUInt8.toNat = x.toNat % 256 := by
  simp [UInt64.toNat_toUInt8]

theorem byte_of_shift (x : Word) (k : Nat) (hk : k < 64) :
    (x >>> UInt64.ofNat k).toUInt8.toNat = x.toNat / 2 ^ k % 256 := by
  rw [toUInt8_toNat, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

/-- Two 32-bit stores at `a` and `a + 4` make the word of `lo + 2^32·hi`. -/
theorem wordAt_write32_pair {m : Memory} {a lo hi : Word} (hlo : lo.toNat < 2 ^ 32) (hhi : hi.toNat < 2 ^ 32)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hr : ∀ i < 8, m.readable (a + UInt64.ofNat i) = true) :
    WordAt ((m.write .w32 a lo).write .w32 (a + 4) hi) a (UInt64.ofNat (lo.toNat + 2 ^ 32 * hi.toNat)) where
  bytes i hi8 := by
    have hv : (UInt64.ofNat (lo.toNat + 2 ^ 32 * hi.toNat)).toNat = lo.toNat + 2 ^ 32 * hi.toNat :=
      toNat_ofNat_lt' (by omega)
    apply UInt8.toNat_inj.mp
    rw [byte_of_shift _ _ (by omega), hv]
    have h4 : (a + 4).toNat = a.toNat + 4 := by
      have := addr_toNat (a := a) (i := 4) (by omega)
      simpa using this
    simp only [Memory.write, X86.Width.bytes]
    by_cases hlow : i < 4
    · rw [writeLittle_bytes_out (by omega) (by omega) (by rw [addr_toNat (by omega), h4]; omega)]
      rw [X86.Memory.writeLittle_bytes m a lo (by omega) hlow, byte_of_shift _ _ (by omega)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
    · have hai : a + UInt64.ofNat i = (a + 4) + UInt64.ofNat (i - 4) := by
        apply UInt64.toNat_inj.mp
        rw [addr_toNat (by omega), addr_toNat (by omega), h4]
        omega
      rw [hai, X86.Memory.writeLittle_bytes _ (a + 4) hi (by omega) (by omega), byte_of_shift _ _ (by omega)]
      rcases (show i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with rfl | rfl | rfl | rfl <;> omega
  readable i hi8 := by simpa [Memory.write] using hr i hi8
where
  toNat_ofNat_lt' {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-! ## The tag half-word -/

theorem add_two_toNat {a : Word} (ha : a.toNat + 8 ≤ 2 ^ 64) : (a + 2).toNat = a.toNat + 2 := by
  rw [UInt64.toNat_add]
  simp
  omega

/-- The 16-bit read two bytes into a word is bits 16–31 of the word. -/
theorem WordAt.read16_tag {m : Memory} {a v : Word} (h : WordAt m a v) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    m.read? .w16 (a + 2) = .ok (UInt64.ofNat (v.toNat / 2 ^ 16 % 2 ^ 16)) := by
  have hA := add_two_toNat ha
  have h2 : ∀ i < 2, a + 2 + UInt64.ofNat i = a + UInt64.ofNat (2 + i) := by
    intro i hi
    apply UInt64.toNat_inj.mp
    rw [addr_toNat (by omega), addr_toNat (by omega), hA]
    omega
  rw [read?_ok (w := .w16) (fun i hi => by
    have hi' : i < 2 := by simpa [X86.Width.bytes] using hi
    rw [h2 i hi']
    exact h.readable _ (by omega))]
  congr 1
  apply UInt64.toNat_inj.mp
  have e0 : m.bytes (a + 2 + UInt64.ofNat 0) = (v >>> UInt64.ofNat 16).toUInt8 := by
    rw [h2 0 (by omega)]; exact h.bytes 2 (by omega)
  have e1 : m.bytes (a + 2 + UInt64.ofNat 1) = (v >>> UInt64.ofNat 24).toUInt8 := by
    rw [h2 1 (by omega)]; exact h.bytes 3 (by omega)
  simp only [Memory.read, X86.Width.bytes, Memory.readLittle, e0, e1]
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    UInt8.toNat_toUInt64, byte_of_shift _ _ (by omega), byte_of_shift _ _ (by omega)]
  have hv := v.toNat_lt_size
  simp only [UInt64.size] at hv
  simp only [UInt64.toNat_ofNat', Nat.mul_zero, Nat.mul_one, Nat.zero_mod, Nat.shiftLeft_zero]
  rw [show UInt64.toNat 0 = 0 from rfl, Nat.zero_or, show 8 % 2 ^ 64 % 64 = 8 from rfl, Nat.shiftLeft_eq]
  have h1 : v.toNat / 2 ^ 16 % 256 % 2 ^ 64 = v.toNat / 2 ^ 16 % 256 := Nat.mod_eq_of_lt (by omega)
  have h2' : v.toNat / 2 ^ 24 % 256 * 2 ^ 8 % 2 ^ 64 = v.toNat / 2 ^ 24 % 256 * 2 ^ 8 :=
    Nat.mod_eq_of_lt (by omega)
  rw [h1, h2', Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

end Compilatrix.Rt.Proof
