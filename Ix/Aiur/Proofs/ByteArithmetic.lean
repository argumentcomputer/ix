/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LocalConstraints

/-!
Virtual byte carries and the four-byte strict-comparison gadget.

The native byte-add/subtract lookups supply only their low byte. Multiplying
the residual by the inverse of 256 gives the carry or borrow in the semantic
operation. For `u32_less_than`, twelve range-checked bytes and four boolean
carry equations give the integer identity `a + witness + 1 = b + carry*2^32`.
The range bounds make its final carry exactly the complement of `a < b`.

All arithmetic is over the actual Goldilocks representation. Lookup-derived
byte bounds and decoding the native expressions remain separate inputs.
-/

namespace Aiur

theorem G.mul_assoc (a b c : G) : (a * b) * c = a * (b * c) := by
  apply G.ext_n
  simp only [G.n_mul, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem G.n_sub (a b : G) : (a - b).n = (a.n + gSize.toNat - b.n) % gSize.toNat :=
  G.n_ofNat _

namespace AIR

def inverse256 : G := 18374686475393433601

theorem inverse256_correct : inverse256 * 256 = 1 := by decide +kernel

theorem byte_division_eq (value : G) : (value * inverse256) * 256 = value := by
  rw [G.mul_assoc, inverse256_correct, G.mul_one]

theorem byte_add_carry {x y low : G} (hx : x.n < 256) (hy : y.n < 256)
    (hlow : low = G.ofNat ((x.n + y.n) % 256)) :
    (x + y - low) * inverse256 = G.ofNat ((x.n + y.n) / 256) := by
  apply G.ext_n
  rw [hlow]
  simp only [G.n_mul, G.n_sub, G.n_add, G.n_ofNat]
  have p : gSize.toNat = 18446744069414584321 := by decide
  have inv : inverse256.n = 18374686475393433601 := rfl
  rw [p, inv]
  omega

theorem byte_sub_borrow {x y low : G} (hx : x.n < 256) (hy : y.n < 256)
    (hlow : low = G.ofNat ((x.n + 256 - y.n) % 256)) :
    (low + y - x) * inverse256 = if x.n < y.n then 1 else 0 := by
  have diff : low + y - x = if x.n < y.n then 256 else 0 := by
    apply G.ext_n
    rw [hlow]
    split
    all_goals
      simp only [G.n_sub, G.n_add, G.n_ofNat]
      have full : (256 : G).n = 256 := rfl
      have zero : (0 : G).n = 0 := rfl
      simp only [full, zero]
      have p : gSize.toNat = 18446744069414584321 := by decide
      rw [p]
      omega
  rw [diff]
  split <;> decide +kernel

theorem byte_carry_relation {x y z previous carry : G}
    (hx : x.n < 256) (hy : y.n < 256) (hz : z.n < 256)
    (hp : previous = 0 ∨ previous = 1) (hc : carry = 0 ∨ carry = 1)
    (computed : carry = (x + y + previous - z) * inverse256) :
    x.n + y.n + previous.n = z.n + 256 * carry.n := by
  have hp' : previous.n ≤ 1 := by rcases hp with rfl | rfl <;> decide
  have hc' : carry.n ≤ 1 := by rcases hc with rfl | rfl <;> decide
  have fieldEqual : carry * 256 = x + y + previous - z := by
    rw [computed, byte_division_eq]
  have numeric := congrArg G.n fieldEqual
  simp only [G.n_mul, G.n_sub, G.n_add] at numeric
  have scale : (256 : G).n = 256 := rfl
  have p : gSize.toNat = 18446744069414584321 := by decide
  rw [scale, p] at numeric
  omega

def pack4 (bytes : Fin 4 → G) : G :=
  bytes 0 + 256 * bytes 1 + 65536 * bytes 2 + 16777216 * bytes 3

def pack4Nat (bytes : Fin 4 → G) : Nat :=
  (bytes 0).n + 256 * (bytes 1).n + 65536 * (bytes 2).n + 16777216 * (bytes 3).n

theorem pack4_n (bytes : Fin 4 → G) (bounded : ∀ i, (bytes i).n < 256) :
    (pack4 bytes).n = pack4Nat bytes ∧ (pack4 bytes).n < 2 ^ 32 := by
  have h0 := bounded 0
  have h1 := bounded 1
  have h2 := bounded 2
  have h3 := bounded 3
  have totalBound : (bytes 0).n + 256 * (bytes 1).n + 65536 * (bytes 2).n +
      16777216 * (bytes 3).n < 2 ^ 32 := by omega
  have fieldBound : (bytes 0).n + 256 * (bytes 1).n + 65536 * (bytes 2).n +
      16777216 * (bytes 3).n < 18446744069414584321 :=
    Nat.lt_trans totalBound (by decide)
  have s1 : (256 : G).n = 256 := rfl
  have s2 : (65536 : G).n = 65536 := rfl
  have s3 : (16777216 : G).n = 16777216 := rfl
  simp only [pack4, pack4Nat, G.n_add, G.n_mul, s1, s2, s3]
  have p : gSize.toNat = 18446744069414584321 := by decide
  rw [p]
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]
  rw [Nat.mod_eq_of_lt fieldBound]
  exact ⟨rfl, totalBound⟩

def carryStep (x y z previous : G) : G := (x + y + previous - z) * inverse256

def u32Carries (x y z : Fin 4 → G) : Fin 5 → G :=
  let c1 := carryStep (x 0) (y 0) (z 0) 1
  let c2 := carryStep (x 1) (y 1) (z 1) c1
  let c3 := carryStep (x 2) (y 2) (z 2) c2
  let c4 := carryStep (x 3) (y 3) (z 3) c3
  fun i => match i with
    | 0 => 1
    | 1 => c1
    | 2 => c2
    | 3 => c3
    | 4 => c4

theorem u32Carry_relation (x y z : Fin 4 → G)
    (hx : ∀ i, (x i).n < 256) (hy : ∀ i, (y i).n < 256) (hz : ∀ i, (z i).n < 256)
    (boolean : ∀ i : Fin 4, booleanConstraint (u32Carries x y z i.succ) = 0) :
    pack4Nat x + pack4Nat y + 1 = pack4Nat z + 2 ^ 32 * (u32Carries x y z 4).n := by
  have hc0 : u32Carries x y z 0 = 0 ∨ u32Carries x y z 0 = 1 := Or.inr rfl
  have hc1 := G.boolean_of_constraint (boolean 0)
  have hc2 := G.boolean_of_constraint (boolean 1)
  have hc3 := G.boolean_of_constraint (boolean 2)
  have hc4 := G.boolean_of_constraint (boolean 3)
  have r0 := byte_carry_relation (hx 0) (hy 0) (hz 0) hc0 hc1 rfl
  have r1 := byte_carry_relation (hx 1) (hy 1) (hz 1) hc1 hc2 rfl
  have r2 := byte_carry_relation (hx 2) (hy 2) (hz 2) hc2 hc3 rfl
  have r3 := byte_carry_relation (hx 3) (hy 3) (hz 3) hc3 hc4 rfl
  simp only [show (0 : Fin 4).succ = (1 : Fin 5) from rfl,
    show (1 : Fin 4).succ = (2 : Fin 5) from rfl,
    show (2 : Fin 4).succ = (3 : Fin 5) from rfl,
    show (3 : Fin 4).succ = (4 : Fin 5) from rfl] at r0 r1 r2 r3
  have initial : (u32Carries x y z 0).n = 1 := rfl
  rw [initial] at r0
  unfold pack4Nat
  omega

theorem u32_less_than (x y z : Fin 4 → G)
    (hx : ∀ i, (x i).n < 256) (hy : ∀ i, (y i).n < 256) (hz : ∀ i, (z i).n < 256)
    (boolean : ∀ i : Fin 4, booleanConstraint (u32Carries x y z i.succ) = 0) :
    1 - u32Carries x y z 4 = G.u32LessThan (pack4 x) (pack4 z) := by
  have relation := u32Carry_relation x y z hx hy hz boolean
  obtain ⟨nx, bx⟩ := pack4_n x hx
  obtain ⟨ny, by'⟩ := pack4_n y hy
  obtain ⟨nz, bz⟩ := pack4_n z hz
  have last := G.boolean_of_constraint (boolean 3)
  change u32Carries x y z 4 = 0 ∨ u32Carries x y z 4 = 1 at last
  rcases last with zero | one
  · have value : (u32Carries x y z 4).n = 0 := congrArg G.n zero
    have less : (pack4 x).n < (pack4 z).n := by omega
    rw [zero, G.u32LessThan, if_pos less]
    decide +kernel
  · have value : (u32Carries x y z 4).n = 1 := congrArg G.n one
    have notLess : ¬(pack4 x).n < (pack4 z).n := by omega
    rw [one, G.u32LessThan, if_neg notLess]
    decide +kernel

theorem active_u32_less_than {selector a b : G} (active : selector = 1)
    (x y z : Fin 4 → G)
    (hx : ∀ i, (x i).n < 256) (hy : ∀ i, (y i).n < 256) (hz : ∀ i, (z i).n < 256)
    (decomposeA : selector * (a - pack4 x) = 0)
    (decomposeB : selector * (b - pack4 z) = 0)
    (carries : ∀ i : Fin 4, selector * booleanConstraint (u32Carries x y z i.succ) = 0) :
    a.n < 2 ^ 32 ∧ b.n < 2 ^ 32 ∧
      1 - u32Carries x y z 4 = G.u32LessThan a b := by
  have ha := active_case active decomposeA
  have hb := active_case active decomposeB
  subst a b
  refine ⟨(pack4_n x hx).2, (pack4_n z hz).2, u32_less_than x y z hx hy hz ?_⟩
  intro i
  have satisfied := carries i
  rw [active, G.mul_comm, G.mul_one] at satisfied
  exact satisfied

end AIR
end Aiur
