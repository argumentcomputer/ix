import IxCC.BigNat.NatEntry
import IxCC.BigNat.Proof

/-! # The entries over `Nat` are the `Nat` operations (`IxCC.BigNat.Proof.NatEntry`)

Design note: `plans/ONE-PIPELINE.md`, sections 4.3 and 4.6.

1. **The adapter layer.** The two representation primitives of `IxCC.Nat.Rep` against the
   library's own reading of a limb array: `ofLimbs a = BigNat.toNat a` for every array,
   `BigNat.toNat (toLimbs n) = n`, `BigNat.WF (toLimbs n)`, and the library's normal form `WF`
   is the specification's `CanonicalLimbs`.
2. **One equation per entry**: the entry is the `Nat` operation, for all arguments, with no
   side condition (`add_eq`, ..., `log2_eq`). Each is a corollary of the limb-level theorem of
   the library (`toNat_add`, ...), whose statement is unchanged, and of the adapter layer.
3. **The equations collected** (`Spec`, proved by `spec`): the contract of the library as a
   proposition about Lean functions over `Nat`. The design's `NatLib.Spec` is this contract
   about the compiled image of these same functions at `Fir`'s evaluator; it stays a named
   hypothesis until grounding and progress cover the library (decision D6). The form indexed by
   the evaluators' primitive type is `IxCC.BigNat.Proof.NatPrim`.

Every theorem depends on a subset of `[propext, Classical.choice, Quot.sound]`
(`IxCCTests.Fences.BigNat`).
-/

set_option autoImplicit false

namespace IxCC.BigNat.NatEntry

open IxCC.BigNat
open IxCC.NatRep (toLimbs ofLimbs limbBase CanonicalLimbs)

/-! ## The adapter layer: limb arrays of the library and the representation primitives -/

theorem getLimb_mk_cons_zero (l : UInt64) (ls : List UInt64) :
    getLimb (Array.mk (l :: ls)) 0 = l :=
  getLimb_lt (show 0 < (Array.mk (l :: ls)).size from Nat.succ_pos ls.length)

theorem getLimb_mk_cons_succ (l : UInt64) (ls : List UInt64) (i : Nat) :
    getLimb (Array.mk (l :: ls)) (i + 1) = getLimb (Array.mk ls) i := by
  by_cases h : i < ls.length
  · have h1 : i + 1 < (Array.mk (l :: ls)).size := Nat.succ_lt_succ h
    have h2 : i < (Array.mk ls).size := h
    exact (getLimb_lt h1).trans (getLimb_lt h2).symm
  · have h1 : (Array.mk (l :: ls)).size ≤ i + 1 := Nat.succ_le_succ (Nat.le_of_not_lt h)
    have h2 : (Array.mk ls).size ≤ i := Nat.le_of_not_lt h
    exact (getLimb_ge h1).trans (getLimb_ge h2).symm

private theorem horner_step (a b p g q : Nat) :
    a + b * p + g * (q * b) = a + b * (p + g * q) := by
  rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm q b, Nat.mul_left_comm g b q]

theorem toNatPrefix_mk_cons (l : UInt64) (ls : List UInt64) : ∀ k : Nat,
    toNatPrefix (Array.mk (l :: ls)) (k + 1) =
      l.toNat + 2 ^ 64 * toNatPrefix (Array.mk ls) k
  | 0 => by
    rw [toNatPrefix_succ (Array.mk (l :: ls)) 0, toNatPrefix_zero, toNatPrefix_zero,
      getLimb_mk_cons_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  | k + 1 => by
    have hp : (2 ^ 64 : Nat) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 := Nat.pow_succ (2 ^ 64) k
    rw [toNatPrefix_succ (Array.mk (l :: ls)) (k + 1), toNatPrefix_mk_cons l ls k,
      getLimb_mk_cons_succ, toNatPrefix_succ (Array.mk ls) k, hp]
    exact horner_step _ _ _ _ _

/-- The library's value of a limb array, one limb at a time from the least significant. -/
theorem toNat_mk_cons (l : UInt64) (ls : List UInt64) :
    toNat (Array.mk (l :: ls)) = l.toNat + 2 ^ 64 * toNat (Array.mk ls) :=
  toNatPrefix_mk_cons l ls ls.length

/-- **`ofLimbs` is the library's `toNat`**, on every limb array (canonical or not). -/
theorem ofLimbs_eq_toNat (a : Array UInt64) : ofLimbs a = toNat a := by
  cases a with
  | mk ls =>
    induction ls with
    | nil => rfl
    | cons l ls ih =>
      exact (IxCC.NatRep.ofLimbs_mk_cons l ls).trans
        ((congrArg (fun t => l.toNat + 2 ^ 64 * t) ih).trans (toNat_mk_cons l ls).symm)

theorem toLimbsFuel_eq_ofNatLoop : ∀ (fuel n : Nat) (acc : Array UInt64), n ≤ fuel →
    IxCC.NatRep.toLimbsFuel fuel n acc = ofNatLoop n acc
  | 0, n, acc, h => by
    have h0 : n = 0 := by omega
    subst h0
    unfold ofNatLoop
    rfl
  | fuel + 1, n, acc, h => by
    unfold ofNatLoop
    rw [IxCC.NatRep.toLimbsFuel_succ]
    by_cases h0 : n = 0
    · rw [ite_eq_left h0, dite_eq_left h0]
    · rw [ite_eq_right h0, dite_eq_right h0]
      have hs : n / limbBase = n >>> 64 := (Nat.shiftRight_eq_div_pow n 64).symm
      exact (toLimbsFuel_eq_ofNatLoop fuel (n / limbBase) (acc.push (UInt64.ofNat n))
        (IxCC.NatRep.div_limbBase_le h0 h)).trans
        (congrArg (fun m => ofNatLoop m (acc.push (UInt64.ofNat n))) hs)

/-- **`toLimbs` is the library's `ofNat`.** -/
theorem toLimbs_eq_ofNat (n : Nat) : toLimbs n = ofNat n :=
  toLimbsFuel_eq_ofNatLoop n n #[] (Nat.le_refl n)

/-- `toLimbs` returns the library's normal form. -/
theorem wf_toLimbs (n : Nat) : WF (toLimbs n) := by
  rw [toLimbs_eq_ofNat]
  exact wf_ofNat n

/-- The library reads `toLimbs n` as `n`. -/
theorem toNat_toLimbs (n : Nat) : toNat (toLimbs n) = n := by
  rw [toLimbs_eq_ofNat]
  exact toNat_ofNat n

/-- On the library's normal form, `toLimbs` inverts `toNat`. -/
theorem toLimbs_toNat {a : Array UInt64} (ha : WF a) : toLimbs (toNat a) = a :=
  toNat_inj (wf_toLimbs _) ha (toNat_toLimbs _)

/-- `toLimbs ∘ ofLimbs` is the library's `normalize`. -/
theorem toLimbs_ofLimbs_eq_normalize (a : Array UInt64) : toLimbs (ofLimbs a) = normalize a :=
  toNat_inj (wf_toLimbs _) (wf_normalize a)
    (by rw [toNat_toLimbs, ofLimbs_eq_toNat, toNat_normalize])

/-- The library's normal form is the specification's canonical form. -/
theorem canonical_of_wf {a : Array UInt64} (ha : WF a) :
    CanonicalLimbs (a.toList.map UInt64.toNat) := by
  have h := IxCC.NatRep.canonical_toLimbs (toNat a)
  rw [toLimbs_toNat ha] at h
  exact h

/-- ... and conversely. -/
theorem wf_of_canonical {a : Array UInt64} (h : CanonicalLimbs (a.toList.map UInt64.toNat)) :
    WF a := by
  have hw := wf_toLimbs (ofLimbs a)
  rw [IxCC.NatRep.toLimbs_ofLimbs a h] at hw
  exact hw

theorem wf_iff_canonical (a : Array UInt64) :
    WF a ↔ CanonicalLimbs (a.toList.map UInt64.toNat) :=
  Iff.intro canonical_of_wf wf_of_canonical

/-! ## One equation per entry -/

theorem add_eq (a b : Nat) : add a b = a + b := by
  unfold add
  rw [ofLimbs_eq_toNat, toNat_add, toNat_toLimbs, toNat_toLimbs]

theorem sub_eq (a b : Nat) : sub a b = a - b := by
  unfold sub
  rw [ofLimbs_eq_toNat, toNat_subRaw, toNat_toLimbs, toNat_toLimbs]

theorem pred_eq (a : Nat) : pred a = a - 1 := by
  unfold pred
  rw [ofLimbs_eq_toNat, toNat_pred (wf_toLimbs a), toNat_toLimbs]

theorem mul_eq (a b : Nat) : mul a b = a * b := by
  unfold mul
  rw [ofLimbs_eq_toNat, toNat_mul, toNat_toLimbs, toNat_toLimbs]

theorem div_eq (a b : Nat) : div a b = a / b := by
  unfold div
  rw [ofLimbs_eq_toNat, toNat_div, toNat_toLimbs, toNat_toLimbs]

theorem mod_eq (a b : Nat) : mod a b = a % b := by
  unfold mod
  rw [ofLimbs_eq_toNat, toNat_mod, toNat_toLimbs, toNat_toLimbs]

theorem pow_eq (a e : Nat) : pow a e = a ^ e := by
  unfold pow
  rw [ofLimbs_eq_toNat, toNat_pow, toNat_toLimbs]

theorem gcd_eq (a b : Nat) : gcd a b = Nat.gcd a b := by
  unfold gcd
  rw [ofLimbs_eq_toNat, toNat_gcd, toNat_toLimbs, toNat_toLimbs]

theorem cmp_eq (a b : Nat) : cmp a b = compare a b := by
  unfold cmp
  rw [cmp_spec (wf_toLimbs a) (wf_toLimbs b), toNat_toLimbs, toNat_toLimbs]

theorem beq_eq (a b : Nat) : beq a b = (a == b) := by
  unfold beq
  rw [beq_spec (wf_toLimbs a) (wf_toLimbs b), toNat_toLimbs, toNat_toLimbs]

theorem ble_eq (a b : Nat) : ble a b = decide (a ≤ b) := by
  unfold ble
  rw [ble_spec (wf_toLimbs a) (wf_toLimbs b)]
  simp only [toNat_toLimbs]

theorem blt_eq (a b : Nat) : blt a b = decide (a < b) := by
  unfold blt
  rw [blt_spec (wf_toLimbs a) (wf_toLimbs b)]
  simp only [toNat_toLimbs]

theorem land_eq (a b : Nat) : land a b = a &&& b := by
  unfold land
  rw [ofLimbs_eq_toNat, toNat_land, toNat_toLimbs, toNat_toLimbs]

theorem lor_eq (a b : Nat) : lor a b = a ||| b := by
  unfold lor
  rw [ofLimbs_eq_toNat, toNat_lor, toNat_toLimbs, toNat_toLimbs]

theorem xor_eq (a b : Nat) : xor a b = a ^^^ b := by
  unfold xor
  rw [ofLimbs_eq_toNat, toNat_xor, toNat_toLimbs, toNat_toLimbs]

theorem shiftLeft_eq (a s : Nat) : shiftLeft a s = a <<< s := by
  unfold shiftLeft
  rw [ofLimbs_eq_toNat, toNat_shiftLeft, toNat_toLimbs]

theorem shiftLeft_eq_mul (a s : Nat) : shiftLeft a s = a * 2 ^ s := by
  rw [shiftLeft_eq, Nat.shiftLeft_eq]

theorem shiftRight_eq (a s : Nat) : shiftRight a s = a >>> s := by
  unfold shiftRight
  rw [ofLimbs_eq_toNat, toNat_shiftRight, toNat_toLimbs]

theorem shiftRight_eq_div (a s : Nat) : shiftRight a s = a / 2 ^ s := by
  rw [shiftRight_eq, Nat.shiftRight_eq_div_pow]

theorem log2_eq (a : Nat) : log2 a = Nat.log2 a := by
  unfold log2
  rw [log2_spec (wf_toLimbs a), toNat_toLimbs]

/-- Parsing the digits of a natural gives the natural back. -/
theorem ofDecimal_toDecimal (a : Nat) : ofDecimal (toDecimal a) = some a := by
  unfold ofDecimal toDecimal
  rw [IxCC.BigNat.ofDecimal_toDecimal (wf_toLimbs a), Option.map_some,
    IxCC.NatRep.ofLimbs_toLimbs]

/-! ## The equations, collected -/

/-- **The contract of the `Nat` library, about its Lean functions**: every entry is the `Nat`
operation it is the slow path of, on all arguments. No limb, cell or tag occurs in it. -/
structure Spec : Prop where
  add : ∀ a b : Nat, NatEntry.add a b = a + b
  sub : ∀ a b : Nat, NatEntry.sub a b = a - b
  pred : ∀ a : Nat, NatEntry.pred a = a - 1
  mul : ∀ a b : Nat, NatEntry.mul a b = a * b
  div : ∀ a b : Nat, NatEntry.div a b = a / b
  mod : ∀ a b : Nat, NatEntry.mod a b = a % b
  pow : ∀ a e : Nat, NatEntry.pow a e = a ^ e
  gcd : ∀ a b : Nat, NatEntry.gcd a b = Nat.gcd a b
  cmp : ∀ a b : Nat, NatEntry.cmp a b = compare a b
  beq : ∀ a b : Nat, NatEntry.beq a b = (a == b)
  ble : ∀ a b : Nat, NatEntry.ble a b = decide (a ≤ b)
  blt : ∀ a b : Nat, NatEntry.blt a b = decide (a < b)
  land : ∀ a b : Nat, NatEntry.land a b = a &&& b
  lor : ∀ a b : Nat, NatEntry.lor a b = a ||| b
  xor : ∀ a b : Nat, NatEntry.xor a b = a ^^^ b
  shiftLeft : ∀ a s : Nat, NatEntry.shiftLeft a s = a <<< s
  shiftRight : ∀ a s : Nat, NatEntry.shiftRight a s = a >>> s
  log2 : ∀ a : Nat, NatEntry.log2 a = Nat.log2 a
  decimal : ∀ a : Nat, NatEntry.ofDecimal (NatEntry.toDecimal a) = some a

/-- **The contract holds.** -/
theorem spec : Spec where
  add := add_eq
  sub := sub_eq
  pred := pred_eq
  mul := mul_eq
  div := div_eq
  mod := mod_eq
  pow := pow_eq
  gcd := gcd_eq
  cmp := cmp_eq
  beq := beq_eq
  ble := ble_eq
  blt := blt_eq
  land := land_eq
  lor := lor_eq
  xor := xor_eq
  shiftLeft := shiftLeft_eq
  shiftRight := shiftRight_eq
  log2 := log2_eq
  decimal := ofDecimal_toDecimal

end IxCC.BigNat.NatEntry
