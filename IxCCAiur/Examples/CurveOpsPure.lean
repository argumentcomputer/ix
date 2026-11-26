import Ix.Compile.CircuitContract

/-! # Single-Source Curve-Parameterized Non-Native `Fq` & `G1` Affine Ops (`CurveOpsPure`)

Phase 2/3 M2 milestone: a single, 100% Mathlib-free, total Lean 4 specification of
non-native prime-field (`Fq`) arithmetic, Tier-2 kernel-verified `guess` operations
(`checked def ... complete by` and `@[circuit_guess]`), multi-limb packing
(`Limb4` 4×80b / 4×64b for BN254, `Limb5` 5×80b & `Limb6` 6×64b for BLS12-381),
and affine short-Weierstrass `G1` point doubling, addition, and scalar
multiplication (`y² = x³ + b (mod p)`), parameterized cleanly over `CurveParams`
across:

1. **BN254 `G1`** over `Fp` (254-bit prime, `b = 3`, generator `(1, 2)`, order `Fr`),
2. **BLS12-381 `G1`** over `Fp` (381-bit prime, `b = 4`, standard IETF/Zcash `G1`
   generator `(x_G1, y_G1)`, order `Fr`),
3. **Small toy prime curve** (`p = 101`, `b = 3`, generator `(1, 2)`, prime-order
   17 subgroup) and **Fermat prime `F₄`** (`p = 65537`, `b = 3`, generator `(1, 2)`),
   allowing the exact same generic `g1AddAffine` / `fqMulMod` / `fqInvMod` code
   to compile and prove live end-to-end through `ixcc-aiur --typed --inline-fuse --schedule`
   and `ixcc_prove --controls`.

## Design Notes

* **Zero forbidden constructs**: pure total Lean 4 only — every recursive function
  uses structural recursion (`termination_by structural`), with zero `sorry`,
  `admit`, `axiom`, `partial`, `unsafe`, `native_decide`, `bv_decide`,
  `@[extern]`, or `@[implemented_by]`.
* **Zero Ixon content-address mutation**: every `@[circuit_inline]`,
  `@[circuit_noinline]`, `@[circuit_budget]`, `@[circuit_guess]`, and
  `checked def` annotation registers sidecar metadata under `open scoped Ix.Circuit`
  without modifying any elaborated `ConstantInfo`.
* **Kernel-verified Tier-2 `guess` operations** (accepted by `IxCC.Src.Table.Guess.checkGuess`,
  `Table.ofCert`, and `CompileClaim.checkSeedClosure` / `Ix.Kernel.Admission.checkBytes`):
  1. `fqMulMod` (`checked def ... complete by`): canonical `(a * b) % p` with
     quotient-remainder check (`r < p ∧ q * p + r == a * b`).
  2. `fqMulDivMod` (`@[circuit_guess]`): 100% division-free `(q, r)` witness
     (`r < p ∧ q * p + r == a * b`) with uniqueness and completeness proofs.
  3. `fqInvMod` (`checked def`): general curve-parameterized modular inverse over
     any prime `p < 2^384` (covering BN254 `Fp`, BLS12-381 `Fp`, `65537`, and `101`)
     computed via pure-`Nat` structural-fuel unsigned extended Euclid (`egcdStep`),
     with algebraic checker `r < p ∧ (a * r) % p == 1` and unconditional
     uniqueness proof (`fqInvMod.check_unique`) plus coprime completeness theorem.
  4. `fqInvModToy` (`checked def ... complete by`): concrete prime `p = 101`
     modular inverse with pure algebraic checker `r < 101 ∧ (a * r) % 101 == 1`
     and both uniqueness and completeness theorems.
  5. `fqDivModToy` (`checked def ... complete by`): concrete prime `p = 101`
     field division / affine slope witness `den * λ ≡ num (mod 101)` with both
     uniqueness and completeness theorems.
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace CurveOpsPure

/-! ## Monomorphic ADTs (`ShapeInfer`-Unboxed) -/

/-- Monomorphic quotient-remainder witness pair for division-free `fqMulDivMod`. -/
structure QuotRem where
  q : Nat
  r : Nat
  deriving BEq, DecidableEq, Repr

/-- Single-source parameters for a short-Weierstrass curve `y² = x³ + b (mod p)`
with base-point generator `(gx, gy)`. -/
structure CurveParams where
  p : Nat
  b : Nat
  gx : Nat
  gy : Nat
  deriving BEq, DecidableEq, Repr

/-- Canonical affine `G1` point over `Fp`:
* Infinity (`O`) has the unique encoding `{ x := 0, y := 0, isInf := 1 }`.
* Finite points have `isInf = 0` and canonical coordinates `x < p`, `y < p`. -/
structure G1Point where
  x : Nat
  y : Nat
  isInf : Nat
  deriving BEq, DecidableEq, Repr

/-- 4-limb packed field element (BN254 `Fp`: `4×80b` radix `2^80` or `4×64b` radix `2^64`). -/
structure Limb4 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  deriving BEq, DecidableEq, Repr

/-- 5-limb packed field element (BLS12-381 `Fp`: `5×80b` radix `2^80`, `5 * 80 = 400 > 381`). -/
structure Limb5 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  deriving BEq, DecidableEq, Repr

/-- 6-limb packed field element (BLS12-381 `Fp`: `6×64b` radix `2^64`, `6 * 64 = 384 > 381`). -/
structure Limb6 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  l5 : Nat
  deriving BEq, DecidableEq, Repr

/-! ## Single-Source Curve Constants (100% Pure Lean `Nat`, Zero Mathlib) -/

/-- Upper bound `2^384 = 2^192 * 2^192` covering BN254 `Fp` (254-bit), BLS12-381 `Fp`
(381-bit), and all smaller curve primes. Written as `2^192 * 2^192` to stay below
Lean's default `exponentiation.threshold` (256) without extra options. Referenced only
by specifications and Tier-2 checkers, never by the toy-prime STARK entrypoint. -/
def maxFieldModulus : Nat := (2 ^ 192) * (2 ^ 192)

/-- Small toy prime `p = 101` (`(p - 1)² = 10000 < 2^56`).
On `y² = x³ + 3 (mod 101)`, the generator `(1, 2)` generates a prime-order `17` subgroup. -/
@[circuit_inline]
def toyPrime : Nat := 101

/-- Subgroup order of `(1, 2)` on `y² = x³ + 3 (mod 101)`. -/
def toyOrder : Nat := 17

/-- Toy prime curve parameters (`p = 101`, `b = 3`, `G = (1, 2)`). -/
@[circuit_inline]
def toyCurve : CurveParams :=
  { p := toyPrime, b := 3, gx := 1, gy := 2 }

/-- Fermat prime `F₄ = 65537 = 2^16 + 1` (`(p - 1)² = 2^32 < 2^56`). -/
def f4Prime : Nat := 65537

/-- Curve `y² = x³ + 3 (mod 65537)` with generator `(1, 2)`. -/
def f4Curve : CurveParams :=
  { p := f4Prime, b := 3, gx := 1, gy := 2 }

/-- BN254 base field prime `Fp` (254 bits). -/
def bn254Fp : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- BN254 scalar field prime `Fr` (order of `G1`). -/
def bn254Fr : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 `G1` curve parameters (`y² = x³ + 3 (mod bn254Fp)`, generator `(1, 2)`). -/
def bn254Curve : CurveParams :=
  { p := bn254Fp, b := 3, gx := 1, gy := 2 }

/-- BLS12-381 base field prime `Fp` (381 bits). -/
def bls12381Fp : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- BLS12-381 scalar field prime `Fr` (order of `G1`). -/
def bls12381Fr : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- Standard IETF/Zcash/EIP-2537 BLS12-381 `G1` generator `x`-coordinate. -/
def bls12381G1X : Nat :=
  3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507

/-- Standard IETF/Zcash/EIP-2537 BLS12-381 `G1` generator `y`-coordinate. -/
def bls12381G1Y : Nat :=
  1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569

/-- BLS12-381 `G1` curve parameters (`y² = x³ + 4 (mod bls12381Fp)`). -/
def bls12381Curve : CurveParams :=
  { p := bls12381Fp, b := 4, gx := bls12381G1X, gy := bls12381G1Y }

/-! ## Non-Native `Fq` Arithmetic & Kernel-Verified Tier-2 `guess` Operations -/

/-- Branchless field addition `(a + b) mod p` (0 depth columns in recursive callers). -/
@[circuit_noinline]
def fqAddMod (p a b : Nat) : Nat :=
  (a + b) % p

/-- Branchless field subtraction `(a - b) mod p` for canonical `b ≤ p`. -/
@[circuit_noinline]
def fqSubMod (p a b : Nat) : Nat :=
  (a + p - b) % p

/-- Field negation `(-a) mod p` for canonical `a < p`. -/
@[circuit_inline]
def fqNegMod (p a : Nat) : Nat :=
  if a == 0 then 0 else p - a

/-- **Tier-2 `guess` #1 (`checked def ... complete by`)**: modular multiplication
`(a * b) % p`, verified by canonical remainder bound `r < p` and Euclidean product
equation `((a * b) / p) * p + r == a * b`. Non-circular (checker never references
`fqMulMod`) with kernel-checked uniqueness and completeness for all `p a b : Nat`. -/
@[circuit_noinline]
checked def fqMulMod (p a b : Nat) : Nat :=
  hint (a * b) % p
  where check fun r =>
    if p == 0 then r == a * b
    else decide (r < p) && (((a * b) / p) * p + r == a * b)
  by
    intro res hr
    unfold fqMulMod.check at hr
    unfold fqMulMod
    by_cases hp : p = 0
    · subst hp
      simp at hr ⊢
      exact hr
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB] at hr
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hr
      obtain ⟨_, heq⟩ := hr
      have hdm : p * ((a * b) / p) + (a * b) % p = a * b := Nat.div_add_mod (a * b) p
      rw [Nat.mul_comm p ((a * b) / p)] at hdm
      omega
  complete by
    unfold fqMulMod.check fqMulMod
    by_cases hp : p = 0
    · subst hp
      simp
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB]
      have hpPos : 0 < p := Nat.pos_of_ne_zero hp
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      refine ⟨Nat.mod_lt (a * b) hpPos, ?_⟩
      rw [Nat.mul_comm, Nat.div_add_mod]

/-- **Tier-2 `guess` #2 (`@[circuit_guess]`)**: modular multiplication returning
both quotient and remainder `{ q := (a * b) / p, r := (a * b) % p }`. Its checker
`fqMulDivModCheck` is 100% division-free (uses only `<`, `*`, `+`, `==`). -/
@[circuit_noinline]
def fqMulDivMod (p a b : Nat) : QuotRem :=
  { q := (a * b) / p, r := (a * b) % p }

/-- 100% division-free checker for `fqMulDivMod`: verifies `qr.r < p` and
`qr.q * p + qr.r == a * b` (with exact degenerate handling for `p = 0`). -/
def fqMulDivModCheck (p a b : Nat) (qr : QuotRem) : Bool :=
  if p == 0 then
    (qr.q == 0) && (qr.r == a * b)
  else
    decide (qr.r < p) && (qr.q * p + qr.r == a * b)

/-- Uniqueness/soundness theorem for `fqMulDivMod` across all `p a b : Nat`. -/
theorem fqMulDivMod_sound (p a b : Nat) (qr : QuotRem)
    (h : fqMulDivModCheck p a b qr = true) :
    qr = fqMulDivMod p a b := by
  cases qr with
  | mk q r =>
    unfold fqMulDivModCheck at h
    unfold fqMulDivMod
    by_cases hp : p = 0
    · subst hp
      simp at h ⊢
      exact h
    · have hpB : (p == 0) = false := beq_false_of_ne hp
      rw [hpB] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at h
      obtain ⟨hrp, hmul⟩ := h
      have hpPos : 0 < p := Nat.pos_of_ne_zero hp
      have hq : (a * b) / p = q := by
        rw [← hmul, Nat.mul_comm q p, Nat.mul_add_div hpPos, Nat.div_eq_of_lt hrp, Nat.add_zero]
      have hr : (a * b) % p = r := by
        rw [← hmul, Nat.mul_comm q p, Nat.mul_add_mod, Nat.mod_eq_of_lt hrp]
      rw [hq, hr]

/-- Completeness theorem for `fqMulDivMod` across all `p a b : Nat`. -/
theorem fqMulDivMod_complete (p a b : Nat) :
    fqMulDivModCheck p a b (fqMulDivMod p a b) = true := by
  unfold fqMulDivModCheck fqMulDivMod
  by_cases hp : p = 0
  · subst hp
    simp
  · have hpB : (p == 0) = false := beq_false_of_ne hp
    rw [hpB]
    have hpPos : 0 < p := Nat.pos_of_ne_zero hp
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨Nat.mod_lt (a * b) hpPos, ?_⟩
    rw [Nat.mul_comm, Nat.div_add_mod]

attribute [circuit_guess fqMulDivModCheck fqMulDivMod_sound fqMulDivMod_complete] fqMulDivMod

/-! ### Pure-`Nat` Structural Extended Euclid (`egcdStep`) & Proof of `fqInvMod` -/

/-- Pure-`Nat` structural-fuel unsigned extended Euclidean worker modulo `p`.
Maintains the Bézout invariants `a * t0 ≡ r0 (mod p)` and `a * t1 ≡ r1 (mod p)`
with `t0, t1 < p` and zero signed integers (`Int`). Early-exits as soon as
`r1 = 0` (at most 8 iterations for `p = 101`, guaranteed termination within
`2 * k + 1` steps for any `p < 2^k`, including BN254 `Fp` and BLS12-381 `Fp`). -/
@[circuit_noinline]
def egcdStep (p : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, t0, _ => t0
  | fuel + 1, r0, r1, t0, t1 =>
    match r1 with
    | 0 => if r0 == 1 then t0 else 0
    | r1' + 1 =>
      let d := r1' + 1
      let q := r0 / d
      let r2 := r0 % d
      let qt1 := fqMulMod p q t1
      let t2 := fqSubMod p t0 qt1
      egcdStep p fuel d r2 t1 t2
termination_by structural fuel => fuel

/-! #### Pure-Lean Modular Arithmetic Lemmas (Zero Mathlib) -/

private def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

private theorem pow2_eq_pow : ∀ k, pow2 k = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [pow2, pow2_eq_pow k, Nat.pow_succ, Nat.mul_comm]

private theorem pow2_add (m n : Nat) : pow2 (m + n) = pow2 m * pow2 n := by
  induction m with
  | zero => simp [pow2]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [pow2, ih, Nat.mul_assoc]

private theorem maxFieldModulus_eq_pow2 : maxFieldModulus = pow2 384 := by
  unfold maxFieldModulus
  rw [← pow2_eq_pow 192, ← pow2_add 192 192]

private theorem mul_mod_left_eq (a b p : Nat) : ((a % p) * b) % p = (a * b) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem mul_mod_right_eq (a b p : Nat) : (a * (b % p)) % p = (a * b) % p := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem mod_inv_unique (p a r1 r2 : Nat)
    (hr1 : r1 < p) (hr2 : r2 < p)
    (heq1 : (a * r1) % p = 1) (heq2 : (a * r2) % p = 1) :
    r1 = r2 := by
  have h1 : (r1 * (a * r2)) % p = r1 := by
    rw [Nat.mul_mod, heq2, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hr1]
  have h2 : (r1 * (a * r2)) % p = r2 := by
    have hassoc : r1 * (a * r2) = (a * r1) * r2 := by
      rw [← Nat.mul_assoc, Nat.mul_comm r1 a]
    rw [hassoc, Nat.mul_mod, heq1, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr2]
  exact h1.symm.trans h2

private theorem two_mul_mod_lt (r0 r1 : Nat) (hr1 : 0 < r1) (hle : r1 ≤ r0) :
    2 * (r0 % r1) < r0 := by
  have hdm : r1 * (r0 / r1) + r0 % r1 = r0 := Nat.div_add_mod r0 r1
  have hmod : r0 % r1 < r1 := Nat.mod_lt r0 hr1
  have hq : 1 ≤ r0 / r1 := Nat.div_pos hle hr1
  by_cases hq1 : r0 / r1 = 1
  · rw [hq1, Nat.mul_one] at hdm
    omega
  · have hq2 : 2 ≤ r0 / r1 := by omega
    have hmul : r1 * 2 ≤ r1 * (r0 / r1) := Nat.mul_le_mul_left r1 hq2
    omega

private theorem add_mod_right_cancel (p x y z : Nat) (hp : 0 < p)
    (hx : x < p) (hy : y < p) (h : (x + z) % p = (y + z) % p) :
    x = y := by
  have hz : z % p < p := Nat.mod_lt z hp
  have hx' : (x + z) % p = (x + z % p) % p := by
    rw [Nat.add_mod x z p, Nat.mod_eq_of_lt hx]
  have hy' : (y + z) % p = (y + z % p) % p := by
    rw [Nat.add_mod y z p, Nat.mod_eq_of_lt hy]
  rw [hx', hy'] at h
  generalize z % p = z' at hz h
  by_cases h1 : x + z' < p
  · rw [Nat.mod_eq_of_lt h1] at h
    by_cases h2 : y + z' < p
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · have hsub : (y + z') % p = y + z' - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at h
      omega
  · have hsub1 : (x + z') % p = x + z' - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub1] at h
    by_cases h2 : y + z' < p
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · have hsub2 : (y + z') % p = y + z' - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub2] at h
      omega

private theorem bezout_step (p a r0 r1 t0 t1 : Nat)
    (hp : 0 < p)
    (ht0 : (a * t0) % p = r0 % p) (ht1 : (a * t1) % p = r1 % p) :
    let q := r0 / r1
    let r2 := r0 % r1
    let qt1 := fqMulMod p q t1
    let t2 := fqSubMod p t0 qt1
    t2 < p ∧ (a * t2) % p = r2 % p := by
  intro q r2 qt1 t2
  have hqt1Lt : qt1 < p := Nat.mod_lt (q * t1) hp
  have ht2Lt : t2 < p := Nat.mod_lt (t0 + p - qt1) hp
  refine ⟨ht2Lt, ?_⟩
  have hsumMod : (t2 + qt1) % p = t0 % p := by
    have h1 : (t2 + qt1) % p = ((t0 + p - qt1) + qt1) % p := by
      rw [Nat.add_mod, show t2 % p = (t0 + p - qt1) % p from Nat.mod_mod _ _, ← Nat.add_mod]
    have h2 : (t0 + p - qt1) + qt1 = t0 + p := by omega
    rw [h1, h2, Nat.add_mod_right]
  have hmulSum : (a * t2 + a * qt1) % p = r0 % p := by
    rw [← Nat.mul_add, Nat.mul_mod, hsumMod, ← Nat.mul_mod, ht0]
  have haqt1 : (a * qt1) % p = (q * r1) % p := by
    calc
      (a * qt1) % p = (a * ((q * t1) % p)) % p := rfl
      _ = (a * (q * t1)) % p := mul_mod_right_eq a (q * t1) p
      _ = (q * (a * t1)) % p := by rw [Nat.mul_left_comm]
      _ = (q * ((a * t1) % p)) % p := (mul_mod_right_eq q (a * t1) p).symm
      _ = (q * (r1 % p)) % p := by rw [ht1]
      _ = (q * r1) % p := mul_mod_right_eq q r1 p
  have hr0Eq : r2 + q * r1 = r0 := by
    have hdm : r1 * q + r2 = r0 := Nat.div_add_mod r0 r1
    rw [Nat.mul_comm r1 q, Nat.add_comm] at hdm
    exact hdm
  have hEq : ((a * t2) % p + (q * r1) % p) % p = (r2 % p + (q * r1) % p) % p := by
    calc
      ((a * t2) % p + (q * r1) % p) % p
        = ((a * t2) % p + (a * qt1) % p) % p := by rw [haqt1]
      _ = (a * t2 + a * qt1) % p := by rw [← Nat.add_mod]
      _ = r0 % p := hmulSum
      _ = (r2 + q * r1) % p := by rw [hr0Eq]
      _ = (r2 % p + (q * r1) % p) % p := Nat.add_mod r2 (q * r1) p
  exact add_mod_right_cancel p ((a * t2) % p) (r2 % p) ((q * r1) % p) hp
    (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hEq

private theorem gcd_step_eq (r0 r1 : Nat) : Nat.gcd r1 (r0 % r1) = Nat.gcd r0 r1 := by
  rw [Nat.gcd_comm r1 (r0 % r1), ← Nat.gcd_rec r1 r0, Nat.gcd_comm]

private theorem egcdStep_spec (p a : Nat) (hp : 2 ≤ p) :
    ∀ (k fuel r0 r1 t0 t1 : Nat),
      2 * k + 1 ≤ fuel →
      r0 < pow2 k →
      r1 ≤ r0 →
      t0 < p →
      t1 < p →
      (a * t0) % p = r0 % p →
      (a * t1) % p = r1 % p →
      Nat.gcd r0 r1 = 1 →
      let out := egcdStep p fuel r0 r1 t0 t1
      out < p ∧ (a * out) % p = 1 := by
  intro k
  induction k with
  | zero =>
    intro fuel r0 r1 t0 t1 _ hr0 hle _ _ _ _ hgcd
    have hr0z : r0 = 0 := by
      have : pow2 0 = 1 := rfl
      omega
    have hr1z : r1 = 0 := by omega
    subst hr0z; subst hr1z
    simp at hgcd
  | succ k ih =>
    intro fuel r0 r1 t0 t1 hfuel hr0 hle ht0Lt ht1Lt ht0 ht1 hgcd
    have hpPos : 0 < p := by omega
    obtain ⟨fuel1, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    cases r1 with
    | zero =>
      simp only [egcdStep]
      have hr0One : r0 = 1 := by simpa using hgcd
      subst hr0One
      simp only [beq_self_eq_true, ↓reduceIte]
      exact ⟨ht0Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht0⟩
    | succ r1' =>
      let d := r1' + 1
      have hdPos : 0 < d := Nat.succ_pos r1'
      have hbz1 := bezout_step p a r0 d t0 t1 hpPos ht0 ht1
      let q1 := r0 / d
      let r2 := r0 % d
      let t2 := fqSubMod p t0 (fqMulMod p q1 t1)
      have ht2Lt : t2 < p := hbz1.1
      have ht2Eq : (a * t2) % p = r2 % p := hbz1.2
      have hgcd1 : Nat.gcd d r2 = 1 := by
        rw [gcd_step_eq r0 d]
        exact hgcd
      have h2r2 : 2 * r2 < r0 := two_mul_mod_lt r0 d hdPos hle
      have hr2Pow : r2 < pow2 k := by
        have hpow : pow2 (k + 1) = 2 * pow2 k := rfl
        omega
      obtain ⟨fuel2, rfl⟩ : ∃ m, fuel1 = m + 1 := ⟨fuel1 - 1, by omega⟩
      have hstep1 : egcdStep p (fuel2 + 1 + 1) r0 d t0 t1 = egcdStep p (fuel2 + 1) d r2 t1 t2 := rfl
      show let out := egcdStep p (fuel2 + 1 + 1) r0 d t0 t1; out < p ∧ (a * out) % p = 1
      rw [hstep1]
      cases hr2Case : r2 with
      | zero =>
        simp only [egcdStep]
        rw [hr2Case] at hgcd1
        have hdOne : d = 1 := by simpa using hgcd1
        have ht1d : (a * t1) % p = d % p := ht1
        rw [hdOne] at ht1d ⊢
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ⟨ht1Lt, by simpa [Nat.mod_eq_of_lt (show 1 < p by omega)] using ht1d⟩
      | succ r2' =>
        have hr2Pos : 0 < r2 := by omega
        have hbz2 := bezout_step p a d r2 t1 t2 hpPos ht1 ht2Eq
        let q2 := d / r2
        let r3 := d % r2
        let t3 := fqSubMod p t1 (fqMulMod p q2 t2)
        have hstep2 : egcdStep p (fuel2 + 1) d (r2' + 1) t1 t2 = egcdStep p fuel2 r2 r3 t2 t3 := by
          change egcdStep p fuel2 (r2' + 1) (d % (r2' + 1)) t2
            (fqSubMod p t1 (fqMulMod p (d / (r2' + 1)) t2)) =
            egcdStep p fuel2 r2 (d % r2) t2 (fqSubMod p t1 (fqMulMod p (d / r2) t2))
          rw [hr2Case]
        rw [hstep2]
        have hgcd2 : Nat.gcd r2 r3 = 1 := by
          rw [gcd_step_eq d r2]
          exact hgcd1
        have hr3Le : r3 ≤ r2 := Nat.le_of_lt (Nat.mod_lt d hr2Pos)
        exact ih fuel2 r2 r3 t2 t3 (by omega) hr2Pow hr3Le ht2Lt hbz2.1 ht2Eq hbz2.2 hgcd2

private theorem gcd_eq_one_of_mul_mod_eq_one (p a r : Nat) (h : (a * r) % p = 1) :
    Nat.gcd p a = 1 := by
  have hdvdP : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  have hdvdA : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
  have hdvdAR : Nat.gcd p a ∣ a * r := Nat.dvd_mul_right_of_dvd hdvdA r
  have hdvdPQ : Nat.gcd p a ∣ p * (a * r / p) := Nat.dvd_mul_right_of_dvd hdvdP (a * r / p)
  have hdm : p * (a * r / p) + 1 = a * r := by
    have := Nat.div_add_mod (a * r) p
    rw [h] at this
    exact this
  rw [← hdm] at hdvdAR
  have hdvd1 : Nat.gcd p a ∣ 1 := (Nat.dvd_add_right hdvdPQ).mp hdvdAR
  exact Nat.eq_one_of_dvd_one hdvd1

/-- **Tier-2 `guess` #3 (`checked def`)**: curve-parameterized modular inverse
over any prime `p < 2^384` (BN254 `Fp`, BLS12-381 `Fp`, `65537`, `101`).
The checker is pure algebraic (`r < p ∧ (a * r) % p == 1`) with zero circularity
and unconditional kernel-checked uniqueness (`fqInvMod.check_unique`) across all
`p a : Nat`. -/
@[circuit_noinline]
checked def fqInvMod (p a : Nat) : Nat :=
  hint if p < 2 then 0
       else if a % p == 0 then 0
       else egcdStep p 769 p (a % p) 0 1
  where check fun r =>
    if p < 2 then r == 0
    else if a % p == 0 then r == 0
    else decide (p < maxFieldModulus) && decide (r < p) && ((a * r) % p == 1)
  by
    intro res hr
    unfold fqInvMod.check at hr
    unfold fqInvMod
    by_cases hp2 : p < 2
    · simp [hp2] at hr ⊢
      exact hr
    · have hpGe : 2 ≤ p := by omega
      simp only [hp2, ↓reduceIte] at hr ⊢
      by_cases ha0 : a % p = 0
      · simp [ha0] at hr ⊢
        exact hr
      · have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
        rw [ha0B] at hr ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hr
        obtain ⟨⟨hpMax, hresLt⟩, hmulEq⟩ := hr
        have hpPow2 : p < pow2 384 := by rwa [maxFieldModulus_eq_pow2] at hpMax
        have hgcdPA : Nat.gcd p a = 1 := gcd_eq_one_of_mul_mod_eq_one p a res hmulEq
        have hgcdMod : Nat.gcd p (a % p) = 1 := by
          rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]
          exact hgcdPA
        have hpPos : 0 < p := by omega
        have hspec := egcdStep_spec p a hpGe 384 769 p (a % p) 0 1
          (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
          hpPos (by omega)
          (by simp)
          (by simp [Nat.mul_one])
          hgcdMod
        exact mod_inv_unique p a res _ hresLt hspec.1 hmulEq hspec.2

/-- Completeness of `fqInvMod` for every coprime input `(p, a)` with `2 ≤ p < 2^384`
(hence for all non-zero elements of BN254 `Fp`, BLS12-381 `Fp`, `65537`, and `101`). -/
theorem fqInvMod_complete_of_coprime (p a : Nat)
    (hpGe : 2 ≤ p) (hpMax : p < maxFieldModulus) (hcop : Nat.gcd p a = 1) :
    fqInvMod.check p a (fqInvMod p a) = true := by
  unfold fqInvMod.check fqInvMod
  have hp2 : ¬ (p < 2) := by omega
  simp only [hp2, ↓reduceIte]
  by_cases ha0 : a % p = 0
  · simp [ha0]
  · have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
    rw [ha0B]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hpPow2 : p < pow2 384 := by rwa [maxFieldModulus_eq_pow2] at hpMax
    have hgcdMod : Nat.gcd p (a % p) = 1 := by
      rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]
      exact hcop
    have hpPos : 0 < p := by omega
    have hspec := egcdStep_spec p a hpGe 384 769 p (a % p) 0 1
      (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
      hpPos (by omega)
      (by simp)
      (by simp [Nat.mul_one])
      hgcdMod
    exact ⟨⟨hpMax, hspec.1⟩, hspec.2⟩

/-! ### Concrete Prime `p = 101` Tier-2 `guess` Operations (`complete by` Included) -/

/-- Pure linear-arithmetic primality lemma for `toyPrime = 101` (zero `WellFounded`
reduction in `Ix.Kernel.Admission.checkBytes`). -/
private theorem dvd_101_iff (d : Nat) (hd : d ∣ 101) : d = 1 ∨ d = 101 := by
  rcases hd with ⟨q, hq⟩
  by_cases hd10 : d ≤ 10
  · rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | d <;> omega
  · by_cases hq10 : q ≤ 10
    · rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q <;> omega
    · have hge : 11 * 11 ≤ d * q := Nat.mul_le_mul (by omega) (by omega)
      omega

private theorem gcd_101_eq_one (a : Nat) (ha : a % toyPrime ≠ 0) : Nat.gcd toyPrime a = 1 := by
  have hdvd : Nat.gcd toyPrime a ∣ 101 := Nat.gcd_dvd_left 101 a
  rcases dvd_101_iff (Nat.gcd toyPrime a) hdvd with h1 | h101
  · exact h1
  · have hdvdA : 101 ∣ a := by
      have := Nat.gcd_dvd_right toyPrime a
      rw [h101] at this
      exact this
    have hmod : a % 101 = 0 := Nat.mod_eq_zero_of_dvd hdvdA
    exact False.elim (ha hmod)

private theorem toyPrime_lt_maxFieldModulus : toyPrime < maxFieldModulus := by
  unfold toyPrime maxFieldModulus
  have h1 : 101 < 2 ^ 192 :=
    Nat.lt_of_lt_of_le (by decide : 101 < 2 ^ 7)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 7 ≤ 192))
  have h2 : 0 < 2 ^ 192 := Nat.pow_pos (by decide : 0 < 2)
  exact Nat.lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right (2 ^ 192) h2)

/-- **Tier-2 `guess` #4 (`checked def ... complete by`)**: concrete-prime modular
inverse over `toyPrime = 101` with pure algebraic checker
`if a % 101 == 0 then r == 0 else decide (r < 101) && ((a * r) % 101 == 1)` and
both kernel-checked uniqueness AND completeness theorems. -/
@[circuit_noinline]
checked def fqInvModToy (a : Nat) : Nat :=
  hint fqInvMod toyPrime a
  where check fun r =>
    if a % toyPrime == 0 then r == 0
    else decide (r < toyPrime) && ((a * r) % toyPrime == 1)
  by
    intro res hr
    unfold fqInvModToy.check at hr
    unfold fqInvModToy
    apply fqInvMod.check_unique toyPrime a res
    unfold fqInvMod.check
    have h2 : ¬ (toyPrime < 2) := by decide
    simp only [h2, ↓reduceIte]
    by_cases ha0 : a % toyPrime = 0
    · simp [ha0] at hr ⊢
      exact hr
    · have ha0B : (a % toyPrime == 0) = false := beq_false_of_ne ha0
      rw [ha0B] at hr ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hr ⊢
      exact ⟨⟨toyPrime_lt_maxFieldModulus, hr.1⟩, hr.2⟩
  complete by
    unfold fqInvModToy.check fqInvModToy
    have h2 : ¬ (toyPrime < 2) := by decide
    by_cases ha0 : a % toyPrime = 0
    · have ha0B : (a % toyPrime == 0) = true := beq_iff_eq.mpr ha0
      unfold fqInvMod
      simp only [h2, ha0B, ↓reduceIte, beq_self_eq_true]
    · have hcomp := fqInvMod_complete_of_coprime toyPrime a (by decide)
        toyPrime_lt_maxFieldModulus (gcd_101_eq_one a ha0)
      unfold fqInvMod.check at hcomp
      have ha0B : (a % toyPrime == 0) = false := beq_false_of_ne ha0
      simp only [h2, ha0B, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hcomp ⊢
      exact ⟨hcomp.1.2, hcomp.2⟩

/-- **Tier-2 `guess` #5 (`checked def ... complete by`)**: concrete-prime field
division / affine slope witness `λ = num / den (mod 101)`, verified directly by
the single multiplicative relation `den * λ ≡ num (mod 101)` (matching `G1` slope
constraints) with both kernel-checked uniqueness AND completeness theorems. -/
@[circuit_noinline]
checked def fqDivModToy (num den : Nat) : Nat :=
  hint if den % toyPrime == 0 then 0
       else fqMulMod toyPrime num (fqInvMod toyPrime den)
  where check fun r =>
    if den % toyPrime == 0 then r == 0
    else decide (r < toyPrime) && ((den * r) % toyPrime == num % toyPrime)
  by
    intro res hr
    unfold fqDivModToy.check at hr
    unfold fqDivModToy
    by_cases hd0 : den % toyPrime = 0
    · simp [hd0] at hr ⊢
      exact hr
    · have hd0B : (den % toyPrime == 0) = false := beq_false_of_ne hd0
      rw [hd0B] at hr ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hr
      obtain ⟨hresLt, hmulEq⟩ := hr
      have hinvComp := fqInvMod_complete_of_coprime toyPrime den (by decide)
        toyPrime_lt_maxFieldModulus (gcd_101_eq_one den hd0)
      unfold fqInvMod.check at hinvComp
      have h2 : ¬ (toyPrime < 2) := by decide
      simp only [h2, hd0B, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hinvComp
      have hinvEq : (den * fqInvMod toyPrime den) % toyPrime = 1 := hinvComp.2
      unfold fqMulMod
      calc
        res = res % toyPrime := (Nat.mod_eq_of_lt hresLt).symm
        _ = (res * 1) % toyPrime := by rw [Nat.mul_one]
        _ = (res * ((den * fqInvMod toyPrime den) % toyPrime)) % toyPrime := by rw [hinvEq]
        _ = (res * (den * fqInvMod toyPrime den)) % toyPrime :=
          mul_mod_right_eq res (den * fqInvMod toyPrime den) toyPrime
        _ = ((den * res) * fqInvMod toyPrime den) % toyPrime := by
          rw [← Nat.mul_assoc, Nat.mul_comm res den]
        _ = (((den * res) % toyPrime) * fqInvMod toyPrime den) % toyPrime :=
          (mul_mod_left_eq (den * res) (fqInvMod toyPrime den) toyPrime).symm
        _ = ((num % toyPrime) * fqInvMod toyPrime den) % toyPrime := by rw [hmulEq]
        _ = (num * fqInvMod toyPrime den) % toyPrime :=
          mul_mod_left_eq num (fqInvMod toyPrime den) toyPrime
  complete by
    unfold fqDivModToy.check fqDivModToy
    by_cases hd0 : den % toyPrime = 0
    · simp [hd0]
    · have hd0B : (den % toyPrime == 0) = false := beq_false_of_ne hd0
      rw [hd0B]
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      have hinvComp := fqInvMod_complete_of_coprime toyPrime den (by decide)
        toyPrime_lt_maxFieldModulus (gcd_101_eq_one den hd0)
      unfold fqInvMod.check at hinvComp
      have h2 : ¬ (toyPrime < 2) := by decide
      simp only [h2, hd0B, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hinvComp
      have hinvEq : (den * fqInvMod toyPrime den) % toyPrime = 1 := hinvComp.2
      unfold fqMulMod
      refine ⟨Nat.mod_lt _ (by decide), ?_⟩
      calc
        (den * ((num * fqInvMod toyPrime den) % toyPrime)) % toyPrime
          = (den * (num * fqInvMod toyPrime den)) % toyPrime :=
            mul_mod_right_eq den (num * fqInvMod toyPrime den) toyPrime
        _ = ((den * fqInvMod toyPrime den) * num) % toyPrime := by
            rw [Nat.mul_comm num (fqInvMod toyPrime den), ← Nat.mul_assoc]
        _ = (((den * fqInvMod toyPrime den) % toyPrime) * num) % toyPrime :=
            (mul_mod_left_eq (den * fqInvMod toyPrime den) num toyPrime).symm
        _ = (1 * num) % toyPrime := by rw [hinvEq]
        _ = num % toyPrime := by rw [Nat.one_mul]

/-! ## Single-Source Curve-Parameterized `G1` Affine Operations -/

/-- Canonical point at infinity `O = (0, 0, 1)`. -/
@[circuit_inline]
def g1Inf : G1Point :=
  { x := 0, y := 0, isInf := 1 }

/-- Curve generator `G = (c.gx, c.gy, 0)`. -/
@[circuit_inline]
def g1Gen (c : CurveParams) : G1Point :=
  { x := c.gx, y := c.gy, isInf := 0 }

/-- Canonical point equality on `G1Point`. -/
@[circuit_inline]
def g1Eq (P Q : G1Point) : Bool :=
  if P.isInf == Q.isInf then
    if P.x == Q.x then P.y == Q.y else false
  else false

/-- Short-Weierstrass curve membership check `y² ≡ x³ + b (mod p)` with canonical
coordinate bounds `x < p`, `y < p`, and unique infinity encoding `(0, 0, 1)`. -/
@[circuit_noinline]
def g1OnCurve (c : CurveParams) (P : G1Point) : Bool :=
  if P.isInf == 1 then
    if P.x == 0 then P.y == 0 else false
  else if P.isInf == 0 then
    if P.x < c.p then
      if P.y < c.p then
        let y2 := fqMulMod c.p P.y P.y
        let x2 := fqMulMod c.p P.x P.x
        let x3 := fqMulMod c.p x2 P.x
        let rhs := fqAddMod c.p x3 (c.b % c.p)
        y2 == rhs
      else false
    else false
  else false

/-- Affine negation `-P = (x, -y mod p)` with `-O = O`. -/
@[circuit_inline]
def g1Neg (c : CurveParams) (P : G1Point) : G1Point :=
  if P.isInf == 1 then g1Inf
  else { x := P.x, y := fqNegMod c.p P.y, isInf := 0 }

/-- Affine point doubling `2P` on `y² = x³ + b (mod p)`:
`λ = (3 x²) / (2 y) mod p`, `x₃ = λ² - 2 x mod p`, `y₃ = λ (x - x₃) - y mod p`. -/
@[circuit_noinline]
def g1DoubleAffine (c : CurveParams) (P : G1Point) : G1Point :=
  if P.isInf == 1 then g1Inf
  else if P.y == 0 then g1Inf
  else
    let x2 := fqMulMod c.p P.x P.x
    let num := fqAddMod c.p (fqAddMod c.p x2 x2) x2
    let den := fqAddMod c.p P.y P.y
    let invDen := fqInvMod c.p den
    let lam := fqMulMod c.p num invDen
    let lam2 := fqMulMod c.p lam lam
    let x3 := fqSubMod c.p (fqSubMod c.p lam2 P.x) P.x
    let dx := fqSubMod c.p P.x x3
    let y3 := fqSubMod c.p (fqMulMod c.p lam dx) P.y
    { x := x3, y := y3, isInf := 0 }

/-- Complete affine point addition `P + Q` on `y² = x³ + b (mod p)`, handling
infinity (`O + Q = Q`, `P + O = P`), doubling (`P = Q`), inverse cancellation
(`P = -Q ⇒ O`), and distinct affine chords (`λ = (y₂ - y₁) / (x₂ - x₁) mod p`). -/
@[circuit_noinline]
def g1AddAffine (c : CurveParams) (P Q : G1Point) : G1Point :=
  if P.isInf == 1 then Q
  else if Q.isInf == 1 then P
  else if P.x == Q.x then
    if P.y == Q.y then g1DoubleAffine c P
    else g1Inf
  else
    let num := fqSubMod c.p Q.y P.y
    let den := fqSubMod c.p Q.x P.x
    let invDen := fqInvMod c.p den
    let lam := fqMulMod c.p num invDen
    let lam2 := fqMulMod c.p lam lam
    let x3 := fqSubMod c.p (fqSubMod c.p lam2 P.x) Q.x
    let dx := fqSubMod c.p P.x x3
    let y3 := fqSubMod c.p (fqMulMod c.p lam dx) P.y
    { x := x3, y := y3, isInf := 0 }

/-- Conditional point addition helper avoiding join-point splitting inside `g1ScalarMulFuel`. -/
@[circuit_noinline]
def g1CondAdd (c : CurveParams) (bit : Nat) (acc cur : G1Point) : G1Point :=
  match bit with
  | 0 => acc
  | _ => g1AddAffine c acc cur

/-- Structural countdown double-and-add scalar multiplication `acc + k · cur`. -/
@[circuit_noinline]
def g1ScalarMulFuel (c : CurveParams) : Nat → Nat → G1Point → G1Point → G1Point
  | 0, _, _, acc => acc
  | fuel + 1, k, cur, acc =>
    match k with
    | 0 => acc
    | _ =>
      let nextAcc := g1CondAdd c (k % 2) acc cur
      let nextCur := g1DoubleAffine c cur
      g1ScalarMulFuel c fuel (k / 2) nextCur nextAcc
termination_by structural fuel => fuel

/-- Scalar multiplication `k · P` supporting up to 256-bit scalars (covering both
BN254 `Fr` and BLS12-381 `Fr`, with early exit on `k = 0`). -/
@[circuit_inline]
def g1ScalarMul (c : CurveParams) (k : Nat) (P : G1Point) : G1Point :=
  g1ScalarMulFuel c 256 k P g1Inf

/-! ## Limb-Packed Field Conversions (`4×80b`/`4×64b` for BN254, `5×80b`/`6×64b` for BLS12-381) -/

/-- Radix `2^80` matching `Aiur.Library.Field.BN254.Fq.radix`. -/
def radix80 : Nat := 2 ^ 80

/-- Radix `2^64` for 64-bit word limb layouts (`4×64b` BN254, `6×64b` BLS12-381). -/
def radix64 : Nat := 2 ^ 64

/-- Unpack a BN254 `Fp` element (`< 2^254 < 2^320`) into `4×80b` limbs. -/
def toLimb4 (x : Nat) : Limb4 :=
  let r := radix80
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let l3 := q2 / r
  { l0, l1, l2, l3 }

/-- Recompose a `4×80b` limb vector back into a `Nat`. -/
def ofLimb4 (v : Limb4) : Nat :=
  let r := radix80
  v.l0 + r * (v.l1 + r * (v.l2 + r * v.l3))

/-- Canonical range check for a BN254 `Fp` `4×80b` element. -/
def limb4CanonicalBN254 (v : Limb4) : Bool :=
  let r := radix80
  decide (v.l0 < r) && decide (v.l1 < r) && decide (v.l2 < r) && decide (v.l3 < r) &&
    decide (ofLimb4 v < bn254Fp)

/-- Unpack a BN254 `Fp` element into `4×64b` limbs. -/
def toLimb4U64 (x : Nat) : Limb4 :=
  let r := radix64
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let l3 := q2 / r
  { l0, l1, l2, l3 }

/-- Recompose a `4×64b` limb vector back into a `Nat`. -/
def ofLimb4U64 (v : Limb4) : Nat :=
  let r := radix64
  v.l0 + r * (v.l1 + r * (v.l2 + r * v.l3))

/-- Unpack a BLS12-381 `Fp` element (`< 2^381 < 2^400`) into `5×80b` limbs. -/
def toLimb5 (x : Nat) : Limb5 :=
  let r := radix80
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let q3 := q2 / r
  let l3 := q3 % r
  let l4 := q3 / r
  { l0, l1, l2, l3, l4 }

/-- Recompose a `5×80b` limb vector back into a `Nat`. -/
def ofLimb5 (v : Limb5) : Nat :=
  let r := radix80
  v.l0 + r * (v.l1 + r * (v.l2 + r * (v.l3 + r * v.l4)))

/-- Canonical range check for a BLS12-381 `Fp` `5×80b` element. -/
def limb5CanonicalBLS12381 (v : Limb5) : Bool :=
  let r := radix80
  decide (v.l0 < r) && decide (v.l1 < r) && decide (v.l2 < r) && decide (v.l3 < r) &&
    decide (v.l4 < r) && decide (ofLimb5 v < bls12381Fp)

/-- Unpack a BLS12-381 `Fp` element (`< 2^381 < 2^384`) into `6×64b` limbs. -/
def toLimb6U64 (x : Nat) : Limb6 :=
  let r := radix64
  let l0 := x % r
  let q1 := x / r
  let l1 := q1 % r
  let q2 := q1 / r
  let l2 := q2 % r
  let q3 := q2 / r
  let l3 := q3 % r
  let q4 := q3 / r
  let l4 := q4 % r
  let l5 := q4 / r
  { l0, l1, l2, l3, l4, l5 }

/-- Recompose a `6×64b` limb vector back into a `Nat`. -/
def ofLimb6U64 (v : Limb6) : Nat :=
  let r := radix64
  v.l0 + r * (v.l1 + r * (v.l2 + r * (v.l3 + r * (v.l4 + r * v.l5))))

/-- Round-trip identity `ofLimb4 (toLimb4 x) = x` for all `x : Nat`. -/
theorem ofLimb4_toLimb4 (x : Nat) : ofLimb4 (toLimb4 x) = x := by
  simp only [ofLimb4, toLimb4, Nat.mod_add_div]

/-- Round-trip identity `ofLimb5 (toLimb5 x) = x` for all `x : Nat`. -/
theorem ofLimb5_toLimb5 (x : Nat) : ofLimb5 (toLimb5 x) = x := by
  simp only [ofLimb5, toLimb5, Nat.mod_add_div]

/-! ## Live STARK Benchmark Entrypoint (`g1AddEntry`) -/

/-- **STARK Entrypoint (`g1AddEntry`)**: invokes the exact shared generic
`g1OnCurve` and `g1AddAffine` (which calls `fqInvMod`, `fqMulMod`, `fqAddMod`,
`fqSubMod`, `g1DoubleAffine`) on `toyCurve` (`y² = x³ + 3 mod 101`).
Returns `1` iff both `(px, py)` and `(qx, qy)` are canonical on-curve points and
`g1AddAffine toyCurve P Q = (rx, ry)` (finite), else `0`.

Valid witnesses:
* Distinct chord `G + 2G = 3G`: `(1, 2, 68, 74, 26, 45) → 1`
* Point doubling `G + G = 2G`: `(1, 2, 1, 2, 68, 74) → 1`
* Commutativity `2G + G = 3G`: `(68, 74, 1, 2, 26, 45) → 1` -/
@[circuit_budget 12 160 44 0 360]
def g1AddEntry (px py qx qy rx ry : Nat) : Nat :=
  let c := toyCurve
  let pPt : G1Point := { x := px, y := py, isInf := 0 }
  let qPt : G1Point := { x := qx, y := qy, isInf := 0 }
  if g1OnCurve c pPt then
    if g1OnCurve c qPt then
      let sum := g1AddAffine c pPt qPt
      if sum.isInf == 0 then
        if sum.x == rx then
          if sum.y == ry then 1 else 0
        else 0
      else 0
    else 0
  else 0

/-! ## Pure Lean Self-Checks (`#guard`): BN254 `G1`, BLS12-381 `G1`, `F₄`, Toy Curve, Limbs -/

-- 1. BN254 `G1` (`y² = x³ + 3 mod bn254Fp`, generator `(1, 2)`, order `bn254Fr`)
private def bn254G : G1Point := g1Gen bn254Curve
private def bn254_2G : G1Point := g1AddAffine bn254Curve bn254G bn254G
private def bn254_3G : G1Point := g1AddAffine bn254Curve bn254_2G bn254G

#guard bn254Fp < maxFieldModulus
#guard g1OnCurve bn254Curve bn254G == true
#guard g1OnCurve bn254Curve bn254_2G == true
#guard g1OnCurve bn254Curve bn254_3G == true
#guard bn254_2G ==
  { x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
    y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
    isInf := 0 }
#guard bn254_3G ==
  { x := 3353031288059533942658390886683067124040920775575537747144343083137631628272
    y := 19321533766552368860946552437480515441416830039777911637913418824951667761761
    isInf := 0 }
#guard g1AddAffine bn254Curve bn254G bn254_2G == bn254_3G
#guard g1AddAffine bn254Curve bn254_2G (g1Neg bn254Curve bn254_2G) == g1Inf
#guard g1AddAffine bn254Curve g1Inf bn254_2G == bn254_2G
#guard g1AddAffine bn254Curve bn254_2G g1Inf == bn254_2G
#guard g1ScalarMul bn254Curve 3 bn254G == bn254_3G
#guard g1ScalarMul bn254Curve bn254Fr bn254G == g1Inf
#guard fqInvMod.check bn254Fp bn254_2G.x (fqInvMod bn254Fp bn254_2G.x) == true
#guard fqMulMod.check bn254Fp bn254_2G.x bn254_3G.y (fqMulMod bn254Fp bn254_2G.x bn254_3G.y) == true
#guard fqMulDivModCheck bn254Fp bn254_2G.x bn254_3G.y (fqMulDivMod bn254Fp bn254_2G.x bn254_3G.y) == true

-- 2. BLS12-381 `G1` (`y² = x³ + 4 mod bls12381Fp`, IETF generator, order `bls12381Fr`)
private def blsG : G1Point := g1Gen bls12381Curve
private def bls_2G : G1Point := g1AddAffine bls12381Curve blsG blsG
private def bls_3G : G1Point := g1AddAffine bls12381Curve bls_2G blsG

#guard bls12381Fp < maxFieldModulus
#guard g1OnCurve bls12381Curve blsG == true
#guard g1OnCurve bls12381Curve bls_2G == true
#guard g1OnCurve bls12381Curve bls_3G == true
#guard bls_2G ==
  { x := 838589206289216005799424730305866328161735431124665289961769162861615689790485775997575391185127590486775437397838
    y := 3450209970729243429733164009999191867485184320918914219895632678707687208996709678363578245114137957452475385814312
    isInf := 0 }
#guard bls_3G ==
  { x := 1527649530533633684281386512094328299672026648504329745640827351945739272160755686119065091946435084697047221031460
    y := 487897572011753812113448064805964756454529228648704488481988876974355015977479905373670519228592356747638779818193
    isInf := 0 }
#guard g1AddAffine bls12381Curve blsG bls_2G == bls_3G
#guard g1AddAffine bls12381Curve bls_2G (g1Neg bls12381Curve bls_2G) == g1Inf
#guard g1AddAffine bls12381Curve g1Inf bls_2G == bls_2G
#guard g1AddAffine bls12381Curve bls_2G g1Inf == bls_2G
#guard g1ScalarMul bls12381Curve 3 blsG == bls_3G
#guard g1ScalarMul bls12381Curve bls12381Fr blsG == g1Inf
#guard fqInvMod.check bls12381Fp blsG.x (fqInvMod bls12381Fp blsG.x) == true
#guard fqMulMod.check bls12381Fp blsG.x bls_2G.y (fqMulMod bls12381Fp blsG.x bls_2G.y) == true
#guard fqMulDivModCheck bls12381Fp blsG.x bls_2G.y (fqMulDivMod bls12381Fp blsG.x bls_2G.y) == true

-- 3. Limb-packed round-trips on BN254 (`4×80b` & `4×64b`) and BLS12-381 (`5×80b` & `6×64b`)
--    for generator `G`, `2G`, and `3G` coordinates
#guard ofLimb4 (toLimb4 bn254G.x) == bn254G.x && limb4CanonicalBN254 (toLimb4 bn254G.x)
#guard ofLimb4 (toLimb4 bn254G.y) == bn254G.y && limb4CanonicalBN254 (toLimb4 bn254G.y)
#guard ofLimb4 (toLimb4 bn254_2G.x) == bn254_2G.x && limb4CanonicalBN254 (toLimb4 bn254_2G.x)
#guard ofLimb4 (toLimb4 bn254_2G.y) == bn254_2G.y && limb4CanonicalBN254 (toLimb4 bn254_2G.y)
#guard ofLimb4 (toLimb4 bn254_3G.x) == bn254_3G.x && limb4CanonicalBN254 (toLimb4 bn254_3G.x)
#guard ofLimb4 (toLimb4 bn254_3G.y) == bn254_3G.y && limb4CanonicalBN254 (toLimb4 bn254_3G.y)
#guard ofLimb4U64 (toLimb4U64 bn254_2G.x) == bn254_2G.x
#guard ofLimb4U64 (toLimb4U64 bn254_3G.y) == bn254_3G.y

#guard ofLimb5 (toLimb5 blsG.x) == blsG.x && limb5CanonicalBLS12381 (toLimb5 blsG.x)
#guard ofLimb5 (toLimb5 blsG.y) == blsG.y && limb5CanonicalBLS12381 (toLimb5 blsG.y)
#guard ofLimb5 (toLimb5 bls_2G.x) == bls_2G.x && limb5CanonicalBLS12381 (toLimb5 bls_2G.x)
#guard ofLimb5 (toLimb5 bls_2G.y) == bls_2G.y && limb5CanonicalBLS12381 (toLimb5 bls_2G.y)
#guard ofLimb5 (toLimb5 bls_3G.x) == bls_3G.x && limb5CanonicalBLS12381 (toLimb5 bls_3G.x)
#guard ofLimb5 (toLimb5 bls_3G.y) == bls_3G.y && limb5CanonicalBLS12381 (toLimb5 bls_3G.y)
#guard ofLimb6U64 (toLimb6U64 blsG.x) == blsG.x
#guard ofLimb6U64 (toLimb6U64 bls_2G.x) == bls_2G.x
#guard ofLimb6U64 (toLimb6U64 bls_3G.y) == bls_3G.y

-- 4. Fermat prime `F₄ = 65537` curve (`y² = x³ + 3 mod 65537`, generator `(1, 2)`)
private def f4G : G1Point := g1Gen f4Curve
private def f4_2G : G1Point := g1AddAffine f4Curve f4G f4G
private def f4_3G : G1Point := g1AddAffine f4Curve f4_2G f4G

#guard g1OnCurve f4Curve f4G == true
#guard f4_2G == { x := 28671, y := 11264, isInf := 0 }
#guard f4_3G == { x := 17495, y := 40705, isInf := 0 }
#guard g1AddAffine f4Curve f4G f4_2G == f4_3G
#guard g1AddAffine f4Curve f4_2G (g1Neg f4Curve f4_2G) == g1Inf

-- 5. Toy prime curve (`p = 101`, `b = 3`, `G = (1, 2)`, order `17`) & STARK entrypoint `g1AddEntry`
private def toyG : G1Point := g1Gen toyCurve
private def toy_2G : G1Point := g1AddAffine toyCurve toyG toyG
private def toy_3G : G1Point := g1AddAffine toyCurve toy_2G toyG
private def toy_4G : G1Point := g1AddAffine toyCurve toy_3G toyG
private def toy_5G : G1Point := g1AddAffine toyCurve toy_4G toyG

#guard g1OnCurve toyCurve toyG == true
#guard toy_2G == { x := 68, y := 74, isInf := 0 }
#guard toy_3G == { x := 26, y := 45, isInf := 0 }
#guard toy_4G == { x := 65, y := 98, isInf := 0 }
#guard toy_5G == { x := 12, y := 32, isInf := 0 }
#guard g1AddAffine toyCurve toyG toy_2G == toy_3G
#guard g1AddAffine toyCurve (g1AddAffine toyCurve toyG toy_2G) toy_2G ==
  g1AddAffine toyCurve toyG (g1AddAffine toyCurve toy_2G toy_2G)
#guard g1AddAffine toyCurve toy_2G (g1Neg toyCurve toy_2G) == g1Inf
#guard g1ScalarMul toyCurve toyOrder toyG == g1Inf
#guard fqInvModToy.check 37 (fqInvModToy 37) == true
#guard fqDivModToy.check 45 37 (fqDivModToy 45 37) == true

-- `g1AddEntry` positive & negative checks (valid chord, doubling, commutativity vs tampered/off-curve)
#guard g1AddEntry 1 2 68 74 26 45 == 1
#guard g1AddEntry 1 2 1 2 68 74 == 1
#guard g1AddEntry 68 74 1 2 26 45 == 1
#guard g1AddEntry 26 45 68 74 12 32 == 1
#guard g1AddEntry 1 2 68 74 27 45 == 0
#guard g1AddEntry 1 2 68 74 26 46 == 0
#guard g1AddEntry 1 3 68 74 26 45 == 0
#guard g1AddEntry 1 2 68 75 26 45 == 0
#guard g1AddEntry 102 2 68 74 26 45 == 0
#guard g1AddEntry 68 74 68 27 0 0 == 0

end CurveOpsPure
