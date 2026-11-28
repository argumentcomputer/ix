import Ix.Compile.CircuitContract

/-! # Pure Annotated Lean 4 `MultiStark` `Fp3` Cubic Extension & FRI Verifier (`FriPure`)

Phase 3 M3c vertical slice — the third pillar of single-source annotated Lean 4
`MultiStark` Protocol `v6` verifier compilation (alongside `MmcsPure.lean` and
`KzgAlgebraPure.lean`), matching the exact algebraic formulas of:
* `Aiur/Aiur/Library/Field/Goldilocks.lean` (cubic trinomial extension
  $\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$ with 6-mul Karatsuba
  multiplication `eg_mul` and adjugate norm inversion `eg_inverse`),
* `MultiStark/MultiStark/Modules/Pcs.lean` (`fri_fold2`, `exp_by_bits`,
  `glist_rev`, `recon_evals`, `rollin`, `finalize_buckets` DEEP quotient,
  `verify_query`), and
* Plonky3 `TwoAdicFriFolding` multi-arity FRI folding (`log_arity ∈ {1, 2, 3}`,
  i.e., `mla = 3` Endpoint 1 arity-2 / arity-4 / arity-8 butterfly folding with a
  single base-field inversion per round) and final-polynomial Horner evaluation
  (`evalFinalPoly`).

## Design Notes

* **Zero forbidden constructs**: pure total Lean 4 only — every recursive function
  uses structural recursion (`termination_by structural`), with zero `sorry`,
  `admit`, `axiom`, `partial`, `unsafe`, `native_decide`, `bv_decide`,
  `@[extern]`, or `@[implemented_by]`.
* **Zero Ixon content-address mutation**: every `@[circuit_inline]`,
  `@[circuit_noinline]`, `@[circuit_budget]`, and `checked def` annotation
  registers sidecar metadata strictly under `open scoped Ix.Circuit` without
  mutating any elaborated `ConstantInfo`.
* **Monomorphic unboxed ADTs (`ShapeInfer`, 0 `Obj` fallback, 0 depth columns)**:
  `Fp3` (3-field `.data` struct, 0 ROM), `BitList`, `Fp3List`, `FriParams`,
  `FriRound`, `FriRoundList`, `Evals2`, `Evals4`, `Evals8`.
* **Kernel-verified Tier-2 `guess` operations** (`checked def ... complete by`):
  1. `fInvMod`: general base-field inverse modulo any `2 ≤ p < 2^65` (covering
     Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$, 23-adic NTT prime
     $998244353$, and Fermat prime $F_3 = 257$), with algebraic checker
     `r < p ∧ (a * r) % p == 1` and unconditional uniqueness proof.
  2. `fInvToy`: concrete prime `p = 257` base-field inverse with both
     kernel-checked uniqueness and completeness proofs.
  3. `fp3InvToy`: concrete prime `p = 257` cubic extension `Fp3 → Fp3` inverse
     over $\mathbb{F}_{257}[X]/(X^3 - X - 1)$, verified directly by
     `fp3Canonical 257 r && (fp3Eq (fp3Mul 257 a r) fp3One == 1)` (eliminating
     the entire adjugate + Euclid tower from the STARK circuit!) with both
     kernel-checked uniqueness (`by`) and full unconditional completeness
     (`complete by`, proved from primality of `257` and irreducibility of
     $X^3 - X - 1$ over $\mathbb{F}_{257}$).
* **Live STARK Benchmark Entrypoint (`FriPure.entryFriQuery`)**:
  Exercises the full end-to-end query verifier over `p = 257` (where
  $X^3 - X - 1$ is genuinely irreducible, 2-adicity is `8`, and
  $(p - 1)^2 = 65536 < 2^{56}$ fits `TableTier.byte256`):
  DEEP quotient via `fp3InvToy`, 3 mixed multi-arity FRI rounds
  (`log_arity = 3` arity-8 + roll-in → `log_arity = 2` arity-4 →
  `log_arity = 1` arity-2, all invoking `fInvMod` inside the shared generic
  `verifyFriQuery`), and degree-1 final-polynomial Horner evaluation
  `evalFinalPoly` at `x_final = 241 ≠ 1`.
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace FriPure

/-! ## Monomorphic ADTs (`ShapeInfer`-Unboxed, 0 `Obj` Fallback) -/

/-- Cubic extension field element `c0 + c1·X + c2·X²` in
$\mathbb{F}_{p^3} = \mathbb{F}_p[X]/(X^3 - X - 1)$ (unboxed 3-field `.data`
struct, 0 ROM, matching `Goldilocks::ExtGoldilocks = [Field; 3]`). -/
structure Fp3 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  deriving BEq, DecidableEq, Repr

/-- LSB-first query index bits (`Lists::List<Field>` in `Pcs.lean`). -/
inductive BitList where
  | nil
  | cons (bit : Nat) (rest : BitList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of cubic extension elements (siblings and final polynomial
coefficients). -/
inductive Fp3List where
  | nil
  | cons (head : Fp3) (tail : Fp3List)
  deriving BEq, DecidableEq, Repr

/-- Single-source FRI field and 2-adic subgroup parameters.
* `p`: prime modulus where $X^3 - X - 1$ is irreducible over $\mathbb{F}_p$,
* `inv2`: `(p + 1) / 2 = 2⁻¹ mod p`,
* `genMax`: primitive `2^maxLog`-th root of unity in $\mathbb{F}_p^\times$,
* `w2Inv`: inverse of the primitive 4th root `twoAdicGen 2` (for arity-4 folds),
* `w3Inv`: inverse of the primitive 8th root `twoAdicGen 3` (for arity-8 folds). -/
structure FriParams where
  p : Nat
  inv2 : Nat
  genMax : Nat
  maxLog : Nat
  w2Inv : Nat
  w3Inv : Nat
  deriving BEq, DecidableEq, Repr

/-- One FRI commit-phase folding round for a single query, supporting variable
arity `logArity ∈ {1, 2, 3}` and optional height-matched reduced-opening roll-in
(`Pcs::rollin` / Plonky3 `fold_query`). -/
structure FriRound where
  logArity : Nat
  beta : Fp3
  sibs : Fp3List
  hasRollin : Nat
  rollin : Fp3
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of FRI folding rounds. -/
inductive FriRoundList where
  | nil
  | cons (head : FriRound) (tail : FriRoundList)
  deriving BEq, DecidableEq, Repr

/-- Unboxed reconstructed arity-2 sibling row (`ok = 1` iff valid sibling count). -/
structure Evals2 where
  ok : Nat
  e0 : Fp3
  e1 : Fp3
  deriving BEq, DecidableEq, Repr

/-- Unboxed reconstructed arity-4 sibling row (`ok = 1` iff valid sibling count). -/
structure Evals4 where
  ok : Nat
  e0 : Fp3
  e1 : Fp3
  e2 : Fp3
  e3 : Fp3
  deriving BEq, DecidableEq, Repr

/-- Unboxed reconstructed arity-8 sibling row (`ok = 1` iff valid sibling count). -/
structure Evals8 where
  ok : Nat
  e0 : Fp3
  e1 : Fp3
  e2 : Fp3
  e3 : Fp3
  e4 : Fp3
  e5 : Fp3
  e6 : Fp3
  e7 : Fp3
  deriving BEq, DecidableEq, Repr

/-- Result of one multi-arity FRI round (`ok = 1` iff arity & sibling shape valid). -/
structure RoundStepResult where
  ok : Nat
  folded : Fp3
  nextBits : BitList
  nextLog : Nat
  deriving BEq, DecidableEq, Repr

/-! ## Single-Source Prime Field & FRI Subgroup Constants -/

/-- Upper bound `2^65` covering Goldilocks (`2^64 - 2^32 + 1`), 23-adic NTT
prime `998244353`, and Fermat prime `257`. -/
def maxFriModulus : Nat := 2 ^ 65

/-- Fermat prime `F₃ = 257 = 2^8 + 1`: 8-adic NTT prime with `(p - 1)² = 65536 < 2^56`
and $X^3 - X - 1$ genuinely irreducible over $\mathbb{F}_{257}$. -/
@[circuit_inline]
def toyPrime : Nat := 257

/-- FRI parameters for `toyPrime = 257` (`genMax = 3` has exact order `2^8 = 256`,
`w2 = 241`, `w2Inv = 16`, `w3 = 64`, `w3Inv = 253`). -/
@[circuit_inline]
def toyFriParams : FriParams :=
  { p := toyPrime
    inv2 := 129
    genMax := 3
    maxLog := 8
    w2Inv := 16
    w3Inv := 253 }

/-- Protocol `v6` Goldilocks prime $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$. -/
def goldilocksPrime : Nat := 18446744069414584321

/-- Exact Goldilocks primitive $2^{32}$-th root of unity (`StarkVerifier::two_adic_gen(32)`). -/
def goldilocksGen32 : Nat := 1753635133440165772

/-- Exact Goldilocks $2^{-1} = (p_{\mathrm{GL}} + 1) / 2$ (`Pcs::fri_fold2`). -/
def goldilocksInv2 : Nat := 9223372034707292161

/-- FRI parameters for Protocol `v6` Goldilocks ($\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$). -/
def goldilocksFriParams : FriParams :=
  { p := goldilocksPrime
    inv2 := goldilocksInv2
    genMax := goldilocksGen32
    maxLog := 32
    w2Inv := 18446462594437873665
    w3Inv := 1099511627520 }

/-- 23-adic NTT prime `998244353 = 119 * 2^23 + 1` ($X^3 - X - 1$ irreducible). -/
def ntt23Prime : Nat := 998244353

/-- Primitive $2^{23}$-th root of unity in $\mathbb{F}_{998244353}^\times$ (`3^119 mod p`). -/
def ntt23Gen23 : Nat := 15311432

/-! ## Base Prime Field Arithmetic & Tier-2 `guess` Inverses -/

/-- Branchless modular addition `(a + b) mod p` (0 depth columns in recursive callers). -/
@[circuit_noinline]
def addMod (p a b : Nat) : Nat :=
  (a + b) % p

/-- Branchless modular subtraction `(a - b) mod p` for `b ≤ p`. -/
@[circuit_noinline]
def subMod (p a b : Nat) : Nat :=
  (a + p - b) % p

/-- Modular negation `(-a) mod p` for canonical `a < p`. -/
@[circuit_inline]
def negMod (p a : Nat) : Nat :=
  if a == 0 then 0 else p - a

/-- Modular multiplication `(a * b) mod p`. -/
@[circuit_noinline]
def mulMod (p a b : Nat) : Nat :=
  (a * b) % p

/-- Pure-`Nat` structural-fuel unsigned extended Euclidean worker modulo `p`.
Maintains Bézout invariants `a * t0 ≡ r0 (mod p)` and `a * t1 ≡ r1 (mod p)`
with `t0, t1 < p` and early exit on `r1 = 0`. -/
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
      let qt1 := mulMod p q t1
      let t2 := subMod p t0 qt1
      egcdStep p fuel d r2 t1 t2
termination_by structural fuel => fuel

/-! ### Pure-Lean Modular Arithmetic & Euclid Correctness Lemmas (Zero Mathlib) -/

private def pow2 : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * pow2 k

private theorem pow2_eq_pow : ∀ k, pow2 k = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [pow2, pow2_eq_pow k, Nat.pow_succ, Nat.mul_comm]

private theorem maxFriModulus_eq_pow2 : maxFriModulus = pow2 65 := by
  unfold maxFriModulus
  exact (pow2_eq_pow 65).symm

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
    let qt1 := mulMod p q t1
    let t2 := subMod p t0 qt1
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
      let t2 := subMod p t0 (mulMod p q1 t1)
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
        let t3 := subMod p t1 (mulMod p q2 t2)
        have hstep2 : egcdStep p (fuel2 + 1) d (r2' + 1) t1 t2 = egcdStep p fuel2 r2 r3 t2 t3 := by
          change egcdStep p fuel2 (r2' + 1) (d % (r2' + 1)) t2
            (subMod p t1 (mulMod p (d / (r2' + 1)) t2)) =
            egcdStep p fuel2 r2 (d % r2) t2 (subMod p t1 (mulMod p (d / r2) t2))
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

/-- **Tier-2 `guess` #1 (`checked def`)**: general base-field modular inverse
over any prime `2 ≤ p < 2^65` (covering Goldilocks $2^{64}-2^{32}+1$,
`998244353`, and `257`). Checker is pure algebraic (`r < p ∧ (a * r) % p == 1`)
with zero circularity and unconditional kernel-checked uniqueness across all
`p a : Nat`. -/
@[circuit_noinline]
checked def fInvMod (p a : Nat) : Nat :=
  hint if p < 2 then 0
       else if a % p == 0 then 0
       else egcdStep p 131 p (a % p) 0 1
  where check fun r =>
    if p < 2 then r == 0
    else if a % p == 0 then r == 0
    else decide (p < maxFriModulus) && decide (r < p) && ((a * r) % p == 1)
  by
    intro res hr
    unfold fInvMod.check at hr
    unfold fInvMod
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
        have hpPow2 : p < pow2 65 := by rwa [maxFriModulus_eq_pow2] at hpMax
        have hgcdPA : Nat.gcd p a = 1 := gcd_eq_one_of_mul_mod_eq_one p a res hmulEq
        have hgcdMod : Nat.gcd p (a % p) = 1 := by
          rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]
          exact hgcdPA
        have hpPos : 0 < p := by omega
        have hspec := egcdStep_spec p a hpGe 65 131 p (a % p) 0 1
          (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
          hpPos (by omega)
          (by simp)
          (by simp [Nat.mul_one])
          hgcdMod
        exact mod_inv_unique p a res _ hresLt hspec.1 hmulEq hspec.2

/-- Completeness of `fInvMod` for every coprime input `(p, a)` with `2 ≤ p < 2^65`
(hence for all non-zero elements of Goldilocks, `998244353`, and `257`). -/
theorem fInvMod_complete_of_coprime (p a : Nat)
    (hpGe : 2 ≤ p) (hpMax : p < maxFriModulus) (hcop : Nat.gcd p a = 1) :
    fInvMod.check p a (fInvMod p a) = true := by
  unfold fInvMod.check fInvMod
  have hp2 : ¬ (p < 2) := by omega
  simp only [hp2, ↓reduceIte]
  by_cases ha0 : a % p = 0
  · simp [ha0]
  · have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
    rw [ha0B]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    have hpPow2 : p < pow2 65 := by rwa [maxFriModulus_eq_pow2] at hpMax
    have hgcdMod : Nat.gcd p (a % p) = 1 := by
      rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]
      exact hcop
    have hpPos : 0 < p := by omega
    have hspec := egcdStep_spec p a hpGe 65 131 p (a % p) 0 1
      (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
      hpPos (by omega)
      (by simp)
      (by simp [Nat.mul_one])
      hgcdMod
    exact ⟨⟨hpMax, hspec.1⟩, hspec.2⟩

/-- Structural primality checker for `toyPrime = 257`: confirms no `d ∈ [2, 16]`
divides `257` (since `17 * 17 = 289 > 257`). Proved by `rfl` with tiny proof term. -/
private def checkNoDiv257 : Nat → Bool
  | 0 => true
  | k + 1 =>
    let d := k + 2
    ((257 % d) != 0) && checkNoDiv257 k

private theorem checkNoDiv257_sound : ∀ n, checkNoDiv257 n = true →
    ∀ d, 2 ≤ d → d < n + 2 → 257 % d ≠ 0
  | 0, _, _, hd2, hdLt => by omega
  | n + 1, h, d, hd2, hdLt => by
    simp only [checkNoDiv257, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    by_cases hdn : d = n + 2
    · subst hdn; exact h.1
    · exact checkNoDiv257_sound n h.2 d hd2 (by omega)

private theorem dvd_257_iff (d : Nat) (hd : d ∣ 257) : d = 1 ∨ d = 257 := by
  rcases hd with ⟨q, hq⟩
  by_cases hd16 : d ≤ 16
  · by_cases hd0 : d = 0
    · subst hd0; omega
    · by_cases hd1 : d = 1
      · exact Or.inl hd1
      · have hmod : 257 % d = 0 := by rw [hq, Nat.mul_mod_right]
        have hne := checkNoDiv257_sound 15 rfl d (by omega) (by omega)
        exact False.elim (hne hmod)
  · by_cases hq16 : q ≤ 16
    · by_cases hq0 : q = 0
      · subst hq0; omega
      · by_cases hq1 : q = 1
        · subst hq1; exact Or.inr (by omega)
        · have hmod : 257 % q = 0 := by rw [hq, Nat.mul_mod_left]
          have hne := checkNoDiv257_sound 15 rfl q (by omega) (by omega)
          exact False.elim (hne hmod)
    · have hge : 17 * 17 ≤ d * q := Nat.mul_le_mul (by omega) (by omega)
      omega

private theorem gcd_257_eq_one (a : Nat) (ha : a % toyPrime ≠ 0) : Nat.gcd toyPrime a = 1 := by
  have hdvd : Nat.gcd toyPrime a ∣ 257 := Nat.gcd_dvd_left 257 a
  rcases dvd_257_iff (Nat.gcd toyPrime a) hdvd with h1 | h257
  · exact h1
  · have hdvdA : 257 ∣ a := by
      have := Nat.gcd_dvd_right toyPrime a
      rw [h257] at this
      exact this
    exact False.elim (ha (Nat.mod_eq_zero_of_dvd hdvdA))

private theorem toyPrime_lt_maxFriModulus : toyPrime < maxFriModulus := by
  decide

private theorem fInvMod_toy_spec (a : Nat) (ha : a % toyPrime ≠ 0) :
    fInvMod toyPrime a < toyPrime ∧ (a * fInvMod toyPrime a) % toyPrime = 1 := by
  have hcomp := fInvMod_complete_of_coprime toyPrime a (by decide)
    toyPrime_lt_maxFriModulus (gcd_257_eq_one a ha)
  unfold fInvMod.check at hcomp
  have h2 : ¬ (toyPrime < 2) := by decide
  have haB : (a % toyPrime == 0) = false := beq_false_of_ne ha
  simp only [h2, haB, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hcomp
  exact ⟨hcomp.1.2, hcomp.2⟩

/-- **Tier-2 `guess` #2 (`checked def ... complete by`)**: concrete-prime
(`p = 257`) base-field modular inverse with both kernel-checked uniqueness
(`by`) AND unconditional completeness (`complete by`). -/
@[circuit_noinline]
checked def fInvToy (a : Nat) : Nat :=
  hint fInvMod toyPrime a
  where check fun r =>
    if a % toyPrime == 0 then r == 0
    else decide (r < toyPrime) && ((a * r) % toyPrime == 1)
  by
    intro res hr
    unfold fInvToy.check at hr
    unfold fInvToy
    apply fInvMod.check_unique toyPrime a res
    unfold fInvMod.check
    have h2 : ¬ (toyPrime < 2) := by decide
    simp only [h2, ↓reduceIte]
    by_cases ha0 : a % toyPrime = 0
    · simp [ha0] at hr ⊢
      exact hr
    · have ha0B : (a % toyPrime == 0) = false := beq_false_of_ne ha0
      rw [ha0B] at hr ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hr ⊢
      exact ⟨⟨toyPrime_lt_maxFriModulus, hr.1⟩, hr.2⟩
  complete by
    unfold fInvToy.check fInvToy
    have h2 : ¬ (toyPrime < 2) := by decide
    by_cases ha0 : a % toyPrime = 0
    · have ha0B : (a % toyPrime == 0) = true := beq_iff_eq.mpr ha0
      unfold fInvMod
      simp only [h2, ha0B, ↓reduceIte, beq_self_eq_true]
    · have ha0B : (a % toyPrime == 0) = false := beq_false_of_ne ha0
      have hspec := fInvMod_toy_spec a ha0
      simp only [ha0B, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq]
      exact hspec

/-! ## Cubic Extension Field `Fp3` ($\mathbb{F}_p[X]/(X^3 - X - 1)$, `Goldilocks.lean`) -/

/-- Additive identity `0 ∈ Fp3`. -/
@[circuit_inline]
def fp3Zero : Fp3 :=
  { c0 := 0, c1 := 0, c2 := 0 }

/-- Multiplicative identity `1 ∈ Fp3`. -/
@[circuit_inline]
def fp3One : Fp3 :=
  { c0 := 1, c1 := 0, c2 := 0 }

/-- Embed a base field element `x ∈ F_p` into `Fp3`. -/
@[circuit_inline]
def fp3OfBase (x : Nat) : Fp3 :=
  { c0 := x, c1 := 0, c2 := 0 }

/-- Canonical range check `c0 < p ∧ c1 < p ∧ c2 < p`. -/
@[circuit_inline]
def fp3Canonical (p : Nat) (a : Fp3) : Bool :=
  decide (a.c0 < p) && decide (a.c1 < p) && decide (a.c2 < p)

/-- Zero test modulo `p` (`a ≡ 0 (mod p)`). -/
@[circuit_inline]
def fp3IsZeroMod (p : Nat) (a : Fp3) : Bool :=
  (a.c0 % p == 0) && (a.c1 % p == 0) && (a.c2 % p == 0)

/-- Equality returning `1` iff all 3 coordinates match, else `0` (`Goldilocks::eg_eq`). -/
@[circuit_inline]
def fp3Eq (a b : Fp3) : Nat :=
  if a.c0 == b.c0 then
    if a.c1 == b.c1 then
      if a.c2 == b.c2 then 1 else 0
    else 0
  else 0

/-- Cubic extension addition (`Goldilocks::eg_add`). -/
@[circuit_noinline]
def fp3Add (p : Nat) (a b : Fp3) : Fp3 :=
  { c0 := addMod p a.c0 b.c0
    c1 := addMod p a.c1 b.c1
    c2 := addMod p a.c2 b.c2 }

/-- Cubic extension subtraction (`Goldilocks::eg_sub`). -/
@[circuit_noinline]
def fp3Sub (p : Nat) (a b : Fp3) : Fp3 :=
  { c0 := subMod p a.c0 b.c0
    c1 := subMod p a.c1 b.c1
    c2 := subMod p a.c2 b.c2 }

/-- Cubic extension negation (`Goldilocks::eg_neg`). -/
@[circuit_inline]
def fp3Neg (p : Nat) (a : Fp3) : Fp3 :=
  { c0 := negMod p a.c0
    c1 := negMod p a.c1
    c2 := negMod p a.c2 }

/-- Scale a cubic extension element by a base-field scalar `k ∈ F_p`. -/
@[circuit_noinline]
def fp3Scale (p : Nat) (a : Fp3) (k : Nat) : Fp3 :=
  { c0 := mulMod p a.c0 k
    c1 := mulMod p a.c1 k
    c2 := mulMod p a.c2 k }

/-- Karatsuba multiplication in $\mathbb{F}_p[X]/(X^3 - X - 1)$
(`X^3 = 1 + X`, `X^4 = X + X^2`), matching `Goldilocks::eg_mul` line-for-line
(6 base-field multiplications). -/
@[circuit_noinline]
def fp3Mul (p : Nat) (a b : Fp3) : Fp3 :=
  let v0 := mulMod p a.c0 b.c0
  let v1 := mulMod p a.c1 b.c1
  let v2 := mulMod p a.c2 b.c2
  let m01 := subMod p (subMod p (mulMod p (addMod p a.c0 a.c1) (addMod p b.c0 b.c1)) v0) v1
  let m02 := subMod p (subMod p (mulMod p (addMod p a.c0 a.c2) (addMod p b.c0 b.c2)) v0) v2
  let m12 := subMod p (subMod p (mulMod p (addMod p a.c1 a.c2) (addMod p b.c1 b.c2)) v1) v2
  { c0 := addMod p v0 m12
    c1 := addMod p (addMod p m01 m12) v2
    c2 := addMod p (addMod p m02 v1) v2 }

/-- Dedicated squaring in $\mathbb{F}_p[X]/(X^3 - X - 1)$ (`Plonky3::cubic_square`). -/
@[circuit_noinline]
def fp3Square (p : Nat) (a : Fp3) : Fp3 :=
  let s0 := mulMod p a.c0 a.c0
  let s1 := mulMod p a.c1 a.c1
  let s2 := mulMod p a.c2 a.c2
  let a01 := mulMod p a.c0 a.c1
  let m01 := addMod p a01 a01
  let a02 := mulMod p a.c0 a.c2
  let m02 := addMod p a02 a02
  let a12 := mulMod p a.c1 a.c2
  let m12 := addMod p a12 a12
  { c0 := addMod p s0 m12
    c1 := addMod p (addMod p m01 m12) s2
    c2 := addMod p (addMod p m02 s1) s2 }

/-- Repeated squaring `a^(2^k)` in `Fp3` (`StarkVerifier::ext_exp_pow2`). -/
@[circuit_noinline]
def fp3ExpPow2 (p : Nat) (a : Fp3) : Nat → Fp3
  | 0 => a
  | k + 1 => fp3ExpPow2 p (fp3Square p a) k
termination_by structural k => k

/-- Adjugate of `a` in $\mathbb{F}_p[X]/(X^3 - X - 1)$ (`Goldilocks::eg_inverse`
cofactors `(d0, d1, d2)` satisfying `a * adj(a) = (norm(a), 0, 0)`). -/
@[circuit_noinline]
def fp3Adj (p : Nat) (a : Fp3) : Fp3 :=
  let s := addMod p a.c0 a.c2
  let d0 := subMod p (mulMod p s s) (mulMod p a.c1 (addMod p a.c1 a.c2))
  let d1 := subMod p (mulMod p a.c2 a.c2) (mulMod p a.c0 a.c1)
  let d2 := subMod p (mulMod p a.c1 a.c1) (mulMod p a.c2 s)
  { c0 := d0, c1 := d1, c2 := d2 }

/-- Cubic field norm `N(a) = a0·d0 + a2·d1 + a1·d2 mod p` (`Goldilocks::eg_inverse`). -/
@[circuit_noinline]
def fp3Norm (p : Nat) (a : Fp3) : Nat :=
  let d := fp3Adj p a
  addMod p (addMod p (mulMod p a.c0 d.c0) (mulMod p a.c2 d.c1)) (mulMod p a.c1 d.c2)

/-- General cubic extension inverse via adjugate and base-field norm inverse
(`Goldilocks::eg_inverse`), working over Goldilocks, `998244353`, and `257`. -/
@[circuit_noinline]
def fp3Inv (p : Nat) (a : Fp3) : Fp3 :=
  if p < 2 then fp3Zero
  else if fp3IsZeroMod p a then fp3Zero
  else
    let d := fp3Adj p a
    let norm := addMod p (addMod p (mulMod p a.c0 d.c0) (mulMod p a.c2 d.c1)) (mulMod p a.c1 d.c2)
    let ninv := fInvMod p norm
    fp3Scale p d ninv

/-! ### Pure-Lean `Fp3` Ring & Irreducibility Proofs for Tier-2 `guess` `fp3InvToy` -/

private theorem mod_add {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a + b) % P = (a' + b') % P := by
  rw [Int.add_emod, ha, hb, ← Int.add_emod]

private theorem mod_sub {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a - b) % P = (a' - b') % P := by
  rw [Int.sub_emod, ha, hb, ← Int.sub_emod]

private theorem mod_mul {P a a' b b' : Int} (ha : a % P = a' % P) (hb : b % P = b' % P) :
    (a * b) % P = (a' * b') % P := by
  rw [Int.mul_emod, ha, hb, ← Int.mul_emod]

private theorem mod_neg {P a a' : Int} (ha : a % P = a' % P) :
    (-a) % P = (-a') % P := by
  rw [← Int.zero_sub a, ← Int.zero_sub a']
  exact mod_sub rfl ha

private theorem int_addMod_emod (p a b : Nat) :
    ((addMod p a b : Nat) : Int) % (p : Int) = ((a : Int) + (b : Int)) % (p : Int) := by
  unfold addMod
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add]

private theorem int_mulMod_emod (p a b : Nat) :
    ((mulMod p a b : Nat) : Int) % (p : Int) = ((a : Int) * (b : Int)) % (p : Int) := by
  unfold mulMod
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_mul]

private theorem int_subMod_emod (p a b : Nat) (hb : b ≤ p) :
    ((subMod p a b : Nat) : Int) % (p : Int) = ((a : Int) - (b : Int)) % (p : Int) := by
  unfold subMod
  rw [Int.natCast_emod, Int.emod_emod]
  have hcast : ((a + p - b : Nat) : Int) = (a : Int) - (b : Int) + (p : Int) := by omega
  rw [hcast, Int.add_emod_right]

private theorem nat_eq_of_int_emod_eq (p u v : Nat) (hu : u < p) (hv : v < p)
    (h : (u : Int) % (p : Int) = (v : Int) % (p : Int)) : u = v := by
  have hu' : (u : Int) % (p : Int) = (u : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have hv' : (v : Int) % (p : Int) = (v : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hu', hv'] at h
  omega

private theorem fp3Mul_int_emod (p : Nat) (hp : 0 < p) (a b : Fp3) :
    let m := fp3Mul p a b
    let a0 : Int := a.c0; let a1 : Int := a.c1; let a2 : Int := a.c2
    let b0 : Int := b.c0; let b1 : Int := b.c1; let b2 : Int := b.c2
    let P : Int := p
    (m.c0 : Int) % P = (a0 * b0 + a1 * b2 + a2 * b1) % P ∧
    (m.c1 : Int) % P = (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2) % P ∧
    (m.c2 : Int) % P = (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) % P := by
  dsimp only [fp3Mul]
  have hv0Lt : mulMod p a.c0 b.c0 ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  have hv1Lt : mulMod p a.c1 b.c1 ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  have hv2Lt : mulMod p a.c2 b.c2 ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  have hv0 := int_mulMod_emod p a.c0 b.c0
  have hv1 := int_mulMod_emod p a.c1 b.c1
  have hv2 := int_mulMod_emod p a.c2 b.c2
  have hm01 : ((subMod p (subMod p (mulMod p (addMod p a.c0 a.c1) (addMod p b.c0 b.c1))
      (mulMod p a.c0 b.c0)) (mulMod p a.c1 b.c1) : Nat) : Int) % (p : Int) =
      ((a.c0 : Int) * (b.c1 : Int) + (a.c1 : Int) * (b.c0 : Int)) % (p : Int) := by
    refine (int_subMod_emod p _ _ hv1Lt).trans ?_
    refine (mod_sub ((int_subMod_emod p _ _ hv0Lt).trans
      (mod_sub ((int_mulMod_emod p _ _).trans
        (mod_mul (int_addMod_emod p _ _) (int_addMod_emod p _ _))) hv0)) hv1).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  have hm02 : ((subMod p (subMod p (mulMod p (addMod p a.c0 a.c2) (addMod p b.c0 b.c2))
      (mulMod p a.c0 b.c0)) (mulMod p a.c2 b.c2) : Nat) : Int) % (p : Int) =
      ((a.c0 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c0 : Int)) % (p : Int) := by
    refine (int_subMod_emod p _ _ hv2Lt).trans ?_
    refine (mod_sub ((int_subMod_emod p _ _ hv0Lt).trans
      (mod_sub ((int_mulMod_emod p _ _).trans
        (mod_mul (int_addMod_emod p _ _) (int_addMod_emod p _ _))) hv0)) hv2).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  have hm12 : ((subMod p (subMod p (mulMod p (addMod p a.c1 a.c2) (addMod p b.c1 b.c2))
      (mulMod p a.c1 b.c1)) (mulMod p a.c2 b.c2) : Nat) : Int) % (p : Int) =
      ((a.c1 : Int) * (b.c2 : Int) + (a.c2 : Int) * (b.c1 : Int)) % (p : Int) := by
    refine (int_subMod_emod p _ _ hv2Lt).trans ?_
    refine (mod_sub ((int_subMod_emod p _ _ hv1Lt).trans
      (mod_sub ((int_mulMod_emod p _ _).trans
        (mod_mul (int_addMod_emod p _ _) (int_addMod_emod p _ _))) hv1)) hv2).trans ?_
    congr 1; simp only [Int.add_mul, Int.mul_add]; omega
  refine ⟨?_, ?_, ?_⟩
  · refine (int_addMod_emod p _ _).trans ((mod_add hv0 hm12).trans ?_)
    congr 1; omega
  · refine (int_addMod_emod p _ _).trans ((mod_add ((int_addMod_emod p _ _).trans (mod_add hm01 hm12)) hv2).trans ?_)
    congr 1; omega
  · refine (int_addMod_emod p _ _).trans ((mod_add ((int_addMod_emod p _ _).trans (mod_add hm02 hv1)) hv2).trans ?_)
    congr 1; omega

private theorem fp3Mul_canonical (p : Nat) (hp : 0 < p) (a b : Fp3) :
    (fp3Mul p a b).c0 < p ∧ (fp3Mul p a b).c1 < p ∧ (fp3Mul p a b).c2 < p :=
  ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

private theorem fp3Mul_comm (p : Nat) (hp : 0 < p) (a b : Fp3) :
    fp3Mul p a b = fp3Mul p b a := by
  have hab := fp3Mul_int_emod p hp a b
  have hba := fp3Mul_int_emod p hp b a
  have hc1 := fp3Mul_canonical p hp a b
  have hc2 := fp3Mul_canonical p hp b a
  cases hm1 : fp3Mul p a b with
  | mk x0 x1 x2 =>
    cases hm2 : fp3Mul p b a with
    | mk y0 y1 y2 =>
      rw [hm1] at hab hc1; rw [hm2] at hba hc2
      have h0 : x0 = y0 := nat_eq_of_int_emod_eq p x0 y0 hc1.1 hc2.1 (by
        rw [hab.1, hba.1]; congr 1
        rw [Int.mul_comm (a.c0 : Int), Int.mul_comm (a.c1 : Int), Int.mul_comm (a.c2 : Int)]; omega)
      have h1 : x1 = y1 := nat_eq_of_int_emod_eq p x1 y1 hc1.2.1 hc2.2.1 (by
        rw [hab.2.1, hba.2.1]; congr 1
        rw [Int.mul_comm (a.c0 : Int), Int.mul_comm (a.c1 : Int), Int.mul_comm (a.c1 : Int),
          Int.mul_comm (a.c2 : Int), Int.mul_comm (a.c2 : Int)]; omega)
      have h2 : x2 = y2 := nat_eq_of_int_emod_eq p x2 y2 hc1.2.2 hc2.2.2 (by
        rw [hab.2.2, hba.2.2]; congr 1
        rw [Int.mul_comm (a.c0 : Int), Int.mul_comm (a.c1 : Int), Int.mul_comm (a.c2 : Int),
          Int.mul_comm (a.c2 : Int)]; omega)
      rw [h0, h1, h2]

private theorem fp3Mul_one_right (p : Nat) (hp : 0 < p) (a : Fp3)
    (hc0 : a.c0 < p) (hc1 : a.c1 < p) (hc2 : a.c2 < p) :
    fp3Mul p a fp3One = a := by
  have hm := fp3Mul_int_emod p hp a fp3One
  have hcan := fp3Mul_canonical p hp a fp3One
  cases heq : fp3Mul p a fp3One with
  | mk x0 x1 x2 =>
    rw [heq] at hm hcan
    cases a with
    | mk a0 a1 a2 =>
      dsimp only [fp3One] at hm
      have h0 : x0 = a0 := nat_eq_of_int_emod_eq p x0 a0 hcan.1 hc0 (by rw [hm.1]; simp)
      have h1 : x1 = a1 := nat_eq_of_int_emod_eq p x1 a1 hcan.2.1 hc1 (by rw [hm.2.1]; simp)
      have h2 : x2 = a2 := nat_eq_of_int_emod_eq p x2 a2 hcan.2.2 hc2 (by rw [hm.2.2]; simp)
      rw [h0, h1, h2]

private theorem fp3Mul_assoc (p : Nat) (hp : 0 < p) (a b c : Fp3) :
    fp3Mul p (fp3Mul p a b) c = fp3Mul p a (fp3Mul p b c) := by
  have hab := fp3Mul_int_emod p hp a b
  have hbc := fp3Mul_int_emod p hp b c
  have hlhs := fp3Mul_int_emod p hp (fp3Mul p a b) c
  have hrhs := fp3Mul_int_emod p hp a (fp3Mul p b c)
  have hcL := fp3Mul_canonical p hp (fp3Mul p a b) c
  have hcR := fp3Mul_canonical p hp a (fp3Mul p b c)
  cases hL : fp3Mul p (fp3Mul p a b) c with
  | mk x0 x1 x2 =>
    cases hR : fp3Mul p a (fp3Mul p b c) with
    | mk y0 y1 y2 =>
      rw [hL] at hlhs hcL; rw [hR] at hrhs hcR
      have h0 : x0 = y0 := nat_eq_of_int_emod_eq p x0 y0 hcL.1 hcR.1 (by
        refine hlhs.1.trans ?_
        refine (mod_add (mod_add (mod_mul hab.1 rfl) (mod_mul hab.2.1 rfl)) (mod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (mod_add (mod_add (mod_mul rfl hbc.1) (mod_mul rfl hbc.2.2)) (mod_mul rfl hbc.2.1)).symm |>.trans hrhs.1.symm
        congr 1; simp only [Int.add_mul, Int.mul_add, Int.mul_assoc]; omega)
      have h1 : x1 = y1 := nat_eq_of_int_emod_eq p x1 y1 hcL.2.1 hcR.2.1 (by
        refine hlhs.2.1.trans ?_
        refine (mod_add (mod_add (mod_add (mod_add (mod_mul hab.1 rfl) (mod_mul hab.2.1 rfl))
          (mod_mul hab.2.1 rfl)) (mod_mul hab.2.2 rfl)) (mod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (mod_add (mod_add (mod_add (mod_add (mod_mul rfl hbc.2.1) (mod_mul rfl hbc.1))
          (mod_mul rfl hbc.2.2)) (mod_mul rfl hbc.2.1)) (mod_mul rfl hbc.2.2)).symm |>.trans hrhs.2.1.symm
        congr 1; simp only [Int.add_mul, Int.mul_add, Int.mul_assoc]; omega)
      have h2 : x2 = y2 := nat_eq_of_int_emod_eq p x2 y2 hcL.2.2 hcR.2.2 (by
        refine hlhs.2.2.trans ?_
        refine (mod_add (mod_add (mod_add (mod_mul hab.1 rfl) (mod_mul hab.2.1 rfl))
          (mod_mul hab.2.2 rfl)) (mod_mul hab.2.2 rfl)).trans ?_
        refine Eq.trans ?_ (mod_add (mod_add (mod_add (mod_mul rfl hbc.2.2) (mod_mul rfl hbc.2.1))
          (mod_mul rfl hbc.1)) (mod_mul rfl hbc.2.2)).symm |>.trans hrhs.2.2.symm
        congr 1; simp only [Int.add_mul, Int.mul_add, Int.mul_assoc]; omega)
      rw [h0, h1, h2]

private theorem fp3Adj_int_emod (p : Nat) (hp : 0 < p) (a : Fp3) :
    let d := fp3Adj p a
    let a0 : Int := a.c0; let a1 : Int := a.c1; let a2 : Int := a.c2
    let P : Int := p
    (d.c0 : Int) % P = ((a0 + a2) * (a0 + a2) - a1 * (a1 + a2)) % P ∧
    (d.c1 : Int) % P = (a2 * a2 - a0 * a1) % P ∧
    (d.c2 : Int) % P = (a1 * a1 - a2 * (a0 + a2)) % P := by
  dsimp only [fp3Adj]
  have h1 : mulMod p a.c1 (addMod p a.c1 a.c2) ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  have h2 : mulMod p a.c0 a.c1 ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  have h3 : mulMod p a.c2 (addMod p a.c0 a.c2) ≤ p := Nat.le_of_lt (Nat.mod_lt _ hp)
  refine ⟨?_, ?_, ?_⟩
  · exact (int_subMod_emod p _ _ h1).trans <| mod_sub
      ((int_mulMod_emod p _ _).trans (mod_mul (int_addMod_emod p _ _) (int_addMod_emod p _ _)))
      ((int_mulMod_emod p _ _).trans (mod_mul rfl (int_addMod_emod p _ _)))
  · exact (int_subMod_emod p _ _ h2).trans <|
      mod_sub (int_mulMod_emod p _ _) (int_mulMod_emod p _ _)
  · exact (int_subMod_emod p _ _ h3).trans <| mod_sub
      (int_mulMod_emod p _ _)
      ((int_mulMod_emod p _ _).trans (mod_mul rfl (int_addMod_emod p _ _)))

/-- Exact integer identity for `a * adj(a)` in $\mathbb{Z}[X]/(X^3 - X - 1)$:
the `X` and `X²` coefficients vanish identically over `Int`. -/
private theorem adj_cancel_int (a0 a1 a2 : Int) :
    let d0 := (a0 + a2) * (a0 + a2) - a1 * (a1 + a2)
    let d1 := a2 * a2 - a0 * a1
    let d2 := a1 * a1 - a2 * (a0 + a2)
    a0 * d1 + a1 * d0 + a1 * d2 + a2 * d1 + a2 * d2 = 0 ∧
    a0 * d2 + a1 * d1 + a2 * d0 + a2 * d2 = 0 := by
  dsimp only
  have m10 : a1 * a0 = a0 * a1 := Int.mul_comm _ _
  have m20 : a2 * a0 = a0 * a2 := Int.mul_comm _ _
  have m21 : a2 * a1 = a1 * a2 := Int.mul_comm _ _
  have ml10 : ∀ x, a1 * (a0 * x) = a0 * (a1 * x) := fun x => Int.mul_left_comm _ _ _
  have ml20 : ∀ x, a2 * (a0 * x) = a0 * (a2 * x) := fun x => Int.mul_left_comm _ _ _
  have ml21 : ∀ x, a2 * (a1 * x) = a1 * (a2 * x) := fun x => Int.mul_left_comm _ _ _
  constructor
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub,
      m10, m20, m21, ml10, ml20, ml21]
    omega
  · simp only [Int.mul_add, Int.add_mul, Int.mul_sub,
      m20, m21, ml10, ml20, ml21]
    omega

private theorem fp3Mul_scale_right (p : Nat) (hp : 0 < p) (a b : Fp3) (k : Nat) :
    fp3Mul p a (fp3Scale p b k) = fp3Scale p (fp3Mul p a b) k := by
  have hm1 := fp3Mul_int_emod p hp a (fp3Scale p b k)
  have hm2 := fp3Mul_int_emod p hp a b
  have hc1 := fp3Mul_canonical p hp a (fp3Scale p b k)
  have hs0 := int_mulMod_emod p b.c0 k
  have hs1 := int_mulMod_emod p b.c1 k
  have hs2 := int_mulMod_emod p b.c2 k
  cases hL : fp3Mul p a (fp3Scale p b k) with
  | mk x0 x1 x2 =>
    rw [hL] at hm1 hc1
    dsimp only [fp3Scale] at hm1 ⊢
    have h0 : x0 = mulMod p (fp3Mul p a b).c0 k :=
      nat_eq_of_int_emod_eq p x0 _ hc1.1 (Nat.mod_lt _ hp) (by
        refine hm1.1.trans ?_
        refine (mod_add (mod_add (mod_mul rfl hs0) (mod_mul rfl hs2)) (mod_mul rfl hs1)).trans ?_
        refine Eq.trans ?_ ((int_mulMod_emod p _ _).trans (mod_mul hm2.1 rfl)).symm
        congr 1; simp only [Int.add_mul, Int.mul_assoc])
    have h1 : x1 = mulMod p (fp3Mul p a b).c1 k :=
      nat_eq_of_int_emod_eq p x1 _ hc1.2.1 (Nat.mod_lt _ hp) (by
        refine hm1.2.1.trans ?_
        refine (mod_add (mod_add (mod_add (mod_add (mod_mul rfl hs1) (mod_mul rfl hs0))
          (mod_mul rfl hs2)) (mod_mul rfl hs1)) (mod_mul rfl hs2)).trans ?_
        refine Eq.trans ?_ ((int_mulMod_emod p _ _).trans (mod_mul hm2.2.1 rfl)).symm
        congr 1; simp only [Int.add_mul, Int.mul_assoc])
    have h2 : x2 = mulMod p (fp3Mul p a b).c2 k :=
      nat_eq_of_int_emod_eq p x2 _ hc1.2.2 (Nat.mod_lt _ hp) (by
        refine hm1.2.2.trans ?_
        refine (mod_add (mod_add (mod_add (mod_mul rfl hs2) (mod_mul rfl hs1))
          (mod_mul rfl hs0)) (mod_mul rfl hs2)).trans ?_
        refine Eq.trans ?_ ((int_mulMod_emod p _ _).trans (mod_mul hm2.2.2 rfl)).symm
        congr 1; simp only [Int.add_mul, Int.mul_assoc])
    rw [h0, h1, h2]

private theorem fp3Mul_adj_eq_norm (p : Nat) (hp : 0 < p) (a : Fp3) :
    fp3Mul p a (fp3Adj p a) = fp3OfBase (fp3Norm p a) := by
  have hm := fp3Mul_int_emod p hp a (fp3Adj p a)
  have hadj := fp3Adj_int_emod p hp a
  have hcan := fp3Mul_canonical p hp a (fp3Adj p a)
  have hcancel := adj_cancel_int (a.c0 : Int) (a.c1 : Int) (a.c2 : Int)
  have hnormEmod : ((fp3Norm p a : Nat) : Int) % (p : Int) =
      ((a.c0 : Int) * ((fp3Adj p a).c0 : Int) + (a.c2 : Int) * ((fp3Adj p a).c1 : Int)
        + (a.c1 : Int) * ((fp3Adj p a).c2 : Int)) % (p : Int) := by
    dsimp only [fp3Norm]
    exact (int_addMod_emod p _ _).trans <|
      mod_add ((int_addMod_emod p _ _).trans (mod_add (int_mulMod_emod p _ _) (int_mulMod_emod p _ _)))
        (int_mulMod_emod p _ _)
  cases heq : fp3Mul p a (fp3Adj p a) with
  | mk x0 x1 x2 =>
    rw [heq] at hm hcan
    dsimp only [fp3OfBase]
    have h0 : x0 = fp3Norm p a :=
      nat_eq_of_int_emod_eq p x0 (fp3Norm p a) hcan.1 (Nat.mod_lt _ hp) (by
        rw [hm.1, hnormEmod]; congr 1; omega)
    have h1 : x1 = 0 :=
      nat_eq_of_int_emod_eq p x1 0 hcan.2.1 hp (by
        refine hm.2.1.trans ?_
        refine (mod_add (mod_add (mod_add (mod_add (mod_mul rfl hadj.2.1) (mod_mul rfl hadj.1))
          (mod_mul rfl hadj.2.2)) (mod_mul rfl hadj.2.1)) (mod_mul rfl hadj.2.2)).trans ?_
        rw [hcancel.1]; rfl)
    have h2 : x2 = 0 :=
      nat_eq_of_int_emod_eq p x2 0 hcan.2.2 hp (by
        refine hm.2.2.trans ?_
        refine (mod_add (mod_add (mod_add (mod_mul rfl hadj.2.2) (mod_mul rfl hadj.2.1))
          (mod_mul rfl hadj.1)) (mod_mul rfl hadj.2.2)).trans ?_
        rw [hcancel.2]; rfl)
    rw [h0, h1, h2]

/-! #### Irreducibility of $X^3 - X - 1$ over $\mathbb{F}_{257}$ (`fp3Norm_ne_zero_257`)

To prove full unconditional completeness (`complete by`) of `fp3InvToy`, we prove
that every non-zero `a ∈ F_257[X]/(X^3 - X - 1)` has non-zero cubic norm `N(a) ≢ 0 (mod 257)`.
Rather than enumerating $257^3 = 16{,}974{,}593$ elements, we verify the 257 base-field
values via a depth-8 binary tree (`checkNoRootTree`, proved by `rfl` with recursion depth 8)
and lift that to non-vanishing of `N(a)` via the explicit degree-4 polynomial identity
`(a0 + a1·X + a2·X²)(d0 + d1·X + d2·X²) - N(a) = (q0 + q1·X)(X³ - X - 1)`. -/

/-- Depth-`d` binary-tree checker confirming `X^3 - X - 1 ≢ 0 (mod 257)` on `[lo, lo + 2^d)`. -/
private def checkNoRootTree : Nat → Nat → Bool
  | 0, lo => ((lo * lo * lo + 256 * lo + 256) % 257) != 0
  | d + 1, lo => checkNoRootTree d lo && checkNoRootTree d (lo + pow2 d)

private theorem checkNoRootTree_sound : ∀ d lo, checkNoRootTree d lo = true →
    ∀ x, lo ≤ x → x < lo + pow2 d → (x * x * x + 256 * x + 256) % 257 ≠ 0
  | 0, lo, h, x, hlo, hhi => by
    simp only [checkNoRootTree, bne_iff_ne, ne_eq] at h
    have hxeq : x = lo := by
      have : pow2 0 = 1 := rfl
      omega
    subst hxeq; exact h
  | d + 1, lo, h, x, hlo, hhi => by
    simp only [checkNoRootTree, Bool.and_eq_true] at h
    have hpow : pow2 (d + 1) = 2 * pow2 d := rfl
    by_cases hlt : x < lo + pow2 d
    · exact checkNoRootTree_sound d lo h.1 x hlo hlt
    · exact checkNoRootTree_sound d (lo + pow2 d) h.2 x (by omega) (by omega)

private theorem no_root_257_nat (r : Nat) (hr : r < 257) :
    (r * r * r + 256 * r + 256) % 257 ≠ 0 := by
  by_cases h256 : r < 256
  · exact checkNoRootTree_sound 8 0 rfl r (Nat.zero_le r) (by
      have : pow2 8 = 256 := rfl; omega)
  · have hrEq : r = 256 := by omega
    subst hrEq; decide

private theorem nat_emod_257 (a : Nat) : ((a % 257 : Nat) : Int) = (a : Int) % 257 :=
  Int.natCast_emod a 257

private theorem no_root_257_int (x : Int) : (x * x * x - x - 1) % 257 ≠ 0 := by
  intro h
  let r : Nat := (x % 257).toNat
  have hxmLt : 0 ≤ x % 257 := Int.emod_nonneg x (by decide)
  have hxmHi : x % 257 < 257 := Int.emod_lt_of_pos x (by decide)
  have hrLt : r < 257 := by omega
  have hrCast : (r : Int) = x % 257 := Int.toNat_of_nonneg hxmLt
  have hrMod : (r : Int) % 257 = x % 257 := by rw [hrCast, Int.emod_emod]
  have hmod : ((r * r * r + 256 * r + 256 : Nat) : Int) % 257 = (x * x * x - x - 1) % 257 := by
    have h1 : ((r * r * r + 256 * r + 256 : Nat) : Int) =
        (r : Int) * r * r + 256 * r + 256 := by
      simp only [Int.natCast_add, Int.natCast_mul]; rfl
    rw [h1]
    have h2 : ((r : Int) * r * r + 256 * r + 256) % 257 = ((r : Int) * r * r - r - 1) % 257 := by
      have : (r : Int) * r * r + 256 * r + 256 =
          ((r : Int) * r * r - r - 1) + 257 * ((r : Int) + 1) := by omega
      rw [this, Int.add_mul_emod_self_left]
    exact h2.trans (mod_sub (mod_sub (mod_mul (mod_mul hrMod hrMod) hrMod) hrMod) rfl)
  rw [h] at hmod
  have hnat : (r * r * r + 256 * r + 256) % 257 = 0 := by
    rw [← nat_emod_257] at hmod; omega
  exact no_root_257_nat r hrLt hnat

private theorem prime_257_mul_emod_zero (x y : Int) (h : (x * y) % 257 = 0) :
    x % 257 = 0 ∨ y % 257 = 0 := by
  let a : Nat := (x % 257).toNat
  let b : Nat := (y % 257).toNat
  have ha0 : 0 ≤ x % 257 := Int.emod_nonneg x (by decide)
  have hb0 : 0 ≤ y % 257 := Int.emod_nonneg y (by decide)
  have haHi : x % 257 < 257 := Int.emod_lt_of_pos x (by decide)
  have hbHi : y % 257 < 257 := Int.emod_lt_of_pos y (by decide)
  have haCast : (a : Int) = x % 257 := Int.toNat_of_nonneg ha0
  have hbCast : (b : Int) = y % 257 := Int.toNat_of_nonneg hb0
  by_cases hax : a = 0
  · left; omega
  · by_cases hby : b = 0
    · right; omega
    · exfalso
      have haLt : a < 257 := by omega
      have hbLt : b < 257 := by omega
      have haNe : a % toyPrime ≠ 0 := by
        change a % 257 ≠ 0
        rw [Nat.mod_eq_of_lt haLt]; exact hax
      have hinv := fInvMod_toy_spec a haNe
      have hab0 : (a * b) % 257 = 0 := by
        have hInt : ((a * b : Nat) : Int) % 257 = 0 := by
          rw [Int.natCast_mul, haCast, hbCast, ← Int.mul_emod]; exact h
        rw [← nat_emod_257] at hInt; omega
      have hinvMod : (a * fInvMod toyPrime a) % 257 = 1 := hinv.2
      have hb1 : b % 257 = 0 := by
        calc
          b % 257 = (1 * b) % 257 := by rw [Nat.one_mul]
          _ = (((a * fInvMod toyPrime a) % 257) * b) % 257 := by rw [hinvMod]
          _ = ((a * fInvMod toyPrime a) * b) % 257 := mul_mod_left_eq _ b 257
          _ = ((a * b) * fInvMod toyPrime a) % 257 := by
            rw [Nat.mul_assoc, Nat.mul_comm (fInvMod toyPrime a) b, ← Nat.mul_assoc]
          _ = (((a * b) % 257) * fInvMod toyPrime a) % 257 := (mul_mod_left_eq _ _ 257).symm
          _ = 0 := by rw [hab0, Nat.zero_mul, Nat.zero_mod]
      rw [Nat.mod_eq_of_lt hbLt] at hb1
      exact hby hb1

private theorem exists_inv_257_int (x : Int) (hx : x % 257 ≠ 0) :
    ∃ y : Int, (x * y) % 257 = 1 := by
  let a : Nat := (x % 257).toNat
  have ha0 : 0 ≤ x % 257 := Int.emod_nonneg x (by decide)
  have haHi : x % 257 < 257 := Int.emod_lt_of_pos x (by decide)
  have haLt : a < 257 := by omega
  have haCast : (a : Int) = x % 257 := Int.toNat_of_nonneg ha0
  have haNe : a % toyPrime ≠ 0 := by
    change a % 257 ≠ 0
    rw [Nat.mod_eq_of_lt haLt]; omega
  have hinv := fInvMod_toy_spec a haNe
  have hinvMod : (a * fInvMod toyPrime a) % 257 = 1 := hinv.2
  refine ⟨(fInvMod toyPrime a : Int), ?_⟩
  have hxEq : x % 257 = (a : Int) % 257 := by rw [haCast, Int.emod_emod]
  refine (mod_mul hxEq rfl).trans ?_
  rw [← Int.natCast_mul, ← nat_emod_257, hinvMod]
  rfl

private theorem int_emod_eq_of_sub_eq_zero (a b : Int) (h : (a - b) % 257 = 0) :
    a % 257 = b % 257 := by
  have hdvd : (257 : Int) ∣ a - b := Int.dvd_of_emod_eq_zero h
  rcases hdvd with ⟨k, hk⟩
  have ha : a = b + 257 * k := by omega
  rw [ha, Int.add_mul_emod_self_left]

/-- Exact polynomial multiplication expansion at `r` for degree-2 factors over `Int`. -/
private theorem quad_prod_eval (a0 a1 a2 d0 d1 d2 norm q0 q1 r : Int)
    (h1 : a2 * d2 = q1)
    (h2 : a1 * d2 + a2 * d1 = q0)
    (h3 : a0 * d2 + a1 * d1 + a2 * d0 = -q1)
    (h4 : a0 * d1 + a1 * d0 = -q0 - q1)
    (h5 : a0 * d0 - norm = -q0) :
    (a0 + a1 * r + a2 * r * r) * (d0 + d1 * r + d2 * r * r) - norm =
      (q0 + q1 * r) * (r * r * r - r - 1) := by
  have eLHS : (a0 + a1 * r + a2 * r * r) * (d0 + d1 * r + d2 * r * r) - norm =
      (a2 * d2) * (r * (r * (r * r))) + (a1 * d2 + a2 * d1) * (r * (r * r)) +
      (a0 * d2 + a1 * d1 + a2 * d0) * (r * r) + (a0 * d1 + a1 * d0) * r +
      (a0 * d0 - norm) := by
    have c1 : r * d0 = d0 * r := Int.mul_comm _ _
    have c2 : r * (d0 * r) = d0 * (r * r) := Int.mul_left_comm _ _ _
    have c3 : r * (d1 * r) = d1 * (r * r) := Int.mul_left_comm _ _ _
    have c4 : r * (d1 * (r * r)) = d1 * (r * (r * r)) := Int.mul_left_comm _ _ _
    have c5 : r * (d2 * (r * r)) = d2 * (r * (r * r)) := Int.mul_left_comm _ _ _
    have c6 : r * (d2 * (r * (r * r))) = d2 * (r * (r * (r * r))) := Int.mul_left_comm _ _ _
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, c1, c2, c3, c4, c5, c6]
    omega
  have eRHS : (q0 + q1 * r) * (r * r * r - r - 1) =
      q1 * (r * (r * (r * r))) + q0 * (r * (r * r)) + (-q1) * (r * r) +
      (-q0 - q1) * r + (-q0) := by
    simp only [Int.add_mul, Int.mul_sub, Int.sub_mul, Int.neg_mul, Int.mul_one, Int.mul_assoc]
    omega
  rw [eLHS, eRHS, h1, h2, h3, h4, h5]

/-- Exact degree-4 polynomial identity over `Int`:
`(a0 + a1·X + a2·X²)(d0 + d1·X + d2·X²) - N(a) = (q0 + q1·X)(X³ - X - 1)`
where `q0 = a1·d2 + a2·d1` and `q1 = a2·d2`, expressed as its 5 coefficients. -/
private theorem adj_poly_coeffs_int (a0 a1 a2 : Int) :
    let d0 := (a0 + a2) * (a0 + a2) - a1 * (a1 + a2)
    let d1 := a2 * a2 - a0 * a1
    let d2 := a1 * a1 - a2 * (a0 + a2)
    let norm := a0 * d0 + a2 * d1 + a1 * d2
    let q0 := a1 * d2 + a2 * d1
    let q1 := a2 * d2
    a2 * d2 = q1 ∧
    a1 * d2 + a2 * d1 = q0 ∧
    a0 * d2 + a1 * d1 + a2 * d0 = -q1 ∧
    a0 * d1 + a1 * d0 = -q0 - q1 ∧
    a0 * d0 - norm = -q0 := by
  dsimp only
  have hc := adj_cancel_int a0 a1 a2
  dsimp only at hc
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> omega

/-- Symmetric degree-4 factor cancellation lemma over $\mathbb{F}_{257}$:
if `u(X) v(X) ≡ (q0 + q1·X)(X³ - X - 1) (mod 257)` with `q1 ≢ 0`, `u2 ≢ 0`,
`q0 + q1·r ≡ 0`, and `u(r) ≡ 0`, then `u(X)/(X - r) = u2·X + (u1 + u2·r)` has a
root `r'` in $\mathbb{F}_{257}$ satisfying `r'³ - r' - 1 ≡ 0 (mod 257)` — contradiction! -/
private theorem quad_factor_contradiction (u0 u1 u2 v0 v1 v2 q0 q1 r : Int)
    (he4 : (u2 * v2 - q1) % 257 = 0)
    (he3 : (u1 * v2 + u2 * v1 - q0) % 257 = 0)
    (he2 : (u0 * v2 + u1 * v1 + u2 * v0 + q1) % 257 = 0)
    (he1 : (u0 * v1 + u1 * v0 + q0 + q1) % 257 = 0)
    (hq1 : q1 % 257 ≠ 0)
    (hu2 : u2 % 257 ≠ 0)
    (hqr : (q0 + q1 * r) % 257 = 0)
    (hur : (u0 + u1 * r + u2 * r * r) % 257 = 0) : False := by
  obtain ⟨u2inv, hu2inv⟩ := exists_inv_257_int u2 hu2
  let b0 : Int := u1 + u2 * r
  let b1 : Int := u2
  let r' : Int := -(b0 * u2inv)
  have hb0r' : (b0 + b1 * r') % 257 = 0 := by
    have h1 : b0 + b1 * r' = b0 * (1 - u2 * u2inv) := by
      dsimp only [b1, r']; rw [Int.mul_neg, Int.mul_sub, Int.mul_one, Int.mul_left_comm]; omega
    rw [h1, Int.mul_emod, Int.sub_emod, hu2inv]
    simp
  have h257 : ∀ A B : Int, A % 257 = 0 → B % 257 = 0 → (A + B) % 257 = 0 := by
    intro A B hA hB; rw [Int.add_emod, hA, hB]; rfl
  have h257mul : ∀ A B : Int, A % 257 = 0 → (A * B) % 257 = 0 := by
    intro A B hA; rw [Int.mul_emod, hA]; simp
  have hc3 : (b1 * v2 - q1) % 257 = 0 := he4
  have hc2 : (b0 * v2 + b1 * v1) % 257 = 0 := by
    have h := h257 _ _ (h257 _ _ he3 (h257mul _ r he4)) hqr
    have hid : (u1 * v2 + u2 * v1 - q0) + (u2 * v2 - q1) * r + (q0 + q1 * r) =
        b0 * v2 + b1 * v1 := by
      dsimp only [b0, b1]
      have c1 : r * v2 = v2 * r := Int.mul_comm _ _
      simp only [Int.add_mul, Int.sub_mul, Int.mul_assoc, c1]
      omega
    rwa [hid] at h
  have hc1 : (b0 * v1 + b1 * v0 + q1) % 257 = 0 := by
    have h := h257 _ _ (h257 _ _ he2 (h257mul _ r hc2)) (h257mul _ (-v2) hur)
    have hid : (u0 * v2 + u1 * v1 + u2 * v0 + q1) + (b0 * v2 + b1 * v1) * r +
        (u0 + u1 * r + u2 * r * r) * (-v2) = b0 * v1 + b1 * v0 + q1 := by
      dsimp only [b0, b1]
      have c1 : r * v2 = v2 * r := Int.mul_comm _ _
      have c2 : r * v1 = v1 * r := Int.mul_comm _ _
      have c3 : r * (v2 * r) = v2 * (r * r) := Int.mul_left_comm _ _ _
      simp only [Int.add_mul, Int.mul_neg, Int.mul_assoc, c1, c2, c3]
      omega
    rwa [hid] at h
  have hc0 : (b0 * v0 + q1) % 257 = 0 := by
    have h1 := h257 _ _ he1 (h257mul _ (-1) hqr)
    have h2 := h257 _ _ (h257 _ _ h1 (h257mul _ r hc1)) (h257mul _ (-v1) hur)
    have hid : ((u0 * v1 + u1 * v0 + q0 + q1) + (q0 + q1 * r) * (-1)) +
        (b0 * v1 + b1 * v0 + q1) * r + (u0 + u1 * r + u2 * r * r) * (-v1) =
        b0 * v0 + q1 := by
      dsimp only [b0, b1]
      have c1 : r * v1 = v1 * r := Int.mul_comm _ _
      have c2 : r * v0 = v0 * r := Int.mul_comm _ _
      have c3 : r * (v1 * r) = v1 * (r * r) := Int.mul_left_comm _ _ _
      simp only [Int.add_mul, Int.mul_neg, Int.mul_one, Int.mul_assoc, c1, c2, c3]
      omega
    rwa [hid] at h2
  have hcomb : ((b1 * v2 - q1) * (r' * r' * r') + (b0 * v2 + b1 * v1) * (r' * r')
      + (b0 * v1 + b1 * v0 + q1) * r' + (b0 * v0 + q1)) % 257 = 0 :=
    h257 _ _ (h257 _ _ (h257 _ _ (h257mul _ _ hc3) (h257mul _ _ hc2)) (h257mul _ _ hc1)) hc0
  have hcomb2 : ((b0 + b1 * r') * (v0 + v1 * r' + v2 * (r' * r'))
      - q1 * (r' * r' * r' - r' - 1)) % 257 = 0 := by
    have hid : (b1 * v2 - q1) * (r' * r' * r') + (b0 * v2 + b1 * v1) * (r' * r')
        + (b0 * v1 + b1 * v0 + q1) * r' + (b0 * v0 + q1) =
        (b0 + b1 * r') * (v0 + v1 * r' + v2 * (r' * r')) - q1 * (r' * r' * r' - r' - 1) := by
      have s1 : r' * v0 = v0 * r' := Int.mul_comm _ _
      have s2 : r' * (v1 * r') = v1 * (r' * r') := Int.mul_left_comm _ _ _
      have s3 : r' * (v2 * (r' * r')) = v2 * (r' * (r' * r')) := Int.mul_left_comm _ _ _
      simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc,
        s1, s2, s3]
      omega
    rwa [hid] at hcomb
  have hq1f : (q1 * (r' * r' * r' - r' - 1)) % 257 = 0 := by
    have h0 := h257mul _ (v0 + v1 * r' + v2 * (r' * r')) hb0r'
    have hsub := int_emod_eq_of_sub_eq_zero _ _ hcomb2
    rw [h0] at hsub
    exact hsub.symm
  rcases prime_257_mul_emod_zero _ _ hq1f with hq1z | hroot
  · exact hq1 hq1z
  · exact no_root_257_int r' hroot

private theorem cubic_scale_id (r t : Int) :
    (r * r * r - r - 1) * (t * t * t) =
      (r * t) * (r * t) * (r * t) - (r * t) * (t * t) - t * t * t := by
  have c1 : r * t = r * t := rfl
  have c2 : t * r = r * t := Int.mul_comm _ _
  have c3 : t * (r * t) = r * (t * t) := Int.mul_left_comm _ _ _
  have c4 : t * (r * (r * (t * t))) = r * (t * (r * (t * t))) := Int.mul_left_comm _ _ _
  have c5 : t * (r * (t * t)) = r * (t * (t * t)) := Int.mul_left_comm _ _ _
  have hcub : r * (r * (r * (t * (t * t)))) = (r * t) * ((r * t) * (r * t)) := by
    calc
      r * (r * (r * (t * (t * t))))
        = r * (r * (t * (r * (t * t)))) := by rw [Int.mul_left_comm r t (t * t)]
      _ = r * (t * (r * (r * (t * t)))) := by rw [Int.mul_left_comm r t (r * (t * t))]
      _ = r * (t * (r * (t * (r * t)))) := by rw [Int.mul_left_comm r t t]
      _ = (r * t) * ((r * t) * (r * t)) := by simp only [Int.mul_assoc]
  simp only [Int.sub_mul, Int.one_mul, Int.mul_assoc]
  rw [hcub]
  simp only [Int.mul_assoc]

private theorem fp3Norm_ne_zero_257 (a : Fp3) (hnez : fp3IsZeroMod toyPrime a = false) :
    fp3Norm toyPrime a % toyPrime ≠ 0 := by
  intro hnormZ
  have hnormZ' : ((fp3Norm toyPrime a : Nat) : Int) % 257 = 0 := by
    rw [← nat_emod_257]; exact Int.ofNat_eq_zero.mpr hnormZ
  let a0 : Int := a.c0
  let a1 : Int := a.c1
  let a2 : Int := a.c2
  let d0 : Int := (a0 + a2) * (a0 + a2) - a1 * (a1 + a2)
  let d1 : Int := a2 * a2 - a0 * a1
  let d2 : Int := a1 * a1 - a2 * (a0 + a2)
  let norm : Int := a0 * d0 + a2 * d1 + a1 * d2
  let q0 : Int := a1 * d2 + a2 * d1
  let q1 : Int := a2 * d2
  have hadj := fp3Adj_int_emod toyPrime (by decide) a
  have hnormEq : norm % 257 = 0 := by
    have h1 : ((fp3Norm toyPrime a : Nat) : Int) % 257 = norm % 257 := by
      dsimp only [fp3Norm, norm]
      exact (int_addMod_emod 257 _ _).trans <|
        mod_add ((int_addMod_emod 257 _ _).trans
          (mod_add ((int_mulMod_emod 257 _ _).trans (mod_mul rfl hadj.1))
            ((int_mulMod_emod 257 _ _).trans (mod_mul rfl hadj.2.1))))
          ((int_mulMod_emod 257 _ _).trans (mod_mul rfl hadj.2.2))
    exact h1.symm.trans hnormZ'
  have hnotAllZero : a0 % 257 ≠ 0 ∨ a1 % 257 ≠ 0 ∨ a2 % 257 ≠ 0 := by
    dsimp only [fp3IsZeroMod, toyPrime] at hnez
    by_cases c0 : a.c0 % 257 = 0
    · by_cases c1 : a.c1 % 257 = 0
      · by_cases c2 : a.c2 % 257 = 0
        · simp [c0, c1, c2] at hnez
        · right; right; dsimp only [a2]; rw [← nat_emod_257]; omega
      · right; left; dsimp only [a1]; rw [← nat_emod_257]; omega
    · left; dsimp only [a0]; rw [← nat_emod_257]; omega
  by_cases ha2 : a2 % 257 = 0
  · by_cases ha1 : a1 % 257 = 0
    · have ha0 : a0 % 257 ≠ 0 := by
        rcases hnotAllZero with h | h | h
        · exact h
        · exact False.elim (h ha1)
        · exact False.elim (h ha2)
      have hstep : norm % 257 = (a0 * (a0 * a0)) % 257 := by
        dsimp only [norm, d0, d1, d2]
        have ha2z : a2 % 257 = (0 : Int) % 257 := ha2
        have ha1z : a1 % 257 = (0 : Int) % 257 := ha1
        refine (mod_add (mod_add (mod_mul rfl (mod_sub (mod_mul (mod_add rfl ha2z) (mod_add rfl ha2z))
          (mod_mul ha1z rfl))) (mod_mul ha2z rfl)) (mod_mul ha1z rfl)).trans ?_
        congr 1; simp only [Int.add_zero, Int.zero_mul, Int.sub_zero]
      have ha0cube : (a0 * (a0 * a0)) % 257 = 0 := hstep.symm.trans hnormEq
      rcases prime_257_mul_emod_zero _ _ ha0cube with h0 | h00
      · exact ha0 h0
      · rcases prime_257_mul_emod_zero _ _ h00 with h0 | h0 <;> exact ha0 h0
    · obtain ⟨a1inv, ha1inv⟩ := exists_inv_257_int a1 ha1
      let r : Int := -(a0 * a1inv)
      have hpoly : (a0 * a0 * a0 - a0 * a1 * a1 + a1 * a1 * a1) % 257 = 0 := by
        have hstep : norm % 257 = (a0 * a0 * a0 - a0 * a1 * a1 + a1 * a1 * a1) % 257 := by
          dsimp only [norm, d0, d1, d2]
          have ha2z : a2 % 257 = (0 : Int) % 257 := ha2
          refine (mod_add (mod_add (mod_mul rfl (mod_sub (mod_mul (mod_add rfl ha2z) (mod_add rfl ha2z))
            (mod_mul rfl (mod_add rfl ha2z)))) (mod_mul ha2z rfl))
            (mod_mul rfl (mod_sub rfl (mod_mul ha2z rfl)))).trans ?_
          congr 1; simp only [Int.add_zero, Int.zero_mul, Int.sub_zero, Int.mul_sub, Int.mul_assoc]
        exact hstep.symm.trans hnormEq
      have hroot : (r * r * r - r - 1) % 257 = 0 := by
        have h1 : (r * a1) % 257 = (-a0) % 257 := by
          have hr1 : r * a1 = (-a0) * (a1 * a1inv) := by
            dsimp only [r]; rw [Int.neg_mul, Int.neg_mul, Int.mul_assoc, Int.mul_comm a1inv a1]
          rw [hr1, Int.mul_emod, ha1inv]; simp
        have hscale : ((r * r * r - r - 1) * (a1 * a1 * a1)) % 257 = 0 := by
          rw [cubic_scale_id r a1]
          refine (mod_sub (mod_sub (mod_mul (mod_mul h1 h1) h1) (mod_mul h1 rfl)) rfl).trans ?_
          have hneg : ((-a0) * (-a0) * (-a0) - (-a0) * (a1 * a1) - a1 * a1 * a1) =
              -(a0 * a0 * a0 - a0 * a1 * a1 + a1 * a1 * a1) := by
            simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_assoc]; omega
          rw [hneg]
          have hpolyz : (a0 * a0 * a0 - a0 * a1 * a1 + a1 * a1 * a1) % 257 = (0 : Int) % 257 := hpoly
          exact (mod_neg hpolyz).trans rfl
        rcases prime_257_mul_emod_zero _ _ hscale with hr0 | ha1cube
        · exact hr0
        · rcases prime_257_mul_emod_zero _ _ ha1cube with ha12 | h1
          · rcases prime_257_mul_emod_zero _ _ ha12 with h1 | h1 <;> exact False.elim (ha1 h1)
          · exact False.elim (ha1 h1)
      exact no_root_257_int r hroot
  · by_cases hd2 : d2 % 257 = 0
    · by_cases hd1 : d1 % 257 = 0
      · obtain ⟨a2inv, ha2inv⟩ := exists_inv_257_int a2 ha2
        let r : Int := a1 * a2inv
        have hrel : (a1 * a1 * a1 - a1 * (a2 * a2) - a2 * a2 * a2) % 257 = 0 := by
          have hdiff : ((a1 * d2 + a2 * d1) - 2 * (a2 * d1)) % 257 = 0 := by
            have hd2z : d2 % 257 = (0 : Int) % 257 := hd2
            have hd1z : d1 % 257 = (0 : Int) % 257 := hd1
            exact (mod_sub (mod_add (mod_mul rfl hd2z) (mod_mul rfl hd1z))
              (mod_mul rfl (mod_mul rfl hd1z))).trans rfl
          have hid2 : (a1 * d2 + a2 * d1) - 2 * (a2 * d1) =
              a1 * a1 * a1 - a1 * (a2 * a2) - a2 * a2 * a2 := by
            dsimp only [d1, d2]
            have c1 : a1 * (a2 * a0) = a0 * (a1 * a2) := by
              rw [Int.mul_comm a2 a0, Int.mul_left_comm]
            have c2 : a2 * (a0 * a1) = a0 * (a1 * a2) := by
              rw [Int.mul_left_comm a2 a0, Int.mul_comm a2 a1]
            simp only [Int.mul_sub, Int.mul_add, Int.mul_assoc, c1, c2]; omega
          rwa [hid2] at hdiff
        have hscale : ((r * r * r - r - 1) * (a2 * a2 * a2)) % 257 = 0 := by
          have hra2 : (r * a2) % 257 = a1 % 257 := by
            have hr1 : r * a2 = a1 * (a2 * a2inv) := by
              dsimp only [r]; rw [Int.mul_assoc, Int.mul_comm a2inv a2]
            rw [hr1, Int.mul_emod, ha2inv]; simp
          rw [cubic_scale_id r a2]
          exact (mod_sub (mod_sub (mod_mul (mod_mul hra2 hra2) hra2) (mod_mul hra2 rfl)) rfl).trans hrel
        rcases prime_257_mul_emod_zero _ _ hscale with hroot | ha2cube
        · exact no_root_257_int r hroot
        · rcases prime_257_mul_emod_zero _ _ ha2cube with ha22 | h2
          · rcases prime_257_mul_emod_zero _ _ ha22 with h2 | h2 <;> exact ha2 h2
          · exact ha2 h2
      · obtain ⟨d1inv, hd1inv⟩ := exists_inv_257_int d1 hd1
        let r : Int := -(d0 * d1inv)
        have hpoly := adj_poly_coeffs_int a0 a1 a2
        dsimp only at hpoly
        have hq0ne : q0 % 257 ≠ 0 := by
          intro hq0z
          have hd2z : d2 % 257 = (0 : Int) % 257 := hd2
          have hq0eq : q0 % 257 = (a2 * d1) % 257 := by
            dsimp only [q0]
            exact (mod_add (mod_mul rfl hd2z) rfl).trans (by simp)
          rcases prime_257_mul_emod_zero _ _ (hq0eq.symm.trans hq0z) with h | h
          · exact ha2 h
          · exact hd1 h
        have hq1z : q1 % 257 = 0 := by
          dsimp only [q1]
          have hd2z : d2 % 257 = (0 : Int) % 257 := hd2
          exact (mod_mul rfl hd2z).trans (by simp)
        have hd01r : (d0 + d1 * r) % 257 = 0 := by
          have : d0 + d1 * r = d0 * (1 - d1 * d1inv) := by
            dsimp only [r]; rw [Int.mul_neg, Int.mul_sub, Int.mul_one, Int.mul_left_comm]; omega
          rw [this, Int.mul_emod d0, Int.sub_emod 1, hd1inv]; simp
        have heval := quad_prod_eval a0 a1 a2 d0 d1 d2 norm q0 q1 r
          hpoly.1 hpoly.2.1 hpoly.2.2.1 hpoly.2.2.2.1 hpoly.2.2.2.2
        have hlhs0 : ((a0 + a1 * r + a2 * r * r) * (d0 + d1 * r + d2 * r * r) - norm) % 257 = 0 := by
          have hd2z : d2 % 257 = (0 : Int) % 257 := hd2
          have hd01rz : (d0 + d1 * r) % 257 = (0 : Int) % 257 := hd01r
          have hdr0 : (d0 + d1 * r + d2 * r * r) % 257 = (0 : Int) % 257 :=
            (mod_add hd01rz (mod_mul (mod_mul hd2z rfl) rfl)).trans (by simp)
          have hnormz : norm % 257 = (0 : Int) % 257 := hnormEq
          exact (mod_sub (mod_mul rfl hdr0) hnormz).trans (by simp)
        rw [heval] at hlhs0
        have hq0f : (q0 * (r * r * r - r - 1)) % 257 = 0 := by
          have hq1z' : q1 % 257 = (0 : Int) % 257 := hq1z
          have hstep : ((q0 + q1 * r) * (r * r * r - r - 1)) % 257 =
              (q0 * (r * r * r - r - 1)) % 257 :=
            (mod_mul (mod_add rfl (mod_mul hq1z' rfl)) rfl).trans (by simp)
          exact hstep.symm.trans hlhs0
        rcases prime_257_mul_emod_zero _ _ hq0f with h | h
        · exact hq0ne h
        · exact no_root_257_int r h
    · have hq1ne : q1 % 257 ≠ 0 := by
        intro h
        rcases prime_257_mul_emod_zero a2 d2 h with h1 | h2
        · exact ha2 h1
        · exact hd2 h2
      obtain ⟨q1inv, hq1inv⟩ := exists_inv_257_int q1 hq1ne
      let r : Int := -(q0 * q1inv)
      have hqr : (q0 + q1 * r) % 257 = 0 := by
        have : q0 + q1 * r = q0 * (1 - q1 * q1inv) := by
          dsimp only [r]; rw [Int.mul_neg, Int.mul_sub, Int.mul_one, Int.mul_left_comm]; omega
        rw [this, Int.mul_emod q0, Int.sub_emod 1, hq1inv]; simp
      have hpoly := adj_poly_coeffs_int a0 a1 a2
      dsimp only at hpoly
      have hhe4 : (a2 * d2 - q1) % 257 = 0 := by
        have : a2 * d2 - q1 = 0 := by dsimp only [q1]; omega
        rw [this]; rfl
      have hhe3 : (a1 * d2 + a2 * d1 - q0) % 257 = 0 := by
        have : a1 * d2 + a2 * d1 - q0 = 0 := by dsimp only [q0]; omega
        rw [this]; rfl
      have hhe2 : (a0 * d2 + a1 * d1 + a2 * d0 + q1) % 257 = 0 := by
        have : a0 * d2 + a1 * d1 + a2 * d0 + q1 = 0 := by
          have := hpoly.2.2.1; dsimp only [d0, d1, d2, q1]; omega
        rw [this]; rfl
      have hhe1 : (a0 * d1 + a1 * d0 + q0 + q1) % 257 = 0 := by
        have : a0 * d1 + a1 * d0 + q0 + q1 = 0 := by
          have := hpoly.2.2.2.1; dsimp only [d0, d1, d2, q0, q1]; omega
        rw [this]; rfl
      have heval := quad_prod_eval a0 a1 a2 d0 d1 d2 norm q0 q1 r
        hpoly.1 hpoly.2.1 hpoly.2.2.1 hpoly.2.2.2.1 hpoly.2.2.2.2
      have hprod0 : ((a0 + a1 * r + a2 * r * r) * (d0 + d1 * r + d2 * r * r)) % 257 = 0 := by
        have hsub : ((a0 + a1 * r + a2 * r * r) * (d0 + d1 * r + d2 * r * r) - norm) % 257 = 0 := by
          rw [heval]
          have hqrz : (q0 + q1 * r) % 257 = (0 : Int) % 257 := hqr
          exact (mod_mul hqrz rfl).trans (by simp)
        exact (int_emod_eq_of_sub_eq_zero _ _ hsub).trans hnormEq
      rcases prime_257_mul_emod_zero _ _ hprod0 with har | hdr
      · exact quad_factor_contradiction a0 a1 a2 d0 d1 d2 q0 q1 r
          hhe4 hhe3 hhe2 hhe1 hq1ne ha2 hqr har
      · exact quad_factor_contradiction d0 d1 d2 a0 a1 a2 q0 q1 r
          (by rw [Int.mul_comm d2 a2]; exact hhe4)
          (by rw [Int.mul_comm d1 a2, Int.mul_comm d2 a1, Int.add_comm]; exact hhe3)
          (by rw [Int.mul_comm d0 a2, Int.mul_comm d1 a1, Int.mul_comm d2 a0];
              have : a2 * d0 + a1 * d1 + a0 * d2 + q1 = a0 * d2 + a1 * d1 + a2 * d0 + q1 := by omega
              rw [this]; exact hhe2)
          (by rw [Int.mul_comm d0 a1, Int.mul_comm d1 a0, Int.add_comm (a1 * d0)]; exact hhe1)
          hq1ne hd2 hqr hdr

private theorem fp3Eq_eq_one_iff (a b : Fp3) : fp3Eq a b = 1 ↔ a = b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  unfold fp3Eq
  by_cases h0 : a0 = b0
  · subst h0; simp only [beq_self_eq_true, ↓reduceIte]
    by_cases h1 : a1 = b1
    · subst h1; simp only [beq_self_eq_true, ↓reduceIte]
      by_cases h2 : a2 = b2
      · subst h2; simp
      · have h2b : (a2 == b2) = false := beq_false_of_ne h2
        simp [h2b, h2]
    · have h1b : (a1 == b1) = false := beq_false_of_ne h1
      simp [h1b, h1]
  · have h0b : (a0 == b0) = false := beq_false_of_ne h0
    simp [h0b, h0]

private theorem fp3Inv_toy_spec (a : Fp3) (hnez : fp3IsZeroMod toyPrime a = false) :
    fp3Canonical toyPrime (fp3Inv toyPrime a) = true ∧
    fp3Mul toyPrime a (fp3Inv toyPrime a) = fp3One := by
  unfold fp3Inv
  have h2 : ¬ (toyPrime < 2) := by decide
  simp only [h2, hnez, Bool.false_eq_true, ↓reduceIte]
  have hnormNe : fp3Norm toyPrime a % toyPrime ≠ 0 := fp3Norm_ne_zero_257 a hnez
  have hinv := fInvMod_toy_spec (fp3Norm toyPrime a) hnormNe
  have hp : 0 < toyPrime := by decide
  refine ⟨?_, ?_⟩
  · unfold fp3Canonical fp3Scale
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩, Nat.mod_lt _ hp⟩
  · have hnormDef : addMod toyPrime (addMod toyPrime (mulMod toyPrime a.c0 (fp3Adj toyPrime a).c0)
        (mulMod toyPrime a.c2 (fp3Adj toyPrime a).c1))
        (mulMod toyPrime a.c1 (fp3Adj toyPrime a).c2) = fp3Norm toyPrime a := rfl
    rw [hnormDef, fp3Mul_scale_right toyPrime hp a (fp3Adj toyPrime a),
      fp3Mul_adj_eq_norm toyPrime hp a]
    dsimp only [fp3Scale, fp3OfBase, fp3One, mulMod]
    rw [hinv.2, Nat.zero_mul, Nat.zero_mod]

/-- **Tier-2 `guess` #3 (`checked def ... complete by`)**: concrete-prime (`p = 257`)
cubic extension field inverse `a⁻¹ ∈ F_257[X]/(X^3 - X - 1)`.
Its non-circular checker verifies ONLY `fp3Canonical 257 r` and
`fp3Eq (fp3Mul 257 a r) fp3One == 1` (eliminating the entire adjugate + Euclid
tower from the STARK circuit!), with both kernel-checked uniqueness (`by`) AND
full unconditional completeness (`complete by`). -/
@[circuit_noinline]
checked def fp3InvToy (a : Fp3) : Fp3 :=
  hint fp3Inv toyPrime a
  where check fun r =>
    if fp3IsZeroMod toyPrime a then fp3Eq r fp3Zero == 1
    else fp3Canonical toyPrime r && (fp3Eq (fp3Mul toyPrime a r) fp3One == 1)
  by
    intro res hr
    unfold fp3InvToy.check at hr
    unfold fp3InvToy
    by_cases haz : fp3IsZeroMod toyPrime a = true
    · rw [haz] at hr
      simp only [↓reduceIte, beq_iff_eq] at hr
      have hresZ : res = fp3Zero := (fp3Eq_eq_one_iff res fp3Zero).mp hr
      unfold fp3Inv
      have h2 : ¬ (toyPrime < 2) := by decide
      simp only [h2, haz, ↓reduceIte]
      exact hresZ
    · have hazF : fp3IsZeroMod toyPrime a = false := Bool.eq_false_iff.mpr haz
      rw [hazF] at hr
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨hcanRes, hmulResEq⟩ := hr
      have hmulRes : fp3Mul toyPrime a res = fp3One := (fp3Eq_eq_one_iff _ _).mp hmulResEq
      have hspec := fp3Inv_toy_spec a hazF
      have hp : 0 < toyPrime := by decide
      unfold fp3Canonical at hcanRes
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcanRes
      have hcanInv := hspec.1
      unfold fp3Canonical at hcanInv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcanInv
      calc
        res = fp3Mul toyPrime res fp3One :=
          (fp3Mul_one_right toyPrime hp res hcanRes.1.1 hcanRes.1.2 hcanRes.2).symm
        _ = fp3Mul toyPrime res (fp3Mul toyPrime a (fp3Inv toyPrime a)) := by rw [hspec.2]
        _ = fp3Mul toyPrime (fp3Mul toyPrime res a) (fp3Inv toyPrime a) :=
          (fp3Mul_assoc toyPrime hp res a (fp3Inv toyPrime a)).symm
        _ = fp3Mul toyPrime (fp3Mul toyPrime a res) (fp3Inv toyPrime a) := by
          rw [fp3Mul_comm toyPrime hp res a]
        _ = fp3Mul toyPrime fp3One (fp3Inv toyPrime a) := by rw [hmulRes]
        _ = fp3Mul toyPrime (fp3Inv toyPrime a) fp3One :=
          fp3Mul_comm toyPrime hp fp3One (fp3Inv toyPrime a)
        _ = fp3Inv toyPrime a :=
          fp3Mul_one_right toyPrime hp (fp3Inv toyPrime a) hcanInv.1.1 hcanInv.1.2 hcanInv.2
  complete by
    unfold fp3InvToy.check fp3InvToy
    by_cases haz : fp3IsZeroMod toyPrime a = true
    · rw [haz]
      unfold fp3Inv
      have h2 : ¬ (toyPrime < 2) := by decide
      simp only [h2, haz, ↓reduceIte, beq_iff_eq]
      exact (fp3Eq_eq_one_iff fp3Zero fp3Zero).mpr rfl
    · have hazF : fp3IsZeroMod toyPrime a = false := Bool.eq_false_iff.mpr haz
      rw [hazF]
      have hspec := fp3Inv_toy_spec a hazF
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq]
      exact ⟨hspec.1, (fp3Eq_eq_one_iff _ _).mpr hspec.2⟩

/-! ## Subgroup, Bit-Reversal, and Multi-Arity FRI Folding Core (`Pcs.lean` + Plonky3) -/

/-- Repeated squaring `value^(2^log) mod p` (structural countdown, 0 depth cols). -/
@[circuit_noinline]
def expPower2 (p value : Nat) : Nat → Nat
  | 0 => value
  | log + 1 => expPower2 p (mulMod p value value) log
termination_by structural log => log

/-- Primitive `2^log`-th root of unity (`StarkVerifier::two_adic_gen`). -/
@[circuit_inline]
def twoAdicGen (fp : FriParams) (log : Nat) : Nat :=
  expPower2 fp.p fp.genMax (fp.maxLog - log)

/-- Reverse an LSB-first bit list (`Pcs::glist_rev`). -/
@[circuit_noinline]
def bitListRev (bits acc : BitList) : BitList :=
  match bits with
  | .nil => acc
  | .cons b rest => bitListRev rest (.cons b acc)
termination_by structural bits

/-- Drop the `n` least-significant bits (`Lists::drop`). -/
@[circuit_noinline]
def bitListDrop (n : Nat) (bits : BitList) : BitList :=
  match n with
  | 0 => bits
  | n' + 1 =>
    match bits with
    | .nil => .nil
    | .cons _ rest => bitListDrop n' rest
termination_by structural n

/-- Conditional base-field multiplication helper avoiding join-point splitting
inside `expByBits` (keeps 0 depth columns under `Depth.Structural`). -/
@[circuit_noinline]
def condMul (p bit base half : Nat) : Nat :=
  if bit == 0 then half else mulMod p base half

/-- Binary exponentiation `base^(bitsToNum bits) mod p` (`Pcs::exp_by_bits`). -/
@[circuit_noinline]
def expByBits (p base : Nat) : BitList → Nat
  | .nil => 1
  | .cons b rest =>
    let half := expByBits p (mulMod p base base) rest
    condMul p b base half
termination_by structural bits => bits

/-- Encode an 8-bit query index `idx < 256` as an 8-element LSB-first `BitList`. -/
@[circuit_noinline]
def bitsOf8 (idx : Nat) : BitList :=
  let b0 := idx % 2; let q1 := idx / 2
  let b1 := q1 % 2;  let q2 := q1 / 2
  let b2 := q2 % 2;  let q3 := q2 / 2
  let b3 := q3 % 2;  let q4 := q3 / 2
  let b4 := q4 % 2;  let q5 := q4 / 2
  let b5 := q5 % 2;  let q6 := q5 / 2
  let b6 := q6 % 2;  let b7 := q6 / 2
  .cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons b4 (.cons b5 (.cons b6 (.cons b7 .nil)))))))

/-- Core degree-2 FRI butterfly step:
`((e0 + e1) * inv2) + beta * ((e0 - e1) * inv2x)`
matching `MultiStark/Modules/Pcs.lean::fri_fold2` lines 157–163. -/
@[circuit_noinline]
def friFold2Step (p inv2 inv2x : Nat) (beta e0 e1 : Fp3) : Fp3 :=
  let sumHalf := fp3Scale p (fp3Add p e0 e1) inv2
  let diffDiv := fp3Scale p (fp3Sub p e0 e1) inv2x
  fp3Add p sumHalf (fp3Mul p beta diffDiv)

/-- Binary (`log_arity = 1`, arity 2) FRI fold (`Pcs::fri_fold2`).
Given `parentBits` (length `logFolded`, LSB-first), computes
`s = twoAdicGen(logFolded + 1)^(revBits(parentBits))`, `inv2s = (2 * s)⁻¹`,
and returns `((e0 + e1) / 2) + beta * ((e0 - e1) / (2 * s))`. -/
@[circuit_noinline]
def friFold2 (fp : FriParams) (parentBits : BitList) (logFolded : Nat)
    (beta e0 e1 : Fp3) : Fp3 :=
  let g := twoAdicGen fp (logFolded + 1)
  let s := expByBits fp.p g (bitListRev parentBits .nil)
  let inv2s := fInvMod fp.p (addMod fp.p s s)
  friFold2Step fp.p fp.inv2 inv2s beta e0 e1

/-- Arity-4 (`log_arity = 2`, `mla = 2`) FRI fold via 2-stage binary butterfly
matching Plonky3 `TwoAdicFriFolding::fold_row` / `fold_matrix` over bit-reversed
coset points `[s, -s, s·w₂, -s·w₂]` using a single base-field inversion `inv2s`. -/
@[circuit_noinline]
def friFold4 (fp : FriParams) (parentBits : BitList) (logFolded : Nat)
    (beta e0 e1 e2 e3 : Fp3) : Fp3 :=
  let g := twoAdicGen fp (logFolded + 2)
  let s := expByBits fp.p g (bitListRev parentBits .nil)
  let inv2s := fInvMod fp.p (addMod fp.p s s)
  let inv2sw := mulMod fp.p inv2s fp.w2Inv
  let f0 := friFold2Step fp.p fp.inv2 inv2s beta e0 e1
  let f1 := friFold2Step fp.p fp.inv2 inv2sw beta e2 e3
  let sq := mulMod fp.p inv2s inv2s
  let inv2s2 := addMod fp.p sq sq
  let beta2 := fp3Square fp.p beta
  friFold2Step fp.p fp.inv2 inv2s2 beta2 f0 f1

/-- Arity-8 (`log_arity = 3`, `mla = 3` Endpoint 1) FRI fold via 3-stage binary
butterfly matching Plonky3 `TwoAdicFriFolding::fold_row` / `fold_matrix` over
bit-reversed coset points `[s, -s, s·w₃², -s·w₃², s·w₃, -s·w₃, s·w₃³, -s·w₃³]`
using a single base-field inversion `inv2s`. -/
@[circuit_noinline]
def friFold8 (fp : FriParams) (parentBits : BitList) (logFolded : Nat)
    (beta e0 e1 e2 e3 e4 e5 e6 e7 : Fp3) : Fp3 :=
  let g := twoAdicGen fp (logFolded + 3)
  let s := expByBits fp.p g (bitListRev parentBits .nil)
  let inv2s := fInvMod fp.p (addMod fp.p s s)
  let w1 := fp.w3Inv
  let w2 := mulMod fp.p w1 w1
  let w3 := mulMod fp.p w2 w1
  let g0 := friFold2Step fp.p fp.inv2 inv2s beta e0 e1
  let g1 := friFold2Step fp.p fp.inv2 (mulMod fp.p inv2s w2) beta e2 e3
  let g2 := friFold2Step fp.p fp.inv2 (mulMod fp.p inv2s w1) beta e4 e5
  let g3 := friFold2Step fp.p fp.inv2 (mulMod fp.p inv2s w3) beta e6 e7
  let sq1 := mulMod fp.p inv2s inv2s
  let inv2s2 := addMod fp.p sq1 sq1
  let beta2 := fp3Square fp.p beta
  let h0 := friFold2Step fp.p fp.inv2 inv2s2 beta2 g0 g1
  let h1 := friFold2Step fp.p fp.inv2 (mulMod fp.p inv2s2 w2) beta2 g2 g3
  let sq2 := mulMod fp.p inv2s2 inv2s2
  let inv2s4 := addMod fp.p sq2 sq2
  let beta4 := fp3Square fp.p beta2
  friFold2Step fp.p fp.inv2 inv2s4 beta4 h0 h1

/-- Multi-arity FRI fold dispatching across `logArity ∈ {1, 2, 3}` over a full
coset evaluation list `evals` of length `2^logArity`. Uses `if ... == ...` and
single-level ADT matches so `IxCC.Fir.ShapeInfer` generates zero `match_N` closures. -/
@[circuit_noinline]
def friFoldArity (fp : FriParams) (logArity : Nat) (parentBits : BitList)
    (logFolded : Nat) (beta : Fp3) (evals : Fp3List) : Fp3 :=
  if logArity == 1 then
    match evals with
    | .nil => fp3Zero
    | .cons e0 t0 =>
      match t0 with
      | .nil => fp3Zero
      | .cons e1 t1 =>
        match t1 with
        | .nil => friFold2 fp parentBits logFolded beta e0 e1
        | .cons _ _ => fp3Zero
  else if logArity == 2 then
    match evals with
    | .nil => fp3Zero
    | .cons e0 t0 =>
      match t0 with
      | .nil => fp3Zero
      | .cons e1 t1 =>
        match t1 with
        | .nil => fp3Zero
        | .cons e2 t2 =>
          match t2 with
          | .nil => fp3Zero
          | .cons e3 t3 =>
            match t3 with
            | .nil => friFold4 fp parentBits logFolded beta e0 e1 e2 e3
            | .cons _ _ => fp3Zero
  else if logArity == 3 then
    match evals with
    | .nil => fp3Zero
    | .cons e0 t0 =>
      match t0 with
      | .nil => fp3Zero
      | .cons e1 t1 =>
        match t1 with
        | .nil => fp3Zero
        | .cons e2 t2 =>
          match t2 with
          | .nil => fp3Zero
          | .cons e3 t3 =>
            match t3 with
            | .nil => fp3Zero
            | .cons e4 t4 =>
              match t4 with
              | .nil => fp3Zero
              | .cons e5 t5 =>
                match t5 with
                | .nil => fp3Zero
                | .cons e6 t6 =>
                  match t6 with
                  | .nil => fp3Zero
                  | .cons e7 t7 =>
                    match t7 with
                    | .nil => friFold8 fp parentBits logFolded beta e0 e1 e2 e3 e4 e5 e6 e7
                    | .cons _ _ => fp3Zero
  else fp3Zero

/-- Reconstruct arity-2 sibling row from `(b0, folded, [s0])` (`Pcs::recon_evals`). -/
@[circuit_noinline]
def reconEvals2 (b0 : Nat) (folded : Fp3) (sibs : Fp3List) : Evals2 :=
  let bad : Evals2 := { ok := 0, e0 := fp3Zero, e1 := fp3Zero }
  match sibs with
  | .nil => bad
  | .cons s0 t0 =>
    match t0 with
    | .cons _ _ => bad
    | .nil =>
      if b0 == 0 then { ok := 1, e0 := folded, e1 := s0 }
      else { ok := 1, e0 := s0, e1 := folded }

/-- Reconstruct arity-4 sibling row from `(idx ∈ 0..3, folded, [s0, s1, s2])`. -/
@[circuit_noinline]
def reconEvals4 (idx : Nat) (folded : Fp3) (sibs : Fp3List) : Evals4 :=
  let bad : Evals4 := { ok := 0, e0 := fp3Zero, e1 := fp3Zero, e2 := fp3Zero, e3 := fp3Zero }
  match sibs with
  | .nil => bad
  | .cons s0 t0 =>
    match t0 with
    | .nil => bad
    | .cons s1 t1 =>
      match t1 with
      | .nil => bad
      | .cons s2 t2 =>
        match t2 with
        | .cons _ _ => bad
        | .nil =>
          if idx == 0 then { ok := 1, e0 := folded, e1 := s0, e2 := s1, e3 := s2 }
          else if idx == 1 then { ok := 1, e0 := s0, e1 := folded, e2 := s1, e3 := s2 }
          else if idx == 2 then { ok := 1, e0 := s0, e1 := s1, e2 := folded, e3 := s2 }
          else { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := folded }

/-- Reconstruct arity-8 sibling row from `(idx ∈ 0..7, folded, [s0..s6])`. -/
@[circuit_noinline]
def reconEvals8 (idx : Nat) (folded : Fp3) (sibs : Fp3List) : Evals8 :=
  let bad : Evals8 :=
    { ok := 0, e0 := fp3Zero, e1 := fp3Zero, e2 := fp3Zero, e3 := fp3Zero
      e4 := fp3Zero, e5 := fp3Zero, e6 := fp3Zero, e7 := fp3Zero }
  match sibs with
  | .nil => bad
  | .cons s0 t0 =>
    match t0 with
    | .nil => bad
    | .cons s1 t1 =>
      match t1 with
      | .nil => bad
      | .cons s2 t2 =>
        match t2 with
        | .nil => bad
        | .cons s3 t3 =>
          match t3 with
          | .nil => bad
          | .cons s4 t4 =>
            match t4 with
            | .nil => bad
            | .cons s5 t5 =>
              match t5 with
              | .nil => bad
              | .cons s6 t6 =>
                match t6 with
                | .cons _ _ => bad
                | .nil =>
                  if idx == 0 then { ok := 1, e0 := folded, e1 := s0, e2 := s1, e3 := s2, e4 := s3, e5 := s4, e6 := s5, e7 := s6 }
                  else if idx == 1 then { ok := 1, e0 := s0, e1 := folded, e2 := s1, e3 := s2, e4 := s3, e5 := s4, e6 := s5, e7 := s6 }
                  else if idx == 2 then { ok := 1, e0 := s0, e1 := s1, e2 := folded, e3 := s2, e4 := s3, e5 := s4, e6 := s5, e7 := s6 }
                  else if idx == 3 then { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := folded, e4 := s3, e5 := s4, e6 := s5, e7 := s6 }
                  else if idx == 4 then { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := s3, e4 := folded, e5 := s4, e6 := s5, e7 := s6 }
                  else if idx == 5 then { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := s3, e4 := s4, e5 := folded, e6 := s5, e7 := s6 }
                  else if idx == 6 then { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := s3, e4 := s4, e5 := s5, e6 := folded, e7 := s6 }
                  else { ok := 1, e0 := s0, e1 := s1, e2 := s2, e3 := s3, e4 := s4, e5 := s5, e6 := s6, e7 := folded }

/-- Optional reduced-opening roll-in `folded + beta^(2^logArity) * rollin`
(`Pcs::rollin` generalized to multi-arity per Plonky3 `fold_query`). -/
@[circuit_noinline]
def applyRollin (p : Nat) (folded : Fp3) (logArity : Nat) (beta : Fp3)
    (hasRollin : Nat) (rollin : Fp3) : Fp3 :=
  if hasRollin == 0 then folded
  else
    let betaPow := fp3ExpPow2 p beta logArity
    fp3Add p folded (fp3Mul p betaPow rollin)

/-- Execute one FRI folding round (validating `logArity ∈ {1, 2, 3}`, extracting
`inGroupIdx` and `parentBits`, reconstructing the coset row, folding via
`friFold2`/`friFold4`/`friFold8`, and applying optional roll-in). Isolated as a
`@[circuit_noinline]` chip with strictly first-order `if` + single-level ADT
matches so `ShapeInfer` keeps all lists unboxed (zero `Obj`, zero depth cols). -/
@[circuit_noinline]
def friRoundStep (fp : FriParams) (folded : Fp3) (domBits : BitList)
    (logCur : Nat) (round : FriRound) : RoundStepResult :=
  let bad : RoundStepResult := { ok := 0, folded := fp3Zero, nextBits := .nil, nextLog := 0 }
  if round.logArity == 1 then
    if logCur < 1 then bad
    else
      match domBits with
      | .nil => bad
      | .cons b0 rest =>
        let ev := reconEvals2 b0 folded round.sibs
        let logFolded := logCur - 1
        let f1 := friFold2 fp rest logFolded round.beta ev.e0 ev.e1
        let f2 := applyRollin fp.p f1 1 round.beta round.hasRollin round.rollin
        { ok := ev.ok, folded := f2, nextBits := rest, nextLog := logFolded }
  else if round.logArity == 2 then
    if logCur < 2 then bad
    else
      match domBits with
      | .nil => bad
      | .cons b0 r1 =>
        match r1 with
        | .nil => bad
        | .cons b1 rest =>
          let idx := b0 + b1 + b1
          let ev := reconEvals4 idx folded round.sibs
          let logFolded := logCur - 2
          let f1 := friFold4 fp rest logFolded round.beta ev.e0 ev.e1 ev.e2 ev.e3
          let f2 := applyRollin fp.p f1 2 round.beta round.hasRollin round.rollin
          { ok := ev.ok, folded := f2, nextBits := rest, nextLog := logFolded }
  else if round.logArity == 3 then
    if logCur < 3 then bad
    else
      match domBits with
      | .nil => bad
      | .cons b0 r1 =>
        match r1 with
        | .nil => bad
        | .cons b1 r2 =>
          match r2 with
          | .nil => bad
          | .cons b2 rest =>
            let b12 := b1 + b2 + b2
            let idx := b0 + b12 + b12
            let ev := reconEvals8 idx folded round.sibs
            let logFolded := logCur - 3
            let f1 := friFold8 fp rest logFolded round.beta
              ev.e0 ev.e1 ev.e2 ev.e3 ev.e4 ev.e5 ev.e6 ev.e7
            let f2 := applyRollin fp.p f1 3 round.beta round.hasRollin round.rollin
            { ok := ev.ok, folded := f2, nextBits := rest, nextLog := logFolded }
  else bad

/-- Horner evaluation of the FRI final polynomial `c0 + x*(c1 + x*(...))` in `Fp3`
at base-field query point `x ∈ F_p` (matching Plonky3 `final_poly.horner(x)`). -/
@[circuit_noinline]
def evalFinalPoly (p : Nat) (coeffs : Fp3List) (x : Nat) : Fp3 :=
  match coeffs with
  | .nil => fp3Zero
  | .cons c rest =>
    fp3Add p c (fp3Scale p (evalFinalPoly p rest x) x)
termination_by structural coeffs

/-- Horner evaluation of an `Fp3` polynomial at an extension point `z ∈ Fp3`
(used by `#guard` algebraic consistency tests). -/
def evalPolyExt (p : Nat) (coeffs : Fp3List) (z : Fp3) : Fp3 :=
  match coeffs with
  | .nil => fp3Zero
  | .cons c rest =>
    fp3Add p c (fp3Mul p (evalPolyExt p rest z) z)
termination_by structural coeffs

/-- DEEP quotient evaluation `(evalZeta - evalX) / (zeta - [x, 0, 0])` in `Fp3`
(`Pcs::finalize_buckets` lines 475–479) using general `fp3Inv`. -/
@[circuit_noinline]
def deepQuotient (p : Nat) (zeta : Fp3) (x : Nat) (evalZeta evalX : Fp3) : Fp3 :=
  let num := fp3Sub p evalZeta evalX
  let den := fp3Sub p zeta (fp3OfBase x)
  fp3Mul p num (fp3Inv p den)

/-- DEEP quotient evaluation over `toyPrime = 257` invoking the Tier-2 `guess`
`fp3InvToy` (`checked def ... complete by`) directly. -/
@[circuit_noinline]
def deepQuotientToy (zeta : Fp3) (x : Nat) (evalZeta evalX : Fp3) : Fp3 :=
  let num := fp3Sub toyPrime evalZeta evalX
  let den := fp3Sub toyPrime zeta (fp3OfBase x)
  fp3Mul toyPrime num (fp3InvToy den)

/-- Final-round consistency check: verifies `ok == 1`, `logCur == logFinal`,
computes `xFinal = twoAdicGen(logFinal)^(revBits(domBits))`, and returns
`fp3Eq folded (evalFinalPoly fp.p finalCoeffs xFinal)`. -/
@[circuit_noinline]
def checkFinalPoly (fp : FriParams) (ok : Nat) (folded : Fp3) (domBits : BitList)
    (logCur logFinal : Nat) (finalCoeffs : Fp3List) : Nat :=
  if ok == 1 then
    if logCur == logFinal then
      let gFinal := twoAdicGen fp logFinal
      let xFinal := expByBits fp.p gFinal (bitListRev domBits .nil)
      let expected := evalFinalPoly fp.p finalCoeffs xFinal
      fp3Eq folded expected
    else 0
  else 0

/-- Structural multi-round FRI query loop accumulating `ok` across all rounds so
`Depth.Structural` assigns 0 depth columns. -/
@[circuit_noinline]
def verifyFriQueryLoop (fp : FriParams) (ok : Nat) (folded : Fp3) (domBits : BitList)
    (logCur logFinal : Nat) (rounds : FriRoundList) (finalCoeffs : Fp3List) : Nat :=
  match rounds with
  | .nil => checkFinalPoly fp ok folded domBits logCur logFinal finalCoeffs
  | .cons round rest =>
    let step := friRoundStep fp folded domBits logCur round
    let nextOk := if ok == 1 then step.ok else 0
    verifyFriQueryLoop fp nextOk step.folded step.nextBits step.nextLog logFinal rest finalCoeffs
termination_by structural rounds

/-- Multi-round FRI query verifier (supporting mixed arities `logArity ∈ {1, 2, 3}`,
height-matched roll-in buckets, and arbitrary-degree final polynomial evaluation).
Returns `1` iff every round folds validly and matches `evalFinalPoly`, else `0`. -/
@[circuit_inline]
def verifyFriQuery (fp : FriParams) (initFolded : Fp3) (domBits : BitList)
    (logCur logFinal : Nat) (rounds : FriRoundList) (finalCoeffs : Fp3List) : Nat :=
  verifyFriQueryLoop fp 1 initFolded domBits logCur logFinal rounds finalCoeffs

/-! ## Live STARK Benchmark Entrypoint (`FriPure.entryFriQuery`)

Exercises the full `MultiStark` FRI query pipeline over `toyPrime = 257`
($\mathbb{F}_{257}[X]/(X^3 - X - 1)$, irreducible cubic trinomial, 8-adic domain
`N = 256`, `(p - 1)² = 65536 < 2^56` → `TableTier.byte256`):
1. Canonical input validation (`qIdx < 256`, field coords `< 257`),
2. Domain point `x0 = twoAdicGen(8)^(revBits(qIdx))` via `bitsOf8` + `expByBits`,
3. DEEP quotient `(P(zeta) - P(x0)) / (zeta - x0)` via Tier-2 `Fp3` `guess` `fp3InvToy`,
4. 3 mixed multi-arity FRI rounds inside shared generic `verifyFriQuery`:
   * Round 0: `logArity = 3` (arity-8 `friFold8`, `mla = 3`) + `rollin` at `log_h = 5`,
   * Round 1: `logArity = 2` (arity-4 `friFold4`, `mla = 2`),
   * Round 2: `logArity = 1` (arity-2 `friFold2`, `mla = 1`),
   each calling Tier-2 base-field `guess` `fInvMod`,
5. Degree-1 final-polynomial Horner evaluation `evalFinalPoly` at `xFinal = 241 ≠ 1`
   and `fp3Eq` consistency check.

Valid witness: `(173, 228, 22, 153, 13) → 1`. -/
@[circuit_budget 32 512 208 32 1900]
def entryFriQuery (qIdx eval0_c0 sib0_c0 final0_c0 beta0_c0 : Nat) : Nat :=
  let p := toyPrime
  if qIdx < 256 then
    if eval0_c0 < p then
      if sib0_c0 < p then
        if final0_c0 < p then
          if beta0_c0 < p then
            let fp := toyFriParams
            let domBits := bitsOf8 qIdx
            let g0 := twoAdicGen fp 8
            let x0 := expByBits p g0 (bitListRev domBits .nil)
            let zeta : Fp3 := { c0 := 19, c1 := 37, c2 := 53 }
            let evalZeta : Fp3 := { c0 := 58, c1 := 192, c2 := 242 }
            let evalX0 : Fp3 := { c0 := eval0_c0, c1 := 184, c2 := 66 }
            let initFolded := deepQuotientToy zeta x0 evalZeta evalX0
            let sibs0 : Fp3List :=
              .cons { c0 := sib0_c0, c1 := 6, c2 := 218 }
              (.cons { c0 := 202, c1 := 197, c2 := 195 }
              (.cons { c0 := 78, c1 := 119, c2 := 243 }
              (.cons { c0 := 2, c1 := 209, c2 := 183 }
              (.cons { c0 := 100, c1 := 26, c2 := 187 }
              (.cons { c0 := 203, c1 := 42, c2 := 95 }
              (.cons { c0 := 203, c1 := 131, c2 := 249 } .nil))))))
            let r0 : FriRound :=
              { logArity := 3
                beta := { c0 := beta0_c0, c1 := 29, c2 := 41 }
                sibs := sibs0
                hasRollin := 1
                rollin := { c0 := 165, c1 := 150, c2 := 175 } }
            let sibs1 : Fp3List :=
              .cons { c0 := 34, c1 := 164, c2 := 2 }
              (.cons { c0 := 57, c1 := 194, c2 := 9 }
              (.cons { c0 := 129, c1 := 147, c2 := 18 } .nil))
            let r1 : FriRound :=
              { logArity := 2
                beta := { c0 := 17, c1 := 31, c2 := 47 }
                sibs := sibs1
                hasRollin := 0
                rollin := fp3Zero }
            let sibs2 : Fp3List :=
              .cons { c0 := 159, c1 := 156, c2 := 192 } .nil
            let r2 : FriRound :=
              { logArity := 1
                beta := { c0 := 23, c1 := 43, c2 := 59 }
                sibs := sibs2
                hasRollin := 0
                rollin := fp3Zero }
            let rounds : FriRoundList := .cons r0 (.cons r1 (.cons r2 .nil))
            let finalCoeffs : Fp3List :=
              .cons { c0 := final0_c0, c1 := 11, c2 := 96 }
              (.cons { c0 := 166, c1 := 189, c2 := 127 } .nil)
            verifyFriQuery fp initFolded domBits 8 2 rounds finalCoeffs
          else 0
        else 0
      else 0
    else 0
  else 0

/-! ## Pure Lean Self-Checks (`#guard`): Goldilocks, `p = 257`, and `p = 998244353` -/

-- 1. Goldilocks `Fp3` ($\mathbb{F}_{2^{64}-2^{32}+1}[X]/(X^3 - X - 1)$) ring axioms & inverse
private def glA : Fp3 := { c0 := 1234567890123456789, c1 := 9876543210987654321, c2 := 4242424242424242424 }
private def glB : Fp3 := { c0 := 1111111111111111111, c1 := 2222222222222222222, c2 := 3333333333333333333 }
private def glC : Fp3 := { c0 := 1753635133440165772, c1 := 9223372034707292161, c2 := 7 }

#guard goldilocksPrime < maxFriModulus
#guard fp3Add goldilocksPrime glA glB == fp3Add goldilocksPrime glB glA
#guard fp3Sub goldilocksPrime (fp3Add goldilocksPrime glA glB) glB == glA
#guard fp3Add goldilocksPrime glA (fp3Neg goldilocksPrime glA) == fp3Zero
#guard fp3Mul goldilocksPrime glA glB == fp3Mul goldilocksPrime glB glA
#guard fp3Mul goldilocksPrime (fp3Mul goldilocksPrime glA glB) glC ==
  fp3Mul goldilocksPrime glA (fp3Mul goldilocksPrime glB glC)
#guard fp3Mul goldilocksPrime glA (fp3Add goldilocksPrime glB glC) ==
  fp3Add goldilocksPrime (fp3Mul goldilocksPrime glA glB) (fp3Mul goldilocksPrime glA glC)
#guard fp3Mul goldilocksPrime glA fp3One == glA
#guard fp3Square goldilocksPrime glA == fp3Mul goldilocksPrime glA glA
#guard fp3Scale goldilocksPrime glA 7 == fp3Mul goldilocksPrime glA (fp3OfBase 7)
#guard fp3Mul goldilocksPrime glA (fp3Inv goldilocksPrime glA) == fp3One
#guard fp3Mul goldilocksPrime glB (fp3Inv goldilocksPrime glB) == fp3One
#guard fp3Mul goldilocksPrime glC (fp3Inv goldilocksPrime glC) == fp3One
#guard twoAdicGen goldilocksFriParams 0 == 1
#guard twoAdicGen goldilocksFriParams 1 == goldilocksPrime - 1
#guard mulMod goldilocksPrime (twoAdicGen goldilocksFriParams 2) goldilocksFriParams.w2Inv == 1
#guard mulMod goldilocksPrime (twoAdicGen goldilocksFriParams 3) goldilocksFriParams.w3Inv == 1
#guard mulMod goldilocksPrime 2 goldilocksInv2 == 1

-- 2. Goldilocks multi-arity FRI folding (`friFold2`, `friFold4`, `friFold8`, `friFoldArity`)
--    verified directly against polynomial evaluation at `beta`
private def glPoly2 : Fp3List :=
  .cons { c0 := 3, c1 := 5, c2 := 2 } (.cons { c0 := 10, c1 := 16, c2 := 15 } .nil)

private def glPoly4 : Fp3List :=
  .cons { c0 := 3, c1 := 5, c2 := 2 }
  (.cons { c0 := 10, c1 := 16, c2 := 15 }
  (.cons { c0 := 17, c1 := 27, c2 := 28 }
  (.cons { c0 := 24, c1 := 38, c2 := 41 } .nil)))

private def glPoly8 : Fp3List :=
  .cons { c0 := 3, c1 := 5, c2 := 2 }
  (.cons { c0 := 10, c1 := 16, c2 := 15 }
  (.cons { c0 := 17, c1 := 27, c2 := 28 }
  (.cons { c0 := 24, c1 := 38, c2 := 41 }
  (.cons { c0 := 31, c1 := 49, c2 := 54 }
  (.cons { c0 := 38, c1 := 60, c2 := 67 }
  (.cons { c0 := 45, c1 := 71, c2 := 80 }
  (.cons { c0 := 52, c1 := 82, c2 := 93 } .nil)))))))

private def glBetaTest : Fp3 := { c0 := 17, c1 := 29, c2 := 43 }
private def parentBits3 : BitList := .cons 1 (.cons 1 .nil)

#guard
  let fp := goldilocksFriParams
  let g := twoAdicGen fp 3
  let s := expByBits fp.p g (bitListRev parentBits3 .nil)
  let e0 := evalFinalPoly fp.p glPoly2 s
  let e1 := evalFinalPoly fp.p glPoly2 (negMod fp.p s)
  friFold2 fp parentBits3 2 glBetaTest e0 e1 == evalPolyExt fp.p glPoly2 glBetaTest &&
  friFoldArity fp 1 parentBits3 2 glBetaTest (.cons e0 (.cons e1 .nil)) ==
    evalPolyExt fp.p glPoly2 glBetaTest

#guard
  let fp := goldilocksFriParams
  let g := twoAdicGen fp 4
  let s := expByBits fp.p g (bitListRev parentBits3 .nil)
  let w := twoAdicGen fp 2
  let sw := mulMod fp.p s w
  let e0 := evalFinalPoly fp.p glPoly4 s
  let e1 := evalFinalPoly fp.p glPoly4 (negMod fp.p s)
  let e2 := evalFinalPoly fp.p glPoly4 sw
  let e3 := evalFinalPoly fp.p glPoly4 (negMod fp.p sw)
  friFold4 fp parentBits3 2 glBetaTest e0 e1 e2 e3 == evalPolyExt fp.p glPoly4 glBetaTest &&
  friFoldArity fp 2 parentBits3 2 glBetaTest (.cons e0 (.cons e1 (.cons e2 (.cons e3 .nil)))) ==
    evalPolyExt fp.p glPoly4 glBetaTest

#guard
  let fp := goldilocksFriParams
  let g := twoAdicGen fp 5
  let s := expByBits fp.p g (bitListRev parentBits3 .nil)
  let w := twoAdicGen fp 3
  let w2 := mulMod fp.p w w
  let w3 := mulMod fp.p w2 w
  let e0 := evalFinalPoly fp.p glPoly8 s
  let e1 := evalFinalPoly fp.p glPoly8 (negMod fp.p s)
  let e2 := evalFinalPoly fp.p glPoly8 (mulMod fp.p s w2)
  let e3 := evalFinalPoly fp.p glPoly8 (negMod fp.p (mulMod fp.p s w2))
  let e4 := evalFinalPoly fp.p glPoly8 (mulMod fp.p s w)
  let e5 := evalFinalPoly fp.p glPoly8 (negMod fp.p (mulMod fp.p s w))
  let e6 := evalFinalPoly fp.p glPoly8 (mulMod fp.p s w3)
  let e7 := evalFinalPoly fp.p glPoly8 (negMod fp.p (mulMod fp.p s w3))
  friFold8 fp parentBits3 2 glBetaTest e0 e1 e2 e3 e4 e5 e6 e7 == evalPolyExt fp.p glPoly8 glBetaTest &&
  friFoldArity fp 3 parentBits3 2 glBetaTest
    (.cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 .nil)))))))) ==
    evalPolyExt fp.p glPoly8 glBetaTest

-- 3. Full 3-round mixed-arity Goldilocks FRI query (`log_arity = [3, 2, 1]` + DEEP quotient + roll-in + final poly)
private def glQueryTest (tamperEval tamperFinal tamperBeta : Nat) : Nat :=
  let fp := goldilocksFriParams
  let p := fp.p
  let domBits := bitsOf8 173
  let x0 := expByBits p (twoAdicGen fp 8) (bitListRev domBits .nil)
  let zeta : Fp3 := { c0 := 19, c1 := 37, c2 := 53 }
  let evalZeta : Fp3 := { c0 := 13081549493958805761, c1 := 17030695439907425675, c2 := 12744337651521039832 }
  let evalX0 : Fp3 :=
    { c0 := addMod p 17368528072965332137 tamperEval
      c1 := 5164012147910210953
      c2 := 13842612648831983548 }
  let initFolded := deepQuotient p zeta x0 evalZeta evalX0
  let sibs0 : Fp3List :=
    .cons { c0 := 14176127106311549984, c1 := 7902448167918197255, c2 := 16852465880437482554 }
    (.cons { c0 := 4729222952131734773, c1 := 10650544263098136906, c2 := 6494281137944425034 }
    (.cons { c0 := 5457274499486376665, c1 := 8892769979567311815, c2 := 8047060542915656305 }
    (.cons { c0 := 4523530088336357594, c1 := 6659732739698037301, c2 := 14517354050407758484 }
    (.cons { c0 := 8102665624324472298, c1 := 14255853511449305929, c2 := 6018592914879474958 }
    (.cons { c0 := 15084935715861271502, c1 := 3510630872085447983, c2 := 16313489120806084058 }
    (.cons { c0 := 11674901159913919827, c1 := 9493235833840645049, c2 := 18189371016230823641 } .nil))))))
  let r0 : FriRound :=
    { logArity := 3
      beta := { c0 := addMod p 13 tamperBeta, c1 := 29, c2 := 41 }
      sibs := sibs0
      hasRollin := 1
      rollin := { c0 := 15067387877763249821, c1 := 6282808216778127063, c2 := 349287461669388580 } }
  let sibs1 : Fp3List :=
    .cons { c0 := 6064597544929321974, c1 := 8139036044785596674, c2 := 9024291269404874251 }
    (.cons { c0 := 1231512566621219917, c1 := 2530313209841374760, c2 := 13154231748508648358 }
    (.cons { c0 := 10110646275321921411, c1 := 8642357972677344278, c2 := 9060174056637952728 } .nil))
  let r1 : FriRound :=
    { logArity := 2
      beta := { c0 := 17, c1 := 31, c2 := 47 }
      sibs := sibs1
      hasRollin := 0
      rollin := fp3Zero }
  let sibs2 : Fp3List :=
    .cons { c0 := 7524105363992586291, c1 := 8494418821224355348, c2 := 17509429969077471001 } .nil
  let r2 : FriRound :=
    { logArity := 1
      beta := { c0 := 23, c1 := 43, c2 := 59 }
      sibs := sibs2
      hasRollin := 0
      rollin := fp3Zero }
  let rounds : FriRoundList := .cons r0 (.cons r1 (.cons r2 .nil))
  let finalCoeffs : Fp3List :=
    .cons { c0 := addMod p 13665557187114029321 tamperFinal, c1 := 11509263837069962195, c2 := 9653781131652746995 }
    (.cons { c0 := 13901964498164714879, c1 := 11993864364359438531, c2 := 6843636990974372516 } .nil)
  verifyFriQuery fp initFolded domBits 8 2 rounds finalCoeffs

#guard glQueryTest 0 0 0 == 1
#guard glQueryTest 1 0 0 == 0
#guard glQueryTest 0 1 0 == 0
#guard glQueryTest 0 0 1 == 0

-- 4. Toy Fermat prime `p = 257` `Fp3` ring axioms, Tier-2 `guess` checkers, and `entryFriQuery`
private def toyA : Fp3 := { c0 := 19, c1 := 37, c2 := 53 }
private def toyB : Fp3 := { c0 := 101, c1 := 203, c2 := 77 }
private def toyC : Fp3 := { c0 := 250, c1 := 12, c2 := 199 }

#guard fp3Add toyPrime toyA toyB == fp3Add toyPrime toyB toyA
#guard fp3Mul toyPrime toyA toyB == fp3Mul toyPrime toyB toyA
#guard fp3Mul toyPrime (fp3Mul toyPrime toyA toyB) toyC ==
  fp3Mul toyPrime toyA (fp3Mul toyPrime toyB toyC)
#guard fp3Square toyPrime toyA == fp3Mul toyPrime toyA toyA
#guard fp3Mul toyPrime toyA (fp3InvToy toyA) == fp3One
#guard fp3Mul toyPrime toyB (fp3InvToy toyB) == fp3One
#guard fp3InvToy.check toyA (fp3InvToy toyA) == true
#guard fp3InvToy.check fp3Zero (fp3InvToy fp3Zero) == true
#guard fInvToy.check 42 (fInvToy 42) == true
#guard fInvMod.check toyPrime 42 (fInvMod toyPrime 42) == true
#guard mulMod toyPrime (twoAdicGen toyFriParams 2) toyFriParams.w2Inv == 1
#guard mulMod toyPrime (twoAdicGen toyFriParams 3) toyFriParams.w3Inv == 1

-- `entryFriQuery` positive & negative controls (same function, different witnesses):
#guard entryFriQuery 173 228 22 153 13 == 1
#guard entryFriQuery 173 229 22 153 13 == 0   -- tampered initial query evaluation
#guard entryFriQuery 173 228 23 153 13 == 0   -- tampered round-0 sibling evaluation
#guard entryFriQuery 173 228 22 154 13 == 0   -- tampered final polynomial coeff
#guard entryFriQuery 173 228 22 153 14 == 0   -- tampered round-0 beta challenge
#guard entryFriQuery 174 228 22 153 13 == 0   -- tampered query index
#guard entryFriQuery 173 (228 + 257) 22 153 13 == 0 -- non-canonical field coordinate >= 257
#guard entryFriQuery 256 228 22 153 13 == 0   -- out-of-range query index >= 256

-- 5. 23-adic NTT prime `p = 998244353` ($X^3 - X - 1$ irreducible) sanity checks
private def nttA : Fp3 := { c0 := 123456, c1 := 789012, c2 := 345678 }
#guard fp3Mul ntt23Prime nttA (fp3Inv ntt23Prime nttA) == fp3One
#guard expPower2 ntt23Prime ntt23Gen23 23 == 1
#guard expPower2 ntt23Prime ntt23Gen23 22 == ntt23Prime - 1

end FriPure
