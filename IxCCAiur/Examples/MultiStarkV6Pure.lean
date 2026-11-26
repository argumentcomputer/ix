import Ix.Compile.CircuitContract

/-! # Unified Pure Annotated Lean 4 `MultiStark` Protocol `v6` Verifier (`MultiStarkV6Pure`)

Single-source pure total Lean 4 unification of **all four pillars** of `MultiStark`
Protocol `v6` verification (unifying `MmcsPure.lean`, `KzgAlgebraPure.lean`, and
`FriPure.lean` with a Protocol `v6` Fiat-Shamir challenger), annotated solely with
`open scoped Ix.Circuit` operational directives (`@[circuit_inline]`,
`@[circuit_noinline]`, `@[circuit_budget ...]`, and Tier-2 `checked def ... complete by`).

## Architecture (Four Unified Protocol `v6` Pillars)

1. **Pillar 1 — Fiat-Shamir Transcript / Challenger**:
   * **Real 7-round keyed `UInt32` BLAKE3 challenger** (`deriveChallengesBlake3`),
     using exact Protocol `v6` domain tag `"multi-stark/v6"` and precomputed BLAKE3
     `derive_key_context` chaining values matching `MultiStark/Modules/StarkHash.lean`
     (`v6TranscriptBatchCv`, `v6MerkleLeafCv`, `v6MerkleCompressCv`), verified from
     first principles via `#guard`.
   * **Compact algebraic sponge challenger** (`deriveChallengesCompact`), implementing
     the exact same Protocol `v6` absorb/squeeze schedule over $\mathbb{F}_p^4$ while
     staying strictly under `TableTier.byte256` (256 fixed rows) for fast `ixcc_prove`
     and Endpoint 1 single-circuit Goldilocks STARK proving.
   * Both challengers absorb `"multi-stark/v6"`, public inputs, main/quotient Merkle
     caps, and OOD openings, squeezing `(betaLogup, gammaBase, alphaBase, zetaBase,
     zetaExt ∈ F_{p^3} \ F_p, friBeta0, friBeta1, qBits)` deterministically from the
     transcript with genuine Fiat-Shamir causality (zero circularity).
2. **Pillar 2 — MMCS Merkle Opening Verification**:
   * Verifies committed coset leaf openings at the transcript-squeezed query index
     `leafBits = bitListDrop 2 qBits` against the committed `mainCap` already absorbed
     in Pillar 1 (binding `evalX0` and `friSib0` cryptographically to `mainCap`).
   * Compact variant exercises full batched MMCS (`frontierSortFuel4`, `frontierMergeFuel4`,
     `frontierLevelCons4`, `frontierFold4`, `injectMaybe4`, `compressOrdered4`, `digest4Eq`).
   * BLAKE3 variant exercises `mkLeafDigest32` (`v6MerkleLeafCv`) and depth-2 keyed
     BLAKE3 Merkle path folding (`frontierFold32`, `mmcsCompress32` with
     `v6MerkleCompressCv`, `flags = 75`, `digest32Eq`).
3. **Pillar 3 — AIR Constraint DAG & LogUp Quotient Check at OOD `zetaBase`**:
   * Evaluates the 27-node AIR constraint DAG (`evalAt`, covering all 10 `Node`
     constructors across all 6 opened trace rows and all 4 public columns, with
     `Node.pub 0` bound directly to `pub0`) and 3-lookup 2-group LogUp accumulator
     (`lookupFingerprint`, `groupSummary`, `foldLookups`) at the transcript-squeezed
     `(alphaBase, betaLogup, gammaBase, zetaBase)`.
   * Dynamically computes Lagrange selectors `invG`, `first`, `last`, and `injection`
     via kernel-checked Tier-2 `guess` `fInv257` (general `verifyAirQuotient` uses
     `fInvMod` and is `#guard`-verified on Goldilocks $p_{\mathrm{GL}} = 2^{64}-2^{32}+1$).
4. **Pillar 4 — $\mathbb{F}_{p^3}$ Cubic Extension DEEP Quotient & Multi-Arity FRI**:
   * Exact $\mathbb{F}_p[X]/(X^3 - X - 1)$ cubic extension arithmetic (`fp3Add`, `fp3Sub`,
     `fp3Scale`, `fp3Mul`, `fp3Square`, `fp3ExpPow2`, `fp3Inv`), validated on both
     $p = 257$ and Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$.
   * Computes the DEEP quotient `(evalZeta - evalX0) / (zetaExt - [x0, 0, 0])` where
     `evalZeta = (main0, q0, stage2_0)` binds Pillar 3's OOD openings to Pillar 2's
     verified leaf `evalX0`, using kernel-checked Tier-2 `guess` `fp3Inv257`
     (`checked def ... complete by` with zero-`sorry` primality and irreducibility proofs).
   * Runs 2 multi-arity FRI folding rounds (`log_arity = 2` arity-4 + roll-in →
     `log_arity = 1` arity-2) driven by `(friBeta0, friBeta1, qBits)` using Tier-2
     `guess` `fInvMod`, followed by degree-1 final polynomial Horner evaluation
     `evalFinalPoly` at `xFinal = 256 = -1 ≠ 1`.

## Proof & Compilation Hygiene

* **Zero forbidden constructs**: ONLY `import Ix.Compile.CircuitContract`; zero
  `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `partial`, `unsafe`,
  `@[extern]`, or `@[implemented_by]`. Strictly structural recursion throughout.
* **100% Ixon content-address invariant**: stripping `import Ix.Compile.CircuitContract`,
  `open scoped Ix.Circuit`, all `@[circuit_*]` attributes, and rewriting `checked def`
  to plain `def` yields bit-for-bit identical Ixon content addresses for every declaration.
* **Two `Nat`-argument live STARK benchmark entrypoints**:
  1. `MultiStarkV6Pure.entryVerifyV6Compact (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : Nat`
     (valid witness `(4, 11, 188, 42, 30, 71, 21) → 1`, `TableTier.byte256`).
  2. `MultiStarkV6Pure.entryVerifyV6Blake3 (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : Nat`
     (valid witness `(1, 11, 26, 42, 13, 71, 154) → 1`, `TableTier.u32` with 6 real
     7-round keyed Protocol-`v6` BLAKE3 compressions).
-/

set_option autoImplicit false

open scoped Ix.Circuit

namespace MultiStarkV6Pure

/-! ## Section 1: Monomorphic ADTs (`ShapeInfer`-Unboxed, 0 `Obj` Fallback) -/

/-- LSB-first query index bits (`Lists::List<Field>`). -/
inductive BitList where
  | nil
  | cons (bit : Nat) (rest : BitList)
  deriving BEq, DecidableEq, Repr

/-- Matrix log-heights committed in an MMCS batch. -/
inductive HeightList where
  | nil
  | cons (height : Nat) (rest : HeightList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of base-field elements. -/
inductive FList where
  | nil
  | cons (head : Nat) (tail : FList)
  deriving BEq, DecidableEq, Repr

/-- Cubic extension element `c0 + c1·X + c2·X² ∈ F_p[X]/(X³ - X - 1)`. -/
structure Fp3 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of cubic extension elements. -/
inductive Fp3List where
  | nil
  | cons (head : Fp3) (tail : Fp3List)
  deriving BEq, DecidableEq, Repr

/-- 4-limb unboxed algebraic digest (`TableTier.byte256`). -/
structure Digest4 where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  deriving BEq, DecidableEq, Repr

/-- Merkle proof sibling list for compact 4-limb MMCS. -/
inductive Digest4List where
  | nil
  | cons (head : Digest4) (tail : Digest4List)
  deriving BEq, DecidableEq, Repr

/-- Active node in the compact batched MMCS frontier. -/
structure FrontierNode4 where
  idx : Nat
  bits : BitList
  rowTag : Nat
  digest : Digest4
  deriving BEq, DecidableEq, Repr

/-- Active compact MMCS frontier list. -/
inductive FrontierList4 where
  | nil
  | cons (head : FrontierNode4) (tail : FrontierList4)
  deriving BEq, DecidableEq, Repr

/-- Split pair for compact frontier merge sort. -/
structure FrontierPair4 where
  left : FrontierList4
  right : FrontierList4
  deriving BEq, DecidableEq, Repr

/-- Output of one compact MMCS frontier level / fold. -/
structure LevelResult4 where
  nodes : FrontierList4
  proof : Digest4List
  deriving BEq, DecidableEq, Repr

/-- 8-word (32-byte) flat unboxed `UInt32` BLAKE3 digest / chaining value. -/
structure Digest32 where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  deriving BEq, DecidableEq, Repr

/-- Output of one BLAKE3 quarter-round `G` call. -/
structure QuarterOut where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word BLAKE3 internal compression state. -/
structure State16 where
  v0 : UInt32
  v1 : UInt32
  v2 : UInt32
  v3 : UInt32
  v4 : UInt32
  v5 : UInt32
  v6 : UInt32
  v7 : UInt32
  v8 : UInt32
  v9 : UInt32
  v10 : UInt32
  v11 : UInt32
  v12 : UInt32
  v13 : UInt32
  v14 : UInt32
  v15 : UInt32
  deriving BEq, DecidableEq, Repr

/-- 16-word (64-byte) BLAKE3 message block. -/
structure Block16 where
  m0 : UInt32
  m1 : UInt32
  m2 : UInt32
  m3 : UInt32
  m4 : UInt32
  m5 : UInt32
  m6 : UInt32
  m7 : UInt32
  m8 : UInt32
  m9 : UInt32
  m10 : UInt32
  m11 : UInt32
  m12 : UInt32
  m13 : UInt32
  m14 : UInt32
  m15 : UInt32
  deriving BEq, DecidableEq, Repr

/-- Merkle sibling list of 32-byte BLAKE3 digests. -/
inductive Digest32List where
  | nil
  | cons (head : Digest32) (tail : Digest32List)
  deriving BEq, DecidableEq, Repr

/-- Frontier node carrying a 32-byte BLAKE3 digest. -/
structure FrontierNode32 where
  idx : Nat
  bits : BitList
  digest : Digest32
  deriving BEq, DecidableEq, Repr

/-- Active BLAKE3 MMCS frontier list. -/
inductive FrontierList32 where
  | nil
  | cons (head : FrontierNode32) (tail : FrontierList32)
  deriving BEq, DecidableEq, Repr

/-- Output of one BLAKE3 MMCS frontier level / fold. -/
structure LevelResult32 where
  nodes : FrontierList32
  proof : Digest32List
  deriving BEq, DecidableEq, Repr

/-- AIR constraint expression DAG node (`KzgDeserialize::Node` / `SysNode`).
`var source offset column` uses `source ∈ {0: fixed, 1: main, 2: stage2}` and
`offset ∈ {0: current row, 1: next row}`. -/
inductive Node where
  | const (value : Nat)
  | var (source offset column : Nat)
  | pub (index : Nat)
  | first
  | last
  | transition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of AIR constraint DAG nodes. -/
inductive NodeList where
  | nil
  | cons (head : Node) (tail : NodeList)
  deriving BEq, DecidableEq, Repr

/-- One LogUp lookup descriptor (`multiplicity` node index + `args` node indices). -/
structure Lookup where
  multiplicity : Nat
  args : FList
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of LogUp lookups. -/
inductive LookupList where
  | nil
  | cons (head : Lookup) (tail : LookupList)
  deriving BEq, DecidableEq, Repr

/-- Evaluation context for `evalAt`, carrying opened trace rows, 4 public inputs,
and Lagrange/transition selectors. -/
structure AirContext where
  main : FList
  mainNext : FList
  fixed : FList
  fixedNext : FList
  stage2 : FList
  stage2Next : FList
  pub0 : Nat
  pub1 : Nat
  pub2 : Nat
  pub3 : Nat
  first : Nat
  last : Nat
  transition : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic result of `groupSummary`. -/
structure GroupSummaryResult where
  product : Nat
  numerator : Nat
  rest : LookupList
  deriving BEq, DecidableEq, Repr

/-- Complete AIR + LogUp single-frame input (Lagrange selectors computed dynamically
from transcript-squeezed `zeta` via Tier-2 `guess` inverses). -/
structure AirFrameInput where
  nodes : NodeList
  roots : FList
  lookups : LookupList
  groupSize : Nat
  maxDepth : Nat
  log : Nat
  genMax : Nat
  maxLog : Nat
  main : FList
  mainNext : FList
  fixed : FList
  fixedNext : FList
  stage2 : FList
  stage2Next : FList
  quotientOpen : FList
  pub0 : Nat
  beta : Nat
  gamma : Nat
  alpha : Nat
  zeta : Nat
  acc : Nat
  nextAcc : Nat
  deriving BEq, DecidableEq, Repr

/-- Single-source FRI prime field and 2-adic subgroup parameters. -/
structure FriParams where
  p : Nat
  inv2 : Nat
  genMax : Nat
  maxLog : Nat
  w2Inv : Nat
  w3Inv : Nat
  deriving BEq, DecidableEq, Repr

/-- One multi-arity FRI folding round (`logArity ∈ {1, 2}`) with optional roll-in. -/
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

/-- Unboxed reconstructed arity-2 sibling row (`ok = 1` iff sibling count matches). -/
structure Evals2 where
  ok : Nat
  e0 : Fp3
  e1 : Fp3
  deriving BEq, DecidableEq, Repr

/-- Unboxed reconstructed arity-4 sibling row (`ok = 1` iff sibling count matches). -/
structure Evals4 where
  ok : Nat
  e0 : Fp3
  e1 : Fp3
  e2 : Fp3
  e3 : Fp3
  deriving BEq, DecidableEq, Repr

/-- Result of one multi-arity FRI folding round. -/
structure RoundStepResult where
  ok : Nat
  folded : Fp3
  nextBits : BitList
  nextLog : Nat
  deriving BEq, DecidableEq, Repr

/-- Complete bundle of Fiat-Shamir challenges squeezed from the Protocol `v6` transcript. -/
structure TranscriptChallenges where
  betaLogup : Nat
  gammaBase : Nat
  alphaBase : Nat
  zetaBase : Nat
  zetaExt : Fp3
  friBeta0 : Fp3
  friBeta1 : Fp3
  qBits : BitList
  deriving BEq, DecidableEq, Repr

/-- Full Protocol `v6` proof bundle for the compact algebraic-sponge verifier. -/
structure V6CompactProof where
  pub0 : Nat
  acc : Nat
  nextAcc : Nat
  mainCap : Digest4
  quotCap : Digest4
  mmcsSibs : Digest4List
  main0 : Nat
  stage2_0 : Nat
  q0 : Nat
  q1 : Nat
  evalX0 : Fp3
  friSib0 : Fp3
  friSibs0Tail : Fp3List
  friRollin0 : Fp3
  friSibs1 : Fp3List
  finalCoeffs : Fp3List
  deriving BEq, DecidableEq, Repr

/-- Full Protocol `v6` proof bundle for the real 7-round keyed BLAKE3 verifier. -/
structure V6Blake3Proof where
  pub0 : Nat
  acc : Nat
  nextAcc : Nat
  mainCap : Digest32
  quotCap : Digest32
  mmcsSibs : Digest32List
  main0 : Nat
  stage2_0 : Nat
  q0 : Nat
  q1 : Nat
  evalX0 : Fp3
  friSib0 : Fp3
  friSibs0Tail : Fp3List
  friRollin0 : Fp3
  friSibs1 : Fp3List
  finalCoeffs : Fp3List
  deriving BEq, DecidableEq, Repr

/-! ## Section 2: Prime Field Arithmetic, Cubic Extension `Fp3` & Tier-2 `guess` Inverses -/

/-- Upper bound `2^65` covering Goldilocks ($2^{64} - 2^{32} + 1$) and `toyPrime = 257`. -/
def maxFriModulus : Nat := 2 ^ 65

/-- Fermat prime `F₃ = 257 = 2^8 + 1`: 8-adic NTT prime with `(p - 1)² = 65536 < 2^56`
and $X^3 - X - 1$ genuinely irreducible over $\mathbb{F}_{257}$. -/
@[circuit_inline]
def toyPrime : Nat := 257

/-- FRI parameters for `toyPrime = 257` (`genMax = 3`, `w2 = 241`, `w2Inv = 16`, `w3Inv = 253`). -/
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

/-- Exact Goldilocks $2^{-1} = (p_{\mathrm{GL}} + 1) / 2$. -/
def goldilocksInv2 : Nat := 9223372034707292161

/-- FRI parameters for Protocol `v6` Goldilocks ($\mathbb{F}_{p_{\mathrm{GL}}}[X]/(X^3 - X - 1)$). -/
def goldilocksFriParams : FriParams :=
  { p := goldilocksPrime
    inv2 := goldilocksInv2
    genMax := goldilocksGen32
    maxLog := 32
    w2Inv := 18446462594437873665
    w3Inv := 1099511627520 }

/-- Branchless modular addition `(a + b) mod p` (0 depth columns in recursive callers). -/
@[circuit_noinline]
def addMod (p a b : Nat) : Nat :=
  (a + b) % p

/-- Branchless modular subtraction `(a - b) mod p` for canonical `b ≤ p`. -/
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

/-- Domain size `2^log mod p` (`KzgShape::power2`). -/
@[circuit_noinline]
def power2Mod (p : Nat) : Nat → Nat
  | 0 => 1
  | log + 1 =>
    let half := power2Mod p log
    addMod p half half
termination_by structural log => log

/-- Pure-`Nat` structural-fuel unsigned extended Euclidean worker modulo `p`. -/
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
over any prime `2 ≤ p < 2^65` (covering Goldilocks $2^{64}-2^{32}+1$ and `257`),
with non-circular algebraic checker and unconditional uniqueness proof. -/
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

/-- Specification of `fInvMod` for every coprime `(p, a)` with `2 ≤ p < 2^65`
and `a % p ≠ 0` (independent of `fInvMod.check`). -/
private theorem fInvMod_spec_of_coprime (p a : Nat)
    (hpGe : 2 ≤ p) (hpMax : p < maxFriModulus) (hcop : Nat.gcd p a = 1)
    (ha0 : a % p ≠ 0) :
    fInvMod p a < p ∧ (a * fInvMod p a) % p = 1 := by
  unfold fInvMod
  have hp2 : ¬ (p < 2) := by omega
  have ha0B : (a % p == 0) = false := beq_false_of_ne ha0
  simp only [hp2, ha0B, Bool.false_eq_true, ↓reduceIte]
  have hpPow2 : p < pow2 65 := by rwa [maxFriModulus_eq_pow2] at hpMax
  have hgcdMod : Nat.gcd p (a % p) = 1 := by
    rw [Nat.gcd_comm p (a % p), ← Nat.gcd_rec p a]
    exact hcop
  have hpPos : 0 < p := by omega
  exact egcdStep_spec p a hpGe 65 131 p (a % p) 0 1
    (by decide) hpPow2 (Nat.le_of_lt (Nat.mod_lt a hpPos))
    hpPos (by omega)
    (by simp)
    (by simp [Nat.mul_one])
    hgcdMod

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

private theorem fInvMod_257_spec (a : Nat) (ha : a % toyPrime ≠ 0) :
    fInvMod toyPrime a < toyPrime ∧ (a * fInvMod toyPrime a) % toyPrime = 1 :=
  fInvMod_spec_of_coprime toyPrime a (by decide) toyPrime_lt_maxFriModulus (gcd_257_eq_one a ha) ha

/-- **Tier-2 `guess` #2 (`checked def ... complete by`)**: concrete-prime
(`p = 257`) base-field inverse used for dynamic OOD Lagrange selectors in Pillar 3,
with kernel-checked uniqueness (`by`) and unconditional completeness (`complete by`). -/
@[circuit_noinline]
checked def fInv257 (a : Nat) : Nat :=
  hint fInvMod toyPrime a
  where check fun r =>
    if a % toyPrime == 0 then r == 0
    else decide (r < toyPrime) && ((a * r) % toyPrime == 1)
  by
    intro res hr
    unfold fInv257.check at hr
    unfold fInv257
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
    unfold fInv257.check fInv257
    have h2 : ¬ (toyPrime < 2) := by decide
    by_cases ha0 : a % toyPrime = 0
    · have ha0B : (a % toyPrime == 0) = true := beq_iff_eq.mpr ha0
      unfold fInvMod
      simp only [h2, ha0B, ↓reduceIte, beq_self_eq_true]
    · have ha0B : (a % toyPrime == 0) = false := beq_false_of_ne ha0
      have hspec := fInvMod_257_spec a ha0
      simp only [ha0B, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq]
      exact hspec

/-! ### Exact Cubic Extension Field `Fp3` ($\mathbb{F}_p[X]/(X^3 - X - 1)$) -/

@[circuit_inline]
def fp3Zero : Fp3 := { c0 := 0, c1 := 0, c2 := 0 }

@[circuit_inline]
def fp3One : Fp3 := { c0 := 1, c1 := 0, c2 := 0 }

@[circuit_inline]
def fp3OfBase (x : Nat) : Fp3 := { c0 := x, c1 := 0, c2 := 0 }

@[circuit_inline]
def fp3Canonical (p : Nat) (a : Fp3) : Bool :=
  decide (a.c0 < p) && decide (a.c1 < p) && decide (a.c2 < p)

@[circuit_inline]
def fp3IsZeroMod (p : Nat) (a : Fp3) : Bool :=
  (a.c0 % p == 0) && (a.c1 % p == 0) && (a.c2 % p == 0)

@[circuit_inline]
def fp3Eq (a b : Fp3) : Nat :=
  if a.c0 == b.c0 then
    if a.c1 == b.c1 then
      if a.c2 == b.c2 then 1 else 0
    else 0
  else 0

@[circuit_noinline]
def fp3Add (p : Nat) (a b : Fp3) : Fp3 :=
  { c0 := addMod p a.c0 b.c0
    c1 := addMod p a.c1 b.c1
    c2 := addMod p a.c2 b.c2 }

@[circuit_noinline]
def fp3Sub (p : Nat) (a b : Fp3) : Fp3 :=
  { c0 := subMod p a.c0 b.c0
    c1 := subMod p a.c1 b.c1
    c2 := subMod p a.c2 b.c2 }

@[circuit_inline]
def fp3Neg (p : Nat) (a : Fp3) : Fp3 :=
  { c0 := negMod p a.c0
    c1 := negMod p a.c1
    c2 := negMod p a.c2 }

@[circuit_noinline]
def fp3Scale (p : Nat) (a : Fp3) (k : Nat) : Fp3 :=
  { c0 := mulMod p a.c0 k
    c1 := mulMod p a.c1 k
    c2 := mulMod p a.c2 k }

/-- Karatsuba multiplication in $\mathbb{F}_p[X]/(X^3 - X - 1)$ (`Goldilocks::eg_mul`). -/
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

/-- Squaring in $\mathbb{F}_p[X]/(X^3 - X - 1)$. -/
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

/-- Repeated squaring `a^(2^k)` in `Fp3`. -/
@[circuit_noinline]
def fp3ExpPow2 (p : Nat) (a : Fp3) : Nat → Fp3
  | 0 => a
  | k + 1 => fp3ExpPow2 p (fp3Square p a) k
termination_by structural k => k

/-- Adjugate in $\mathbb{F}_p[X]/(X^3 - X - 1)$ (`Goldilocks::eg_inverse`). -/
@[circuit_noinline]
def fp3Adj (p : Nat) (a : Fp3) : Fp3 :=
  let s := addMod p a.c0 a.c2
  let d0 := subMod p (mulMod p s s) (mulMod p a.c1 (addMod p a.c1 a.c2))
  let d1 := subMod p (mulMod p a.c2 a.c2) (mulMod p a.c0 a.c1)
  let d2 := subMod p (mulMod p a.c1 a.c1) (mulMod p a.c2 s)
  { c0 := d0, c1 := d1, c2 := d2 }

/-- Cubic field norm `N(a) = a0·d0 + a2·d1 + a1·d2 mod p`. -/
@[circuit_noinline]
def fp3Norm (p : Nat) (a : Fp3) : Nat :=
  let d := fp3Adj p a
  addMod p (addMod p (mulMod p a.c0 d.c0) (mulMod p a.c2 d.c1)) (mulMod p a.c1 d.c2)

/-- General cubic extension inverse via adjugate and norm inverse. -/
@[circuit_noinline]
def fp3Inv (p : Nat) (a : Fp3) : Fp3 :=
  if p < 2 then fp3Zero
  else if fp3IsZeroMod p a then fp3Zero
  else
    let d := fp3Adj p a
    let norm := addMod p (addMod p (mulMod p a.c0 d.c0) (mulMod p a.c2 d.c1)) (mulMod p a.c1 d.c2)
    let ninv := fInvMod p norm
    fp3Scale p d ninv

/-! ### Pure-Lean `Fp3` Ring & Irreducibility Proofs for Tier-2 `guess` `fp3Inv257` -/

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
      have hinv := fInvMod_257_spec a haNe
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
  have hinv := fInvMod_257_spec a haNe
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

private theorem fp3Inv_257_spec (a : Fp3) (hnez : fp3IsZeroMod toyPrime a = false) :
    fp3Canonical toyPrime (fp3Inv toyPrime a) = true ∧
    fp3Mul toyPrime a (fp3Inv toyPrime a) = fp3One := by
  unfold fp3Inv
  have h2 : ¬ (toyPrime < 2) := by decide
  simp only [h2, hnez, Bool.false_eq_true, ↓reduceIte]
  have hnormNe : fp3Norm toyPrime a % toyPrime ≠ 0 := fp3Norm_ne_zero_257 a hnez
  have hinv := fInvMod_257_spec (fp3Norm toyPrime a) hnormNe
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
cubic extension field inverse `a⁻¹ ∈ F_257[X]/(X³ - X - 1)` used in Pillar 4's DEEP
quotient, eliminating the entire adjugate + Euclid tower from the STARK circuit, with
kernel-checked uniqueness (`by`) and unconditional completeness (`complete by`). -/
@[circuit_noinline]
checked def fp3Inv257 (a : Fp3) : Fp3 :=
  hint fp3Inv toyPrime a
  where check fun r =>
    if fp3IsZeroMod toyPrime a then fp3Eq r fp3Zero == 1
    else fp3Canonical toyPrime r && (fp3Eq (fp3Mul toyPrime a r) fp3One == 1)
  by
    intro res hr
    unfold fp3Inv257.check at hr
    unfold fp3Inv257
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
      have hspec := fp3Inv_257_spec a hazF
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
    unfold fp3Inv257.check fp3Inv257
    by_cases haz : fp3IsZeroMod toyPrime a = true
    · rw [haz]
      unfold fp3Inv
      have h2 : ¬ (toyPrime < 2) := by decide
      simp only [h2, haz, ↓reduceIte, beq_iff_eq]
      exact (fp3Eq_eq_one_iff fp3Zero fp3Zero).mpr rfl
    · have hazF : fp3IsZeroMod toyPrime a = false := Bool.eq_false_iff.mpr haz
      rw [hazF]
      have hspec := fp3Inv_257_spec a hazF
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq]
      exact ⟨hspec.1, (fp3Eq_eq_one_iff _ _).mpr hspec.2⟩

/-! ## Section 3: Shared Bit-List & Index Helpers (`Pcs::bits_to_num`, `Pcs::has_height`) -/

/-- Decode an LSB-first bit list to its natural index (`Pcs::bits_to_num`). -/
@[circuit_noinline]
def bitsToNum : BitList → Nat
  | .nil => 0
  | .cons b rest =>
    let r := bitsToNum rest
    b + r + r
termination_by structural bits => bits

/-- Return `1` iff `target` appears in `lhs`, else `0` (`Pcs::has_height`). -/
@[circuit_noinline]
def hasHeight (lhs : HeightList) (target : Nat) : Nat :=
  match lhs with
  | .nil => 0
  | .cons h rest =>
    if h == target then 1 else hasHeight rest target
termination_by structural lhs

/-- Encode a 4-bit query index `idx < 16` as an LSB-first `BitList`. -/
@[circuit_noinline]
def bitsOf4 (idx : Nat) : BitList :=
  let b0 := idx % 2; let q1 := idx / 2
  let b1 := q1 % 2;  let q2 := q1 / 2
  let b2 := q2 % 2;  let q3 := q2 / 2
  let b3 := q3 % 2
  .cons b0 (.cons b1 (.cons b2 (.cons b3 .nil)))

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

/-- Conditional base-field multiplication avoiding join-point splitting in `expByBits`. -/
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

/-! ## Section 4: Pillar 1 — Fiat-Shamir Transcript / Challenger

Provides BOTH:
1. Compact algebraic sponge (`deriveChallengesCompact`, `TableTier.byte256`), and
2. Real 7-round keyed `UInt32` BLAKE3 transcript (`deriveChallengesBlake3`, matching
   `MultiStark/Modules/StarkHash.lean` and `Transcript.lean`, `TableTier.u32`). -/

/-- Compressed `"multi-stark/v6"` ASCII domain tag for the compact algebraic sponge
(`109+105=214, 117+45=162, 108+115=223, 116+54=170`, all `< 257`). -/
@[circuit_inline]
def v6TagCompact : Digest4 :=
  { d0 := 214, d1 := 162, d2 := 223, d3 := 170 }

/-- Absorb 4 field elements into the compact 4-limb sponge state. -/
@[circuit_inline]
def spongeAbsorb4 (p : Nat) (s : Digest4) (a0 a1 a2 a3 : Nat) : Digest4 :=
  { d0 := addMod p s.d0 a0
    d1 := addMod p s.d1 a1
    d2 := addMod p s.d2 a2
    d3 := addMod p s.d3 a3 }

/-- One nonlinear quadratic + circulant-MDS round over $\mathbb{F}_p^4$ (`TableTier.byte256`). -/
@[circuit_noinline]
def spongeStepCompact (p rc : Nat) (s : Digest4) : Digest4 :=
  let x0 := addMod p s.d0 rc
  let x1 := addMod p s.d1 (rc + 1)
  let x2 := addMod p s.d2 (rc + 2)
  let x3 := addMod p s.d3 (rc + 3)
  let y0 := mulMod p x0 (addMod p x0 1)
  let y1 := mulMod p x1 (addMod p x1 3)
  let y2 := mulMod p x2 (addMod p x2 5)
  let y3 := mulMod p x3 (addMod p x3 7)
  let tot := addMod p (addMod p y0 y1) (addMod p y2 y3)
  { d0 := addMod p tot (addMod p y0 y1)
    d1 := addMod p tot (addMod p y1 y2)
    d2 := addMod p tot (addMod p y2 y3)
    d3 := addMod p tot (addMod p y3 y0) }

/-- Structural compact sponge permutation loop (`rounds = 2` executes `rc` and `rc + 11`). -/
@[circuit_noinline]
def spongePermLoop (p : Nat) : Nat → Nat → Digest4 → Digest4
  | 0, _, s => s
  | r + 1, rc, s => spongePermLoop p r (rc + 11) (spongeStepCompact p rc s)
termination_by structural r => r

@[circuit_inline]
def spongePermCompact (p rc : Nat) (s : Digest4) : Digest4 :=
  spongePermLoop p 2 rc s

/-- **Pillar 1 (Compact Algebraic Challenger)**: Protocol `v6` Fiat-Shamir absorb/squeeze
schedule absorbing `"multi-stark/v6"`, public inputs `(pub0, acc, nextAcc)`, committed
`mainCap`, `quotCap`, and OOD openings `(main0, stage2_0, q0)` to squeeze all challenges
and query bits deterministically under `TableTier.byte256`.
Parameterized by structural `steps = 1` so Pillar 1 stays an isolated chip. -/
@[circuit_noinline]
def deriveChallengesCompactFuel (p pub0 acc nextAcc : Nat)
    (mainCap quotCap : Digest4) (main0 stage2_0 q0 : Nat) : Nat → TranscriptChallenges
  | 0 =>
    { betaLogup := 0, gammaBase := 0, alphaBase := 0, zetaBase := 0
      zetaExt := fp3Zero, friBeta0 := fp3Zero, friBeta1 := fp3Zero, qBits := .nil }
  | k + 1 =>
    let sA := spongeAbsorb4 p v6TagCompact pub0 acc nextAcc 6
    let st1 := spongePermCompact p 17
      (spongeAbsorb4 p sA (mainCap.d0 % p) (mainCap.d1 % p) (mainCap.d2 % p) (mainCap.d3 % p))
    let st2 := spongePermCompact p 41
      (spongeAbsorb4 p st1 (quotCap.d0 % p) (quotCap.d1 % p) (quotCap.d2 % p) (quotCap.d3 % p))
    let st3 := spongePermCompact p 73 (spongeAbsorb4 p st2 main0 stage2_0 q0 1)
    let st4 := spongePermCompact p 109 st3
    match k with
    | 0 =>
      { betaLogup := st1.d0
        gammaBase := st1.d1
        alphaBase := st1.d2
        zetaBase := st2.d0
        zetaExt := { c0 := st2.d1, c1 := (st2.d2 % (p - 1)) + 1, c2 := st2.d3 }
        friBeta0 := { c0 := st3.d0, c1 := st3.d1, c2 := st3.d2 }
        friBeta1 := { c0 := st4.d0, c1 := st4.d1, c2 := st4.d2 }
        qBits := bitsOf4 (st4.d3 % 16) }
    | _ => deriveChallengesCompactFuel p pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0 k
termination_by structural n => n

@[circuit_inline]
def deriveChallengesCompact (p pub0 acc nextAcc : Nat)
    (mainCap quotCap : Digest4) (main0 stage2_0 q0 : Nat) : TranscriptChallenges :=
  deriveChallengesCompactFuel p pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0 1

/-! ### Real 7-Round Keyed `UInt32` BLAKE3 Core & Protocol `v6` Challenger -/

/-- Standard BLAKE3 IV (`Aiur.Library.Blake3.iv`). -/
@[circuit_inline]
def blake3IV : Digest32 :=
  { w0 := 0x6A09E667, w1 := 0xBB67AE85, w2 := 0x3C6EF372, w3 := 0xA54FF53A
    w4 := 0x510E527F, w5 := 0x9B05688C, w6 := 0x1F83D9AB, w7 := 0x5BE0CD19 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/merkle/leaf")`
(`StarkHash::v6_merkle_leaf_cv`). -/
@[circuit_inline]
def v6MerkleLeafCv : Digest32 :=
  { w0 := 0x77042819, w1 := 0x5A1DD04F, w2 := 0x2F8D0BB8, w3 := 0x39D27832
    w4 := 0x552A30F6, w5 := 0x546C9899, w6 := 0x8510A8EF, w7 := 0x83ECCD66 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/merkle/compress")`
(`StarkHash::v6_merkle_compress_cv`). -/
@[circuit_inline]
def v6MerkleCompressCv : Digest32 :=
  { w0 := 0xCC4D7633, w1 := 0xF8492FEC, w2 := 0x5704B1FD, w3 := 0x2D69A6B5
    w4 := 0xA871EBB5, w5 := 0x6439610D, w6 := 0x89E86BE6, w7 := 0x02E22A34 }

/-- Precomputed Protocol `v6` BLAKE3 `derive_key_context("multi-stark/v6/transcript/batch")`
(`StarkHash::v6_transcript_batch_cv`). -/
@[circuit_inline]
def v6TranscriptBatchCv : Digest32 :=
  { w0 := 0x56945548, w1 := 0x0BAEB2C2, w2 := 0xB0BC28DD, w3 := 0x9EBE2699
    w4 := 0xD7B24F82, w5 := 0x35470F4D, w6 := 0x065F18D3, w7 := 0xF3B2994F }

/-- BLAKE3 quarter-round `G` in Peephole-fusible direct `UInt32.*` form (`add3`, `rotr16`,
`xor_rotr12`, `rotr8`, `xor_rotr7`, zero typeclass closure residualization). -/
@[circuit_inline]
def blake3G (a b c d mx my : UInt32) : QuarterOut :=
  let a1 := UInt32.add (UInt32.add a b) mx
  let t1 := UInt32.xor d a1
  let d1 := UInt32.lor (UInt32.shiftRight t1 (UInt32.ofNat 16)) (UInt32.shiftLeft t1 (UInt32.ofNat 16))
  let c1 := UInt32.add c d1
  let t2 := UInt32.xor b c1
  let b1 := UInt32.lor (UInt32.shiftRight t2 (UInt32.ofNat 12)) (UInt32.shiftLeft t2 (UInt32.ofNat 20))
  let a2 := UInt32.add (UInt32.add a1 b1) my
  let t3 := UInt32.xor d1 a2
  let d2 := UInt32.lor (UInt32.shiftRight t3 (UInt32.ofNat 8)) (UInt32.shiftLeft t3 (UInt32.ofNat 24))
  let c2 := UInt32.add c1 d2
  let t4 := UInt32.xor b1 c2
  let b2 := UInt32.lor (UInt32.shiftRight t4 (UInt32.ofNat 7)) (UInt32.shiftLeft t4 (UInt32.ofNat 25))
  { a := a2, b := b2, c := c2, d := d2 }

/-- One full BLAKE3 round (4 column + 4 diagonal quarter-rounds), shared as one
memoized Peephole-fused chip across all transcript and MMCS compressions. -/
@[circuit_noinline]
def blake3Round (s : State16) (m : Block16) : State16 :=
  let c0 := blake3G s.v0 s.v4 s.v8 s.v12 m.m0 m.m1
  let c1 := blake3G s.v1 s.v5 s.v9 s.v13 m.m2 m.m3
  let c2 := blake3G s.v2 s.v6 s.v10 s.v14 m.m4 m.m5
  let c3 := blake3G s.v3 s.v7 s.v11 s.v15 m.m6 m.m7
  let d0 := blake3G c0.a c1.b c2.c c3.d m.m8 m.m9
  let d1 := blake3G c1.a c2.b c3.c c0.d m.m10 m.m11
  let d2 := blake3G c2.a c3.b c0.c c1.d m.m12 m.m13
  let d3 := blake3G c3.a c0.b c1.c c2.d m.m14 m.m15
  { v0 := d0.a, v1 := d1.a, v2 := d2.a, v3 := d3.a
    v4 := d3.b, v5 := d0.b, v6 := d1.b, v7 := d2.b
    v8 := d2.c, v9 := d3.c, v10 := d0.c, v11 := d1.c
    v12 := d1.d, v13 := d2.d, v14 := d3.d, v15 := d0.d }

/-- BLAKE3 message-schedule permutation between rounds. -/
@[circuit_inline]
def blake3Permute (m : Block16) : Block16 :=
  { m0 := m.m2,  m1 := m.m6,  m2 := m.m3,  m3 := m.m10
    m4 := m.m7,  m5 := m.m0,  m6 := m.m4,  m7 := m.m13
    m8 := m.m1,  m9 := m.m11, m10 := m.m12, m11 := m.m5
    m12 := m.m9, m13 := m.m14, m14 := m.m15, m15 := m.m8 }

/-- Structural 7-round BLAKE3 compression loop (`rem = 6` runs rounds `0..6`). -/
@[circuit_noinline]
def blake3CompressLoop (rem : Nat) (s : State16) (m : Block16) : Digest32 :=
  let s1 := blake3Round s m
  match rem with
  | 0 =>
    { w0 := UInt32.xor s1.v0 s1.v8,  w1 := UInt32.xor s1.v1 s1.v9
      w2 := UInt32.xor s1.v2 s1.v10, w3 := UInt32.xor s1.v3 s1.v11
      w4 := UInt32.xor s1.v4 s1.v12, w5 := UInt32.xor s1.v5 s1.v13
      w6 := UInt32.xor s1.v6 s1.v14, w7 := UInt32.xor s1.v7 s1.v15 }
  | k + 1 =>
    blake3CompressLoop k s1 (blake3Permute m)
termination_by structural rem

/-- Pure-Lean `Blake3::compress_init` (`counter = 0`) over flat `UInt32` structs. -/
@[circuit_noinline]
def blake3CompressInit (cv : Digest32) (m : Block16) (blockLen flags : UInt32) : Digest32 :=
  let iv := blake3IV
  let st : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := iv.w0, v9 := iv.w1, v10 := iv.w2, v11 := iv.w3
      v12 := 0, v13 := 0, v14 := blockLen, v15 := flags }
  blake3CompressLoop 6 st m

/-- **Pillar 1 (Keyed BLAKE3 Challenger)**: 3-batch Protocol `v6` Fiat-Shamir sponge
using exact domain tag `"multi-stark/v6"` (`0x746c756d, 0x74732d69, 0x2f6b7261, 0x00003676`)
and `v6TranscriptBatchCv` (`flags = 75 = DERIVE_KEY_MATERIAL | CHUNK_START | CHUNK_END | ROOT`). -/
@[circuit_noinline]
def blake3AbsorbBatch (state payload : Digest32) (blockLen : UInt32) : Nat → Digest32
  | 0 => state
  | k + 1 =>
    let blk : Block16 :=
      { m0 := state.w0, m1 := state.w1, m2 := state.w2, m3 := state.w3
        m4 := state.w4, m5 := state.w5, m6 := state.w6, m7 := state.w7
        m8 := payload.w0, m9 := payload.w1, m10 := payload.w2, m11 := payload.w3
        m12 := payload.w4, m13 := payload.w5, m14 := payload.w6, m15 := payload.w7 }
    let h := blake3CompressInit v6TranscriptBatchCv blk blockLen 75
    match k with
    | 0 => h
    | _ => blake3AbsorbBatch h payload blockLen k
termination_by structural n => n

@[circuit_noinline]
def deriveChallengesBlake3Fuel (p pub0 acc nextAcc : Nat)
    (mainCap quotCap : Digest32) (main0 stage2_0 q0 : Nat) : Nat → TranscriptChallenges
  | 0 =>
    { betaLogup := 0, gammaBase := 0, alphaBase := 0, zetaBase := 0
      zetaExt := fp3Zero, friBeta0 := fp3Zero, friBeta1 := fp3Zero, qBits := .nil }
  | k + 1 =>
    let seed0 : Digest32 :=
      { w0 := 0x746c756d, w1 := 0x74732d69, w2 := 0x2f6b7261, w3 := 0x00003676
        w4 := UInt32.ofNat pub0, w5 := UInt32.ofNat acc, w6 := UInt32.ofNat nextAcc, w7 := UInt32.ofNat 6 }
    let h1 := blake3AbsorbBatch seed0 mainCap 64 1
    let h2 := blake3AbsorbBatch h1 quotCap 64 1
    let oodPayload : Digest32 :=
      { w0 := UInt32.ofNat main0, w1 := UInt32.ofNat stage2_0, w2 := UInt32.ofNat q0, w3 := 0
        w4 := 0, w5 := 0, w6 := 0, w7 := 0 }
    let h3 := blake3AbsorbBatch h2 oodPayload 44 1
    match k with
    | 0 =>
      { betaLogup := h1.w0.toNat % p
        gammaBase := h1.w1.toNat % p
        alphaBase := h1.w2.toNat % p
        zetaBase := h2.w0.toNat % p
        zetaExt :=
          { c0 := h2.w1.toNat % p
            c1 := (h2.w2.toNat % (p - 1)) + 1
            c2 := h2.w3.toNat % p }
        friBeta0 := { c0 := h3.w0.toNat % p, c1 := h3.w1.toNat % p, c2 := h3.w2.toNat % p }
        friBeta1 := { c0 := h3.w3.toNat % p, c1 := h3.w4.toNat % p, c2 := h3.w5.toNat % p }
        qBits := bitsOf4 (h3.w6.toNat % 16) }
    | _ => deriveChallengesBlake3Fuel p pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0 k
termination_by structural n => n

@[circuit_inline]
def deriveChallengesBlake3 (p pub0 acc nextAcc : Nat)
    (mainCap quotCap : Digest32) (main0 stage2_0 q0 : Nat) : TranscriptChallenges :=
  deriveChallengesBlake3Fuel p pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0 1

/-! ## Section 5: Pillar 2 — MMCS Merkle Opening Verification (Compact Batched & Keyed BLAKE3) -/

@[circuit_inline]
def mkDigest4 (seed : Nat) : Digest4 :=
  { d0 := seed, d1 := seed + 1, d2 := seed + 2, d3 := seed + 3 }

/-- Compact MMCS coset leaf hash binding `evalX0` and `friSib0` into `mainCap`. -/
@[circuit_inline]
def mkLeafDigest4 (evalX0 friSib0 : Fp3) : Digest4 :=
  let p := toyPrime
  { d0 := addMod p evalX0.c0 friSib0.c0
    d1 := addMod p evalX0.c1 friSib0.c1
    d2 := addMod p evalX0.c2 friSib0.c2
    d3 := addMod p (addMod p evalX0.c0 evalX0.c1) (addMod p friSib0.c1 19) }

@[circuit_inline]
def digest4Eq (a b : Digest4) : Nat :=
  if a.d0 == b.d0 then
    if a.d1 == b.d1 then
      if a.d2 == b.d2 then
        if a.d3 == b.d3 then 1 else 0
      else 0
    else 0
  else 0

@[circuit_inline]
def mixCompress4 (a b : Digest4) : Digest4 :=
  { d0 := a.d0 + b.d0 + b.d1 + 1
    d1 := a.d1 + b.d1 + b.d2 + 3
    d2 := a.d2 + b.d2 + b.d3 + 5
    d3 := a.d3 + b.d3 + b.d0 + 7 }

@[circuit_inline]
def compressOrdered4 (bit : Nat) (d s : Digest4) : Digest4 :=
  match bit with
  | 0 => mixCompress4 d s
  | _ => mixCompress4 s d

@[circuit_inline]
def injectMaybe4 (rowTag : Nat) (lhs : HeightList) (lh : Nat) (d : Digest4) : Digest4 :=
  match hasHeight lhs lh with
  | 0 => d
  | _ => mixCompress4 d (mkDigest4 (rowTag + lh + 100))

@[circuit_inline]
def sameClaimsLe (rowA rowB : Nat) (lhs : HeightList) (nextLh : Nat) : Bool :=
  match hasHeight lhs nextLh with
  | 0 => true
  | _ => rowA == rowB

@[circuit_noinline]
def frontierLength4 : FrontierList4 → Nat
  | .nil => 0
  | .cons _ rest => frontierLength4 rest + 1
termination_by structural xs => xs

@[circuit_noinline]
def frontierSplitAux (xs : FrontierList4) (toggle : Nat) : FrontierPair4 :=
  match xs with
  | .nil => { left := .nil, right := .nil }
  | .cons x rest =>
    let nextToggle := if toggle == 0 then 1 else 0
    let sp := frontierSplitAux rest nextToggle
    if toggle == 0 then
      { left := .cons x sp.left, right := sp.right }
    else
      { left := sp.left, right := .cons x sp.right }
termination_by structural xs

@[circuit_inline]
def frontierSplit4 (xs : FrontierList4) : FrontierPair4 :=
  frontierSplitAux xs 0

@[circuit_noinline]
def frontierMergeFuel4 (fuel : Nat) (xs ys : FrontierList4) : FrontierList4 :=
  match fuel with
  | 0 => xs
  | fuel' + 1 =>
    match xs with
    | .nil => ys
    | .cons x xrest =>
      match ys with
      | .nil => xs
      | .cons y yrest =>
        if x.idx < y.idx then
          .cons x (frontierMergeFuel4 fuel' xrest ys)
        else if x.idx == y.idx then
          if digest4Eq x.digest y.digest == 1 then
            if x.rowTag == y.rowTag then
              .cons x (frontierMergeFuel4 fuel' xrest yrest)
            else .nil
          else .nil
        else
          .cons y (frontierMergeFuel4 fuel' xs yrest)
termination_by structural fuel

@[circuit_inline]
def frontierMerge4 (xs ys : FrontierList4) : FrontierList4 :=
  frontierMergeFuel4 (frontierLength4 xs + frontierLength4 ys) xs ys

@[circuit_noinline]
def frontierSortFuel4 (fuel : Nat) (xs : FrontierList4) : FrontierList4 :=
  match fuel with
  | 0 => xs
  | fuel' + 1 =>
    match xs with
    | .nil => .nil
    | .cons _ rest =>
      match rest with
      | .nil => xs
      | .cons _ _ =>
        let sp := frontierSplit4 xs
        frontierMerge4 (frontierSortFuel4 fuel' sp.left) (frontierSortFuel4 fuel' sp.right)
termination_by structural fuel

@[circuit_noinline]
def frontierLevelFuel4 (fuel : Nat) (nodes : FrontierList4) (proof : Digest4List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult4 :=
  match fuel with
  | 0 => { nodes := .nil, proof := proof }
  | fuel' + 1 =>
    match nodes with
    | .nil => { nodes := .nil, proof := proof }
    | .cons a rest =>
      match a.bits with
      | .nil => { nodes := .nil, proof := proof }
      | .cons abit aparentBits =>
        let aparent := bitsToNum aparentBits
        match rest with
        | .nil =>
          match proof with
          | .nil => { nodes := .nil, proof := .nil }
          | .cons sib prest =>
            let parent := injectMaybe4 a.rowTag lhs nextLh (compressOrdered4 abit a.digest sib)
            { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } .nil
              proof := prest }
        | .cons b brest =>
          match b.bits with
          | .nil => { nodes := .nil, proof := proof }
          | .cons _bbit bparentBits =>
            if aparent == bitsToNum bparentBits then
              if sameClaimsLe a.rowTag b.rowTag lhs nextLh then
                let parent := injectMaybe4 a.rowTag lhs nextLh (mixCompress4 a.digest b.digest)
                let r := frontierLevelFuel4 fuel' brest proof lhs nextLh
                { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } r.nodes
                  proof := r.proof }
              else
                { nodes := .nil, proof := proof }
            else
              match proof with
              | .nil => { nodes := .nil, proof := .nil }
              | .cons sib prest =>
                let parent := injectMaybe4 a.rowTag lhs nextLh (compressOrdered4 abit a.digest sib)
                let r := frontierLevelFuel4 fuel' rest prest lhs nextLh
                { nodes := .cons { idx := aparent, bits := aparentBits, rowTag := a.rowTag, digest := parent } r.nodes
                  proof := r.proof }
termination_by structural fuel

@[circuit_inline]
def frontierLevel4 (nodes : FrontierList4) (proof : Digest4List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult4 :=
  frontierLevelFuel4 (frontierLength4 nodes + 1) nodes proof lhs nextLh

@[circuit_noinline]
def frontierFold4 (nodes : FrontierList4) (proof : Digest4List)
    (lhs : HeightList) : Nat → LevelResult4
  | 0 => { nodes := nodes, proof := proof }
  | levels + 1 =>
    let step := frontierLevel4 nodes proof lhs levels
    frontierFold4 step.nodes step.proof lhs levels
termination_by structural levels => levels

/-- Batched compact MMCS verifier (`Mmcs::mmcs_verify_multi`). -/
@[circuit_noinline]
def verifyMulti4 (expected : Digest4) (leaves : FrontierList4)
    (lhs : HeightList) (proof : Digest4List) (logMax : Nat) : Nat :=
  let sorted := frontierSortFuel4 (frontierLength4 leaves) leaves
  let res := frontierFold4 sorted proof lhs logMax
  match res.proof with
  | .cons _ _ => 0
  | .nil =>
    match res.nodes with
    | .nil => 0
    | .cons root tail =>
      match tail with
      | .cons _ _ => 0
      | .nil => if root.idx == 0 then digest4Eq expected root.digest else 0

/-! ### Keyed BLAKE3 MMCS Opening Verifier (`Digest32`) -/

@[circuit_inline]
def u32Eq (a b : UInt32) : Bool :=
  a.toNat == b.toNat

@[circuit_inline]
def digest32Eq (a b : Digest32) : Nat :=
  if u32Eq a.w0 b.w0 then
    if u32Eq a.w1 b.w1 then
      if u32Eq a.w2 b.w2 then
        if u32Eq a.w3 b.w3 then
          if u32Eq a.w4 b.w4 then
            if u32Eq a.w5 b.w5 then
              if u32Eq a.w6 b.w6 then
                if u32Eq a.w7 b.w7 then 1 else 0
              else 0
            else 0
          else 0
        else 0
      else 0
    else 0
  else 0

@[circuit_inline]
def mkDigest32 (seed : Nat) : Digest32 :=
  let w := UInt32.ofNat seed
  { w0 := w, w1 := UInt32.add w (UInt32.ofNat 1), w2 := UInt32.add w (UInt32.ofNat 2)
    w3 := UInt32.add w (UInt32.ofNat 3), w4 := UInt32.add w (UInt32.ofNat 4)
    w5 := UInt32.add w (UInt32.ofNat 5), w6 := UInt32.add w (UInt32.ofNat 6)
    w7 := UInt32.add w (UInt32.ofNat 7) }

/-- Protocol `v6` keyed BLAKE3 MMCS leaf hash (`v6MerkleLeafCv`, `blockLen = 24`, `flags = 75`)
binding `evalX0` and `friSib0` cryptographically into `mainCap`. -/
@[circuit_noinline]
def mkLeafDigest32 (evalX0 friSib0 : Fp3) : Digest32 :=
  let blk : Block16 :=
    { m0 := UInt32.ofNat evalX0.c0, m1 := UInt32.ofNat evalX0.c1, m2 := UInt32.ofNat evalX0.c2
      m3 := UInt32.ofNat friSib0.c0, m4 := UInt32.ofNat friSib0.c1, m5 := UInt32.ofNat friSib0.c2
      m6 := 0, m7 := 0, m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }
  blake3CompressInit v6MerkleLeafCv blk 24 75

/-- Protocol `v6` keyed BLAKE3 2-to-1 MMCS compression (`v6MerkleCompressCv`, `flags = 75`). -/
@[circuit_noinline]
def mmcsCompress32 (a b : Digest32) : Digest32 :=
  let blk : Block16 :=
    { m0 := a.w0, m1 := a.w1, m2 := a.w2, m3 := a.w3
      m4 := a.w4, m5 := a.w5, m6 := a.w6, m7 := a.w7
      m8 := b.w0, m9 := b.w1, m10 := b.w2, m11 := b.w3
      m12 := b.w4, m13 := b.w5, m14 := b.w6, m15 := b.w7 }
  blake3CompressInit v6MerkleCompressCv blk 64 75

@[circuit_inline]
def compressOrdered32 (bit : Nat) (d s : Digest32) : Digest32 :=
  match bit with
  | 0 => mmcsCompress32 d s
  | _ => mmcsCompress32 s d

@[circuit_inline]
def injectMaybe32 (lhs : HeightList) (lh : Nat) (d : Digest32) : Digest32 :=
  match hasHeight lhs lh with
  | 0 => d
  | _ => mmcsCompress32 d (mkDigest32 (lh + 100))

@[circuit_noinline]
def frontierLength32 : FrontierList32 → Nat
  | .nil => 0
  | .cons _ rest => frontierLength32 rest + 1
termination_by structural xs => xs

@[circuit_noinline]
def frontierLevelFuel32 (fuel : Nat) (nodes : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult32 :=
  match fuel with
  | 0 => { nodes := .nil, proof := proof }
  | fuel' + 1 =>
    match nodes with
    | .nil => { nodes := .nil, proof := proof }
    | .cons a rest =>
      match a.bits with
      | .nil => { nodes := .nil, proof := proof }
      | .cons abit aparentBits =>
        let aparent := bitsToNum aparentBits
        match rest with
        | .nil =>
          match proof with
          | .nil => { nodes := .nil, proof := .nil }
          | .cons sib prest =>
            let parent := injectMaybe32 lhs nextLh (compressOrdered32 abit a.digest sib)
            { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } .nil
              proof := prest }
        | .cons b brest =>
          match b.bits with
          | .nil => { nodes := .nil, proof := proof }
          | .cons _bbit bparentBits =>
            if aparent == bitsToNum bparentBits then
              let parent := injectMaybe32 lhs nextLh (mmcsCompress32 a.digest b.digest)
              let r := frontierLevelFuel32 fuel' brest proof lhs nextLh
              { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } r.nodes
                proof := r.proof }
            else
              match proof with
              | .nil => { nodes := .nil, proof := .nil }
              | .cons sib prest =>
                let parent := injectMaybe32 lhs nextLh (compressOrdered32 abit a.digest sib)
                let r := frontierLevelFuel32 fuel' rest prest lhs nextLh
                { nodes := .cons { idx := aparent, bits := aparentBits, digest := parent } r.nodes
                  proof := r.proof }
termination_by structural fuel

@[circuit_inline]
def frontierLevel32 (nodes : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) (nextLh : Nat) : LevelResult32 :=
  frontierLevelFuel32 (frontierLength32 nodes + 1) nodes proof lhs nextLh

@[circuit_noinline]
def frontierFold32 (nodes : FrontierList32) (proof : Digest32List)
    (lhs : HeightList) : Nat → LevelResult32
  | 0 => { nodes := nodes, proof := proof }
  | levels + 1 =>
    let step := frontierLevel32 nodes proof lhs levels
    frontierFold32 step.nodes step.proof lhs levels
termination_by structural levels => levels

/-- Full keyed-BLAKE3 MMCS Merkle path verifier. -/
@[circuit_noinline]
def verifyPath32 (expected : Digest32) (leaf : Digest32)
    (bits : BitList) (lhs : HeightList) (proof : Digest32List) (logMax : Nat) : Nat :=
  let start : FrontierList32 :=
    .cons { idx := bitsToNum bits, bits := bits, digest := leaf } .nil
  let res := frontierFold32 start proof lhs logMax
  match res.proof with
  | .cons _ _ => 0
  | .nil =>
    match res.nodes with
    | .nil => 0
    | .cons root tail =>
      match tail with
      | .cons _ _ => 0
      | .nil => if root.idx == 0 then digest32Eq expected root.digest else 0

/-! ## Section 6: Pillar 3 — AIR Constraint DAG & LogUp Quotient Verification -/

@[circuit_noinline]
def fListGet (xs : FList) (idx : Nat) : Nat :=
  match xs with
  | .nil => 0
  | .cons v rest =>
    match idx with
    | 0 => v
    | k + 1 => fListGet rest k
termination_by structural xs

@[circuit_noinline]
def nodeListGet (nodes : NodeList) (idx : Nat) : Node :=
  match nodes with
  | .nil => .const 0
  | .cons n rest =>
    match idx with
    | 0 => n
    | k + 1 => nodeListGet rest k
termination_by structural nodes

@[circuit_noinline]
def lookupLength : LookupList → Nat
  | .nil => 0
  | .cons _ rest => lookupLength rest + 1
termination_by structural xs => xs

/-- Right-to-left Horner polynomial evaluation `c0 + point * (c1 + ...)`. -/
@[circuit_noinline]
def polynomial (p : Nat) (values : FList) (point : Nat) : Nat :=
  match values with
  | .nil => 0
  | .cons v rest => addMod p v (mulMod p point (polynomial p rest point))
termination_by structural values

@[circuit_inline]
def selectRow (ctx : AirContext) (source offset : Nat) : FList :=
  match source + source + offset with
  | 0 => ctx.fixed
  | 1 => ctx.fixedNext
  | 2 => ctx.main
  | 3 => ctx.mainNext
  | 4 => ctx.stage2
  | _ => ctx.stage2Next

@[circuit_inline]
def pubAt (ctx : AirContext) (index : Nat) : Nat :=
  match index with
  | 0 => ctx.pub0
  | 1 => ctx.pub1
  | 2 => ctx.pub2
  | _ => ctx.pub3

/-- Bounded-depth AIR constraint DAG evaluator (`eval_at`, 0 depth columns). -/
@[circuit_noinline]
def evalAt (p : Nat) (nodes : NodeList) (ctx : AirContext) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, idx =>
    match nodeListGet nodes idx with
    | .const v => v
    | .var source offset column => fListGet (selectRow ctx source offset) column
    | .pub i => pubAt ctx i
    | .first => ctx.first
    | .last => ctx.last
    | .transition => ctx.transition
    | .add a b => addMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .sub a b => subMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .mul a b => mulMod p (evalAt p nodes ctx fuel a) (evalAt p nodes ctx fuel b)
    | .neg a => negMod p (evalAt p nodes ctx fuel a)
termination_by structural fuel => fuel

/-- Left-to-right Horner folding of evaluated AIR constraint roots (`fold_roots`). -/
@[circuit_noinline]
def foldRoots (p : Nat) (roots : FList) (nodes : NodeList) (ctx : AirContext)
    (maxDepth alpha acc : Nat) : Nat :=
  match roots with
  | .nil => acc
  | .cons root rest =>
    let e := evalAt p nodes ctx maxDepth root
    let nextAcc := addMod p (mulMod p acc alpha) e
    foldRoots p rest nodes ctx maxDepth alpha nextAcc
termination_by structural roots

/-- Right-to-left Horner fingerprint over DAG-evaluated LogUp arguments. -/
@[circuit_noinline]
def lookupFingerprint (p : Nat) (args : FList) (nodes : NodeList) (ctx : AirContext)
    (maxDepth gamma : Nat) : Nat :=
  match args with
  | .nil => 0
  | .cons arg rest =>
    let e := evalAt p nodes ctx maxDepth arg
    let tailFp := lookupFingerprint p rest nodes ctx maxDepth gamma
    addMod p e (mulMod p gamma tailFp)
termination_by structural args

/-- Accumulate up to `remaining` lookups into a grouped rational sum (`group_summary`). -/
@[circuit_noinline]
def groupSummary (p : Nat) (lookups : LookupList) (remaining : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma product numerator : Nat) :
    GroupSummaryResult :=
  match remaining with
  | 0 => { product := product, numerator := numerator, rest := lookups }
  | rem + 1 =>
    match lookups with
    | .nil => { product := product, numerator := numerator, rest := .nil }
    | .cons lk rest =>
      let fp := lookupFingerprint p lk.args nodes ctx maxDepth gamma
      let message := addMod p beta fp
      let multVal := evalAt p nodes ctx maxDepth lk.multiplicity
      let nextProd := mulMod p product message
      let nextNum := addMod p (mulMod p numerator message) (mulMod p multVal product)
      groupSummary p rest rem nodes ctx maxDepth beta gamma nextProd nextNum
termination_by structural remaining

/-- Structural countdown worker for grouped LogUp constraint folding (`fold_lookups`). -/
@[circuit_noinline]
def foldLookupsFuel (p : Nat) (fuel : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    match lookups with
    | .nil =>
      let diff := subMod p (fListGet next 0) (fListGet current 0)
      let term := addMod p diff injection
      addMod p (mulMod p acc alpha) term
    | .cons _ _ =>
      let gs := groupSummary p lookups size nodes ctx maxDepth beta gamma 1 0
      let curIdx := fListGet current index
      match gs.rest with
      | .nil =>
        let target := addMod p (fListGet next 0) injection
        let delta := subMod p target curIdx
        let value := subMod p (mulMod p gs.product delta) gs.numerator
        addMod p (mulMod p acc alpha) value
      | rest =>
        let target := fListGet current (index + 1)
        let delta := subMod p target curIdx
        let value := subMod p (mulMod p gs.product delta) gs.numerator
        let nextAcc := addMod p (mulMod p acc alpha) value
        foldLookupsFuel p fuel' rest size (index + 1) nodes ctx maxDepth
          beta gamma alpha current next injection nextAcc
termination_by structural fuel

@[circuit_inline]
def foldLookups (p : Nat) (lookups : LookupList) (size index : Nat)
    (nodes : NodeList) (ctx : AirContext) (maxDepth beta gamma alpha : Nat)
    (current next : FList) (injection acc : Nat) : Nat :=
  foldLookupsFuel p (lookupLength lookups + 1) lookups size index nodes ctx
    maxDepth beta gamma alpha current next injection acc

/-- Generic Pillar 3 AIR + LogUp OOD quotient verifier over any prime `p < 2^65`
(including Goldilocks $p_{\mathrm{GL}}$), computing all Lagrange/injection inverses
dynamically via `fInvMod`. -/
@[circuit_noinline]
def verifyAirQuotient (p : Nat) (f : AirFrameInput) : Nat :=
  let zN := expPower2 p f.zeta f.log
  let vanishing := subMod p zN 1
  if vanishing == 0 then 0
  else
    let g := expPower2 p f.genMax (f.maxLog - f.log)
    let invG := fInvMod p g
    let transition := subMod p f.zeta invG
    let first := mulMod p vanishing (fInvMod p (subMod p f.zeta 1))
    let last := mulMod p vanishing (fInvMod p transition)
    let domSize := power2Mod p f.log
    let injection := mulMod p (mulMod p last (subMod p f.nextAcc f.acc))
      (fInvMod p (mulMod p domSize g))
    let ctx : AirContext :=
      { main := f.main, mainNext := f.mainNext
        fixed := f.fixed, fixedNext := f.fixedNext
        stage2 := f.stage2, stage2Next := f.stage2Next
        pub0 := f.pub0, pub1 := f.beta, pub2 := f.gamma, pub3 := f.acc
        first := first, last := last, transition := transition }
    let folded0 := foldRoots p f.roots f.nodes ctx f.maxDepth f.alpha 0
    let folded := foldLookups p f.lookups f.groupSize 0 f.nodes ctx
      f.maxDepth f.beta f.gamma f.alpha f.stage2 f.stage2Next injection folded0
    let quotient := polynomial p f.quotientOpen zN
    if folded == mulMod p vanishing quotient then 1 else 0

/-- 27-node AIR constraint DAG (depth 5, all 10 `Node` constructors live, with
`Node.pub 0` binding public input `pub0` directly into root 2). -/
@[circuit_noinline]
def sampleAirNodes : NodeList :=
  .cons (.var 1 0 0)        -- 0:  main[0]
  (.cons (.var 1 1 0)       -- 1:  mainNext[0]
  (.cons (.var 0 0 0)       -- 2:  fixed[0]
  (.cons (.var 0 1 0)       -- 3:  fixedNext[0]
  (.cons (.var 2 0 0)       -- 4:  stage2[0]
  (.cons (.var 2 1 0)       -- 5:  stage2Next[0]
  (.cons (.const 1)         -- 6:  Const(1)
  (.cons (.pub 0)           -- 7:  pub0
  (.cons (.pub 1)           -- 8:  betaLogup
  (.cons (.pub 2)           -- 9:  gammaBase
  (.cons (.pub 3)           -- 10: acc
  (.cons .first             -- 11: First
  (.cons .last              -- 12: Last
  (.cons .transition        -- 13: Transition
  (.cons (.add 0 2)         -- 14: main[0] + fixed[0]
  (.cons (.sub 1 14)        -- 15: mainNext[0] - (main[0] + fixed[0])
  (.cons (.mul 13 15)       -- 16: transition * (...) [root 0]
  (.cons (.neg 6)           -- 17: -1
  (.cons (.add 0 17)        -- 18: main[0] - 1
  (.cons (.mul 11 18)       -- 19: first * (main[0] - 1) [root 1]
  (.cons (.sub 4 7)         -- 20: stage2[0] - pub0
  (.cons (.add 5 8)         -- 21: stage2Next[0] + betaLogup
  (.cons (.sub 20 3)        -- 22: (stage2[0] - pub0) - fixedNext[0]
  (.cons (.add 9 10)        -- 23: gammaBase + acc
  (.cons (.sub 21 23)       -- 24: (stage2Next[0] + betaLogup) - (gammaBase + acc)
  (.cons (.add 22 24)       -- 25: combined boundary expr
  (.cons (.mul 12 25)       -- 26: last * (...) [root 2]
  .nil))))))))))))))))))))))))))

@[circuit_inline]
def sampleAirRoots : FList :=
  .cons 16 (.cons 19 (.cons 26 .nil))

/-- Three LogUp lookups (`groupSize = 2` splits into 2 groups: `[0, 1]` and `[2]`). -/
@[circuit_noinline]
def sampleLookups : LookupList :=
  .cons { multiplicity := 6, args := .cons 0 (.cons 2 .nil) }
  (.cons { multiplicity := 17, args := .cons 1 (.cons 3 .nil) }
  (.cons { multiplicity := 6, args := .cons 14 .nil }
  .nil))

/-- Concrete `p = 257` Pillar 3 AIR + LogUp OOD quotient verifier invoking Tier-2
`guess` `fInv257` (`checked def ... complete by`) for all 4 dynamic selector inverses,
taking flat scalars directly (avoiding a 22-field frame wrapper in compiled circuits). -/
@[circuit_noinline]
def verifyAirCore257 (pub0 main0 stage2_0 q0 q1 acc nextAcc beta gamma alpha zeta : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let p := toyPrime
    let zN := expPower2 p zeta 2
    let vanishing := subMod p zN 1
    let ok :=
      if vanishing == 0 then 0
      else
        let g := expPower2 p 3 6
        let invG := fInv257 g
        let transition := subMod p zeta invG
        let first := mulMod p vanishing (fInv257 (subMod p zeta 1))
        let last := mulMod p vanishing (fInv257 transition)
        let domSize := power2Mod p 2
        let injection := mulMod p (mulMod p last (subMod p nextAcc acc))
          (fInv257 (mulMod p domSize g))
        let stage2Row : FList := .cons stage2_0 (.cons 55 .nil)
        let stage2NextRow : FList := .cons 61 (.cons 73 .nil)
        let ctx : AirContext :=
          { main := .cons main0 (.cons 23 .nil)
            mainNext := .cons 29 (.cons 31 .nil)
            fixed := .cons 13 (.cons 17 .nil)
            fixedNext := .cons 19 (.cons 21 .nil)
            stage2 := stage2Row
            stage2Next := stage2NextRow
            pub0 := pub0, pub1 := beta, pub2 := gamma, pub3 := acc
            first := first, last := last, transition := transition }
        let folded0 := foldRoots p sampleAirRoots sampleAirNodes ctx 5 alpha 0
        let folded := foldLookups p sampleLookups 2 0 sampleAirNodes ctx
          5 beta gamma alpha stage2Row stage2NextRow injection folded0
        let quotient := polynomial p (.cons q0 (.cons q1 .nil)) zN
        if folded == mulMod p vanishing quotient then 1 else 0
    match k with
    | 0 => ok
    | _ => verifyAirCore257 pub0 main0 stage2_0 q0 q1 acc nextAcc beta gamma alpha zeta k
termination_by structural n => n

/-! ## Section 7: Pillar 4 — `Fp3` DEEP Quotient, Multi-Arity FRI Folding & Final Polynomial -/

/-- Core degree-2 FRI butterfly step (`Pcs::fri_fold2`). -/
@[circuit_noinline]
def friFold2Step (p inv2 inv2x : Nat) (beta e0 e1 : Fp3) : Fp3 :=
  let sumHalf := fp3Scale p (fp3Add p e0 e1) inv2
  let diffDiv := fp3Scale p (fp3Sub p e0 e1) inv2x
  fp3Add p sumHalf (fp3Mul p beta diffDiv)

/-- Arity-2 (`log_arity = 1`) FRI fold invoking Tier-2 `guess` `fInvMod`. -/
@[circuit_noinline]
def friFold2 (fp : FriParams) (parentBits : BitList) (logFolded : Nat)
    (beta e0 e1 : Fp3) : Fp3 :=
  let g := twoAdicGen fp (logFolded + 1)
  let s := expByBits fp.p g (bitListRev parentBits .nil)
  let inv2s := fInvMod fp.p (addMod fp.p s s)
  friFold2Step fp.p fp.inv2 inv2s beta e0 e1

/-- Arity-4 (`log_arity = 2`) FRI fold via 2-stage butterfly with a single `fInvMod`. -/
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

@[circuit_noinline]
def applyRollin (p : Nat) (folded : Fp3) (logArity : Nat) (beta : Fp3)
    (hasRollin : Nat) (rollin : Fp3) : Fp3 :=
  if hasRollin == 0 then folded
  else
    let betaPow := fp3ExpPow2 p beta logArity
    fp3Add p folded (fp3Mul p betaPow rollin)

/-- Execute one multi-arity FRI folding round (`logArity ∈ {1, 2}`). -/
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
  else bad

/-- Horner evaluation of the FRI final polynomial `c0 + x*(c1 + ...)` in `Fp3`. -/
@[circuit_noinline]
def evalFinalPoly (p : Nat) (coeffs : Fp3List) (x : Nat) : Fp3 :=
  match coeffs with
  | .nil => fp3Zero
  | .cons c rest =>
    fp3Add p c (fp3Scale p (evalFinalPoly p rest x) x)
termination_by structural coeffs

/-- Horner evaluation of an `Fp3` polynomial at `z ∈ Fp3` (for `#guard` algebraic checks). -/
def evalPolyExt (p : Nat) (coeffs : Fp3List) (z : Fp3) : Fp3 :=
  match coeffs with
  | .nil => fp3Zero
  | .cons c rest =>
    fp3Add p c (fp3Mul p (evalPolyExt p rest z) z)
termination_by structural coeffs

/-- Generic DEEP quotient `(evalZeta - evalX) / (zeta - [x, 0, 0])` in `Fp3`. -/
@[circuit_noinline]
def deepQuotient (p : Nat) (zeta : Fp3) (x : Nat) (evalZeta evalX : Fp3) : Fp3 :=
  let num := fp3Sub p evalZeta evalX
  let den := fp3Sub p zeta (fp3OfBase x)
  fp3Mul p num (fp3Inv p den)

/-- Concrete `p = 257` DEEP quotient invoking Tier-2 `guess` `fp3Inv257` directly. -/
@[circuit_noinline]
def deepQuotient257 (zeta : Fp3) (x : Nat) (evalZeta evalX : Fp3) : Fp3 :=
  let num := fp3Sub toyPrime evalZeta evalX
  let den := fp3Sub toyPrime zeta (fp3OfBase x)
  fp3Mul toyPrime num (fp3Inv257 den)

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

@[circuit_inline]
def verifyFriQuery (fp : FriParams) (initFolded : Fp3) (domBits : BitList)
    (logCur logFinal : Nat) (rounds : FriRoundList) (finalCoeffs : Fp3List) : Nat :=
  verifyFriQueryLoop fp 1 initFolded domBits logCur logFinal rounds finalCoeffs

/-- Pillar 2 (Compact Batched MMCS) isolated worker: constructs the 3-node unsorted
frontier at `leafBits = bitListDrop 2 qBits` binding `evalX0` + `friSib0` and verifies
against `mainCap`. -/
@[circuit_noinline]
def runMmcsCompact (mainCap : Digest4) (mmcsSibs : Digest4List)
    (evalX0 friSib0 : Fp3) (qBits : BitList) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let leafBits := bitListDrop 2 qBits
    let leaf := mkLeafDigest4 evalX0 friSib0
    let nQ : FrontierNode4 :=
      { idx := bitsToNum leafBits, bits := leafBits, rowTag := 2, digest := leaf }
    let n1 : FrontierNode4 :=
      { idx := 1, bits := .cons 1 (.cons 0 .nil), rowTag := 1, digest := mkDigest4 20 }
    let n0 : FrontierNode4 :=
      { idx := 0, bits := .cons 0 (.cons 0 .nil), rowTag := 1, digest := mkDigest4 10 }
    let leaves : FrontierList4 := .cons nQ (.cons n1 (.cons n0 .nil))
    let lhs : HeightList := .cons 2 (.cons 1 .nil)
    let ok := verifyMulti4 mainCap leaves lhs mmcsSibs 2
    match k with
    | 0 => ok
    | _ => runMmcsCompact mainCap mmcsSibs evalX0 friSib0 qBits k
termination_by structural n => n

/-- Pillar 2 (Keyed BLAKE3 MMCS) isolated worker: hashes `(evalX0, friSib0)` under
`v6MerkleLeafCv` and verifies the depth-2 keyed BLAKE3 path (`v6MerkleCompressCv`)
at `leafBits = bitListDrop 2 qBits` against `mainCap`. -/
@[circuit_noinline]
def runMmcsBlake3 (mainCap : Digest32) (mmcsSibs : Digest32List)
    (evalX0 friSib0 : Fp3) (qBits : BitList) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let leafBits := bitListDrop 2 qBits
    let leaf := mkLeafDigest32 evalX0 friSib0
    let lhs : HeightList := .cons 2 .nil
    let ok := verifyPath32 mainCap leaf leafBits lhs mmcsSibs 2
    match k with
    | 0 => ok
    | _ => runMmcsBlake3 mainCap mmcsSibs evalX0 friSib0 qBits k
termination_by structural n => n

/-- Pillar 4 (`Fp3` DEEP Quotient + Multi-Arity FRI) isolated worker over `p = 257`,
invoking Tier-2 `fp3Inv257` for the DEEP quotient and Tier-2 `fInvMod` for arity-4 +
arity-2 FRI folding, followed by degree-1 final polynomial Horner evaluation. -/
@[circuit_noinline]
def runDeepFri257 (zetaExt friBeta0 friBeta1 : Fp3) (qBits : BitList)
    (main0 q0 stage2_0 : Nat) (evalX0 friSib0 : Fp3) (friSibs0Tail : Fp3List)
    (friRollin0 : Fp3) (friSibs1 finalCoeffs : Fp3List) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let fp := toyFriParams
    let x0 := expByBits toyPrime (twoAdicGen fp 4) (bitListRev qBits .nil)
    let evalZeta : Fp3 := { c0 := main0, c1 := q0, c2 := stage2_0 }
    let initFolded := deepQuotient257 zetaExt x0 evalZeta evalX0
    let r0 : FriRound :=
      { logArity := 2
        beta := friBeta0
        sibs := .cons friSib0 friSibs0Tail
        hasRollin := 1
        rollin := friRollin0 }
    let r1 : FriRound :=
      { logArity := 1
        beta := friBeta1
        sibs := friSibs1
        hasRollin := 0
        rollin := fp3Zero }
    let ok := verifyFriQuery fp initFolded qBits 4 1 (.cons r0 (.cons r1 .nil)) finalCoeffs
    match k with
    | 0 => ok
    | _ => runDeepFri257 zetaExt friBeta0 friBeta1 qBits main0 q0 stage2_0 evalX0 friSib0
            friSibs0Tail friRollin0 friSibs1 finalCoeffs k
termination_by structural n => n

/-- Canonical input bound check returning `1` iff every element in `xs` is `< bound`. -/
@[circuit_noinline]
def allLt (bound : Nat) : FList → Nat
  | .nil => 1
  | .cons x rest =>
    if x < bound then allLt bound rest else 0
termination_by structural xs => xs

/-! ## Section 8: Unified 4-Pillar Protocol `v6` Verifiers & Live STARK Entrypoints -/

/-- **Unified 4-Pillar Protocol `v6` Verifier Core (Compact Algebraic Sponge)** taking
direct proof components so compiled STARK entrypoints avoid redundant wrapper structs. -/
@[circuit_noinline]
def verifyV6CompactCore (pub0 acc nextAcc : Nat) (mainCap quotCap : Digest4)
    (mmcsSibs : Digest4List) (main0 stage2_0 q0 q1 : Nat)
    (evalX0 friSib0 : Fp3) (friSibs0Tail : Fp3List) (friRollin0 : Fp3)
    (friSibs1 finalCoeffs : Fp3List) : Nat :=
  let ch := deriveChallengesCompact toyPrime pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0
  if runMmcsCompact mainCap mmcsSibs evalX0 friSib0 ch.qBits 1 == 1 then
    if verifyAirCore257 pub0 main0 stage2_0 q0 q1 acc nextAcc
        ch.betaLogup ch.gammaBase ch.alphaBase ch.zetaBase 1 == 1 then
      runDeepFri257 ch.zetaExt ch.friBeta0 ch.friBeta1 ch.qBits main0 q0 stage2_0
        evalX0 friSib0 friSibs0Tail friRollin0 friSibs1 finalCoeffs 1
    else 0
  else 0

/-- **Unified 4-Pillar Protocol `v6` Verifier Core (Real 7-Round Keyed BLAKE3)** taking
direct proof components so compiled STARK entrypoints avoid redundant wrapper structs. -/
@[circuit_noinline]
def verifyV6Blake3Core (pub0 acc nextAcc : Nat) (mainCap quotCap : Digest32)
    (mmcsSibs : Digest32List) (main0 stage2_0 q0 q1 : Nat)
    (evalX0 friSib0 : Fp3) (friSibs0Tail : Fp3List) (friRollin0 : Fp3)
    (friSibs1 finalCoeffs : Fp3List) : Nat :=
  let ch := deriveChallengesBlake3 toyPrime pub0 acc nextAcc mainCap quotCap main0 stage2_0 q0
  if runMmcsBlake3 mainCap mmcsSibs evalX0 friSib0 ch.qBits 1 == 1 then
    if verifyAirCore257 pub0 main0 stage2_0 q0 q1 acc nextAcc
        ch.betaLogup ch.gammaBase ch.alphaBase ch.zetaBase 1 == 1 then
      runDeepFri257 ch.zetaExt ch.friBeta0 ch.friBeta1 ch.qBits main0 q0 stage2_0
        evalX0 friSib0 friSibs0Tail friRollin0 friSibs1 finalCoeffs 1
    else 0
  else 0

/-- Struct-bundled compact Protocol `v6` verifier (for structured `#guard` tamper tests). -/
def verifyV6Compact (proof : V6CompactProof) : Nat :=
  verifyV6CompactCore proof.pub0 proof.acc proof.nextAcc proof.mainCap proof.quotCap
    proof.mmcsSibs proof.main0 proof.stage2_0 proof.q0 proof.q1
    proof.evalX0 proof.friSib0 proof.friSibs0Tail proof.friRollin0
    proof.friSibs1 proof.finalCoeffs

/-- Struct-bundled keyed-BLAKE3 Protocol `v6` verifier (for structured `#guard` tamper tests). -/
def verifyV6Blake3 (proof : V6Blake3Proof) : Nat :=
  verifyV6Blake3Core proof.pub0 proof.acc proof.nextAcc proof.mainCap proof.quotCap
    proof.mmcsSibs proof.main0 proof.stage2_0 proof.q0 proof.q1
    proof.evalX0 proof.friSib0 proof.friSibs0Tail proof.friRollin0
    proof.friSibs1 proof.finalCoeffs

/-! ### Canonical Committed Caps & Proof Builders -/

@[circuit_inline]
def expectedCompactMainCap : Digest4 :=
  { d0 := 1113, d1 := 1057, d2 := 1138, d3 := 1208 }

@[circuit_inline]
def expectedCompactQuotCap : Digest4 :=
  { d0 := 51, d1 := 97, d2 := 143, d3 := 211 }

@[circuit_inline]
def expectedBlake3MainCap : Digest32 :=
  { w0 := 0x7C22EBC8, w1 := 0xF46F109A, w2 := 0x5D3536B8, w3 := 0x573A2A47
    w4 := 0xDE7DAB75, w5 := 0x455E86BF, w6 := 0x4409F038, w7 := 0xF0D15EF9 }

@[circuit_inline]
def expectedBlake3Sib1 : Digest32 :=
  { w0 := 0x7928F958, w1 := 0x3BC62B45, w2 := 0x36500408, w3 := 0x8A3A99A6
    w4 := 0x3FC2E9C1, w5 := 0x88246938, w6 := 0xB582F895, w7 := 0x19B1344D }

@[circuit_inline]
def mkCompactProof (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : V6CompactProof :=
  { pub0 := pub0
    acc := 10
    nextAcc := 20
    mainCap := expectedCompactMainCap
    quotCap := expectedCompactQuotCap
    mmcsSibs := .cons (mkDigest4 sib0) .nil
    main0 := main0
    stage2_0 := stage2_0
    q0 := q0
    q1 := 17
    evalX0 := { c0 := 43, c1 := 89, c2 := 137 }
    friSib0 := { c0 := friSib0, c1 := 103, c2 := 151 }
    friSibs0Tail :=
      .cons { c0 := 88, c1 := 121, c2 := 173 }
      (.cons { c0 := 149, c1 := 202, c2 := 33 } .nil)
    friRollin0 := { c0 := 61, c1 := 117, c2 := 189 }
    friSibs1 := .cons { c0 := 93, c1 := 144, c2 := 215 } .nil
    finalCoeffs :=
      .cons { c0 := final0, c1 := 91, c2 := 31 }
      (.cons { c0 := 166, c1 := 189, c2 := 127 } .nil) }

@[circuit_inline]
def mkBlake3Proof (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : V6Blake3Proof :=
  { pub0 := pub0
    acc := 10
    nextAcc := 20
    mainCap := expectedBlake3MainCap
    quotCap := mkDigest32 77
    mmcsSibs := .cons (mkDigest32 sib0) (.cons expectedBlake3Sib1 .nil)
    main0 := main0
    stage2_0 := stage2_0
    q0 := q0
    q1 := 17
    evalX0 := { c0 := 43, c1 := 89, c2 := 137 }
    friSib0 := { c0 := friSib0, c1 := 103, c2 := 151 }
    friSibs0Tail :=
      .cons { c0 := 88, c1 := 121, c2 := 173 }
      (.cons { c0 := 149, c1 := 202, c2 := 33 } .nil)
    friRollin0 := { c0 := 61, c1 := 117, c2 := 189 }
    friSibs1 := .cons { c0 := 93, c1 := 144, c2 := 215 } .nil
    finalCoeffs :=
      .cons { c0 := final0, c1 := 25, c2 := 42 }
      (.cons { c0 := 166, c1 := 189, c2 := 127 } .nil) }

/-- **Benchmark Entrypoint 1 (`entryVerifyV6Compact`)**:
Unifies ALL 4 Protocol `v6` pillars under `TableTier.byte256` (256 fixed rows):
algebraic sponge Fiat-Shamir transcript → batched MMCS Merkle verification →
AIR DAG + LogUp OOD quotient (`fInv257` guess) → `Fp3` DEEP quotient (`fp3Inv257`
guess) + multi-arity FRI folding (`friFold4` + roll-in + `friFold2` via `fInvMod`
guess) + `evalFinalPoly`.

Valid witness: `(4, 11, 188, 42, 30, 71, 21) → 1`. -/
@[circuit_budget 64 480 180 56 3600]
def entryVerifyV6Compact (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : Nat :=
  let inputs : FList :=
    .cons pub0 (.cons main0 (.cons q0 (.cons stage2_0 (.cons sib0 (.cons friSib0 (.cons final0 .nil))))))
  if allLt toyPrime inputs == 1 then
    verifyV6CompactCore pub0 10 20 expectedCompactMainCap expectedCompactQuotCap
      (.cons (mkDigest4 sib0) .nil) main0 stage2_0 q0 17
      { c0 := 43, c1 := 89, c2 := 137 }
      { c0 := friSib0, c1 := 103, c2 := 151 }
      (.cons { c0 := 88, c1 := 121, c2 := 173 }
        (.cons { c0 := 149, c1 := 202, c2 := 33 } .nil))
      { c0 := 61, c1 := 117, c2 := 189 }
      (.cons { c0 := 93, c1 := 144, c2 := 215 } .nil)
      (.cons { c0 := final0, c1 := 91, c2 := 31 }
        (.cons { c0 := 166, c1 := 189, c2 := 127 } .nil))
  else 0

/-- **Benchmark Entrypoint 2 (`entryVerifyV6Blake3`)**:
Unifies ALL 4 Protocol `v6` pillars WITH 6 real 7-round keyed `UInt32` Protocol-`v6`
BLAKE3 compressions (`v6TranscriptBatchCv` × 3 + `v6MerkleLeafCv` × 1 +
`v6MerkleCompressCv` × 2) + AIR DAG & LogUp OOD quotient (`fInv257` guess) +
`Fp3` DEEP quotient (`fp3Inv257` guess) + multi-arity FRI fold (`fInvMod` guess) +
`evalFinalPoly`.

Valid witness: `(1, 11, 26, 42, 13, 71, 154) → 1`. -/
@[circuit_budget 64 600 360 56 4800]
def entryVerifyV6Blake3 (pub0 main0 q0 stage2_0 sib0 friSib0 final0 : Nat) : Nat :=
  let inputs : FList :=
    .cons pub0 (.cons main0 (.cons q0 (.cons stage2_0 (.cons sib0 (.cons friSib0 (.cons final0 .nil))))))
  if allLt toyPrime inputs == 1 then
    verifyV6Blake3Core pub0 10 20 expectedBlake3MainCap (mkDigest32 77)
      (.cons (mkDigest32 sib0) (.cons expectedBlake3Sib1 .nil)) main0 stage2_0 q0 17
      { c0 := 43, c1 := 89, c2 := 137 }
      { c0 := friSib0, c1 := 103, c2 := 151 }
      (.cons { c0 := 88, c1 := 121, c2 := 173 }
        (.cons { c0 := 149, c1 := 202, c2 := 33 } .nil))
      { c0 := 61, c1 := 117, c2 := 189 }
      (.cons { c0 := 93, c1 := 144, c2 := 215 } .nil)
      (.cons { c0 := final0, c1 := 25, c2 := 42 }
        (.cons { c0 := 166, c1 := 189, c2 := 127 } .nil))
  else 0

/-! ## Section 9: Comprehensive Pure-Lean Self-Checks (`#guard`) -/

-- 1. Official BLAKE3("") test vector & ALL THREE Protocol `v6` `derive_key_context` CVs
private def zeroBlock16 : Block16 :=
  { m0 := 0, m1 := 0, m2 := 0, m3 := 0, m4 := 0, m5 := 0, m6 := 0, m7 := 0
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def officialEmptyBlake3 : Digest32 :=
  { w0 := 0xb94913af, w1 := 0xa6a1f9f5, w2 := 0xea4d40a0, w3 := 0x49c9dc36
    w4 := 0xc925cb9b, w5 := 0xb712c1ad, w6 := 0xca939acc, w7 := 0x62321fe4 }

private def v6LeafCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x6d2f3676
    m4 := 0x6c6b7265, m5 := 0x656c2f65, m6 := 0x00006661, m7 := 0
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def v6CompressCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x6d2f3676
    m4 := 0x6c6b7265, m5 := 0x6f632f65, m6 := 0x6572706d, m7 := 0x00007373
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

private def v6TranscriptCtxBlock : Block16 :=
  { m0 := 0x746c756d, m1 := 0x74732d69, m2 := 0x2f6b7261, m3 := 0x742f3676
    m4 := 0x736e6172, m5 := 0x70697263, m6 := 0x61622f74, m7 := 0x00686374
    m8 := 0, m9 := 0, m10 := 0, m11 := 0, m12 := 0, m13 := 0, m14 := 0, m15 := 0 }

#guard blake3CompressInit blake3IV zeroBlock16 0 11 == officialEmptyBlake3
#guard blake3CompressInit blake3IV v6LeafCtxBlock 26 43 == v6MerkleLeafCv
#guard blake3CompressInit blake3IV v6CompressCtxBlock 30 43 == v6MerkleCompressCv
#guard blake3CompressInit blake3IV v6TranscriptCtxBlock 31 43 == v6TranscriptBatchCv

-- 2. Kernel-verified Tier-2 `guess` checkers (`fInvMod`, `fInv257`, `fp3Inv257`)
private def toyElemA : Fp3 := { c0 := 19, c1 := 37, c2 := 53 }
#guard fInvMod.check toyPrime 42 (fInvMod toyPrime 42) == true
#guard fInv257.check 42 (fInv257 42) == true
#guard fInv257.check 0 (fInv257 0) == true
#guard fp3Inv257.check toyElemA (fp3Inv257 toyElemA) == true
#guard fp3Inv257.check fp3Zero (fp3Inv257 fp3Zero) == true
#guard fp3Mul toyPrime toyElemA (fp3Inv257 toyElemA) == fp3One

-- 3. `entryVerifyV6Compact`: valid acceptance & tampering rejection across ALL 4 pillars
#guard entryVerifyV6Compact 4 11 188 42 30 71 21 == 1
#guard entryVerifyV6Compact 5 11 188 42 30 71 21 == 0   -- tampered public input `pub0` (Pillar 1/2/3/4)
#guard entryVerifyV6Compact 4 12 188 42 30 71 21 == 0   -- tampered OOD main opening (Pillar 1/3/4)
#guard entryVerifyV6Compact 4 11 189 42 30 71 21 == 0   -- tampered OOD quotient opening (Pillar 1/3/4)
#guard entryVerifyV6Compact 4 11 188 43 30 71 21 == 0   -- tampered LogUp stage2 accumulator (Pillar 1/3/4)
#guard entryVerifyV6Compact 4 11 188 42 31 71 21 == 0   -- tampered MMCS Merkle sibling (Pillar 2)
#guard entryVerifyV6Compact 4 11 188 42 30 72 21 == 0   -- tampered FRI round-0 sibling & MMCS leaf (Pillar 2/4)
#guard entryVerifyV6Compact 4 11 188 42 30 71 22 == 0   -- tampered FRI final polynomial coeff (Pillar 4)
#guard entryVerifyV6Compact (4 + 257) 11 188 42 30 71 21 == 0 -- non-canonical input >= 257

-- Structural tamper checks on `verifyV6Compact` (Merkle root, quotient cap, evalX0, FRI round-1 sibling)
private def validCompact : V6CompactProof := mkCompactProof 4 11 188 42 30 71 21
#guard verifyV6Compact validCompact == 1
#guard verifyV6Compact { validCompact with mainCap := { expectedCompactMainCap with d0 := 1114 } } == 0
#guard verifyV6Compact { validCompact with quotCap := { expectedCompactQuotCap with d0 := 52 } } == 0
#guard verifyV6Compact { validCompact with evalX0 := { c0 := 44, c1 := 89, c2 := 137 } } == 0
#guard verifyV6Compact { validCompact with friSibs1 := .cons { c0 := 94, c1 := 144, c2 := 215 } .nil } == 0

-- 4. `entryVerifyV6Blake3`: valid acceptance & tampering rejection across ALL 4 pillars
#guard expectedBlake3MainCap ==
  mmcsCompress32 expectedBlake3Sib1
    (mmcsCompress32 (mkLeafDigest32 { c0 := 43, c1 := 89, c2 := 137 } { c0 := 71, c1 := 103, c2 := 151 })
      (mkDigest32 13))
#guard entryVerifyV6Blake3 1 11 26 42 13 71 154 == 1
#guard entryVerifyV6Blake3 2 11 26 42 13 71 154 == 0   -- tampered public input `pub0` (Pillar 1/2/3/4)
#guard entryVerifyV6Blake3 1 12 26 42 13 71 154 == 0   -- tampered OOD main opening (Pillar 1/3/4)
#guard entryVerifyV6Blake3 1 11 27 42 13 71 154 == 0   -- tampered OOD quotient opening (Pillar 1/3/4)
#guard entryVerifyV6Blake3 1 11 26 43 13 71 154 == 0   -- tampered LogUp stage2 accumulator (Pillar 1/3/4)
#guard entryVerifyV6Blake3 1 11 26 42 14 71 154 == 0   -- tampered MMCS Merkle sibling (Pillar 2)
#guard entryVerifyV6Blake3 1 11 26 42 13 72 154 == 0   -- tampered FRI round-0 sibling & MMCS leaf (Pillar 2/4)
#guard entryVerifyV6Blake3 1 11 26 42 13 71 155 == 0   -- tampered FRI final polynomial coeff (Pillar 4)
#guard entryVerifyV6Blake3 1 11 (26 + 257) 42 13 71 154 == 0 -- non-canonical input >= 257

-- Structural tamper checks on `verifyV6Blake3` (Merkle root, quotient cap, evalX0, FRI round-1 sibling)
private def validBlake3 : V6Blake3Proof := mkBlake3Proof 1 11 26 42 13 71 154
#guard verifyV6Blake3 validBlake3 == 1
#guard verifyV6Blake3 { validBlake3 with mainCap := { expectedBlake3MainCap with w0 := 0x7C22EBC9 } } == 0
#guard verifyV6Blake3 { validBlake3 with quotCap := mkDigest32 78 } == 0
#guard verifyV6Blake3 { validBlake3 with evalX0 := { c0 := 44, c1 := 89, c2 := 137 } } == 0
#guard verifyV6Blake3 { validBlake3 with friSibs1 := .cons { c0 := 94, c1 := 144, c2 := 215 } .nil } == 0

-- 5. Real Protocol `v6` Goldilocks $p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$ checks across
--    `Fp3` ring/inverse, AIR + LogUp quotient (`verifyAirQuotient`), and multi-arity FRI (`verifyFriQuery`)
private def glA : Fp3 := { c0 := 1234567890123456789, c1 := 9876543210987654321, c2 := 4242424242424242424 }
private def glB : Fp3 := { c0 := 1111111111111111111, c1 := 2222222222222222222, c2 := 3333333333333333333 }

#guard fp3Mul goldilocksPrime glA (fp3Inv goldilocksPrime glA) == fp3One
#guard fp3Mul goldilocksPrime glA glB == fp3Mul goldilocksPrime glB glA
#guard mulMod goldilocksPrime (twoAdicGen goldilocksFriParams 2) goldilocksFriParams.w2Inv == 1
#guard mulMod goldilocksPrime 2 goldilocksInv2 == 1

private def glPoly4 : Fp3List :=
  .cons { c0 := 3, c1 := 5, c2 := 2 }
  (.cons { c0 := 10, c1 := 16, c2 := 15 }
  (.cons { c0 := 17, c1 := 27, c2 := 28 }
  (.cons { c0 := 24, c1 := 38, c2 := 41 } .nil)))

private def glParentBits : BitList := .cons 1 (.cons 1 .nil)
private def glBeta : Fp3 := { c0 := 17, c1 := 29, c2 := 43 }

#guard
  let fp := goldilocksFriParams
  let g := twoAdicGen fp 4
  let s := expByBits fp.p g (bitListRev glParentBits .nil)
  let w := twoAdicGen fp 2
  let sw := mulMod fp.p s w
  let e0 := evalFinalPoly fp.p glPoly4 s
  let e1 := evalFinalPoly fp.p glPoly4 (negMod fp.p s)
  let e2 := evalFinalPoly fp.p glPoly4 sw
  let e3 := evalFinalPoly fp.p glPoly4 (negMod fp.p sw)
  friFold4 fp glParentBits 2 glBeta e0 e1 e2 e3 == evalPolyExt fp.p glPoly4 glBeta

private def glAirFrame (q0Delta : Nat) : AirFrameInput :=
  { nodes := sampleAirNodes
    roots := sampleAirRoots
    lookups := sampleLookups
    groupSize := 2
    maxDepth := 5
    log := 3
    genMax := goldilocksGen32
    maxLog := 32
    main := .cons 11 (.cons 23 .nil)
    mainNext := .cons 29 (.cons 31 .nil)
    fixed := .cons 13 (.cons 17 .nil)
    fixedNext := .cons 19 (.cons 21 .nil)
    stage2 := .cons 42 (.cons 55 .nil)
    stage2Next := .cons 61 (.cons 73 .nil)
    quotientOpen := .cons (addMod goldilocksPrime 2921308523684807209 q0Delta) (.cons 42 .nil)
    pub0 := 777
    beta := 111
    gamma := 222
    alpha := 333
    zeta := 123456789
    acc := 77
    nextAcc := 99 }

#guard verifyAirQuotient goldilocksPrime (glAirFrame 0) == 1
#guard verifyAirQuotient goldilocksPrime (glAirFrame 1) == 0

private def glFriTest (tamperFinal : Nat) : Nat :=
  let fp := goldilocksFriParams
  let p := fp.p
  let qBits := bitsOf4 11
  let x0 := expByBits p (twoAdicGen fp 4) (bitListRev qBits .nil)
  let zeta : Fp3 := { c0 := 19, c1 := 37, c2 := 53 }
  let evalZeta : Fp3 := { c0 := 11, c1 := 2921308523684807209, c2 := 42 }
  let evalX0 : Fp3 := { c0 := 1234567890123, c1 := 9876543210987, c2 := 4242424242424 }
  let initFolded := deepQuotient p zeta x0 evalZeta evalX0
  let r0 : FriRound :=
    { logArity := 2
      beta := { c0 := 17, c1 := 29, c2 := 43 }
      sibs :=
        .cons { c0 := 111, c1 := 222, c2 := 333 }
        (.cons { c0 := 444, c1 := 555, c2 := 666 }
        (.cons { c0 := 777, c1 := 888, c2 := 999 } .nil))
      hasRollin := 1
      rollin := { c0 := 1001, c1 := 2002, c2 := 3003 } }
  let r1 : FriRound :=
    { logArity := 1
      beta := { c0 := 31, c1 := 47, c2 := 59 }
      sibs := .cons { c0 := 13579, c1 := 24680, c2 := 97531 } .nil
      hasRollin := 0
      rollin := fp3Zero }
  let finalCoeffs : Fp3List :=
    .cons { c0 := addMod p 5898465325124117256 tamperFinal
            c1 := 1087034718983181511
            c2 := 12973924308681512844 }
    (.cons { c0 := 55555, c1 := 66666, c2 := 77777 } .nil)
  verifyFriQuery fp initFolded qBits 4 1 (.cons r0 (.cons r1 .nil)) finalCoeffs

#guard glFriTest 0 == 1
#guard glFriTest 1 == 0

end MultiStarkV6Pure
