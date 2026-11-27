import Ix.Compile.CircuitContract
import IxCCAiur.Compression.KzgWire

/-! # Single-Source Pure Annotated Lean 4 Optimal Ate `PairingCheck` Verifier (BN254 & BLS12-381)

Pure total Lean 4 specification (ONLY `import Ix.Compile.CircuitContract` and
`import IxCCAiur.Compression.KzgWire`; ZERO `MultiStark`, `Aiur`, `IxCC`, or Mathlib
imports, zero forbidden constructs) eliminating `tools/gnark`'s unverified Go
`PairingCheck` gadget (`sw_bn254.PairingCheck` & `sw_bls12381.PairingCheck`) via a
single-source optimal Ate pairing verifier parameterized by `PairingParams`:

1. **Tower Extension Fields ($\mathbb{F}_{q^2}, \mathbb{F}_{q^6}, \mathbb{F}_{q^{12}}$)**:
   - Reuses `KzgWire`'s non-native `Fq` arithmetic (`fqAddMod`, `fqSubMod`,
     and Tier-2 `checked def` guesses `fqMulMod`, `fqInvMod`) plus `Limb4` (`4×80b` for
     BN254) and `Limb5` (`5×80b` for BLS12-381) canonical limb codecs.
   - Branchless `fqNeg` (`fqSubMod q 0 a`) and tail-position short-circuiting predicates
     eliminate join-point chains and `Obj` heap boxing (`memory = 0` across every tower
     & pairing chip).
   - `Fp2` ($\mathbb{F}_q[u]/(u^2 + 1)$ on both BN254 and BLS12-381): `add`, `sub`,
     `neg`, `mul` (Karatsuba), `sqr`, `conj`, `mulByFq`, `mulByNonResidue` ($\xi = 9+u$
     on BN254, $\xi = 1+u$ on BLS12-381), `inv`, `eq`, `isZero`, `isOne`.
   - `Fp6` ($\mathbb{F}_{q^2}[v]/(v^3 - \xi)$): `add`, `sub`, `neg`, `mul`, `sqr`,
     `mulByNonResidue` ($v \cdot a$), `mulByFp2`, sparse `mulBy01` / `mulBy1`, `inv`,
     and Frobenius endomorphisms $\pi_q, \pi_{q^2}, \pi_{q^3}$.
   - `Fp12` ($\mathbb{F}_{q^6}[w]/(w^2 - v)$): `add`, `sub`, `neg`, `mul`, complex `sqr`,
     `conj` (exact $q^6$-Frobenius / unitary inverse), general `inv` via `Fp6`, sparse
     line multiplications `mulBy034` (D-type twist BN254) and `mulBy014` (M-type twist
     BLS12-381), binary `pow`, and exact Frobenius maps $\pi_q, \pi_{q^2}, \pi_{q^3}$.
2. **2-Pairing Optimal Ate Miller Loop (`millerLoop2`, `millerLoop2Binary`, `millerLoop2Prepared`)**:
   - Inversion-free homogeneous projective `G2` line steps (`g2DoubleStep`, `g2AddStep`),
     matching `ark-bn254 0.5.0` and `ark-bls12-381 0.5.0` bit-for-bit on every `Fp12`
     coordinate.
   - **BN254**: Optimal Ate loop over `6x + 2 = 29793968203157093288` (D-type twist
     $E': y^2 = x^3 + 3/(9+u)$) plus the two Frobenius adjustment lines
     $\ell_{[6x+2]Q, \pi(Q)}(P)$ and $\ell_{[6x+2]Q + \pi(Q), -\pi^2(Q)}(P)$.
   - **BLS12-381**: Optimal Ate loop over $|x| = \text{0xd201000000010000}$ (M-type twist
     $E': y^2 = x^3 + 4(1+u)$) with negative-seed conjugation (`fp12Conj`) and exact
     prime-order `G1` subgroup membership check $[x^2]P = -\psi(P)$ (Bowe 2019/814,
     rejecting every cofactor torsion point on $E(\mathbb{F}_q)$!).
   - Clean infinity handling (`inf = 1 → (0,0)`, `inf = 0 → (x,y) ≠ (0,0) ∧ onCurve`,
     skipping line evaluation when $P_i = \mathcal{O}$ or $Q_i = \mathcal{O}$).
3. **Sound Residue-Witnessed Final Exponentiation Check (`verifyFinalExpWitness`)**:
   - Proves $f^{(q^{12}-1)/r} = 1$ with **zero inversions** using a single prover witness
     $c \in \mathbb{F}_{q^{12}}^*$ via the unitary identity $f^{q^6 - 1} = c^\lambda$:
     - **BN254** ($\lambda = 6x + 2 + q - q^2 + q^3$, $r \mid \lambda$,
       $\gcd(\lambda, (q^6+1)/r) = 1$, $\gcd(r, q^6-1) = 1$): checks $f \neq 0$, $c \neq 0$,
       and $\bar{f} \cdot c^{q^2} = f \cdot c^{6x+2} \cdot c^q \cdot c^{q^3}$.
     - **BLS12-381** ($\lambda = q - x = q + |x|$, $r \mid \lambda$,
       $\gcd(\lambda, (q^6+1)/r) = 1$, $\gcd(r, q^6-1) = 1$): checks $f \neq 0$, $c \neq 0$,
       and $\bar{f} = f \cdot c^q \cdot c^{|x|}$ (and $\bar{f} \cdot c^x = f \cdot c^q$
       for positive-seed BLS12 curves).
   - **Soundness**: Raising $f^{q^6-1} = c^\lambda$ to $E = (q^{12}-1)/r$ yields
     $(f^E)^{q^6-1} = (c^{q^{12}-1})^{\lambda/r} = 1$; since $(f^E)^r = 1$ and
     $\gcd(q^6 - 1, r) = 1$, this forces $f^E = 1$.
   - **Completeness**: For any $f \in \mathbb{F}_{q^{12}}^*$ with $f^E = 1$,
     $f_1 = \bar{f} \cdot f^{-1}$ has order dividing $M = (q^6+1)/r$; since
     $\gcd(\lambda, M) = 1$ on BOTH BN254 and BLS12-381, $c = f_1^{\lambda^{-1} \bmod M}$
     always exists and satisfies $\bar{f} = f \cdot c^\lambda$.
   - Also provides the fixed $d = 3$ residue-table verifier `verifyFinalExpTableBN254`
     (since $\gcd(\lambda_{\mathrm{BN}}/r, (q^{12}-1)/r) = 3$, with compile-time table
     $w_k = \zeta_{27}^k \in \mathbb{F}_{q^6}^*$ satisfying $w_k^{(q^{12}-1)/r} = 1$;
     whereas on BLS12-381 $\gcd((q-x)/r, (q^{12}-1)/r) = 1 - x = 3 \cdot 5044125407647214251$
     divides $q^6 - 1$, making the unitary / $\mathbb{F}_{q^6}^*$-scaling form both
     complete and sound for all valid pairings).
4. **Live-Exportable Entrypoints (`plonk_export`, `private_outputs: 0`)**:
   - `entryFp12MulBN254`, `entryFp12MulBLS12381` (fast-compile $\mathbb{F}_{q^{12}}$ mul,
     inv, and Frobenius smoke entrypoints with **0 ROM / 0 memory**),
   - `entryPairingCheckBN254`, `entryPairingCheckBLS12381` (full 18-word / 22-word affine
     2-pairing optimal Ate + residue-witnessed final exp verifiers instantiated on genuine
     `< 2^56` pairing-friendly BN (`q = 103, r = 97, x = 1`) and BLS12 (`q = 727, r = 241,
     x = 4, h₁ = 3`) curves with static G2 anchors and **0 ROM / 0 memory**).
-/

set_option autoImplicit false

open scoped Ix.Circuit
open KzgWire

namespace PairingPure

/-! ## Section 1: Monomorphic Unboxed Tower & Pairing ADTs (`ShapeInfer`-Unboxed, 0 ROM) -/

/-- Element of $\mathbb{F}_{q^2} = \mathbb{F}_q[u]/(u^2 + 1)$ (`c0 + c1 * u`). -/
structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving BEq, DecidableEq, Repr

/-- Element of $\mathbb{F}_{q^6} = \mathbb{F}_{q^2}[v]/(v^3 - \xi)$ (`c0 + c1 * v + c2 * v^2`). -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving BEq, DecidableEq, Repr

/-- Element of $\mathbb{F}_{q^{12}} = \mathbb{F}_{q^6}[w]/(w^2 - v)$ (`c0 + c1 * w`). -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving BEq, DecidableEq, Repr

/-- Jacobian projective `G1` point `(x : y : z)` representing `(x/z², y/z³)` (`z = 0` is `O`)
for inversion-free BLS12 prime-order subgroup checks (`[x²]P = -ψ(P)`). -/
structure G1Jac where
  x : Nat
  y : Nat
  z : Nat
  deriving BEq, DecidableEq, Repr

/-- Canonical affine `G2` point over $\mathbb{F}_{q^2}$ on the sextic twist $E'$. -/
structure G2Point where
  x : Fp2
  y : Fp2
  isInf : Nat
  deriving BEq, DecidableEq, Repr

/-- Homogeneous projective `G2` accumulator `(x : y : z)` for inversion-free Miller loops. -/
structure G2Proj where
  x : Fp2
  y : Fp2
  z : Fp2
  deriving BEq, DecidableEq, Repr

/-- Sparse line evaluation coefficients `(c0, c1, c2)` matching `ark-ec` `EllCoeff`. -/
structure EllCoeff where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving BEq, DecidableEq, Repr

/-- Monomorphic output of `g2DoubleStep` / `g2AddStep` (zero `Prod` boxing). -/
structure EllStep where
  next : G2Proj
  coeff : EllCoeff
  deriving BEq, DecidableEq, Repr

/-- Monomorphic single-pair Miller step output (zero `Prod` boxing). -/
structure SingleMillerOut where
  f : Fp12
  t : G2Proj
  deriving BEq, DecidableEq, Repr

/-- Monomorphic joint 2-pairing Miller loop state. -/
structure MillerState where
  f : Fp12
  t0 : G2Proj
  t1 : G2Proj
  deriving BEq, DecidableEq, Repr

/-- Monomorphic result of decoding one canonical `Fq` coordinate from limbs. -/
structure DecodeFqResult where
  ok : Nat
  val : Nat
  deriving BEq, DecidableEq, Repr

/-- Monomorphic result of decoding a canonical affine `G1` point from limb words. -/
structure DecodeG1Result where
  ok : Nat
  point : G1Point
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of optimal Ate loop digits (`0`: skip, `1`: `+Q`, `2`: `-Q`). -/
inductive BitList where
  | nil
  | cons (digit : Nat) (tail : BitList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic list of precomputed `G2` line evaluations. -/
inductive EllCoeffList where
  | nil
  | cons (head : EllCoeff) (tail : EllCoeffList)
  deriving BEq, DecidableEq, Repr

/-- Monomorphic cursor output for consuming one precomputed line coefficient. -/
structure LinePop where
  has : Nat
  coeff : EllCoeff
  rest : EllCoeffList
  deriving BEq, DecidableEq, Repr

/-- Monomorphic state for prepared-line Miller loop walk. -/
structure PrepMillerState where
  f : Fp12
  l0 : EllCoeffList
  l1 : EllCoeffList
  deriving BEq, DecidableEq, Repr

/-- Single-source 100% flat (non-recursive, zero-ROM) pairing curve & $\mathbb{F}_{q^{12}}$
tower descriptor covering production 254-bit BN254, production 381-bit BLS12-381, and
genuine `< 2^56` pairing-friendly BN (`q = 103, r = 97`) and BLS12 (`q = 727, r = 241`)
circuit curves. -/
structure PairingParams where
  curve : CurveParams
  isBn : Nat
  isNegSeed : Nat
  xi0 : Nat
  twoInv : Nat
  bTwist : Fp2
  g2Gen : G2Point
  twistMulByQX : Fp2
  twistMulByQY : Fp2
  g1EndoBeta : Nat
  loopExp : Nat
  loopBits : Nat
  loopTopPow2 : Nat
  frob6C1_1 : Fp2
  frob6C2_1 : Fp2
  frob6C1_2 : Fp2
  frob6C2_2 : Fp2
  frob6C1_3 : Fp2
  frob6C2_3 : Fp2
  frob12C1_1 : Fp2
  frob12C1_2 : Fp2
  frob12C1_3 : Fp2
  topLimbBound : Nat
  deriving BEq, DecidableEq, Repr

/-! ## Section 2: Branchless `Fq` Negation & Zero-Join-Point Monus Predicates -/

/-- Branchless non-native `Fq` negation `(-a) mod q = (q - a) % q` for canonical `a < q`
(identical to `KzgWire.fqNegMod`, zero `if` join points in callers!). -/
@[circuit_noinline]
def fqNeg (q a : Nat) : Nat :=
  fqSubMod q 0 a

/-- Branchless `Nat` symmetric monus distance `|a - b|`: equals `0` iff `a = b`. -/
@[circuit_inline]
def natAbsDiff (a b : Nat) : Nat :=
  (a - b) + (b - a)

/-- Branchless `Nat` strict upper-bound excess `(a + 1) - bound`: equals `0` iff `a < bound`. -/
@[circuit_inline]
def natLtErr (a bound : Nat) : Nat :=
  (a + 1) - bound

/-! ## Section 3: Tower Extension Field $\mathbb{F}_{q^2}$ (`u² + 1 = 0`) -/

@[circuit_inline]
def fp2Zero : Fp2 := { c0 := 0, c1 := 0 }

@[circuit_inline]
def fp2One : Fp2 := { c0 := 1, c1 := 0 }

@[circuit_inline]
def fp2Sum (a : Fp2) : Nat :=
  a.c0 + a.c1

@[circuit_noinline]
def fp2Diff (a b : Fp2) : Nat :=
  natAbsDiff a.c0 b.c0 + natAbsDiff a.c1 b.c1

@[circuit_noinline]
def fp2CanonErr (q : Nat) (a : Fp2) : Nat :=
  natLtErr a.c0 q + natLtErr a.c1 q

@[circuit_inline]
def fp2IsZero (a : Fp2) : Bool :=
  fp2Sum a == 0

@[circuit_inline]
def fp2IsOne (a : Fp2) : Bool :=
  natAbsDiff a.c0 1 + a.c1 == 0

@[circuit_inline]
def fp2Eq (a b : Fp2) : Bool :=
  fp2Diff a b == 0

@[circuit_inline]
def fp2Canonical (q : Nat) (a : Fp2) : Bool :=
  fp2CanonErr q a == 0

@[circuit_noinline]
def fp2Add (q : Nat) (a b : Fp2) : Fp2 :=
  { c0 := fqAddMod q a.c0 b.c0, c1 := fqAddMod q a.c1 b.c1 }

@[circuit_noinline]
def fp2Sub (q : Nat) (a b : Fp2) : Fp2 :=
  { c0 := fqSubMod q a.c0 b.c0, c1 := fqSubMod q a.c1 b.c1 }

@[circuit_noinline]
def fp2Neg (q : Nat) (a : Fp2) : Fp2 :=
  { c0 := fqNeg q a.c0, c1 := fqNeg q a.c1 }

@[circuit_noinline]
def fp2Conj (q : Nat) (a : Fp2) : Fp2 :=
  { c0 := a.c0, c1 := fqNeg q a.c1 }

@[circuit_inline]
def fp2Double (q : Nat) (a : Fp2) : Fp2 :=
  fp2Add q a a

@[circuit_inline]
def fp2Triple (q : Nat) (a : Fp2) : Fp2 :=
  fp2Add q (fp2Add q a a) a

@[circuit_noinline]
def fp2MulByFq (q : Nat) (a : Fp2) (s : Nat) : Fp2 :=
  { c0 := fqMulMod q a.c0 s, c1 := fqMulMod q a.c1 s }

/-- Karatsuba multiplication in $\mathbb{F}_{q^2} = \mathbb{F}_q[u]/(u^2 + 1)$ (3 `fqMulMod`s). -/
@[circuit_noinline]
def fp2Mul (q : Nat) (a b : Fp2) : Fp2 :=
  let v0 := fqMulMod q a.c0 b.c0
  let v1 := fqMulMod q a.c1 b.c1
  let s0 := fqAddMod q a.c0 a.c1
  let s1 := fqAddMod q b.c0 b.c1
  let p01 := fqMulMod q s0 s1
  let c0 := fqSubMod q v0 v1
  let c1 := fqSubMod q (fqSubMod q p01 v0) v1
  { c0, c1 }

/-- Complex squaring in $\mathbb{F}_{q^2} = \mathbb{F}_q[u]/(u^2 + 1)$ (2 `fqMulMod`s). -/
@[circuit_noinline]
def fp2Sqr (q : Nat) (a : Fp2) : Fp2 :=
  let ab := fqMulMod q a.c0 a.c1
  let sum := fqAddMod q a.c0 a.c1
  let diff := fqSubMod q a.c0 a.c1
  let c0 := fqMulMod q sum diff
  let c1 := fqAddMod q ab ab
  { c0, c1 }

/-- Multiply by cubic/quadratic non-residue $\xi = \xi_0 + u \in \mathbb{F}_{q^2}$:
`(a0 + a1*u) * (xi0 + u) = (a0*xi0 - a1) + (a0 + a1*xi0)*u`. -/
@[circuit_noinline]
def fp2MulByNonResidue (q xi0 : Nat) (a : Fp2) : Fp2 :=
  let t0 := fqMulMod q a.c0 xi0
  let t1 := fqMulMod q a.c1 xi0
  { c0 := fqSubMod q t0 a.c1, c1 := fqAddMod q a.c0 t1 }

/-- Multiplicative inverse in $\mathbb{F}_{q^2}$ (`0⁻¹ = 0`) using `KzgWire.fqInvMod` guess. -/
@[circuit_noinline]
def fp2Inv (q : Nat) (a : Fp2) : Fp2 :=
  let n0 := fqMulMod q a.c0 a.c0
  let n1 := fqMulMod q a.c1 a.c1
  let norm := fqAddMod q n0 n1
  let invNorm := fqInvMod q norm
  { c0 := fqMulMod q a.c0 invNorm, c1 := fqNeg q (fqMulMod q a.c1 invNorm) }

/-! ## Section 4: Tower Extension Field $\mathbb{F}_{q^6}$ (`v³ = ξ`) -/

@[circuit_inline]
def fp6Zero : Fp6 := { c0 := fp2Zero, c1 := fp2Zero, c2 := fp2Zero }

@[circuit_inline]
def fp6One : Fp6 := { c0 := fp2One, c1 := fp2Zero, c2 := fp2Zero }

@[circuit_noinline]
def fp6Sum (a : Fp6) : Nat :=
  fp2Sum a.c0 + fp2Sum a.c1 + fp2Sum a.c2

@[circuit_noinline]
def fp6Diff (a b : Fp6) : Nat :=
  fp2Diff a.c0 b.c0 + fp2Diff a.c1 b.c1 + fp2Diff a.c2 b.c2

@[circuit_noinline]
def fp6CanonErr (q : Nat) (a : Fp6) : Nat :=
  fp2CanonErr q a.c0 + fp2CanonErr q a.c1 + fp2CanonErr q a.c2

@[circuit_inline]
def fp6IsZero (a : Fp6) : Bool :=
  fp6Sum a == 0

@[circuit_inline]
def fp6IsOne (a : Fp6) : Bool :=
  natAbsDiff a.c0.c0 1 + a.c0.c1 + fp2Sum a.c1 + fp2Sum a.c2 == 0

@[circuit_inline]
def fp6Eq (a b : Fp6) : Bool :=
  fp6Diff a b == 0

@[circuit_inline]
def fp6Canonical (q : Nat) (a : Fp6) : Bool :=
  fp6CanonErr q a == 0

@[circuit_noinline]
def fp6Add (q : Nat) (a b : Fp6) : Fp6 :=
  { c0 := fp2Add q a.c0 b.c0, c1 := fp2Add q a.c1 b.c1, c2 := fp2Add q a.c2 b.c2 }

@[circuit_noinline]
def fp6Sub (q : Nat) (a b : Fp6) : Fp6 :=
  { c0 := fp2Sub q a.c0 b.c0, c1 := fp2Sub q a.c1 b.c1, c2 := fp2Sub q a.c2 b.c2 }

@[circuit_noinline]
def fp6Neg (q : Nat) (a : Fp6) : Fp6 :=
  { c0 := fp2Neg q a.c0, c1 := fp2Neg q a.c1, c2 := fp2Neg q a.c2 }

/-- Multiply an $\mathbb{F}_{q^6}$ element by the non-residue $v$:
`(c0 + c1*v + c2*v^2) * v = (xi*c2) + c0*v + c1*v^2`. -/
@[circuit_noinline]
def fp6MulByNonResidue (q xi0 : Nat) (a : Fp6) : Fp6 :=
  { c0 := fp2MulByNonResidue q xi0 a.c2, c1 := a.c0, c2 := a.c1 }

/-- Scalar multiplication of $\mathbb{F}_{q^6}$ by an $\mathbb{F}_{q^2}$ element. -/
@[circuit_noinline]
def fp6MulByFp2 (q : Nat) (a : Fp6) (s : Fp2) : Fp6 :=
  { c0 := fp2Mul q a.c0 s, c1 := fp2Mul q a.c1 s, c2 := fp2Mul q a.c2 s }

/-- Karatsuba multiplication in $\mathbb{F}_{q^6} = \mathbb{F}_{q^2}[v]/(v^3 - \xi)$ (6 `fp2Mul`s). -/
@[circuit_noinline]
def fp6Mul (q xi0 : Nat) (a b : Fp6) : Fp6 :=
  let v0 := fp2Mul q a.c0 b.c0
  let v1 := fp2Mul q a.c1 b.c1
  let v2 := fp2Mul q a.c2 b.c2
  let t12 := fp2Sub q (fp2Sub q (fp2Mul q (fp2Add q a.c1 a.c2) (fp2Add q b.c1 b.c2)) v1) v2
  let c0 := fp2Add q v0 (fp2MulByNonResidue q xi0 t12)
  let t01 := fp2Sub q (fp2Sub q (fp2Mul q (fp2Add q a.c0 a.c1) (fp2Add q b.c0 b.c1)) v0) v1
  let c1 := fp2Add q t01 (fp2MulByNonResidue q xi0 v2)
  let t02 := fp2Sub q (fp2Sub q (fp2Mul q (fp2Add q a.c0 a.c2) (fp2Add q b.c0 b.c2)) v0) v2
  let c2 := fp2Add q t02 v1
  { c0, c1, c2 }

/-- Squaring in $\mathbb{F}_{q^6}$ (CH-SQR2: 3 `fp2Sqr` + 2 `fp2Mul`). -/
@[circuit_noinline]
def fp6Sqr (q xi0 : Nat) (a : Fp6) : Fp6 :=
  let s0 := fp2Sqr q a.c0
  let ab := fp2Mul q a.c0 a.c1
  let s1 := fp2Add q ab ab
  let s2 := fp2Sqr q (fp2Add q (fp2Sub q a.c0 a.c1) a.c2)
  let bc := fp2Mul q a.c1 a.c2
  let s3 := fp2Add q bc bc
  let s4 := fp2Sqr q a.c2
  let c0 := fp2Add q s0 (fp2MulByNonResidue q xi0 s3)
  let c1 := fp2Add q s1 (fp2MulByNonResidue q xi0 s4)
  let c2 := fp2Sub q (fp2Sub q (fp2Add q (fp2Add q s1 s2) s3) s0) s4
  { c0, c1, c2 }

/-- Sparse multiplication in $\mathbb{F}_{q^6}$ by `(b0 + b1*v + 0*v^2)` (`ark-ff` `mul_by_01`). -/
@[circuit_noinline]
def fp6MulBy01 (q xi0 : Nat) (a : Fp6) (b0 b1 : Fp2) : Fp6 :=
  let aa := fp2Mul q a.c0 b0
  let bb := fp2Mul q a.c1 b1
  let t1 := fp2Add q (fp2MulByNonResidue q xi0 (fp2Sub q (fp2Mul q b1 (fp2Add q a.c1 a.c2)) bb)) aa
  let t3 := fp2Add q (fp2Sub q (fp2Mul q b0 (fp2Add q a.c0 a.c2)) aa) bb
  let t2 := fp2Sub q (fp2Sub q (fp2Mul q (fp2Add q b0 b1) (fp2Add q a.c0 a.c1)) aa) bb
  { c0 := t1, c1 := t2, c2 := t3 }

/-- Sparse multiplication in $\mathbb{F}_{q^6}$ by `(0 + b1*v + 0*v^2)` (`ark-ff` `mul_by_1`). -/
@[circuit_noinline]
def fp6MulBy1 (q xi0 : Nat) (a : Fp6) (b1 : Fp2) : Fp6 :=
  { c0 := fp2MulByNonResidue q xi0 (fp2Mul q a.c2 b1)
    c1 := fp2Mul q a.c0 b1
    c2 := fp2Mul q a.c1 b1 }

/-- Multiplicative inverse in $\mathbb{F}_{q^6}$ (`0⁻¹ = 0`). -/
@[circuit_noinline]
def fp6Inv (q xi0 : Nat) (a : Fp6) : Fp6 :=
  let c0 := fp2Sub q (fp2Sqr q a.c0) (fp2MulByNonResidue q xi0 (fp2Mul q a.c1 a.c2))
  let c1 := fp2Sub q (fp2MulByNonResidue q xi0 (fp2Sqr q a.c2)) (fp2Mul q a.c0 a.c1)
  let c2 := fp2Sub q (fp2Sqr q a.c1) (fp2Mul q a.c0 a.c2)
  let t := fp2Add q (fp2Mul q a.c0 c0)
    (fp2MulByNonResidue q xi0 (fp2Add q (fp2Mul q a.c2 c1) (fp2Mul q a.c1 c2)))
  let invT := fp2Inv q t
  { c0 := fp2Mul q c0 invT, c1 := fp2Mul q c1 invT, c2 := fp2Mul q c2 invT }

/-- Odd-power Frobenius map (`π_q` or `π_{q^3}`) in $\mathbb{F}_{q^6}$ (branchless!). -/
@[circuit_noinline]
def fp6FrobOdd (q : Nat) (k1 k2 : Fp2) (a : Fp6) : Fp6 :=
  { c0 := fp2Conj q a.c0
    c1 := fp2Mul q (fp2Conj q a.c1) k1
    c2 := fp2Mul q (fp2Conj q a.c2) k2 }

/-- Even-power Frobenius map (`π_{q^2}`) in $\mathbb{F}_{q^6}$ (branchless!). -/
@[circuit_noinline]
def fp6FrobEven (q : Nat) (k1 k2 : Fp2) (a : Fp6) : Fp6 :=
  { c0 := a.c0
    c1 := fp2Mul q a.c1 k1
    c2 := fp2Mul q a.c2 k2 }

@[circuit_inline]
def fp6Frob1 (p : PairingParams) (a : Fp6) : Fp6 :=
  fp6FrobOdd p.curve.fqMod p.frob6C1_1 p.frob6C2_1 a

@[circuit_inline]
def fp6Frob2 (p : PairingParams) (a : Fp6) : Fp6 :=
  fp6FrobEven p.curve.fqMod p.frob6C1_2 p.frob6C2_2 a

@[circuit_inline]
def fp6Frob3 (p : PairingParams) (a : Fp6) : Fp6 :=
  fp6FrobOdd p.curve.fqMod p.frob6C1_3 p.frob6C2_3 a

/-! ## Section 5: Tower Extension Field $\mathbb{F}_{q^{12}}$ (`w² = v`) -/

@[circuit_inline]
def fp12Zero : Fp12 := { c0 := fp6Zero, c1 := fp6Zero }

@[circuit_inline]
def fp12One : Fp12 := { c0 := fp6One, c1 := fp6Zero }

@[circuit_noinline]
def fp12Sum (a : Fp12) : Nat :=
  fp6Sum a.c0 + fp6Sum a.c1

@[circuit_noinline]
def fp12Diff (a b : Fp12) : Nat :=
  fp6Diff a.c0 b.c0 + fp6Diff a.c1 b.c1

@[circuit_noinline]
def fp12CanonErr (q : Nat) (a : Fp12) : Nat :=
  fp6CanonErr q a.c0 + fp6CanonErr q a.c1

@[circuit_inline]
def fp12IsZero (a : Fp12) : Bool :=
  fp12Sum a == 0

@[circuit_inline]
def fp12IsOne (a : Fp12) : Bool :=
  natAbsDiff a.c0.c0.c0 1 + a.c0.c0.c1 + fp2Sum a.c0.c1 + fp2Sum a.c0.c2 + fp6Sum a.c1 == 0

@[circuit_inline]
def fp12Eq (a b : Fp12) : Bool :=
  fp12Diff a b == 0

@[circuit_inline]
def fp12Canonical (q : Nat) (a : Fp12) : Bool :=
  fp12CanonErr q a == 0

/-- Embed an $\mathbb{F}_{q^6}$ element into $\mathbb{F}_{q^{12}}$ (`c0 = s, c1 = 0`). -/
@[circuit_inline]
def fp12OfFp6 (s : Fp6) : Fp12 :=
  { c0 := s, c1 := fp6Zero }

@[circuit_noinline]
def fp12Add (q : Nat) (a b : Fp12) : Fp12 :=
  { c0 := fp6Add q a.c0 b.c0, c1 := fp6Add q a.c1 b.c1 }

@[circuit_noinline]
def fp12Sub (q : Nat) (a b : Fp12) : Fp12 :=
  { c0 := fp6Sub q a.c0 b.c0, c1 := fp6Sub q a.c1 b.c1 }

@[circuit_noinline]
def fp12Neg (q : Nat) (a : Fp12) : Fp12 :=
  { c0 := fp6Neg q a.c0, c1 := fp6Neg q a.c1 }

/-- Conjugation $\overline{c_0 + c_1 w} = c_0 - c_1 w = a^{q^6}$ (exact unitary inverse). -/
@[circuit_noinline]
def fp12Conj (q : Nat) (a : Fp12) : Fp12 :=
  { c0 := a.c0, c1 := fp6Neg q a.c1 }

/-- Karatsuba multiplication in $\mathbb{F}_{q^{12}} = \mathbb{F}_{q^6}[w]/(w^2 - v)$ (3 `fp6Mul`s). -/
@[circuit_noinline]
def fp12Mul (q xi0 : Nat) (a b : Fp12) : Fp12 :=
  let v0 := fp6Mul q xi0 a.c0 b.c0
  let v1 := fp6Mul q xi0 a.c1 b.c1
  let c0 := fp6Add q v0 (fp6MulByNonResidue q xi0 v1)
  let c1 := fp6Sub q (fp6Sub q (fp6Mul q xi0 (fp6Add q a.c0 a.c1) (fp6Add q b.c0 b.c1)) v0) v1
  { c0, c1 }

/-- Complex squaring in $\mathbb{F}_{q^{12}}$ (2 `fp6Mul`s instead of 3). -/
@[circuit_noinline]
def fp12Sqr (q xi0 : Nat) (a : Fp12) : Fp12 :=
  let ab := fp6Mul q xi0 a.c0 a.c1
  let s0 := fp6Add q a.c0 a.c1
  let s1 := fp6Add q a.c0 (fp6MulByNonResidue q xi0 a.c1)
  let prod := fp6Mul q xi0 s0 s1
  let c0 := fp6Sub q (fp6Sub q prod ab) (fp6MulByNonResidue q xi0 ab)
  let c1 := fp6Add q ab ab
  { c0, c1 }

/-- General multiplicative inverse in $\mathbb{F}_{q^{12}}$ (`0⁻¹ = 0`) via $\mathbb{F}_{q^6}$ norm. -/
@[circuit_noinline]
def fp12Inv (q xi0 : Nat) (a : Fp12) : Fp12 :=
  let norm := fp6Sub q (fp6Sqr q xi0 a.c0) (fp6MulByNonResidue q xi0 (fp6Sqr q xi0 a.c1))
  let invNorm := fp6Inv q xi0 norm
  { c0 := fp6Mul q xi0 a.c0 invNorm, c1 := fp6Neg q (fp6Mul q xi0 a.c1 invNorm) }

/-- Sparse D-type twist line multiplication in $\mathbb{F}_{q^{12}}$ (`ark-ff` `mul_by_034`). -/
@[circuit_noinline]
def fp12MulBy034 (q xi0 : Nat) (f : Fp12) (c0 c3 c4 : Fp2) : Fp12 :=
  let a := fp6MulByFp2 q f.c0 c0
  let b := fp6MulBy01 q xi0 f.c1 c3 c4
  let e := fp6MulBy01 q xi0 (fp6Add q f.c0 f.c1) (fp2Add q c0 c3) c4
  let resC1 := fp6Sub q e (fp6Add q a b)
  let resC0 := fp6Add q (fp6MulByNonResidue q xi0 b) a
  { c0 := resC0, c1 := resC1 }

/-- Sparse M-type twist line multiplication in $\mathbb{F}_{q^{12}}$ (`ark-ff` `mul_by_014`). -/
@[circuit_noinline]
def fp12MulBy014 (q xi0 : Nat) (f : Fp12) (c0 c1 c4 : Fp2) : Fp12 :=
  let aa := fp6MulBy01 q xi0 f.c0 c0 c1
  let bb := fp6MulBy1 q xi0 f.c1 c4
  let o := fp2Add q c1 c4
  let e := fp6MulBy01 q xi0 (fp6Add q f.c0 f.c1) c0 o
  let resC1 := fp6Sub q (fp6Sub q e aa) bb
  let resC0 := fp6Add q (fp6MulByNonResidue q xi0 bb) aa
  { c0 := resC0, c1 := resC1 }

/-- Odd-power Frobenius (`π_q` or `π_{q^3}`) in $\mathbb{F}_{q^{12}}$ (100% branchless). -/
@[circuit_noinline]
def fp12FrobOdd (q : Nat) (k1 k2 w1 : Fp2) (a : Fp12) : Fp12 :=
  { c0 := fp6FrobOdd q k1 k2 a.c0
    c1 := fp6MulByFp2 q (fp6FrobOdd q k1 k2 a.c1) w1 }

/-- Even-power Frobenius (`π_{q^2}`) in $\mathbb{F}_{q^{12}}$ (100% branchless). -/
@[circuit_noinline]
def fp12FrobEven (q : Nat) (k1 k2 w1 : Fp2) (a : Fp12) : Fp12 :=
  { c0 := fp6FrobEven q k1 k2 a.c0
    c1 := fp6MulByFp2 q (fp6FrobEven q k1 k2 a.c1) w1 }

@[circuit_inline]
def fp12Frob1 (p : PairingParams) (a : Fp12) : Fp12 :=
  fp12FrobOdd p.curve.fqMod p.frob6C1_1 p.frob6C2_1 p.frob12C1_1 a

@[circuit_inline]
def fp12Frob2 (p : PairingParams) (a : Fp12) : Fp12 :=
  fp12FrobEven p.curve.fqMod p.frob6C1_2 p.frob6C2_2 p.frob12C1_2 a

@[circuit_inline]
def fp12Frob3 (p : PairingParams) (a : Fp12) : Fp12 :=
  fp12FrobOdd p.curve.fqMod p.frob6C1_3 p.frob6C2_3 p.frob12C1_3 a

/-- Conditional multiply helper avoiding join-point chains inside `fp12PowFuel`. -/
@[circuit_noinline]
def fp12CondMul (q xi0 bit : Nat) (acc base : Fp12) : Fp12 :=
  match bit with
  | 0 => acc
  | _ => fp12Mul q xi0 acc base

/-- Structural countdown binary exponentiation `acc * base^exp` in $\mathbb{F}_{q^{12}}$. -/
@[circuit_noinline]
def fp12PowFuel (q xi0 : Nat) : Nat → Fp12 → Nat → Fp12 → Fp12
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    match exp with
    | 0 => acc
    | _ =>
      let nextAcc := fp12CondMul q xi0 (exp % 2) acc base
      fp12PowFuel q xi0 fuel (fp12Sqr q xi0 base) (exp / 2) nextAcc
termination_by structural fuel => fuel

/-- Binary exponentiation `base^exp` in $\mathbb{F}_{q^{12}}$ bounded by `bits` bits. -/
@[circuit_inline]
def fp12Pow (q xi0 bits : Nat) (base : Fp12) (exp : Nat) : Fp12 :=
  fp12PowFuel q xi0 bits base exp fp12One

/-! ## Section 6: `G1` Validation, Inversion-Free BLS12 Subgroup Check & Affine Limb Codecs -/

@[circuit_inline]
def g1JacInf : G1Jac :=
  { x := 1, y := 1, z := 0 }

/-- Branchless inversion-free Jacobian `G1` doubling `2R` on $E: y^2 = x^3 + b$
(`a = 0`, EFD `dbl-2009-l`): naturally preserves infinity (`R.z = 0 → z3 = 0`) and
handles 2-torsion (`R.y = 0 → z3 = 0`) with **zero `if` branches / zero join points**! -/
@[circuit_noinline]
def g1JacDouble (q : Nat) (R : G1Jac) : G1Jac :=
  let a := fqMulMod q R.x R.x
  let b := fqMulMod q R.y R.y
  let c := fqMulMod q b b
  let xb := fqAddMod q R.x b
  let d0 := fqSubMod q (fqSubMod q (fqMulMod q xb xb) a) c
  let d := fqAddMod q d0 d0
  let e := fqAddMod q (fqAddMod q a a) a
  let f := fqMulMod q e e
  let d2 := fqAddMod q d d
  let x3 := fqSubMod q f d2
  let c2 := fqAddMod q c c
  let c4 := fqAddMod q c2 c2
  let c8 := fqAddMod q c4 c4
  let y3 := fqSubMod q (fqMulMod q e (fqSubMod q d x3)) c8
  let yz := fqMulMod q R.y R.z
  let z3 := fqAddMod q yz yz
  { x := x3, y := y3, z := z3 }

/-- Complete inversion-free Jacobian `G1` addition `R1 + R2` on $E: y^2 = x^3 + b$. -/
@[circuit_noinline]
def g1JacAdd (q : Nat) (R1 R2 : G1Jac) : G1Jac :=
  if R1.z == 0 then R2
  else if R2.z == 0 then R1
  else
    let z1z1 := fqMulMod q R1.z R1.z
    let z2z2 := fqMulMod q R2.z R2.z
    let u1 := fqMulMod q R1.x z2z2
    let u2 := fqMulMod q R2.x z1z1
    let s1 := fqMulMod q R1.y (fqMulMod q R2.z z2z2)
    let s2 := fqMulMod q R2.y (fqMulMod q R1.z z1z1)
    let h := fqSubMod q u2 u1
    let r := fqSubMod q s2 s1
    if h == 0 then
      if r == 0 then g1JacDouble q R1 else g1JacInf
    else
      let hh := fqMulMod q h h
      let hhh := fqMulMod q h hh
      let v := fqMulMod q u1 hh
      let x3 := fqSubMod q (fqSubMod q (fqMulMod q r r) hhh) (fqAddMod q v v)
      let y3 := fqSubMod q (fqMulMod q r (fqSubMod q v x3)) (fqMulMod q s1 hhh)
      let z3 := fqMulMod q (fqMulMod q R1.z R2.z) h
      { x := x3, y := y3, z := z3 }

/-- Structural countdown MSB-to-LSB inversion-free Jacobian scalar multiplication `[k]base`
starting from `acc = base` (leading `1` bit) with `fuel = bits - 1`, `bitMask = topPow2 / 2`. -/
@[circuit_noinline]
def g1JacScalarMulMsb (q k : Nat) : Nat → Nat → G1Jac → G1Jac → G1Jac
  | 0, _, _, acc => acc
  | fuel + 1, bitMask, base, acc =>
    let dbl := g1JacDouble q acc
    let bit := (k / bitMask) % 2
    if bit == 1 then
      g1JacScalarMulMsb q k fuel (bitMask / 2) base (g1JacAdd q dbl base)
    else
      g1JacScalarMulMsb q k fuel (bitMask / 2) base dbl
termination_by structural fuel => fuel

/-- Prime-order `G1` subgroup membership check (100% inversion-free!):
* BN curves (`isBn = 1`, cofactor $h_1 = 1$): every on-curve point is already in $G_1$.
* BLS12 curves (`isBn = 0`, cofactor $h_1 = (x-1)^2/3 > 1$): verifies
  $[x^2]P = -\psi(P)$ in Jacobian coordinates ($Z \neq 0$, $X \equiv \beta x Z^2$,
  $Y \equiv (-y) Z^3 \pmod q$), which implies $[x^4 - x^2 + 1]P = [r]P = \mathcal{O}$
  (Bowe 2019/814) with zero field inversions. -/
@[circuit_noinline]
def g1InSubgroup (p : PairingParams) (P : G1Point) : Bool :=
  if P.isInf == 1 then true
  else if p.isBn == 1 then true
  else
    let q := p.curve.fqMod
    let pJac : G1Jac := { x := P.x, y := P.y, z := 1 }
    let xP := g1JacScalarMulMsb q p.loopExp (p.loopBits - 1) (p.loopTopPow2 / 2) pJac pJac
    let x2P := g1JacScalarMulMsb q p.loopExp (p.loopBits - 1) (p.loopTopPow2 / 2) xP xP
    if x2P.z == 0 then false
    else
      let z2 := fqMulMod q x2P.z x2P.z
      let z3 := fqMulMod q z2 x2P.z
      let psiX := fqMulMod q (fqMulMod q p.g1EndoBeta P.x) z2
      let negY := fqMulMod q (fqNeg q P.y) z3
      natAbsDiff x2P.x psiX + natAbsDiff x2P.y negY == 0

/-- Full `G1` point validation (branchless monus predicates, minimal join points):
1. `isInf ∈ {0, 1}`,
2. `isInf = 1 → (x = 0 ∧ y = 0)`,
3. `isInf = 0 → (x, y) ≠ (0, 0) ∧ x < q ∧ y < q ∧ y² ≡ x³ + b (mod q) ∧ P ∈ G1`. -/
@[circuit_noinline]
def g1Validate (p : PairingParams) (P : G1Point) : Bool :=
  let q := p.curve.fqMod
  if P.isInf == 1 then
    P.x + P.y == 0
  else if P.isInf == 0 then
    if natLtErr P.x q + natLtErr P.y q == 0 then
      if P.x + P.y == 0 then false
      else
        let y2 := fqMulMod q P.y P.y
        let x3 := fqMulMod q (fqMulMod q P.x P.x) P.x
        let rhs := fqAddMod q x3 (p.curve.curveB % q)
        if y2 == rhs then g1InSubgroup p P else false
    else false
  else false

/-- Zero-join-point canonical 4-limb `Fq` decoder under `(radix, topBound, q)`. -/
@[circuit_noinline]
def decodeLimb4Canonical (r topBound q : Nat) (v : Limb4) : DecodeFqResult :=
  let err := natLtErr v.l0 r + natLtErr v.l1 r + natLtErr v.l2 r + natLtErr v.l3 topBound
  if err == 0 then
    let val := v.l0 + r * (v.l1 + r * (v.l2 + r * v.l3))
    if val < q then { ok := 1, val } else { ok := 0, val := 0 }
  else { ok := 0, val := 0 }

/-- Zero-join-point canonical 5-limb `Fq` decoder under `(radix, topBound, q)`. -/
@[circuit_noinline]
def decodeLimb5Canonical (r topBound q : Nat) (v : Limb5) : DecodeFqResult :=
  let err :=
    natLtErr v.l0 r + natLtErr v.l1 r + natLtErr v.l2 r + natLtErr v.l3 r + natLtErr v.l4 topBound
  if err == 0 then
    let val := v.l0 + r * (v.l1 + r * (v.l2 + r * (v.l3 + r * v.l4)))
    if val < q then { ok := 1, val } else { ok := 0, val := 0 }
  else { ok := 0, val := 0 }

/-- Strictly decode & validate a 9-word BN254 `AffineG1BN254` point (canonical limbs,
strict infinity rule, on-curve check, and subgroup check; flat monus error sum). -/
@[circuit_noinline]
def decodeAffineG1BN254 (p : PairingParams) (pt : AffineG1BN254) : DecodeG1Result :=
  let r := p.curve.limbRadix
  let tb := p.topLimbBound
  let limbErr :=
    natLtErr pt.x.l0 r + natLtErr pt.x.l1 r + natLtErr pt.x.l2 r + natLtErr pt.x.l3 tb +
    natLtErr pt.y.l0 r + natLtErr pt.y.l1 r + natLtErr pt.y.l2 r + natLtErr pt.y.l3 tb
  if limbErr == 0 then
    let vx := pt.x.l0 + r * (pt.x.l1 + r * (pt.x.l2 + r * pt.x.l3))
    let vy := pt.y.l0 + r * (pt.y.l1 + r * (pt.y.l2 + r * pt.y.l3))
    let g : G1Point := { x := vx, y := vy, isInf := pt.isInf }
    if g1Validate p g then { ok := 1, point := g }
    else { ok := 0, point := g1Inf }
  else { ok := 0, point := g1Inf }

/-- Strictly decode & validate an 11-word BLS12-381 `AffineG1BLS12381` point (canonical limbs,
strict infinity rule, on-curve check, and BLS12 prime-order subgroup check; flat monus error sum). -/
@[circuit_noinline]
def decodeAffineG1BLS12381 (p : PairingParams) (pt : AffineG1BLS12381) : DecodeG1Result :=
  let r := p.curve.limbRadix
  let tb := p.topLimbBound
  let limbErr :=
    natLtErr pt.x.l0 r + natLtErr pt.x.l1 r + natLtErr pt.x.l2 r + natLtErr pt.x.l3 r + natLtErr pt.x.l4 tb +
    natLtErr pt.y.l0 r + natLtErr pt.y.l1 r + natLtErr pt.y.l2 r + natLtErr pt.y.l3 r + natLtErr pt.y.l4 tb
  if limbErr == 0 then
    let vx := pt.x.l0 + r * (pt.x.l1 + r * (pt.x.l2 + r * (pt.x.l3 + r * pt.x.l4)))
    let vy := pt.y.l0 + r * (pt.y.l1 + r * (pt.y.l2 + r * (pt.y.l3 + r * pt.y.l4)))
    let g : G1Point := { x := vx, y := vy, isInf := pt.isInf }
    if g1Validate p g then { ok := 1, point := g }
    else { ok := 0, point := g1Inf }
  else { ok := 0, point := g1Inf }

/-! ## Section 7: 2-Pairing Optimal Ate Miller Loop (`G2` Projective Lines & `millerLoop2`) -/

/-- Canonical `G2` point at infinity. -/
@[circuit_inline]
def g2Inf : G2Point :=
  { x := fp2Zero, y := fp2Zero, isInf := 1 }

/-- Affine negation `-Q = (x, -y)` in `G2`. -/
@[circuit_noinline]
def g2Neg (q : Nat) (Q : G2Point) : G2Point :=
  if Q.isInf == 1 then g2Inf
  else { x := Q.x, y := fp2Neg q Q.y, isInf := 0 }

/-- Check if an affine `G2` point lies on the twist curve $E': y^2 = x^3 + b'$. -/
@[circuit_noinline]
def g2OnTwist (p : PairingParams) (Q : G2Point) : Bool :=
  let q := p.curve.fqMod
  if Q.isInf == 1 then
    if fp2IsZero Q.x then fp2IsZero Q.y else false
  else if Q.isInf == 0 then
    if fp2Canonical q Q.x then
      if fp2Canonical q Q.y then
        let y2 := fp2Sqr q Q.y
        let x3 := fp2Mul q (fp2Sqr q Q.x) Q.x
        let rhs := fp2Add q x3 p.bTwist
        fp2Eq y2 rhs
      else false
    else false
  else false

/-- Complete affine `G2` point doubling `2Q` on $E': y^2 = x^3 + b'$. -/
@[circuit_noinline]
def g2DoubleAffine (q : Nat) (Q : G2Point) : G2Point :=
  if Q.isInf == 1 then g2Inf
  else if fp2IsZero Q.y then g2Inf
  else
    let num := fp2Triple q (fp2Sqr q Q.x)
    let den := fp2Double q Q.y
    let lam := fp2Mul q num (fp2Inv q den)
    let x3 := fp2Sub q (fp2Sub q (fp2Sqr q lam) Q.x) Q.x
    let y3 := fp2Sub q (fp2Mul q lam (fp2Sub q Q.x x3)) Q.y
    { x := x3, y := y3, isInf := 0 }

/-- Complete affine `G2` point addition `P + Q` on $E': y^2 = x^3 + b'$. -/
@[circuit_noinline]
def g2AddAffine (q : Nat) (P Q : G2Point) : G2Point :=
  if P.isInf == 1 then Q
  else if Q.isInf == 1 then P
  else if fp2Eq P.x Q.x then
    if fp2Eq P.y Q.y then g2DoubleAffine q P
    else g2Inf
  else
    let num := fp2Sub q Q.y P.y
    let den := fp2Sub q Q.x P.x
    let lam := fp2Mul q num (fp2Inv q den)
    let x3 := fp2Sub q (fp2Sub q (fp2Sqr q lam) P.x) Q.x
    let y3 := fp2Sub q (fp2Mul q lam (fp2Sub q P.x x3)) P.y
    { x := x3, y := y3, isInf := 0 }

/-- Structural countdown scalar multiplication in `G2` (for fixture construction & tests). -/
@[circuit_noinline]
def g2ScalarMulFuel (q : Nat) : Nat → Nat → G2Point → G2Point → G2Point
  | 0, _, _, acc => acc
  | fuel + 1, k, cur, acc =>
    match k with
    | 0 => acc
    | _ =>
      let nextAcc := if k % 2 == 1 then g2AddAffine q acc cur else acc
      g2ScalarMulFuel q fuel (k / 2) (g2DoubleAffine q cur) nextAcc
termination_by structural fuel => fuel

@[circuit_inline]
def g2ScalarMul (q k : Nat) (Q : G2Point) : G2Point :=
  g2ScalarMulFuel q 256 k Q g2Inf

/-- Untwist-Frobenius-twist endomorphism $\pi(Q) = (\bar{x} \cdot \xi^{(q-1)/3}, \bar{y} \cdot \xi^{(q-1)/2})$
on BN curves (`ark-ec` `mul_by_char`). -/
@[circuit_noinline]
def g2MulByChar (q : Nat) (twistQX twistQY : Fp2) (Q : G2Point) : G2Point :=
  if Q.isInf == 1 then g2Inf
  else
    { x := fp2Mul q (fp2Conj q Q.x) twistQX
      y := fp2Mul q (fp2Conj q Q.y) twistQY
      isInf := 0 }

/-- Inversion-free homogeneous projective `G2` tangent-line doubling step (`ark-ec` `double_in_place`). -/
@[circuit_noinline]
def g2DoubleStep (q twoInv isBn : Nat) (bTwist : Fp2) (R : G2Proj) : EllStep :=
  let a := fp2MulByFq q (fp2Mul q R.x R.y) twoInv
  let b := fp2Sqr q R.y
  let c := fp2Sqr q R.z
  let e := fp2Mul q bTwist (fp2Triple q c)
  let f := fp2Triple q e
  let g := fp2MulByFq q (fp2Add q b f) twoInv
  let h := fp2Sub q (fp2Sqr q (fp2Add q R.y R.z)) (fp2Add q b c)
  let i := fp2Sub q e b
  let j := fp2Sqr q R.x
  let e2 := fp2Sqr q e
  let nx := fp2Mul q a (fp2Sub q b f)
  let ny := fp2Sub q (fp2Sqr q g) (fp2Triple q e2)
  let nz := fp2Mul q b h
  let j3 := fp2Triple q j
  let negH := fp2Neg q h
  if isBn == 1 then
    { next := { x := nx, y := ny, z := nz }, coeff := { c0 := negH, c1 := j3, c2 := i } }
  else
    { next := { x := nx, y := ny, z := nz }, coeff := { c0 := i, c1 := j3, c2 := negH } }

/-- Inversion-free homogeneous projective `G2` chord-line addition step (`ark-ec` `add_in_place`). -/
@[circuit_noinline]
def g2AddStep (q isBn : Nat) (R : G2Proj) (Q : G2Point) : EllStep :=
  let theta := fp2Sub q R.y (fp2Mul q Q.y R.z)
  let lam := fp2Sub q R.x (fp2Mul q Q.x R.z)
  let c := fp2Sqr q theta
  let d := fp2Sqr q lam
  let e := fp2Mul q lam d
  let f := fp2Mul q R.z c
  let g := fp2Mul q R.x d
  let h := fp2Sub q (fp2Add q e f) (fp2Double q g)
  let nx := fp2Mul q lam h
  let ny := fp2Sub q (fp2Mul q theta (fp2Sub q g h)) (fp2Mul q e R.y)
  let nz := fp2Mul q R.z e
  let j := fp2Sub q (fp2Mul q theta Q.x) (fp2Mul q lam Q.y)
  let negTheta := fp2Neg q theta
  if isBn == 1 then
    { next := { x := nx, y := ny, z := nz }, coeff := { c0 := lam, c1 := negTheta, c2 := j } }
  else
    { next := { x := nx, y := ny, z := nz }, coeff := { c0 := j, c1 := negTheta, c2 := lam } }

/-- Evaluate a sparse line `coeff` at affine `G1` point `P` and multiply into `f ∈ Fp12`.
Skips multiplication (returns `f` unchanged) whenever `P = O`. -/
@[circuit_noinline]
def evalLine (q xi0 isBn : Nat) (f : Fp12) (coeff : EllCoeff) (P : G1Point) : Fp12 :=
  if P.isInf == 1 then f
  else if isBn == 1 then
    let c0 := fp2MulByFq q coeff.c0 P.y
    let c1 := fp2MulByFq q coeff.c1 P.x
    fp12MulBy034 q xi0 f c0 c1 coeff.c2
  else
    let c1 := fp2MulByFq q coeff.c1 P.x
    let c2 := fp2MulByFq q coeff.c2 P.y
    fp12MulBy014 q xi0 f coeff.c0 c1 c2

/-- Monomorphic single-pair double-and-evaluate step (zero `Prod` boxing, zero join points). -/
@[circuit_noinline]
def doubleAndEval (q xi0 twoInv isBn qIsInf : Nat) (bTwist : Fp2)
    (P : G1Point) (T : G2Proj) (f : Fp12) : SingleMillerOut :=
  if P.isInf == 0 then
    if qIsInf == 0 then
      let s := g2DoubleStep q twoInv isBn bTwist T
      { f := evalLine q xi0 isBn f s.coeff P, t := s.next }
    else { f, t := T }
  else { f, t := T }

/-- Monomorphic single-pair add-and-evaluate step (zero `Prod` boxing, zero join points). -/
@[circuit_noinline]
def addAndEval (q xi0 isBn : Nat) (P : G1Point) (Q : G2Point)
    (T : G2Proj) (f : Fp12) : SingleMillerOut :=
  if P.isInf == 0 then
    if Q.isInf == 0 then
      let s := g2AddStep q isBn T Q
      { f := evalLine q xi0 isBn f s.coeff P, t := s.next }
    else { f, t := T }
  else { f, t := T }

/-- Apply the two BN Frobenius adjustment lines $\ell_{T, \pi(Q)}(P)$ and
$\ell_{T + \pi(Q), -\pi^2(Q)}(P)$ for one pair `(P, Q)` (no-op if either is `O`). -/
@[circuit_noinline]
def applyBnFrobLines (q xi0 : Nat) (twistQX twistQY : Fp2)
    (f : Fp12) (T : G2Proj) (P : G1Point) (Q : G2Point) : Fp12 :=
  if P.isInf == 0 then
    if Q.isInf == 0 then
      let q1 := g2MulByChar q twistQX twistQY Q
      let q2 := g2Neg q (g2MulByChar q twistQX twistQY q1)
      let s1 := g2AddStep q 1 T q1
      let f1 := evalLine q xi0 1 f s1.coeff P
      let s2 := g2AddStep q 1 s1.next q2
      evalLine q xi0 1 f1 s2.coeff P
    else f
  else f

/-- Main Miller-loop structural fold over signed NAF/binary `BitList` (`0`: skip, `1`: `+Q`, `2`: `-Q`).
Uses `1^2 = 1` on the first iteration so zero `isFirst` branch/join point is needed. -/
@[circuit_noinline]
def millerLoop2Walk (p : PairingParams) (digits : BitList)
    (P0 P1 : G1Point) (Q0 negQ0 Q1 negQ1 : G2Point) (st : MillerState) : MillerState :=
  match digits with
  | .nil => st
  | .cons digit rest =>
    let q := p.curve.fqMod
    let xi0 := p.xi0
    let f0 := fp12Sqr q xi0 st.f
    let o0 := doubleAndEval q xi0 p.twoInv p.isBn Q0.isInf p.bTwist P0 st.t0 f0
    let o1 := doubleAndEval q xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f
    if digit == 1 then
      let a0 := addAndEval q xi0 p.isBn P0 Q0 o0.t o1.f
      let a1 := addAndEval q xi0 p.isBn P1 Q1 o1.t a0.f
      millerLoop2Walk p rest P0 P1 Q0 negQ0 Q1 negQ1 { f := a1.f, t0 := a0.t, t1 := a1.t }
    else if digit == 2 then
      let a0 := addAndEval q xi0 p.isBn P0 negQ0 o0.t o1.f
      let a1 := addAndEval q xi0 p.isBn P1 negQ1 o1.t a0.f
      millerLoop2Walk p rest P0 P1 Q0 negQ0 Q1 negQ1 { f := a1.f, t0 := a0.t, t1 := a1.t }
    else
      millerLoop2Walk p rest P0 P1 Q0 negQ0 Q1 negQ1 { f := o1.f, t0 := o0.t, t1 := o1.t }
termination_by structural digits

/-- Apply BN Frobenius adjustment lines for both pairs (helper keeping `millerLoop2Finalize` tail-clean). -/
@[circuit_noinline]
def millerLoop2FinishBn (p : PairingParams) (P0 P1 : G1Point) (Q0 Q1 : G2Point)
    (t0 t1 : G2Proj) (f : Fp12) : Fp12 :=
  if p.isBn == 1 then
    let q := p.curve.fqMod
    let xi0 := p.xi0
    let f2 := applyBnFrobLines q xi0 p.twistMulByQX p.twistMulByQY f t0 P0 Q0
    applyBnFrobLines q xi0 p.twistMulByQX p.twistMulByQY f2 t1 P1 Q1
  else f

/-- Finalize a Miller loop state: apply negative-seed conjugation and (on BN curves)
the two Frobenius adjustment lines for each active pair (0 join points). -/
@[circuit_noinline]
def millerLoop2Finalize (p : PairingParams)
    (P0 P1 : G1Point) (Q0 Q1 : G2Point) (st : MillerState) : Fp12 :=
  if p.isNegSeed == 1 then
    millerLoop2FinishBn p P0 P1 Q0 Q1 st.t0 st.t1 (fp12Conj p.curve.fqMod st.f)
  else
    millerLoop2FinishBn p P0 P1 Q0 Q1 st.t0 st.t1 st.f

/-- **Joint 2-Pairing Optimal Ate Miller Loop (`millerLoop2`)** over arbitrary signed NAF
or binary `digits : BitList` (matching `ark-bn254 0.5.0` and `ark-bls12-381 0.5.0` bit-for-bit). -/
@[circuit_noinline]
def millerLoop2 (p : PairingParams) (digits : BitList)
    (P0 : G1Point) (Q0 : G2Point) (P1 : G1Point) (Q1 : G2Point) : Fp12 :=
  let q := p.curve.fqMod
  let t0Init : G2Proj := { x := Q0.x, y := Q0.y, z := fp2One }
  let t1Init : G2Proj := { x := Q1.x, y := Q1.y, z := fp2One }
  let negQ0 := g2Neg q Q0
  let negQ1 := g2Neg q Q1
  let st := millerLoop2Walk p digits P0 P1 Q0 negQ0 Q1 negQ1
    { f := fp12One, t0 := t0Init, t1 := t1Init }
  millerLoop2Finalize p P0 P1 Q0 Q1 st

/-- 100% heap-free (zero-ROM, zero-join-point) MSB-to-LSB binary optimal Ate Miller-loop walk
(starting at mask `bitMask = loopTopPow2 / 2` for `loopBits - 1` steps). -/
@[circuit_noinline]
def millerLoop2BinaryWalk (p : PairingParams) : Nat → Nat →
    G1Point → G1Point → G2Point → G2Point → MillerState → MillerState
  | 0, _, _, _, _, _, st => st
  | fuel + 1, bitMask, P0, P1, Q0, Q1, st =>
    let q := p.curve.fqMod
    let xi0 := p.xi0
    let f0 := fp12Sqr q xi0 st.f
    let o0 := doubleAndEval q xi0 p.twoInv p.isBn Q0.isInf p.bTwist P0 st.t0 f0
    let o1 := doubleAndEval q xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f
    let bit := (p.loopExp / bitMask) % 2
    if bit == 1 then
      let a0 := addAndEval q xi0 p.isBn P0 Q0 o0.t o1.f
      let a1 := addAndEval q xi0 p.isBn P1 Q1 o1.t a0.f
      millerLoop2BinaryWalk p fuel (bitMask / 2) P0 P1 Q0 Q1 { f := a1.f, t0 := a0.t, t1 := a1.t }
    else
      millerLoop2BinaryWalk p fuel (bitMask / 2) P0 P1 Q0 Q1 { f := o1.f, t0 := o0.t, t1 := o1.t }
termination_by structural fuel => fuel

/-- **Heap-Free (0-ROM) Joint 2-Pairing Binary Optimal Ate Miller Loop (`millerLoop2Binary`)**:
walks the binary bits of `p.loopExp` directly (identical to `millerLoop2` for all binary-loop
curves: `bls12381PairingParams`, `bn254CircuitPairingParams`, `bls12381CircuitPairingParams`,
and mathematically equivalent modulo final exp for `bn254PairingParams`). -/
@[circuit_noinline]
def millerLoop2Binary (p : PairingParams)
    (P0 : G1Point) (Q0 : G2Point) (P1 : G1Point) (Q1 : G2Point) : Fp12 :=
  let t0Init : G2Proj := { x := Q0.x, y := Q0.y, z := fp2One }
  let t1Init : G2Proj := { x := Q1.x, y := Q1.y, z := fp2One }
  let st := millerLoop2BinaryWalk p (p.loopBits - 1) (p.loopTopPow2 / 2)
    P0 P1 Q0 Q1 { f := fp12One, t0 := t0Init, t1 := t1Init }
  millerLoop2Finalize p P0 P1 Q0 Q1 st

/-! ### Precomputed-Line `G2` Anchor Variant (`precomputeG2Lines` & `millerLoop2Prepared`) -/

@[circuit_noinline]
def precomputeG2Walk (p : PairingParams) (digits : BitList) (Q negQ : G2Point) (R : G2Proj) :
    EllCoeffList :=
  let q := p.curve.fqMod
  match digits with
  | .nil =>
    if p.isBn == 1 then
      let q1 := g2MulByChar q p.twistMulByQX p.twistMulByQY Q
      let q2 := g2Neg q (g2MulByChar q p.twistMulByQX p.twistMulByQY q1)
      let s1 := g2AddStep q 1 R q1
      let s2 := g2AddStep q 1 s1.next q2
      .cons s1.coeff (.cons s2.coeff .nil)
    else .nil
  | .cons digit rest =>
    let sd := g2DoubleStep q p.twoInv p.isBn p.bTwist R
    if digit == 1 then
      let sa := g2AddStep q p.isBn sd.next Q
      .cons sd.coeff (.cons sa.coeff (precomputeG2Walk p rest Q negQ sa.next))
    else if digit == 2 then
      let sa := g2AddStep q p.isBn sd.next negQ
      .cons sd.coeff (.cons sa.coeff (precomputeG2Walk p rest Q negQ sa.next))
    else
      .cons sd.coeff (precomputeG2Walk p rest Q negQ sd.next)
termination_by structural digits

/-- Precompute all Miller-loop + BN Frobenius line coefficients for a fixed `G2` anchor `Q`. -/
@[circuit_noinline]
def precomputeG2Lines (p : PairingParams) (digits : BitList) (Q : G2Point) : EllCoeffList :=
  if Q.isInf == 1 then .nil
  else
    let init : G2Proj := { x := Q.x, y := Q.y, z := fp2One }
    precomputeG2Walk p digits Q (g2Neg p.curve.fqMod Q) init

@[circuit_inline]
def popLine (ls : EllCoeffList) : LinePop :=
  match ls with
  | .nil => { has := 0, coeff := { c0 := fp2Zero, c1 := fp2Zero, c2 := fp2Zero }, rest := .nil }
  | .cons c rest => { has := 1, coeff := c, rest }

@[circuit_inline]
def evalPoppedLine (q xi0 isBn : Nat) (f : Fp12) (lp : LinePop) (P : G1Point) : Fp12 :=
  if lp.has == 1 then evalLine q xi0 isBn f lp.coeff P else f

@[circuit_noinline]
def millerLoop2PreparedWalk (p : PairingParams) (digits : BitList)
    (P0 P1 : G1Point) (st : PrepMillerState) : PrepMillerState :=
  match digits with
  | .nil => st
  | .cons digit rest =>
    let q := p.curve.fqMod
    let xi0 := p.xi0
    let f0 := fp12Sqr q xi0 st.f
    let p0d := popLine st.l0
    let p1d := popLine st.l1
    let f1 := evalPoppedLine q xi0 p.isBn f0 p0d P0
    let f2 := evalPoppedLine q xi0 p.isBn f1 p1d P1
    if digit == 1 || digit == 2 then
      let p0a := popLine p0d.rest
      let p1a := popLine p1d.rest
      let f3 := evalPoppedLine q xi0 p.isBn f2 p0a P0
      let f4 := evalPoppedLine q xi0 p.isBn f3 p1a P1
      millerLoop2PreparedWalk p rest P0 P1 { f := f4, l0 := p0a.rest, l1 := p1a.rest }
    else
      millerLoop2PreparedWalk p rest P0 P1 { f := f2, l0 := p0d.rest, l1 := p1d.rest }
termination_by structural digits

/-- 2-pairing Miller loop over static precomputed `G2` line tables (exact match with `millerLoop2`). -/
@[circuit_noinline]
def millerLoop2Prepared (p : PairingParams) (digits : BitList)
    (P0 : G1Point) (lines0 : EllCoeffList) (P1 : G1Point) (lines1 : EllCoeffList) : Fp12 :=
  let q := p.curve.fqMod
  let xi0 := p.xi0
  let st := millerLoop2PreparedWalk p digits P0 P1 { f := fp12One, l0 := lines0, l1 := lines1 }
  let f1 := if p.isNegSeed == 1 then fp12Conj q st.f else st.f
  if p.isBn == 1 then
    let p0a := popLine st.l0
    let p0b := popLine p0a.rest
    let p1a := popLine st.l1
    let p1b := popLine p1a.rest
    let f2 := evalPoppedLine q xi0 1 f1 p0a P0
    let f3 := evalPoppedLine q xi0 1 f2 p0b P0
    let f4 := evalPoppedLine q xi0 1 f3 p1a P1
    evalPoppedLine q xi0 1 f4 p1b P1
  else f1

/-! ## Section 8: Sound Residue-Witnessed Final Exponentiation Check -/

/-- **Sound Residue-Witnessed Final Exponentiation Verifier (`verifyFinalExpWitness`)**:
Proves $f^{(q^{12}-1)/r} = 1$ using a single prover-supplied witness $c \in \mathbb{F}_{q^{12}}^*$
with **zero field inversions** and **zero join points**:
1. Checks canonical `c` (`fp12Canonical`), `f ≠ 0`, and `c ≠ 0`.
2. Computes `cLoop = c^{loopExp}` and `cFrob1 = π_q(c)`, `fConj = conj(f) = f^{q^6}`.
3. **BN (`isBn = 1`, $\lambda = 6x + 2 + q - q^2 + q^3$)**:
   checks `conj(f) * c^{q^2} == f * c^{6x+2} * c^q * c^{q^3}`.
4. **BLS12 (`isBn = 0`, $\lambda = q - x$)**:
   - if `isNegSeed = 1` ($x < 0$, e.g. BLS12-381): checks `conj(f) == f * c^q * c^{|x|}`,
   - if `isNegSeed = 0` ($x > 0$, e.g. small BLS12): checks `conj(f) * c^{|x|} == f * c^q`. -/
@[circuit_noinline]
def verifyFinalExpWitness (p : PairingParams) (f c : Fp12) : Nat :=
  let q := p.curve.fqMod
  let xi0 := p.xi0
  if fp12IsZero f then 0
  else if fp12Canonical q c then
    if fp12IsZero c then 0
    else
      let fConj := fp12Conj q f
      let cLoop := fp12Pow q xi0 p.loopBits c p.loopExp
      let cFrob1 := fp12Frob1 p c
      if p.isBn == 1 then
        let cFrob2 := fp12Frob2 p c
        let cFrob3 := fp12Frob3 p c
        let lhs := fp12Mul q xi0 fConj cFrob2
        let rhs := fp12Mul q xi0 f (fp12Mul q xi0 cLoop (fp12Mul q xi0 cFrob1 cFrob3))
        if fp12Eq lhs rhs then 1 else 0
      else if p.isNegSeed == 1 then
        let rhs := fp12Mul q xi0 f (fp12Mul q xi0 cFrob1 cLoop)
        if fp12Eq fConj rhs then 1 else 0
      else
        let lhs := fp12Mul q xi0 fConj cLoop
        let rhs := fp12Mul q xi0 f cFrob1
        if fp12Eq lhs rhs then 1 else 0
  else 0

/-- **Novakovic-Eagen / Onuki-Aoki $\mathbb{F}_{q^6}^*$-Scaled Final Exponentiation Check**:
Proves $f^{(q^{12}-1)/r} = 1$ using `(c : Fp12, s : Fp6)` with $c \neq 0$, $s \in \mathbb{F}_{q^6}^*$,
checking $f \cdot s = c^\lambda$. -/
@[circuit_noinline]
def verifyFinalExpWitnessFp6 (p : PairingParams) (f c : Fp12) (s : Fp6) : Nat :=
  let q := p.curve.fqMod
  let xi0 := p.xi0
  if fp12IsZero f then 0
  else if fp12Canonical q c then
    if fp12IsZero c then 0
    else if fp6Canonical q s then
      if fp6IsZero s then 0
      else
        let fs := fp12Mul q xi0 f (fp12OfFp6 s)
        let cLoop := fp12Pow q xi0 p.loopBits c p.loopExp
        let cFrob1 := fp12Frob1 p c
        if p.isBn == 1 then
          let cFrob2 := fp12Frob2 p c
          let cFrob3 := fp12Frob3 p c
          let lhs := fp12Mul q xi0 fs cFrob2
          let rhs := fp12Mul q xi0 cLoop (fp12Mul q xi0 cFrob1 cFrob3)
          if fp12Eq lhs rhs then 1 else 0
        else if p.isNegSeed == 1 then
          let rhs := fp12Mul q xi0 cFrob1 cLoop
          if fp12Eq fs rhs then 1 else 0
        else
          let lhs := fp12Mul q xi0 fs cLoop
          if fp12Eq lhs cFrob1 then 1 else 0
    else 0
  else 0

/-- Core checked 2-pairing verifier over signed/binary `digits`. Returns `1` iff valid. -/
@[circuit_noinline]
def verifyPairingCheck (p : PairingParams) (digits : BitList) (P0 : G1Point) (Q0 : G2Point)
    (P1 : G1Point) (Q1 : G2Point) (c : Fp12) : Nat :=
  if g1Validate p P0 then
    if g1Validate p P1 then
      let f := millerLoop2 p digits P0 Q0 P1 Q1
      verifyFinalExpWitness p f c
    else 0
  else 0

/-! ## Section 9: Single-Source Curve Parameters (Real BN254, Real BLS12-381 & Circuit Curves) -/

/-- Exact BN254 optimal Ate loop NAF digits (MSB-to-LSB after leading `1`, matching
`ark-bn254` `ATE_LOOP_COUNT.iter().rev().skip(1)`, encoding `1 → 1`, `-1 → 2`, `0 → 0`). -/
def bn254AteLoopDigits : BitList :=
  .cons 1 (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0
  (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 1 (.cons 0
  (.cons 2 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 1 (.cons 0
  (.cons 0 (.cons 2 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0
  (.cons 1 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 2 (.cons 0
  (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 0 (.cons 2 (.cons 0 (.cons 0
  (.cons 2 (.cons 0 (.cons 1 (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 0 .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Exact BLS12-381 optimal Ate loop binary digits of `|x| = 0xd201000000010000`
(63 bits MSB-to-LSB after leading `1`, matching `ark-bls12-381` `BitIteratorBE::new(X).skip(1)`). -/
def bls12381AteLoopDigits : BitList :=
  .cons 1 (.cons 0 (.cons 1 (.cons 0 (.cons 0 (.cons 1 (.cons 0
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 1
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 1
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0
  (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 (.cons 0 .nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- **Production 254-bit BN254 `PairingParams`** (`ark-bn254 0.5.0` exact tower & twist):
* `q = bn254Fp`, `r = bn254Fr`, `x = 4965661367192848881`, `6x + 2 = 29793968203157093288`,
* D-type sextic twist $\xi = 9 + u$, $E': y^2 = x^3 + 3/(9+u)$,
* `4×80b` affine-u80 limbs (`80, 80, 80, 14` bits, `topLimbBound = 16384`), 18 words per pair. -/
def bn254PairingParams : PairingParams :=
  { curve := bn254CurveParams
    isBn := 1
    isNegSeed := 0
    xi0 := 9
    twoInv := 10944121435919637611123202872628637544348155578648911831344518947322613104292
    bTwist :=
      { c0 := 19485874751759354771024239261021720505790618469301721065564631296452457478373
        c1 := 266929791119991161246907387137283842545076965332900288569378510910307636690 }
    g2Gen :=
      { x :=
          { c0 := 10857046999023057135944570762232829481370756359578518086990519993285655852781
            c1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634 }
        y :=
          { c0 := 8495653923123431417604973247489272438418190587263600148770280649306958101930
            c1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531 }
        isInf := 0 }
    twistMulByQX :=
      { c0 := 21575463638280843010398324269430826099269044274347216827212613867836435027261
        c1 := 10307601595873709700152284273816112264069230130616436755625194854815875713954 }
    twistMulByQY :=
      { c0 := 2821565182194536844548159561693502659359617185244120367078079554186484126554
        c1 := 3505843767911556378687030309984248845540243509899259641013678093033130930403 }
    g1EndoBeta := 0
    loopExp := 29793968203157093288
    loopBits := 65
    loopTopPow2 := 18446744073709551616 -- 2^64
    frob6C1_1 :=
      { c0 := 21575463638280843010398324269430826099269044274347216827212613867836435027261
        c1 := 10307601595873709700152284273816112264069230130616436755625194854815875713954 }
    frob6C2_1 :=
      { c0 := 2581911344467009335267311115468803099551665605076196740867805258568234346338
        c1 := 19937756971775647987995932169929341994314640652964949448313374472400716661030 }
    frob6C1_2 :=
      { c0 := 21888242871839275220042445260109153167277707414472061641714758635765020556616
        c1 := 0 }
    frob6C2_2 :=
      { c0 := 2203960485148121921418603742825762020974279258880205651966
        c1 := 0 }
    frob6C1_3 :=
      { c0 := 3772000881919853776433695186713858239009073593817195771773381919316419345261
        c1 := 2236595495967245188281701248203181795121068902605861227855261137820944008926 }
    frob6C2_3 :=
      { c0 := 5324479202449903542726783395506214481928257762400643279780343368557297135718
        c1 := 16208900380737693084919495127334387981393726419856888799917914180988844123039 }
    frob12C1_1 :=
      { c0 := 8376118865763821496583973867626364092589906065868298776909617916018768340080
        c1 := 16469823323077808223889137241176536799009286646108169935659301613961712198316 }
    frob12C1_2 :=
      { c0 := 21888242871839275220042445260109153167277707414472061641714758635765020556617
        c1 := 0 }
    frob12C1_3 :=
      { c0 := 11697423496358154304825782922584725312912383441159505038794027105778954184319
        c1 := 303847389135065887422783454877609941456349188919719272345083954437860409601 }
    topLimbBound := 16384 }

/-- Compile-time fixed `d = 3` BN254 residue table `w_k = ζ₂₇^k ∈ Fp6*` (`k ∈ {0, 1, 2}`):
since `gcd(λ_BN / r, (q^12 - 1)/r) = 3` and every `w_k` has order dividing `27 | (q^12 - 1)/r`
and lies in `Fp6*`, every `w_k` strictly satisfies `w_k^((q^12 - 1)/r) = 1`. -/
def bn254ResidueW0 : Fp6 := fp6One

def bn254ResidueW1 : Fp6 :=
  { c0 := fp2Zero
    c1 :=
      { c0 := 9483667112135124394372960210728142145589475128897916459350428495526310884707
        c1 := 4534159768373982659291990808346042891252278737770656686799127720849666919525 }
    c2 := fp2Zero }

def bn254ResidueW2 : Fp6 :=
  { c0 := fp2Zero
    c1 := fp2Zero
    c2 :=
      { c0 := 19980927575007324824158303482676250543132869272873419411837481938595769097674
        c1 := 1296461116503196556365099397830741391777269588311624000352671663269058798238 } }

/-- Fixed-table (`d = 3`) BN254 final exponentiation witness verifier:
checks `wIdx < 3`, `f ≠ 0`, `c ≠ 0`, and `f * w[wIdx] * c^{q^2} == c^{6x+2} * c^q * c^{q^3}`. -/
@[circuit_noinline]
def verifyFinalExpTableBN254 (f c : Fp12) (wIdx : Nat) : Nat :=
  if wIdx == 0 then verifyFinalExpWitnessFp6 bn254PairingParams f c bn254ResidueW0
  else if wIdx == 1 then verifyFinalExpWitnessFp6 bn254PairingParams f c bn254ResidueW1
  else if wIdx == 2 then verifyFinalExpWitnessFp6 bn254PairingParams f c bn254ResidueW2
  else 0

/-- **Production 381-bit BLS12-381 `PairingParams`** (`ark-bls12-381 0.5.0` exact tower & twist):
* `q = bls12381Fp`, `r = bls12381Fr`, `x = -0xd201000000010000` (`isNegSeed = 1`),
* M-type sextic twist $\xi = 1 + u$, $E': y^2 = x^3 + 4(1+u)$,
* GLV endomorphism $\beta$ for prime-order `G1` subgroup check $[x^2]P = -\psi(P)$,
* `5×80b` affine-u80 limbs (`80, 80, 80, 80, 61` bits, `topLimbBound = 2^61`), 22 words per pair. -/
def bls12381PairingParams : PairingParams :=
  { curve := bls12381CurveParams
    isBn := 0
    isNegSeed := 1
    xi0 := 1
    twoInv := 2001204777610833696708894912867952078278441409969503942666029068062015825245418932221343814564507832018947136279894
    bTwist := { c0 := 4, c1 := 4 }
    g2Gen :=
      { x :=
          { c0 := 352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160
            c1 := 3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758 }
        y :=
          { c0 := 1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905
            c1 := 927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582 }
        isInf := 0 }
    twistMulByQX :=
      { c0 := 0
        c1 := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 }
    twistMulByQY :=
      { c0 := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257
        c1 := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 }
    g1EndoBeta := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350
    loopExp := 15132376222941642752
    loopBits := 64
    loopTopPow2 := 9223372036854775808 -- 2^63
    frob6C1_1 :=
      { c0 := 0
        c1 := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436 }
    frob6C2_1 :=
      { c0 := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437
        c1 := 0 }
    frob6C1_2 :=
      { c0 := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350
        c1 := 0 }
    frob6C2_2 :=
      { c0 := 4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436
        c1 := 0 }
    frob6C1_3 := { c0 := 0, c1 := 1 }
    frob6C2_3 :=
      { c0 := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786
        c1 := 0 }
    frob12C1_1 :=
      { c0 := 3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760
        c1 := 151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027 }
    frob12C1_2 :=
      { c0 := 793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351
        c1 := 0 }
    frob12C1_3 :=
      { c0 := 2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530
        c1 := 1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257 }
    topLimbBound := 2305843009213693952 } -- 2^61

/-- **Genuine `< 2^56` BN Circuit Pairing Curve (`x = 1, q = 103, r = 97`)**:
* Exact BN family curve $E(\mathbb{F}_{103}): y^2 = x^3 + 5$, prime order $r = 97$ ($h_1 = 1$),
* Exact D-type sextic twist $\xi = 2 + u$, $E': y^2 = x^3 + 5/(2+u) = x^3 + (2 + 102u)$,
* `6x + 2 = 8 = 0b1000` (3 loop iterations + 2 Frobenius adjustment lines), `q² = 10609 ≪ 2^56`,
* Preserves the exact 4-limb (18-word) BN254 terminal affine ABI layout for live `ixcc-aiur --field bn254` + `plonk_export`! -/
@[circuit_inline]
def bn254CircuitPairingParams : PairingParams :=
  { curve :=
      { frMod := 97
        fqMod := 103
        maxLog := 5
        twoAdicGenMax := 5
        curveB := 5
        gx := 2
        gy := 61
        fqLimbCount := 4
        limbRadix := 16
        g1ByteLen := 2
        affineWords := 18 }
    isBn := 1
    isNegSeed := 0
    xi0 := 2
    twoInv := 52
    bTwist := { c0 := 2, c1 := 102 }
    g2Gen := { x := { c0 := 85, c1 := 44 }, y := { c0 := 15, c1 := 59 }, isInf := 0 }
    twistMulByQX := { c0 := 63, c1 := 1 }
    twistMulByQY := { c0 := 12, c1 := 24 }
    g1EndoBeta := 0
    loopExp := 8
    loopBits := 4
    loopTopPow2 := 8
    frob6C1_1 := { c0 := 63, c1 := 1 }
    frob6C2_1 := { c0 := 54, c1 := 23 }
    frob6C1_2 := { c0 := 56, c1 := 0 }
    frob6C2_2 := { c0 := 46, c1 := 0 }
    frob6C1_3 := { c0 := 26, c1 := 56 }
    frob6C2_3 := { c0 := 12, c1 := 28 }
    frob12C1_1 := { c0 := 36, c1 := 93 }
    frob12C1_2 := { c0 := 57, c1 := 0 }
    frob12C1_3 := { c0 := 95, c1 := 48 }
    topLimbBound := 16 }

/-- **Genuine `< 2^56` BLS12 Circuit Pairing Curve (`x = 4, q = 727, r = 241, h₁ = 3`)**:
* Exact BLS12 family curve $E(\mathbb{F}_{727}): y^2 = x^3 + 7$, order $723 = 3 \cdot 241$
  (real non-trivial cofactor $h_1 = 3$ exercising the exact $[x^2]P = -\psi(P)$ subgroup check!),
* Exact M-type sextic twist $\xi = 13 + u$, $E': y^2 = x^3 + 7(13+u) = x^3 + (91 + 7u)$,
* `|x| = 4 = 0b100`, `q² = 528529 ≪ 2^56`,
* Preserves the exact 5-limb (22-word) BLS12-381 terminal affine ABI layout for live `ixcc-aiur --field bls12-381` + `plonk_export --bls12-381`! -/
@[circuit_inline]
def bls12381CircuitPairingParams : PairingParams :=
  { curve :=
      { frMod := 241
        fqMod := 727
        maxLog := 4
        twoAdicGenMax := 7
        curveB := 7
        gx := 45
        gy := 316
        fqLimbCount := 5
        limbRadix := 16
        g1ByteLen := 2
        affineWords := 22 }
    isBn := 0
    isNegSeed := 0
    xi0 := 13
    twoInv := 364
    bTwist := { c0 := 91, c1 := 7 }
    g2Gen := { x := { c0 := 704, c1 := 284 }, y := { c0 := 653, c1 := 5 }, isInf := 0 }
    twistMulByQX := { c0 := 287, c1 := 434 }
    twistMulByQY := { c0 := 580, c1 := 270 }
    g1EndoBeta := 281
    loopExp := 4
    loopBits := 3
    loopTopPow2 := 4
    frob6C1_1 := { c0 := 287, c1 := 434 }
    frob6C2_1 := { c0 := 155, c1 := 482 }
    frob6C1_2 := { c0 := 281, c1 := 0 }
    frob6C2_2 := { c0 := 445, c1 := 0 }
    frob6C1_3 := { c0 := 677, c1 := 545 }
    frob6C2_3 := { c0 := 637, c1 := 25 }
    frob12C1_1 := { c0 := 241, c1 := 19 }
    frob12C1_2 := { c0 := 282, c1 := 0 }
    frob12C1_3 := { c0 := 351, c1 := 269 }
    topLimbBound := 16 }

/-! ## Section 10: Production 18-Word BN254 & 22-Word BLS12-381 `PairingCheck` APIs -/

/-- **Production BN254 18-Word Affine `PairingCheck`** accepting `AffinePairBN254`
(two 9-word `4×80b` affine `G1` points), two fixed `G2` anchors `(Q0, Q1)`, and
residue witness `c ∈ Fp12*`. -/
@[circuit_noinline]
def pairingCheckAffineBN254 (p : PairingParams) (digits : BitList) (pair : AffinePairBN254)
    (Q0 Q1 : G2Point) (c : Fp12) : Nat :=
  let d0 := decodeAffineG1BN254 p pair.a
  if d0.ok == 1 then
    let d1 := decodeAffineG1BN254 p pair.b
    if d1.ok == 1 then
      let f := millerLoop2 p digits d0.point Q0 d1.point Q1
      verifyFinalExpWitness p f c
    else 0
  else 0

/-- **Zero-ROM BN254 18-Word Affine `PairingCheck`** using `millerLoop2Binary` (0 heap allocs). -/
@[circuit_noinline]
def pairingCheckAffineBinaryBN254 (p : PairingParams) (pair : AffinePairBN254)
    (Q0 Q1 : G2Point) (c : Fp12) : Nat :=
  let d0 := decodeAffineG1BN254 p pair.a
  if d0.ok == 1 then
    let d1 := decodeAffineG1BN254 p pair.b
    if d1.ok == 1 then
      let f := millerLoop2Binary p d0.point Q0 d1.point Q1
      verifyFinalExpWitness p f c
    else 0
  else 0

/-- **Production BN254 18-Word Affine `PairingCheck` (Fixed `d = 3` Residue Table)**:
verifies $f \cdot w_{\text{wIdx}} \cdot c^{q^2} = c^{6x+2} \cdot c^q \cdot c^{q^3}$
against the compile-time 3-entry table `w[0..2] ⊂ Fp6*`. -/
@[circuit_noinline]
def pairingCheckAffineTableBN254 (pair : AffinePairBN254)
    (Q0 Q1 : G2Point) (c : Fp12) (wIdx : Nat) : Nat :=
  let p := bn254PairingParams
  let d0 := decodeAffineG1BN254 p pair.a
  if d0.ok == 1 then
    let d1 := decodeAffineG1BN254 p pair.b
    if d1.ok == 1 then
      let f := millerLoop2 p bn254AteLoopDigits d0.point Q0 d1.point Q1
      verifyFinalExpTableBN254 f c wIdx
    else 0
  else 0

/-- **Production BLS12-381 22-Word Affine `PairingCheck`** accepting `AffinePairBLS12381`
(two 11-word `5×80b` affine `G1` points), two fixed `G2` anchors `(Q0, Q1)`, and
residue witness `c ∈ Fp12*`. Enforces canonical `5×80b` limb bounds, strict infinity
encoding, curve equation, prime-order `G1` subgroup membership $[x^2]P = -\psi(P)$,
optimal Ate Miller loop, and residue-witnessed final exponentiation. -/
@[circuit_noinline]
def pairingCheckAffineBLS12381 (p : PairingParams) (pair : AffinePairBLS12381)
    (Q0 Q1 : G2Point) (c : Fp12) : Nat :=
  let d0 := decodeAffineG1BLS12381 p pair.a
  if d0.ok == 1 then
    let d1 := decodeAffineG1BLS12381 p pair.b
    if d1.ok == 1 then
      let f := millerLoop2Binary p d0.point Q0 d1.point Q1
      verifyFinalExpWitness p f c
    else 0
  else 0

/-! ## Section 11: Live-Exportable Self-Contained Benchmark Entrypoints (`plonk_export`, `outputs = 0`) -/

/-- Construct an `Fp12` element from 12 flat `Nat` coordinates. -/
@[circuit_inline]
def mkFp12 (c000 c001 c010 c011 c020 c021 c100 c101 c110 c111 c120 c121 : Nat) : Fp12 :=
  { c0 := { c0 := { c0 := c000, c1 := c001 }, c1 := { c0 := c010, c1 := c011 }, c2 := { c0 := c020, c1 := c021 } }
    c1 := { c0 := { c0 := c100, c1 := c101 }, c1 := { c0 := c110, c1 := c111 }, c2 := { c0 := c120, c1 := c121 } } }

/-- Shared zero-ROM $\mathbb{F}_{q^{12}}$ arithmetic smoke kernel exercising `Fp2`, `Fp6`,
`Fp12` multiplication, general inversion (triggering `KzgWire.fqMulMod` & `fqInvMod`
guesses), and Frobenius endomorphism consistency $\pi_{q^3} = \pi_q \circ \pi_{q^2}$. -/
@[circuit_noinline]
def runFp12MulSmoke (p : PairingParams) (a0 a1 b0 b1 : Nat) : Nat :=
  let q := p.curve.fqMod
  let xi0 := p.xi0
  let argsErr := natLtErr a0 q + natLtErr a1 q + natLtErr b0 q + natLtErr b1 q
  if argsErr == 0 then
    let elA := mkFp12 a0 a1 1 2 3 4 5 6 7 8 9 10
    let elB := mkFp12 b0 b1 2 1 4 3 6 5 8 7 10 9
    if fp12Sum elB == 0 then 0
    else
      let prod := fp12Mul q xi0 elA elB
      let invB := fp12Inv q xi0 elB
      let back := fp12Mul q xi0 prod invB
      let frobA := fp12Frob3 p elA
      let frobB := fp12Frob1 p (fp12Frob2 p elA)
      if fp12Diff back elA + fp12Diff frobA frobB == 0 then 1 else 0
  else 0

/-- **Entrypoint 1 (`entryFp12MulBN254`)**: fast-compile zero-ROM BN254-field $\mathbb{F}_{q^{12}}$
mul + inv + Frobenius smoke entrypoint for live `ixcc-aiur --field bn254 --assert-ok` →
`plonk_export` (`private_outputs: 0`). Valid witness: `(2, 3, 5, 7) → 1`. -/
def entryFp12MulBN254 (a0 a1 b0 b1 : Nat) : Nat :=
  runFp12MulSmoke bn254CircuitPairingParams a0 a1 b0 b1

/-- **Entrypoint 2 (`entryFp12MulBLS12381`)**: fast-compile zero-ROM BLS12-381-field $\mathbb{F}_{q^{12}}$
mul + inv + Frobenius smoke entrypoint for live `ixcc-aiur --field bls12-381 --assert-ok` →
`plonk_export --bls12-381` (`private_outputs: 0`). Valid witness: `(2, 3, 5, 7) → 1`. -/
def entryFp12MulBLS12381 (a0 a1 b0 b1 : Nat) : Nat :=
  runFp12MulSmoke bls12381CircuitPairingParams a0 a1 b0 b1

/-- Static fixed `G2` anchor `Q0 = [51]G2` for `entryPairingCheckBN254` (non-trivial anchor). -/
@[circuit_inline]
def staticBnAnchorQ0 : G2Point :=
  { x := { c0 := 81, c1 := 25 }, y := { c0 := 85, c1 := 38 }, isInf := 0 }

/-- Static fixed `G2` anchor `Q1 = G2` for `entryPairingCheckBN254`. -/
@[circuit_inline]
def staticBnAnchorQ1 : G2Point :=
  bn254CircuitPairingParams.g2Gen

/-- Static fixed `G2` anchor `Q0 = [161]G2` for `entryPairingCheckBLS12381` (non-trivial anchor). -/
@[circuit_inline]
def staticBlsAnchorQ0 : G2Point :=
  { x := { c0 := 536, c1 := 586 }, y := { c0 := 674, c1 := 599 }, isInf := 0 }

/-- Static fixed `G2` anchor `Q1 = G2` for `entryPairingCheckBLS12381`. -/
@[circuit_inline]
def staticBlsAnchorQ1 : G2Point :=
  bls12381CircuitPairingParams.g2Gen

/-- **Entrypoint 3 (`entryPairingCheckBN254`)**: full self-contained zero-ROM BN 2-pairing
optimal Ate + residue-witnessed final exponentiation verifier taking **18 affine-limb words**
`(aX0..aX3, aY0..aY3, aInf, bX0..bX3, bY0..bY3, bInf)` + 12 `Fp12` witness coordinates
against static `G2` anchors `(staticBnAnchorQ0, staticBnAnchorQ1)`.
Compiles live through `ixcc-aiur --typed --inline-fuse --field-lower --enable-guesses
--field bn254 --entry-name PairingCheck::verify_bn254 --assert-ok` → `plonk_export` (`outputs = 0`)! -/
def entryPairingCheckBN254
    (aX0 aX1 aX2 aX3 aY0 aY1 aY2 aY3 aInf : Nat)
    (bX0 bX1 bX2 bX3 bY0 bY1 bY2 bY3 bInf : Nat)
    (c000 c001 c010 c011 c020 c021 c100 c101 c110 c111 c120 c121 : Nat) : Nat :=
  let pair : AffinePairBN254 :=
    { a := { x := { l0 := aX0, l1 := aX1, l2 := aX2, l3 := aX3 }
             y := { l0 := aY0, l1 := aY1, l2 := aY2, l3 := aY3 }
             isInf := aInf }
      b := { x := { l0 := bX0, l1 := bX1, l2 := bX2, l3 := bX3 }
             y := { l0 := bY0, l1 := bY1, l2 := bY2, l3 := bY3 }
             isInf := bInf } }
  let c := mkFp12 c000 c001 c010 c011 c020 c021 c100 c101 c110 c111 c120 c121
  pairingCheckAffineBinaryBN254 bn254CircuitPairingParams pair staticBnAnchorQ0 staticBnAnchorQ1 c

/-- **Entrypoint 4 (`entryPairingCheckBLS12381`)**: full self-contained zero-ROM BLS12 2-pairing
optimal Ate + prime-order `G1` subgroup check + residue-witnessed final exponentiation
verifier taking **22 affine-limb words** `(aX0..aX4, aY0..aY4, aInf, bX0..bX4, bY0..bY4, bInf)`
+ 12 `Fp12` witness coordinates against static `G2` anchors `(staticBlsAnchorQ0, staticBlsAnchorQ1)`.
Compiles live through `ixcc-aiur --typed --inline-fuse --field-lower --enable-guesses
--field bls12-381 --entry-name PairingCheck::verify_bls12381 --assert-ok` → `plonk_export --bls12-381` (`outputs = 0`)! -/
def entryPairingCheckBLS12381
    (aX0 aX1 aX2 aX3 aX4 aY0 aY1 aY2 aY3 aY4 aInf : Nat)
    (bX0 bX1 bX2 bX3 bX4 bY0 bY1 bY2 bY3 bY4 bInf : Nat)
    (c000 c001 c010 c011 c020 c021 c100 c101 c110 c111 c120 c121 : Nat) : Nat :=
  let pair : AffinePairBLS12381 :=
    { a := { x := { l0 := aX0, l1 := aX1, l2 := aX2, l3 := aX3, l4 := aX4 }
             y := { l0 := aY0, l1 := aY1, l2 := aY2, l3 := aY3, l4 := aY4 }
             isInf := aInf }
      b := { x := { l0 := bX0, l1 := bX1, l2 := bX2, l3 := bX3, l4 := bX4 }
             y := { l0 := bY0, l1 := bY1, l2 := bY2, l3 := bY3, l4 := bY4 }
             isInf := bInf } }
  let c := mkFp12 c000 c001 c010 c011 c020 c021 c100 c101 c110 c111 c120 c121
  let p := { bls12381CircuitPairingParams with isBn := 0 }
  pairingCheckAffineBLS12381 p pair staticBlsAnchorQ0 staticBlsAnchorQ1 c

/-! ## Section 12: Cryptographic Ground-Truth `#guard` Suite (`ark-bn254` & `ark-bls12-381`) -/

section PairingTests

/-! ### 1. Tower Field Algebraic & Frobenius Identities on Real BN254 & Real BLS12-381 -/

private def sampleA : Fp12 := mkFp12 2 3 5 7 11 13 17 19 23 29 31 37
private def sampleB : Fp12 := mkFp12 41 43 47 53 59 61 67 71 73 79 83 89
private def sampleC : Fp12 := mkFp12 97 101 103 107 109 113 127 131 137 139 149 151

private def checkTowerLaws (p : PairingParams) : Bool :=
  let q := p.curve.fqMod
  let xi0 := p.xi0
  let u : Fp2 := { c0 := 11 % q, c1 := 17 % q }
  let v : Fp2 := { c0 := 23 % q, c1 := 29 % q }
  let w : Fp2 := { c0 := 31 % q, c1 := 37 % q }
  let ok2 :=
    (fqNeg q 0 == 0) &&
    (fqNeg q (11 % q) == fqNegMod q (11 % q)) &&
    (fp2Mul q u (fp2Inv q u) == fp2One) &&
    (fp2Sqr q u == fp2Mul q u u) &&
    (fp2Mul q (fp2Mul q u v) w == fp2Mul q u (fp2Mul q v w)) &&
    (fp2Mul q u (fp2Add q v w) == fp2Add q (fp2Mul q u v) (fp2Mul q u w)) &&
    (fp2Conj q (fp2Mul q u v) == fp2Mul q (fp2Conj q u) (fp2Conj q v)) &&
    (fp2MulByNonResidue q xi0 u == fp2Mul q u { c0 := xi0, c1 := 1 }) &&
    (fp2Add q u (fp2Neg q u) == fp2Zero) &&
    (fp2Sub q (fp2Add q u v) v == u)
  let f6a : Fp6 := { c0 := u, c1 := v, c2 := w }
  let f6b : Fp6 := { c0 := v, c1 := w, c2 := u }
  let ok6 :=
    (fp6Mul q xi0 f6a (fp6Inv q xi0 f6a) == fp6One) &&
    (fp6Sqr q xi0 f6a == fp6Mul q xi0 f6a f6a) &&
    (fp6MulBy01 q xi0 f6a u v == fp6Mul q xi0 f6a { c0 := u, c1 := v, c2 := fp2Zero }) &&
    (fp6MulBy1 q xi0 f6a v == fp6Mul q xi0 f6a { c0 := fp2Zero, c1 := v, c2 := fp2Zero }) &&
    (fp6Frob3 p f6a == fp6Frob1 p (fp6Frob2 p f6a)) &&
    (fp6Frob2 p (fp6Frob2 p (fp6Frob2 p f6a)) == f6a) &&
    (fp6Frob1 p (fp6Mul q xi0 f6a f6b) == fp6Mul q xi0 (fp6Frob1 p f6a) (fp6Frob1 p f6b))
  let a : Fp12 := { c0 := f6a, c1 := f6b }
  let b : Fp12 := { c0 := f6b, c1 := { c0 := w, c1 := u, c2 := v } }
  let c : Fp12 := { c0 := { c0 := v, c1 := u, c2 := w }, c1 := f6a }
  let ok12 :=
    (fp12Mul q xi0 a (fp12Inv q xi0 a) == fp12One) &&
    (fp12Sqr q xi0 a == fp12Mul q xi0 a a) &&
    (fp12Mul q xi0 (fp12Mul q xi0 a b) c == fp12Mul q xi0 a (fp12Mul q xi0 b c)) &&
    (fp12MulBy034 q xi0 a u v w ==
      fp12Mul q xi0 a { c0 := { c0 := u, c1 := fp2Zero, c2 := fp2Zero }
                        c1 := { c0 := v, c1 := w, c2 := fp2Zero } }) &&
    (fp12MulBy014 q xi0 a u v w ==
      fp12Mul q xi0 a { c0 := { c0 := u, c1 := v, c2 := fp2Zero }
                        c1 := { c0 := fp2Zero, c1 := w, c2 := fp2Zero } }) &&
    (fp12Frob3 p a == fp12Frob1 p (fp12Frob2 p a)) &&
    (fp12Frob3 p (fp12Frob3 p a) == fp12Conj q a) &&
    (fp12Frob1 p (fp12Mul q xi0 a b) == fp12Mul q xi0 (fp12Frob1 p a) (fp12Frob1 p b)) &&
    (fp12Frob2 p (fp12Mul q xi0 a b) == fp12Mul q xi0 (fp12Frob2 p a) (fp12Frob2 p b)) &&
    (fp12Frob3 p (fp12Mul q xi0 a b) == fp12Mul q xi0 (fp12Frob3 p a) (fp12Frob3 p b))
  ok2 && ok6 && ok12

#guard checkTowerLaws bn254PairingParams == true
#guard checkTowerLaws bls12381PairingParams == true
#guard checkTowerLaws bn254CircuitPairingParams == true
#guard checkTowerLaws bls12381CircuitPairingParams == true
#guard fp12Mul bn254Fp 9 sampleA (fp12Inv bn254Fp 9 sampleA) == fp12One
#guard fp12Mul bls12381Fp 1 sampleA (fp12Inv bls12381Fp 1 sampleA) == fp12One
#guard fp12Mul bn254Fp 9 (fp12Mul bn254Fp 9 sampleA sampleB) sampleC ==
  fp12Mul bn254Fp 9 sampleA (fp12Mul bn254Fp 9 sampleB sampleC)
#guard fp12Mul bls12381Fp 1 (fp12Mul bls12381Fp 1 sampleA sampleB) sampleC ==
  fp12Mul bls12381Fp 1 sampleA (fp12Mul bls12381Fp 1 sampleB sampleC)

/-! ### 2. `G2` Curve & Twist Generator Checks -/

#guard g2OnTwist bn254PairingParams bn254PairingParams.g2Gen == true
#guard g2OnTwist bls12381PairingParams bls12381PairingParams.g2Gen == true
#guard g2OnTwist bn254CircuitPairingParams bn254CircuitPairingParams.g2Gen == true
#guard g2OnTwist bls12381CircuitPairingParams bls12381CircuitPairingParams.g2Gen == true
#guard g2OnTwist bn254CircuitPairingParams staticBnAnchorQ0 == true
#guard g2OnTwist bls12381CircuitPairingParams staticBlsAnchorQ0 == true
#guard g2ScalarMul bn254CircuitPairingParams.curve.fqMod 51 bn254CircuitPairingParams.g2Gen == staticBnAnchorQ0
#guard g2ScalarMul bls12381CircuitPairingParams.curve.fqMod 161 bls12381CircuitPairingParams.g2Gen == staticBlsAnchorQ0

/-! ### 3. Bit-for-Bit Ground-Truth Match Against `ark-bn254 0.5.0` & `ark-bls12-381 0.5.0` -/

-- Exact `ark_bn254::Bn254::multi_miller_loop([G1], [G2])`
private def arkBn254MlGen : Fp12 :=
  mkFp12
    7839923261617885508987657002451344696432320114614434307852847339179413313131
    12717477091189878191750757105631642814394974815225599372235521871186456047185
    4495351289242968368489443409990120909266958997534941096233383580904652570968
    18260482371840806269258274155140294304605237478103224910052874688449597450291
    1279265302254125767302656014297491966433341127593655239766626748952970630698
    1388121835306334572356808027484473543889687237652069077660202994440235528548
    19852083908929483692825705709699891513888357475021762293723964644225448489959
    19585424606244653125874350451545466165975231973942042158315113677433890127948
    16200718250890395597511978989568765255542844217061356566590841434924851848883
    18471953788557918301135801699439586176981449163871144189161405096649508064561
    17475922307275585000629274569182183704942867998604624902575839562555121108505
    4598062826746979912844329033999650324061844598778337136104700815112494089718

-- Exact `ark_bn254::Bn254::multi_miller_loop([[a]G1, [-ab]G1], [[b]G2, G2])` for a=1234567, b=7654321
private def arkBn254Ml2AB : Fp12 :=
  mkFp12
    13011790729169000921356995020691422957809294107035965878354371218287864965588
    2464191529122886218022644276866030511819461270255594974477580909586629281592
    20766251611241228557909011221283276921083073294049008140211607075570497084117
    21622336817639062215021356864325938594151384656854759546913193861148945747977
    7639558478705952302848357076329159430614375807658231237569363280634781311455
    21511954418440141920859178870561024852961983059985252996879868508480825837891
    5397729440214513521354035985045714425483225714560008334044732576824945435987
    12100446126570364023741986818779259429636597008695738820848857048056431233399
    2011945281265293985832837235165589864263310705298971149013730652901768183206
    11938557297285554719318586762393329562014618930415337757428697081427217070104
    10470449120674282905483200525667426530779123541965902904716227275958988329508
    21487748889676100425302429786814939667591434404276969233251064620320991570657

-- Exact `ark_bls12_381::Bls12_381::multi_miller_loop([G1], [G2])`
private def arkBls12381MlGen : Fp12 :=
  mkFp12
    2082832974237641092700420664926212012601923689321750436277964672672466536406068201391665791157739850107688972746723
    2188998168044730298369128305152617103558675018239082824861291130746754380139617137865114204136019107138471213476851
    2392336401811501404745774377129891330347374745753842119062499171206650384830277273345589160779190732386820480773659
    2633045349740707708071811800161088362676323126630562725433977227413906176602622446132729452955879868723530145381966
    220748764745913447756616354453889028747773582571363238211358562489175229758597385143868154838763104895463695242885
    631781936522367680475545670092627650330243772619608713241745327312228585305293682680521772395066786082446537943839
    1331696699251905410180704770706671086342918940957143356409587882796411629070773603814760989432089851060345349778181
    2344596306628961987025484248373516032661659559588734882325833675660660388259339056457447637116879751070682700499607
    2546534044808734448228467327151204779936667041736650915457913919208182951668421256585932861753262399523238937574278
    3471751334380596922231014636298395844847003886219426491236805320479630385655533623159962318932856265232738790198772
    1685173958410217589186006011054297327645795762812958662649817251938118499431747451147745368068631578852635242391711
    3388308247563799343103555425754048897856489204905093664441072753245169907800054576324061510606358470377904354636815

-- Exact `ark_bls12_381::Bls12_381::multi_miller_loop([[a]G1, [-ab]G1], [[b]G2, G2])` for a=1234567, b=7654321
private def arkBls12381Ml2AB : Fp12 :=
  mkFp12
    3240874310197804661911881611856171828737523996001107340249008394403599079390624360024392942667914903813032583678680
    767719734504837337685143852793198846690800458782674640160031530312037404886223433818824873104481160994228073143306
    2306801583521121377353115672633618682792559459632228637895939710281803558975264906215477500222729139366417273635749
    3332789149802894814896205640760883791983551745837109789901967916604339038243721999045139208171608069826923424229282
    1706017205894272967369630961771660449087984762997653141371910062687326667612917511106334568937718646733070211457484
    1982173703992353757213746515588772851521843071686504922176285816554747983322124247563899653024509760546630189674076
    3229676240603466418074292950971145191821818040713760568166292860684346094129883148631810773506215650963100201429432
    2569764863540091907893020644989563315993844794738484579235339047411050205122506991694375453967457755115110629254323
    3735989603264660242346882341169617184918792761270899918217724640687413578127068235229031009273470748641289110842667
    1171948799101660371934563614067579173960554279021907115442480305792591432391512940472243642306106735647243032394850
    3883407939533057262996686181109535215543135849380059822412761025212508824638253277445311632262607212953900486341698
    288503280625559951875639127825804886045384735389802327636928763255458087668818852727991576490977107304639275419733

private def bnP0AB : G1Point :=
  { x := 5260701971153217998271766165282167317134796743668792602672522694732953126276
    y := 4825124334084439482326934656042154820606002828296494717134849704227696847413
    isInf := 0 }

private def bnQ0AB : G2Point :=
  { x :=
      { c0 := 5429662431327998444524588871484129577439597916341682256162312263537367199432
        c1 := 14034149922221847126241739062830657115173472053134873970260331559661301757434 }
    y :=
      { c0 := 11911708527650426885517571179201187924477332847263552419101105598668477148127
        c1 := 3985162613871310317199713205349226866242092849337398109472157537461646360812 }
    isInf := 0 }

private def bnP1AB : G1Point :=
  { x := 13674220374567792143136402119478748262690646710992366809721271156164470463267
    y := 20357313559113068286415407371972093874122923974059081924707495126153644403733
    isInf := 0 }

private def bnWitnessAB : Fp12 :=
  mkFp12
    7534611045590187447265218351901945461120367592195345704804327961142673434088
    7589055145679365930177747479740493796170100365322492171008990593176573198307
    15079757237246443898405663596661290970263925709198725336199248124275784986492
    18245842547683789768712170021077860143382974546371200708705302925721031289770
    10291614857819399494505401614238469463005062944134071862600728151207611537926
    21573807755089562509790919089494074035354711325140612772852069462536957367772
    854712967294453013731602126282833974428788737121784942745610669655863962445
    9894638458863197386370287393859758061735656448614358899554770050324946930809
    16885232252528456825695767921313218660428936683414102264811435056431917086019
    20360205924195180141740445726852348246270979786482466514394002411207497107448
    7005678217175330466246602651789304708042632397855511600263617117235088026939
    7206113703784450550951731739311410945747294947488764621002330967529172360157

private def bnWitnessTableAB : Fp12 :=
  mkFp12
    8927440168791993930361383509263706368870377684182110211004975909473321755039
    21297791915146303488393865693428065102380603783211904146756706887218431511355
    1790836443471683928375166478474245847534431133230603490815010055630430322595
    17139588382432213857522077743972380257359133883133603353284068903636988422620
    2916934058682611689669416965303785959030110053136662892697105357112205975958
    18269564769175984780234723115147510880656315348309690713728458682248333998749
    7182332527721818069848297932603412171736398527585599649883099649925611116095
    4808781746819489924395150270521122689834817127591608930782260856797221274131
    21711081020534888986770223442272037342090168105857681590258398821227257788118
    8777960327047371525230909632339052293018201009706991415641603571050241979611
    9382862105902724635256696659225261212930517542745323323948162554722558279996
    7293577595589497095411403128587724623952832047943322935889817677724190414216

private def blsP0AB : G1Point :=
  { x := 2692774828344496329302857221881558456687930215547239128764741076961478364983749016898548084741404528993590529237160
    y := 2854663322886649950013803173936538691128363050644696522278545158974587049233023478599735149127378986005097616945785
    isInf := 0 }

private def blsQ0AB : G2Point :=
  { x :=
      { c0 := 1588758840457702647441544296423502352517059201809668935726930959596905950184177688786328175660997440522432299509575
        c1 := 3626570105011496832388020516310481832319472981702556244580781261171801470593791037600355307349809757620153298776413 }
    y :=
      { c0 := 2294474814859042078686954785842783817132638451169326232465977890331827607786150957678454922054692092236713538320186
        c1 := 1528365689840967917276980822189838434517896578947369795205042368120826027515006566675140536824444769116400480884404 }
    isInf := 0 }

private def blsP1AB : G1Point :=
  { x := 2848498605988143773024694891718208784622800276456225343988983382642180643397710894359745881963663669498255765859380
    y := 85779643834639491078973317682294919305596982012268692605377528220784239722338445648458201196126334659634363154411
    isInf := 0 }

private def blsWitnessAB : Fp12 :=
  mkFp12
    3049559761788789418548182105209632547604157781987897996917127743891168182613329492953313660325892234348253490572562
    3420053536932637721195216898121079144349828989518170964181329483767335734855774954805315819543487674055473006131789
    1457509975769951769818105949583701270628665561891251656714059440394098403595477950184917595710908103903373081312213
    3095273247690663996461819008658766448051301024510443806555300660272059818962903038083050115496088222026577078822542
    2597844484521450539565810950066931919111057628523463955276314360134698266829710622787471651226213819815096498908141
    2365987699060640212217204558270412961828839807313915152093945563979043510974077663900302900796385336760570046516256
    3301352808411318628738138398942664023142434995662656300077782745043131854023293749916739767290175075567255744915416
    1763744445189527145540613789560888918622146516727711563133086297881407577230815112348268536055771500170391284818398
    516526377051990387810121652354453801246353420205922811361949944430996872667552109388930308757757554523054734470529
    1856631131630901777053212197470635229336372961663936537449262179324733061917219768256865832424766638733688113960389
    3712234709775805943396211087507280264457638837711330057393112028255160677950543129810900279552218374578777298354911
    3054157647056317057646674317235530894972045333335164354520846283484458953275111673859361700326105844832064956120524

-- Bit-for-bit match against `ark-bn254 0.5.0`
#guard millerLoop2 bn254PairingParams bn254AteLoopDigits
  (g1Gen bn254CurveParams) bn254PairingParams.g2Gen g1Inf bn254PairingParams.g2Gen == arkBn254MlGen
#guard millerLoop2 bn254PairingParams bn254AteLoopDigits
  bnP0AB bnQ0AB bnP1AB bn254PairingParams.g2Gen == arkBn254Ml2AB
#guard millerLoop2Prepared bn254PairingParams bn254AteLoopDigits
  bnP0AB (precomputeG2Lines bn254PairingParams bn254AteLoopDigits bnQ0AB)
  bnP1AB (precomputeG2Lines bn254PairingParams bn254AteLoopDigits bn254PairingParams.g2Gen) == arkBn254Ml2AB

-- Bit-for-bit match against `ark-bls12-381 0.5.0` (both `BitList`, zero-ROM binary, and prepared lines!)
#guard millerLoop2 bls12381PairingParams bls12381AteLoopDigits
  (g1Gen bls12381CurveParams) bls12381PairingParams.g2Gen g1Inf bls12381PairingParams.g2Gen == arkBls12381MlGen
#guard millerLoop2 bls12381PairingParams bls12381AteLoopDigits
  blsP0AB blsQ0AB blsP1AB bls12381PairingParams.g2Gen == arkBls12381Ml2AB
#guard millerLoop2Binary bls12381PairingParams
  blsP0AB blsQ0AB blsP1AB bls12381PairingParams.g2Gen == arkBls12381Ml2AB
#guard millerLoop2Prepared bls12381PairingParams bls12381AteLoopDigits
  blsP0AB (precomputeG2Lines bls12381PairingParams bls12381AteLoopDigits blsQ0AB)
  blsP1AB (precomputeG2Lines bls12381PairingParams bls12381AteLoopDigits bls12381PairingParams.g2Gen) == arkBls12381Ml2AB

-- Verify every entry in BN254 `w[0..2]` is a genuine `r`-th power (`w[k]^27 == 1`, `27 | (q^12-1)/r`)
#guard ((bn254Fp ^ 12 - 1) / bn254Fr) % 27 == 0
#guard fp12Pow bn254Fp 9 6 (fp12OfFp6 bn254ResidueW0) 27 == fp12One
#guard fp12Pow bn254Fp 9 6 (fp12OfFp6 bn254ResidueW1) 27 == fp12One
#guard fp12Pow bn254Fp 9 6 (fp12OfFp6 bn254ResidueW2) 27 == fp12One
#guard fp12Pow bn254Fp 9 6 (fp12OfFp6 bn254ResidueW1) 9 != fp12One
#guard fp12Mul bn254Fp 9 (fp12OfFp6 bn254ResidueW1) (fp12OfFp6 bn254ResidueW1) == fp12OfFp6 bn254ResidueW2

/-! ### 4. Real BN254 & Real BLS12-381 Full Pairing Checks (18 & 22 Affine-u80 Words) -/

private def bnPair11 : AffinePairBN254 :=
  encodeAffinePairBN254 radix80 (g1Gen bn254CurveParams) (g1Neg bn254CurveParams (g1Gen bn254CurveParams))
private def bnPairAB : AffinePairBN254 :=
  encodeAffinePairBN254 radix80 bnP0AB bnP1AB
private def bnPairOO : AffinePairBN254 :=
  encodeAffinePairBN254 radix80 g1Inf g1Inf

#guard pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPair11
  bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 1
#guard pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPairAB
  bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 1
#guard pairingCheckAffineTableBN254 bnPairAB
  bnQ0AB bn254PairingParams.g2Gen bnWitnessTableAB 1 == 1
#guard pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPairOO
  bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 1

private def blsPair11 : AffinePairBLS12381 :=
  encodeAffinePairBLS12381 radix80 (g1Gen bls12381CurveParams) (g1Neg bls12381CurveParams (g1Gen bls12381CurveParams))
private def blsPairAB : AffinePairBLS12381 :=
  encodeAffinePairBLS12381 radix80 blsP0AB blsP1AB
private def blsPairOO : AffinePairBLS12381 :=
  encodeAffinePairBLS12381 radix80 g1Inf g1Inf

#guard pairingCheckAffineBLS12381 bls12381PairingParams blsPair11
  bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 1
#guard pairingCheckAffineBLS12381 bls12381PairingParams blsPairAB
  blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 1
#guard pairingCheckAffineBLS12381 bls12381PairingParams blsPairOO
  bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 1

/-! ### 5. Comprehensive Negative Controls Rejected on BOTH Real BN254 & Real BLS12-381 -/

-- BN254 negative controls:
#guard
  let badPair := encodeAffinePairBN254 radix80 (g1Gen bn254CurveParams)
    (g1Neg bn254CurveParams (g1Double bn254CurveParams (g1Gen bn254CurveParams)))
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits badPair
    bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 0
#guard
  let singleInf := encodeAffinePairBN254 radix80 (g1Gen bn254CurveParams) g1Inf
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits singleInf
    bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 0
#guard
  let offCurve : AffinePairBN254 :=
    { bnPairAB with a := { bnPairAB.a with y := { bnPairAB.a.y with l0 := bnPairAB.a.y.l0 + 1 } } }
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits offCurve
    bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 0
#guard
  let badLimb0 : AffinePairBN254 :=
    { bnPairAB with a := { bnPairAB.a with x := { bnPairAB.a.x with l0 := radix80 } } }
  let badTop : AffinePairBN254 :=
    { bnPairAB with a := { bnPairAB.a with x := { bnPairAB.a.x with l3 := 16384 } } }
  let modX : AffinePairBN254 :=
    { bnPairAB with a := { bnPairAB.a with x := toLimb4 bn254Fp } }
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits badLimb0 bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits badTop bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits modX bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 0
#guard
  let badC : Fp12 :=
    { bnWitnessAB with c0 := { bnWitnessAB.c0 with c0 := { bnWitnessAB.c0.c0 with c0 := bnWitnessAB.c0.c0.c0 + 1 } } }
  let nonCanonC : Fp12 :=
    { bnWitnessAB with c0 := { bnWitnessAB.c0 with c0 := { bnWitnessAB.c0.c0 with c0 := bn254Fp } } }
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPairAB bnQ0AB bn254PairingParams.g2Gen badC == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPairAB bnQ0AB bn254PairingParams.g2Gen fp12Zero == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits bnPairAB bnQ0AB bn254PairingParams.g2Gen nonCanonC == 0
#guard
  pairingCheckAffineTableBN254 bnPairAB bnQ0AB bn254PairingParams.g2Gen bnWitnessTableAB 0 == 0 &&
  pairingCheckAffineTableBN254 bnPairAB bnQ0AB bn254PairingParams.g2Gen bnWitnessTableAB 2 == 0 &&
  pairingCheckAffineTableBN254 bnPairAB bnQ0AB bn254PairingParams.g2Gen bnWitnessTableAB 3 == 0
#guard
  let infFlag2 : AffinePairBN254 := { bnPairOO with a := { bnPairOO.a with isInf := 2 } }
  let infNonZero : AffinePairBN254 := { bnPairAB with a := { bnPairAB.a with isInf := 1 } }
  let finiteZero : AffinePairBN254 := { bnPairOO with a := { bnPairOO.a with isInf := 0 } }
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits infFlag2 bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits infNonZero bnQ0AB bn254PairingParams.g2Gen bnWitnessAB == 0 &&
  pairingCheckAffineBN254 bn254PairingParams bn254AteLoopDigits finiteZero bn254PairingParams.g2Gen bn254PairingParams.g2Gen fp12One == 0

-- BLS12-381 negative controls:
#guard
  let badPair := encodeAffinePairBLS12381 radix80 (g1Gen bls12381CurveParams)
    (g1Neg bls12381CurveParams (g1Double bls12381CurveParams (g1Gen bls12381CurveParams)))
  pairingCheckAffineBLS12381 bls12381PairingParams badPair
    bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 0
#guard
  let offCurve : AffinePairBLS12381 :=
    { blsPairAB with a := { blsPairAB.a with y := { blsPairAB.a.y with l0 := blsPairAB.a.y.l0 + 1 } } }
  pairingCheckAffineBLS12381 bls12381PairingParams offCurve
    blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 0
#guard
  let badLimb0 : AffinePairBLS12381 :=
    { blsPairAB with a := { blsPairAB.a with x := { blsPairAB.a.x with l0 := radix80 } } }
  let badTop : AffinePairBLS12381 :=
    { blsPairAB with a := { blsPairAB.a with x := { blsPairAB.a.x with l4 := 2305843009213693952 } } }
  let modX : AffinePairBLS12381 :=
    { blsPairAB with a := { blsPairAB.a with x := toLimb5 bls12381Fp } }
  pairingCheckAffineBLS12381 bls12381PairingParams badLimb0 blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams badTop blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams modX blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 0
#guard
  let badC : Fp12 :=
    { blsWitnessAB with c1 := { blsWitnessAB.c1 with c2 := { blsWitnessAB.c1.c2 with c1 := blsWitnessAB.c1.c2.c1 + 1 } } }
  let nonCanonC : Fp12 :=
    { blsWitnessAB with c0 := { blsWitnessAB.c0 with c0 := { blsWitnessAB.c0.c0 with c0 := bls12381Fp } } }
  pairingCheckAffineBLS12381 bls12381PairingParams blsPairAB blsQ0AB bls12381PairingParams.g2Gen badC == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams blsPairAB blsQ0AB bls12381PairingParams.g2Gen fp12Zero == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams blsPairAB blsQ0AB bls12381PairingParams.g2Gen nonCanonC == 0
#guard
  let infFlag2 : AffinePairBLS12381 := { blsPairOO with a := { blsPairOO.a with isInf := 2 } }
  let infNonZero : AffinePairBLS12381 := { blsPairAB with a := { blsPairAB.a with isInf := 1 } }
  let finiteZero : AffinePairBLS12381 := { blsPairOO with a := { blsPairOO.a with isInf := 0 } }
  pairingCheckAffineBLS12381 bls12381PairingParams infFlag2 bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams infNonZero blsQ0AB bls12381PairingParams.g2Gen blsWitnessAB == 0 &&
  pairingCheckAffineBLS12381 bls12381PairingParams finiteZero bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 0

-- Real BLS12-381 torsion point ON curve y² = x³ + 4 OUTSIDE prime-order G1 subgroup!
private def blsTorsionPoint : G1Point :=
  { x := 4
    y := 1630892974828014537729259858097113969650871260980656934049590190201941782487224876496582135785777461178964897591404
    isInf := 0 }

#guard g1OnCurve bls12381CurveParams blsTorsionPoint == true
#guard g1InSubgroup bls12381PairingParams blsTorsionPoint == false
#guard g1InSubgroup bls12381PairingParams (g1Gen bls12381CurveParams) == true
#guard g1InSubgroup bls12381PairingParams blsP0AB == true
#guard
  let torsionPair := encodeAffinePairBLS12381 radix80 blsTorsionPoint (g1Neg bls12381CurveParams blsTorsionPoint)
  pairingCheckAffineBLS12381 bls12381PairingParams torsionPair
    bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One == 0

/-! ### 6. Live-Exportable Benchmark Entrypoint `#guard`s (Positive + Negative Controls) -/

#guard entryFp12MulBN254 2 3 5 7 == 1
#guard entryFp12MulBN254 103 3 5 7 == 0
#guard entryFp12MulBLS12381 2 3 5 7 == 1
#guard entryFp12MulBLS12381 727 3 5 7 == 0

#guard entryPairingCheckBN254
  9 3 0 0  2 0 0 0  0
  6 4 0 0  2 1 0 0  0
  50 44 39 60 6 14 98 91 71 49 41 64 == 1
#guard entryPairingCheckBN254
  9 3 0 0  2 0 0 0  0
  6 4 0 0  2 1 0 0  0
  51 44 39 60 6 14 98 91 71 49 41 64 == 0
#guard entryPairingCheckBN254
  9 3 0 0  3 0 0 0  0
  6 4 0 0  2 1 0 0  0
  50 44 39 60 6 14 98 91 71 49 41 64 == 0
#guard entryPairingCheckBN254
  16 3 0 0  2 0 0 0  0
  6 4 0 0  2 1 0 0  0
  50 44 39 60 6 14 98 91 71 49 41 64 == 0
#guard entryPairingCheckBN254
  0 0 0 0  0 0 0 0  1
  0 0 0 0  0 0 0 0  1
  1 0 0 0 0 0 0 0 0 0 0 0 == 1
#guard entryPairingCheckBN254
  0 0 0 0  0 0 0 0  2
  0 0 0 0  0 0 0 0  1
  1 0 0 0 0 0 0 0 0 0 0 0 == 0

#guard entryPairingCheckBLS12381
  1 6 1 0 0  15 11 2 0 0  0
  8 10 1 0 0  14 8 0 0 0  0
  667 411 405 246 357 40 413 516 211 624 429 697 == 1
#guard entryPairingCheckBLS12381
  1 6 1 0 0  15 11 2 0 0  0
  8 10 1 0 0  14 8 0 0 0  0
  668 411 405 246 357 40 413 516 211 624 429 697 == 0
#guard entryPairingCheckBLS12381
  1 6 1 0 0  14 11 2 0 0  0
  8 10 1 0 0  14 8 0 0 0  0
  667 411 405 246 357 40 413 516 211 624 429 697 == 0
#guard entryPairingCheckBLS12381
  16 6 1 0 0  15 11 2 0 0  0
  8 10 1 0 0  14 8 0 0 0  0
  667 411 405 246 357 40 413 516 211 624 429 697 == 0
#guard g1OnCurve bls12381CircuitPairingParams.curve { x := 1, y := 673, isInf := 0 } == true
#guard g1InSubgroup bls12381CircuitPairingParams { x := 1, y := 673, isInf := 0 } == false
#guard entryPairingCheckBLS12381
  1 0 0 0 0  1 10 2 0 0  0
  1 0 0 0 0  6 3 0 0 0  0
  1 0 0 0 0 0 0 0 0 0 0 0 == 0
#guard entryPairingCheckBLS12381
  0 0 0 0 0  0 0 0 0 0  1
  0 0 0 0 0  0 0 0 0 0  1
  1 0 0 0 0 0 0 0 0 0 0 0 == 1

end PairingTests

end PairingPure
