/-! # Pure Lean 4 BN254 Groth16 Prover & Verifier for Certified `IxCC` x86-64 Execution

Completely standalone pure total Lean 4 (zero imports beyond the standard prelude;
zero `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `partial`, `unsafe`,
`@[extern]`, or `@[implemented_by]`) implementing:

1. **Certified `< 2^63` `9 × 29-bit` Montgomery Arithmetic (`Limb9`)** for BN254 `Fq` and `Fr`:
   - Every limb is `< 2^29 = 536870912` (`9 × 29 = 261 > 254` bits).
   - Every pairwise product is `< 2^58` and every CIOS Montgomery accumulator step
     `t_j + a_i * b_j + q * m_j + carry` stays `< 2^60 ≪ 2^63`.
   - Zero BigNat, zero `--uncertified` flags: 100% inside `IxCC`'s certified x86-64 fragment.
2. **Full BN254 Extension Field Tower (`Fp2`, `Fp6`, `Fp12`)**:
   - `Fp2 = Fp[u]/(u^2 + 1)`, `Fp6 = Fp2[v]/(v^3 - (9+u))`, `Fp12 = Fp6[w]/(w^2 - v)`.
   - Karatsuba/complex multiplication & squaring, inversion, sparse D-type `mulBy034`,
     and exact Frobenius endomorphisms `π_p`, `π_{p^2}`, `π_{p^3}`.
3. **Full BN254 Elliptic Curves `G1` ($y^2 = x^3 + 3$) & `G2` ($y^2 = x^3 + 3/(9+u)$)**:
   - Affine and Jacobian add, mixed add, double, negation, MSB-to-LSB scalar multiplication,
     canonicality/on-curve validation, and exact prime-order `G2` subgroup check
     `ψ(Q) = [6x^2]Q` (since `Norm(ψ - 6x^2) = r`).
4. **Full Exact BN254 Optimal Ate Pairing (`bn254Pairing`, `bn254MultiPairing4`)**:
   - Optimal Ate Miller loop over `6x + 2 = 29793968203157093288` (packed 64-digit NAF
     matching `ark-bn254 0.5.0` bit-for-bit) + Frobenius adjustment lines
     `ℓ_{T, π(Q)}(P)` and `ℓ_{T+π(Q), -π^2(Q)}(P)`.
   - Exact final exponentiation `f^((p^12 - 1)/r)` (easy part `(p^6 - 1)(p^2 + 1)` +
     exact Devegili-Scott hard part `(p^4 - p^2 + 1)/r` using 3 exponentiations by `x`).
5. **Real BN254 Groth16 Dev Setup + Prover + Verifier (Fermat Cubic R1CS Circuit)**:
   - Proves knowledge of `(x, y, z, d_inv)` satisfying `(x^3 + y^3 - z^3) * d_inv = 1`
     and `x + 256*y + 65536*z = pub` (8 R1CS constraints, 12 wires, exact 8th-root-of-unity
     QAP domain in BN254 `Fr`, 256-byte `(A ∈ G1, B ∈ G2, C ∈ G1)` proof, 4-pairing verify).
6. **Standalone Certified `IxCC` x86-64 Entrypoints**:
   - `groth16X86Main (mode : Nat) : Nat` for `ixcc compile --exe`,
   - `groth16MachineStep (s e : Nat) : Nat` for `ixcc compile --exe --machine`.
-/

set_option autoImplicit false

namespace Groth16X86

/-! ## Section 1: Certified `< 2^63` `9 × 29-bit` Limb & CIOS Montgomery Arithmetic -/

/-- Nine 29-bit little-endian `Nat` limbs (`< 2^29 = 536870912` each, `261` bits total).
Every CIOS Montgomery step stays strictly below `2^60 ≪ 2^63`. -/
structure Limb9 where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  l5 : Nat
  l6 : Nat
  l7 : Nat
  l8 : Nat

def limb9Zero : Limb9 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def limb9Unit : Limb9 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩

def limb9IsZero (a : Limb9) : Bool :=
  let s :=
    Nat.lor (Nat.lor (Nat.lor a.l0 a.l1) (Nat.lor a.l2 a.l3))
            (Nat.lor (Nat.lor a.l4 a.l5) (Nat.lor (Nat.lor a.l6 a.l7) a.l8))
  Nat.beq s 0

def limb9Eq (a b : Limb9) : Bool :=
  let d0 := Nat.xor a.l0 b.l0
  let d1 := Nat.xor a.l1 b.l1
  let d2 := Nat.xor a.l2 b.l2
  let d3 := Nat.xor a.l3 b.l3
  let d4 := Nat.xor a.l4 b.l4
  let d5 := Nat.xor a.l5 b.l5
  let d6 := Nat.xor a.l6 b.l6
  let d7 := Nat.xor a.l7 b.l7
  let d8 := Nat.xor a.l8 b.l8
  let s :=
    Nat.lor (Nat.lor (Nat.lor d0 d1) (Nat.lor d2 d3))
            (Nat.lor (Nat.lor d4 d5) (Nat.lor (Nat.lor d6 d7) d8))
  Nat.beq s 0

/-- Pack two 29-bit limbs into one 58-bit `Nat` (`< 2^58 ≪ 2^63`) for compact comparison. -/
def pack2 (lo hi : Nat) : Nat :=
  Nat.add lo (Nat.mul hi 536870912)

/-- Returns `true` iff `a ≥ b` for canonical `9 × 29-bit` limbs. -/
def limb9Ge (a b : Limb9) : Bool :=
  let a67 := pack2 a.l6 a.l7
  let b67 := pack2 b.l6 b.l7
  let a45 := pack2 a.l4 a.l5
  let b45 := pack2 b.l4 b.l5
  let a23 := pack2 a.l2 a.l3
  let b23 := pack2 b.l2 b.l3
  let a01 := pack2 a.l0 a.l1
  let b01 := pack2 b.l0 b.l1
  bif Nat.beq a.l8 b.l8 then
    bif Nat.beq a67 b67 then
      bif Nat.beq a45 b45 then
        bif Nat.beq a23 b23 then Nat.ble b01 a01
        else Nat.blt b23 a23
      else Nat.blt b45 a45
    else Nat.blt b67 a67
  else Nat.blt b.l8 a.l8

/-- Checks every limb `< 2^29` and total value `< m`. -/
def limb9Canonical (m a : Limb9) : Bool :=
  let hi :=
    Nat.lor (Nat.lor (Nat.lor (Nat.shiftRight a.l0 29) (Nat.shiftRight a.l1 29))
                     (Nat.lor (Nat.shiftRight a.l2 29) (Nat.shiftRight a.l3 29)))
            (Nat.lor (Nat.lor (Nat.shiftRight a.l4 29) (Nat.shiftRight a.l5 29))
                     (Nat.lor (Nat.lor (Nat.shiftRight a.l6 29) (Nat.shiftRight a.l7 29))
                              (Nat.shiftRight a.l8 29)))
  bif Nat.beq hi 0 then
    bif limb9Ge a m then false else true
  else false

/-- Branchless 9-limb addition (`a + b < 2^261`). -/
def limb9AddRaw (a b : Limb9) : Limb9 :=
  let s0 := Nat.add a.l0 b.l0
  let r0 := Nat.land s0 536870911
  let c1 := Nat.shiftRight s0 29
  let s1 := Nat.add (Nat.add a.l1 b.l1) c1
  let r1 := Nat.land s1 536870911
  let c2 := Nat.shiftRight s1 29
  let s2 := Nat.add (Nat.add a.l2 b.l2) c2
  let r2 := Nat.land s2 536870911
  let c3 := Nat.shiftRight s2 29
  let s3 := Nat.add (Nat.add a.l3 b.l3) c3
  let r3 := Nat.land s3 536870911
  let c4 := Nat.shiftRight s3 29
  let s4 := Nat.add (Nat.add a.l4 b.l4) c4
  let r4 := Nat.land s4 536870911
  let c5 := Nat.shiftRight s4 29
  let s5 := Nat.add (Nat.add a.l5 b.l5) c5
  let r5 := Nat.land s5 536870911
  let c6 := Nat.shiftRight s5 29
  let s6 := Nat.add (Nat.add a.l6 b.l6) c6
  let r6 := Nat.land s6 536870911
  let c7 := Nat.shiftRight s6 29
  let s7 := Nat.add (Nat.add a.l7 b.l7) c7
  let r7 := Nat.land s7 536870911
  let c8 := Nat.shiftRight s7 29
  let r8 := Nat.add (Nat.add a.l8 b.l8) c8
  ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩

/-- Branchless 9-limb subtraction (`a ≥ b`, all limbs `< 2^29`). -/
def limb9SubRaw (a b : Limb9) : Limb9 :=
  let d0 := Nat.sub (Nat.add 536870912 a.l0) b.l0
  let r0 := Nat.land d0 536870911
  let w1 := Nat.sub 1 (Nat.shiftRight d0 29)
  let d1 := Nat.sub (Nat.add 536870912 a.l1) (Nat.add b.l1 w1)
  let r1 := Nat.land d1 536870911
  let w2 := Nat.sub 1 (Nat.shiftRight d1 29)
  let d2 := Nat.sub (Nat.add 536870912 a.l2) (Nat.add b.l2 w2)
  let r2 := Nat.land d2 536870911
  let w3 := Nat.sub 1 (Nat.shiftRight d2 29)
  let d3 := Nat.sub (Nat.add 536870912 a.l3) (Nat.add b.l3 w3)
  let r3 := Nat.land d3 536870911
  let w4 := Nat.sub 1 (Nat.shiftRight d3 29)
  let d4 := Nat.sub (Nat.add 536870912 a.l4) (Nat.add b.l4 w4)
  let r4 := Nat.land d4 536870911
  let w5 := Nat.sub 1 (Nat.shiftRight d4 29)
  let d5 := Nat.sub (Nat.add 536870912 a.l5) (Nat.add b.l5 w5)
  let r5 := Nat.land d5 536870911
  let w6 := Nat.sub 1 (Nat.shiftRight d5 29)
  let d6 := Nat.sub (Nat.add 536870912 a.l6) (Nat.add b.l6 w6)
  let r6 := Nat.land d6 536870911
  let w7 := Nat.sub 1 (Nat.shiftRight d6 29)
  let d7 := Nat.sub (Nat.add 536870912 a.l7) (Nat.add b.l7 w7)
  let r7 := Nat.land d7 536870911
  let w8 := Nat.sub 1 (Nat.shiftRight d7 29)
  let d8 := Nat.sub (Nat.add 536870912 a.l8) (Nat.add b.l8 w8)
  let r8 := Nat.land d8 536870911
  ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩

/-- Single CIOS Montgomery step: `t' = (t + ai * b + q * m) / 2^29` with `t' < 2 * m`. -/
def montStep (m : Limb9) (mInv : Nat) (t b : Limb9) (ai : Nat) : Limb9 :=
  let u0 := Nat.land (Nat.add t.l0 (Nat.mul ai b.l0)) 536870911
  let q := Nat.land (Nat.mul u0 mInv) 536870911
  let s0 := Nat.add (Nat.add t.l0 (Nat.mul ai b.l0)) (Nat.mul q m.l0)
  let c1 := Nat.shiftRight s0 29
  let s1 := Nat.add (Nat.add (Nat.add t.l1 (Nat.mul ai b.l1)) (Nat.mul q m.l1)) c1
  let r0 := Nat.land s1 536870911
  let c2 := Nat.shiftRight s1 29
  let s2 := Nat.add (Nat.add (Nat.add t.l2 (Nat.mul ai b.l2)) (Nat.mul q m.l2)) c2
  let r1 := Nat.land s2 536870911
  let c3 := Nat.shiftRight s2 29
  let s3 := Nat.add (Nat.add (Nat.add t.l3 (Nat.mul ai b.l3)) (Nat.mul q m.l3)) c3
  let r2 := Nat.land s3 536870911
  let c4 := Nat.shiftRight s3 29
  let s4 := Nat.add (Nat.add (Nat.add t.l4 (Nat.mul ai b.l4)) (Nat.mul q m.l4)) c4
  let r3 := Nat.land s4 536870911
  let c5 := Nat.shiftRight s4 29
  let s5 := Nat.add (Nat.add (Nat.add t.l5 (Nat.mul ai b.l5)) (Nat.mul q m.l5)) c5
  let r4 := Nat.land s5 536870911
  let c6 := Nat.shiftRight s5 29
  let s6 := Nat.add (Nat.add (Nat.add t.l6 (Nat.mul ai b.l6)) (Nat.mul q m.l6)) c6
  let r5 := Nat.land s6 536870911
  let c7 := Nat.shiftRight s6 29
  let s7 := Nat.add (Nat.add (Nat.add t.l7 (Nat.mul ai b.l7)) (Nat.mul q m.l7)) c7
  let r6 := Nat.land s7 536870911
  let c8 := Nat.shiftRight s7 29
  let s8 := Nat.add (Nat.add (Nat.add t.l8 (Nat.mul ai b.l8)) (Nat.mul q m.l8)) c8
  let r7 := Nat.land s8 536870911
  let r8 := Nat.shiftRight s8 29
  ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩

def condSub (m a : Limb9) : Limb9 :=
  bif limb9Ge a m then limb9SubRaw a m else a

def modAdd (m a b : Limb9) : Limb9 :=
  condSub m (limb9AddRaw a b)

def modSub (m a b : Limb9) : Limb9 :=
  bif limb9Ge a b then limb9SubRaw a b else limb9SubRaw (limb9AddRaw a m) b

def modNeg (m a : Limb9) : Limb9 :=
  bif limb9IsZero a then limb9Zero else limb9SubRaw m a

def montMul (m : Limb9) (mInv : Nat) (a b : Limb9) : Limb9 :=
  let t0 := montStep m mInv limb9Zero b a.l0
  let t1 := montStep m mInv t0 b a.l1
  let t2 := montStep m mInv t1 b a.l2
  let t3 := montStep m mInv t2 b a.l3
  let t4 := montStep m mInv t3 b a.l4
  let t5 := montStep m mInv t4 b a.l5
  let t6 := montStep m mInv t5 b a.l6
  let t7 := montStep m mInv t6 b a.l7
  let t8 := montStep m mInv t7 b a.l8
  condSub m t8

/-- Convert a `< 2^63` `Nat` into raw `Limb9` (`< 2^63 < p, r`). -/
def limb9OfNat (n : Nat) : Limb9 :=
  ⟨Nat.land n 536870911,
   Nat.land (Nat.shiftRight n 29) 536870911,
   Nat.shiftRight n 58,
   0, 0, 0, 0, 0, 0⟩

/-! ## Section 2: BN254 Base Field `Fq` and Scalar Field `Fr` (Montgomery Form) -/

/-- BN254 `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`. -/
def fqP : Limb9 := ⟨410844487, 17064118, 477274959, 47522512, 361093496, 47923392, 10936641, 240920116, 3171406⟩
def fqPInv : Nat := 75916169
def fqOne : Limb9 := ⟨360500257, 337389400, 408039635, 21759001, 178483129, 490881230, 299191303, 86689704, 903222⟩
def fqTwo : Limb9 := ⟨184129602, 137907889, 279208359, 43518003, 356966258, 444891548, 61511695, 173379409, 1806444⟩
def fqThree : Limb9 := ⟨7758947, 475297290, 150377082, 65277005, 535449387, 398901866, 360702999, 260069113, 2709666⟩
def fqTwoInv : Limb9 := ⟨385672372, 177226759, 174221841, 303076213, 269788312, 269402311, 155063972, 163804910, 2037314⟩
def fqR2 : Limb9 := ⟨94088208, 219480995, 25171640, 279645352, 40052281, 46143135, 379321683, 294034764, 2757030⟩
def fqPm2 : Limb9 := ⟨410844485, 17064118, 477274959, 47522512, 361093496, 47923392, 10936641, 240920116, 3171406⟩

def fqAdd (a b : Limb9) : Limb9 := modAdd fqP a b
def fqSub (a b : Limb9) : Limb9 := modSub fqP a b
def fqNeg (a : Limb9) : Limb9 := modNeg fqP a
def fqDouble (a : Limb9) : Limb9 := modAdd fqP a a
def fqTriple (a : Limb9) : Limb9 := modAdd fqP (modAdd fqP a a) a
def fqMul (a b : Limb9) : Limb9 := montMul fqP fqPInv a b
def fqSqr (a : Limb9) : Limb9 := montMul fqP fqPInv a a
def fqToMont (a : Limb9) : Limb9 := montMul fqP fqPInv a fqR2
def fqFromMont (a : Limb9) : Limb9 := montMul fqP fqPInv a limb9Unit
def fqOfNat (n : Nat) : Limb9 := fqToMont (limb9OfNat n)
def fqCanonical (a : Limb9) : Bool := limb9Canonical fqP a

/-- Multiply an `Fq` element by `9` using 3 doublings + 1 addition (zero `fqMul`). -/
def fqMul9 (a : Limb9) : Limb9 :=
  let a2 := fqAdd a a
  let a4 := fqAdd a2 a2
  let a8 := fqAdd a4 a4
  fqAdd a8 a

def fqPowLimb (base : Limb9) (limb : Nat) : Nat → Limb9 → Limb9
  | 0, acc => acc
  | k + 1, acc =>
    let sq := fqSqr acc
    let bit := Nat.land (Nat.shiftRight limb k) 1
    let next := bif Nat.beq bit 1 then fqMul sq base else sq
    fqPowLimb base limb k next

def fqPow (base exp : Limb9) : Limb9 :=
  let a8 := fqPowLimb base exp.l8 22 fqOne
  let a7 := fqPowLimb base exp.l7 29 a8
  let a6 := fqPowLimb base exp.l6 29 a7
  let a5 := fqPowLimb base exp.l5 29 a6
  let a4 := fqPowLimb base exp.l4 29 a5
  let a3 := fqPowLimb base exp.l3 29 a4
  let a2 := fqPowLimb base exp.l2 29 a3
  let a1 := fqPowLimb base exp.l1 29 a2
  fqPowLimb base exp.l0 29 a1

def fqInv (a : Limb9) : Limb9 :=
  bif limb9IsZero a then limb9Zero else fqPow a fqPm2

/-- BN254 `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`. -/
def frR : Limb9 := ⟨268435457, 521120927, 240919632, 131109107, 361091715, 47923392, 10936641, 240920116, 3171406⟩
def frRInv : Nat := 268435455
def frOne : Limb9 := ⟨268435287, 514263732, 86771339, 391139145, 178784091, 490881230, 299191303, 86689704, 903222⟩
def frR2 : Limb9 := ⟨95853524, 102173274, 34397646, 498479371, 240439551, 486036963, 471195907, 131109217, 656714⟩
def frRm2 : Limb9 := ⟨268435455, 521120927, 240919632, 131109107, 361091715, 47923392, 10936641, 240920116, 3171406⟩
def frInv8 : Limb9 := ⟨268435435, 330749674, 309396827, 467934215, 470137659, 67350577, 307201449, 309386683, 509328⟩

def frAdd (a b : Limb9) : Limb9 := modAdd frR a b
def frSub (a b : Limb9) : Limb9 := modSub frR a b
def frNeg (a : Limb9) : Limb9 := modNeg frR a
def frMul (a b : Limb9) : Limb9 := montMul frR frRInv a b
def frSqr (a : Limb9) : Limb9 := montMul frR frRInv a a
def frToMont (a : Limb9) : Limb9 := montMul frR frRInv a frR2
def frFromMont (a : Limb9) : Limb9 := montMul frR frRInv a limb9Unit
def frOfNat (n : Nat) : Limb9 := frToMont (limb9OfNat n)
def frCanonical (a : Limb9) : Bool := limb9Canonical frR a

def frPowLimb (base : Limb9) (limb : Nat) : Nat → Limb9 → Limb9
  | 0, acc => acc
  | k + 1, acc =>
    let sq := frSqr acc
    let bit := Nat.land (Nat.shiftRight limb k) 1
    let next := bif Nat.beq bit 1 then frMul sq base else sq
    frPowLimb base limb k next

def frPow (base exp : Limb9) : Limb9 :=
  let a8 := frPowLimb base exp.l8 22 frOne
  let a7 := frPowLimb base exp.l7 29 a8
  let a6 := frPowLimb base exp.l6 29 a7
  let a5 := frPowLimb base exp.l5 29 a6
  let a4 := frPowLimb base exp.l4 29 a5
  let a3 := frPowLimb base exp.l3 29 a4
  let a2 := frPowLimb base exp.l2 29 a3
  let a1 := frPowLimb base exp.l1 29 a2
  frPowLimb base exp.l0 29 a1

def frInv (a : Limb9) : Limb9 :=
  bif limb9IsZero a then limb9Zero else frPow a frRm2

/-! ## Section 3: BN254 Extension Field Tower (`Fp2`, `Fp6`, `Fp12`) -/

/-- Element of `Fp2 = Fp[u]/(u^2 + 1)` (`c0 + c1 * u`) with Montgomery `Fq` coordinates. -/
structure Fp2 where
  c0 : Limb9
  c1 : Limb9

def fp2Zero : Fp2 := { c0 := limb9Zero, c1 := limb9Zero }
def fp2One : Fp2 := { c0 := fqOne, c1 := limb9Zero }

def fp2IsZero (a : Fp2) : Bool :=
  bif limb9IsZero a.c0 then limb9IsZero a.c1 else false

def fp2Eq (a b : Fp2) : Bool :=
  bif limb9Eq a.c0 b.c0 then limb9Eq a.c1 b.c1 else false

def fp2Canonical (a : Fp2) : Bool :=
  bif fqCanonical a.c0 then fqCanonical a.c1 else false

def fp2Add (a b : Fp2) : Fp2 := { c0 := fqAdd a.c0 b.c0, c1 := fqAdd a.c1 b.c1 }
def fp2Sub (a b : Fp2) : Fp2 := { c0 := fqSub a.c0 b.c0, c1 := fqSub a.c1 b.c1 }
def fp2Neg (a : Fp2) : Fp2 := { c0 := fqNeg a.c0, c1 := fqNeg a.c1 }
def fp2Conj (a : Fp2) : Fp2 := { c0 := a.c0, c1 := fqNeg a.c1 }
def fp2Double (a : Fp2) : Fp2 := fp2Add a a
def fp2Triple (a : Fp2) : Fp2 := fp2Add (fp2Add a a) a
def fp2MulByFq (a : Fp2) (s : Limb9) : Fp2 := { c0 := fqMul a.c0 s, c1 := fqMul a.c1 s }

/-- Karatsuba multiplication in `Fp2` (3 `fqMul`). -/
def fp2Mul (a b : Fp2) : Fp2 :=
  let v0 := fqMul a.c0 b.c0
  let v1 := fqMul a.c1 b.c1
  let s0 := fqAdd a.c0 a.c1
  let s1 := fqAdd b.c0 b.c1
  let p01 := fqMul s0 s1
  let c0 := fqSub v0 v1
  let c1 := fqSub (fqSub p01 v0) v1
  { c0, c1 }

/-- Complex squaring in `Fp2` (2 `fqMul`). -/
def fp2Sqr (a : Fp2) : Fp2 :=
  let ab := fqMul a.c0 a.c1
  let sum := fqAdd a.c0 a.c1
  let diff := fqSub a.c0 a.c1
  let c0 := fqMul sum diff
  let c1 := fqAdd ab ab
  { c0, c1 }

/-- Multiply by BN254 non-residue `ξ = 9 + u`: `(a0 + a1*u)*(9 + u) = (9*a0 - a1) + (a0 + 9*a1)*u`. -/
def fp2MulByNonResidue (a : Fp2) : Fp2 :=
  { c0 := fqSub (fqMul9 a.c0) a.c1, c1 := fqAdd a.c0 (fqMul9 a.c1) }

/-- Multiplicative inverse in `Fp2` (`0⁻¹ = 0`). -/
def fp2Inv (a : Fp2) : Fp2 :=
  let norm := fqAdd (fqSqr a.c0) (fqSqr a.c1)
  let invNorm := fqInv norm
  { c0 := fqMul a.c0 invNorm, c1 := fqNeg (fqMul a.c1 invNorm) }

/-- BN254 Frobenius constants in `Fp2` (Montgomery form). -/
def frob6C1_1 : Fp2 := { c0 := ⟨77959568, 116720857, 200831163, 387972444, 449106301, 79574741, 198110247, 444835091, 2396851⟩, c1 := ⟨286535409, 187804871, 492312764, 403373079, 442701694, 360078139, 294614062, 104485018, 1269326⟩ }
def frob6C2_1 : Fp2 := { c0 := ⟨276953182, 328873349, 306900296, 55370336, 434202341, 186067288, 221116544, 233072759, 1472337⟩, c1 := ⟨258042488, 93586473, 404468614, 107881851, 15098452, 202552781, 251052073, 472003299, 457208⟩ }
def frob6C1_2 : Fp2 := { c0 := ⟨416069521, 391846970, 193189602, 244240497, 310558434, 69340804, 535036287, 352865610, 1478937⟩, c1 := limb9Zero }
def frob6C2_2 : Fp2 := { c0 := ⟨171145621, 361569571, 412916632, 318393925, 408922844, 24572269, 250450874, 338235712, 789246⟩, c1 := limb9Zero }
def frob6C1_3 : Fp2 := { c0 := ⟨325889741, 432474136, 497955025, 42907526, 200183625, 441570494, 324828416, 301853753, 830815⟩, c1 := ⟨115639766, 437132463, 279613835, 73502212, 128670103, 395362884, 114011013, 518486521, 2516630⟩ }
def frob6C2_3 : Fp2 := { c0 := ⟨184051396, 109191840, 495742184, 2670331, 316545484, 294905530, 164669302, 459358945, 1341039⟩, c1 := ⟨164889335, 177818119, 378890167, 153193343, 453739841, 53273248, 261318439, 380451190, 765836⟩ }
def frob12C1_1 : Fp2 := { c0 := ⟨168567705, 446838140, 21606957, 76005147, 193575774, 320063457, 492961205, 101471925, 3016032⟩, c1 := ⟨466013235, 394132337, 371054763, 25204381, 93145077, 448361909, 29518381, 483951129, 39811⟩ }
def frob12C1_2 : Fp2 := { c0 := ⟨239698866, 192365459, 64358326, 265999499, 489041563, 23351122, 297356679, 439555315, 2382159⟩, c1 := limb9Zero }
def frob12C1_3 : Fp2 := { c0 := ⟨241843517, 234894524, 489670951, 377358109, 130864789, 78929213, 242247822, 507627824, 1062952⟩, c1 := ⟨256797489, 98403818, 382339799, 433159222, 464404099, 29325343, 50434485, 281019966, 1260793⟩ }

/-- Element of `Fp6 = Fp2[v]/(v^3 - (9+u))`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2

def fp6Zero : Fp6 := { c0 := fp2Zero, c1 := fp2Zero, c2 := fp2Zero }
def fp6One : Fp6 := { c0 := fp2One, c1 := fp2Zero, c2 := fp2Zero }

def fp6IsZero (a : Fp6) : Bool :=
  bif fp2IsZero a.c0 then (bif fp2IsZero a.c1 then fp2IsZero a.c2 else false) else false

def fp6Eq (a b : Fp6) : Bool :=
  bif fp2Eq a.c0 b.c0 then (bif fp2Eq a.c1 b.c1 then fp2Eq a.c2 b.c2 else false) else false

def fp6Add (a b : Fp6) : Fp6 := { c0 := fp2Add a.c0 b.c0, c1 := fp2Add a.c1 b.c1, c2 := fp2Add a.c2 b.c2 }
def fp6Sub (a b : Fp6) : Fp6 := { c0 := fp2Sub a.c0 b.c0, c1 := fp2Sub a.c1 b.c1, c2 := fp2Sub a.c2 b.c2 }
def fp6Neg (a : Fp6) : Fp6 := { c0 := fp2Neg a.c0, c1 := fp2Neg a.c1, c2 := fp2Neg a.c2 }

def fp6MulByNonResidue (a : Fp6) : Fp6 :=
  { c0 := fp2MulByNonResidue a.c2, c1 := a.c0, c2 := a.c1 }

def fp6MulByFp2 (a : Fp6) (s : Fp2) : Fp6 :=
  { c0 := fp2Mul a.c0 s, c1 := fp2Mul a.c1 s, c2 := fp2Mul a.c2 s }

/-- Karatsuba multiplication in `Fp6` (6 `fp2Mul`). -/
def fp6Mul (a b : Fp6) : Fp6 :=
  let v0 := fp2Mul a.c0 b.c0
  let v1 := fp2Mul a.c1 b.c1
  let v2 := fp2Mul a.c2 b.c2
  let t12 := fp2Sub (fp2Sub (fp2Mul (fp2Add a.c1 a.c2) (fp2Add b.c1 b.c2)) v1) v2
  let c0 := fp2Add v0 (fp2MulByNonResidue t12)
  let t01 := fp2Sub (fp2Sub (fp2Mul (fp2Add a.c0 a.c1) (fp2Add b.c0 b.c1)) v0) v1
  let c1 := fp2Add t01 (fp2MulByNonResidue v2)
  let t02 := fp2Sub (fp2Sub (fp2Mul (fp2Add a.c0 a.c2) (fp2Add b.c0 b.c2)) v0) v2
  let c2 := fp2Add t02 v1
  { c0, c1, c2 }

/-- CH-SQR2 squaring in `Fp6`. -/
def fp6Sqr (a : Fp6) : Fp6 :=
  let s0 := fp2Sqr a.c0
  let ab := fp2Mul a.c0 a.c1
  let s1 := fp2Add ab ab
  let s2 := fp2Sqr (fp2Add (fp2Sub a.c0 a.c1) a.c2)
  let bc := fp2Mul a.c1 a.c2
  let s3 := fp2Add bc bc
  let s4 := fp2Sqr a.c2
  let c0 := fp2Add s0 (fp2MulByNonResidue s3)
  let c1 := fp2Add s1 (fp2MulByNonResidue s4)
  let c2 := fp2Sub (fp2Sub (fp2Add (fp2Add s1 s2) s3) s0) s4
  { c0, c1, c2 }

/-- Sparse multiplication in `Fp6` by `b0 + b1*v`. -/
def fp6MulBy01 (a : Fp6) (b0 b1 : Fp2) : Fp6 :=
  let aa := fp2Mul a.c0 b0
  let bb := fp2Mul a.c1 b1
  let t1 := fp2Add (fp2MulByNonResidue (fp2Sub (fp2Mul b1 (fp2Add a.c1 a.c2)) bb)) aa
  let t3 := fp2Add (fp2Sub (fp2Mul b0 (fp2Add a.c0 a.c2)) aa) bb
  let t2 := fp2Sub (fp2Sub (fp2Mul (fp2Add b0 b1) (fp2Add a.c0 a.c1)) aa) bb
  { c0 := t1, c1 := t2, c2 := t3 }

/-- Multiplicative inverse in `Fp6` (`0⁻¹ = 0`). -/
def fp6Inv (a : Fp6) : Fp6 :=
  let c0 := fp2Sub (fp2Sqr a.c0) (fp2MulByNonResidue (fp2Mul a.c1 a.c2))
  let c1 := fp2Sub (fp2MulByNonResidue (fp2Sqr a.c2)) (fp2Mul a.c0 a.c1)
  let c2 := fp2Sub (fp2Sqr a.c1) (fp2Mul a.c0 a.c2)
  let t := fp2Add (fp2Mul a.c0 c0)
    (fp2MulByNonResidue (fp2Add (fp2Mul a.c2 c1) (fp2Mul a.c1 c2)))
  let invT := fp2Inv t
  { c0 := fp2Mul c0 invT, c1 := fp2Mul c1 invT, c2 := fp2Mul c2 invT }

def fp6FrobOdd (k1 k2 : Fp2) (a : Fp6) : Fp6 :=
  { c0 := fp2Conj a.c0, c1 := fp2Mul (fp2Conj a.c1) k1, c2 := fp2Mul (fp2Conj a.c2) k2 }

def fp6FrobEven (k1 k2 : Fp2) (a : Fp6) : Fp6 :=
  { c0 := a.c0, c1 := fp2Mul a.c1 k1, c2 := fp2Mul a.c2 k2 }

/-- Element of `Fp12 = Fp6[w]/(w^2 - v)`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6

def fp12Zero : Fp12 := { c0 := fp6Zero, c1 := fp6Zero }
def fp12One : Fp12 := { c0 := fp6One, c1 := fp6Zero }

def fp12IsZero (a : Fp12) : Bool :=
  bif fp6IsZero a.c0 then fp6IsZero a.c1 else false

def fp12Eq (a b : Fp12) : Bool :=
  bif fp6Eq a.c0 b.c0 then fp6Eq a.c1 b.c1 else false

def fp12IsOne (a : Fp12) : Bool :=
  fp12Eq a fp12One

def fp12Add (a b : Fp12) : Fp12 := { c0 := fp6Add a.c0 b.c0, c1 := fp6Add a.c1 b.c1 }
def fp12Sub (a b : Fp12) : Fp12 := { c0 := fp6Sub a.c0 b.c0, c1 := fp6Sub a.c1 b.c1 }
def fp12Neg (a : Fp12) : Fp12 := { c0 := fp6Neg a.c0, c1 := fp6Neg a.c1 }
def fp12Conj (a : Fp12) : Fp12 := { c0 := a.c0, c1 := fp6Neg a.c1 }

/-- Karatsuba multiplication in `Fp12` (3 `fp6Mul`). -/
def fp12Mul (a b : Fp12) : Fp12 :=
  let v0 := fp6Mul a.c0 b.c0
  let v1 := fp6Mul a.c1 b.c1
  let c0 := fp6Add v0 (fp6MulByNonResidue v1)
  let c1 := fp6Sub (fp6Sub (fp6Mul (fp6Add a.c0 a.c1) (fp6Add b.c0 b.c1)) v0) v1
  { c0, c1 }

/-- Complex squaring in `Fp12` (2 `fp6Mul`). -/
def fp12Sqr (a : Fp12) : Fp12 :=
  let ab := fp6Mul a.c0 a.c1
  let s0 := fp6Add a.c0 a.c1
  let s1 := fp6Add a.c0 (fp6MulByNonResidue a.c1)
  let prod := fp6Mul s0 s1
  let c0 := fp6Sub (fp6Sub prod ab) (fp6MulByNonResidue ab)
  let c1 := fp6Add ab ab
  { c0, c1 }

/-- Multiplicative inverse in `Fp12` (`0⁻¹ = 0`). -/
def fp12Inv (a : Fp12) : Fp12 :=
  let norm := fp6Sub (fp6Sqr a.c0) (fp6MulByNonResidue (fp6Sqr a.c1))
  let invNorm := fp6Inv norm
  { c0 := fp6Mul a.c0 invNorm, c1 := fp6Neg (fp6Mul a.c1 invNorm) }

/-- Sparse D-type twist line multiplication in `Fp12` (`ark-ff` `mul_by_034`). -/
def fp12MulBy034 (f : Fp12) (c0 c3 c4 : Fp2) : Fp12 :=
  let a := fp6MulByFp2 f.c0 c0
  let b := fp6MulBy01 f.c1 c3 c4
  let e := fp6MulBy01 (fp6Add f.c0 f.c1) (fp2Add c0 c3) c4
  let resC1 := fp6Sub e (fp6Add a b)
  let resC0 := fp6Add (fp6MulByNonResidue b) a
  { c0 := resC0, c1 := resC1 }

def fp12Frob1 (a : Fp12) : Fp12 :=
  { c0 := fp6FrobOdd frob6C1_1 frob6C2_1 a.c0
    c1 := fp6MulByFp2 (fp6FrobOdd frob6C1_1 frob6C2_1 a.c1) frob12C1_1 }

def fp12Frob2 (a : Fp12) : Fp12 :=
  { c0 := fp6FrobEven frob6C1_2 frob6C2_2 a.c0
    c1 := fp6MulByFp2 (fp6FrobEven frob6C1_2 frob6C2_2 a.c1) frob12C1_2 }

def fp12Frob3 (a : Fp12) : Fp12 :=
  { c0 := fp6FrobOdd frob6C1_3 frob6C2_3 a.c0
    c1 := fp6MulByFp2 (fp6FrobOdd frob6C1_3 frob6C2_3 a.c1) frob12C1_3 }

/-- BN254 curve seed `x = 4965661367192848881` (63-bit `< 2^63`, leading `1` at bit 62). -/
def bn254X : Nat := 4965661367192848881

def fp12PowXLoop (base : Fp12) : Nat → Fp12 → Fp12
  | 0, acc => acc
  | k + 1, acc =>
    let sq := fp12Sqr acc
    let bit := Nat.land (Nat.shiftRight bn254X k) 1
    let next := bif Nat.beq bit 1 then fp12Mul sq base else sq
    fp12PowXLoop base k next

/-- Exact exponentiation `f^x` for BN254 seed `x = 4965661367192848881`. -/
def fp12PowX (f : Fp12) : Fp12 :=
  fp12PowXLoop f 62 f

/-- Compute `f^6 = (f^3)^2` (2 squarings + 1 multiplication). -/
def fp12Pow6 (f : Fp12) : Fp12 :=
  let f2 := fp12Sqr f
  let f3 := fp12Mul f2 f
  fp12Sqr f3

/-! ## Section 4: BN254 Curves `G1` ($y^2 = x^3 + 3$) & `G2` ($y^2 = x^3 + 3/(9+u)$) -/

/-- Canonical affine `G1` point (`isInf = 1` iff point at infinity `(0, 0)`). -/
structure G1Aff where
  x : Limb9
  y : Limb9
  isInf : Nat

/-- Jacobian projective `G1` point (`z = 0` iff point at infinity). -/
structure G1Jac where
  x : Limb9
  y : Limb9
  z : Limb9

def g1Inf : G1Aff := { x := limb9Zero, y := limb9Zero, isInf := 1 }
def g1Gen : G1Aff := { x := fqOne, y := fqTwo, isInf := 0 }
def g1JacInf : G1Jac := { x := fqOne, y := fqOne, z := limb9Zero }

def g1Eq (P Q : G1Aff) : Bool :=
  bif Nat.beq P.isInf Q.isInf then
    bif Nat.beq P.isInf 1 then true
    else bif limb9Eq P.x Q.x then limb9Eq P.y Q.y else false
  else false

def g1Neg (P : G1Aff) : G1Aff :=
  bif Nat.beq P.isInf 1 then g1Inf else { x := P.x, y := fqNeg P.y, isInf := 0 }

/-- Canonicality and curve equation check on `E(Fq): y^2 = x^3 + 3` (`h_1 = 1`). -/
def g1OnCurve (P : G1Aff) : Bool :=
  bif Nat.beq P.isInf 1 then
    bif limb9IsZero P.x then limb9IsZero P.y else false
  else bif Nat.beq P.isInf 0 then
    bif fqCanonical P.x then
      bif fqCanonical P.y then
        let y2 := fqSqr P.y
        let x3 := fqMul (fqSqr P.x) P.x
        limb9Eq y2 (fqAdd x3 fqThree)
      else false
    else false
  else false

def g1ToJac (P : G1Aff) : G1Jac :=
  bif Nat.beq P.isInf 1 then g1JacInf else { x := P.x, y := P.y, z := fqOne }

def g1ToAff (R : G1Jac) : G1Aff :=
  bif limb9IsZero R.z then g1Inf
  else
    let zi := fqInv R.z
    let zi2 := fqSqr zi
    let zi3 := fqMul zi2 zi
    { x := fqMul R.x zi2, y := fqMul R.y zi3, isInf := 0 }

/-- Branchless Jacobian `G1` doubling (`a = 0`, EFD `dbl-2009-l`). -/
def g1JacDouble (R : G1Jac) : G1Jac :=
  let a := fqSqr R.x
  let b := fqSqr R.y
  let c := fqSqr b
  let xb := fqAdd R.x b
  let d0 := fqSub (fqSub (fqSqr xb) a) c
  let d := fqAdd d0 d0
  let e := fqTriple a
  let f := fqSqr e
  let x3 := fqSub f (fqAdd d d)
  let c2 := fqAdd c c
  let c4 := fqAdd c2 c2
  let c8 := fqAdd c4 c4
  let y3 := fqSub (fqMul e (fqSub d x3)) c8
  let yz := fqMul R.y R.z
  let z3 := fqAdd yz yz
  { x := x3, y := y3, z := z3 }

/-- Complete mixed Jacobian + Affine `G1` addition `R + P`. -/
def g1JacAddMixed (R : G1Jac) (P : G1Aff) : G1Jac :=
  bif Nat.beq P.isInf 1 then R
  else bif limb9IsZero R.z then { x := P.x, y := P.y, z := fqOne }
  else
    let z1z1 := fqSqr R.z
    let u2 := fqMul P.x z1z1
    let s2 := fqMul P.y (fqMul R.z z1z1)
    let h := fqSub u2 R.x
    let r := fqSub s2 R.y
    bif limb9IsZero h then
      bif limb9IsZero r then g1JacDouble R else g1JacInf
    else
      let hh := fqSqr h
      let hhh := fqMul h hh
      let v := fqMul R.x hh
      let x3 := fqSub (fqSub (fqSqr r) hhh) (fqAdd v v)
      let y3 := fqSub (fqMul r (fqSub v x3)) (fqMul R.y hhh)
      let z3 := fqMul R.z h
      { x := x3, y := y3, z := z3 }

/-- Complete Jacobian + Jacobian `G1` addition `R1 + R2`. -/
def g1JacAdd (R1 R2 : G1Jac) : G1Jac :=
  bif limb9IsZero R1.z then R2
  else bif limb9IsZero R2.z then R1
  else
    let z1z1 := fqSqr R1.z
    let z2z2 := fqSqr R2.z
    let u1 := fqMul R1.x z2z2
    let u2 := fqMul R2.x z1z1
    let s1 := fqMul R1.y (fqMul R2.z z2z2)
    let s2 := fqMul R2.y (fqMul R1.z z1z1)
    let h := fqSub u2 u1
    let r := fqSub s2 s1
    bif limb9IsZero h then
      bif limb9IsZero r then g1JacDouble R1 else g1JacInf
    else
      let hh := fqSqr h
      let hhh := fqMul h hh
      let v := fqMul u1 hh
      let x3 := fqSub (fqSub (fqSqr r) hhh) (fqAdd v v)
      let y3 := fqSub (fqMul r (fqSub v x3)) (fqMul s1 hhh)
      let z3 := fqMul (fqMul R1.z R2.z) h
      { x := x3, y := y3, z := z3 }

def g1AddAff (P Q : G1Aff) : G1Aff :=
  g1ToAff (g1JacAddMixed (g1ToJac P) Q)

def g1MulLimb (base : G1Aff) (limb : Nat) : Nat → G1Jac → G1Jac
  | 0, acc => acc
  | k + 1, acc =>
    let dbl := g1JacDouble acc
    let bit := Nat.land (Nat.shiftRight limb k) 1
    let next := bif Nat.beq bit 1 then g1JacAddMixed dbl base else dbl
    g1MulLimb base limb k next

def g1MulLimbOpt (base : G1Aff) (limb bits : Nat) (acc : G1Jac) : G1Jac :=
  bif limb9IsZero acc.z then
    bif Nat.beq limb 0 then acc else g1MulLimb base limb bits acc
  else g1MulLimb base limb bits acc

/-- Jacobian `G1` scalar multiplication `[k]base` for a raw (non-Montgomery) `Limb9` scalar `k`. -/
def g1MulRawJac (k : Limb9) (base : G1Aff) : G1Jac :=
  bif Nat.beq base.isInf 1 then g1JacInf
  else
    let a8 := g1MulLimbOpt base k.l8 22 g1JacInf
    let a7 := g1MulLimbOpt base k.l7 29 a8
    let a6 := g1MulLimbOpt base k.l6 29 a7
    let a5 := g1MulLimbOpt base k.l5 29 a6
    let a4 := g1MulLimbOpt base k.l4 29 a5
    let a3 := g1MulLimbOpt base k.l3 29 a4
    let a2 := g1MulLimbOpt base k.l2 29 a3
    let a1 := g1MulLimbOpt base k.l1 29 a2
    g1MulLimbOpt base k.l0 29 a1

/-- Jacobian `G1` scalar multiplication `[s]base` for a Montgomery-encoded `Fr` scalar `s`. -/
def g1MulJac (s : Limb9) (base : G1Aff) : G1Jac :=
  bif Nat.beq base.isInf 1 then g1JacInf
  else bif limb9IsZero s then g1JacInf
  else g1MulRawJac (frFromMont s) base

def g1Mul (s : Limb9) (base : G1Aff) : G1Aff :=
  g1ToAff (g1MulJac s base)

def g1MsmAcc (acc : G1Jac) (s : Limb9) (pt : G1Aff) : G1Jac :=
  bif Nat.beq pt.isInf 1 then acc
  else bif limb9IsZero s then acc
  else g1JacAdd acc (g1MulJac s pt)

/-- BN254 `G2` sextic twist parameters (`b' = 3 / (9 + u)`, generator `G2`, Frobenius maps). -/
def bn254BTwist : Fp2 := { c0 := ⟨189306456, 13619797, 266050167, 47090167, 3383508, 443974981, 116276700, 275414465, 1651051⟩, c1 := ⟨463465696, 132959441, 275378631, 215966963, 22334433, 231877312, 116106472, 422158901, 2635577⟩ }
def bn254G2GenX : Fp2 := { c0 := ⟨263467088, 326092182, 283205507, 419112272, 492970580, 382036998, 328189953, 16512512, 2400801⟩, c1 := ⟨187911013, 121279584, 83090042, 310628709, 121681262, 178446394, 218858586, 306035017, 2803220⟩ }
def bn254G2GenY : Fp2 := { c0 := ⟨407799875, 42232385, 348424631, 137056607, 383782229, 419585381, 300289327, 184709515, 334743⟩, c1 := ⟨111539777, 3403866, 165551449, 80368455, 523834231, 36564106, 458035537, 420650429, 68954⟩ }
def bn254TwistQX : Fp2 := frob6C1_1
def bn254TwistQY : Fp2 := { c0 := ⟨455018104, 57932550, 320278461, 408777911, 37819167, 383878197, 519288526, 32534274, 1918653⟩, c1 := ⟨430327765, 436072363, 496131354, 220163167, 145517765, 530932250, 323946238, 161949718, 1410845⟩ }

/-- Canonical affine `G2` point over `Fp2`. -/
structure G2Aff where
  x : Fp2
  y : Fp2
  isInf : Nat

/-- Jacobian projective `G2` point over `Fp2` (`z = 0` iff infinity). -/
structure G2Jac where
  x : Fp2
  y : Fp2
  z : Fp2

def g2Inf : G2Aff := { x := fp2Zero, y := fp2Zero, isInf := 1 }
def g2Gen : G2Aff := { x := bn254G2GenX, y := bn254G2GenY, isInf := 0 }
def g2JacInf : G2Jac := { x := fp2One, y := fp2One, z := fp2Zero }

def g2Eq (P Q : G2Aff) : Bool :=
  bif Nat.beq P.isInf Q.isInf then
    bif Nat.beq P.isInf 1 then true
    else bif fp2Eq P.x Q.x then fp2Eq P.y Q.y else false
  else false

def g2Neg (Q : G2Aff) : G2Aff :=
  bif Nat.beq Q.isInf 1 then g2Inf else { x := Q.x, y := fp2Neg Q.y, isInf := 0 }

/-- Untwist-Frobenius-twist endomorphism `ψ(Q) = (x̄ · ξ^((p-1)/3), ȳ · ξ^((p-1)/2))`. -/
def g2MulByChar (Q : G2Aff) : G2Aff :=
  bif Nat.beq Q.isInf 1 then g2Inf
  else
    { x := fp2Mul (fp2Conj Q.x) bn254TwistQX
      y := fp2Mul (fp2Conj Q.y) bn254TwistQY
      isInf := 0 }

/-- Canonicality and twist curve check on `E'(Fp2): y^2 = x^3 + 3/(9+u)`. -/
def g2OnCurve (Q : G2Aff) : Bool :=
  bif Nat.beq Q.isInf 1 then
    bif fp2IsZero Q.x then fp2IsZero Q.y else false
  else bif Nat.beq Q.isInf 0 then
    bif fp2Canonical Q.x then
      bif fp2Canonical Q.y then
        let y2 := fp2Sqr Q.y
        let x3 := fp2Mul (fp2Sqr Q.x) Q.x
        fp2Eq y2 (fp2Add x3 bn254BTwist)
      else false
    else false
  else false

def g2ToJac (Q : G2Aff) : G2Jac :=
  bif Nat.beq Q.isInf 1 then g2JacInf else { x := Q.x, y := Q.y, z := fp2One }

def g2ToAff (R : G2Jac) : G2Aff :=
  bif fp2IsZero R.z then g2Inf
  else
    let zi := fp2Inv R.z
    let zi2 := fp2Sqr zi
    let zi3 := fp2Mul zi2 zi
    { x := fp2Mul R.x zi2, y := fp2Mul R.y zi3, isInf := 0 }

def g2JacDouble (R : G2Jac) : G2Jac :=
  let a := fp2Sqr R.x
  let b := fp2Sqr R.y
  let c := fp2Sqr b
  let xb := fp2Add R.x b
  let d0 := fp2Sub (fp2Sub (fp2Sqr xb) a) c
  let d := fp2Add d0 d0
  let e := fp2Triple a
  let f := fp2Sqr e
  let x3 := fp2Sub f (fp2Add d d)
  let c2 := fp2Add c c
  let c4 := fp2Add c2 c2
  let c8 := fp2Add c4 c4
  let y3 := fp2Sub (fp2Mul e (fp2Sub d x3)) c8
  let yz := fp2Mul R.y R.z
  let z3 := fp2Add yz yz
  { x := x3, y := y3, z := z3 }

def g2JacAddMixed (R : G2Jac) (Q : G2Aff) : G2Jac :=
  bif Nat.beq Q.isInf 1 then R
  else bif fp2IsZero R.z then { x := Q.x, y := Q.y, z := fp2One }
  else
    let z1z1 := fp2Sqr R.z
    let u2 := fp2Mul Q.x z1z1
    let s2 := fp2Mul Q.y (fp2Mul R.z z1z1)
    let h := fp2Sub u2 R.x
    let r := fp2Sub s2 R.y
    bif fp2IsZero h then
      bif fp2IsZero r then g2JacDouble R else g2JacInf
    else
      let hh := fp2Sqr h
      let hhh := fp2Mul h hh
      let v := fp2Mul R.x hh
      let x3 := fp2Sub (fp2Sub (fp2Sqr r) hhh) (fp2Add v v)
      let y3 := fp2Sub (fp2Mul r (fp2Sub v x3)) (fp2Mul R.y hhh)
      let z3 := fp2Mul R.z h
      { x := x3, y := y3, z := z3 }

def g2JacAdd (R1 R2 : G2Jac) : G2Jac :=
  bif fp2IsZero R1.z then R2
  else bif fp2IsZero R2.z then R1
  else
    let z1z1 := fp2Sqr R1.z
    let z2z2 := fp2Sqr R2.z
    let u1 := fp2Mul R1.x z2z2
    let u2 := fp2Mul R2.x z1z1
    let s1 := fp2Mul R1.y (fp2Mul R2.z z2z2)
    let s2 := fp2Mul R2.y (fp2Mul R1.z z1z1)
    let h := fp2Sub u2 u1
    let r := fp2Sub s2 s1
    bif fp2IsZero h then
      bif fp2IsZero r then g2JacDouble R1 else g2JacInf
    else
      let hh := fp2Sqr h
      let hhh := fp2Mul h hh
      let v := fp2Mul u1 hh
      let x3 := fp2Sub (fp2Sub (fp2Sqr r) hhh) (fp2Add v v)
      let y3 := fp2Sub (fp2Mul r (fp2Sub v x3)) (fp2Mul s1 hhh)
      let z3 := fp2Mul (fp2Mul R1.z R2.z) h
      { x := x3, y := y3, z := z3 }

def g2MulLimb (base : G2Aff) (limb : Nat) : Nat → G2Jac → G2Jac
  | 0, acc => acc
  | k + 1, acc =>
    let dbl := g2JacDouble acc
    let bit := Nat.land (Nat.shiftRight limb k) 1
    let next := bif Nat.beq bit 1 then g2JacAddMixed dbl base else dbl
    g2MulLimb base limb k next

def g2MulLimbOpt (base : G2Aff) (limb bits : Nat) (acc : G2Jac) : G2Jac :=
  bif fp2IsZero acc.z then
    bif Nat.beq limb 0 then acc else g2MulLimb base limb bits acc
  else g2MulLimb base limb bits acc

def g2MulRawJac (k : Limb9) (base : G2Aff) : G2Jac :=
  bif Nat.beq base.isInf 1 then g2JacInf
  else
    let a8 := g2MulLimbOpt base k.l8 22 g2JacInf
    let a7 := g2MulLimbOpt base k.l7 29 a8
    let a6 := g2MulLimbOpt base k.l6 29 a7
    let a5 := g2MulLimbOpt base k.l5 29 a6
    let a4 := g2MulLimbOpt base k.l4 29 a5
    let a3 := g2MulLimbOpt base k.l3 29 a4
    let a2 := g2MulLimbOpt base k.l2 29 a3
    let a1 := g2MulLimbOpt base k.l1 29 a2
    g2MulLimbOpt base k.l0 29 a1

def g2MulJac (s : Limb9) (base : G2Aff) : G2Jac :=
  bif Nat.beq base.isInf 1 then g2JacInf
  else bif limb9IsZero s then g2JacInf
  else g2MulRawJac (frFromMont s) base

def g2Mul (s : Limb9) (base : G2Aff) : G2Aff :=
  g2ToAff (g2MulJac s base)

def g2MsmAcc (acc : G2Jac) (s : Limb9) (pt : G2Aff) : G2Jac :=
  bif Nat.beq pt.isInf 1 then acc
  else bif limb9IsZero s then acc
  else g2JacAdd acc (g2MulJac s pt)

/-- Jacobian `G2` scalar multiplication by the 63-bit BN254 seed `x = 4965661367192848881`. -/
def g2MulXJacLoop (base : G2Jac) : Nat → G2Jac → G2Jac
  | 0, acc => acc
  | k + 1, acc =>
    let dbl := g2JacDouble acc
    let bit := Nat.land (Nat.shiftRight bn254X k) 1
    let next := bif Nat.beq bit 1 then g2JacAdd dbl base else dbl
    g2MulXJacLoop base k next

def g2MulXJac (R : G2Jac) : G2Jac :=
  bif fp2IsZero R.z then g2JacInf else g2MulXJacLoop R 62 R

/-- Exact inversion-free BN254 prime-order `G2` subgroup check:
verifies `ψ(Q) = [6x^2]Q` in Jacobian coordinates (`Norm(ψ - 6x^2) = r`). -/
def g2InSubgroup (Q : G2Aff) : Bool :=
  bif Nat.beq Q.isInf 1 then true
  else
    let qJac := g2ToJac Q
    let xQ := g2MulXJac qJac
    let x2Q := g2MulXJac xQ
    let x2Q2 := g2JacDouble x2Q
    let x2Q3 := g2JacAdd x2Q2 x2Q
    let lhs := g2JacDouble x2Q3
    bif fp2IsZero lhs.z then false
    else
      let psiQ := g2MulByChar Q
      let z2 := fp2Sqr lhs.z
      let z3 := fp2Mul z2 lhs.z
      let okX := fp2Eq lhs.x (fp2Mul psiQ.x z2)
      let okY := fp2Eq lhs.y (fp2Mul psiQ.y z3)
      bif okX then okY else false

/-! ## Section 5: Full Exact BN254 Optimal Ate Pairing & Final Exponentiation -/

/-- Homogeneous projective `G2` accumulator `(x : y : z)` for inversion-free Miller loops. -/
structure G2Proj where
  x : Fp2
  y : Fp2
  z : Fp2

/-- Sparse D-type line evaluation coefficients `(c0, c1, c2)` matching `ark-ec` `EllCoeff`. -/
structure EllCoeff where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2

structure EllStep where
  next : G2Proj
  coeff : EllCoeff

structure SingleMillerOut where
  f : Fp12
  t : G2Proj

structure Miller4State where
  f : Fp12
  t0 : G2Proj
  t1 : G2Proj
  t2 : G2Proj
  t3 : G2Proj

/-- Packed 64-digit signed NAF of BN254 `6x + 2 = 29793968203157093288` after leading `1`
(`0 -> 0`, `1 -> +1`, `2 -> -1`, 2 bits/digit, 22 digits per word, `< 2^44 ≪ 2^63`). -/
def nafW0 : Nat := 558647877649
def nafW1 : Nat := 77317873728
def nafW2 : Nat := 4597482530

def bn254NafDigit (idx : Nat) : Nat :=
  bif Nat.blt idx 22 then
    Nat.land (Nat.shiftRight nafW0 (Nat.mul 2 idx)) 3
  else bif Nat.blt idx 44 then
    Nat.land (Nat.shiftRight nafW1 (Nat.mul 2 (Nat.sub idx 22))) 3
  else
    Nat.land (Nat.shiftRight nafW2 (Nat.mul 2 (Nat.sub idx 44))) 3

/-- Inversion-free homogeneous projective `G2` doubling step (`ark-ec` `double_in_place`). -/
def g2DoubleStep (R : G2Proj) : EllStep :=
  let a := fp2MulByFq (fp2Mul R.x R.y) fqTwoInv
  let b := fp2Sqr R.y
  let c := fp2Sqr R.z
  let e := fp2Mul bn254BTwist (fp2Triple c)
  let f := fp2Triple e
  let g := fp2MulByFq (fp2Add b f) fqTwoInv
  let h := fp2Sub (fp2Sqr (fp2Add R.y R.z)) (fp2Add b c)
  let i := fp2Sub e b
  let j := fp2Sqr R.x
  let e2 := fp2Sqr e
  let nx := fp2Mul a (fp2Sub b f)
  let ny := fp2Sub (fp2Sqr g) (fp2Triple e2)
  let nz := fp2Mul b h
  let j3 := fp2Triple j
  let negH := fp2Neg h
  { next := { x := nx, y := ny, z := nz }, coeff := { c0 := negH, c1 := j3, c2 := i } }

/-- Inversion-free homogeneous projective `G2` chord addition step (`ark-ec` `add_in_place`). -/
def g2AddStep (R : G2Proj) (Q : G2Aff) : EllStep :=
  let theta := fp2Sub R.y (fp2Mul Q.y R.z)
  let lam := fp2Sub R.x (fp2Mul Q.x R.z)
  let c := fp2Sqr theta
  let d := fp2Sqr lam
  let e := fp2Mul lam d
  let f := fp2Mul R.z c
  let g := fp2Mul R.x d
  let h := fp2Sub (fp2Add e f) (fp2Double g)
  let nx := fp2Mul lam h
  let ny := fp2Sub (fp2Mul theta (fp2Sub g h)) (fp2Mul e R.y)
  let nz := fp2Mul R.z e
  let j := fp2Sub (fp2Mul theta Q.x) (fp2Mul lam Q.y)
  let negTheta := fp2Neg theta
  { next := { x := nx, y := ny, z := nz }, coeff := { c0 := lam, c1 := negTheta, c2 := j } }

def evalLine (f : Fp12) (coeff : EllCoeff) (P : G1Aff) : Fp12 :=
  bif Nat.beq P.isInf 1 then f
  else
    let c0 := fp2MulByFq coeff.c0 P.y
    let c1 := fp2MulByFq coeff.c1 P.x
    fp12MulBy034 f c0 c1 coeff.c2

def doubleAndEval (qIsInf : Nat) (P : G1Aff) (T : G2Proj) (f : Fp12) : SingleMillerOut :=
  bif Nat.beq P.isInf 0 then
    bif Nat.beq qIsInf 0 then
      let s := g2DoubleStep T
      { f := evalLine f s.coeff P, t := s.next }
    else { f, t := T }
  else { f, t := T }

def addAndEval (P : G1Aff) (Q : G2Aff) (T : G2Proj) (f : Fp12) : SingleMillerOut :=
  bif Nat.beq P.isInf 0 then
    bif Nat.beq Q.isInf 0 then
      let s := g2AddStep T Q
      { f := evalLine f s.coeff P, t := s.next }
    else { f, t := T }
  else { f, t := T }

/-- Apply the two BN254 Frobenius adjustment lines `ℓ_{T, π(Q)}(P)` and `ℓ_{T+π(Q), -π^2(Q)}(P)`. -/
def applyBnFrobLines (f : Fp12) (T : G2Proj) (P : G1Aff) (Q : G2Aff) : Fp12 :=
  bif Nat.beq P.isInf 0 then
    bif Nat.beq Q.isInf 0 then
      let q1 := g2MulByChar Q
      let q2 := g2Neg (g2MulByChar q1)
      let s1 := g2AddStep T q1
      let f1 := evalLine f s1.coeff P
      let s2 := g2AddStep s1.next q2
      evalLine f1 s2.coeff P
    else f
  else f

def miller1Walk (P : G1Aff) (Q negQ : G2Aff) : Nat → Nat → SingleMillerOut → SingleMillerOut
  | 0, _, st => st
  | fuel + 1, idx, st =>
    let f0 := fp12Sqr st.f
    let o0 := doubleAndEval Q.isInf P st.t f0
    let digit := bn254NafDigit idx
    let next :=
      bif Nat.beq digit 1 then addAndEval P Q o0.t o0.f
      else bif Nat.beq digit 2 then addAndEval P negQ o0.t o0.f
      else o0
    miller1Walk P Q negQ fuel (Nat.add idx 1) next

/-- Single-pair BN254 optimal Ate Miller loop (matches `ark-bn254 0.5.0` bit-for-bit). -/
def bn254MillerLoop1 (P : G1Aff) (Q : G2Aff) : Fp12 :=
  let tInit : G2Proj := { x := Q.x, y := Q.y, z := fp2One }
  let st := miller1Walk P Q (g2Neg Q) 64 0 { f := fp12One, t := tInit }
  applyBnFrobLines st.f st.t P Q

def miller4StepAdd (P0 P1 P2 P3 : G1Aff) (A0 A1 A2 A3 : G2Aff)
    (o0 o1 o2 o3 : SingleMillerOut) : Miller4State :=
  let a0 := addAndEval P0 A0 o0.t o3.f
  let a1 := addAndEval P1 A1 o1.t a0.f
  let a2 := addAndEval P2 A2 o2.t a1.f
  let a3 := addAndEval P3 A3 o3.t a2.f
  { f := a3.f, t0 := a0.t, t1 := a1.t, t2 := a2.t, t3 := a3.t }

def miller4Walk (P0 P1 P2 P3 : G1Aff)
    (Q0 negQ0 Q1 negQ1 Q2 negQ2 Q3 negQ3 : G2Aff) :
    Nat → Nat → Miller4State → Miller4State
  | 0, _, st => st
  | fuel + 1, idx, st =>
    let f0 := fp12Sqr st.f
    let o0 := doubleAndEval Q0.isInf P0 st.t0 f0
    let o1 := doubleAndEval Q1.isInf P1 st.t1 o0.f
    let o2 := doubleAndEval Q2.isInf P2 st.t2 o1.f
    let o3 := doubleAndEval Q3.isInf P3 st.t3 o2.f
    let digit := bn254NafDigit idx
    let next :=
      bif Nat.beq digit 1 then
        miller4StepAdd P0 P1 P2 P3 Q0 Q1 Q2 Q3 o0 o1 o2 o3
      else bif Nat.beq digit 2 then
        miller4StepAdd P0 P1 P2 P3 negQ0 negQ1 negQ2 negQ3 o0 o1 o2 o3
      else
        { f := o3.f, t0 := o0.t, t1 := o1.t, t2 := o2.t, t3 := o3.t }
    miller4Walk P0 P1 P2 P3 Q0 negQ0 Q1 negQ1 Q2 negQ2 Q3 negQ3 fuel (Nat.add idx 1) next

/-- Joint 4-pairing BN254 optimal Ate Miller loop for Groth16 verification. -/
def bn254MillerLoop4 (P0 P1 P2 P3 : G1Aff) (Q0 Q1 Q2 Q3 : G2Aff) : Fp12 :=
  let t0 : G2Proj := { x := Q0.x, y := Q0.y, z := fp2One }
  let t1 : G2Proj := { x := Q1.x, y := Q1.y, z := fp2One }
  let t2 : G2Proj := { x := Q2.x, y := Q2.y, z := fp2One }
  let t3 : G2Proj := { x := Q3.x, y := Q3.y, z := fp2One }
  let st := miller4Walk P0 P1 P2 P3
    Q0 (g2Neg Q0) Q1 (g2Neg Q1) Q2 (g2Neg Q2) Q3 (g2Neg Q3)
    64 0 { f := fp12One, t0, t1, t2, t3 }
  let f1 := applyBnFrobLines st.f st.t0 P0 Q0
  let f2 := applyBnFrobLines f1 st.t1 P1 Q1
  let f3 := applyBnFrobLines f2 st.t2 P2 Q2
  applyBnFrobLines f3 st.t3 P3 Q3

/-- Exact BN254 Final Exponentiation `f^((p^12 - 1)/r)`:
- Easy part: `f2 = f^((p^6 - 1)(p^2 + 1))`
- Hard part: exact Devegili-Scott decomposition `(p^4 - p^2 + 1)/r = q0 + q1*p + q2*p^2 + p^3`
  with `q2 = 6x^2 + 1`, `q1 = -36x^3 - 18x^2 - 12x + 1`, `q0 = -36x^3 - 30x^2 - 18x - 2`,
  taking only 3 exponentiations by `x = 4965661367192848881`. -/
def bn254FinalExp (f : Fp12) : Fp12 :=
  bif fp12IsZero f then fp12Zero
  else
    -- Easy part: f1 = f^(p^6 - 1), f2 = f1^(p^2 + 1)
    let f1 := fp12Mul (fp12Conj f) (fp12Inv f)
    let f2 := fp12Mul (fp12Frob2 f1) f1
    -- Hard part: exact (p^4 - p^2 + 1)/r via 3 pow-x calls
    let fx := fp12PowX f2
    let fx2 := fp12PowX fx
    let fx3 := fp12PowX fx2
    let u1 := fp12Pow6 fx
    let u2 := fp12Pow6 fx2
    let u3 := fp12Pow6 fx3
    let u3_6 := fp12Pow6 u3
    let u2_2 := fp12Sqr u2
    let u2_3 := fp12Mul u2_2 u2
    let u1_2 := fp12Sqr u1
    let c := fp12Mul u3_6 (fp12Mul u2_3 u1_2)
    let c0 := fp12Mul c (fp12Mul u2_2 (fp12Mul u1 (fp12Sqr f2)))
    let y0 := fp12Conj c0
    let y1 := fp12Frob1 (fp12Mul f2 (fp12Conj c))
    let y2 := fp12Frob2 (fp12Mul f2 u2)
    let y3 := fp12Frob3 f2
    fp12Mul (fp12Mul y0 y1) (fp12Mul y2 y3)

def bn254Pairing (P : G1Aff) (Q : G2Aff) : Fp12 :=
  bn254FinalExp (bn254MillerLoop1 P Q)

def bn254MultiPairing4 (P0 P1 P2 P3 : G1Aff) (Q0 Q1 Q2 Q3 : G2Aff) : Fp12 :=
  bn254FinalExp (bn254MillerLoop4 P0 P1 P2 P3 Q0 Q1 Q2 Q3)

/-! ## Section 6: Real BN254 Groth16 Dev Setup, Prover & Verifier (Fermat Cubic Circuit)

8-constraint, 12-wire R1CS over BN254 `Fr` proving knowledge of `(x, y, z, d_inv)` such that:
- `w0 = 1`, `w1 = pub` (public instance input)
- `w2 = x`, `w3 = y`, `w4 = z`, `w5 = x^2`, `w6 = x^3`, `w7 = y^2`, `w8 = y^3`,
  `w9 = z^2`, `w10 = z^3`, `w11 = d_inv`
- Constraints (`k = 0..7`, domain `D = {1, ω, ..., ω^7}`, `ω^8 = 1`):
  0. `x * x = x^2`
  1. `x^2 * x = x^3`
  2. `y * y = y^2`
  3. `y^2 * y = y^3`
  4. `z * z = z^2`
  5. `z^2 * z = z^3`
  6. `(x^3 + y^3 - z^3) * d_inv = 1`
  7. `(x + 256*y + 65536*z) * 1 = pub`
-/

/-- Powers of the primitive 8th root of unity `ω` and `ω⁻¹` in BN254 `Fr` (Montgomery form). -/
def frOmega8Pow (k : Nat) : Limb9 :=
  let m := Nat.land k 7
  bif Nat.blt m 4 then
    bif Nat.blt m 2 then
      bif Nat.beq m 0 then frOne
      else ⟨95389641, 48390241, 300332159, 503503635, 82342134, 285411315, 99516069, 313982138, 3083408⟩
    else
      bif Nat.beq m 2 then ⟨463335748, 260486700, 175442720, 184242609, 507099171, 396110723, 361117074, 47371890, 1832658⟩
      else ⟨464268461, 201319995, 481687180, 405656272, 458932501, 120013866, 484094282, 501415006, 2094159⟩
  else
    bif Nat.blt m 6 then
      bif Nat.beq m 4 then ⟨170, 6857195, 154148293, 276840874, 182307623, 93913074, 248616249, 154230411, 2268184⟩
      else ⟨173045816, 472730686, 477458385, 164476383, 278749580, 299382989, 448291483, 463808889, 87997⟩
    else
      bif Nat.beq m 6 then ⟨341970621, 260634226, 65476912, 483737410, 390863455, 188683580, 186690478, 193548225, 1338748⟩
      else ⟨341037908, 319800931, 296103364, 262323746, 439030125, 464780437, 63713270, 276376021, 1077246⟩

def frOmega8InvPow (k : Nat) : Limb9 :=
  let m := Nat.land k 7
  bif Nat.beq m 0 then frOne else frOmega8Pow (Nat.sub 8 m)

structure FrVec8 where
  v0 : Limb9
  v1 : Limb9
  v2 : Limb9
  v3 : Limb9
  v4 : Limb9
  v5 : Limb9
  v6 : Limb9
  v7 : Limb9

structure FrVec7 where
  v0 : Limb9
  v1 : Limb9
  v2 : Limb9
  v3 : Limb9
  v4 : Limb9
  v5 : Limb9
  v6 : Limb9

/-- 12-wire witness `(w0=1, w1=pub, x, y, z, x^2, x^3, y^2, y^3, z^2, z^3, d_inv)` in Montgomery `Fr`. -/
structure FermatWitness where
  w0 : Limb9
  w1 : Limb9
  w2 : Limb9
  w3 : Limb9
  w4 : Limb9
  w5 : Limb9
  w6 : Limb9
  w7 : Limb9
  w8 : Limb9
  w9 : Limb9
  w10 : Limb9
  w11 : Limb9

/-- Genuine 256-byte BN254 Groth16 proof `(A ∈ G1, B ∈ G2, C ∈ G1)` (8 × 32-byte `Fq` coords). -/
structure Groth16Proof where
  a : G1Aff
  b : G2Aff
  c : G1Aff

/-- BN254 Groth16 Verifying Key for 1 public input (`IC_0, IC_1`). -/
structure Groth16VK where
  alphaG1 : G1Aff
  betaG2 : G2Aff
  gammaG2 : G2Aff
  deltaG2 : G2Aff
  ic0 : G1Aff
  ic1 : G1Aff

/-- Sparse BN254 Groth16 Proving Key for the 8-constraint, 12-wire Fermat cubic circuit. -/
structure Groth16PK where
  alphaG1 : G1Aff
  betaG1 : G1Aff
  betaG2 : G2Aff
  deltaG1 : G1Aff
  deltaG2 : G2Aff
  -- Nonzero `A_query[i] = [u_i(τ)]G1` for `i ∈ {2..10}`
  a2 : G1Aff
  a3 : G1Aff
  a4 : G1Aff
  a5 : G1Aff
  a6 : G1Aff
  a7 : G1Aff
  a8 : G1Aff
  a9 : G1Aff
  a10 : G1Aff
  -- Nonzero `B_g1_query[i] = [v_i(τ)]G1` for `i ∈ {0, 2, 3, 4, 11}`
  b1_0 : G1Aff
  b1_2 : G1Aff
  b1_3 : G1Aff
  b1_4 : G1Aff
  b1_11 : G1Aff
  -- Nonzero `B_g2_query[i] = [v_i(τ)]G2` for `i ∈ {0, 2, 3, 4, 11}`
  b2_0 : G2Aff
  b2_2 : G2Aff
  b2_3 : G2Aff
  b2_4 : G2Aff
  b2_11 : G2Aff
  -- Private wire `L_query[i] = [(β*u_i + α*v_i + w_i)/δ]G1` for `i ∈ {2..11}`
  l2 : G1Aff
  l3 : G1Aff
  l4 : G1Aff
  l5 : G1Aff
  l6 : G1Aff
  l7 : G1Aff
  l8 : G1Aff
  l9 : G1Aff
  l10 : G1Aff
  l11 : G1Aff
  -- Quotient `H_query[j] = [τ^j * (τ^8 - 1) / δ]G1` for `j ∈ {0..6}`
  h0 : G1Aff
  h1 : G1Aff
  h2 : G1Aff
  h3 : G1Aff
  h4 : G1Aff
  h5 : G1Aff
  h6 : G1Aff

structure Groth16Setup where
  pk : Groth16PK
  vk : Groth16VK

def frVec8Get (v : FrVec8) (idx : Nat) : Limb9 :=
  bif Nat.blt idx 4 then
    bif Nat.blt idx 2 then (bif Nat.beq idx 0 then v.v0 else v.v1)
    else (bif Nat.beq idx 2 then v.v2 else v.v3)
  else
    bif Nat.blt idx 6 then (bif Nat.beq idx 4 then v.v4 else v.v5)
    else (bif Nat.beq idx 6 then v.v6 else v.v7)

/-- Evaluate `L_k(τ) = ω^k * (τ^8 - 1) / (8 * (τ - ω^k))`. -/
def evalLagrange1 (tau tTau : Limb9) (k : Nat) : Limb9 :=
  let wk := frOmega8Pow k
  let num := frMul wk tTau
  let den := frSub tau wk
  frMul (frMul num frInv8) (frInv den)

def evalLagrange8 (tau tTau : Limb9) : FrVec8 :=
  { v0 := evalLagrange1 tau tTau 0
    v1 := evalLagrange1 tau tTau 1
    v2 := evalLagrange1 tau tTau 2
    v3 := evalLagrange1 tau tTau 3
    v4 := evalLagrange1 tau tTau 4
    v5 := evalLagrange1 tau tTau 5
    v6 := evalLagrange1 tau tTau 6
    v7 := evalLagrange1 tau tTau 7 }

/-- Compute `(β * u + α * v + w) * scale` in `Fr`. -/
def qapLinComb (alpha beta scale u v w : Limb9) : Limb9 :=
  let t1 := frAdd (frMul beta u) (frMul alpha v)
  frMul (frAdd t1 w) scale

/-- Construct genuine BN254 Groth16 `(ProvingKey, VerifyingKey)` from deterministic dev trapdoor
`(τ, α, β, γ, δ)` in Montgomery `Fr` (no trusted setup ceremony). -/
def groth16SetupDev (tau alpha beta gamma delta : Limb9) : Groth16Setup :=
  let tau2 := frSqr tau
  let tau4 := frSqr tau2
  let tau8 := frSqr tau4
  let tTau := frSub tau8 frOne
  let gamInv := frInv gamma
  let delInv := frInv delta
  let L := evalLagrange8 tau tTau
  let c256 := frOfNat 256
  let c65536 := frOfNat 65536
  -- Wire evaluations at τ:
  let u2 := frAdd L.v0 L.v7
  let u3 := frAdd L.v2 (frMul c256 L.v7)
  let u4 := frAdd L.v4 (frMul c65536 L.v7)
  let u10 := frNeg L.v6
  let v2 := frAdd L.v0 L.v1
  let v3 := frAdd L.v2 L.v3
  let v4 := frAdd L.v4 L.v5
  -- Common group elements:
  let alphaG1 := g1Mul alpha g1Gen
  let betaG1 := g1Mul beta g1Gen
  let betaG2 := g2Mul beta g2Gen
  let gammaG2 := g2Mul gamma g2Gen
  let deltaG1 := g1Mul delta g1Gen
  let deltaG2 := g2Mul delta g2Gen
  -- VK public IC elements:
  let ic0 := g1Mul (qapLinComb alpha beta gamInv limb9Zero L.v7 L.v6) g1Gen
  let ic1 := g1Mul (qapLinComb alpha beta gamInv limb9Zero limb9Zero L.v7) g1Gen
  -- Private wire L_query[2..11]:
  let l2 := g1Mul (qapLinComb alpha beta delInv u2 v2 limb9Zero) g1Gen
  let l3 := g1Mul (qapLinComb alpha beta delInv u3 v3 limb9Zero) g1Gen
  let l4 := g1Mul (qapLinComb alpha beta delInv u4 v4 limb9Zero) g1Gen
  let l5 := g1Mul (qapLinComb alpha beta delInv L.v1 limb9Zero L.v0) g1Gen
  let l6 := g1Mul (qapLinComb alpha beta delInv L.v6 limb9Zero L.v1) g1Gen
  let l7 := g1Mul (qapLinComb alpha beta delInv L.v3 limb9Zero L.v2) g1Gen
  let l8 := g1Mul (qapLinComb alpha beta delInv L.v6 limb9Zero L.v3) g1Gen
  let l9 := g1Mul (qapLinComb alpha beta delInv L.v5 limb9Zero L.v4) g1Gen
  let l10 := g1Mul (qapLinComb alpha beta delInv u10 limb9Zero L.v5) g1Gen
  let l11 := g1Mul (qapLinComb alpha beta delInv limb9Zero L.v6 limb9Zero) g1Gen
  -- Quotient H_query[0..6]:
  let hs0 := frMul tTau delInv
  let hs1 := frMul hs0 tau
  let hs2 := frMul hs1 tau
  let hs3 := frMul hs2 tau
  let hs4 := frMul hs3 tau
  let hs5 := frMul hs4 tau
  let hs6 := frMul hs5 tau
  let vk : Groth16VK := { alphaG1, betaG2, gammaG2, deltaG2, ic0, ic1 }
  let pk : Groth16PK :=
    { alphaG1, betaG1, betaG2, deltaG1, deltaG2
      a2 := g1Mul u2 g1Gen
      a3 := g1Mul u3 g1Gen
      a4 := g1Mul u4 g1Gen
      a5 := g1Mul L.v1 g1Gen
      a6 := g1Mul L.v6 g1Gen
      a7 := g1Mul L.v3 g1Gen
      a8 := g1Mul L.v6 g1Gen
      a9 := g1Mul L.v5 g1Gen
      a10 := g1Mul u10 g1Gen
      b1_0 := g1Mul L.v7 g1Gen
      b1_2 := g1Mul v2 g1Gen
      b1_3 := g1Mul v3 g1Gen
      b1_4 := g1Mul v4 g1Gen
      b1_11 := g1Mul L.v6 g1Gen
      b2_0 := g2Mul L.v7 g2Gen
      b2_2 := g2Mul v2 g2Gen
      b2_3 := g2Mul v3 g2Gen
      b2_4 := g2Mul v4 g2Gen
      b2_11 := g2Mul L.v6 g2Gen
      l2, l3, l4, l5, l6, l7, l8, l9, l10, l11
      h0 := g1Mul hs0 g1Gen
      h1 := g1Mul hs1 g1Gen
      h2 := g1Mul hs2 g1Gen
      h3 := g1Mul hs3 g1Gen
      h4 := g1Mul hs4 g1Gen
      h5 := g1Mul hs5 g1Gen
      h6 := g1Mul hs6 g1Gen }
  { pk, vk }

/-- Compute one coefficient `j` of the 8-point inverse DFT `(1/8) * Σ_{k=0}^7 ev[k] * ω^(-j*k)`. -/
def idft8CoeffLoop (ev : FrVec8) (j : Nat) : Nat → Nat → Limb9 → Limb9
  | 0, _, acc => frMul acc frInv8
  | fuel + 1, k, acc =>
    let term := frMul (frVec8Get ev k) (frOmega8InvPow (Nat.mul j k))
    idft8CoeffLoop ev j fuel (Nat.add k 1) (frAdd acc term)

def idft8 (ev : FrVec8) : FrVec8 :=
  { v0 := idft8CoeffLoop ev 0 8 0 limb9Zero
    v1 := idft8CoeffLoop ev 1 8 0 limb9Zero
    v2 := idft8CoeffLoop ev 2 8 0 limb9Zero
    v3 := idft8CoeffLoop ev 3 8 0 limb9Zero
    v4 := idft8CoeffLoop ev 4 8 0 limb9Zero
    v5 := idft8CoeffLoop ev 5 8 0 limb9Zero
    v6 := idft8CoeffLoop ev 6 8 0 limb9Zero
    v7 := idft8CoeffLoop ev 7 8 0 limb9Zero }

/-- High coefficient `d = j + 8` of `A(X) * B(X)` (equals `H_j` for `t(X) = X^8 - 1`). -/
def polyProdHighCoeff (a b : FrVec8) (d : Nat) : Nat → Nat → Limb9 → Limb9
  | 0, _, acc => acc
  | fuel + 1, pIdx, acc =>
    let qIdx := Nat.sub d pIdx
    let term :=
      bif Nat.ble pIdx d then
        bif Nat.blt qIdx 8 then frMul (frVec8Get a pIdx) (frVec8Get b qIdx)
        else limb9Zero
      else limb9Zero
    polyProdHighCoeff a b d fuel (Nat.add pIdx 1) (frAdd acc term)

/-- Compute exact QAP quotient coefficients `H_0..H_6` of `(A(X)B(X) - C(X)) / (X^8 - 1)`. -/
def computeQapH (w : FermatWitness) : FrVec7 :=
  let diff := frSub (frAdd w.w6 w.w8) w.w10
  let linPub := frAdd w.w2 (frAdd (frMul (frOfNat 256) w.w3) (frMul (frOfNat 65536) w.w4))
  let aEv : FrVec8 := { v0 := w.w2, v1 := w.w5, v2 := w.w3, v3 := w.w7, v4 := w.w4, v5 := w.w9, v6 := diff, v7 := linPub }
  let bEv : FrVec8 := { v0 := w.w2, v1 := w.w2, v2 := w.w3, v3 := w.w3, v4 := w.w4, v5 := w.w4, v6 := w.w11, v7 := w.w0 }
  let aC := idft8 aEv
  let bC := idft8 bEv
  { v0 := polyProdHighCoeff aC bC 8 8 0 limb9Zero
    v1 := polyProdHighCoeff aC bC 9 8 0 limb9Zero
    v2 := polyProdHighCoeff aC bC 10 8 0 limb9Zero
    v3 := polyProdHighCoeff aC bC 11 8 0 limb9Zero
    v4 := polyProdHighCoeff aC bC 12 8 0 limb9Zero
    v5 := polyProdHighCoeff aC bC 13 8 0 limb9Zero
    v6 := polyProdHighCoeff aC bC 14 8 0 limb9Zero }

/-- Construct valid Fermat cubic witness for `(x, y, z)` (`x^3 + y^3 ≠ z^3` in `Fr`). -/
def mkFermatWitness (xNat yNat zNat : Nat) : FermatWitness :=
  let x := frOfNat xNat
  let y := frOfNat yNat
  let z := frOfNat zNat
  let x2 := frSqr x
  let x3 := frMul x2 x
  let y2 := frSqr y
  let y3 := frMul y2 y
  let z2 := frSqr z
  let z3 := frMul z2 z
  let diff := frSub (frAdd x3 y3) z3
  let dInv := frInv diff
  let pub := frAdd x (frAdd (frMul (frOfNat 256) y) (frMul (frOfNat 65536) z))
  { w0 := frOne, w1 := pub, w2 := x, w3 := y, w4 := z,
    w5 := x2, w6 := x3, w7 := y2, w8 := y3, w9 := z2, w10 := z3, w11 := dInv }

def proveA (pk : Groth16PK) (w : FermatWitness) (rBlind : Limb9) : G1Aff :=
  let acc0 := g1ToJac pk.alphaG1
  let acc1 := g1MsmAcc acc0 w.w2 pk.a2
  let acc2 := g1MsmAcc acc1 w.w3 pk.a3
  let acc3 := g1MsmAcc acc2 w.w4 pk.a4
  let acc4 := g1MsmAcc acc3 w.w5 pk.a5
  let acc5 := g1MsmAcc acc4 w.w6 pk.a6
  let acc6 := g1MsmAcc acc5 w.w7 pk.a7
  let acc7 := g1MsmAcc acc6 w.w8 pk.a8
  let acc8 := g1MsmAcc acc7 w.w9 pk.a9
  let acc9 := g1MsmAcc acc8 w.w10 pk.a10
  let acc10 := g1MsmAcc acc9 rBlind pk.deltaG1
  g1ToAff acc10

def proveB1 (pk : Groth16PK) (w : FermatWitness) (sBlind : Limb9) : G1Aff :=
  let acc0 := g1ToJac pk.betaG1
  let acc1 := g1MsmAcc acc0 w.w0 pk.b1_0
  let acc2 := g1MsmAcc acc1 w.w2 pk.b1_2
  let acc3 := g1MsmAcc acc2 w.w3 pk.b1_3
  let acc4 := g1MsmAcc acc3 w.w4 pk.b1_4
  let acc5 := g1MsmAcc acc4 w.w11 pk.b1_11
  let acc6 := g1MsmAcc acc5 sBlind pk.deltaG1
  g1ToAff acc6

def proveB2 (pk : Groth16PK) (w : FermatWitness) (sBlind : Limb9) : G2Aff :=
  let acc0 := g2ToJac pk.betaG2
  let acc1 := g2MsmAcc acc0 w.w0 pk.b2_0
  let acc2 := g2MsmAcc acc1 w.w2 pk.b2_2
  let acc3 := g2MsmAcc acc2 w.w3 pk.b2_3
  let acc4 := g2MsmAcc acc3 w.w4 pk.b2_4
  let acc5 := g2MsmAcc acc4 w.w11 pk.b2_11
  let acc6 := g2MsmAcc acc5 sBlind pk.deltaG2
  g2ToAff acc6

def proveCL (pk : Groth16PK) (w : FermatWitness) : G1Jac :=
  let a0 := g1MsmAcc g1JacInf w.w2 pk.l2
  let a1 := g1MsmAcc a0 w.w3 pk.l3
  let a2 := g1MsmAcc a1 w.w4 pk.l4
  let a3 := g1MsmAcc a2 w.w5 pk.l5
  let a4 := g1MsmAcc a3 w.w6 pk.l6
  let a5 := g1MsmAcc a4 w.w7 pk.l7
  let a6 := g1MsmAcc a5 w.w8 pk.l8
  let a7 := g1MsmAcc a6 w.w9 pk.l9
  let a8 := g1MsmAcc a7 w.w10 pk.l10
  g1MsmAcc a8 w.w11 pk.l11

def proveCH (pk : Groth16PK) (h : FrVec7) (acc : G1Jac) : G1Jac :=
  let a0 := g1MsmAcc acc h.v0 pk.h0
  let a1 := g1MsmAcc a0 h.v1 pk.h1
  let a2 := g1MsmAcc a1 h.v2 pk.h2
  let a3 := g1MsmAcc a2 h.v3 pk.h3
  let a4 := g1MsmAcc a3 h.v4 pk.h4
  let a5 := g1MsmAcc a4 h.v5 pk.h5
  g1MsmAcc a5 h.v6 pk.h6

/-- Compute genuine 256-byte BN254 Groth16 proof `(A, B, C)` with ZK blinding `(rBlind, sBlind)`. -/
def groth16Prove (pk : Groth16PK) (w : FermatWitness) (rBlind sBlind : Limb9) : Groth16Proof :=
  let h := computeQapH w
  let proofA := proveA pk w rBlind
  let proofB1 := proveB1 pk w sBlind
  let proofB2 := proveB2 pk w sBlind
  let cL := proveCL pk w
  let cLH := proveCH pk h cL
  let cS := g1MsmAcc cLH sBlind proofA
  let cSR := g1MsmAcc cS rBlind proofB1
  let rs := frMul rBlind sBlind
  let cFinal := g1MsmAcc cSR rs (g1Neg pk.deltaG1)
  { a := proofA, b := proofB2, c := g1ToAff cFinal }

/-- **Full Real 254-bit BN254 Groth16 Verifier**:
1. Checks canonical raw public input `pubRaw < r`.
2. Validates `proof.a ∈ G1`, `proof.b ∈ G2` (on twist + prime-order subgroup `ψ(B) = [6x^2]B`),
   and `proof.c ∈ G1`.
3. Computes `vk_x = IC_0 + [pubRaw]IC_1`.
4. Verifies exact 4-pairing Groth16 equation:
   `e(A, B) · e(-α, β) · e(-vk_x, γ) · e(-C, δ) = 1`. -/
def groth16Verify (vk : Groth16VK) (pubRaw : Limb9) (proof : Groth16Proof) : Bool :=
  bif frCanonical pubRaw then
    bif g1OnCurve proof.a then
      bif g2OnCurve proof.b then
        bif g2InSubgroup proof.b then
          bif g1OnCurve proof.c then
            let vkX := g1ToAff (g1JacAdd (g1ToJac vk.ic0) (g1MulRawJac pubRaw vk.ic1))
            let res := bn254MultiPairing4
              proof.a (g1Neg vk.alphaG1) (g1Neg vkX) (g1Neg proof.c)
              proof.b vk.betaG2 vk.gammaG2 vk.deltaG2
            fp12IsOne res
          else false
        else false
      else false
    else false
  else false

/-- **Full Real 254-bit BN254 Groth16 Verifier (2 Public Inputs)**:
1. Checks canonical raw public inputs `pub0Raw < r`, `pub1Raw < r`.
2. Validates `proof.a ∈ G1`, `proof.b ∈ G2` (on twist + prime-order subgroup `ψ(B) = [6x^2]B`),
   and `proof.c ∈ G1`.
3. Computes `vk_x = IC_0 + [pub0Raw]IC_1 + [pub1Raw]IC_2`.
4. Verifies exact 4-pairing Groth16 equation:
   `e(A, B) · e(-α, β) · e(-vk_x, γ) · e(-C, δ) = 1`. -/
structure Groth16VK2 where
  alphaG1 : G1Aff
  betaG2 : G2Aff
  gammaG2 : G2Aff
  deltaG2 : G2Aff
  ic0 : G1Aff
  ic1 : G1Aff
  ic2 : G1Aff

def groth16Verify2 (vk : Groth16VK2) (pub0Raw pub1Raw : Limb9) (proof : Groth16Proof) : Bool :=
  bif frCanonical pub0Raw then
    bif frCanonical pub1Raw then
      bif g1OnCurve proof.a then
        bif g2OnCurve proof.b then
          bif g2InSubgroup proof.b then
            bif g1OnCurve proof.c then
              let t0 := g1JacAdd (g1ToJac vk.ic0) (g1MulRawJac pub0Raw vk.ic1)
              let vkX := g1ToAff (g1JacAdd t0 (g1MulRawJac pub1Raw vk.ic2))
              let res := bn254MultiPairing4
                proof.a (g1Neg vk.alphaG1) (g1Neg vkX) (g1Neg proof.c)
                proof.b vk.betaG2 vk.gammaG2 vk.deltaG2
              fp12IsOne res
            else false
          else false
        else false
      else false
    else false
  else false

/-! ### Cross-Verification Vector: Rust `ark-bn254` & EVM-Verified 256-Byte Groth16 Proof

Exact 256-byte BN254 Groth16 Fermat Margin Note proof (`x=3, y=4, z=5`, `r=1637, s=1670`)
independently generated by the Rust `ark-bn254` prover and verified on EVM (`199,785` gas
via `IxGroth16Verifier.sol`), encoded here in certified `< 2^29` Montgomery limbs. -/

def w6bPub0Raw : Limb9 := ⟨413763275, 229355926, 48346680, 268142114, 682, 0, 0, 0, 0⟩
def w6bPub0BadRaw : Limb9 := ⟨413763276, 229355926, 48346680, 268142114, 682, 0, 0, 0, 0⟩
def w6bPub1Raw : Limb9 := ⟨517546357, 503283045, 249916072, 200697905, 1327, 0, 0, 0, 0⟩

def w6bProofA : G1Aff :=
  { x := ⟨459980383, 97959318, 262271242, 490310277, 534858130, 159364273, 517656625, 507637394, 2586922⟩
    y := ⟨402553907, 268256141, 492187386, 482310074, 113028291, 50705807, 81365381, 242713160, 691252⟩
    isInf := 0 }

def w6bProofB : G2Aff :=
  { x :=
      { c0 := ⟨409057264, 182398575, 348207807, 243999112, 198054070, 462065454, 452012422, 64595224, 2777697⟩
        c1 := ⟨513284826, 56477048, 373592514, 492204240, 517345618, 214822201, 209953265, 393217624, 265755⟩ }
    y :=
      { c0 := ⟨123616189, 386107168, 423516152, 322183346, 307451304, 159610915, 39561918, 156544991, 1730148⟩
        c1 := ⟨33339310, 441190763, 85748627, 316347986, 446748605, 285518927, 250580831, 297400358, 2855428⟩ }
    isInf := 0 }

def w6bProofC : G1Aff :=
  { x := ⟨159380022, 528532520, 143099670, 399160389, 432078839, 381106743, 294552366, 47806299, 1280502⟩
    y := ⟨227274133, 536359696, 189618417, 122942003, 281224988, 230367677, 400907483, 24117746, 2407616⟩
    isInf := 0 }

def w6bVkAlpha : G1Aff :=
  { x := ⟨446815397, 463944461, 363178572, 104490020, 34354839, 464738784, 457479436, 194961177, 846971⟩
    y := ⟨90811995, 317289686, 96483965, 244914687, 371078230, 53138013, 1602639, 301167015, 1360197⟩
    isInf := 0 }

def w6bVkBeta : G2Aff :=
  { x :=
      { c0 := ⟨220605068, 523811198, 164431080, 352778668, 86070107, 517972145, 244144195, 148098875, 2413156⟩
        c1 := ⟨184571651, 237280057, 123750939, 435153781, 445977719, 227442912, 348605961, 458062563, 3134478⟩ }
    y :=
      { c0 := ⟨136074006, 50030543, 234864404, 224075119, 436271341, 284506975, 353108502, 433251999, 2471529⟩
        c1 := ⟨181509945, 105291286, 401181212, 258034255, 390262537, 279569515, 486217996, 119125822, 1769190⟩ }
    isInf := 0 }

def w6bVkGamma : G2Aff :=
  { x :=
      { c0 := ⟨397288544, 403763488, 276845037, 277602821, 370965334, 409020185, 477214223, 416220381, 1590041⟩
        c1 := ⟨410858507, 267732481, 413000013, 163720002, 482417498, 200630308, 234492411, 87498025, 2459256⟩ }
    y :=
      { c0 := ⟨377362442, 432084880, 80730368, 161164641, 13037407, 81090282, 262175952, 82829580, 78280⟩
        c1 := ⟨297100199, 174215131, 43849879, 352531656, 450140603, 108604507, 294095936, 400131128, 1402102⟩ }
    isInf := 0 }

def w6bVkDelta : G2Aff :=
  { x :=
      { c0 := ⟨322228990, 128200013, 326271065, 20267361, 489978471, 350530144, 501048790, 169053415, 1722961⟩
        c1 := ⟨188154238, 472920091, 326172860, 381405734, 404699355, 136538461, 311313601, 106709828, 573423⟩ }
    y :=
      { c0 := ⟨461712405, 112991751, 124054477, 75773941, 390891708, 531911138, 475792119, 41335336, 1444537⟩
        c1 := ⟨107119278, 189670275, 487271440, 256480707, 310227439, 441148566, 144776394, 349292689, 438020⟩ }
    isInf := 0 }

def w6bVkIc0 : G1Aff :=
  { x := ⟨352300943, 176610291, 380892680, 74057794, 158315299, 407796951, 178126912, 343797645, 1295676⟩
    y := ⟨81759342, 315431855, 232447325, 68159225, 97057817, 403705484, 367576376, 352206569, 938802⟩
    isInf := 0 }

def w6bVkIc1 : G1Aff :=
  { x := ⟨420838749, 184796678, 407497543, 38197964, 247764358, 369890264, 104245958, 182870096, 2211561⟩
    y := ⟨307212089, 503190531, 291572966, 100896715, 525947836, 289982196, 291501126, 101290734, 877903⟩
    isInf := 0 }

def w6bVkIc2 : G1Aff :=
  { x := ⟨450482467, 99320376, 253254444, 408187175, 154355520, 284150121, 265377768, 236159165, 2230889⟩
    y := ⟨497926822, 352841880, 434111482, 66210054, 448331029, 101457528, 192267177, 258044099, 1989370⟩
    isInf := 0 }

def w6bVK : Groth16VK2 :=
  { alphaG1 := w6bVkAlpha, betaG2 := w6bVkBeta, gammaG2 := w6bVkGamma, deltaG2 := w6bVkDelta
    ic0 := w6bVkIc0, ic1 := w6bVkIc1, ic2 := w6bVkIc2 }

def w6bProof : Groth16Proof :=
  { a := w6bProofA, b := w6bProofB, c := w6bProofC }

/-- Cross-verify the live Rust `ark-bn254` + EVM (`199,785` gas) 256-byte Fermat Margin Note proof:
- `mode = 5`: valid 256-byte proof + public inputs → `true`
- `mode = 6`: tampered `pub0 + 1` → `false`
- `mode = 7`: tampered `proof.a + G1` → `false` -/
def runW6bCrossVerifyMode (mode : Nat) : Bool :=
  bif Nat.beq mode 5 then
    groth16Verify2 w6bVK w6bPub0Raw w6bPub1Raw w6bProof
  else bif Nat.beq mode 6 then
    groth16Verify2 w6bVK w6bPub0BadRaw w6bPub1Raw w6bProof
  else
    let badProof : Groth16Proof := { w6bProof with a := g1AddAff w6bProof.a g1Gen }
    groth16Verify2 w6bVK w6bPub0Raw w6bPub1Raw badProof

/-! ## Section 7: Standalone Certified `IxCC` x86-64 Entrypoints (`--exe` & `--exe --machine`) -/

/-- Run live dev setup + Fermat `(3, 4, 5)` prove + mode-selected verify check. -/
def runGroth16Mode (mode : Nat) : Bool :=
  let tau := frOfNat 12345678901234567
  let alpha := frOfNat 98765432109876543
  let beta := frOfNat 19283746556473829
  let gamma := frOfNat 55566677788899911
  let delta := frOfNat 31415926535897932
  let rBlind := frOfNat 27182818284590452
  let sBlind := frOfNat 16180339887498948
  let setup := groth16SetupDev tau alpha beta gamma delta
  let w := mkFermatWitness 3 4 5
  let proof := groth16Prove setup.pk w rBlind sBlind
  let pubRaw := frFromMont w.w1
  bif Nat.beq mode 0 then
    groth16Verify setup.vk pubRaw proof
  else bif Nat.beq mode 1 then
    let badPub := frFromMont (frAdd w.w1 frOne)
    groth16Verify setup.vk badPub proof
  else bif Nat.beq mode 2 then
    let badProof : Groth16Proof := { proof with a := g1AddAff proof.a g1Gen }
    groth16Verify setup.vk pubRaw badProof
  else
    let badProof : Groth16Proof := { proof with c := g1AddAff proof.c g1Gen }
    groth16Verify setup.vk pubRaw badProof

/-- Standalone BN254 pairing bilinearity & non-degeneracy check:
`e([7]G1, [11]G2) ≠ 1` and `e([7]G1, [11]G2) · e([-77]G1, G2) = 1`. -/
def runBilinearityMode : Bool :=
  let p7 := g1Mul (frOfNat 7) g1Gen
  let q11 := g2Mul (frOfNat 11) g2Gen
  let pNeg77 := g1Neg (g1Mul (frOfNat 77) g1Gen)
  let single := bn254Pairing p7 q11
  let okNonDeg := bif fp12IsOne single then false else true
  let prod := bn254MultiPairing4 p7 pNeg77 g1Inf g1Inf q11 g2Gen g2Gen g2Gen
  bif okNonDeg then fp12IsOne prod else false

/-- **Standalone Certified `IxCC` x86-64 Entrypoint (`ixcc compile --exe`)**:
- `mode = 0`: valid real 254-bit BN254 Groth16 dev setup + prove + verify on Fermat `(3,4,5)` → `1`
- `mode = 1`: tampered public input (`pub + 1`) → `0` (rejected)
- `mode = 2`: tampered proof `A` (`A + G1`) → `0` (rejected)
- `mode = 3`: tampered proof `C` (`C + G1`) → `0` (rejected)
- `mode = 4`: standalone BN254 pairing bilinearity `e([7]G1,[11]G2)·e([-77]G1,G2) = 1` → `1`
- `mode = 5`: cross-verify live Rust `ark-bn254` / EVM-verified 256-byte Groth16 proof → `1`
- `mode = 6`: cross-verify tampered `pub0 + 1` on Rust/EVM proof → `0` (rejected)
- `mode = 7`: cross-verify tampered `proof.a + G1` on Rust/EVM proof → `0` (rejected) -/
def groth16X86Main (mode : Nat) : Nat :=
  bif Nat.blt mode 4 then
    bif runGroth16Mode mode then 1 else 0
  else bif Nat.beq mode 4 then
    bif runBilinearityMode then 1 else 0
  else bif Nat.blt mode 8 then
    bif runW6bCrossVerifyMode mode then 1 else 0
  else 0

/-! ### Self-Contained `IxccExe` Platform-v0 Machine Wrapper (`ixcc compile --exe --machine`) -/

def machResult (s r : Nat) : Nat := Nat.add (Nat.mul s 2048) r
def machArg : Nat := 0
def machOut (b : Nat) : Nat := Nat.add 1 (Nat.mul 8 b)
def machErr (b : Nat) : Nat := Nat.add 2 (Nat.mul 8 b)
def machExit (c : Nat) : Nat := Nat.add 3 (Nat.mul 8 c)
def machLimit : Nat := 281474976710656

def machParse (acc seen : Nat) : Nat := Nat.add (Nat.mul (Nat.add (Nat.mul acc 2) seen) 4) 1
def machRender (p : Nat) : Nat := Nat.add (Nat.mul p 4) 2

def machReady (s e : Nat) : Bool :=
  bif Nat.beq (Nat.mod s 4) 1 then
    bif Nat.beq e 256 then
      bif Nat.beq (Nat.mod (Nat.div s 4) 2) 1 then Nat.blt (Nat.div s 8) machLimit else false
    else false
  else false

def machFinishBit (r : Nat) : Nat :=
  machResult (machRender 1) (machOut (Nat.add 48 (Nat.land r 1)))

def machStep (s e : Nat) : Nat :=
  let p := Nat.div s 4
  let phase := Nat.mod s 4
  let a := bif Nat.beq e 1 then machResult (machParse 0 0) machArg else machResult 0 (machExit 2)
  let n := Nat.add (Nat.mul (Nat.div p 2) 10) (Nat.sub e 48)
  let digit := bif Nat.ble 48 e then Nat.ble e 57 else false
  let b :=
    bif Nat.blt e 256 then
      bif digit then
        machResult (machParse (bif Nat.blt n machLimit then n else machLimit) 1) machArg
      else machResult 0 (machExit 3)
    else machResult 0 (machExit 3)
  let c :=
    bif Nat.beq e 0 then
      bif Nat.beq p 0 then machResult 0 (machExit 0)
      else machResult (machRender 0) (machOut 10)
    else machResult 0 (machExit 74)
  bif Nat.beq phase 0 then a
  else bif Nat.beq phase 1 then b
  else c

/-- **`IxccExe`-Protocol Numeric State Machine Entrypoint (`ixcc compile --exe --machine`)**:
parses one decimal CLI argument in compiled Lean, executes `groth16X86Main`, writes `'0'`/`'1'` +
newline to stdout, and exits `0` (zero trusted parsing/rendering shell!). -/
def groth16MachineStep (s e : Nat) : Nat :=
  bif machReady s e then machFinishBit (groth16X86Main (Nat.div s 8))
  else machStep s e

/-! ## Section 8: Cryptographic Ground-Truth `#guard` Verification Suite -/

section Tests

private def limb9ToNat (a : Limb9) : Nat :=
  a.l0 + (2 ^ 29) * (a.l1 + (2 ^ 29) * (a.l2 + (2 ^ 29) * (a.l3 +
    (2 ^ 29) * (a.l4 + (2 ^ 29) * (a.l5 + (2 ^ 29) * (a.l6 +
      (2 ^ 29) * (a.l7 + (2 ^ 29) * a.l8)))))))

private def fqToNat (a : Limb9) : Nat := limb9ToNat (fqFromMont a)
private def frToNat (a : Limb9) : Nat := limb9ToNat (frFromMont a)

private def bn254P : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

private def bn254R : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- 1. BN254 Fq & Fr Montgomery field laws
#guard limb9ToNat fqP == bn254P
#guard limb9ToNat frR == bn254R
#guard fqToNat fqOne == 1
#guard fqToNat fqTwo == 2
#guard fqToNat fqThree == 3
#guard fqToNat (fqMul fqTwo fqTwoInv) == 1
#guard fqToNat (fqMul (fqOfNat 123456789) (fqInv (fqOfNat 123456789))) == 1
#guard frToNat (frMul (frOfNat 987654321) (frInv (frOfNat 987654321))) == 1
#guard frToNat (frSub (frOfNat 10) (frOfNat 25)) == bn254R - 15
#guard fqToNat (fqSub (fqOfNat 7) (fqOfNat 19)) == bn254P - 12
#guard frToNat (frPow (frOmega8Pow 1) (limb9OfNat 8)) == 1
#guard frToNat (frPow (frOmega8Pow 1) (limb9OfNat 4)) == bn254R - 1

-- 2. Fp2, Fp6, Fp12 tower arithmetic & Frobenius laws
private def sampleFp12 : Fp12 :=
  { c0 := { c0 := { c0 := fqOfNat 2, c1 := fqOfNat 3 }
            c1 := { c0 := fqOfNat 5, c1 := fqOfNat 7 }
            c2 := { c0 := fqOfNat 11, c1 := fqOfNat 13 } }
    c1 := { c0 := { c0 := fqOfNat 17, c1 := fqOfNat 19 }
            c1 := { c0 := fqOfNat 23, c1 := fqOfNat 29 }
            c2 := { c0 := fqOfNat 31, c1 := fqOfNat 37 } } }

private def sampleFp12B : Fp12 :=
  { c0 := { c0 := { c0 := fqOfNat 41, c1 := fqOfNat 43 }
            c1 := { c0 := fqOfNat 47, c1 := fqOfNat 53 }
            c2 := { c0 := fqOfNat 59, c1 := fqOfNat 61 } }
    c1 := { c0 := { c0 := fqOfNat 67, c1 := fqOfNat 71 }
            c1 := { c0 := fqOfNat 73, c1 := fqOfNat 79 }
            c2 := { c0 := fqOfNat 83, c1 := fqOfNat 89 } } }

#guard fp12IsOne (fp12Mul sampleFp12 (fp12Inv sampleFp12)) == true
#guard fp12Eq (fp12Sqr sampleFp12) (fp12Mul sampleFp12 sampleFp12) == true
#guard fp12Eq (fp12Frob3 sampleFp12) (fp12Frob1 (fp12Frob2 sampleFp12)) == true
#guard fp12Eq (fp12Frob3 (fp12Frob3 sampleFp12)) (fp12Conj sampleFp12) == true
#guard fp12Eq (fp12Frob1 (fp12Mul sampleFp12 sampleFp12B))
              (fp12Mul (fp12Frob1 sampleFp12) (fp12Frob1 sampleFp12B)) == true
#guard fp12Eq (fp12Frob2 (fp12Mul sampleFp12 sampleFp12B))
              (fp12Mul (fp12Frob2 sampleFp12) (fp12Frob2 sampleFp12B)) == true

-- 3. Curve G1, G2 on-curve & prime-order subgroup checks
#guard g1OnCurve g1Gen == true
#guard g2OnCurve g2Gen == true
#guard g2InSubgroup g2Gen == true
#guard g1OnCurve { x := fqOne, y := fqThree, isInf := 0 } == false
#guard g2OnCurve { x := bn254G2GenX, y := fp2Add bn254G2GenY fp2One, isInf := 0 } == false

-- 4. Exact bit-for-bit match with `ark-bn254 0.5.0` `Bn254::multi_miller_loop([G1], [G2])`
private def fp12Coords (f : Fp12) : List Nat :=
  [ fqToNat f.c0.c0.c0, fqToNat f.c0.c0.c1,
    fqToNat f.c0.c1.c0, fqToNat f.c0.c1.c1,
    fqToNat f.c0.c2.c0, fqToNat f.c0.c2.c1,
    fqToNat f.c1.c0.c0, fqToNat f.c1.c0.c1,
    fqToNat f.c1.c1.c0, fqToNat f.c1.c1.c1,
    fqToNat f.c1.c2.c0, fqToNat f.c1.c2.c1 ]

private def arkBn254MlGenCoords : List Nat :=
  [ 7839923261617885508987657002451344696432320114614434307852847339179413313131,
    12717477091189878191750757105631642814394974815225599372235521871186456047185,
    4495351289242968368489443409990120909266958997534941096233383580904652570968,
    18260482371840806269258274155140294304605237478103224910052874688449597450291,
    1279265302254125767302656014297491966433341127593655239766626748952970630698,
    1388121835306334572356808027484473543889687237652069077660202994440235528548,
    19852083908929483692825705709699891513888357475021762293723964644225448489959,
    19585424606244653125874350451545466165975231973942042158315113677433890127948,
    16200718250890395597511978989568765255542844217061356566590841434924851848883,
    18471953788557918301135801699439586176981449163871144189161405096649508064561,
    17475922307275585000629274569182183704942867998604624902575839562555121108505,
    4598062826746979912844329033999650324061844598778337136104700815112494089718 ]

#guard fp12Coords (bn254MillerLoop1 g1Gen g2Gen) == arkBn254MlGenCoords

-- 5. Full exact BN254 optimal Ate pairing bilinearity: e([7]G1, [11]G2) == e([77]G1, G2) ≠ 1
#guard
  let e1 := bn254Pairing (g1Mul (frOfNat 7) g1Gen) (g2Mul (frOfNat 11) g2Gen)
  let e2 := bn254Pairing (g1Mul (frOfNat 77) g1Gen) g2Gen
  (!fp12IsOne e1) && fp12Eq e1 e2

-- 6. Standalone x86-64 entrypoint positive & negative controls (modes 0..7)
#guard groth16X86Main 0 == 1
#guard groth16X86Main 1 == 0
#guard groth16X86Main 2 == 0
#guard groth16X86Main 3 == 0
#guard groth16X86Main 4 == 1
#guard groth16X86Main 5 == 1
#guard groth16X86Main 6 == 0
#guard groth16X86Main 7 == 0

-- 7. Numeric state-machine wrapper protocol check (mode 4 -> '1\n', exit 0)
#guard
  let r0 := groth16MachineStep 0 1
  let s1 := r0 / 2048
  let r1 := groth16MachineStep s1 52 -- ASCII '4'
  let s2 := r1 / 2048
  let r2 := groth16MachineStep s2 256 -- endOfArgument -> runs mode 4
  let ch := (r2 % 2048) / 8
  let s3 := r2 / 2048
  let r3 := groth16MachineStep s3 0 -- written -> newline
  let nl := (r3 % 2048) / 8
  let s4 := r3 / 2048
  let r4 := groth16MachineStep s4 0 -- written -> exit 0
  ch == 49 && nl == 10 && (r4 % 2048) == 3

end Tests

end Groth16X86
