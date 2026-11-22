import Mathlib.Algebra.Field.Basic

/-!
# gnark's sparse R1CS

The constraint system that gnark's PLONK prover and Solidity verifier accept,
as a Lean structure. This is the boundary where crypto-layer trust begins:
the crypto layer supplies that a valid proof yields a satisfying wire
assignment, and that the commitment challenge is `H` of the committed values
for a random oracle `H` over a binding commitment.

* Wires `0 .. publics - 1` are public.
* A gate is `qL·a + qR·b + qO·c + qM·a·b + qC = 0` over three wire ids.
* A wire id that occurs in several gates denotes one value: gnark's
  permutation argument is the copy constraint.
* One BSB22 commitment binds the values of `committed`; wire `gamma` holds the
  challenge derived from it.
-/

namespace Aiur.Plonk

structure Gate (F : Type) where
  a : Nat
  b : Nat
  c : Nat
  qL : F
  qR : F
  qO : F
  qM : F
  qC : F
  deriving Repr, DecidableEq

def Gate.Holds {F : Type} [CommRing F] (w : Nat → F) (g : Gate F) : Prop :=
  g.qL * w g.a + g.qR * w g.b + g.qO * w g.c + g.qM * (w g.a * w g.b) + g.qC = 0

structure Scs (F : Type) where
  wires : Nat
  publics : Nat
  committed : List Nat
  gamma : Nat
  gates : List (Gate F)
  deriving Repr

/-- `w` satisfies `S` for public values `pub` and commitment challenge `H`. -/
def Scs.Satisfied {F : Type} [CommRing F] (S : Scs F) (w : Nat → F) (pub : List F)
    (H : List F → F) : Prop :=
  (∀ i (h : i < pub.length), i < S.publics → w i = pub[i]) ∧
    w S.gamma = H (S.committed.map w) ∧ ∀ g ∈ S.gates, g.Holds w

/-! ## The form gnark's frontend accepts

`AddPlonkConstraint(a, b, o, sL, sR, sO, sM, qC)` takes integer selectors and
reads field coefficients from the operand terms (`Mul(x, α)` only changes a
term's coefficient). An exported gate is therefore given by per-operand
coefficients, 0/1 selectors and a small integer constant. Its meaning is
`toGate`; the loader passes the fields through unchanged. -/

structure GGate (F : Type) where
  a : Nat
  b : Nat
  c : Nat
  α : F
  β : F
  ω : F
  sL : Bool
  sR : Bool
  sO : Bool
  sM : Bool
  qC : Int
  deriving Repr, DecidableEq

def sel {F : Type} [Zero F] (s : Bool) (x : F) : F := if s then x else 0

def GGate.toGate {F : Type} [CommRing F] (g : GGate F) : Gate F where
  a := g.a
  b := g.b
  c := g.c
  qL := sel g.sL g.α
  qR := sel g.sR g.β
  qO := sel g.sO g.ω
  qM := sel g.sM (g.α * g.β)
  qC := (g.qC : F)

/-- Scaling `L·a + R·b + O·c + M·a·b + C` by a nonzero `λ` into `GGate` form.
It fails only when `L, R, M, C` are all nonzero and `M·C ≠ L·R`. -/
def GGate.ofCoeffs {F : Type} [Field F] [DecidableEq F] (a b c : Nat) (L R O M C : F) :
    Option (GGate F) :=
  let lam : F := if C = 0 then 1 else C⁻¹
  let qC : Int := if C = 0 then 0 else 1
  if M = 0 then
    some ⟨a, b, c, lam * L, lam * R, lam * O, L ≠ 0, R ≠ 0, O ≠ 0, false, qC⟩
  else if L ≠ 0 ∧ R ≠ 0 then
    if C ≠ 0 ∧ M * C ≠ L * R then none
    else
      let lam' : F := M / (L * R)
      some ⟨a, b, c, lam' * L, lam' * R, lam' * O, true, true, O ≠ 0, true,
        if C = 0 then 0 else 1⟩
  else if L ≠ 0 then
    some ⟨a, b, c, lam * L, M / L, lam * O, true, false, O ≠ 0, true, qC⟩
  else if R ≠ 0 then
    some ⟨a, b, c, M / R, lam * R, lam * O, false, true, O ≠ 0, true, qC⟩
  else
    some ⟨a, b, c, lam * M, 1, lam * O, false, false, O ≠ 0, true, qC⟩

end Aiur.Plonk
