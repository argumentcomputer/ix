module
public import Std

/-! Kernel-reducible arithmetic for the IxBy cryptographic profile. The modulus
and quadratic basis match `Ix/MultiStark/Goldilocks.lean`. These are reference
relations, not a proof that a particular arithmetic gadget implements them. -/

public section
@[expose] section

namespace Ix.Ixby

abbrev goldilocksModulus : Nat := 18446744069414584321
abbrev Goldilocks := Fin goldilocksModulus

namespace Goldilocks

/-- Explicit modular reduction. Wire decoding must instead check `< p`. -/
def reduce (n : Nat) : Goldilocks := ⟨n % goldilocksModulus, Nat.mod_lt _ (by decide)⟩

def add (a b : Goldilocks) : Goldilocks := reduce (a.val + b.val)
def sub (a b : Goldilocks) : Goldilocks := reduce (a.val + goldilocksModulus - b.val)
def mul (a b : Goldilocks) : Goldilocks := reduce (a.val * b.val)
def neg (a : Goldilocks) : Goldilocks := sub 0 a

/-- Exponentiation with a structural bit budget, never a truncated exponent. -/
def pow (a : Goldilocks) (n : Nat) : Goldilocks := go (n.log2 + 1) n where
  go : Nat → Nat → Goldilocks
    | 0, _ => 1
    | fuel + 1, n =>
      if n == 0 then 1 else
        let h := go fuel (n / 2)
        let sq := mul h h
        if n % 2 == 0 then sq else mul sq a

/-- Total inverse convention: `inverse 0 = 0`, as in the current verifier. -/
def inverse (a : Goldilocks) : Goldilocks := pow a (goldilocksModulus - 2)

@[simp] theorem reduce_val (n : Nat) : (reduce n).val = n % goldilocksModulus := rfl

@[simp] theorem reduce_canonical (a : Goldilocks) : reduce a.val = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

end Goldilocks

/-- `c0 + c1 * X` in the quadratic extension with `X² = 7`. Coefficients
are serialized in this order, each as its canonical base-field value. -/
structure ExtGoldilocks where
  c0 : Goldilocks
  c1 : Goldilocks
  deriving BEq, DecidableEq, Repr, Inhabited

namespace ExtGoldilocks

def add (a b : ExtGoldilocks) : ExtGoldilocks :=
  ⟨a.c0.add b.c0, a.c1.add b.c1⟩

def sub (a b : ExtGoldilocks) : ExtGoldilocks :=
  ⟨a.c0.sub b.c0, a.c1.sub b.c1⟩

def mul (a b : ExtGoldilocks) : ExtGoldilocks :=
  ⟨(a.c0.mul b.c0).add ((Goldilocks.mul 7 a.c1).mul b.c1),
   (a.c0.mul b.c1).add (a.c1.mul b.c0)⟩

def inverse (a : ExtGoldilocks) : ExtGoldilocks :=
  let norm := (a.c0.mul a.c0).sub ((Goldilocks.mul 7 a.c1).mul a.c1)
  let inv := norm.inverse
  ⟨a.c0.mul inv, a.c1.neg.mul inv⟩

end ExtGoldilocks
end Ix.Ixby
