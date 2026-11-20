import IxAI.Num

/-!
# More numeric formats, for comparing quality and cost

* `FxN bits`: fixed point with `bits` fractional bits. `FxN 8` computes exactly what `Fx` does.
* `Bfp bits`: block floating point. Values are exact dyadics `m · 2^e`, and arithmetic between
  block boundaries is exact. At each boundary the model marks (`Arith.block`: a layer's
  pre-activations, its deltas, each updated weight row and bias vector) the whole vector is
  rounded, toward negative infinity, to `bits`-bit mantissas sharing the exponent of its largest
  element. This is the shape of the microscaling (MX) formats: integer inner products with one
  exponent per block.

Both are specified on unbounded integers, so every result bit is a pure function of the inputs and
independent of accumulation order.
-/

namespace IxAI

/-- Fixed point: `raw / 2^bits`. -/
structure FxN (bits : Nat) where
  raw : Int
  deriving DecidableEq, Repr, Inhabited

instance {bits : Nat} : Enc (FxN bits) := ⟨fun b x => Enc.enc b x.raw⟩

/-- `raw / 256` rescaled to `bits` fractional bits, rounding toward negative infinity. -/
def FxN.rescale (bits : Nat) (n : Int) : Int :=
  if bits ≥ 8 then n <<< (bits - 8) else n >>> (8 - bits)

instance {bits : Nat} : Arith (FxN bits) where
  zero := ⟨0⟩
  ofInt n := ⟨n <<< bits⟩
  add a b := ⟨a.raw + b.raw⟩
  sub a b := ⟨a.raw - b.raw⟩
  mul a b := ⟨(a.raw * b.raw) >>> bits⟩
  dot xs ys := ⟨(List.zipWith (fun a b => a.raw * b.raw) xs ys).sum >>> bits⟩
  relu a := if a.raw > 0 then a else ⟨0⟩
  pos a := a.raw > 0
  ofScaled n := ⟨FxN.rescale bits n⟩
  within a raw := a.raw.natAbs ≤ raw <<< bits >>> 8

/-- An exact dyadic `m · 2^e`, rounded only by `Bfp.block`. -/
structure Bfp (bits : Nat) where
  m : Int
  e : Int
  deriving DecidableEq, Repr, Inhabited

instance {bits : Nat} : Enc (Bfp bits) := ⟨fun b x => Enc.enc (Enc.enc b x.m) x.e⟩

namespace Bfp

variable {bits : Nat}

/-- The mantissa of `x` on the grid `2^q`, rounding toward negative infinity. -/
def onGrid (x : Bfp bits) (q : Int) : Int :=
  if x.e ≥ q then x.m <<< (x.e - q).toNat else x.m >>> (q - x.e).toNat

def add (a b : Bfp bits) : Bfp bits :=
  let q := min a.e b.e
  ⟨a.onGrid q + b.onGrid q, q⟩

def neg (a : Bfp bits) : Bfp bits := ⟨-a.m, a.e⟩

/-- The exponent of the leading bit, or `none` for zero. -/
def msb (x : Bfp bits) : Option Int :=
  if x.m == 0 then none else some (x.e + (Nat.log2 x.m.natAbs : Int))

/-- Round a vector to `bits`-bit mantissas on the grid of its largest element. -/
def block (xs : List (Bfp bits)) : List (Bfp bits) :=
  match (xs.filterMap msb).max? with
  | none => xs.map fun _ => ⟨0, 0⟩
  | some top =>
    let q := top + 1 - (bits : Int)
    xs.map fun x => ⟨x.onGrid q, q⟩

end Bfp

instance {bits : Nat} : Arith (Bfp bits) where
  zero := ⟨0, 0⟩
  ofInt n := ⟨n, 0⟩
  add := Bfp.add
  sub a b := Bfp.add a b.neg
  mul a b := ⟨a.m * b.m, a.e + b.e⟩
  dot xs ys := (List.zipWith (fun a b => (⟨a.m * b.m, a.e + b.e⟩ : Bfp bits)) xs ys).foldl Bfp.add ⟨0, 0⟩
  relu a := if a.m > 0 then a else ⟨0, 0⟩
  pos a := a.m > 0
  ofScaled n := ⟨n, -8⟩
  within a raw :=
    let s := a.e + 8
    if s ≥ 0 then a.m.natAbs <<< s.toNat ≤ raw else a.m.natAbs ≤ raw <<< (-s).toNat
  block := Bfp.block

end IxAI
