import IxAICommon.Hash

/-!
# Numeric formats for model specifications

A model is written once against `Arith` and instantiated per format. Each format fixes every
result bit as a pure function, so a training run has exactly one correct output whatever hardware
replays it.

Determinism rule: products round, sums of products do not. `dot` is specified as exact
accumulation followed by one rounding, so its result is independent of summation order. This is
what allows a parallel GPU reduction to reproduce the specification bit for bit.

Instances:
* `Fx`: fixed point with 8 fractional bits on unbounded integers. Addition is exact; `mul` and
  `dot` round toward negative infinity (an arithmetic shift).
* FloatLib binary formats (`Float.lean`): IEEE bfloat16 and binary32, with every operation
  rounded once to nearest, ties to even, and `dot` accumulated exactly.
-/

namespace IxAI

class Arith (α : Type) where
  zero : α
  /-- The value `n`, exactly. -/
  ofInt : Int → α
  add : α → α → α
  sub : α → α → α
  /-- A product, rounded to the format. -/
  mul : α → α → α
  /-- `Σ xᵢ·yᵢ` accumulated exactly and rounded once. Extra elements of the longer list are
  ignored. -/
  dot : List α → List α → α
  relu : α → α
  /-- Strictly positive. Used for the ReLU derivative. -/
  pos : α → Bool
  /-- The value `n / 256`, rounded to the format. Configs give weights and rates in these units. -/
  ofScaled : Int → α
  /-- Finite, with magnitude at most `raw / 256`. -/
  within : α → Nat → Bool
  /-- Rounding applied to a whole vector at a block boundary: a layer's pre-activations, its
  deltas, and each updated weight row and bias vector. The identity for scalar formats, which
  round every operation; block floating point rounds the vector to one shared exponent. -/
  block : List α → List α := id

/-- Fixed point: `raw / 2^fracBits`. -/
structure Fx where
  raw : Int
  deriving DecidableEq, Hashable, Repr, Inhabited

def Fx.fracBits : Nat := 8

instance : ToString Fx := ⟨fun x => toString x.raw⟩

instance : Enc Fx := ⟨fun b x => Enc.enc b x.raw⟩

/-- Exact sum of exact products, before the single rounding. -/
def Fx.exactDot (xs ys : List Fx) : Int := (List.zipWith (fun a b => a.raw * b.raw) xs ys).sum

instance : Arith Fx where
  zero := ⟨0⟩
  ofInt n := ⟨n <<< Fx.fracBits⟩
  add a b := ⟨a.raw + b.raw⟩
  sub a b := ⟨a.raw - b.raw⟩
  mul a b := ⟨(a.raw * b.raw) >>> Fx.fracBits⟩
  dot xs ys := ⟨Fx.exactDot xs ys >>> Fx.fracBits⟩
  relu a := if a.raw > 0 then a else ⟨0⟩
  pos a := a.raw > 0
  ofScaled n := ⟨n⟩
  within a raw := a.raw.natAbs ≤ raw

/-- Accumulation order does not matter: summing the products in reverse gives the same value, so
the rounded `dot` is the same too. -/
theorem Fx.exactSum_reverse (ps : List Int) : ps.reverse.sum = ps.sum := List.sum_reverse ps

end IxAI
