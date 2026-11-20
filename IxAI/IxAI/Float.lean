import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import IxAI.Num

/-!
# Floating-point formats from FloatLib

`Model fmt` is FloatLib's bit-level IEEE value. Addition, subtraction and multiplication use
FloatLib's specifications, which decode to exact dyadic rationals and round once to nearest, ties
to even. FloatLib proves its fast backends equal to these specifications.

`dot` follows the same method for a whole sum of products: decode, multiply exactly, add exactly,
round once. The result is therefore independent of the order of accumulation, which is what lets
a parallel implementation reproduce it bit for bit. Any non-finite operand makes the result the
format's invalid result (a NaN), which the training invariant rejects.
-/

open FloatLib FloatLib.Floats.Formats.BinaryInterchange

namespace IxAI

abbrev BF16 := Model FloatFormat.bfloat16
abbrev F32 := Model FloatFormat.binary32

instance {fmt : FloatFormat} : Hashable (Model fmt) := ⟨fun x => hash x.toNatBits⟩

instance {fmt : FloatFormat} : Enc (Model fmt) := ⟨fun b x => Enc.enc b x.toNatBits⟩

def exactProduct (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  { negative := a.negative ^^ b.negative
    significand := a.significand * b.significand
    exponent := a.exponent + b.exponent }

/-- Exact sum of exact products, before rounding. `none` if any operand is not finite. -/
def exactDot? {fmt : FloatFormat} (xs ys : List (Model fmt)) : Option Numerics.Dyadic := do
  let ps ← (List.zipWith (fun x y => (x, y)) xs ys).mapM fun (x, y) => do
    pure (exactProduct (← Model.toDyadic? x) (← Model.toDyadic? y))
  pure (ps.foldl Model.addDyadic Numerics.Dyadic.zero)

def dyadicWithin (d : Numerics.Dyadic) (raw : Nat) : Bool :=
  let e := d.exponent + 8
  if e ≥ 0 then d.significand <<< e.toNat ≤ raw else d.significand ≤ raw <<< (-e).toNat

instance {fmt : FloatFormat} : Arith (Model fmt) where
  zero := Model.zero fmt false
  ofInt n := Model.roundDyadic fmt ⟨n < 0, n.natAbs, 0⟩
  add := Model.Spec.add
  sub := Model.Spec.sub
  mul := Model.Spec.mul
  dot xs ys := match exactDot? xs ys with
    | some d => Model.roundDyadic fmt d
    | none => Model.invalidResult fmt
  relu x := match Model.toDyadic? x with
    | some d => if !d.negative && d.significand != 0 then x else Model.zero fmt false
    | none => x
  pos x := match Model.toDyadic? x with
    | some d => !d.negative && d.significand != 0
    | none => false
  ofScaled n := Model.roundDyadic fmt ⟨n < 0, n.natAbs, -8⟩
  within x raw := match Model.toDyadic? x with
    | some d => dyadicWithin d raw
    | none => false

instance {fmt : FloatFormat} : ToString (Model fmt) := ⟨fun x => toString x.toNatBits⟩

end IxAI
