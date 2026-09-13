module
public import Ix.MultiStark.Verify.Fri.Basic

/-! Independent polynomial interpolation for a two-adic FRI row. This uses
the defining Lagrange products, not the prover's optimized folding circuit.
The challenge is permitted to equal a row point; only the distinct, fixed
row-point denominators are inverted, so that case is well-defined. -/

public section
@[expose] section

namespace MultiStark.Verify.Fri

def rowPoints (index logHeight logArity : Nat) : Except Error (Array Field) := do
  ensure (logHeight + logArity ≤ 32 && index < 2 ^ logHeight) .height
  let generator ← (Arithmetic.twoAdicGenerator (logHeight + logArity)).mapError Error.arithmetic
  let step ← (Arithmetic.twoAdicGenerator logArity).mapError Error.arithmetic
  let start := generator.pow (reverseBits index logHeight)
  return (Array.range (2 ^ logArity)).map fun i =>
    start.mul (step.pow (reverseBits i logArity))

def interpolationProducts (selected : Nat) (xi : Field) (point : Ext) :
    List (Field × Nat) → Ext → Field → Ext × Field
  | [], numerator, denominator => (numerator, denominator)
  | (xj, index) :: points, numerator, denominator =>
    if selected == index then interpolationProducts selected xi point points numerator denominator
    else interpolationProducts selected xi point points
      (numerator.mul (point.sub (Arithmetic.embed xj))) (denominator.mul (xi.sub xj))

def interpolateFrom (allPoints : List (Field × Nat)) (point : Ext) :
    List Field → List Ext → Nat → Ext → Except Error Ext
  | [], [], _, result => .ok result
  | xi :: points, yi :: values, index, result => do
    let (numerator, denominator) := interpolationProducts index xi point allPoints Arithmetic.one 1
    let inverse ← (Arithmetic.inverseBase denominator).mapError Error.arithmetic
    interpolateFrom allPoints point points values (index + 1)
      (result.add (yi.mul (Arithmetic.scale numerator inverse)))
  | _, _, _, _ => .error .width

def interpolate (points : Array Field) (values : Array Ext) (point : Ext) : Except Error Ext := do
  ensure (points.size == values.size && !points.isEmpty) .width
  interpolateFrom points.toList.zipIdx point points.toList values.toList 0 Arithmetic.zero

def foldRow (limits : Limits) (index logHeight logArity : Nat) (beta : Ext)
    (values : Array Ext) : Except Error Ext := do
  ensure (logArity ≤ 32) .arity
  ensure (2 ^ logArity ≤ limits.foldArity) .limit
  ensure (values.size == 2 ^ logArity) .width
  interpolate (← rowPoints index logHeight logArity) values beta

end MultiStark.Verify.Fri
