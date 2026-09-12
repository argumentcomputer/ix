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
  unless logHeight + logArity ≤ 32 && index < 2 ^ logHeight do throw .height
  let generator ← (Arithmetic.twoAdicGenerator (logHeight + logArity)).mapError Error.arithmetic
  let step ← (Arithmetic.twoAdicGenerator logArity).mapError Error.arithmetic
  let start := generator.pow (reverseBits index logHeight)
  return (Array.range (2 ^ logArity)).map fun i =>
    start.mul (step.pow (reverseBits i logArity))

def interpolate (points : Array Field) (values : Array Ext) (point : Ext) : Except Error Ext := do
  unless points.size == values.size && !points.isEmpty do throw .width
  let mut result := Arithmetic.zero
  for i in [0:points.size] do
    let xi ← getAt points i
    let yi ← getAt values i
    let mut numerator := Arithmetic.one
    let mut denominator : Field := 1
    for j in [0:points.size] do
      if i != j then
        let xj ← getAt points j
        numerator := numerator.mul (point.sub (Arithmetic.embed xj))
        denominator := denominator.mul (xi.sub xj)
    let inverse ← (Arithmetic.inverseBase denominator).mapError Error.arithmetic
    result := result.add (yi.mul (Arithmetic.scale numerator inverse))
  return result

def foldRow (limits : Limits) (index logHeight logArity : Nat) (beta : Ext)
    (values : Array Ext) : Except Error Ext := do
  unless logArity ≤ 32 do throw .arity
  if 2 ^ logArity > limits.foldArity then throw .limit
  unless values.size == 2 ^ logArity do throw .width
  interpolate (← rowPoints index logHeight logArity) values beta

end MultiStark.Verify.Fri
