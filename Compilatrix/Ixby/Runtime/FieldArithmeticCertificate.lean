import Compilatrix.Ixby.Runtime.FieldArithmeticCode
import Compilatrix.Ixby.Runtime.NumberConversion

namespace Compilatrix.Ixby.Runtime.FieldArithmetic

open Ix.Ixby ScalarFunction

structure Links where
  conversions : Conversion.Links
  reduce : FunctionId
  add : FunctionId
  sub : FunctionId
  mul : FunctionId
  neg : FunctionId
  inverse : FunctionId
  pack : FunctionId

/-- Complete code evidence for six base-field helpers and extension packing,
including every conversion dependency and all number constructor layouts. -/
structure Certificate (program : Program) (links : Links) : Type where
  conversions : Conversion.Certificate program links.conversions
  reduce : Checked program links.reduce (FieldArithmetic.reduce links.conversions.asField links.conversions.fieldCtor)
  add : Checked program links.add (binary links.conversions.asField links.conversions.fieldCtor .fieldAdd)
  sub : Checked program links.sub (binary links.conversions.asField links.conversions.fieldCtor .fieldSub)
  mul : Checked program links.mul (binary links.conversions.asField links.conversions.fieldCtor .fieldMul)
  neg : Checked program links.neg (negate links.conversions.asField links.conversions.fieldCtor)
  inverse : Checked program links.inverse (invert links.conversions.asField links.conversions.fieldCtor)
  pack : Checked program links.pack (FieldArithmetic.pack links.conversions.asField)

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let conversions ← Conversion.certify program links.conversions
  let reduce ← check program links.reduce (FieldArithmetic.reduce links.conversions.asField links.conversions.fieldCtor)
  let add ← check program links.add (binary links.conversions.asField links.conversions.fieldCtor .fieldAdd)
  let sub ← check program links.sub (binary links.conversions.asField links.conversions.fieldCtor .fieldSub)
  let mul ← check program links.mul (binary links.conversions.asField links.conversions.fieldCtor .fieldMul)
  let neg ← check program links.neg (negate links.conversions.asField links.conversions.fieldCtor)
  let inverse ← check program links.inverse (invert links.conversions.asField links.conversions.fieldCtor)
  let pack ← check program links.pack (FieldArithmetic.pack links.conversions.asField)
  return { conversions, reduce, add, sub, mul, neg, inverse, pack }

end Compilatrix.Ixby.Runtime.FieldArithmetic
