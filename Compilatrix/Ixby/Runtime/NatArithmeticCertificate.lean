import Compilatrix.Ixby.Runtime.NatArithmeticCode
import Compilatrix.Ixby.Runtime.NumberConversion

namespace Compilatrix.Ixby.Runtime.NatArithmetic

open Ix.Ixby ScalarFunction

structure Links where
  conversions : Conversion.Links
  add : FunctionId
  sub : FunctionId
  mul : FunctionId

/-- Complete arithmetic code, including the already certified conversion
callees and number layouts. A changed dependency invalidates this certificate. -/
structure Certificate (program : Program) (links : Links) : Type where
  conversions : Conversion.Certificate program links.conversions
  add : Checked program links.add (binary links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor .natAdd .word32Add)
  sub : Checked program links.sub (subtract links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor)
  mul : Checked program links.mul (binary links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor .natMul .word32Mul)

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let conversions ← Conversion.certify program links.conversions
  let add ← check program links.add (binary links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor .natAdd .word32Add)
  let sub ← check program links.sub (subtract links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor)
  let mul ← check program links.mul (binary links.conversions.natural
    links.conversions.cachedCtor links.conversions.rawCtor links.conversions.fieldCtor .natMul .word32Mul)
  return { conversions, add, sub, mul }

end Compilatrix.Ixby.Runtime.NatArithmetic
