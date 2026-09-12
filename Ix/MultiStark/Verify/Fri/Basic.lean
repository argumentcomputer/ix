module
public import Ix.MultiStark.Verify.Pcs.Basic

public section
@[expose] section

namespace MultiStark.Verify.Fri

/-- Explicit executable resource bounds, separate from protocol security
parameters. Interpolation is the simple quadratic reference algorithm. -/
structure Limits where
  queries : Nat := 1024
  foldArity : Nat := 256
  transcript : Transcript.Limits := {}
  deriving BEq, DecidableEq, Repr

inductive Error where
  | count | arity | height | width | query | empty | point | limit
  | initial | unconsumed | foldHeight | constant
  | finalPoly (query : Nat)
  | arithmetic (error : Arithmetic.Error)
  | transcript (error : Transcript.Error)
  | inputMmcs (batch : Nat) (error : Mmcs.Error)
  | commitMmcs (round : Nat) (error : Mmcs.Error)
  deriving BEq, DecidableEq, Repr, Inhabited

def getAt {α : Type} (values : Array α) (index : Nat) : Except Error α :=
  match values[index]? with | some value => .ok value | none => .error .count

/-- Reverse exactly the requested number of low bits; call sites check the
index range separately. This is not machine-word-wide bit reversal. -/
def reverseBits (value bits : Nat) : Nat := go bits value 0 where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | bits + 1, value, acc => go bits (value / 2) (acc * 2 + value % 2)

def polynomial (coefficients : Array Ext) (point : Ext) : Ext :=
  coefficients.toList.foldr (fun coefficient acc => coefficient.add (point.mul acc)) Arithmetic.zero

structure Challenges where
  alpha : Ext
  betas : Array Ext
  indices : Array Nat
  arities : Array Nat
  logGlobal : Nat
  logFinal : Nat
  deriving BEq, DecidableEq, Repr

end MultiStark.Verify.Fri
