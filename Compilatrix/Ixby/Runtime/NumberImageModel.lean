import Compilatrix.Ixby.Lean

/-! Models of the retired boxed ABI retain its existing proof obligations.
The current frontend uses unboxed scalars and never calls these adapters. -/

namespace Compilatrix.Ixby.LeanFrontend

open Lean Ix.Ixby

def Image.modelNumber (image : Image) (n : Nat) : Except String Value := do
  return .ctor (← image.ctorId `Ixby.Runtime.Number) #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]

def Image.decodeModelNumber (image : Image) (value : Value) : Except String Nat := do
  if let .ctor id #[.scalar (.field f)] := value then
    unless id == (← image.ctorId `Ixby.Runtime.FieldNumber) do
      throw "typed Ixby field number layout failed"
    return f.val
  if let .ctor id #[.scalar (.nat n)] := value then
    unless id == (← image.ctorId `Ixby.Runtime.RawNumber) do
      throw "typed Ixby raw number layout failed"
    return n
  let .ctor id #[.scalar (.nat n), .scalar (.word32 low)] := value |
    throw "typed Ixby output is not a number"
  unless id == (← image.ctorId `Ixby.Runtime.Number) && low == n.toUInt32 do
    throw "typed Ixby output number invariant failed"
  return n

end Compilatrix.Ixby.LeanFrontend
