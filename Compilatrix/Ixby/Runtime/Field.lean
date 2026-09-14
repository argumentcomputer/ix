import Compilatrix.Ixby.Runtime.Number

/-! Representation-aware lowering of the pinned base/extension field source.
Base-field values retain a lazy exact Nat view; extension values use the
runtime's extension scalar directly, including source projections. -/

namespace Compilatrix.Ixby.Runtime

open Lean Ix.Ixby

private def wrap (value : Operand) : CodeM Operand :=
  make `Ixby.Runtime.FieldNumber [value]

def buildFields : BuildM Unit := do
  for (name, arity) in #[
      (`Ix.Ixby.Goldilocks.reduce, 1), (`Ix.Ixby.Goldilocks.add, 2),
      (`Ix.Ixby.Goldilocks.sub, 2), (`Ix.Ixby.Goldilocks.mul, 2),
      (`Ix.Ixby.Goldilocks.neg, 1), (`Ix.Ixby.Goldilocks.inverse, 1),
      (`Ix.Ixby.ExtGoldilocks.mk, 2), (`Ix.Ixby.ExtGoldilocks.add, 2),
      (`Ix.Ixby.ExtGoldilocks.sub, 2), (`Ix.Ixby.ExtGoldilocks.mul, 2),
      (`Ix.Ixby.ExtGoldilocks.inverse, 1), (`Ix.Ixby.instBEqExtGoldilocks.beq, 2),
      (`Ixby.Runtime.extFirst, 1), (`Ixby.Runtime.extSecond, 1)] do
    discard <| reserveFunction name arity
  modify fun state => { state with
    projections := state.projections.insert
      `Ix.Ixby.ExtGoldilocks #[`Ixby.Runtime.extFirst, `Ixby.Runtime.extSecond] }
  let define (name : Name) (arity : Nat) (body : CodeM Unit) : BuildM Unit :=
    discard <| defineFunction name arity body
  define `Ix.Ixby.Goldilocks.reduce 1 do
    ret (← wrap (← call `Ixby.Runtime.asField [.local 0]))
  for (name, operation) in #[(`Ix.Ixby.Goldilocks.add, Primitive.fieldAdd),
      (`Ix.Ixby.Goldilocks.sub, .fieldSub), (`Ix.Ixby.Goldilocks.mul, .fieldMul)] do
    define name 2 do
      let a ← call `Ixby.Runtime.asField [.local 0]
      let b ← call `Ixby.Runtime.asField [.local 1]
      ret (← wrap (← primitive operation [a, b]))
  define `Ix.Ixby.Goldilocks.neg 1 do
    let a ← call `Ixby.Runtime.asField [.local 0]
    ret (← wrap (← primitive .fieldSub [.literal (.field 0), a]))
  define `Ix.Ixby.Goldilocks.inverse 1 do
    ret (← wrap (← primitive .fieldInverse [← call `Ixby.Runtime.asField [.local 0]]))
  define `Ix.Ixby.ExtGoldilocks.mk 2 do
    let a ← call `Ixby.Runtime.asField [.local 0]
    let b ← call `Ixby.Runtime.asField [.local 1]
    ret (← primitive .extPack [a, b])
  for (name, operation) in #[(`Ix.Ixby.ExtGoldilocks.add, Primitive.extAdd),
      (`Ix.Ixby.ExtGoldilocks.sub, .extSub), (`Ix.Ixby.ExtGoldilocks.mul, .extMul),
      (`Ix.Ixby.instBEqExtGoldilocks.beq, .extEq)] do
    define name 2 do ret (← primitive operation [.local 0, .local 1])
  define `Ix.Ixby.ExtGoldilocks.inverse 1 do ret (← primitive .extInverse [.local 0])
  for (name, operation) in #[(`Ixby.Runtime.extFirst, Primitive.extFst),
      (`Ixby.Runtime.extSecond, .extSnd)] do
    define name 1 do ret (← wrap (← primitive operation [.local 0]))

end Compilatrix.Ixby.Runtime
