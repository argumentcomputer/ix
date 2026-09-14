import Compilatrix.Ixby.Runtime.ScalarFunction

/-! Exact templates for the remaining functions emitted by `buildFields`.
Call targets and the field-box constructor come from the compiled image. -/

namespace Compilatrix.Ixby.Runtime.FieldArithmetic

open Ix.Ixby

def reduce (asField : FunctionId) (fieldBox : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.call asField [.local 0]) 1⟩,
    ⟨2, .letOp (.construct fieldBox [.local 1]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

def binary (asField : FunctionId) (fieldBox : Constructor) (operation : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call asField [.local 0]) 1⟩,
    ⟨3, .letOp (.call asField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive operation [.local 2, .local 3]) 3⟩,
    ⟨5, .letOp (.construct fieldBox [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

def negate (asField : FunctionId) (fieldBox : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.call asField [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldSub [.literal (.field 0), .local 1]) 2⟩,
    ⟨3, .letOp (.construct fieldBox [.local 2]) 3⟩,
    ⟨4, .ret (.local 3)⟩] }

def invert (asField : FunctionId) (fieldBox : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.call asField [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldInverse [.local 1]) 2⟩,
    ⟨3, .letOp (.construct fieldBox [.local 2]) 3⟩,
    ⟨4, .ret (.local 3)⟩] }

def pack (asField : FunctionId) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call asField [.local 0]) 1⟩,
    ⟨3, .letOp (.call asField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .extPack [.local 2, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

end Compilatrix.Ixby.Runtime.FieldArithmetic
