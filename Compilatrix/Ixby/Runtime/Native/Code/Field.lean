import Compilatrix.Ixby.Runtime.Native.Code.Basic

/-! Concrete revision-two helper contracts. The certificate checks every
instruction against the emitted image; execution theorems use these bodies.
Function indices belong to this compiler's private runtime prefix. -/

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

/-- `Ix.Ixby.Goldilocks.reduce`, private function 83. -/
def Ix_Ixby_Goldilocks_reduce : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldToNat [.local 1]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ix.Ixby.Goldilocks.add`, private function 84. -/
def Ix_Ixby_Goldilocks_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .fieldAdd [.local 2, .local 3]) 3⟩,
    ⟨5, .letOp (.primitive .fieldToNat [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ix.Ixby.Goldilocks.sub`, private function 85. -/
def Ix_Ixby_Goldilocks_sub : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .fieldSub [.local 2, .local 3]) 3⟩,
    ⟨5, .letOp (.primitive .fieldToNat [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ix.Ixby.Goldilocks.mul`, private function 86. -/
def Ix_Ixby_Goldilocks_mul : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .fieldMul [.local 2, .local 3]) 3⟩,
    ⟨5, .letOp (.primitive .fieldToNat [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ix.Ixby.Goldilocks.neg`, private function 87. -/
def Ix_Ixby_Goldilocks_neg : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldSub [.literal (.field 0), .local 1]) 2⟩,
    ⟨3, .letOp (.primitive .fieldToNat [.local 2]) 3⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Ix.Ixby.Goldilocks.inverse`, private function 88. -/
def Ix_Ixby_Goldilocks_inverse : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldInverse [.local 1]) 2⟩,
    ⟨3, .letOp (.primitive .fieldToNat [.local 2]) 3⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Ix.Ixby.ExtGoldilocks.mk`, private function 89. -/
def Ix_Ixby_ExtGoldilocks_mk : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .extPack [.local 2, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

/-- `Ix.Ixby.ExtGoldilocks.add`, private function 90. -/
def Ix_Ixby_ExtGoldilocks_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .extAdd [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ix.Ixby.ExtGoldilocks.sub`, private function 91. -/
def Ix_Ixby_ExtGoldilocks_sub : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .extSub [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ix.Ixby.ExtGoldilocks.mul`, private function 92. -/
def Ix_Ixby_ExtGoldilocks_mul : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .extMul [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ix.Ixby.ExtGoldilocks.inverse`, private function 93. -/
def Ix_Ixby_ExtGoldilocks_inverse : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .extInverse [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ix.Ixby.instBEqExtGoldilocks.beq`, private function 94. -/
def Ix_Ixby_instBEqExtGoldilocks_beq : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .extEq [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ixby.Runtime.extFirst`, private function 95. -/
def Ixby_Runtime_extFirst : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .extFst [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldToNat [.local 1]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Ixby.Runtime.extSecond`, private function 96. -/
def Ixby_Runtime_extSecond : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .extSnd [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .fieldToNat [.local 1]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

def fieldEntries : Array Entry := #[
  ⟨83, `Ix.Ixby.Goldilocks.reduce, Ix_Ixby_Goldilocks_reduce⟩,
  ⟨84, `Ix.Ixby.Goldilocks.add, Ix_Ixby_Goldilocks_add⟩,
  ⟨85, `Ix.Ixby.Goldilocks.sub, Ix_Ixby_Goldilocks_sub⟩,
  ⟨86, `Ix.Ixby.Goldilocks.mul, Ix_Ixby_Goldilocks_mul⟩,
  ⟨87, `Ix.Ixby.Goldilocks.neg, Ix_Ixby_Goldilocks_neg⟩,
  ⟨88, `Ix.Ixby.Goldilocks.inverse, Ix_Ixby_Goldilocks_inverse⟩,
  ⟨89, `Ix.Ixby.ExtGoldilocks.mk, Ix_Ixby_ExtGoldilocks_mk⟩,
  ⟨90, `Ix.Ixby.ExtGoldilocks.add, Ix_Ixby_ExtGoldilocks_add⟩,
  ⟨91, `Ix.Ixby.ExtGoldilocks.sub, Ix_Ixby_ExtGoldilocks_sub⟩,
  ⟨92, `Ix.Ixby.ExtGoldilocks.mul, Ix_Ixby_ExtGoldilocks_mul⟩,
  ⟨93, `Ix.Ixby.ExtGoldilocks.inverse, Ix_Ixby_ExtGoldilocks_inverse⟩,
  ⟨94, `Ix.Ixby.instBEqExtGoldilocks.beq, Ix_Ixby_instBEqExtGoldilocks_beq⟩,
  ⟨95, `Ixby.Runtime.extFirst, Ixby_Runtime_extFirst⟩,
  ⟨96, `Ixby.Runtime.extSecond, Ixby_Runtime_extSecond⟩]

end Compilatrix.Ixby.Runtime.Native.Code
