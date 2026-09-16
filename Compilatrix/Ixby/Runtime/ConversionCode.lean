import Compilatrix.Ixby.Runtime.ScalarFunction

/-! Exact templates checked against the generated conversion helpers. Function
and constructor indices come from the image; no absolute linkage is assumed.
These templates are proof specifications, not a second compiler or runtime. -/

namespace Compilatrix.Ixby.Runtime.Conversion

open Ix.Ixby ScalarFunction

abbrev N (n : Nat) : Operand := .literal (.nat n)
abbrev W (n : Nat) : Operand := .literal (.word32 n.toUInt32)

/-- The builder's balanced sixteen-leaf tree, parameterized only by direction. -/
def nibble (toWord : Bool) : Function :=
  let less := if toWord then Primitive.natLt else .word32Lt
  let input := if toWord then N else W
  let output := if toWord then W else N
  { arity := 1, blocks := #[
    ⟨1, .letOp (.primitive less [.local 0, input 8]) 1⟩,
    ⟨2, .branch (.local 1) 2 3⟩,
    ⟨2, .letOp (.primitive less [.local 0, input 4]) 4⟩,
    ⟨2, .letOp (.primitive less [.local 0, input 12]) 25⟩,
    ⟨3, .branch (.local 2) 5 6⟩,
    ⟨3, .letOp (.primitive less [.local 0, input 2]) 7⟩,
    ⟨3, .letOp (.primitive less [.local 0, input 6]) 16⟩,
    ⟨4, .branch (.local 3) 8 9⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 1]) 10⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 3]) 13⟩,
    ⟨5, .branch (.local 4) 11 12⟩,
    ⟨5, .ret (output 0)⟩,
    ⟨5, .ret (output 1)⟩,
    ⟨5, .branch (.local 4) 14 15⟩,
    ⟨5, .ret (output 2)⟩,
    ⟨5, .ret (output 3)⟩,
    ⟨4, .branch (.local 3) 17 18⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 5]) 19⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 7]) 22⟩,
    ⟨5, .branch (.local 4) 20 21⟩,
    ⟨5, .ret (output 4)⟩,
    ⟨5, .ret (output 5)⟩,
    ⟨5, .branch (.local 4) 23 24⟩,
    ⟨5, .ret (output 6)⟩,
    ⟨5, .ret (output 7)⟩,
    ⟨3, .branch (.local 2) 26 27⟩,
    ⟨3, .letOp (.primitive less [.local 0, input 10]) 28⟩,
    ⟨3, .letOp (.primitive less [.local 0, input 14]) 37⟩,
    ⟨4, .branch (.local 3) 29 30⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 9]) 31⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 11]) 34⟩,
    ⟨5, .branch (.local 4) 32 33⟩,
    ⟨5, .ret (output 8)⟩,
    ⟨5, .ret (output 9)⟩,
    ⟨5, .branch (.local 4) 35 36⟩,
    ⟨5, .ret (output 10)⟩,
    ⟨5, .ret (output 11)⟩,
    ⟨4, .branch (.local 3) 38 39⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 13]) 40⟩,
    ⟨4, .letOp (.primitive less [.local 0, input 15]) 43⟩,
    ⟨5, .branch (.local 4) 41 42⟩,
    ⟨5, .ret (output 12)⟩,
    ⟨5, .ret (output 13)⟩,
    ⟨5, .branch (.local 4) 44 45⟩,
    ⟨5, .ret (output 14)⟩,
    ⟨5, .ret (output 15)⟩] }

def toWord (_self _digit : FunctionId) : Function := {
  arity := 3, blocks := #[
    ⟨3, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨4, .letOp (.primitive .word32Mul [.local 3, .local 1]) 2⟩,
    ⟨5, .letOp (.primitive .word32Add [.local 2, .local 4]) 3⟩,
    ⟨6, .ret (.local 5)⟩] }

def fromWordLoop (_self _digit : FunctionId) : Function := {
  arity := 3, blocks := #[
    ⟨3, .letOp (.primitive .word32ToNat [.local 0]) 1⟩,
    ⟨4, .letOp (.primitive .natMul [.local 3, .local 1]) 2⟩,
    ⟨5, .letOp (.primitive .natAdd [.local 2, .local 4]) 3⟩,
    ⟨6, .ret (.local 5)⟩] }

def fromWord (loop : FunctionId) (cached : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.call loop [.local 0, N 1, N 0]) 1⟩,
    ⟨2, .letOp (.construct cached [.local 1, .local 0]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

def fromRaw (raw : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.construct raw [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

def lowWord (loop : FunctionId) (cached raw field : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨cached, 1⟩, ⟨raw, 2⟩, ⟨field, 3⟩]⟩,
    ⟨3, .ret (.local 2)⟩,
    ⟨2, .tailCall loop [.local 1, W 1, W 0]⟩,
    ⟨2, .letOp (.primitive .fieldToBytes [.local 1]) 4⟩,
    ⟨3, .letOp (.primitive .bytesSlice [.local 2, W 0, W 4]) 5⟩,
    ⟨4, .letOp (.primitive .bytesToWord32 [.local 3]) 6⟩,
    ⟨5, .ret (.local 4)⟩] }

def natural (fieldNatural : FunctionId) (cached raw field : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨cached, 1⟩, ⟨raw, 2⟩, ⟨field, 3⟩]⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨2, .ret (.local 1)⟩,
    ⟨2, .tailCall fieldNatural [.local 1]⟩] }

def fieldNatural (loop : FunctionId) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .fieldToBytes [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .bytesSlice [.local 1, W 0, W 4]) 2⟩,
    ⟨3, .letOp (.primitive .bytesToWord32 [.local 2]) 3⟩,
    ⟨4, .letOp (.call loop [.local 3, N 1, N 0]) 4⟩,
    ⟨5, .letOp (.primitive .bytesSlice [.local 1, W 4, W 4]) 5⟩,
    ⟨6, .letOp (.primitive .bytesToWord32 [.local 5]) 6⟩,
    ⟨7, .letOp (.call loop [.local 6, N 1, N 0]) 7⟩,
    ⟨8, .letOp (.primitive .natMul [.local 7, N (2 ^ 32)]) 8⟩,
    ⟨9, .letOp (.primitive .natAdd [.local 4, .local 8]) 9⟩,
    ⟨10, .ret (.local 9)⟩] }

def fieldFromNatural (loop : FunctionId) : Function := {
  arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .natMod [.local 0, N goldilocksModulus]) 1⟩,
    ⟨2, .letOp (.call loop [.local 1, W 1, W 0]) 2⟩,
    ⟨3, .letOp (.primitive .natDiv [.local 1, N (2 ^ 32)]) 3⟩,
    ⟨4, .letOp (.call loop [.local 3, W 1, W 0]) 4⟩,
    ⟨5, .letOp (.primitive .word32ToField [.local 2]) 5⟩,
    ⟨6, .letOp (.primitive .word32ToField [.local 4]) 6⟩,
    ⟨7, .letOp (.primitive .fieldMul
      [.local 6, .literal (.field (Goldilocks.reduce (2 ^ 32)))]) 7⟩,
    ⟨8, .letOp (.primitive .fieldAdd [.local 5, .local 7]) 8⟩,
    ⟨9, .ret (.local 8)⟩] }

def asField (fieldFromNatural : FunctionId) (cached raw field : Constructor) : Function := {
  arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨cached, 1⟩, ⟨raw, 2⟩, ⟨field, 3⟩]⟩,
    ⟨3, .tailCall fieldFromNatural [.local 1]⟩,
    ⟨2, .tailCall fieldFromNatural [.local 1]⟩,
    ⟨2, .ret (.local 1)⟩] }

end Compilatrix.Ixby.Runtime.Conversion
