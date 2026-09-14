import Compilatrix.Ixby.Runtime.ConversionCode

/-! Exact code specifications for the remaining UInt8, UInt32, and USize
helpers. The compiler's USize representation has a fixed 64-bit width. -/

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby ScalarFunction Conversion

def identity : Function := { arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }

def truncate (natural lowWord : FunctionId) (cached : Constructor) (arity bits : Nat) : Function := {
  arity, blocks := #[
    ⟨arity, .letOp (.call natural [.local 0]) 1⟩,
    ⟨arity + 1, .letOp (.call lowWord [.local 0]) 2⟩,
    ⟨arity + 2, .letOp (.primitive .natMod [.local arity, N (2 ^ bits)]) 3⟩] ++
    if bits < 32 then #[
      ⟨arity + 3, .letOp (.primitive .word32And [.local (arity + 1), W (2 ^ bits - 1)]) 4⟩,
      ⟨arity + 4, .letOp (.construct cached [.local (arity + 2), .local (arity + 3)]) 5⟩,
      ⟨arity + 5, .ret (.local (arity + 4))⟩]
    else #[
      ⟨arity + 3, .letOp (.construct cached [.local (arity + 2), .local (arity + 1)]) 4⟩,
      ⟨arity + 4, .ret (.local (arity + 3))⟩] }

def compare (natural : FunctionId) (operation : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call natural [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive operation [.local 2, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

def modular (natural lowWord : FunctionId) (cached : Constructor)
    (bits : Nat) (natOp wordOp : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call lowWord [.local 0]) 2⟩,
    ⟨4, .letOp (.call natural [.local 1]) 3⟩,
    ⟨5, .letOp (.call lowWord [.local 1]) 4⟩,
    ⟨6, .letOp (.primitive natOp [.local 2, .local 4]) 5⟩,
    ⟨7, .letOp (.primitive wordOp [.local 3, .local 5]) 6⟩,
    ⟨8, .letOp (.construct cached [.local 6, .local 7]) 7⟩,
    ⟨9, .letOp (.call natural [.local 8]) 8⟩,
    ⟨10, .letOp (.call lowWord [.local 8]) 9⟩,
    ⟨11, .letOp (.primitive .natMod [.local 9, N (2 ^ bits)]) 10⟩] ++
    if bits < 32 then #[
      ⟨12, .letOp (.primitive .word32And [.local 10, W (2 ^ bits - 1)]) 11⟩,
      ⟨13, .letOp (.construct cached [.local 11, .local 12]) 12⟩,
      ⟨14, .ret (.local 13)⟩]
    else #[
      ⟨12, .letOp (.construct cached [.local 11, .local 10]) 11⟩,
      ⟨13, .ret (.local 12)⟩] }

def subtract (natural lowWord : FunctionId) (cached : Constructor) (bits : Nat) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call natural [.local 0]) 1⟩,
    ⟨3, .letOp (.call lowWord [.local 0]) 2⟩,
    ⟨4, .letOp (.call natural [.local 1]) 3⟩,
    ⟨5, .letOp (.call lowWord [.local 1]) 4⟩,
    ⟨6, .letOp (.primitive .natAdd [.local 2, N (2 ^ bits)]) 5⟩,
    ⟨7, .letOp (.primitive .natSub [.local 6, .local 4]) 6⟩,
    ⟨8, .letOp (.primitive .word32Sub [.local 3, .local 5]) 7⟩,
    ⟨9, .letOp (.construct cached [.local 7, .local 8]) 8⟩,
    ⟨10, .letOp (.call natural [.local 9]) 9⟩,
    ⟨11, .letOp (.call lowWord [.local 9]) 10⟩,
    ⟨12, .letOp (.primitive .natMod [.local 10, N (2 ^ bits)]) 11⟩,
    ⟨13, .letOp (.construct cached [.local 12, .local 11]) 12⟩,
    ⟨14, .ret (.local 13)⟩] }

def logical (lowWord fromWord : FunctionId) (operation : Primitive) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call lowWord [.local 0]) 1⟩,
    ⟨3, .letOp (.call lowWord [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive operation [.local 2, .local 3]) 3⟩,
    ⟨5, .tailCall fromWord [.local 4]⟩] }

def shift (lowWord fromWord : FunctionId) (operation : Primitive) (bits : Nat) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call lowWord [.local 0]) 1⟩,
    ⟨3, .letOp (.call lowWord [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .word32And [.local 3, W (bits - 1)]) 3⟩,
    ⟨5, .letOp (.primitive operation [.local 2, .local 4]) 4⟩] ++
    if bits < 32 then #[
      ⟨6, .letOp (.primitive .word32And [.local 5, W (2 ^ bits - 1)]) 5⟩,
      ⟨7, .tailCall fromWord [.local 6]⟩]
    else #[⟨6, .tailCall fromWord [.local 5]⟩] }

end Compilatrix.Ixby.Runtime.Words
