import Compilatrix.Ixby.Runtime.Native.Code.Basic

/-! Concrete revision-two helper contracts. The certificate checks every
instruction against the emitted image; execution theorems use these bodies.
Function indices belong to this compiler's private runtime prefix. -/

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

/-- `Ixby.Runtime.toWord`, private function 0. -/
def Ixby_Runtime_toWord : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨4, .letOp (.primitive .word32Mul [.local 3, .local 1]) 2⟩,
    ⟨5, .letOp (.primitive .word32Add [.local 2, .local 4]) 3⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ixby.Runtime.fromWordLoop`, private function 1. -/
def Ixby_Runtime_fromWordLoop : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .word32ToNat [.local 0]) 1⟩,
    ⟨4, .letOp (.primitive .natMul [.local 3, .local 1]) 2⟩,
    ⟨5, .letOp (.primitive .natAdd [.local 2, .local 4]) 3⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ixby.Runtime.fromWord`, private function 2. -/
def Ixby_Runtime_fromWord : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .word32ToNat [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ixby.Runtime.fromRaw`, private function 3. -/
def Ixby_Runtime_fromRaw : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `Ixby.Runtime.lowWord`, private function 4. -/
def Ixby_Runtime_lowWord : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ixby.Runtime.natural`, private function 5. -/
def Ixby_Runtime_natural : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `Ixby.Runtime.fieldNatural`, private function 6. -/
def Ixby_Runtime_fieldNatural : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .fieldToNat [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ixby.Runtime.asField`, private function 7. -/
def Ixby_Runtime_asField : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ixby.Runtime.fieldFromNatural`, private function 8. -/
def Ixby_Runtime_fieldFromNatural : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `Ixby.Runtime.shiftRightLoop`, private function 9. -/
def Ixby_Runtime_shiftRightLoop : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natEq [.local 1, .literal (.nat 0)]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .ret (.local 0)⟩,
    ⟨3, .letOp (.primitive .natEq [.local 0, .literal (.nat 0)]) 4⟩,
    ⟨4, .branch (.local 3) 5 6⟩,
    ⟨4, .ret (.literal (.nat 0))⟩,
    ⟨4, .letOp (.primitive .natDiv [.local 0, .literal (.nat 2)]) 7⟩,
    ⟨5, .letOp (.primitive .natSub [.local 1, .literal (.nat 1)]) 8⟩,
    ⟨6, .tailCall 9 [.local 4, .local 5]⟩] }

/-- `Ixby.Runtime.log2Loop`, private function 10. -/
def Ixby_Runtime_log2Loop : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natLt [.local 0, .literal (.nat 2)]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨3, .letOp (.primitive .natDiv [.local 0, .literal (.nat 2)]) 4⟩,
    ⟨4, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 5⟩,
    ⟨5, .tailCall 10 [.local 3, .local 4]⟩] }

/-- `Ixby.Runtime.powLoop`, private function 11. -/
def Ixby_Runtime_powLoop : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 1, .literal (.nat 0)]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .ret (.local 2)⟩,
    ⟨4, .letOp (.primitive .natDiv [.local 1, .literal (.nat 2)]) 4⟩,
    ⟨5, .letOp (.primitive .natMod [.local 1, .literal (.nat 2)]) 5⟩,
    ⟨6, .letOp (.primitive .natEq [.local 5, .literal (.nat 1)]) 6⟩,
    ⟨7, .branch (.local 6) 7 8⟩,
    ⟨7, .letOp (.primitive .natMul [.local 2, .local 0]) 9⟩,
    ⟨7, .letOp (.primitive .natEq [.local 4, .literal (.nat 0)]) 14⟩,
    ⟨8, .letOp (.primitive .natEq [.local 4, .literal (.nat 0)]) 10⟩,
    ⟨9, .branch (.local 8) 11 12⟩,
    ⟨9, .ret (.local 7)⟩,
    ⟨9, .letOp (.primitive .natMul [.local 0, .local 0]) 13⟩,
    ⟨10, .tailCall 11 [.local 9, .local 4, .local 7]⟩,
    ⟨8, .branch (.local 7) 15 16⟩,
    ⟨8, .ret (.local 2)⟩,
    ⟨8, .letOp (.primitive .natMul [.local 0, .local 0]) 17⟩,
    ⟨9, .tailCall 11 [.local 8, .local 4, .local 2]⟩] }

/-- `Nat.add`, private function 12. -/
def Nat_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natAdd [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.sub`, private function 13. -/
def Nat_sub : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natSub [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.mul`, private function 14. -/
def Nat_mul : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natMul [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.div`, private function 15. -/
def Nat_div : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natDiv [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.mod`, private function 16. -/
def Nat_mod : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natMod [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.decEq`, private function 17. -/
def Nat_decEq : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natEq [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.decLt`, private function 18. -/
def Nat_decLt : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natLt [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `Nat.decLe`, private function 19. -/
def Nat_decLe : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natLt [.local 1, .local 0]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .ret (.literal (.bool false))⟩,
    ⟨3, .ret (.literal (.bool true))⟩] }

/-- `Nat.pow`, private function 20. -/
def Nat_pow : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .tailCall 11 [.local 0, .local 1, .literal (.nat 1)]⟩] }

/-- `Nat.shiftRight`, private function 21. -/
def Nat_shiftRight : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natEq [.local 1, .literal (.nat 1)]) 1⟩,
    ⟨3, .branch (.local 2) 2 3⟩,
    ⟨3, .letOp (.primitive .natDiv [.local 0, .literal (.nat 2)]) 4⟩,
    ⟨3, .tailCall 9 [.local 0, .local 1]⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Nat.log2`, private function 22. -/
def Nat_log2 : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .tailCall 10 [.local 0, .literal (.nat 0)]⟩] }

/-- `UInt8.ofNat`, private function 23. -/
def UInt8_ofNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .word32And [.local 1, .literal (.word32 255)]) 2⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt8.toNat`, private function 24. -/
def UInt8_toNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .word32ToNat [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `UInt8.toUInt32`, private function 25. -/
def UInt8_toUInt32 : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `UInt8.decEq`, private function 26. -/
def UInt8_decEq : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Eq [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt8.add`, private function 27. -/
def UInt8_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Add [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .word32And [.local 2, .literal (.word32 255)]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `UInt8.shiftLeft`, private function 28. -/
def UInt8_shiftLeft : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32And [.local 1, .literal (.word32 7)]) 1⟩,
    ⟨3, .letOp (.primitive .word32Shl [.local 0, .local 2]) 2⟩,
    ⟨4, .letOp (.primitive .word32And [.local 3, .literal (.word32 255)]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

/-- `UInt8.shiftRight`, private function 29. -/
def UInt8_shiftRight : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32And [.local 1, .literal (.word32 7)]) 1⟩,
    ⟨3, .letOp (.primitive .word32Shr [.local 0, .local 2]) 2⟩,
    ⟨4, .letOp (.primitive .word32And [.local 3, .literal (.word32 255)]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

/-- `UInt32.ofNat`, private function 30. -/
def UInt32_ofNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `UInt32.ofNatLT`, private function 31. -/
def UInt32_ofNatLT : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.toUInt8`, private function 32. -/
def UInt32_toUInt8 : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .word32And [.local 0, .literal (.word32 255)]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `UInt32.toNat`, private function 33. -/
def UInt32_toNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .word32ToNat [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `UInt32.add`, private function 34. -/
def UInt32_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Add [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.sub`, private function 35. -/
def UInt32_sub : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Sub [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.mul`, private function 36. -/
def UInt32_mul : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Mul [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.land`, private function 37. -/
def UInt32_land : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32And [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.lor`, private function 38. -/
def UInt32_lor : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Or [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.xor`, private function 39. -/
def UInt32_xor : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Xor [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.shiftLeft`, private function 40. -/
def UInt32_shiftLeft : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32And [.local 1, .literal (.word32 31)]) 1⟩,
    ⟨3, .letOp (.primitive .word32Shl [.local 0, .local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `UInt32.shiftRight`, private function 41. -/
def UInt32_shiftRight : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32And [.local 1, .literal (.word32 31)]) 1⟩,
    ⟨3, .letOp (.primitive .word32Shr [.local 0, .local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `UInt32.decEq`, private function 42. -/
def UInt32_decEq : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Eq [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `UInt32.decLt`, private function 43. -/
def UInt32_decLt : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32Lt [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `USize.ofNat`, private function 44. -/
def USize_ofNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.primitive .natMod [.local 0, .literal (.nat 18446744073709551616)]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }

/-- `USize.toNat`, private function 45. -/
def USize_toNat : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `USize.add`, private function 46. -/
def USize_add : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natAdd [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .natMod [.local 2, .literal (.nat 18446744073709551616)]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `USize.sub`, private function 47. -/
def USize_sub : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natAdd [.local 0, .literal (.nat 18446744073709551616)]) 1⟩,
    ⟨3, .letOp (.primitive .natSub [.local 2, .local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natMod [.local 3, .literal (.nat 18446744073709551616)]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

/-- `USize.decEq`, private function 48. -/
def USize_decEq : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natEq [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

/-- `USize.decLt`, private function 49. -/
def USize_decLt : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natLt [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }

def numberEntries : Array Entry := #[
  ⟨0, `Ixby.Runtime.toWord, Ixby_Runtime_toWord⟩,
  ⟨1, `Ixby.Runtime.fromWordLoop, Ixby_Runtime_fromWordLoop⟩,
  ⟨2, `Ixby.Runtime.fromWord, Ixby_Runtime_fromWord⟩,
  ⟨3, `Ixby.Runtime.fromRaw, Ixby_Runtime_fromRaw⟩,
  ⟨4, `Ixby.Runtime.lowWord, Ixby_Runtime_lowWord⟩,
  ⟨5, `Ixby.Runtime.natural, Ixby_Runtime_natural⟩,
  ⟨6, `Ixby.Runtime.fieldNatural, Ixby_Runtime_fieldNatural⟩,
  ⟨7, `Ixby.Runtime.asField, Ixby_Runtime_asField⟩,
  ⟨8, `Ixby.Runtime.fieldFromNatural, Ixby_Runtime_fieldFromNatural⟩,
  ⟨9, `Ixby.Runtime.shiftRightLoop, Ixby_Runtime_shiftRightLoop⟩,
  ⟨10, `Ixby.Runtime.log2Loop, Ixby_Runtime_log2Loop⟩,
  ⟨11, `Ixby.Runtime.powLoop, Ixby_Runtime_powLoop⟩,
  ⟨12, `Nat.add, Nat_add⟩,
  ⟨13, `Nat.sub, Nat_sub⟩,
  ⟨14, `Nat.mul, Nat_mul⟩,
  ⟨15, `Nat.div, Nat_div⟩,
  ⟨16, `Nat.mod, Nat_mod⟩,
  ⟨17, `Nat.decEq, Nat_decEq⟩,
  ⟨18, `Nat.decLt, Nat_decLt⟩,
  ⟨19, `Nat.decLe, Nat_decLe⟩,
  ⟨20, `Nat.pow, Nat_pow⟩,
  ⟨21, `Nat.shiftRight, Nat_shiftRight⟩,
  ⟨22, `Nat.log2, Nat_log2⟩,
  ⟨23, `UInt8.ofNat, UInt8_ofNat⟩,
  ⟨24, `UInt8.toNat, UInt8_toNat⟩,
  ⟨25, `UInt8.toUInt32, UInt8_toUInt32⟩,
  ⟨26, `UInt8.decEq, UInt8_decEq⟩,
  ⟨27, `UInt8.add, UInt8_add⟩,
  ⟨28, `UInt8.shiftLeft, UInt8_shiftLeft⟩,
  ⟨29, `UInt8.shiftRight, UInt8_shiftRight⟩,
  ⟨30, `UInt32.ofNat, UInt32_ofNat⟩,
  ⟨31, `UInt32.ofNatLT, UInt32_ofNatLT⟩,
  ⟨32, `UInt32.toUInt8, UInt32_toUInt8⟩,
  ⟨33, `UInt32.toNat, UInt32_toNat⟩,
  ⟨34, `UInt32.add, UInt32_add⟩,
  ⟨35, `UInt32.sub, UInt32_sub⟩,
  ⟨36, `UInt32.mul, UInt32_mul⟩,
  ⟨37, `UInt32.land, UInt32_land⟩,
  ⟨38, `UInt32.lor, UInt32_lor⟩,
  ⟨39, `UInt32.xor, UInt32_xor⟩,
  ⟨40, `UInt32.shiftLeft, UInt32_shiftLeft⟩,
  ⟨41, `UInt32.shiftRight, UInt32_shiftRight⟩,
  ⟨42, `UInt32.decEq, UInt32_decEq⟩,
  ⟨43, `UInt32.decLt, UInt32_decLt⟩,
  ⟨44, `USize.ofNat, USize_ofNat⟩,
  ⟨45, `USize.toNat, USize_toNat⟩,
  ⟨46, `USize.add, USize_add⟩,
  ⟨47, `USize.sub, USize_sub⟩,
  ⟨48, `USize.decEq, USize_decEq⟩,
  ⟨49, `USize.decLt, USize_decLt⟩]

end Compilatrix.Ixby.Runtime.Native.Code
