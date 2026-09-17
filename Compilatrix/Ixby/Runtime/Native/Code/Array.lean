import Compilatrix.Ixby.Runtime.Native.Code.Basic

/-! Concrete revision-two helper contracts. The certificate checks every
instruction against the emitted image; execution theorems use these bodies.
Function indices belong to this compiler's private runtime prefix. -/

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

/-- `Ixby.Runtime.arrayBytes`, private function 50. -/
def Ixby_Runtime_arrayBytes : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.primitive .natLt [.local 1, .local 2]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.primitive .arrayGet [.local 0, .local 1]) 4⟩,
    ⟨5, .letOp (.primitive .byteBuilderFreeze [.local 3]) 9⟩,
    ⟨6, .letOp (.primitive .word32ToBytes [.local 5]) 5⟩,
    ⟨7, .letOp (.primitive .bytesSlice [.local 6, .literal (.word32 0), .literal (.word32 1)]) 6⟩,
    ⟨8, .letOp (.primitive .byteBuilderAppend [.local 3, .local 7]) 7⟩,
    ⟨9, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 8⟩,
    ⟨10, .tailCall 50 [.local 0, .local 9, .local 2, .local 8]⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `Ixby.Runtime.toBytes`, private function 51. -/
def Ixby_Runtime_toBytes : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨2, .letOp (.primitive .arrayLength [.local 1]) 4⟩,
    ⟨2, .letOp (.primitive .byteBuilderFreeze [.local 1]) 6⟩,
    ⟨3, .letOp (.primitive .byteBuilderEmpty []) 5⟩,
    ⟨4, .tailCall 50 [.local 1, .literal (.nat 0), .local 2, .local 3]⟩,
    ⟨3, .letOp (.primitive .byteBuilderLength [.local 1]) 7⟩,
    ⟨4, .ret (.local 2)⟩] }

/-- `Ixby.Runtime.fromList`, private function 52. -/
def Ixby_Runtime_fromList : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .caseCtor (.local 0) [⟨3, 1⟩, ⟨4, 2⟩]⟩,
    ⟨2, .ret (.local 1)⟩,
    ⟨4, .letOp (.call 68 [.erased, .local 1, .local 2]) 3⟩,
    ⟨5, .tailCall 52 [.local 3, .local 4]⟩] }

/-- `Ixby.Runtime.toList`, private function 53. -/
def Ixby_Runtime_toList : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 1, .literal (.nat 0)]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .ret (.local 2)⟩,
    ⟨4, .letOp (.primitive .natSub [.local 1, .literal (.nat 1)]) 4⟩,
    ⟨5, .letOp (.call 62 [.erased, .local 0, .local 4, .erased]) 5⟩,
    ⟨6, .letOp (.construct 4 [.local 5, .local 2]) 6⟩,
    ⟨7, .tailCall 53 [.local 0, .local 4, .local 6]⟩] }

/-- `Ixby.Runtime.fromBytes`, private function 54. -/
def Ixby_Runtime_fromBytes : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.primitive .natLt [.local 1, .local 2]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.primitive .natToWord32 [.local 1]) 4⟩,
    ⟨5, .ret (.local 3)⟩,
    ⟨6, .letOp (.primitive .bytesGet [.local 0, .local 5]) 5⟩,
    ⟨7, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 6⟩,
    ⟨8, .letOp (.call 68 [.erased, .local 3, .local 6]) 7⟩,
    ⟨9, .tailCall 54 [.local 0, .local 7, .local 2, .local 8]⟩] }

/-- `Ixby.Runtime.copyArray`, private function 55. -/
def Ixby_Runtime_copyArray : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨3, .letOp (.call 61 [.erased, .local 2]) 4⟩,
    ⟨2, .ret (.local 0)⟩,
    ⟨2, .letOp (.primitive .byteBuilderFreeze [.local 1]) 5⟩,
    ⟨4, .tailCall 54 [.local 1, .literal (.nat 0), .local 2, .local 3]⟩,
    ⟨3, .letOp (.primitive .byteBuilderLength [.local 1]) 6⟩,
    ⟨4, .letOp (.call 61 [.erased, .local 3]) 7⟩,
    ⟨5, .tailCall 54 [.local 2, .literal (.nat 0), .local 3, .local 4]⟩] }

/-- `Ixby.Runtime.extract`, private function 56. -/
def Ixby_Runtime_extract : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.primitive .natLt [.local 1, .local 2]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.call 62 [.erased, .local 0, .local 1, .erased]) 4⟩,
    ⟨5, .ret (.local 3)⟩,
    ⟨6, .letOp (.call 68 [.erased, .local 3, .local 5]) 5⟩,
    ⟨7, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 6⟩,
    ⟨8, .tailCall 56 [.local 0, .local 7, .local 2, .local 6]⟩] }

/-- `Ixby.Runtime.replicate`, private function 57. -/
def Ixby_Runtime_replicate : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 0, .literal (.nat 0)]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .ret (.local 2)⟩,
    ⟨4, .letOp (.primitive .natSub [.local 0, .literal (.nat 1)]) 4⟩,
    ⟨5, .letOp (.call 68 [.erased, .local 2, .local 1]) 5⟩,
    ⟨6, .tailCall 57 [.local 4, .local 1, .local 5]⟩] }

/-- `Array.size`, private function 58. -/
def Array_size : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .caseCtor (.local 1) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨4, .ret (.local 3)⟩,
    ⟨3, .letOp (.primitive .arrayLength [.local 2]) 4⟩,
    ⟨3, .letOp (.primitive .byteBuilderLength [.local 2]) 5⟩,
    ⟨4, .ret (.local 3)⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Array.usize`, private function 59. -/
def Array_usize : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .tailCall 58 [.erased, .local 1]⟩] }

/-- `Array.emptyWithCapacity`, private function 60. -/
def Array_emptyWithCapacity : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .arrayEmpty []) 1⟩,
    ⟨3, .letOp (.construct 1 [.local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Array.mkEmpty`, private function 61. -/
def Array_mkEmpty : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .arrayEmpty []) 1⟩,
    ⟨3, .letOp (.construct 1 [.local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Array.getInternal`, private function 62. -/
def Array_getInternal : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .caseCtor (.local 1) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨6, .letOp (.primitive .natLt [.local 2, .local 5]) 4⟩,
    ⟨5, .letOp (.primitive .arrayLength [.local 4]) 9⟩,
    ⟨5, .letOp (.primitive .byteBuilderLength [.local 4]) 14⟩,
    ⟨7, .branch (.local 6) 5 6⟩,
    ⟨7, .letOp (.primitive .natToWord32 [.local 2]) 7⟩,
    ⟨7, .caseCtor (.erased) []⟩,
    ⟨8, .letOp (.primitive .bytesGet [.local 4, .local 7]) 8⟩,
    ⟨9, .ret (.local 8)⟩,
    ⟨6, .letOp (.primitive .natLt [.local 2, .local 5]) 10⟩,
    ⟨7, .branch (.local 6) 11 12⟩,
    ⟨7, .letOp (.primitive .arrayGet [.local 4, .local 2]) 13⟩,
    ⟨7, .caseCtor (.erased) []⟩,
    ⟨8, .ret (.local 7)⟩,
    ⟨6, .letOp (.primitive .natLt [.local 2, .local 5]) 15⟩,
    ⟨7, .branch (.local 6) 16 17⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 4]) 18⟩,
    ⟨7, .caseCtor (.erased) []⟩,
    ⟨8, .letOp (.primitive .natToWord32 [.local 2]) 19⟩,
    ⟨9, .letOp (.primitive .bytesGet [.local 7, .local 8]) 20⟩,
    ⟨10, .ret (.local 9)⟩] }

/-- `Array.getInternalBorrowed`, private function 63. -/
def Array_getInternalBorrowed : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .tailCall 62 [.erased, .local 1, .local 2, .erased]⟩] }

/-- `Array.uget`, private function 64. -/
def Array_uget : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .tailCall 62 [.erased, .local 1, .local 2, .erased]⟩] }

/-- `Array.ugetBorrowed`, private function 65. -/
def Array_ugetBorrowed : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .tailCall 62 [.erased, .local 1, .local 2, .erased]⟩] }

/-- `Array.get!Internal`, private function 66. -/
def Array_getBangInternal : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.call 58 [.erased, .local 2]) 1⟩,
    ⟨5, .letOp (.primitive .natLt [.local 3, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .tailCall 62 [.erased, .local 2, .local 3, .erased]⟩,
    ⟨6, .ret (.local 1)⟩] }

/-- `Array.get!InternalBorrowed`, private function 67. -/
def Array_getBangInternalBorrowed : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.call 58 [.erased, .local 2]) 1⟩,
    ⟨5, .letOp (.primitive .natLt [.local 3, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .tailCall 62 [.erased, .local 2, .local 3, .erased]⟩,
    ⟨6, .ret (.local 1)⟩] }

/-- `Array.push`, private function 68. -/
def Array_push : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .caseCtor (.local 1) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨5, .letOp (.call 55 [.local 1]) 4⟩,
    ⟨4, .letOp (.primitive .arrayPush [.local 3, .local 2]) 5⟩,
    ⟨4, .letOp (.primitive .byteBuilderFreeze [.local 3]) 7⟩,
    ⟨6, .tailCall 68 [.erased, .local 5, .local 2]⟩,
    ⟨5, .letOp (.construct 1 [.local 4]) 6⟩,
    ⟨6, .ret (.local 5)⟩,
    ⟨5, .letOp (.primitive .byteBuilderLength [.local 3]) 8⟩,
    ⟨6, .letOp (.call 55 [.local 1]) 9⟩,
    ⟨7, .tailCall 68 [.erased, .local 6, .local 2]⟩] }

/-- `Array.set!`, private function 69. -/
def Array_setBang : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.call 58 [.erased, .local 1]) 1⟩,
    ⟨5, .letOp (.primitive .natLt [.local 2, .local 4]) 2⟩,
    ⟨6, .branch (.local 5) 3 4⟩,
    ⟨6, .caseCtor (.local 1) [⟨0, 5⟩, ⟨1, 6⟩, ⟨2, 7⟩]⟩,
    ⟨6, .ret (.local 1)⟩,
    ⟨8, .letOp (.call 55 [.local 1]) 8⟩,
    ⟨7, .letOp (.primitive .arraySet [.local 6, .local 2, .local 3]) 9⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 6]) 11⟩,
    ⟨9, .tailCall 69 [.erased, .local 8, .local 2, .local 3]⟩,
    ⟨8, .letOp (.construct 1 [.local 7]) 10⟩,
    ⟨9, .ret (.local 8)⟩,
    ⟨8, .letOp (.primitive .byteBuilderLength [.local 6]) 12⟩,
    ⟨9, .letOp (.call 55 [.local 1]) 13⟩,
    ⟨10, .tailCall 69 [.erased, .local 9, .local 2, .local 3]⟩] }

/-- `Array.uset`, private function 70. -/
def Array_uset : Function := {
  arity := 5
  entry := 0
  blocks := #[
    ⟨5, .letOp (.call 58 [.erased, .local 1]) 1⟩,
    ⟨6, .letOp (.primitive .natLt [.local 2, .local 5]) 2⟩,
    ⟨7, .branch (.local 6) 3 4⟩,
    ⟨7, .tailCall 69 [.erased, .local 1, .local 2, .local 3]⟩,
    ⟨7, .caseCtor (.erased) []⟩] }

/-- `Array.extract`, private function 71. -/
def Array_extract : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .tailCall 72 [.local 1, .local 2, .local 3]⟩] }

/-- `Array.extract._redArg`, private function 72. -/
def Array_extract__redArg : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.call 58 [.erased, .local 0]) 1⟩,
    ⟨4, .letOp (.primitive .natLt [.local 3, .local 2]) 2⟩,
    ⟨5, .branch (.local 4) 3 4⟩,
    ⟨5, .letOp (.primitive .natLt [.local 1, .local 3]) 5⟩,
    ⟨5, .letOp (.primitive .natLt [.local 1, .local 2]) 26⟩,
    ⟨6, .branch (.local 5) 6 7⟩,
    ⟨6, .caseCtor (.local 0) [⟨0, 8⟩, ⟨1, 9⟩, ⟨2, 10⟩]⟩,
    ⟨6, .letOp (.primitive .arrayEmpty []) 24⟩,
    ⟨8, .letOp (.primitive .natSub [.local 3, .local 1]) 11⟩,
    ⟨7, .letOp (.call 61 [.erased, .literal (.nat 0)]) 16⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 6]) 17⟩,
    ⟨9, .letOp (.primitive .natToWord32 [.local 1]) 12⟩,
    ⟨10, .letOp (.primitive .natToWord32 [.local 8]) 13⟩,
    ⟨11, .letOp (.primitive .bytesSlice [.local 6, .local 9, .local 10]) 14⟩,
    ⟨12, .letOp (.construct 0 [.local 11, .local 8]) 15⟩,
    ⟨13, .ret (.local 12)⟩,
    ⟨8, .tailCall 56 [.local 0, .local 1, .local 3, .local 7]⟩,
    ⟨8, .letOp (.primitive .byteBuilderLength [.local 6]) 18⟩,
    ⟨9, .letOp (.primitive .natSub [.local 3, .local 1]) 19⟩,
    ⟨10, .letOp (.primitive .natToWord32 [.local 1]) 20⟩,
    ⟨11, .letOp (.primitive .natToWord32 [.local 9]) 21⟩,
    ⟨12, .letOp (.primitive .bytesSlice [.local 7, .local 10, .local 11]) 22⟩,
    ⟨13, .letOp (.construct 0 [.local 12, .local 9]) 23⟩,
    ⟨14, .ret (.local 13)⟩,
    ⟨7, .letOp (.construct 1 [.local 6]) 25⟩,
    ⟨8, .ret (.local 7)⟩,
    ⟨6, .branch (.local 5) 27 28⟩,
    ⟨6, .caseCtor (.local 0) [⟨0, 29⟩, ⟨1, 30⟩, ⟨2, 31⟩]⟩,
    ⟨6, .letOp (.primitive .arrayEmpty []) 45⟩,
    ⟨8, .letOp (.primitive .natSub [.local 2, .local 1]) 32⟩,
    ⟨7, .letOp (.call 61 [.erased, .literal (.nat 0)]) 37⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 6]) 38⟩,
    ⟨9, .letOp (.primitive .natToWord32 [.local 1]) 33⟩,
    ⟨10, .letOp (.primitive .natToWord32 [.local 8]) 34⟩,
    ⟨11, .letOp (.primitive .bytesSlice [.local 6, .local 9, .local 10]) 35⟩,
    ⟨12, .letOp (.construct 0 [.local 11, .local 8]) 36⟩,
    ⟨13, .ret (.local 12)⟩,
    ⟨8, .tailCall 56 [.local 0, .local 1, .local 2, .local 7]⟩,
    ⟨8, .letOp (.primitive .byteBuilderLength [.local 6]) 39⟩,
    ⟨9, .letOp (.primitive .natSub [.local 2, .local 1]) 40⟩,
    ⟨10, .letOp (.primitive .natToWord32 [.local 1]) 41⟩,
    ⟨11, .letOp (.primitive .natToWord32 [.local 9]) 42⟩,
    ⟨12, .letOp (.primitive .bytesSlice [.local 7, .local 10, .local 11]) 43⟩,
    ⟨13, .letOp (.construct 0 [.local 12, .local 9]) 44⟩,
    ⟨14, .ret (.local 13)⟩,
    ⟨7, .letOp (.construct 1 [.local 6]) 46⟩,
    ⟨8, .ret (.local 7)⟩] }

/-- `Array.append`, private function 73. -/
def Array_append : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .tailCall 74 [.local 1, .local 2]⟩] }

/-- `Array.append._redArg`, private function 74. -/
def Array_append__redArg : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.call 58 [.erased, .local 0]) 1⟩,
    ⟨3, .letOp (.call 58 [.erased, .local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natEq [.local 2, .literal (.nat 0)]) 3⟩,
    ⟨5, .branch (.local 4) 4 5⟩,
    ⟨5, .ret (.local 1)⟩,
    ⟨5, .letOp (.primitive .natEq [.local 3, .literal (.nat 0)]) 6⟩,
    ⟨6, .branch (.local 5) 7 8⟩,
    ⟨6, .ret (.local 0)⟩,
    ⟨6, .caseCtor (.local 0) [⟨0, 9⟩, ⟨1, 10⟩, ⟨2, 11⟩]⟩,
    ⟨8, .caseCtor (.local 1) [⟨0, 12⟩, ⟨1, 13⟩, ⟨2, 14⟩]⟩,
    ⟨7, .letOp (.call 55 [.local 0]) 24⟩,
    ⟨7, .letOp (.primitive .byteBuilderFreeze [.local 6]) 25⟩,
    ⟨10, .letOp (.call 82 [.local 6, .local 8]) 15⟩,
    ⟨9, .letOp (.call 55 [.local 0]) 18⟩,
    ⟨9, .letOp (.primitive .byteBuilderFreeze [.local 8]) 19⟩,
    ⟨11, .letOp (.primitive .natAdd [.local 2, .local 3]) 16⟩,
    ⟨12, .letOp (.construct 0 [.local 10, .local 11]) 17⟩,
    ⟨13, .ret (.local 12)⟩,
    ⟨10, .tailCall 56 [.local 1, .literal (.nat 0), .local 3, .local 9]⟩,
    ⟨10, .letOp (.primitive .byteBuilderLength [.local 8]) 20⟩,
    ⟨11, .letOp (.call 82 [.local 6, .local 9]) 21⟩,
    ⟨12, .letOp (.primitive .natAdd [.local 2, .local 3]) 22⟩,
    ⟨13, .letOp (.construct 0 [.local 11, .local 12]) 23⟩,
    ⟨14, .ret (.local 13)⟩,
    ⟨8, .tailCall 56 [.local 1, .literal (.nat 0), .local 3, .local 7]⟩,
    ⟨8, .letOp (.primitive .byteBuilderLength [.local 6]) 26⟩,
    ⟨9, .caseCtor (.local 1) [⟨0, 27⟩, ⟨1, 28⟩, ⟨2, 29⟩]⟩,
    ⟨11, .letOp (.call 82 [.local 7, .local 9]) 30⟩,
    ⟨10, .letOp (.call 55 [.local 0]) 33⟩,
    ⟨10, .letOp (.primitive .byteBuilderFreeze [.local 9]) 34⟩,
    ⟨12, .letOp (.primitive .natAdd [.local 2, .local 3]) 31⟩,
    ⟨13, .letOp (.construct 0 [.local 11, .local 12]) 32⟩,
    ⟨14, .ret (.local 13)⟩,
    ⟨11, .tailCall 56 [.local 1, .literal (.nat 0), .local 3, .local 10]⟩,
    ⟨11, .letOp (.primitive .byteBuilderLength [.local 9]) 35⟩,
    ⟨12, .letOp (.call 82 [.local 7, .local 10]) 36⟩,
    ⟨13, .letOp (.primitive .natAdd [.local 2, .local 3]) 37⟩,
    ⟨14, .letOp (.construct 0 [.local 12, .local 13]) 38⟩,
    ⟨15, .ret (.local 14)⟩] }

/-- `Array.pop`, private function 75. -/
def Array_pop : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.call 58 [.erased, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .natEq [.local 2, .literal (.nat 0)]) 2⟩,
    ⟨4, .branch (.local 3) 3 4⟩,
    ⟨4, .ret (.local 1)⟩,
    ⟨4, .letOp (.primitive .natSub [.local 2, .literal (.nat 1)]) 5⟩,
    ⟨5, .tailCall 72 [.local 1, .literal (.nat 0), .local 4]⟩] }

/-- `Array.mk`, private function 76. -/
def Array_mk : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.call 61 [.erased, .literal (.nat 0)]) 1⟩,
    ⟨3, .tailCall 52 [.local 1, .local 2]⟩] }

/-- `Array.toList`, private function 77. -/
def Array_toList : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.call 58 [.erased, .local 1]) 1⟩,
    ⟨3, .letOp (.construct 3 []) 2⟩,
    ⟨4, .tailCall 53 [.local 1, .local 2, .local 3]⟩] }

/-- `Array.replicate`, private function 78. -/
def Array_replicate : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.call 61 [.erased, .local 1]) 1⟩,
    ⟨4, .tailCall 57 [.local 1, .local 2, .local 3]⟩] }

/-- `String.toUTF8`, private function 79. -/
def String_toUTF8 : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `ByteArray.data`, private function 80. -/
def ByteArray_data : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .ret (.local 0)⟩] }

/-- `Ix.Ixby.Blake3.hash`, private function 81. -/
def Ix_Ixby_Blake3_hash : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.call 51 [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .blake3 [.local 1]) 2⟩,
    ⟨3, .letOp (.construct 0 [.local 2, .literal (.nat 32)]) 3⟩,
    ⟨4, .ret (.local 3)⟩] }

/-- `Ixby.Runtime.appendBytes`, private function 82. -/
def Ixby_Runtime_appendBytes : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .byteBuilderEmpty []) 1⟩,
    ⟨3, .letOp (.primitive .byteBuilderAppend [.local 2, .local 0]) 2⟩,
    ⟨4, .letOp (.primitive .byteBuilderAppend [.local 3, .local 1]) 3⟩,
    ⟨5, .letOp (.primitive .byteBuilderFreeze [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

def arrayEntries : Array Entry := #[
  ⟨50, `Ixby.Runtime.arrayBytes, Ixby_Runtime_arrayBytes⟩,
  ⟨51, `Ixby.Runtime.toBytes, Ixby_Runtime_toBytes⟩,
  ⟨52, `Ixby.Runtime.fromList, Ixby_Runtime_fromList⟩,
  ⟨53, `Ixby.Runtime.toList, Ixby_Runtime_toList⟩,
  ⟨54, `Ixby.Runtime.fromBytes, Ixby_Runtime_fromBytes⟩,
  ⟨55, `Ixby.Runtime.copyArray, Ixby_Runtime_copyArray⟩,
  ⟨56, `Ixby.Runtime.extract, Ixby_Runtime_extract⟩,
  ⟨57, `Ixby.Runtime.replicate, Ixby_Runtime_replicate⟩,
  ⟨58, `Array.size, Array_size⟩,
  ⟨59, `Array.usize, Array_usize⟩,
  ⟨60, `Array.emptyWithCapacity, Array_emptyWithCapacity⟩,
  ⟨61, `Array.mkEmpty, Array_mkEmpty⟩,
  ⟨62, `Array.getInternal, Array_getInternal⟩,
  ⟨63, `Array.getInternalBorrowed, Array_getInternalBorrowed⟩,
  ⟨64, `Array.uget, Array_uget⟩,
  ⟨65, `Array.ugetBorrowed, Array_ugetBorrowed⟩,
  ⟨66, `Array.get!Internal, Array_getBangInternal⟩,
  ⟨67, `Array.get!InternalBorrowed, Array_getBangInternalBorrowed⟩,
  ⟨68, `Array.push, Array_push⟩,
  ⟨69, `Array.set!, Array_setBang⟩,
  ⟨70, `Array.uset, Array_uset⟩,
  ⟨71, `Array.extract, Array_extract⟩,
  ⟨72, `Array.extract._redArg, Array_extract__redArg⟩,
  ⟨73, `Array.append, Array_append⟩,
  ⟨74, `Array.append._redArg, Array_append__redArg⟩,
  ⟨75, `Array.pop, Array_pop⟩,
  ⟨76, `Array.mk, Array_mk⟩,
  ⟨77, `Array.toList, Array_toList⟩,
  ⟨78, `Array.replicate, Array_replicate⟩,
  ⟨79, `String.toUTF8, String_toUTF8⟩,
  ⟨80, `ByteArray.data, ByteArray_data⟩,
  ⟨81, `Ix.Ixby.Blake3.hash, Ix_Ixby_Blake3_hash⟩,
  ⟨82, `Ixby.Runtime.appendBytes, Ixby_Runtime_appendBytes⟩]

end Compilatrix.Ixby.Runtime.Native.Code
