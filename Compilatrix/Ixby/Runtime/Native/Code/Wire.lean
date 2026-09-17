import Compilatrix.Ixby.Runtime.Native.Code.Basic

/-! Concrete revision-two helper contracts. The certificate checks every
instruction against the emitted image; execution theorems use these bodies.
Function indices belong to this compiler's private runtime prefix. -/

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

/-- `Ixby.Runtime.wireLittleLoop`, private function 98. -/
def Ixby_Runtime_wireLittleLoop : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natToWord32 [.local 1]) 1⟩,
    ⟨4, .letOp (.primitive .word32ToBytes [.local 3]) 2⟩,
    ⟨5, .letOp (.primitive .natLt [.local 0, .literal (.nat 5)]) 3⟩,
    ⟨6, .branch (.local 5) 4 5⟩,
    ⟨6, .letOp (.primitive .natToWord32 [.local 0]) 6⟩,
    ⟨6, .letOp (.primitive .natSub [.local 0, .literal (.nat 4)]) 10⟩,
    ⟨7, .letOp (.primitive .bytesSlice [.local 4, .literal (.word32 0), .local 6]) 7⟩,
    ⟨8, .letOp (.primitive .byteBuilderAppend [.local 2, .local 7]) 8⟩,
    ⟨9, .letOp (.primitive .byteBuilderFreeze [.local 8]) 9⟩,
    ⟨10, .ret (.local 9)⟩,
    ⟨7, .letOp (.primitive .natDiv [.local 1, .literal (.nat 4294967296)]) 11⟩,
    ⟨8, .letOp (.primitive .byteBuilderAppend [.local 2, .local 4]) 12⟩,
    ⟨9, .tailCall 98 [.local 6, .local 7, .local 8]⟩] }

/-- `Ixby.Runtime.wireFromLoop`, private function 99. -/
def Ixby_Runtime_wireFromLoop : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .word32Eq [.local 1, .literal (.word32 0)]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .ret (.local 2)⟩,
    ⟨4, .letOp (.primitive .word32Sub [.local 1, .literal (.word32 1)]) 4⟩,
    ⟨5, .letOp (.primitive .bytesGet [.local 0, .local 4]) 5⟩,
    ⟨6, .letOp (.primitive .word32ToNat [.local 5]) 6⟩,
    ⟨7, .letOp (.primitive .natMul [.local 2, .literal (.nat 256)]) 7⟩,
    ⟨8, .letOp (.primitive .natAdd [.local 6, .local 7]) 8⟩,
    ⟨9, .tailCall 99 [.local 0, .local 4, .local 8]⟩] }

/-- `MultiStark.Verify.Codec.Wire.encode`, private function 100. -/
def MultiStark_Verify_Codec_Wire_encode : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .byteBuilderEmpty []) 1⟩,
    ⟨3, .letOp (.construct 2 [.local 2]) 2⟩,
    ⟨4, .letOp (.project (.local 0) 0) 3⟩,
    ⟨5, .letOp (.project (.local 0) 1) 4⟩,
    ⟨6, .letOp (.project (.local 0) 2) 5⟩,
    ⟨7, .letOp (.construct 5 [.local 3, .local 4, .local 5, .local 6]) 6⟩,
    ⟨8, .letOp (.apply (.local 1) [.local 7]) 7⟩,
    ⟨9, .caseCtor (.local 8) [⟨6, 8⟩, ⟨7, 9⟩]⟩,
    ⟨10, .ret (.local 8)⟩,
    ⟨10, .letOp (.project (.local 9) 1) 10⟩,
    ⟨11, .letOp (.project (.local 10) 0) 11⟩,
    ⟨12, .letOp (.call 51 [.local 11]) 12⟩,
    ⟨13, .letOp (.primitive .bytesLength [.local 12]) 13⟩,
    ⟨14, .letOp (.primitive .word32ToNat [.local 13]) 14⟩,
    ⟨15, .letOp (.construct 0 [.local 12, .local 14]) 15⟩,
    ⟨16, .letOp (.construct 7 [.local 15]) 16⟩,
    ⟨17, .ret (.local 16)⟩] }

/-- `MultiStark.Verify.Codec.Wire.writeBytes`, private function 101. -/
def MultiStark_Verify_Codec_Wire_writeBytes : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.project (.local 1) 0) 1⟩,
    ⟨3, .letOp (.call 58 [.erased, .local 2]) 2⟩,
    ⟨4, .letOp (.call 58 [.erased, .local 0]) 3⟩,
    ⟨5, .letOp (.primitive .natAdd [.local 3, .local 4]) 4⟩,
    ⟨6, .letOp (.project (.local 1) 1) 5⟩,
    ⟨7, .letOp (.primitive .natLt [.local 6, .local 5]) 6⟩,
    ⟨8, .branch (.local 7) 7 8⟩,
    ⟨8, .letOp (.construct 8 []) 9⟩,
    ⟨8, .caseCtor (.local 2) [⟨0, 11⟩, ⟨1, 12⟩, ⟨2, 13⟩]⟩,
    ⟨9, .letOp (.construct 6 [.local 8]) 10⟩,
    ⟨10, .ret (.local 9)⟩,
    ⟨10, .letOp (.call 74 [.local 2, .local 0]) 14⟩,
    ⟨9, .letOp (.call 74 [.local 2, .local 0]) 21⟩,
    ⟨9, .letOp (.call 51 [.local 0]) 28⟩,
    ⟨11, .letOp (.project (.local 1) 2) 15⟩,
    ⟨12, .letOp (.project (.local 1) 3) 16⟩,
    ⟨13, .letOp (.construct 5 [.local 10, .local 6, .local 11, .local 12]) 17⟩,
    ⟨14, .letOp (.construct 9 []) 18⟩,
    ⟨15, .letOp (.construct 10 [.local 14, .local 13]) 19⟩,
    ⟨16, .letOp (.construct 7 [.local 15]) 20⟩,
    ⟨17, .ret (.local 16)⟩,
    ⟨10, .letOp (.project (.local 1) 2) 22⟩,
    ⟨11, .letOp (.project (.local 1) 3) 23⟩,
    ⟨12, .letOp (.construct 5 [.local 9, .local 6, .local 10, .local 11]) 24⟩,
    ⟨13, .letOp (.construct 9 []) 25⟩,
    ⟨14, .letOp (.construct 10 [.local 13, .local 12]) 26⟩,
    ⟨15, .letOp (.construct 7 [.local 14]) 27⟩,
    ⟨16, .ret (.local 15)⟩,
    ⟨10, .letOp (.primitive .byteBuilderAppend [.local 8, .local 9]) 29⟩,
    ⟨11, .letOp (.construct 2 [.local 10]) 30⟩,
    ⟨12, .letOp (.project (.local 1) 2) 31⟩,
    ⟨13, .letOp (.project (.local 1) 3) 32⟩,
    ⟨14, .letOp (.construct 5 [.local 11, .local 6, .local 12, .local 13]) 33⟩,
    ⟨15, .letOp (.construct 9 []) 34⟩,
    ⟨16, .letOp (.construct 10 [.local 15, .local 14]) 35⟩,
    ⟨17, .letOp (.construct 7 [.local 16]) 36⟩,
    ⟨18, .ret (.local 17)⟩] }

/-- `MultiStark.Verify.Codec.Wire.littleEndian`, private function 102. -/
def MultiStark_Verify_Codec_Wire_littleEndian : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToWord32 [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .word32ToBytes [.local 3]) 3⟩,
    ⟨5, .letOp (.primitive .natLt [.local 0, .literal (.nat 5)]) 4⟩,
    ⟨6, .branch (.local 5) 5 6⟩,
    ⟨6, .letOp (.primitive .bytesSlice [.local 4, .literal (.word32 0), .local 2]) 7⟩,
    ⟨6, .letOp (.primitive .natSub [.local 0, .literal (.nat 4)]) 9⟩,
    ⟨7, .letOp (.construct 0 [.local 6, .local 0]) 8⟩,
    ⟨8, .ret (.local 7)⟩,
    ⟨7, .letOp (.primitive .natDiv [.local 1, .literal (.nat 4294967296)]) 10⟩,
    ⟨8, .letOp (.primitive .byteBuilderEmpty []) 11⟩,
    ⟨9, .letOp (.primitive .byteBuilderAppend [.local 8, .local 4]) 12⟩,
    ⟨10, .letOp (.call 98 [.local 6, .local 7, .local 9]) 13⟩,
    ⟨11, .letOp (.construct 0 [.local 10, .local 0]) 14⟩,
    ⟨12, .ret (.local 11)⟩] }

/-- `MultiStark.Verify.Codec.Wire.fromLittleEndian`, private function 103. -/
def MultiStark_Verify_Codec_Wire_fromLittleEndian : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.call 51 [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .bytesLength [.local 1]) 2⟩,
    ⟨3, .letOp (.primitive .word32Eq [.local 2, .literal (.word32 4)]) 3⟩,
    ⟨4, .branch (.local 3) 4 5⟩,
    ⟨4, .letOp (.primitive .bytesSlice [.local 1, .literal (.word32 0), .literal (.word32 4)]) 6⟩,
    ⟨4, .letOp (.primitive .word32Eq [.local 2, .literal (.word32 8)]) 9⟩,
    ⟨5, .letOp (.primitive .bytesToWord32 [.local 4]) 7⟩,
    ⟨6, .letOp (.primitive .word32ToNat [.local 5]) 8⟩,
    ⟨7, .ret (.local 6)⟩,
    ⟨5, .branch (.local 4) 10 11⟩,
    ⟨5, .letOp (.primitive .bytesSlice [.local 1, .literal (.word32 4), .literal (.word32 4)]) 12⟩,
    ⟨5, .tailCall 99 [.local 1, .local 2, .literal (.nat 0)]⟩,
    ⟨6, .letOp (.primitive .bytesToWord32 [.local 5]) 13⟩,
    ⟨7, .letOp (.primitive .word32ToNat [.local 6]) 14⟩,
    ⟨8, .letOp (.primitive .natMul [.local 7, .literal (.nat 4294967296)]) 15⟩,
    ⟨9, .letOp (.primitive .bytesSlice [.local 1, .literal (.word32 0), .literal (.word32 4)]) 16⟩,
    ⟨10, .letOp (.primitive .bytesToWord32 [.local 9]) 17⟩,
    ⟨11, .letOp (.primitive .word32ToNat [.local 10]) 18⟩,
    ⟨12, .letOp (.primitive .natAdd [.local 11, .local 8]) 19⟩,
    ⟨13, .ret (.local 12)⟩] }

/-- `MultiStark.Verify.Codec.Wire.writeByte`, private function 104. -/
def MultiStark_Verify_Codec_Wire_writeByte : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .word32ToBytes [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .bytesSlice [.local 2, .literal (.word32 0), .literal (.word32 1)]) 2⟩,
    ⟨4, .letOp (.construct 0 [.local 3, .literal (.nat 1)]) 3⟩,
    ⟨5, .tailCall 101 [.local 4, .local 1]⟩] }

/-- `MultiStark.Verify.Codec.Wire.readField`, private function 105. -/
def MultiStark_Verify_Codec_Wire_readField : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .letOp (.call 97 [.literal (.nat 8), .local 0]) 1⟩,
    ⟨2, .caseCtor (.local 1) [⟨6, 2⟩, ⟨7, 3⟩]⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨3, .letOp (.project (.local 2) 0) 4⟩,
    ⟨4, .letOp (.call 51 [.local 3]) 5⟩,
    ⟨5, .letOp (.primitive .bytesSlice [.local 4, .literal (.word32 4), .literal (.word32 4)]) 6⟩,
    ⟨6, .letOp (.primitive .bytesToWord32 [.local 5]) 7⟩,
    ⟨7, .letOp (.primitive .word32Lt [.local 6, .literal (.word32 4294967295)]) 8⟩,
    ⟨8, .branch (.local 7) 9 10⟩,
    ⟨8, .letOp (.primitive .bytesToField [.local 4]) 11⟩,
    ⟨8, .letOp (.primitive .bytesSlice [.local 4, .literal (.word32 0), .literal (.word32 4)]) 16⟩,
    ⟨9, .letOp (.primitive .fieldToNat [.local 8]) 12⟩,
    ⟨10, .letOp (.project (.local 2) 1) 13⟩,
    ⟨11, .letOp (.construct 10 [.local 9, .local 10]) 14⟩,
    ⟨12, .letOp (.construct 7 [.local 11]) 15⟩,
    ⟨13, .ret (.local 12)⟩,
    ⟨9, .letOp (.primitive .bytesToWord32 [.local 8]) 17⟩,
    ⟨10, .letOp (.primitive .word32Eq [.local 9, .literal (.word32 0)]) 18⟩,
    ⟨11, .branch (.local 10) 19 20⟩,
    ⟨11, .letOp (.primitive .bytesToField [.local 4]) 21⟩,
    ⟨11, .letOp (.construct 11 []) 26⟩,
    ⟨12, .letOp (.primitive .fieldToNat [.local 11]) 22⟩,
    ⟨13, .letOp (.project (.local 2) 1) 23⟩,
    ⟨14, .letOp (.construct 10 [.local 12, .local 13]) 24⟩,
    ⟨15, .letOp (.construct 7 [.local 14]) 25⟩,
    ⟨16, .ret (.local 15)⟩,
    ⟨12, .letOp (.construct 6 [.local 11]) 27⟩,
    ⟨13, .ret (.local 12)⟩] }

/-- `MultiStark.Verify.Codec.Wire.writeField`, private function 106. -/
def MultiStark_Verify_Codec_Wire_writeField : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .fieldToBytes [.local 2]) 2⟩,
    ⟨4, .letOp (.construct 0 [.local 3, .literal (.nat 8)]) 3⟩,
    ⟨5, .tailCall 101 [.local 4, .local 1]⟩] }

/-- `Array.instDecidableEqImpl._at_.MultiStark.Verify.Codec.Wire.canonicalize.spec_0`, private function 107. -/
def Array_instDecidableEqImpl__at__MultiStark_Verify_Codec_Wire_canonicalize_spec_0 : Function := {
  arity := 2
  entry := 0
  blocks := #[
    ⟨2, .letOp (.call 51 [.local 0]) 1⟩,
    ⟨3, .letOp (.call 51 [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive .bytesEq [.local 2, .local 3]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

/-- `Ixby.Runtime.rowBytesLoop`, private function 108. -/
def Ixby_Runtime_rowBytesLoop : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.primitive .natLt [.local 1, .local 2]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.primitive .arrayGet [.local 0, .local 1]) 4⟩,
    ⟨5, .letOp (.primitive .byteBuilderFreeze [.local 3]) 9⟩,
    ⟨6, .letOp (.primitive .natToField [.local 5]) 5⟩,
    ⟨7, .letOp (.primitive .fieldToBytes [.local 6]) 6⟩,
    ⟨8, .letOp (.primitive .byteBuilderAppend [.local 3, .local 7]) 7⟩,
    ⟨9, .letOp (.primitive .natAdd [.local 1, .literal (.nat 1)]) 8⟩,
    ⟨10, .tailCall 108 [.local 0, .local 9, .local 2, .local 8]⟩,
    ⟨6, .ret (.local 5)⟩] }

/-- `MultiStark.Verify.Mmcs.hashRow`, private function 109. -/
def MultiStark_Verify_Mmcs_hashRow : Function := {
  arity := 1
  entry := 0
  blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩,
    ⟨3, .caseCtor .erased []⟩,
    ⟨2, .letOp (.primitive .arrayLength [.local 1]) 4⟩,
    ⟨2, .caseCtor .erased []⟩,
    ⟨3, .letOp (.primitive .byteBuilderEmpty []) 5⟩,
    ⟨4, .letOp (.call 108 [.local 1, .literal (.nat 0), .local 2, .local 3]) 6⟩,
    ⟨5, .letOp (.primitive .blake3 [.local 4]) 7⟩,
    ⟨6, .letOp (.construct 0 [.local 5, .literal (.nat 32)]) 8⟩,
    ⟨7, .ret (.local 6)⟩] }

/-- `Ixby.Runtime.wireNatRange`, private function 110. -/
def Ixby_Runtime_wireNatRange : Function := {
  arity := 4
  entry := 0
  blocks := #[
    ⟨4, .letOp (.primitive .natLt [.local 1, .local 3]) 1⟩,
    ⟨5, .branch (.local 4) 2 3⟩,
    ⟨5, .letOp (.call 102 [.local 0, .local 1]) 4⟩,
    ⟨5, .letOp (.construct 12 []) 5⟩,
    ⟨6, .tailCall 101 [.local 5, .local 2]⟩,
    ⟨6, .letOp (.construct 6 [.local 5]) 6⟩,
    ⟨7, .ret (.local 6)⟩] }

/-- `MultiStark.Verify.Codec.Wire.writeNat`, private function 111. -/
def MultiStark_Verify_Codec_Wire_writeNat : Function := {
  arity := 3
  entry := 0
  blocks := #[
    ⟨3, .letOp (.primitive .natEq [.local 0, .literal (.nat 2)]) 1⟩,
    ⟨4, .branch (.local 3) 2 3⟩,
    ⟨4, .tailCall 110 [.local 0, .local 1, .local 2, .literal (.nat 65536)]⟩,
    ⟨4, .letOp (.primitive .natEq [.local 0, .literal (.nat 8)]) 4⟩,
    ⟨5, .branch (.local 4) 5 6⟩,
    ⟨5, .tailCall 110 [.local 0, .local 1, .local 2, .literal (.nat 18446744073709551616)]⟩,
    ⟨5, .letOp (.primitive .natEq [.local 0, .literal (.nat 1)]) 7⟩,
    ⟨6, .branch (.local 5) 8 9⟩,
    ⟨6, .tailCall 110 [.local 0, .local 1, .local 2, .literal (.nat 256)]⟩,
    ⟨6, .letOp (.primitive .natEq [.local 0, .literal (.nat 4)]) 10⟩,
    ⟨7, .branch (.local 6) 11 12⟩,
    ⟨7, .tailCall 110 [.local 0, .local 1, .local 2, .literal (.nat 4294967296)]⟩,
    ⟨7, .letOp (.primitive .natMul [.literal (.nat 8), .local 0]) 13⟩,
    ⟨8, .letOp (.call 20 [.literal (.nat 2), .local 7]) 14⟩,
    ⟨9, .tailCall 110 [.local 0, .local 1, .local 2, .local 8]⟩] }

def wireEntries : Array Entry := #[
  ⟨98, `Ixby.Runtime.wireLittleLoop, Ixby_Runtime_wireLittleLoop⟩,
  ⟨99, `Ixby.Runtime.wireFromLoop, Ixby_Runtime_wireFromLoop⟩,
  ⟨100, `MultiStark.Verify.Codec.Wire.encode, MultiStark_Verify_Codec_Wire_encode⟩,
  ⟨101, `MultiStark.Verify.Codec.Wire.writeBytes, MultiStark_Verify_Codec_Wire_writeBytes⟩,
  ⟨102, `MultiStark.Verify.Codec.Wire.littleEndian, MultiStark_Verify_Codec_Wire_littleEndian⟩,
  ⟨103, `MultiStark.Verify.Codec.Wire.fromLittleEndian, MultiStark_Verify_Codec_Wire_fromLittleEndian⟩,
  ⟨104, `MultiStark.Verify.Codec.Wire.writeByte, MultiStark_Verify_Codec_Wire_writeByte⟩,
  ⟨105, `MultiStark.Verify.Codec.Wire.readField, MultiStark_Verify_Codec_Wire_readField⟩,
  ⟨106, `MultiStark.Verify.Codec.Wire.writeField, MultiStark_Verify_Codec_Wire_writeField⟩,
  ⟨107, `Array.instDecidableEqImpl._at_.MultiStark.Verify.Codec.Wire.canonicalize.spec_0, Array_instDecidableEqImpl__at__MultiStark_Verify_Codec_Wire_canonicalize_spec_0⟩,
  ⟨108, `Ixby.Runtime.rowBytesLoop, Ixby_Runtime_rowBytesLoop⟩,
  ⟨109, `MultiStark.Verify.Mmcs.hashRow, MultiStark_Verify_Mmcs_hashRow⟩,
  ⟨110, `Ixby.Runtime.wireNatRange, Ixby_Runtime_wireNatRange⟩,
  ⟨111, `MultiStark.Verify.Codec.Wire.writeNat, MultiStark_Verify_Codec_Wire_writeNat⟩]

end Compilatrix.Ixby.Runtime.Native.Code
