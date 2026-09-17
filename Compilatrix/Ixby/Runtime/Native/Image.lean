import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.Native.WireCertificate

namespace Compilatrix.Ixby.LeanFrontend

open Lean Ix.Ixby Runtime.Native

private def Image.checkSymbols (image : Image) (entries : Array Code.Entry)
    (constructors : Array (Name × CtorDecl)) : Except String Unit := do
  for entry in entries do
    unless image.state.functionNames[entry.name]? == some entry.id do
      throw s!"native runtime name binding differs: {entry.name}"
    unless (image.state.functions[entry.id]?).map (·.name) == some entry.name do
      throw s!"native runtime slot binding differs: {entry.name}"
  for ((name, _), index) in constructors.zipIdx do
    unless image.state.constructorNames[name]? == some index do
      throw s!"native runtime constructor binding differs: {name}"

/-- All 97 current scalar, collection, and field helpers are checked against
their full contracts before a typed runtime image is exported. -/
def Image.certifyRuntime (image : Image) : Except String (Certificate image.program) := do
  image.checkSymbols Code.entries Code.constructors
  certify image.program

/-- Wire checking also binds the source-reader call target. Its LCNF body is
outside the native helper theorem and retains the frontend's stated boundary. -/
def Image.certifyWireRuntime (image : Image) : Except String (WireCertificate image.program) := do
  image.checkSymbols (Code.entries ++ Code.wireEntries) wireConstructors
  unless image.state.functionNames[`MultiStark.Verify.Codec.Wire.readBytes]? == some 97 do
    throw "native wire reader binding differs"
  certifyWire image.program

theorem Image.number_decode_roundtrip_v2 (image : Image) (n : Nat) :
    (image.number n).bind image.decodeNumber = .ok n := rfl

theorem Image.word_decode_roundtrip_v2 (image : Image) (word : UInt32) :
    image.decodeWord (image.word word) = .ok word := rfl

theorem Image.nat_word_distinct (image : Image) (word : UInt32) :
    image.decodeNumber (image.word word) = .error "typed Ixby output is not a Nat scalar" := rfl

end Compilatrix.Ixby.LeanFrontend
