import Compilatrix.Aiur.Wire.Records

/-! Canonical framed ingress. Limits are consumer policy, outside identity;
decoding establishes representation only, not well-formedness or execution. -/

namespace Compilatrix.Aiur.Wire

open _root_.Aiur.Bytecode
open Compilatrix.Ixon
open Compilatrix.IxIR

def preimage (value : Toplevel) : ByteArray := header ++ toplevelBytes value

def address (value : Toplevel) : Address := Address.blake3 (preimage value)

def getPreimage (limits : Limits) : GetM Toplevel := do
  Decode.expectBytes header
  getToplevel limits

def Fits (limits : Limits) (value : Toplevel) : Prop :=
  (preimage value).size ≤ limits.maxBytes ∧ toplevelFits limits value = true

def decode (limits : Limits) (bytes : ByteArray) : Except String Toplevel :=
  Bounded.run limits.toLimits (getPreimage limits) preimage (toplevelFits limits) bytes

structure Encoded (limits : Limits) (value : Toplevel) where
  bytes : ByteArray
  exact : bytes = preimage value
  fits : Fits limits value

def encodeChecked (limits : Limits) (value : Toplevel) : Except String (Encoded limits value) := do
  if shape : toplevelFits limits value then
    let bytes := preimage value
    if size : bytes.size ≤ limits.maxBytes then return ⟨bytes, rfl, size, shape⟩
    else throw "Aiur bytecode: encoded byte limit"
  else throw "Aiur bytecode: representation limit"

structure Addressed (limits : Limits) (bytes : ByteArray) (root : Address) where
  value : Toplevel
  decoded : decode limits bytes = .ok value
  identity : address value = root

def decodeAddressed (limits : Limits) (bytes : ByteArray) (root : Address) :
    Except String (Addressed limits bytes root) := do
  match decoded : decode limits bytes with
  | .error message => throw message
  | .ok value =>
      if identity : address value = root then return ⟨value, decoded, identity⟩
      else throw "Aiur bytecode: content root mismatch"

end Compilatrix.Aiur.Wire
