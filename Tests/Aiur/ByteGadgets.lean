/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ByteLookups

/-! Exhaustive comparison with the actual Rust preprocessed byte-chip rows,
lookup arguments and multiplicity columns. The component gate exports its
native file into a temporary directory before running this comparison. -/

open Aiur Aiur.AIR

namespace Tests.Aiur.ByteGadgets

private def appendNat (bytes : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  for index in [:8] do
    bytes := bytes.push ((value >>> (8 * index)) % 256).toUInt8
  return bytes

private def appendValues (bytes : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun bytes value => appendNat bytes value.n) bytes

private def byte1Snapshot (bytes : ByteArray) : ByteArray := Id.run do
  let mut bytes := appendNat (appendNat (appendNat bytes 256) 11) 3
  for width in [10, 3, 3] do bytes := appendNat bytes width
  for index in [:256] do
    if h : index < 256 then
      let row : Fin 256 := ⟨index, h⟩
      bytes := appendValues bytes (byte1Preprocessed row).toList
      for (kind, column) in Byte1Kind.all.zipIdx do
        bytes := appendNat bytes (gSize.toNat - (column + 17))
        bytes := appendValues bytes (byte1Request kind (G.ofNat index) (byte1Outputs kind row))
  return bytes

private def byte2Snapshot (bytes : ByteArray) : ByteArray := Id.run do
  let mut bytes := appendNat (appendNat (appendNat bytes 65536) 14) 10
  for width in [4, 4, 4, 4, 4, 4, 3, 5, 5, 5] do bytes := appendNat bytes width
  for index in [:65536] do
    if h : index < 65536 then
      let row : Fin 65536 := ⟨index, h⟩
      let inputs := byteRangeMessage row
      bytes := appendValues bytes (byte2Preprocessed row).toList
      for (kind, column) in Byte2Kind.all.zipIdx do
        bytes := appendNat bytes (gSize.toNat - (column + 17))
        bytes := appendValues bytes (byte2Request kind inputs.1 inputs.2 (byte2Outputs kind row))
  return bytes

private def expected : ByteArray :=
  byte2Snapshot (byte1Snapshot "Aiur byte gadgets v1\n".toUTF8)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected native byte-gadget snapshot path")
  let native ← IO.FS.readBinFile path
  let reference := expected
  unless native == reference do
    let mut first : Option Nat := none
    for index in [:min native.size reference.size] do
      if native[index]! != reference[index]! then
        first := some index
        break
    throw (IO.userError s!"Byte gadget snapshot differs: native {native.size} bytes, reference {reference.size}; first mismatch {first}")
  IO.println s!"Byte gadgets: all 65,792 rows, 656,128 lookup messages and multiplicity columns match ({native.size} bytes)."

end Tests.Aiur.ByteGadgets

def main := Tests.Aiur.ByteGadgets.main
