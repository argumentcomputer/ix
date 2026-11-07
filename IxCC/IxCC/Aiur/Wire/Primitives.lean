import IxCC.Aiur.Field
import IxCC.IxIR.Bounded

/-! Scalar and collection spellings for `aiur-bytecode/1`. Naturals and
lengths use the existing canonical unsigned LEB128 grammar; field elements
are exactly eight little-endian bytes and must be below the characteristic.
Reader limits are external to the encoded identity. -/

namespace IxCC.Aiur.Wire

open _root_.IxCC.Vendor.Aiur (G gSize)
open IxCC.Ixon
open IxCC.IxIR

structure Limits extends Bounded.Limits where
  maxDepth : Nat := 128
  deriving Repr, Inhabited

def revision : String := "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03"

def header : ByteArray :=
  Encoding.domain "aiur-bytecode/1\x00" ++ Encoding.string revision

def fieldBytes (value : G) : ByteArray := u64LEBytes value.val 8

def getField : GetM G := do
  let word := u64OfLEBytes (← getBytes 8)
  if bounded : word < gSize then return ⟨word, bounded⟩
  else throw "Aiur field: noncanonical representative"

def optionBytes (encode : α → ByteArray) : Option α → ByteArray
  | none => Encoding.tag 0
  | some value => Encoding.tag 1 ++ encode value

def optionFits (fits : α → Bool) : Option α → Bool
  | none => true
  | some value => fits value

def getOptionTag (read : GetM α) : UInt8 → GetM (Option α)
  | 0 => pure none
  | 1 => some <$> read
  | _ => throw "Aiur option: invalid tag"

def getOption (read : GetM α) : GetM (Option α) := do
  getOptionTag read (← getU8)

def natArrayBytes (values : Array Nat) : ByteArray := Encoding.array Encoding.nat values

def natArrayFits (limits : Bounded.Limits) (values : Array Nat) : Bool :=
  Bounded.arrayFits limits (Bounded.natFits limits) values

def getNatArray (limits : Bounded.Limits) : GetM (Array Nat) :=
  Bounded.getArray limits (Bounded.getNat limits)

end IxCC.Aiur.Wire
