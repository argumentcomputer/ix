import LSpec
import Ix.Ixon
import Ix.Address
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

import Tests.Common
import Tests.Ix.Common
import Tests.Ix.Ixon
import Tests.Ix.IR

open LSpec
open SlimCheck
open SlimCheck.Gen

def myConfig : SlimCheck.Configuration where
  numInst := 10000
  maxSize := 100
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true


def Tests.Ix.suite : List LSpec.TestSeq :=
  [
  ]


def hexVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (UInt8.ofNat (10 + (c.toNat - 'a'.toNat)))
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (UInt8.ofNat (10 + (c.toNat - 'A'.toNat)))
  else
    none

/-- Parse a hexadecimal string like `0xdead_beef_cafe_0123_4567_89ab_cdef` into a `ByteArray`.
Underscores are ignored; `0x`/`0X` prefix is optional. Panics on invalid input. -/
def parseHex (x : String) : ByteArray :=
  -- drop optional 0x/0X
  let x :=
    if x.startsWith "0x" || x.startsWith "0X" then x.drop 2 else x
  -- remove underscores
  let x := String.ofList (x.toList.filter (· ≠ '_'))
  -- must have an even number of hex digits
  if x.length % 2 = 1 then
    panic! "parseHex: odd number of hex digits"
  else
    let n := x.length
    let rec loop (i : Nat) (acc : ByteArray) : ByteArray :=
      if i < n then
        -- safe since ASCII: `String.get!` indexes by chars
        let c1 := String.Pos.Raw.get! x ⟨i⟩ 
        let c2 := String.Pos.Raw.get! x ⟨i+1⟩
        match hexVal? c1, hexVal? c2 with
        | some hi, some lo =>
          let b : UInt8 := (hi <<< 4) ||| lo
          loop (i + 2) (acc.push b)
        | _, _ =>
          panic! s!"parseHex: invalid hex at positions {i}..{i+1}"
      else
        acc
    loop 0 ByteArray.empty

/-- Print a `ByteArray` as a lowercase hex string with a `0x` prefix. -/
def printHex (ba : ByteArray) : String :=
  let hexdigits := "0123456789abcdef"
  let rec go (i : Nat) (acc : String) : String :=
    if h : i < ba.size then
      let b := ba.get! i
      let hi := (b.toNat / 16)
      let lo := (b.toNat % 16)
      let acc := acc.push (String.Pos.Raw.get! hexdigits ⟨hi⟩)
      let acc := acc.push (String.Pos.Raw.get! hexdigits ⟨lo⟩)
      go (i + 1) acc
    else acc
  "0x" ++ go 0 ""

def serde_is [Ixon.Serialize A] [BEq A] (x: A) (expect: String): Bool := Id.run do
  let expected := parseHex expect
  let bytes := Ixon.runPut (Ixon.Serialize.put x)
  if bytes == expected then
    match Ixon.runGet Ixon.Serialize.get bytes with
    | .ok (y : A) => x == y
    | _ => false
  else false

def test_serde [Ixon.Serialize A] [BEq A] [Repr A] (x: A) (expect: String): LSpec.TestSeq :=
  let expected := parseHex expect
  let bytes := Ixon.runPut (Ixon.Serialize.put x)
  let res := if bytes == expected then
    match Ixon.runGet Ixon.Serialize.get bytes with
    | .ok (y : A) => x == y
    | _ => false
    else false
  test s!"serde {repr x} <-> {expect}" res

open Ixon



