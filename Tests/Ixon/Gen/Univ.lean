import Ix.Ixon
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import LSpec.SlimCheck.Gen
import LSpec

import Tests.Ixon.Gen.Common

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

def genUniv : SlimCheck.Gen Ixon.Univ := getSize >>= go
  where
    go : Nat -> SlimCheck.Gen Ixon.Univ
    | 0 => return .const 0
    | Nat.succ f =>
      frequency [
        (100, .const <$> genUInt64),
        (100, .var <$> genUInt64),
        (50, .add <$> genUInt64 <*> go f),
        (25, .max <$> go f <*> go f),
        (25, .imax <$> go f <*> go f)
      ]

instance : Shrinkable Univ where
  shrink _ := []

instance : SampleableExt Univ := SampleableExt.mkSelfContained genUniv
