import LSpec
import Ix.Binius.ArithExpr
import Ix.UInt128

open LSpec SlimCheck Gen

def genUInt64 : Gen UInt64 :=
  UInt64.ofNat <$> choose Nat 0 0xFFFFFFFFFFFFFFFF

def genUSize : Gen USize :=
  .ofNat <$> choose Nat 0 (2^System.Platform.numBits - 1)

def genUInt128 : Gen UInt128 :=
  .ofHiLo <$> genUInt64 <*> genUInt64

def frequency' (default: Gen α) (xs: List (Nat × Gen α)) : Gen α := do
  let n ← choose Nat 0 total
  pick n xs
  where
    total := List.sum (Prod.fst <$> xs)
    pick n xs := match xs with
    | [] => default
    | (k, x) :: xs => if n <= k then x else pick (n - k) xs

def frequency [Inhabited α] (xs: List (Nat × Gen α)) : Gen α :=
  frequency' xs.head!.snd xs

open Binius

def genArithExpr : Gen ArithExpr := getSize >>= go
  where
    go : Nat → Gen ArithExpr
    | 0 => return .const (.ofNat 0)
    | Nat.succ n =>
      frequency [
        (40, .const <$> genUInt128),
        (40, .var <$> genUSize),
        (25, .add <$> go n <*> go n),
        (25, .mul <$> go n <*> go n),
        (50, .pow <$> go n <*> genUInt64)
      ]

instance : Shrinkable ArithExpr where
  shrink _ := []

instance : Repr ArithExpr where
  reprPrec expr _ := expr.toString

instance : SampleableExt ArithExpr := SampleableExt.mkSelfContained genArithExpr

def main := lspecIO $
  check "ArithExpr Lean->Rust mapping matches the deserialized bytes"
    (∀ expr : ArithExpr, expr.isEquivalentToBytes expr.toBytes)
