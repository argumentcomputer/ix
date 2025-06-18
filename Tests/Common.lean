import LSpec
import Ix.Unsigned

open LSpec SlimCheck Gen

def genUInt8 : Gen UInt8 :=
  UInt8.ofNat <$> choose Nat 0 0xFF

def genUInt32 : Gen UInt32 :=
  UInt32.ofNat <$> choose Nat 0 0xFFFFFFFF

def genUInt64 : Gen UInt64 :=
  UInt64.ofNat <$> choose Nat 0 0xFFFFFFFFFFFFFFFF

def genUSize : Gen USize :=
  .ofNat <$> choose Nat 0 (2^System.Platform.numBits - 1)

def genUInt128 : Gen UInt128 :=
  .ofLoHi <$> genUInt64 <*> genUInt64

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

def oneOf' [Inhabited α] (xs: List (Gen α)) : Gen α :=
  frequency (xs.map (fun x => (100, x)))
