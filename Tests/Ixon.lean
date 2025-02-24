import LSpec
import Ix.Ixon
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

def genUInt64 : Gen UInt64 :=
  UInt64.ofNat <$> choose Nat 0 0xFFFFFFFFFFFFFFFF


def frequency' (default: Gen A) (xs: List (Nat × Gen A)) : Gen A := do
  let n ← choose Nat 0 total
  pick n xs
  where
    total := List.sum (Prod.fst <$> xs)
    pick n xs := match xs with
    | [] => default
    | (k,x)::xs => if n <= k then x else pick (n - k) xs

def frequency [Inhabited A] (xs: List (Nat × Gen A)) : Gen A := do
  frequency' (Prod.snd <| xs.get! 0) xs

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

def genAdr : SlimCheck.Gen Address := 
  pure (Address.mk (Blake3.hash "foobar".toUTF8).val)

-- TODO: Bias char distribution towards ASCII to be more useful
def genChar : SlimCheck.Gen Char :=
  Char.ofNat <$> (choose Nat 0 0xd800)

def genString : SlimCheck.Gen String := do
  let cs ← listOf genChar
  return String.mk cs

def listOf' (n: Gen α) : Gen (List α) := resize (· / 2) $ listOf n

def genExpr : SlimCheck.Gen Ixon.Expr := getSize >>= go
  where
    go : Nat -> SlimCheck.Gen Ixon.Expr
    | 0 => return .vari 0
    | Nat.succ f =>
      frequency [
        (100, .vari <$> genUInt64),
        (100, .sort <$> genUniv),
        (100, .cnst <$> genAdr <*> listOf' genUniv),
        (100, .rec_ <$> genUInt64 <*> listOf' genUniv),
        (30, .apps <$> go f <*> go f <*> listOf' (go f)),
        (30, .lams <$> listOf' (go f) <*> go f),
        (30, .alls <$> listOf' (go f) <*> go f),
        (30, .let_ <$> go f <*> go f <*> go f),
        (50, .proj <$> genUInt64 <*> go f),
        (100, .strl <$> genString),
        (100, .natl <$> chooseAny Nat)
      ]

instance : Shrinkable Expr where
  shrink _ := []

instance : SampleableExt Expr := SampleableExt.mkSelfContained genExpr

def serde [Serialize A] [BEq A] (x: A) : Bool :=
  match Serialize.get (Serialize.put x) with
  | .ok (y : A) => x == y
  | _ => false

--def myConfig : SlimCheck.Configuration where
--  maxSize := 100
--  traceDiscarded := true
--  traceSuccesses := true
--  traceShrink := true
--  traceShrinkCandidates := true

def main : IO UInt32 := do
  let _ <- lspecIO $ check "universe serde" (∀ x : Univ, serde x)
  let _ <- lspecIO $ check "expr serde" (∀ x : Expr, serde x)
--  SlimCheck.Checkable.check (∀ x: Expr, serde x) myConfig
  return 0
