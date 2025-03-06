import LSpec
import Tests.Common
import Ix.Unsigned
import Ix.Binius.Boundary

open LSpec SlimCheck Gen

open Binius

def genBoundary : Gen Boundary := do
  let numValues ← choose Nat 0 128
  let mut values := Array.mkEmpty numValues
  for _ in [:numValues] do
    values := values.push $ ← genUInt128
  let direction := if ← chooseAny Bool then .pull else .push
  pure ⟨values, ⟨← genUSize⟩, direction, ← genUInt64⟩

instance : Shrinkable Boundary where
  shrink _ := []

instance : Repr Boundary where
  reprPrec boundary _ := boundary.toString

instance : SampleableExt Boundary := SampleableExt.mkSelfContained genBoundary

def Tests.Boundary.suite := [
    check "Boundary Lean->Rust mapping matches the deserialized bytes"
      (∀ boundary : Boundary, boundary.isEquivalentToBytes boundary.toBytes),
  ]
