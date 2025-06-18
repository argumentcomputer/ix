import LSpec
import Tests.Common
import Ix.Binius.Boundary
import Ix.Archon.ArithExpr
import Ix.Archon.ModuleMode
import Ix.Archon.Transparent

open LSpec SlimCheck Gen

open Archon Binius

/- Array UInt32 -/

def genArrayUInt32 : Gen $ Array UInt32 := do
  let numValues ← choose Nat 1 8
  let mut values := Array.mkEmpty numValues
  for _ in [:numValues] do
    values := values.push $ ← genUInt32
  pure values

@[extern "rs_boxed_u32s_are_equivalent_to_bytes"]
opaque boxedUInt32sAreEquivalentToBytes : @& Array UInt32 → @& ByteArray → Bool

def arrayUInt32sToBytes (arr : Array UInt32) : ByteArray :=
  arr.foldl (init := .mkEmpty (4 * arr.size)) fun acc u => acc ++ u.toLEBytes

instance : Shrinkable (Array UInt32) where
  shrink _ := []

instance : SampleableExt (Array UInt32) := SampleableExt.mkSelfContained genArrayUInt32

/- Boundary -/

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

/- ArithExpr -/

def genArithExpr : Gen ArithExpr := getSize >>= go
  where
    go : Nat → Gen ArithExpr
    | 0 => return .const 0
    | Nat.succ n =>
      frequency [
        (30, .const <$> genUInt128),
        (30, .var <$> genUSize),
        (30, .oracle <$> OracleIdx.mk <$> genUSize),
        (25, .add <$> go n <*> go n),
        (25, .mul <$> go n <*> go n),
        (40, .pow <$> go n <*> genUInt64)
      ]

instance : Shrinkable ArithExpr where
  shrink _ := []

instance : Repr ArithExpr where
  reprPrec expr _ := expr.toString

instance : SampleableExt ArithExpr := SampleableExt.mkSelfContained genArithExpr

/- Transparent -/

def genModuleMode : Gen ModuleMode :=
  frequency [
      (5, pure .inactive),
      (15, .active <$> genUInt8 <*> genUInt64),
    ]

instance : Shrinkable ModuleMode where
  shrink _ := []

instance : Repr ModuleMode where
  reprPrec mode _ := mode.toString

instance : SampleableExt ModuleMode := SampleableExt.mkSelfContained genModuleMode

/- Transparent -/

def genTransparent : Gen Transparent :=
  frequency [
      (10, .const <$> genUInt128),
      (10, pure .incremental),
    ]

instance : Shrinkable Transparent where
  shrink _ := []

instance : Repr Transparent where
  reprPrec transparent _ := transparent.toString

instance : SampleableExt Transparent := SampleableExt.mkSelfContained genTransparent

/- Suite -/

def Tests.FFIConsistency.suite := [
    check "Boxed UInt32s are unboxed correctly in Rust"
      (∀ arr : Array UInt32, boxedUInt32sAreEquivalentToBytes arr (arrayUInt32sToBytes arr)),
    check "ArithExpr Lean->Rust mapping matches the deserialized bytes"
      (∀ expr : ArithExpr, expr.isEquivalentToBytes expr.toBytes),
    check "Boundary Lean->Rust mapping matches the deserialized bytes"
      (∀ boundary : Boundary, boundary.isEquivalentToBytes boundary.toBytes),
    check "ModuleMode Lean->Rust mapping matches the deserialized bytes"
      (∀ moduleMode : ModuleMode, moduleMode.isEquivalentToBytes moduleMode.toBytes),
    check "Transparent Lean->Rust mapping matches the deserialized bytes"
      (∀ transparent : Transparent, transparent.isEquivalentToBytes transparent.toBytes),
  ]
