import LSpec
import Tests.Common

open LSpec SlimCheck Gen

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

/- Suite -/

def Tests.FFIConsistency.suite := [
    check "Boxed UInt32s are unboxed correctly in Rust"
      (∀ arr : Array UInt32, boxedUInt32sAreEquivalentToBytes arr (arrayUInt32sToBytes arr)),
  ]
