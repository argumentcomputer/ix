import Tests.Common

open LSpec SlimCheck Gen

namespace Tests.Unsigned

scoped instance (priority := high) : SampleableExt Nat :=
  SampleableExt.mkSelfContained $ choose Nat 0 (UInt128.size - 1)

instance : Shrinkable UInt128 where
  shrink x := Shrinkable.shrink x.toNat |>.map UInt128.ofNatWrap

instance : SampleableExt UInt128 :=
  SampleableExt.mkSelfContained genUInt128

def suite := [
    check "UInt128 to/from Nat roundtrips" (∀ n : Nat, (UInt128.ofNatWrap n).toNat = n),
    check "UInt128 cmp matches Nat cmp" (∀ a b : UInt128, compare a b = compare a.toNat b.toNat),
  ]

end Tests.Unsigned
