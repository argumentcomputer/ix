import Ix.Meta
import Ix.PrimAddrs
import Ix.SpecDigest
import Tests.Ix.Kernel.PrimitiveTable
import LSpec

open LSpec

namespace Tests.Ix.Kernel.PrimAddrs

def specDigestParity : TestSeq :=
  .individualIO "KernelRoleSpec.aiur spec_digest matches Ix.SpecDigest.specDigest" none (do
    let source ← IO.FS.readFile "IxVM/IxVM/Modules/KernelRoleSpec.aiur"
    let .ok digest := Ix.SpecDigest.specDigest
      | return (false, 0, 1, some "Ix.SpecDigest.specDigest failed")
    let expected := ", ".intercalate (digest.hash.data.toList.map fun b => s!"UInt8::BYTE_{b.toNat}")
    let ok := (source.splitOn expected).length > 1
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"KernelRoleSpec.aiur did not contain {expected}")) .done

def suite : List TestSeq := [specDigestParity] ++ Tests.Ix.Kernel.PrimitiveTable.suite

end Tests.Ix.Kernel.PrimAddrs
