module
public import LSpec
public import Ix.PrimAddrs

/-! Exact ordered Lean/Rust primitive-table equality using the shared
address-only table. -/

namespace Tests.Ix.Kernel.PrimitiveTable
open LSpec _root_.Ix

@[extern "rs_prim_addrs_canonical"]
private opaque rsPrimAddrsCanonicalFFI : IO (Array (String × String))

def primsParity : Spec :=
  it "PrimAddrs.canonical parity vs Rust PrimAddrs::new()" do
    let rust ← rsPrimAddrsCanonicalFFI
    let lean := PrimAddrs.leanParityTable
    expect (rust.size == lean.size) s!"size mismatch: rust {rust.size} vs lean {lean.size}"
    let mut bad : Array String := #[]
    for ((rn, rh), (ln, la)) in rust.zip lean do
      if rn != ln then
        bad := bad.push s!"order mismatch: {rn} vs {ln}"
      else if toString la != rh then
        bad := bad.push s!"{rn}: rust {rh} != lean {toString la}"
    expect bad.isEmpty (String.intercalate "; " bad.toList)

public def suite : LSpec.Spec := do
  primsParity

end Tests.Ix.Kernel.PrimitiveTable
