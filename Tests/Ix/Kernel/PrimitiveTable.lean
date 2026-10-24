module
public import LSpec
public import Ix.PrimAddrs

/-! Exact ordered Lean/Rust primitive-table equality retained from
Tests.Ix.Tc.Substrate, using only the Tc-free address table. -/

namespace Tests.Ix.Kernel.PrimitiveTable
open LSpec Ix.Tc

@[extern "rs_prim_addrs_canonical"]
private opaque rsPrimAddrsCanonicalFFI : IO (Array (String × String))

def primsParity : TestSeq :=
  .individualIO "PrimAddrs.canonical parity vs Rust PrimAddrs::new()" none (do
    let rust ← rsPrimAddrsCanonicalFFI
    let lean := PrimAddrs.leanParityTable
    if rust.size != lean.size then
      return (false, rust.size, lean.size,
        some s!"size mismatch: rust {rust.size} vs lean {lean.size}")
    let mut bad : Array String := #[]
    for ((rn, rh), (ln, la)) in rust.zip lean do
      if rn != ln then
        bad := bad.push s!"order mismatch: {rn} vs {ln}"
      else if toString la != rh then
        bad := bad.push s!"{rn}: rust {rh} != lean {toString la}"
    if bad.isEmpty then
      return (true, rust.size, rust.size, none)
    return (false, bad.size, rust.size,
      some (String.intercalate "; " bad.toList))) .done

public def suite : List TestSeq := [primsParity]

end Tests.Ix.Kernel.PrimitiveTable
