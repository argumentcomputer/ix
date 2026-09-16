module
public import Tests.Ix.IxonV3

public section
namespace Tests.IxonV3
open Ixon

@[extern "rs_roundtrip_ixon_expr"] opaque roundtripExpr : @& Expr → Expr
@[extern "rs_roundtrip_ixon_constant"] opaque roundtripConstant : @& Constant → Constant
@[extern "rs_eq_expr_serialization"] opaque equalExprBytes : @& Expr → @& ByteArray → Bool
@[extern "rs_eq_constant_serialization"] opaque equalConstantBytes : @& Constant → @& ByteArray → Bool
@[extern "rs_expr_hash_matches"] opaque equalSharingHash : @& Expr → @& Address → Bool

def runFFI (cases : List ExprCase) : IO Nat := do
  let mut checks := 0
  for ⟨name, expr, _⟩ in cases do
    unless roundtripExpr expr == expr do
      throw <| IO.userError s!"{name}: FFI roundtrip differs"
    unless equalExprBytes expr (runPut (putExpr expr)) do
      throw <| IO.userError s!"{name}: Lean/Rust bytes differ"
    unless equalSharingHash expr (Ix.Sharing.computeExprHash expr) do
      throw <| IO.userError s!"{name}: Lean/Rust sharing hash differs"
    checks := checks + 3
  let typ := Expr.all ⟨.linear, .localUnique⟩ .localShared (.sort 0) (.sort 0)
  let value := lambdaTelescope
  let ctor : Constructor := ⟨true, 5, 1, 2, 3, typ⟩
  let ind : Inductive := ⟨false, 5, 2, 3, typ, #[ctor]⟩
  let recr : Recursor := ⟨true, false, 5, 1, 2, 3, 4, typ, #[⟨3, value⟩]⟩
  let defn : Definition := ⟨.opaq, .part, 5, typ, value⟩
  let infos : Array (String × ConstantInfo) := #[
    ("definition", .defn defn), ("recursor", .recr recr),
    ("axiom", .axio ⟨true, 5, typ⟩), ("quotient", .quot ⟨.lift, 5, typ⟩),
    ("mutual", .muts #[.defn defn, .indc ind, .recr recr])]
  for (name, info) in infos do
    let c : Constant := ⟨info, #[value], #[], #[.zero]⟩
    unless roundtripConstant c == c do
      throw <| IO.userError s!"{name}: declaration FFI roundtrip differs"
    unless equalConstantBytes c (serConstant c) do
      throw <| IO.userError s!"{name}: declaration Lean/Rust bytes differ"
    checks := checks + 2
  return checks

end Tests.IxonV3
