import Aiur.Modules.Function

/-! # IxVM module `KernelTypes`

The kernel's term representation: levels, literals, expressions and constant info.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelTypes where

aiur_decls⟦
module KernelTypes {
  enum KLevelNode {
      Zero,
      Succ(KLevel),
      Max(KLevel, KLevel),
      IMax(KLevel, KLevel),
      Param(Field)
    }

  type KLevel = &KLevelNode;

  type KLimbs = Lists::List<UInt64::U64>;

  enum KLiteral {
      Nat(KLimbs),
      Str(Bytes::Stream)
    }

  enum KExprNode {
      BVar(Field),
      Srt(KLevel),
      Const(Bytes::AddressRef, Lists::List<KLevel>),
      App(KExpr, KExpr),
      -- A binder carries its datum (D2): a level whose zero-ness is the binder's
      -- `pw` (the binder's codomain sort is zero exactly when the level is).
      Lam(KExpr, KExpr, KLevel),
      Forall(KExpr, KExpr, KLevel),
      Let(KExpr, KExpr, KExpr),
      Lit(KLiteral),
      Proj(Bytes::AddressRef, Field, KExpr)
    }

  type KExpr = &KExprNode;

  enum KRecRule {
      Mk(Field, Field, KExpr)
    }

  enum KConstantInfo {
      Axiom(Field, KExpr, Field),
      Defn(Field, KExpr, KExpr, Ixon::DefinitionSafety, Field),
      Thm(Field, KExpr, KExpr),
      Opaque(Field, KExpr, KExpr, Field),
      Quot(Field, KExpr, Ixon::QuotKind),
      Induct(Field, KExpr, Field, Field, Field, Field, Bytes::AddressRef, Field),
      Ctor(Field, KExpr, Bytes::AddressRef, Field, Field, Field, Field, Field),
      Rec(Field, KExpr, Field, Field, Field, Field, Lists::List<KRecRule>, Field, Field, Bytes::AddressRef, Field)
    }
}
⟧

def collect_spine := aiur_fn⟦
  fn collect_spine(e: KExpr) -> (KExpr, Lists::List<KExpr>) {
      match (*(e)) {
        KExprNode::App(f, a) => {
          let (head, args) = collect_spine(f);
          (head, Lists::snoc(args, a)) } ,
        _ => {  (e, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

end

end IxVM
