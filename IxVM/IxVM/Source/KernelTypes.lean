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
      Lam(KExpr, KExpr),
      Forall(KExpr, KExpr),
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
  inline fn collect_spine(e: KExpr) -> (KExpr, Lists::List<KExpr>) {
      collect_spine_onto(e, (&(Lists::Node::Nil)))
    }
⟧

  -- The head of `e` and its arguments in order, followed by `rest`. Arguments are
  -- consed from the last one inwards, so a spine of n arguments costs n rows (a
  -- `snoc` per argument would cost n²/2).

def collect_spine_onto := aiur_fn⟦
  fn collect_spine_onto(e: KExpr, rest: Lists::List<KExpr>) -> (KExpr, Lists::List<KExpr>) {
      match (*(e)) {
        KExprNode::App(f, a) => {  collect_spine_onto(f, (&(Lists::Node::Cons(a, rest)))) } ,
        _ => {  (e, rest) } ,
      }
    }
⟧

end

end IxVM
