import Aiur.Modules.Function

/-! # IxVM module `Ixon`

The Ixon data types: expressions, universes, constants and their metadata.

A constant carries its record's binder-data section (`BinderBlock`s, sorted by
`(ekind, eidx, variant)`): per root expression (`ekind` 0, `eidx` the root's
number, variant 0) and per sharing entry and variant (`ekind` 1), the data of
the expression's numbered nodes in pre-order. The numbered nodes are the `Lam`
and `All` nodes (`Never`, `Zero`, `IfAllZero`, or the undecided sentinel) and
the `Share` nodes whose entry has a binder (`Share`, the entry's variant). The
record's address hashes the section with the rest of its bytes.

Aiur type declarations, imported by `IxVM.Program`. -/

namespace IxVM

aiur_module Ixon where
aiur_decls⟦
module Ixon {
  enum Uses {
      Erased,
      Linear,
      Affine,
      Many
    }

  enum Owned {
      Unique,
      Shared
    }

  enum Locality { Unrestricted, Local }

  enum ValueContract { Mk(Owned, Locality) }

  enum BinderContract { Mk(Uses, ValueContract) }

  enum LetKind { Value, BorrowShared }

  enum LetContract { Mk(Field, LetKind, BinderContract) }

  enum Expr {
      Srt(UInt64::U64),
      Var(UInt64::U64),
      Ref(UInt64::U64, Lists::List<UInt64::U64>),
      Rec(UInt64::U64, Lists::List<UInt64::U64>),
      Prj(UInt64::U64, UInt64::U64, &Expr),
      Str(UInt64::U64),
      Nat(UInt64::U64),
      App(&Expr, &Expr),
      Lam(BinderContract, &Expr, &Expr),
      All(BinderContract, ValueContract, &Expr, &Expr),
      Let(LetContract, &Expr, &Expr, &Expr),
      Share(UInt64::U64)
    }

  enum Univ {
      Zero,
      Succ(&Univ),
      Max(&Univ, &Univ),
      IMax(&Univ, &Univ),
      Var(UInt64::U64)
    }

  enum DefKind {
      Definition,
      Opaque,
      Theorem
    }

  enum DefinitionSafety {
      Unsafe,
      Safe,
      Partial
    }

  enum QuotKind {
      Typ,
      Ctor,
      Lift,
      Ind
    }

  enum Definition {
      Mk(DefKind, DefinitionSafety, UInt64::U64, &Expr, &Expr)
    }

  enum RecursorRule {
      Mk(UInt64::U64, &Expr)
    }

  enum Recursor {
      Mk(Field, Field, UInt64::U64, UInt64::U64, UInt64::U64, UInt64::U64, UInt64::U64, &Expr, Lists::List<RecursorRule>)
    }

  enum Axiom {
      Mk(Field, UInt64::U64, &Expr)
    }

  enum Quotient {
      Mk(QuotKind, UInt64::U64, &Expr)
    }

  enum Constructor {
      Mk(Field, UInt64::U64, UInt64::U64, UInt64::U64, UInt64::U64, &Expr)
    }

  enum Inductive {
      Mk(Field, UInt64::U64, UInt64::U64, UInt64::U64, &Expr, Lists::List<Constructor>)
    }

  enum InductiveProj {
      Mk(UInt64::U64, Bytes::AddressRef)
    }

  enum ConstructorProj {
      Mk(UInt64::U64, UInt64::U64, Bytes::AddressRef)
    }

  enum RecursorProj {
      Mk(UInt64::U64, Bytes::AddressRef)
    }

  enum DefinitionProj {
      Mk(UInt64::U64, Bytes::AddressRef)
    }

  enum MutConst {
      Defn(Definition),
      Indc(Inductive),
      Recr(Recursor)
    }

  enum ConstantInfo {
      Defn(Definition),
      Recr(Recursor),
      Axio(Axiom),
      Quot(Quotient),
      CPrj(ConstructorProj),
      RPrj(RecursorProj),
      IPrj(InductiveProj),
      DPrj(DefinitionProj),
      Muts(Lists::List<MutConst>)
    }

  enum BinderNode {
      Never,
      Zero,
      IfAllZero(Lists::List<UInt64::U64>),
      Share(UInt64::U64),
      Undecided
    }

  enum BinderBlock {
      Mk(Field, UInt64::U64, UInt64::U64, Lists::List<BinderNode>)
    }

  enum Constant {
      Mk(ConstantInfo, Lists::List<&Expr>, Lists::List<Bytes::AddressRef>, Lists::List<&Univ>, Lists::List<BinderBlock>)
    }

  enum BlobEntry {
      Mk(Bytes::AddressRef, UInt64::U64)
    }
}
⟧

end

end IxVM
