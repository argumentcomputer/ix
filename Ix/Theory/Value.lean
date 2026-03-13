/-
  Ix.Theory.Value: Specification-level semantic domain for NbE.

  SVal represents evaluated expressions: closures for binders,
  neutral terms for stuck computations, and literals.
  Mirrors Ix.Kernel2.Value but without thunks, ST, or metadata.
-/
import Ix.Theory.Expr

namespace Ix.Theory

mutual
inductive SVal (L : Type) where
  | lam (dom : SVal L) (body : SExpr L) (env : List (SVal L))
  | pi  (dom : SVal L) (body : SExpr L) (env : List (SVal L))
  | sort (u : L)
  | neutral (head : SHead L) (spine : List (SVal L))
  | lit (n : Nat)
  deriving Inhabited

inductive SHead (L : Type) where
  | fvar (level : Nat)
  | const (id : Nat) (levels : List L)
  deriving Inhabited
end

end Ix.Theory
