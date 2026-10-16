module

public import Ix.Sharing.Exact.Basic
import all Init.Util

public section

namespace Ix.Sharing.Exact

deriving instance DecidableEq for Ixon.Expr

/-- An address is only a candidate selector. The source expression remains
part of the key and must match before a cached value can be used. -/
structure ExprCache.Key where
  address : USize
  source : Ixon.Expr

@[inline] def exprKey (source : Ixon.Expr) : ExprCache.Key := ⟨exprPtr source, source⟩

/-- One retained expression per pointer bucket. A collision may evict a useful
entry, but cannot make another expression's cached value a successful hit. -/
structure ExprCache (α : Type) where
  entries : Std.HashMap USize (Ixon.Expr × α) := {}
  deriving Inhabited

@[inline] def ExprCache.get? (cache : ExprCache α) (key : ExprCache.Key) : Option α :=
  match cache.entries.get? key.address with
  | none => none
  | some (source, value) =>
    letI : Decidable (key.source = source) :=
      withPtrEqDecEq key.source source (fun _ => inferInstance)
    if key.source = source then some value else none

@[inline] def ExprCache.insert (cache : ExprCache α) (key : ExprCache.Key) (value : α) : ExprCache α :=
  ⟨cache.entries.insert key.address (key.source, value)⟩

end Ix.Sharing.Exact
