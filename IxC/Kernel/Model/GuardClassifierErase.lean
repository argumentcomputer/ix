module

public import IxC.Kernel.Model.GuardClassifier
public import IxC.Kernel.Verify.Cached.NormalizeRef

@[expose] public section

/-! # Metadata erasure for the raw field classifier

The classifier is a data computation and never branches on binder/let metadata. The raw
record dictionary therefore uses erased syntax. These structural facts let raw heap lifting,
substitution and universe instantiation be specified without a typed-environment premise.
-/

namespace Ix.Kernel.GuardClassifier

theorem eraseMeta_lift (e : Expr md) (amount : Nat) :
    ∀ cutoff, (e.liftLooseBVars amount cutoff).eraseMeta =
      e.eraseMeta.liftLooseBVars amount cutoff := by
  induction e with
  | bvar i =>
    intro cutoff
    simp only [Expr.liftLooseBVars, Expr.eraseMeta]
    split <;> rfl
  | fvar i ty ih => intro cutoff; rfl
  | sort => intro cutoff; rfl
  | const => intro cutoff; rfl
  | lit => intro cutoff; rfl
  | app f a ihf iha => intro cutoff; simp only [Expr.liftLooseBVars, Expr.eraseMeta, ihf, iha]
  | lam ty body mb iht ihb => intro cutoff; simp only [Expr.liftLooseBVars, Expr.eraseMeta, iht, ihb]
  | forallE ty body mb iht ihb => intro cutoff; simp only [Expr.liftLooseBVars, Expr.eraseMeta, iht, ihb]
  | letE ty value body lm iht ihv ihb =>
    intro cutoff; simp only [Expr.liftLooseBVars, Expr.eraseMeta, iht, ihv, ihb]
  | proj s i e ih => intro cutoff; simp only [Expr.liftLooseBVars, Expr.eraseMeta, ih]

theorem eraseMeta_instantiate1Lift (e v : Expr md) :
    ∀ depth, (e.instantiate1Lift v depth).eraseMeta =
      e.eraseMeta.instantiate1Lift v.eraseMeta depth := by
  induction e with
  | bvar i =>
    intro depth
    simp only [Expr.instantiate1Lift, Expr.eraseMeta]
    split
    · exact eraseMeta_lift v depth 0
    · split <;> rfl
  | fvar i ty ih => intro depth; rfl
  | sort => intro depth; rfl
  | const => intro depth; rfl
  | lit => intro depth; rfl
  | app f a ihf iha => intro depth; simp only [Expr.instantiate1Lift, Expr.eraseMeta, ihf, iha]
  | lam ty body mb iht ihb => intro depth; simp only [Expr.instantiate1Lift, Expr.eraseMeta, iht, ihb]
  | forallE ty body mb iht ihb => intro depth; simp only [Expr.instantiate1Lift, Expr.eraseMeta, iht, ihb]
  | letE ty value body lm iht ihv ihb =>
    intro depth; simp only [Expr.instantiate1Lift, Expr.eraseMeta, iht, ihv, ihb]
  | proj s i e ih => intro depth; simp only [Expr.instantiate1Lift, Expr.eraseMeta, ih]

end Ix.Kernel.GuardClassifier
