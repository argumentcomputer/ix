module

public import IxCK.Kernel.Model.GuardClassifier
public import IxCK.Kernel.Verify.Cached.NormalizeRef

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

/-- Erasing metadata commutes with raw positional universe instantiation. The default binder
annotation is parameter-free, so its substitution remains default. -/
theorem eraseMeta_instantiateLevelParams (e : Expr md) (ks : List LevelParam) (us : List Level) :
    (e.instantiateLevelParams ks us).eraseMeta = e.eraseMeta.instantiateLevelParams ks us := by
  have hdefault : Level.substPW ks us (default : BinderMeta).pw = (default : BinderMeta).pw :=
    Level.substPW_eq_self (by change PropWhen.never.hasParams = false; exact PropWhen.hasParams_never)
  induction e <;> simp_all only [Expr.instantiateLevelParams, Expr.eraseMeta]

/-- Metadata erasure does not introduce or remove free variables. -/
theorem eraseMeta_hasFvar (e : Expr md) : e.eraseMeta.hasFvar = e.hasFvar := by
  induction e <;> simp_all only [Expr.eraseMeta, Expr.hasFvar]


end Ix.Kernel.GuardClassifier
