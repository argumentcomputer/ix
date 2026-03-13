/-
  Ix.Theory.Typing: The IsDefEq typing judgment.

  Defines the core typing/definitional-equality relation combining typing and
  definitional equality in a single inductive, following lean4lean's
  `Lean4Lean/Theory/Typing/Basic.lean`. Extended with `letE`, `lit`, and `proj`
  constructors for a more direct verification bridge to the Ix kernel.

  Reference: docs/theory/kernel.md Part III (lines 301-414).
-/
import Ix.Theory.Env

namespace Ix.Theory

/-! ## Context Lookup

    Variable `i` in context `Γ` has type `Γ[i]` lifted appropriately (to
    account for the bindings between the variable and the point of use). -/

inductive Lookup : List TExpr → Nat → TExpr → Prop where
  | zero : Lookup (ty :: Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A :: Γ) (n+1) ty.lift

/-! ## The IsDefEq Judgment

    The core typing relation combining typing and definitional equality in a
    single inductive. `IsDefEq env uvars litType projType Γ e₁ e₂ A` means
    that `e₁` and `e₂` are definitionally equal at type `A` in context `Γ`,
    given environment `env` with `uvars` universe variables.

    Parameters:
    - `env`: the specification environment (constants + defeqs)
    - `uvars`: number of universe variables in scope
    - `litType`: the type of nat literals (typically `.const natId []`)
    - `projType`: computes the type of a projection given
      (typeName, fieldIdx, struct, structType) -/

variable (env : SEnv) (uvars : Nat)
         (litType : TExpr)
         (projType : Nat → Nat → TExpr → TExpr → TExpr)

inductive IsDefEq : List TExpr → TExpr → TExpr → TExpr → Prop where
  -- Variable
  | bvar : Lookup Γ i A → IsDefEq Γ (.bvar i) (.bvar i) A

  -- Structural
  | symm  : IsDefEq Γ e e' A → IsDefEq Γ e' e A
  | trans : IsDefEq Γ e₁ e₂ A → IsDefEq Γ e₂ e₃ A → IsDefEq Γ e₁ e₃ A

  -- Sorts
  | sortDF :
      l.WF uvars → l'.WF uvars → l ≈ l' →
      IsDefEq Γ (.sort l) (.sort l') (.sort (.succ l))

  -- Constants (universe-polymorphic)
  | constDF :
      env.constants c = some ci →
      (∀ l ∈ ls, l.WF uvars) → (∀ l ∈ ls', l.WF uvars) →
      ls.length = ci.uvars → SForall₂ (· ≈ ·) ls ls' →
      IsDefEq Γ (.const c ls) (.const c ls') (ci.type.instL ls)

  -- Application
  | appDF :
      IsDefEq Γ f f' (.forallE A B) →
      IsDefEq Γ a a' A →
      IsDefEq Γ (.app f a) (.app f' a') (B.inst a)

  -- Lambda
  | lamDF :
      IsDefEq Γ A A' (.sort u) →
      IsDefEq (A :: Γ) body body' B →
      IsDefEq Γ (.lam A body) (.lam A' body') (.forallE A B)

  -- Pi (forallE)
  | forallEDF :
      IsDefEq Γ A A' (.sort u) →
      IsDefEq (A :: Γ) body body' (.sort v) →
      IsDefEq Γ (.forallE A body) (.forallE A' body')
              (.sort (.imax u v))

  -- Type conversion
  | defeqDF :
      IsDefEq Γ A B (.sort u) → IsDefEq Γ e₁ e₂ A →
      IsDefEq Γ e₁ e₂ B

  -- Beta reduction
  | beta :
      IsDefEq (A :: Γ) e e B → IsDefEq Γ e' e' A →
      IsDefEq Γ (.app (.lam A e) e') (e.inst e') (B.inst e')

  -- Eta expansion
  | eta :
      IsDefEq Γ e e (.forallE A B) →
      IsDefEq Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)

  -- Proof irrelevance
  | proofIrrel :
      IsDefEq Γ p p (.sort .zero) →
      IsDefEq Γ h h p → IsDefEq Γ h' h' p →
      IsDefEq Γ h h' p

  -- Extra definitional equalities (delta, iota, nat prims, etc.)
  | extra :
      env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
      IsDefEq Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)

  -- Let-expression
  | letDF :
      IsDefEq Γ ty ty' (.sort u) →
      IsDefEq Γ val val' ty →
      IsDefEq (ty :: Γ) body body' B →
      IsDefEq Γ (.letE ty val body) (.letE ty' val' body') (B.inst val)

  | letZeta :
      IsDefEq Γ ty ty (.sort u) → IsDefEq Γ val val ty →
      IsDefEq (ty :: Γ) body body B →
      IsDefEq Γ (.letE ty val body) (body.inst val) (B.inst val)

  -- Literals
  | litDF :
      IsDefEq Γ (.lit n) (.lit n) litType

  -- Projection
  | projDF :
      IsDefEq Γ s s sType →
      IsDefEq Γ (.proj t i s) (.proj t i s) (projType t i s sType)

/-! ## Abbreviations -/

/-- `HasType` is typing: `e` has type `A` in context `Γ`. -/
def HasType (Γ : List TExpr) (e A : TExpr) : Prop :=
  IsDefEq env uvars litType projType Γ e e A

/-- `IsType` means `A` is a type (i.e., `A : Sort u` for some `u`). -/
def IsType (Γ : List TExpr) (A : TExpr) : Prop :=
  ∃ u, HasType env uvars litType projType Γ A (.sort u)

/-- `IsDefEqU` means `e₁` and `e₂` are definitionally equal at some type. -/
def IsDefEqU (Γ : List TExpr) (e₁ e₂ : TExpr) : Prop :=
  ∃ A, IsDefEq env uvars litType projType Γ e₁ e₂ A

/-! ## Sanity checks

    Construct simple derivation trees to verify the inductive is non-vacuous. -/

-- Sort 0 : Sort 1
example : IsDefEq env uvars litType projType []
    (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF trivial trivial rfl

-- In context [A], variable 0 has type A (lifted)
example : IsDefEq env uvars litType projType [A]
    (.bvar 0) (.bvar 0) A.lift :=
  .bvar (.zero)

-- Sort u ≡ Sort u : Sort (u+1)  for any well-formed level
example (h : l.WF uvars) : IsDefEq env uvars litType projType []
    (.sort l) (.sort l) (.sort (.succ l)) :=
  .sortDF h h (SLevel.equiv_def'.mpr rfl)

-- Literal n : litType
example : IsDefEq env uvars litType projType [] (.lit 42) (.lit 42) litType :=
  .litDF

-- Symmetry: if e₁ ≡ e₂ : A then e₂ ≡ e₁ : A
example (h : IsDefEq env uvars litType projType Γ e₁ e₂ A) :
    IsDefEq env uvars litType projType Γ e₂ e₁ A :=
  .symm h

-- Extra: nat primitive reductions flow through
example (hdf : env.defeqs df) (hlen : ls.length = df.uvars)
    (hwf : ∀ l ∈ ls, l.WF uvars) :
    IsDefEq env uvars litType projType []
      (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
  .extra hdf hwf hlen

end Ix.Theory
