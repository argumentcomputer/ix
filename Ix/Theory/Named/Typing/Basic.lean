/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.VEnv

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
open Ix.Theory.Named

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

/-- A context-wide predicate, exposing each binder in its preceding context. -/
def OnCtx (Γ : List VExpr) (P : List VExpr → VExpr → Prop) : Prop :=
  match Γ with
  | [] => True
  | A::Γ => OnCtx Γ P ∧ P Γ A

namespace VEnv

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEq Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

mutual

inductive IsDefEq : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | structEta :
    env.structEtas rule →
    (∀ level ∈ levels, level.WF uvars) →
    levels.length = rule.uvars →
    params.length = rule.nparams →
    SpineWF Γ (rule.familyType.instL levels) params (.sort resultLevel) →
    Γ ⊢ major : rule.structureType levels params →
    Γ ⊢ rule.rebuild levels params major :
      rule.structureType levels params →
    Γ ⊢ rule.rebuild levels params major ≡ major :
      rule.structureType levels params
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

/-- Typing of an application spine against an iterated pi type: peeling the
expressions of `es` off `A` one instantiation at a time ends at `B`.

This judgment is mutually inductive with `IsDefEq` so rules whose validity
depends on an exact application spine retain induction hypotheses for every
argument typing derivation. -/
inductive SpineWF : List VExpr → VExpr → List VExpr → VExpr → Prop where
  | nil : SpineWF Γ A [] A
  | cons :
    IsDefEq Γ e e A₁ →
    SpineWF Γ (A₂.inst e) es B →
    SpineWF Γ (.forallE A₁ A₂) (e :: es) B

end

end

def HasType (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEq env U Γ e e A

def IsType (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, env.HasType U Γ A (.sort u)

def IsDefEqU (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) :=
  ∃ A, env.IsDefEq U Γ e₁ e₂ A

end VEnv

def VExpr.WF (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) := env.IsDefEqU U Γ e e

def VConstant.WF (env : VEnv) (ci : VConstant) : Prop := env.IsType ci.uvars [] ci.type

def VDefEq.WF (env : VEnv) (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type ∧ env.HasType df.uvars [] df.rhs df.type

/-- Subject-reduction package attached to a registered structure-eta
descriptor.  It consumes the exact family parameter spine but contains no
equality premise. -/
structure VStructEta.WF (rule : VStructEta) (env : VEnv) : Prop where
  /-- The retained family declaration is a closed constant type.  This is the
  syntactic fact which lets an exact parameter-spine certificate survive term
  weakening and substitution. -/
  familyType_closed : rule.familyType.ClosedN
  rebuild_hasType :
    ∀ {env' : VEnv}, env ≤ env' →
      ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
      OnCtx Γ (env'.IsType U) →
      (∀ level ∈ levels, level.WF U) →
      levels.length = rule.uvars →
      params.length = rule.nparams →
      (∃ resultLevel,
        env'.SpineWF U Γ (rule.familyType.instL levels)
          params (.sort resultLevel)) →
      env'.HasType U Γ major (rule.structureType levels params) →
      env'.HasType U Γ (rule.rebuild levels params major)
        (rule.structureType levels params)
