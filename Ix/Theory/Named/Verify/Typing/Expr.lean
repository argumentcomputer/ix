/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Typing.Basic
import Ix.Theory.Named.Literals
import Ix.Theory.Named.Projection
import Ix.Theory.Named.Verify.NameGenerator
import Ix.Theory.Named.Verify.VLCtx
import Ix.Theory.Named.Verify.Axioms

open Ix.Theory (VLevel)

namespace Ix.Theory.Named
open Lean

def Closed : Expr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .fvar _, _ | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app f a, k => Closed f k ∧ Closed a k
  | .lam _ d b _, k
  | .forallE _ d b _, k => Closed d k ∧ Closed b (k+1)
  | .letE _ d v b _, k => Closed d k ∧ Closed v k ∧ Closed b (k+1)
  | .proj _ _ e, k | .mdata _ e, k => Closed e k
  | .mvar .., _ => False

nonrec abbrev _root_.Lean.Expr.Closed := @Closed

/-- This is very inefficient, only use for spec purposes -/
def _root_.Lean.Expr.fvarsList : Expr → List FVarId
  | .bvar _ | .sort .. | .const .. | .lit .. | .mvar .. => []
  | .fvar fv => [fv]
  | .app f a => f.fvarsList ++ a.fvarsList
  | .lam _ d b _
  | .forallE _ d b _ => d.fvarsList ++ b.fvarsList
  | .letE _ d v b _ => d.fvarsList ++ v.fvarsList ++ b.fvarsList
  | .proj _ _ e | .mdata _ e => e.fvarsList

variable (fvars : FVarId → Prop) in
def FVarsIn : Expr → Prop
  | .bvar _ => True
  | .fvar fv => fvars fv
  | .sort u => u.hasMVar' = false
  | .const _ us => ∀ u ∈ us, u.hasMVar' = false
  | .lit .. => True
  | .app f a => FVarsIn f ∧ FVarsIn a
  | .lam _ d b _
  | .forallE _ d b _ => FVarsIn d ∧ FVarsIn b
  | .letE _ d v b _ => FVarsIn d ∧ FVarsIn v ∧ FVarsIn b
  | .proj _ _ e | .mdata _ e => FVarsIn e
  | .mvar .. => False

nonrec abbrev _root_.Lean.Expr.FVarsIn := @FVarsIn

def VLCtx.FVWF : VLCtx → Prop
  | [] => True
  | (ofv, _) :: (Δ : VLCtx) =>
    VLCtx.FVWF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars)

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ.fvars ∧ deps ⊆ Δ.fvars) ∧
    VLocalDecl.WF env U Δ.toCtx d

theorem VLCtx.WF.fvwf : ∀ {Δ}, VLCtx.WF env U Δ → Δ.FVWF
  | [], h => h
  | _ :: _, ⟨h1, h2, _⟩ => ⟨h1.fvwf, h2⟩

/-- Verify compatibility surface for Theory's environment-indexed projection
semantics.  The view, universe instantiation, and parameter spine are hidden
from existing expression-translation consumers, but each witness is fully
constrained by `VEnv.TrProj`; no metadata is existentially invented. -/
def TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (structName : Name) (idx : Nat) (e result : VExpr) : Prop :=
  ∃ view levels params,
    view.name = structName ∧
      env.TrProj U Γ view levels params idx e result

variable (env : VEnv) (Us : List Name) in
inductive TrExprS : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrExprS Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrExprS Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrExprS Δ (.sort u) (.sort u')
  | const :
    env.constants c = some ci →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    TrExprS Δ (.const c us) (.const c us')
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExprS Δ f f' → TrExprS Δ a a' → TrExprS Δ (.app f a) (.app f' a')
  | lam :
    env.IsType Us.length Δ.toCtx ty' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    env.IsType Us.length Δ.toCtx ty' →
    env.IsType Us.length (ty' :: Δ.toCtx) body' →
    TrExprS Δ ty ty' → TrExprS ((none, .vlam ty') :: Δ) body body' →
    TrExprS Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    env.HasType Us.length Δ.toCtx val' ty' →
    TrExprS Δ ty ty' → TrExprS Δ val val' →
    TrExprS ((none, .vlet ty' val') :: Δ) body body' →
    TrExprS Δ (.letE name ty val body nd) body'
  | lit : env.ContainsLits l → TrExprS Δ l.toConstructor e → TrExprS Δ (.lit l) e
  | mdata : TrExprS Δ e e' → TrExprS Δ (.mdata d e) e'
  | proj : TrExprS Δ e e' →
    TrProj env Us.length Δ.toCtx s i e' e'' →
    TrExprS Δ (.proj s i e) e''

def TrExpr (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  ∃ e₂, TrExprS env Us Δ e e₂ ∧ env.IsDefEqU Us.length Δ.toCtx e₂ e'

/-- Deterministic shadow of `TrExprS`: compute the strict Theory translation
of an expression syntactically.  Every semantic premise of `TrExprS` only
validates a translation, it never selects between candidates, so on the
`TrExprS.IsUnique` fragment this function returns exactly the translation of
any derivation (`TrExprS.trExprS?_eq`).  The function checks nothing
semantic: it is meaningful only through that agreement theorem.  The pushed
`vlet` type is a dummy because `TrExprS` never reads it — `VLCtx.find?`
returns a let's value, and the type component is existentially discarded. -/
def trExprS? (Us : List Name) : VLCtx → Expr → Option VExpr
  | Δ, .bvar i => (Δ.find? (.inl i)).map (·.1)
  | Δ, .fvar fv => (Δ.find? (.inr fv)).map (·.1)
  | _, .sort u => (VLevel.ofLevel Us u).map .sort
  | _, .const c us => (us.mapM (VLevel.ofLevel Us)).map (VExpr.const c)
  | Δ, .app f a => do return .app (← trExprS? Us Δ f) (← trExprS? Us Δ a)
  | Δ, .lam _ ty body _ => do
      let ty' ← trExprS? Us Δ ty
      return .lam ty' (← trExprS? Us ((none, .vlam ty') :: Δ) body)
  | Δ, .forallE _ ty body _ => do
      let ty' ← trExprS? Us Δ ty
      return .forallE ty' (← trExprS? Us ((none, .vlam ty') :: Δ) body)
  | Δ, .letE _ _ val body _ => do
      let val' ← trExprS? Us Δ val
      trExprS? Us ((none, .vlet (.sort .zero) val') :: Δ) body
  | _, .lit l => some (.trLiteral l)
  | Δ, .mdata _ e => trExprS? Us Δ e
  | _, .proj .. => none
  | _, .mvar .. => none
