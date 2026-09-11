/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Typing.UniqueTyping

open Ix.Theory (VLevel)

/-! # Theory local declarations

The implementation-independent core of a local context.  `VLocalDecl` only
mentions Theory expressions; the `Lean.FVarId` bookkeeping used by the
verified Lean-expression translator remains in `Ix.Theory.Named.Verify.VLCtx`.
-/

namespace Ix.Theory.Named
open VEnv

inductive VLocalDecl where
  | vlam (type : VExpr)
  | vlet (type value : VExpr)

def VLocalDecl.depth : VLocalDecl → Nat
  | .vlam .. => 1
  | .vlet .. => 0

def VLocalDecl.value : VLocalDecl → VExpr
  | .vlam .. => .bvar 0
  | .vlet _ e => e

def VLocalDecl.type' : VLocalDecl → VExpr
  | .vlam A
  | .vlet A _ => A

def VLocalDecl.type : VLocalDecl → VExpr
  | .vlam A => A.lift
  | .vlet A _ => A

def VLocalDecl.lift' : VLocalDecl → Lift → VLocalDecl
  | .vlam A, n => .vlam (A.lift' n)
  | .vlet A e, n => .vlet (A.lift' n) (e.lift' n)

def VLocalDecl.liftN : VLocalDecl → Nat → Nat → VLocalDecl
  | .vlam A, n, k => .vlam (A.liftN n k)
  | .vlet A e, n, k => .vlet (A.liftN n k) (e.liftN n k)

def VLocalDecl.inst : VLocalDecl → VExpr → (k : Nat := 0) → VLocalDecl
  | .vlam A, e₀, k => .vlam (A.inst e₀ k)
  | .vlet A e, e₀, k => .vlet (A.inst e₀ k) (e.inst e₀ k)

def VLocalDecl.instL : VLocalDecl → List VLevel → VLocalDecl
  | .vlam A, ls => .vlam (A.instL ls)
  | .vlet A e, ls => .vlet (A.instL ls) (e.instL ls)

def VLocalDecl.WF (env : VEnv) (U : Nat) (Γ : List VExpr) : VLocalDecl → Prop
  | .vlam type => env.IsType U Γ type
  | .vlet type value => env.HasType U Γ value type

def VLocalDecl.ClosedN : VLocalDecl → (k : Nat := 0) → Prop
  | .vlam A, k => A.ClosedN k
  | .vlet A e, k => A.ClosedN k ∧ e.ClosedN k

variable! (env : VEnv) (U : Nat) (Γ : List VExpr) in
inductive VLocalDecl.IsDefEq : VLocalDecl → VLocalDecl → Prop
  | vlam : env.IsDefEq U Γ type₁ type₂ (.sort u) →
      VLocalDecl.IsDefEq (.vlam type₁) (.vlam type₂)
  | vlet :
    env.IsDefEq U Γ value₁ value₂ type₁ → env.IsDefEq U Γ type₁ type₂ (.sort u) →
    VLocalDecl.IsDefEq (.vlet type₁ value₁) (.vlet type₂ value₂)

theorem VLocalDecl.lift'_consN_skipN {d : VLocalDecl} :
    d.lift' (.consN (.skipN .refl n) k) = d.liftN n k := by
  cases d <;> simp [VLocalDecl.lift', VLocalDecl.liftN, VExpr.lift'_consN_skipN]

nonrec theorem VLocalDecl.WF.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ') :
    ∀ {d}, WF env U Γ d → WF env U Γ' (d.liftN n k)
  | .vlam _, H | .vlet .., H => H.weakN henv W

nonrec theorem VLocalDecl.WF.instN (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) : ∀ {d}, WF env U Γ₁ d → WF env U Γ (d.inst e₀ k)
  | .vlam _, H | .vlet .., H => H.instN henv W h₀

nonrec theorem VLocalDecl.WF.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {d}, WF env ls.length Γ d → WF env U' (Γ.map (·.instL ls)) (d.instL ls)
  | .vlam _, H | .vlet .., H => H.instL hls

@[simp] theorem VLocalDecl.lift'_depth {d : VLocalDecl} : (d.lift' n).depth = d.depth := by
  cases d <;> rfl

theorem VLocalDecl.lift'_comp {d : VLocalDecl} :
    d.lift' (.comp l₁ l₂) = (d.lift' l₁).lift' l₂ := by
  cases d <;> simp [VLocalDecl.lift', VExpr.lift'_comp]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.Lift' n Γ Γ') in
theorem VLocalDecl.weak'_iff :
    VLocalDecl.WF env U Γ' (d.lift' n) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weak'_iff henv hΓ' W
  | .vlet .. => HasType.weak'_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') in
theorem VLocalDecl.weakN_iff :
    VLocalDecl.WF env U Γ' (d.liftN n k) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weakN_iff henv hΓ' W
  | .vlet .. => HasType.weakN_iff henv hΓ' W

variable! (henv : Ordered env) (hΓ : OnCtx Γ (IsType env U)) in
theorem VLocalDecl.IsDefEq.refl :
    ∀ {d}, VLocalDecl.WF env U Γ d → VLocalDecl.IsDefEq env U Γ d d
  | .vlam _, ⟨_, h1⟩ => .vlam h1
  | .vlet .., h1 => let ⟨_, h2⟩ := h1.isType henv hΓ; .vlet h1 h2

theorem VLocalDecl.IsDefEq.wf :
    VLocalDecl.IsDefEq env U Γ d₁ d₂ → VLocalDecl.WF env U Γ d₁
  | .vlam h3 => ⟨_, h3.hasType.1⟩
  | .vlet h3 _ => h3.hasType.1

theorem VLocalDecl.IsDefEq.mono (henv : env ≤ env') :
    VLocalDecl.IsDefEq env U Γ d₁ d₂ → VLocalDecl.IsDefEq env' U Γ d₁ d₂
  | .vlam h => .vlam (h.mono henv)
  | .vlet h₁ h₂ => .vlet (h₁.mono henv) (h₂.mono henv)

theorem VLocalDecl.IsDefEq.symm :
    VLocalDecl.IsDefEq env U Γ d₁ d₂ → VLocalDecl.IsDefEq env U Γ d₂ d₁
  | .vlam h1 => .vlam h1.symm
  | .vlet h1 h2 => .vlet (h2.defeqDF h1.symm) h2.symm

theorem VLocalDecl.IsDefEq.defeqDFC (henv : Ordered env)
    (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    VLocalDecl.IsDefEq env U Γ₁ d₁ d₂ → VLocalDecl.IsDefEq env U Γ₂ d₁ d₂
  | .vlam h1 => .vlam (h1.defeqDFC henv hΓ)
  | .vlet h1 h2 => .vlet (h1.defeqDFC henv hΓ) (h2.defeqDFC henv hΓ)

#guard_named_axioms Ix.Theory.Named.VLocalDecl.WF.weakN [propext, Quot.sound]

#guard_named_axioms Ix.Theory.Named.VLocalDecl.weakN_iff [
  propext,
  sorryAx,
  Classical.choice,
  Quot.sound]

#guard_named_axioms Ix.Theory.Named.VLocalDecl.IsDefEq.defeqDFC [propext, Quot.sound]

end Ix.Theory.Named
