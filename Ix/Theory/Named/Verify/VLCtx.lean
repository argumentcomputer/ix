/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Expr
import Ix.Theory.Named.LocalContext

open Ix.Theory (VLevel)

namespace Ix.Theory.Named

open Lean (FVarId Expr)

@[reducible] def VLCtx := List (Option (FVarId × List FVarId) × VLocalDecl)

namespace VLCtx

def bvars : VLCtx → Nat
  | [] => 0
  | (none, _) :: Δ => bvars Δ + 1
  | (some _, _) :: Δ => bvars Δ

abbrev NoBV (Δ : VLCtx) : Prop := Δ.bvars = 0

def next : Option (FVarId × List FVarId) → Nat ⊕ FVarId → Option (Nat ⊕ FVarId)
  | none, .inl 0 => none
  | none, .inl (n+1) => some (.inl n)
  | some _, .inl n => some (.inl n)
  | none, .inr fv' => some (.inr fv')
  | some (fv, _), .inr fv' => if fv == fv' then none else some (.inr fv')

def find? : VLCtx → Nat ⊕ FVarId → Option (VExpr × VExpr)
  | [], _ => none
  | (ofv, d) :: Δ, v =>
    match next ofv v with
    | none => some (d.value, d.type)
    | some v => do let (e, A) ← find? Δ v; some (e.liftN d.depth, A.liftN d.depth)

def liftVar (n k : Nat) : Nat ⊕ FVarId → Nat ⊕ FVarId
  | .inl i => .inl (if i < k then i else i + n)
  | .inr fv => .inr fv

def varToExpr : Nat ⊕ FVarId → Expr
  | .inl i => .bvar i
  | .inr fv => .fvar fv

def vlamName : VLCtx → Nat → Option (Option (FVarId × List FVarId))
  | [], _ => none
  | (_, .vlet ..) :: Δ, i
  | (_, .vlam ..) :: Δ, i+1 => vlamName Δ i
  | (ofv, .vlam ..) :: _, 0 => some ofv

def fvars (Δ : VLCtx) : List FVarId := Δ.filterMap (·.1.map (·.1))

@[simp] theorem fvars_nil : fvars [] = [] := rfl
@[simp] theorem fvars_cons_none {Δ : VLCtx} : fvars ((none, d) :: Δ) = fvars Δ := rfl
@[simp] theorem fvars_cons_some {Δ : VLCtx} :
    fvars ((some fv, d) :: Δ) = fv.1 :: fvars Δ := rfl

def toCtx : VLCtx → List VExpr
  | [] => []
  | (_, .vlam ty) :: Δ => ty :: VLCtx.toCtx Δ
  | (_, .vlet _ _) :: Δ => VLCtx.toCtx Δ

def instL (Δ : VLCtx) (ls : List VLevel) : VLCtx :=
  match Δ with
  | [] => []
  | (ofv, d) :: Δ => (ofv, d.instL ls) :: instL Δ ls

theorem find?_eq_some : (∃ x, Δ.find? (.inr fv) = some x) ↔ fv ∈ fvars Δ := by
  induction Δ with simp [find?] | cons d Δ ih
  match d with
  | (none, _) => simp [next, ← ih]; grind
  | (some (fv',  _), _) =>
    simp [next]; rw [@eq_comm _ fv]
    by_cases h : fv' == fv <;> simp [h] <;> simp at h <;> simp [h]; grind

theorem vlamName_mem_fvars :
    ∀ {Δ : VLCtx} {i}, Δ.vlamName i = some (some fv) → fv.1 ∈ fvars Δ
  | (none, .vlet ..) :: Δ, _, h
  | (none, .vlam ..) :: Δ, _+1, h => vlamName_mem_fvars (Δ := Δ) h
  | (some _, .vlet ..) :: Δ, _, h
  | (some _, .vlam ..) :: Δ, _+1, h => .tail _ <| vlamName_mem_fvars (Δ := Δ) h
  | (some _fv, .vlam ..) :: _, 0, rfl => .head _

end VLCtx
