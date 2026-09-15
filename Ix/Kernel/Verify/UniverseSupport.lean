/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.InstUniv

/-! Universe occurrences and finite substitution support shared by the named
translation and the direct set-theoretic refinement. -/

namespace Ix.Kernel

/-! ### Level occurrences and the reach set -/

/-- The levels of an expression: `sort` payloads and `const` level
    arguments, through all subterms. -/
inductive KExpr.HasLevel {m : Mode} : KExpr m → KUniv m → Prop
  | sort {u : KUniv m} {md : ExprInfo m} : HasLevel (.sort u md) u
  | const {id : KId m} {us : Array (KUniv m)} {md : ExprInfo m}
      {u : KUniv m} :
    u ∈ us → HasLevel (.const id us md) u
  | app_f {f a : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel f u → HasLevel (.app f a md) u
  | app_a {f a : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel a u → HasLevel (.app f a md) u
  | lam_ty {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.lam n bi ty body md) u
  | lam_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.lam n bi ty body md) u
  | all_ty {n : m.F Name} {bi : m.F Lean.BinderInfo} {ty body : KExpr m}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.all n bi ty body md) u
  | all_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
      {ty body : KExpr m} {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.all n bi ty body md) u
  | letE_ty {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel ty u → HasLevel (.letE n ty val body nd md) u
  | letE_val {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel val u → HasLevel (.letE n ty val body nd md) u
  | letE_body {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
      {md : ExprInfo m} {u : KUniv m} :
    HasLevel body u → HasLevel (.letE n ty val body nd md) u
  | prj {id : KId m} {field : UInt64} {val : KExpr m} {md : ExprInfo m}
      {u : KUniv m} :
    HasLevel val u → HasLevel (.prj id field val md) u

/-- Level-side reach set of the instantiation walk on `e`: everything
    `substUniv us` can address-compare while rewriting `e`'s levels.
    Finite and spec-determined (union of `SubstUnivReach` over the
    levels of `e`) — never closed under constructors. -/
def KExpr.LevelReach {m : Mode} (us : Array (KUniv m)) (e : KExpr m)
    (x : KUniv m) : Prop :=
  ∃ u, KExpr.HasLevel e u ∧ KUniv.SubstUnivReach us u x

namespace KExpr.LevelReach

variable {m : Mode} {us : Array (KUniv m)} {x : KUniv m}

theorem app_f {f a : KExpr m} {md : ExprInfo m}
    (h : LevelReach us f x) : LevelReach us (.app f a md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .app_f hu, hr⟩

theorem app_a {f a : KExpr m} {md : ExprInfo m}
    (h : LevelReach us a x) : LevelReach us (.app f a md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .app_a hu, hr⟩

theorem lam_ty {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us ty x) : LevelReach us (.lam n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .lam_ty hu, hr⟩

theorem lam_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us body x) :
    LevelReach us (.lam n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .lam_body hu, hr⟩

theorem all_ty {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us ty x) : LevelReach us (.all n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .all_ty hu, hr⟩

theorem all_body {n : m.F Name} {bi : m.F Lean.BinderInfo}
    {ty body : KExpr m} {md : ExprInfo m}
    (h : LevelReach us body x) :
    LevelReach us (.all n bi ty body md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .all_body hu, hr⟩

theorem letE_ty {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us ty x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_ty hu, hr⟩

theorem letE_val {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us val x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_val hu, hr⟩

theorem letE_body {n : m.F Name} {ty val body : KExpr m} {nd : Bool}
    {md : ExprInfo m} (h : LevelReach us body x) :
    LevelReach us (.letE n ty val body nd md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .letE_body hu, hr⟩

theorem prj {id : KId m} {field : UInt64} {val : KExpr m}
    {md : ExprInfo m} (h : LevelReach us val x) :
    LevelReach us (.prj id field val md) x :=
  let ⟨u, hu, hr⟩ := h; ⟨u, .prj hu, hr⟩

end KExpr.LevelReach

end Ix.Kernel

