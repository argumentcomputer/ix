import Ix.Tc.Verify.Whnf.Beta.InstantiationChain

/-!
# Align concrete and Theory beta arguments

The application suffix stores arguments in production order, while the
simultaneous-substitution walker receives their reverse.  This slice proves
the pointwise alignment once, including array/list indexing, so the one-pass
translation theorem can use the exact selected argument in its variable arm.
-/

namespace Ix.Tc

open Lean4Lean

namespace RecM

/-- Pointwise structural translations for an argument list. -/
inductive ArgTranslations (env : VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) : List (KExpr .anon) → List VExpr → Prop
  | nil : ArgTranslations env uvars nameOf trProj Delta [] []
  | cons {arg : KExpr .anon} {argV : VExpr} {args : List (KExpr .anon)}
      {argValues : List VExpr} :
      TrKExprS env uvars nameOf trProj Delta arg argV →
      ArgTranslations env uvars nameOf trProj Delta args argValues →
      ArgTranslations env uvars nameOf trProj Delta (arg :: args)
        (argV :: argValues)

namespace ArgTranslations

theorem append
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx}
    {left right : List (KExpr .anon)} {leftV rightV : List VExpr}
    (hleft : ArgTranslations env uvars nameOf trProj Delta left leftV)
    (hright : ArgTranslations env uvars nameOf trProj Delta right rightV) :
    ArgTranslations env uvars nameOf trProj Delta (left ++ right)
      (leftV ++ rightV) := by
  induction hleft with
  | nil => exact hright
  | cons harg htail ih => exact .cons harg ih

theorem reverse
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx}
    {args : List (KExpr .anon)} {argValues : List VExpr}
    (h : ArgTranslations env uvars nameOf trProj Delta args argValues) :
    ArgTranslations env uvars nameOf trProj Delta args.reverse
      argValues.reverse := by
  induction h with
  | nil => exact .nil
  | cons harg htail ih =>
      simpa using ih.append (.cons harg .nil)

theorem length_eq
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx}
    {args : List (KExpr .anon)} {argValues : List VExpr}
    (h : ArgTranslations env uvars nameOf trProj Delta args argValues) :
    args.length = argValues.length := by
  induction h with
  | nil => rfl
  | cons harg htail ih => simp [ih]

theorem getElemBang
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx}
    {args : List (KExpr .anon)} {argValues : List VExpr}
    (h : ArgTranslations env uvars nameOf trProj Delta args argValues)
    (index : Nat) (hindex : index < args.length) :
    TrKExprS env uvars nameOf trProj Delta args[index]! argValues[index]! := by
  induction h generalizing index with
  | nil => simp at hindex
  | cons harg htail ih =>
      cases index with
      | zero => simpa
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using ih index hindex

end ArgTranslations

namespace TrAppSuffix.Values

/-- Forget application typing while retaining the exact pointwise structural
translations of its concrete and Theory argument lists. -/
theorem argumentTranslations
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {argValues : List VExpr} {resultV : VExpr}
    (h : TrAppSuffix.Values env uvars nameOf trProj Delta start args
      argValues resultV) :
    ArgTranslations env uvars nameOf trProj Delta args argValues := by
  induction h with
  | nil => exact .nil
  | app hprefix hfun harg hargTr ih =>
      exact ih.append (.cons hargTr .nil)

end TrAppSuffix.Values

/-- Exact pointwise relation between the walker's inner-to-outer array and
the reverse of the Theory argument list. -/
structure SimulArgs (env : VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (substs : Array (KExpr .anon))
    (argValues : List VExpr) : Prop where
  size_eq : substs.size = argValues.length
  translate : ∀ index, index < substs.size →
    TrKExprS env uvars nameOf trProj Delta substs[index]!
      argValues.reverse[index]!

namespace SimulArgs

/-- A typed suffix supplies `SimulArgs` for production's exact reversed
concrete array. -/
theorem ofValues
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {argValues : List VExpr} {resultV : VExpr}
    (h : TrAppSuffix.Values env uvars nameOf trProj Delta start args
      argValues resultV) :
    SimulArgs env uvars nameOf trProj Delta args.toArray.reverse
      argValues := by
  have hargs := h.argumentTranslations
  have hreverse := hargs.reverse
  constructor
  · simpa using hargs.length_eq
  · intro index hindex
    have hlistIndex : index < args.reverse.length := by simpa using hindex
    simpa using hreverse.getElemBang index hlistIndex

end SimulArgs
end RecM
end Ix.Tc
