import Ix.Tc.Verify.Whnf.Beta.SemanticCore

/-!
# Translated lambda-peel traces

The operational `BetaPeel` trace records concrete lambda bodies but not the
mixed translation contexts introduced by those binders.  This slice recovers
the exact nested `vlam` contexts and the structural translation of the final
body.  Subsequent simultaneous-instantiation proofs can therefore reason from
the actual binder stack rather than only from the number of consumed terms.
-/

namespace Ix.Tc
namespace RecM

namespace BetaPeel

/-- Structural translation data for every stage of a concrete lambda peel.
The final context is the original `Delta` extended by one `vlam` entry per
consumed argument, in the same innermost-first order used by de Bruijn
indices. -/
inductive Tr (env : Lean4Lean.VEnv) (uvars : Nat)
    (nameOf : Address -> Option Lean.Name) (trProj : RawProjRel)
    (Delta : KVLCtx) (start : KExpr .anon) (startV : Lean4Lean.VExpr) :
    List (KExpr .anon) -> KExpr .anon -> KVLCtx -> Lean4Lean.VExpr -> Prop
  | nil
      (hstart : TrKExprS env uvars nameOf trProj Delta start startV) :
      Tr env uvars nameOf trProj Delta start startV [] start Delta startV
  | snoc {consumed : List (KExpr .anon)}
      {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
      {ty body : KExpr .anon} {info : ExprInfo .anon}
      {arg : KExpr .anon} {currentDelta : KVLCtx}
      {A bodyV : Lean4Lean.VExpr}
      (hprefix : Tr env uvars nameOf trProj Delta start startV consumed
        (.lam name bi ty body info) currentDelta (.lam A bodyV))
      (hA : env.IsType uvars currentDelta.toCtx A)
      (hty : TrKExprS env uvars nameOf trProj currentDelta ty A)
      (hbody : TrKExprS env uvars nameOf trProj
        ((none, .vlam A) :: currentDelta) body bodyV) :
      Tr env uvars nameOf trProj Delta start startV (consumed ++ [arg])
        body ((none, .vlam A) :: currentDelta) bodyV

namespace Tr

/-- The final concrete body in a translated peel trace has the structural
translation stored at the trace endpoint. -/
theorem result
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : KExpr .anon} {startV : Lean4Lean.VExpr}
    {consumed : List (KExpr .anon)} {body : KExpr .anon}
    {bodyDelta : KVLCtx} {bodyV : Lean4Lean.VExpr}
    (h : Tr env uvars nameOf trProj Delta start startV consumed body
      bodyDelta bodyV) :
    TrKExprS env uvars nameOf trProj bodyDelta body bodyV := by
  cases h with
  | nil hstart => exact hstart
  | snoc _ _ _ hbody => exact hbody

/-- Every consumed lambda contributes exactly one Theory binder to the final
mixed context. -/
theorem bvars
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : KExpr .anon} {startV : Lean4Lean.VExpr}
    {consumed : List (KExpr .anon)} {body : KExpr .anon}
    {bodyDelta : KVLCtx} {bodyV : Lean4Lean.VExpr}
    (h : Tr env uvars nameOf trProj Delta start startV consumed body
      bodyDelta bodyV) :
    bodyDelta.bvars = Delta.bvars + consumed.length := by
  induction h with
  | nil => simp
  | snoc hp hA hty hbody ih =>
      simp [KVLCtx.bvars, ih]
      omega

end Tr

/-- A structural translation of the initial lambda chain determines a
translated peel trace and an exact structural translation of the final raw
body under the recovered binder context. -/
theorem translate
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start body : KExpr .anon}
    {consumed : List (KExpr .anon)} {startV : Lean4Lean.VExpr}
    (hpeel : BetaPeel start consumed body)
    (hstart : TrKExprS env uvars nameOf trProj Delta start startV) :
    exists bodyDelta bodyV,
      Tr env uvars nameOf trProj Delta start startV consumed body
        bodyDelta bodyV := by
  induction hpeel with
  | nil => exact ⟨Delta, startV, .nil hstart⟩
  | snoc hprefix ih =>
      obtain ⟨currentDelta, currentV, htrace⟩ := ih
      have hcurrent := htrace.result
      cases hcurrent with
      | lam hA hty hbody =>
          exact ⟨_, _, .snoc htrace hA hty hbody⟩

end BetaPeel
end RecM
end Ix.Tc
