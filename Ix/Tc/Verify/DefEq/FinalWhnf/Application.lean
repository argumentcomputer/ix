import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts

/-!
# Final-WHNF application comparison

This module proves the exact short-circuiting application branch of the
constructor-directed final comparison.  Argument equality is requested only
after function equality succeeds, matching the production order.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite child coverage for supported applications selected by the final
WHNF comparator. -/
structure FinalWhnfApplicationResources (support : RunSupport) : Prop where
  components : ∀ {fn arg : KExpr .anon} {info : ExprInfo .anon},
    support (.app fn arg info) → support fn ∧ support arg

namespace RecM

/-- Positive-result contract for the exact application helper. -/
def TryDefEqWhnfApp.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftFn leftArg rightFn rightArg}
      {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : VExpr},
    support (.app leftFn leftArg leftInfo) →
    support (.app rightFn rightArg rightInfo) →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app leftFn leftArg leftInfo) leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app rightFn rightArg rightInfo) rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfApp leftFn leftArg rightFn rightArg)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Exhaustive execution and semantic proof of the direct application
branch. -/
theorem tryDefEqWhnfApp_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftFn leftArg rightFn rightArg : KExpr .anon}
    {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : VExpr}
    (resources : FinalWhnfApplicationResources support)
    (hleftSupport : support (.app leftFn leftArg leftInfo))
    (hrightSupport : support (.app rightFn rightArg rightInfo))
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app leftFn leftArg leftInfo) leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.app rightFn rightArg rightInfo) rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfApp leftFn leftArg rightFn rightArg)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  obtain ⟨hleftFnSupport, hleftArgSupport⟩ :=
    resources.components hleftSupport
  obtain ⟨hrightFnSupport, hrightArgSupport⟩ :=
    resources.components hrightSupport
  cases hleft with
  | app hleftFnType hleftArgType hleftFn hleftArg =>
      cases hright with
      | app hrightFnType hrightArgType hrightFn hrightArg =>
          unfold tryDefEqWhnfApp
          apply RecM.WF.bind <|
            RecM.isDefEqCall_wf hleftFnSupport hrightFnSupport hleftFn
              hrightFn
          intro functionsEqual afterFunction hfunctions
          cases functionsEqual with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact RecM.WF.pure fun _ => trivial
          | true =>
              simp only [if_true]
              apply RecM.WF.bind <|
                RecM.isDefEqCall_wf hleftArgSupport hrightArgSupport
                  hleftArg hrightArg
              intro argumentsEqual afterArgument harguments
              cases argumentsEqual with
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact RecM.WF.pure fun _ => trivial
              | true =>
                  simp only [if_true]
                  exact RecM.WF.pure fun hI _ => by
                    have hDelta : KVLCtx.WF world.venv uvars Delta :=
                      hI.2.1.wf
                    have hfunctionTyped :=
                      (hfunctions rfl).of_l world.venvWF hDelta.toCtx
                        hleftFnType
                    have hargumentTyped :=
                      (harguments rfl).of_l world.venvWF hDelta.toCtx
                        hleftArgType
                    exact (hfunctionTyped.appDF hargumentTyped).toU

namespace TryDefEqWhnfApp

/-- Package the application proof for the structural-prefix assembly. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (resources : FinalWhnfApplicationResources support) :
    TryDefEqWhnfApp.WFAt layer semantics trProj world support uvars := by
  intro Delta state leftFn leftArg rightFn rightArg leftInfo rightInfo
    leftV rightV hleftSupport hrightSupport hleft hright
  exact tryDefEqWhnfApp_wf resources hleftSupport hrightSupport hleft hright

end TryDefEqWhnfApp

end RecM

end Ix.Tc
