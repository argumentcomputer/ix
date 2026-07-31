import Ix.Tc.Verify.DefEq.SpineArguments

/-!
# General application-spine comparison

The post-delta application tier compares two nonempty application spines.  It
first compares the collected heads, then reuses the common left-to-right
argument loop.  A positive result is reconstructed through the complete typed
spines; constructor misses and unequal arities carry no semantic claim.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite support coverage for the head and arguments selected by the exact
production `collectSpine` executions. -/
structure ApplicationSpineResources (support : RunSupport) : Prop where
  components : ∀ {f arg : KExpr .anon} {info : ExprInfo .anon}
      {head : KExpr .anon} {args : Array (KExpr .anon)},
    support (.app f arg info) →
    (.app f arg info : KExpr .anon).collectSpine = (head, args) →
      support head ∧ ∀ child, child ∈ args.toList → support child

namespace RecM

/-- Exact positive-result contract for the production application-spine
probe.  A negative result is deliberately unconstrained. -/
def TryDefEqApp.WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqApp left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Complete execution proof of `tryDefEqApp`. -/
theorem tryDefEqApp_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : ApplicationSpineResources support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqApp left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases left <;> cases right <;>
    simp only [tryDefEqApp, Bool.not_false, Bool.not_true]
  all_goals
    first
    | exact RecM.WF.pure fun _ h => by contradiction
    | skip
  case app fLeft argLeft infoLeft fRight argRight infoRight =>
    let left : KExpr .anon := .app fLeft argLeft infoLeft
    let right : KExpr .anon := .app fRight argRight infoRight
    rcases hleftCollect : left.collectSpine with ⟨leftHead, leftArgs⟩
    rcases hrightCollect : right.collectSpine with ⟨rightHead, rightArgs⟩
    cases hsize : leftArgs.size != rightArgs.size with
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ h => by contradiction
    | false =>
        simp only [Bool.false_or, Bool.false_eq_true, if_false]
        have hlength : leftArgs.toList.length = rightArgs.toList.length := by
          simpa only [Array.length_toList] using
            eq_of_beq (show (leftArgs.size == rightArgs.size) = true by
              simpa using hsize)
        have hleftSpine := trAppSpine_of_collectSpine hleft hleftCollect
        have hrightSpine := trAppSpine_of_collectSpine hright hrightCollect
        obtain ⟨leftHeadV, hleftHead⟩ := hleftSpine.headTr
        obtain ⟨rightHeadV, hrightHead⟩ := hrightSpine.headTr
        have hleftComponents := resources.components hleftSupport hleftCollect
        have hrightComponents :=
          resources.components hrightSupport hrightCollect
        apply RecM.WF.bind <|
          RecM.isDefEqCall_wf hleftComponents.1 hrightComponents.1
            hleftHead hrightHead
        intro headsEqual afterHead hheadsEqual
        cases headsEqual with
        | false =>
            simp only [Bool.not_false, if_true]
            exact RecM.WF.pure fun _ h => by contradiction
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              pure_bind]
            apply RecM.WF.mono (RecM.WF.withInv <|
              allDefEqSpineArgs_wf _ (by
              intro pair hmem
              have hmem' : pair ∈
                  leftArgs.toList.zip rightArgs.toList := by
                simpa only [Array.toList_zip] using hmem
              have hleftMem := left_mem_of_pair_mem_zip hmem'
              have hrightMem := right_mem_of_pair_mem_zip hmem'
              obtain ⟨pairLeftV, pairLeftTy, hpairLeftTyped, hpairLeft⟩ :=
                hleftSpine.argument hleftMem
              obtain ⟨pairRightV, pairRightTy, hpairRightTyped, hpairRight⟩ :=
                hrightSpine.argument hrightMem
              exact ⟨hleftComponents.2 _ hleftMem,
                hrightComponents.2 _ hrightMem,
                pairLeftV, pairRightV, hpairLeft, hpairRight⟩))
            · intro argsEqual final hpost htrue
              rcases hpost with ⟨hI, hargsEqual⟩
              have hDelta : KVLCtx.WF world.venv uvars Delta :=
                hI.2.1.wf
              apply TrAppSpine.defEq_of_zip theory hDelta hleftSpine
                hrightSpine hlength
              · intro arbitraryLeftV arbitraryRightV arbitraryLeft
                  arbitraryRight
                exact TrAppSpine.argumentDefEq theory hDelta
                  ⟨leftHeadV, rightHeadV, hleftHead, hrightHead,
                    hheadsEqual rfl⟩ arbitraryLeft arbitraryRight
              · intro pair hmem
                exact hargsEqual htrue pair (by
                  simpa only [Array.toList_zip] using hmem)
            · intro _ _ _
              trivial

namespace TryDefEqApp

/-- Package the concrete spine proof as the helper contract consumed by the
stopped lazy-delta continuation. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : ApplicationSpineResources support) :
    TryDefEqApp.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqApp_wf theory resources hleftSupport hrightSupport hleft
    hright

end TryDefEqApp

end RecM

end Ix.Tc
