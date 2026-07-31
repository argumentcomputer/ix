import Ix.Tc.Verify.DefEq.ProjectionProbe

/-!
# Lazy-delta loop finishing checks

After a productive unfold, one lazy-delta iteration performs address equality
and the cheap structural comparison before returning the transformed pair to
the bounded driver.  This module discharges both accepting checks against the
current pair and transports their result back through the loop invariant.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- The final address/structural checks either produce a sound positive
answer or return the unchanged current pair as the next loop state. -/
theorem finishDefEqLazyDeltaStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr} {left right : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (finishDefEqLazyDeltaStep left right)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold finishDefEqLazyDeltaStep
  cases haddr : left.addr == right.addr with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun hI _ =>
        hleftEq.trans world.venvWF hI.2.1.wf <|
          (DefEqMeaning.of_translations theory hI.2.1.wf hleft hright
            (DefEqMeaning.of_addr_beq theory hI.2.1 hcollision
              hpair.leftSupport hpair.rightSupport hleft haddr) rfl).trans
            world.venvWF hI.2.1.wf hrightEq.symm
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind <|
        quickDefEq_wf theory hcollision hsorts hstructural
          hpair.leftSupport hpair.rightSupport hleft hright
      intro accepted afterQuick haccepted
      cases accepted with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun hI _ =>
            hleftEq.trans world.venvWF hI.2.1.wf <|
              (haccepted rfl).trans world.venvWF hI.2.1.wf
                hrightEq.symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact RecM.WF.pure fun _ => hpair

end RecM

end Ix.Tc
