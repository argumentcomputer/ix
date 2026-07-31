import Ix.Tc.Verify.DefEq.NatOffset
import Ix.Tc.Verify.Whnf.Iota.NatOffset

/-!
# Nat-offset decomposition and reconstruction

The optimized DefEq branch parses both operands as a base plus an offset,
removes their common positive suffix, rebuilds the two remainders, and invokes
the recursive DefEq callback once.  Soundness needs only the forward
direction: equality of the rebuilt remainders lifts through the common chain
of `Nat.succ` applications.  No injectivity or completeness claim is used.

This module separates unconditional state safety from the one semantic fact
about successful parser/rebuilder executions.  The latter is indexed by the
exact production runs, so it cannot authorize an unrelated generated term.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace TcM.WF

/-- Retain the invariant and exact successful execution selected by a Hoare
triple.  This combines the two facts needed at execution-indexed semantic
boundaries without giving those boundaries any state authority. -/
theorem withInvRunEq {I : TcState m → Prop} {s : TcState m}
    {x : TcM m α} {Q : α → TcState m → Prop}
    {E : TcError m → TcState m → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => I after ∧ Q value after ∧
        x s = .ok value after)
      E := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact hpost

end TcM.WF

namespace RecM

/-- Semantic meaning of one rebuilt remainder after removing `common`
successors from the source. -/
def NatOffsetRemainderMeaning (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (sourceV : VExpr) (common : Nat) (result : KExpr .anon) : Prop :=
  support result ∧
    ∃ resultV,
      TrKExprS world.venv uvars world.nameOf trProj Delta result resultV ∧
      world.venv.HasType uvars Delta.toCtx resultV .nat ∧
      world.venv.IsDefEqU uvars Delta.toCtx sourceV
        (natSuccIterV common resultV)

/-- Exact semantic boundary for a successful decomposition followed by the
actual production rebuild.  The two executions may be separated by other
read-only parsing work, so both starting invariants are explicit. -/
structure NatOffsetReflection (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {source : KExpr .anon} {sourceV : VExpr}
      {base : Option (KExpr .anon)} {total common : Nat}
      {decomposeBefore decomposeAfter rebuildBefore rebuildAfter :
        TcState .anon} {result : KExpr .anon},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    Methods.WFAt layer semantics trProj world support uvars methods →
    WhnfStateInv layer semantics trProj world support uvars Delta
      decomposeAfter →
    WhnfStateInv layer semantics trProj world support uvars Delta
      rebuildAfter →
    (natOffsetDecompose source).run methods decomposeBefore =
      .ok (some (base, total)) decomposeAfter →
    common ≤ total →
    (natOffsetRebuild base (total - common)).run methods rebuildBefore =
      .ok result rebuildAfter →
    NatOffsetRemainderMeaning trProj world support uvars Delta sourceV
      common result

/-- Primitive authority used only to lift recursive equality through the
common successor suffix. -/
structure NatOffsetCandidateContext (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  table : ∀ prims, prims.CanonicalAnon →
    NoDeltaPrimitiveTableAgrees world prims
  theoryPrimitives : world.venv.HasPrimitives
  reflection : NatOffsetReflection layer semantics trProj world support

/-- `natOffsetDecompose` is read-only on every hit, miss, and bounded-parser
path. -/
theorem natOffsetDecompose_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (source : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((natOffsetDecompose source).run methods)
      (fun _ _ => True) := by
  unfold natOffsetDecompose
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (prims_state_wf methods s)
  intro prims afterRead _
  cases hextract : extractNatValue source prims with
  | some value =>
      simp only
      exact TcM.WF.pure fun _ => trivial
  | none =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind (natOffset_state_wf methods source 0 afterRead)
      intro parsed afterOffset _
      cases parsed with
      | none => exact TcM.WF.pure fun _ => trivial
      | some pair =>
          rcases pair with ⟨base, offset⟩
          cases hzero : offset == 0 with
          | true =>
              simp only [hzero, if_true]
              exact TcM.WF.pure fun _ => trivial
          | false =>
              simp only [hzero, Bool.false_eq_true, if_false]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind (prims_state_wf methods afterOffset)
              intro currentPrims afterSecondRead _
              cases hbase : extractNatValue base currentPrims with
              | none =>
                  simp only
                  exact TcM.WF.pure fun _ => trivial
              | some value =>
                  simp only
                  exact TcM.WF.pure fun _ => trivial

/-- `natOffsetRebuild` either returns pure syntax or performs the already
proved read-only `mkNatAdd` primitive-table query. -/
theorem natOffsetRebuild_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (base : Option (KExpr .anon))
    (remainder : Nat) (s : TcState .anon) :
    TcM.WF I s ((natOffsetRebuild base remainder).run methods)
      (fun _ _ => True) := by
  cases base with
  | none =>
      exact TcM.WF.pure fun _ => trivial
  | some base =>
      cases hzero : remainder == 0 with
      | true =>
          simp only [natOffsetRebuild, hzero, if_true]
          exact TcM.WF.pure fun _ => trivial
      | false =>
          simp only [natOffsetRebuild, hzero, Bool.false_eq_true, if_false]
          exact mkNatAdd_state_wf methods base
            (natExprFromValue remainder) s

/-- Complete production branch after both allocation-free candidate guards
accept.  Positive recursive equality is transported through the common
successor suffix; every parser miss and the zero-common-offset case remains
an ordinary `none`. -/
theorem tryDefEqOffsetAfterCandidates_wf
    {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (context : NatOffsetCandidateContext .noAccel semantics trProj world
      support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterCandidates left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  intro methods hmethods
  unfold tryDefEqOffsetAfterCandidates
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (TcM.WF.withInvRunEq <|
      natOffsetDecompose_state_wf methods left state)
  intro leftResult afterLeft hleftResult
  rcases hleftResult with ⟨hILeft, _, hleftRun⟩
  cases leftResult with
  | none => exact TcM.WF.pure fun _ => trivial
  | some leftParts =>
      rcases leftParts with ⟨baseLeft, leftOffset⟩
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (TcM.WF.withInvRunEq <|
          natOffsetDecompose_state_wf methods right afterLeft)
      intro rightResult afterRight hrightResult
      rcases hrightResult with ⟨hIRight, _, hrightRun⟩
      cases rightResult with
      | none => exact TcM.WF.pure fun _ => trivial
      | some rightParts =>
          rcases rightParts with ⟨baseRight, rightOffset⟩
          cases hzero : (min leftOffset rightOffset == 0) with
          | true =>
              simp only [hzero, if_true]
              exact TcM.WF.pure fun _ => trivial
          | false =>
              simp only [hzero, Bool.false_eq_true, if_false, pure_bind]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (TcM.WF.withInvRunEq <|
                  natOffsetRebuild_state_wf methods baseLeft
                    (leftOffset - min leftOffset rightOffset) afterRight)
              intro rebuiltLeft afterRebuildLeft hrebuiltLeft
              rcases hrebuiltLeft with
                ⟨hIRebuildLeft, _, hleftRebuildRun⟩
              have hleftMeaning := context.reflection.success
                hleftSupport hleft hmethods hILeft hIRebuildLeft hleftRun
                (Nat.min_le_left _ _) hleftRebuildRun
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (TcM.WF.withInvRunEq <|
                  natOffsetRebuild_state_wf methods baseRight
                    (rightOffset - min leftOffset rightOffset)
                    afterRebuildLeft)
              intro rebuiltRight afterRebuildRight hrebuiltRight
              rcases hrebuiltRight with
                ⟨hIRebuildRight, _, hrightRebuildRun⟩
              have hrightMeaning := context.reflection.success
                hrightSupport hright hmethods hIRight hIRebuildRight
                hrightRun (Nat.min_le_right _ _) hrightRebuildRun
              rcases hleftMeaning with
                ⟨hrebuiltLeftSupport, rebuiltLeftV, hrebuiltLeftTr,
                  hrebuiltLeftType, hleftReconstruction⟩
              rcases hrightMeaning with
                ⟨hrebuiltRightSupport, rebuiltRightV, hrebuiltRightTr,
                  hrebuiltRightType, hrightReconstruction⟩
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                ((RecM.isDefEqCall_wf hrebuiltLeftSupport
                  hrebuiltRightSupport hrebuiltLeftTr hrebuiltRightTr)
                  methods hmethods)
              intro answer afterDefEq hanswer
              exact TcM.WF.pure fun hIFinal htrue => by
                have htable := context.table afterDefEq.prims
                  hIFinal.noAccel_primitives
                have hsucc := natSucc_hasType
                  (uvars := uvars) (Delta := Delta)
                  hIFinal.1.core.trustedCatalog htable
                  context.theoryPrimitives
                have hlift := natSuccIterV_congr world.venvWF
                  hIFinal.2.1.wf.toCtx hsucc hrebuiltLeftType
                  (hanswer htrue) (min leftOffset rightOffset)
                exact hleftReconstruction.trans world.venvWF
                  hIFinal.2.1.wf <|
                  hlift.trans world.venvWF hIFinal.2.1.wf
                    hrightReconstruction.symm

namespace TryDefEqOffsetAfterCandidates

/-- Package the production branch as the exact continuation contract used by
the outer Nat-offset prefix. -/
theorem ofContext
    {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : NatOffsetCandidateContext .noAccel semantics trProj world
      support) :
    TryDefEqOffsetAfterCandidates.WFAt .noAccel semantics trProj world
      support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqOffsetAfterCandidates_wf context hleftSupport hrightSupport
    hleft hright

end TryDefEqOffsetAfterCandidates

end RecM

end Ix.Tc
