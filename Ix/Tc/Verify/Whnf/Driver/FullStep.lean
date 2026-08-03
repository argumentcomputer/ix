import Ix.Tc.Verify.Whnf.NoDelta.Reducer

/-!
# Full-WHNF one-step closure

Reducer closes the public no-delta reducer.  A full-WHNF iteration first runs
that reducer with full flags, then performs cycle detection and the outer
native, BitVec, Nat, Decidable, String, compact-Nat-offset, and delta stages.

In the no-acceleration layer the native, BitVec, and Decidable stages are
operationally impossible hits.  Nat and String reuse the exact contracts
already packaged by BaseReductions.  Delta unfolding remains a distinct semantic
boundary: unlike a miss, successful unfolding must justify both support for
the generated expression and its Theory meaning.
-/

namespace Ix.Tc
namespace RecM

/-- The Decidable acceleration gate satisfies the optional-reducer contract
in the no-acceleration layer because production returns `none` before
inspecting the expression or invoking a callback. -/
theorem tryReduceDecidable_noAccel_optional_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} :
    OptionalReduction.WF .noAccel semantics trProj world support
      tryReduceDecidable := by
  intro uvars Delta source sourceV s hsource htr
  intro methods hmethods hI
  rw [tryReduceDecidable_noAccel hI.2.2.1 source]
  exact ⟨hI, trivial⟩

/-- Complete fixed-context input for one production full-WHNF iteration.

All stages except delta are constructed from the same concrete no-delta
driver context.  Keeping delta as an `OptionalReduction.WF` field makes the
remaining admission obligation exact: a successful unfold must preserve the
state invariant, remain in finite run support, and denote a definitionally
equal Theory expression. -/
structure FullWhnfStepContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (keys : WhnfContextKeys)
    (fallback : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (Delta : KVLCtx) : Type where
  noDelta :
    NoDeltaDriverContext initial program requests keys fallback trProj world
      support Delta .FULL
  /-- Main's compact symbolic-Nat guard is a distinct reduction stage.  Its
  exact state/support/meaning contract remains explicit until its callback and
  intern paths are decomposed into finite run-scoped inputs. -/
  natOffsetStuck :
    OptionalReduction.WFAt .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars tryNatOffsetStuck
  delta :
    OptionalReduction.WFAt .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars deltaUnfoldOne

namespace FullWhnfStepContext

/-- The actual production full-WHNF step satisfies the exhaustive local
semantic contract for either successor policy in the no-acceleration layer.
Cycle hits and the final stuck branch retain the meaning established by
no-delta normalization; every successful outer reduction composes its own
meaning with that prefix through Theory transitivity. -/
theorem wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {keys : WhnfContextKeys}
    {fallback : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {Delta : KVLCtx}
    (context : FullWhnfStepContext initial program requests keys fallback
      trProj world support Delta)
    (natSuccMode : NatSuccMode) :
    WhnfStep.WF .noAccel
      (whnfCacheSemantics keys trProj fallback) trProj world support
      keys.uvars Delta
      (fun state : KExpr .anon × Std.HashSet Address => state.1)
      (whnfWithNatSuccModeStep natSuccMode) (fun _ _ => True) := by
  intro state s hsource
  rcases state with ⟨source, seen⟩
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  unfold whnfWithNatSuccModeStep
  apply RecM.WF.bind
    (RecM.WF.withInv
      (context.noDelta.wf natSuccMode hsourceSupport hsourceTr))
  intro reduced s₁ hreduced
  obtain ⟨_, hreducedSupport, hreducedPost⟩ := hreduced
  have hprefix :
      WhnfMeaning trProj world keys.uvars Delta source reduced :=
    WhnfPost.meaning hsourceTr hreducedPost
  obtain ⟨reducedV, hreducedTr, _⟩ := hreducedPost
  cases hcycle : seen.contains reduced.addr with
  | true =>
      simp only [if_true]
      apply RecM.WF.pure
      intro _
      exact ⟨hreducedSupport, hprefix⟩
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      apply RecM.WF.bind
        (RecM.WF.withInv
          (tryReduceNative_noAccel_optional_wf
            hreducedSupport hreducedTr))
      intro nativeResult s₂ hnative
      obtain ⟨hI₂, hnative⟩ := hnative
      cases nativeResult with
      | some result =>
          apply RecM.WF.pure
          intro _
          exact ⟨hnative.1,
            context.noDelta.structural.theory.transMeaning
              hI₂.2.1.wf hprefix hnative.2⟩
      | none =>
          apply RecM.WF.bind
            (RecM.WF.withInv
              (tryReduceBitvec_noAccel_optional_wf
                hreducedSupport hreducedTr))
          intro bitvecResult s₃ hbitvec
          obtain ⟨hI₃, hbitvec⟩ := hbitvec
          cases bitvecResult with
          | some result =>
              apply RecM.WF.pure
              intro _
              exact ⟨hbitvec.1,
                context.noDelta.structural.theory.transMeaning
                  hI₃.2.1.wf hprefix hbitvec.2⟩
          | none =>
              apply RecM.WF.bind
                (RecM.WF.withInv
                  ((context.noDelta.base.oracle natSuccMode).nat
                    hreducedSupport hreducedTr))
              intro natResult s₄ hnat
              obtain ⟨hI₄, hnat⟩ := hnat
              cases natResult with
              | some result =>
                  apply RecM.WF.pure
                  intro _
                  exact ⟨hnat.1,
                    context.noDelta.structural.theory.transMeaning
                      hI₄.2.1.wf hprefix hnat.2⟩
              | none =>
                  apply RecM.WF.bind
                    (RecM.WF.withInv
                      (tryReduceDecidable_noAccel_optional_wf
                        hreducedSupport hreducedTr))
                  intro decidableResult s₅ hdecidable
                  obtain ⟨hI₅, hdecidable⟩ := hdecidable
                  cases decidableResult with
                  | some result =>
                      apply RecM.WF.pure
                      intro _
                      exact ⟨hdecidable.1,
                        context.noDelta.structural.theory.transMeaning
                          hI₅.2.1.wf hprefix hdecidable.2⟩
                  | none =>
                      apply RecM.WF.bind
                        (RecM.WF.withInv
                          ((context.noDelta.base.oracle natSuccMode).string
                            hreducedSupport hreducedTr))
                      intro stringResult s₆ hstring
                      obtain ⟨hI₆, hstring⟩ := hstring
                      cases stringResult with
                      | some result =>
                          apply RecM.WF.pure
                          intro _
                          exact ⟨hstring.1,
                            context.noDelta.structural.theory.transMeaning
                              hI₆.2.1.wf hprefix hstring.2⟩
                      | none =>
                          apply RecM.WF.bind
                            (RecM.WF.withInv
                              (context.natOffsetStuck hreducedSupport
                                hreducedTr))
                          intro offsetResult s₇ hoffset
                          obtain ⟨hI₇, hoffset⟩ := hoffset
                          cases offsetResult with
                          | some result =>
                              apply RecM.WF.pure
                              intro _
                              exact ⟨hoffset.1,
                                context.noDelta.structural.theory.transMeaning
                                  hI₇.2.1.wf hprefix hoffset.2⟩
                          | none =>
                              apply RecM.WF.bind
                                (RecM.WF.withInv
                                  (context.delta hreducedSupport hreducedTr))
                              intro deltaResult s₈ hdelta
                              obtain ⟨hI₈, hdelta⟩ := hdelta
                              cases deltaResult with
                              | some result =>
                                  apply RecM.WF.pure
                                  intro _
                                  exact ⟨hdelta.1,
                                    context.noDelta.structural.theory.transMeaning
                                      hI₈.2.1.wf hprefix hdelta.2⟩
                              | none =>
                                  apply RecM.WF.pure
                                  intro _
                                  exact ⟨hreducedSupport, hprefix⟩

end FullWhnfStepContext
end RecM
end Ix.Tc
