import Ix.Tc.Verify.Check.BlockClassification

/-!
# State framing for successful coordinated routing

Block identity and classifier soundness are semantic claims.  This module
supplies the orthogonal operational fact needed by the `checkConst` driver:
if routing returns a coordinated block, every lazy lookup and classification
step preserves the caller's invariant up to the exact post-route state.
-/

namespace Ix.Tc

namespace RecM

private theorem runTcBindFrame {alpha beta : Type}
    (x : TcM .anon alpha) (k : alpha → TcM .anon beta)
    (state : TcState .anon) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- The direct block/kind router preserves an arbitrary lazy-ingress
invariant on every successful `some` route. -/
theorem coordinatedBlockIfKind_success_preserves
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {block : KId .anon} {kind : CheckBlockKind}
    {before after : TcState .anon}
    (hfault : TcM.LazyFaultPreserves I) (hbefore : I before)
    (hrun : (coordinatedBlockIfKind block kind).run methods before =
      .ok (some block) after) :
    I after := by
  cases coordinatedBlockIfKind_success_trace hrun with
  | run members loaded hlookup hclassification =>
      have hlookupPost := TcM.tryGetBlock_wf hfault block before hbefore
      rw [hlookup] at hlookupPost
      have hclassPost := classifyBlock_wf (methods := methods) hfault members
        loaded hlookupPost.1
      rw [hclassification] at hclassPost
      exact hclassPost.1

/-- The complete production router preserves an arbitrary lazy-ingress
invariant whenever it successfully selects a coordinated block.  The
constructor path includes the parent-inductive lookup before the direct
block/kind router. -/
theorem coordinatedBlockFor_some_preserves
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {concrete : KConst .anon} {routed : KId .anon}
    {before after : TcState .anon}
    (hfault : TcM.LazyFaultPreserves I) (hbefore : I before)
    (hrun : (coordinatedBlockFor concrete).run methods before =
      .ok (some routed) after) :
    I after := by
  cases concrete with
  | defn name levelParams defKind safety hints levels type value leanAll owner =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .defn methods before after
          (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      exact coordinatedBlockIfKind_success_preserves hfault hbefore
        (by simpa [coordinatedBlockFor] using hrun)
  | recr name levelParams k isUnsafe levels params indices motives minors owner
      memberIdx type rules leanAll =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .recursor methods before
          after (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      exact coordinatedBlockIfKind_success_preserves hfault hbefore
        (by simpa [coordinatedBlockFor] using hrun)
  | axio =>
      simp only [coordinatedBlockFor] at hrun
      cases hrun
  | quot =>
      simp only [coordinatedBlockFor] at hrun
      cases hrun
  | indc name levelParams levels params indices isUnsafe owner memberIdx type
      ctors leanAll =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .inductive' methods before
          after (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      exact coordinatedBlockIfKind_success_preserves hfault hbefore
        (by simpa [coordinatedBlockFor] using hrun)
  | ctor name levelParams isUnsafe levels parent cidx params fields type =>
      unfold coordinatedBlockFor at hrun
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
      rw [runTcBindFrame] at hrun
      cases hlookup : (monadLift (TcM.tryGetConst parent) :
          TcM .anon (Option (KConst .anon))) before with
      | error err failed => simp [hlookup] at hrun
      | ok found afterLookup =>
          have hlookup' : TcM.tryGetConst parent before =
              .ok found afterLookup := hlookup
          have hlookupPost := TcM.tryGetConst_wf hfault parent before hbefore
          rw [hlookup'] at hlookupPost
          rw [hlookup] at hrun
          cases found with
          | none =>
              simp only at hrun
              cases hrun
          | some parentConst =>
              cases parentConst with
              | indc parentName parentLevelParams parentLevels parentParams
                  parentIndices parentUnsafe owner parentMemberIdx parentType
                  parentCtors parentLeanAll =>
                  simp only at hrun
                  have hroute : routed = owner :=
                    coordinatedBlockIfKind_some_eq owner routed .inductive'
                      methods afterLookup after hrun
                  subst routed
                  exact coordinatedBlockIfKind_success_preserves hfault
                    hlookupPost.1 hrun
              | defn => simp only at hrun; cases hrun
              | axio => simp only at hrun; cases hrun
              | quot => simp only at hrun; cases hrun
              | ctor => simp only at hrun; cases hrun
              | recr => simp only at hrun; cases hrun

end RecM

end Ix.Tc
