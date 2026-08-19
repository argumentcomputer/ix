import Ix.Tc.Verify.Check.BlockIdentity
import Ix.Tc.Verify.Infer.Constants

/-!
# Soundness of production block routing

This module follows `coordinatedBlockFor` rather than replacing it with an
abstract dispatcher.  The direct definition/inductive/recursor cases return
their recorded owner.  The constructor case must additionally show that the
successful concrete parent lookup is the exact catalogued inductive and that
the constructor itself belongs to that parent's exact member array.
-/

namespace Ix.Tc

namespace RecM

private theorem runTcBind {alpha beta : Type}
    (x : TcM .anon alpha) (k : alpha → TcM .anon beta)
    (state : TcState .anon) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- `coordinatedBlockIfKind` can fail or return `none`, but any successful
`some` result is exactly its input block key. -/
theorem coordinatedBlockIfKind_some_eq
    (candidate result : KId .anon) (expected : CheckBlockKind)
    (methods : Methods .anon) (before after : TcState .anon)
    (hrun : (coordinatedBlockIfKind candidate expected).run methods before =
      .ok (some result) after) :
    result = candidate := by
  unfold coordinatedBlockIfKind at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  rw [runTcBind] at hrun
  cases hblock : (monadLift (TcM.tryGetBlock candidate) :
      TcM .anon (Option (Array (KId .anon)))) before with
  | error err failed => simp [hblock] at hrun
  | ok found afterBlock =>
    rw [hblock] at hrun
    cases found with
    | none =>
      simp only at hrun
      change EStateM.Result.ok none afterBlock =
        EStateM.Result.ok (some result) after at hrun
      cases hrun
    | some members =>
      simp only at hrun
      rw [ReaderT.run_bind, runTcBind] at hrun
      cases hclass : ((classifyBlock members).try?).run methods afterBlock with
      | error err failed => simp [hclass] at hrun
      | ok classified afterClass =>
        rw [hclass] at hrun
        cases classified with
        | none =>
          simp only at hrun
          change EStateM.Result.ok none afterClass =
            EStateM.Result.ok (some result) after at hrun
          cases hrun
        | some actual =>
          simp only at hrun
          split at hrun
          · change EStateM.Result.ok (some candidate) afterClass =
              EStateM.Result.ok (some result) after at hrun
            cases hrun
            rfl
          · change EStateM.Result.ok none afterClass =
              EStateM.Result.ok (some result) after at hrun
            cases hrun

/-- A successful caught classifier probe is exactly a successful execution
of the probed computation, including its post-state. -/
private theorem tryQuestion_some_eq
    {methods : Methods .anon} {x : RecM .anon α}
    {before after : TcState .anon} {value : α}
    (hrun : (try? x).run methods before = .ok (some value) after) :
    x.run methods before = .ok value after := by
  unfold try? at hrun
  change EStateM.tryCatch
    (EStateM.bind (x.run methods)
      (fun a state => EStateM.Result.ok (some a) state)) _ before = _ at hrun
  unfold EStateM.bind EStateM.tryCatch at hrun
  cases hx : x.run methods before with
  | ok found reached =>
      simp only [hx] at hrun
      cases hrun
      rfl
  | error err failed =>
      have hrestore : EStateM.Backtrackable.restore failed
          (EStateM.Backtrackable.save before) = failed := rfl
      simp only [hx, hrestore] at hrun
      change EStateM.Result.ok none failed =
        EStateM.Result.ok (some value) after at hrun
      cases hrun

/-- Exact internal execution selected by a successful block-kind router.
The classifier equation is exposed without its caught-error wrapper. -/
inductive CoordinatedBlockIfKindSuccessTrace
    (methods : Methods .anon) (block : KId .anon)
    (expected : CheckBlockKind) (before after : TcState .anon) : Prop where
  | run (members : Array (KId .anon)) (loaded : TcState .anon) :
      TcM.tryGetBlock block before = .ok (some members) loaded →
      (classifyBlock members).run methods loaded = .ok expected after →
      CoordinatedBlockIfKindSuccessTrace methods block expected before after

/-- Invert a successful `coordinatedBlockIfKind` call into its exact lookup
and successful homogeneous classification. -/
theorem coordinatedBlockIfKind_success_trace
    {methods : Methods .anon} {block : KId .anon}
    {expected : CheckBlockKind} {before after : TcState .anon}
    (hrun : (coordinatedBlockIfKind block expected).run methods before =
      .ok (some block) after) :
    CoordinatedBlockIfKindSuccessTrace methods block expected before after := by
  unfold coordinatedBlockIfKind at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  rw [runTcBind] at hrun
  cases hlookup : (monadLift (TcM.tryGetBlock block) :
      TcM .anon (Option (Array (KId .anon)))) before with
  | error err failed => simp [hlookup] at hrun
  | ok found loaded =>
      rw [hlookup] at hrun
      cases found with
      | none =>
          simp only at hrun
          cases hrun
      | some members =>
          simp only at hrun
          rw [ReaderT.run_bind, runTcBind] at hrun
          cases hclass : ((classifyBlock members).try?).run methods loaded with
          | error err failed => simp [hclass] at hrun
          | ok classified classifiedState =>
              rw [hclass] at hrun
              cases classified with
              | none =>
                  simp only at hrun
                  cases hrun
              | some actual =>
                  simp only at hrun
                  split at hrun
                  · have hactual : actual = expected := by
                      cases actual <;> cases expected
                      all_goals first
                        | rfl
                        | (change false = true at *; contradiction)
                    subst actual
                    cases hrun
                    exact .run members loaded hlookup
                      (tryQuestion_some_eq hclass)
                  · cases hrun

/-- A successful production route places the requested declaration in the
exact immutable member array of the returned block.  Constructor routing is
resolved through the exact parent inductive loaded by production.

The theorem is representation-only: neither the requested declaration nor
its peers become trusted here. -/
theorem coordinatedBlockFor_some_exact
    {trProj : RawProjRel} {world : VerifyWorld}
    {id routed : KId .anon} {concrete : KConst .anon}
    {methods : Methods .anon} {before after : TcState .anon}
    (hcatalog : world.catalog id = some concrete)
    (hblocks : ExactCoordinatedCatalog world)
    (hstate : BlockStateWF trProj before world)
    (hfault : TcM.LazyFaultPreserves
      (fun state => BlockStateWF trProj state world))
    (hrun : (coordinatedBlockFor concrete).run methods before =
      .ok (some routed) after) :
    ∃ members kind,
      ExactCheckBlock world routed members kind ∧ id ∈ members := by
  cases concrete with
  | defn name levelParams defKind safety hints levels type value leanAll owner =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .defn methods before after
          (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      have hshape :
          (KConst.defn name levelParams defKind safety hints levels type value
            leanAll owner).IsMemberOfKind world.catalog owner .defn := by
        rfl
      obtain ⟨members, hexact, hmember⟩ :=
        hblocks.resolve hcatalog hshape
      exact ⟨members, .defn, hexact, hmember⟩
  | recr name levelParams k isUnsafe levels params indices motives minors owner
      memberIdx type rules leanAll =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .recursor methods before
          after (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      have hshape :
          (KConst.recr name levelParams k isUnsafe levels params indices
            motives minors owner memberIdx type rules leanAll).IsMemberOfKind
              world.catalog owner .recursor := by
        rfl
      obtain ⟨members, hexact, hmember⟩ :=
        hblocks.resolve hcatalog hshape
      exact ⟨members, .recursor, hexact, hmember⟩
  | axio name levelParams isUnsafe levels type =>
      simp only [coordinatedBlockFor] at hrun
      change EStateM.Result.ok none before =
        EStateM.Result.ok (some routed) after at hrun
      cases hrun
  | quot name levelParams quotKind levels type =>
      simp only [coordinatedBlockFor] at hrun
      change EStateM.Result.ok none before =
        EStateM.Result.ok (some routed) after at hrun
      cases hrun
  | indc name levelParams levels params indices isUnsafe owner memberIdx type
      ctors leanAll =>
      have hroute : routed = owner :=
        coordinatedBlockIfKind_some_eq owner routed .inductive' methods before
          after (by simpa [coordinatedBlockFor] using hrun)
      subst routed
      have hshape :
          (KConst.indc name levelParams levels params indices isUnsafe owner
            memberIdx type ctors leanAll).IsMemberOfKind world.catalog owner
              .inductive' := by
        rfl
      obtain ⟨members, hexact, hmember⟩ :=
        hblocks.resolve hcatalog hshape
      exact ⟨members, .inductive', hexact, hmember⟩
  | ctor name levelParams isUnsafe levels parent cidx params fields type =>
      unfold coordinatedBlockFor at hrun
      simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
      rw [runTcBind] at hrun
      cases hlookup : (monadLift (TcM.tryGetConst parent) :
          TcM .anon (Option (KConst .anon))) before with
      | error err failed => simp [hlookup] at hrun
      | ok found afterLookup =>
        have hlookup' : TcM.tryGetConst parent before =
            .ok found afterLookup := hlookup
        have hlookupWF := TcM.tryGetConst_wf hfault parent before hstate
        rw [hlookup'] at hlookupWF
        have hstateLookup : BlockStateWF trProj afterLookup world :=
          hlookupWF.1
        rw [hlookup] at hrun
        cases found with
        | none =>
          simp only at hrun
          change EStateM.Result.ok none afterLookup =
            EStateM.Result.ok (some routed) after at hrun
          cases hrun
        | some parentConst =>
          have hparentLoaded : afterLookup.env.get? parent = some parentConst :=
            TcM.tryGetConst_success_loaded hlookup'
          have hparentCatalog : world.catalog parent = some parentConst :=
            hstateLookup.core.loaded hparentLoaded
          cases parentConst with
          | defn =>
              simp only at hrun
              change EStateM.Result.ok none afterLookup =
                EStateM.Result.ok (some routed) after at hrun
              cases hrun
          | recr =>
              simp only at hrun
              change EStateM.Result.ok none afterLookup =
                EStateM.Result.ok (some routed) after at hrun
              cases hrun
          | axio =>
              simp only at hrun
              change EStateM.Result.ok none afterLookup =
                EStateM.Result.ok (some routed) after at hrun
              cases hrun
          | quot =>
              simp only at hrun
              change EStateM.Result.ok none afterLookup =
                EStateM.Result.ok (some routed) after at hrun
              cases hrun
          | @indc parentName parentLevelParams parentLevels parentParams
              parentIndices parentUnsafe owner parentMemberIdx parentType
              parentCtors parentLeanAll =>
              simp only at hrun
              have hroute : routed = owner :=
                coordinatedBlockIfKind_some_eq owner routed .inductive'
                  methods afterLookup after hrun
              subst routed
              have hshape :
                  (KConst.ctor name levelParams isUnsafe levels parent cidx
                    params fields type).IsMemberOfKind world.catalog owner
                      .inductive' := by
                refine ⟨KConst.indc parentName parentLevelParams parentLevels
                  parentParams parentIndices parentUnsafe owner parentMemberIdx
                  parentType parentCtors parentLeanAll, hparentCatalog, ?_⟩
                rfl
              obtain ⟨members, hexact, hmember⟩ :=
                hblocks.resolve hcatalog hshape
              exact ⟨members, .inductive', hexact, hmember⟩
          | ctor =>
              simp only at hrun
              change EStateM.Result.ok none afterLookup =
                EStateM.Result.ok (some routed) after at hrun
              cases hrun

end RecM

end Ix.Tc
