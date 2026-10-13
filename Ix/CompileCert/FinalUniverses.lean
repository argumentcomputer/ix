import Ix.CompileCert.PreseedState

/-! Once the production preseed flag is set, successful universe compilation
preserves the entire primary universe table. This uses the actual no-growth
guard and requires no source, memo or index-map validity assumption. -/

namespace Ix.CompileCert.FinalUniverses

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.Interning
open UniversePipeline (Preserves internPrimaryCanonical internCanonical finishSpelling)

theorem rawRun_throw (error : CompileError) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (throw error : CompileM α) context before = (.error error, before) := rfl

theorem internMeta_frame (value : Ixon.Univ) :
    Preserves (fun state => (state.univs, state.univsFinal)) (internMetaUniv value) := by
  intro context before
  have arraySame := UniversePipeline.internMetaUniv_primary value context before
  have flagSame := congrArg BlockState.univsFinal (UniversePipeline.internMetaUniv_frame value context before)
  exact Prod.ext arraySame flagSame

theorem spelling_frame (raw canonical : Ixon.Univ) (index : UInt64) :
    Preserves (fun state => (state.univs, state.univsFinal)) (finishSpelling raw canonical index) := by
  rw [finishSpelling]
  split
  · exact Preserves.pure _ _
  · exact Preserves.bind (internMeta_frame raw) (fun _ => Preserves.pure _ _)

theorem primary_no_growth (raw canonical : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (finalized : before.univsFinal = true) (output : UInt64 × Option UInt64)
    (ran : rawRun (internPrimaryCanonical raw canonical) context before = (.ok output, after)) :
    after.univs = before.univs ∧ after.univsFinal = true := by
  rw [internPrimaryCanonical, rawRun_bind, rawRun_get] at ran
  dsimp only at ran
  rw [rawRun_bind] at ran
  cases found : before.univsIndex.get? canonical with
  | some index =>
    rw [internUniv_hit canonical context before found] at ran
    simp only [rawRun_bind, rawRun_get, finalized, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at ran
    have frame := spelling_frame raw canonical index context before
    rw [ran] at frame
    exact ⟨(Prod.mk.inj frame).1, (Prod.mk.inj frame).2.trans finalized⟩
  | none =>
    rw [internUniv_miss canonical context before found] at ran
    by_cases room : before.univs.size + 1 < UInt64.size
    · simp [room, rawRun_bind, rawRun_get, finalized, rawRun_throw] at ran
    · simp [room, checkedTableCount, rawRun_throw] at ran

theorem canonical_no_growth (raw canonical : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (finalized : before.univsFinal = true) (output : UInt64 × Option UInt64)
    (ran : rawRun (internCanonical raw canonical) context before = (.ok output, after)) :
    after.univs = before.univs ∧ after.univsFinal = true := by
  rw [internCanonical, rawRun_bind, rawRun_get] at ran
  dsimp only at ran
  split at ran
  · rw [rawRun_bind, rawRun_get] at ran
    dsimp only at ran
    split at ran
    · have frame := Preserves.bind (internMeta_frame canonical) (fun index => spelling_frame raw canonical index) context before
      rw [ran] at frame
      exact ⟨(Prod.mk.inj frame).1, (Prod.mk.inj frame).2.trans finalized⟩
    · exact primary_no_growth raw canonical context before after finalized output ran
  · exact primary_no_growth raw canonical context before after finalized output ran

theorem compile_no_growth (source : Level) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (finalized : before.univsFinal = true) (output : UInt64 × Option UInt64)
    (ran : rawRun (compileAndInternUnivCanon source) context before = (.ok output, after)) :
    after.univs = before.univs ∧ after.univsFinal = true := by
  rw [UniversePipeline.compileAndInternUnivCanon_eq] at ran
  obtain ⟨raw, rawState, rawRan, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  obtain ⟨canonical, canonicalState, canonRan, internRan⟩ := PreseedReferences.bind_ok _ _ context rawState output after rest
  have rawFrame := UniversePipeline.compileUniv_frame source context before
  rw [rawRan] at rawFrame
  have rawUnivs := congrArg BlockState.univs rawFrame
  have rawFinal := congrArg BlockState.univsFinal rawFrame
  have canonFrame : UniversePipeline.withoutCanonCache canonicalState = UniversePipeline.withoutCanonCache rawState := by
    rw [UniversePipeline.canonUnivCached_run] at canonRan
    cases found : rawState.canonUnivCache.get? raw
    all_goals
      rw [found] at canonRan
      obtain ⟨_, states⟩ := Prod.mk.inj canonRan
      cases states
      rfl
  have canonUnivs := congrArg BlockState.univs canonFrame
  have canonFinal := congrArg BlockState.univsFinal canonFrame
  have finished := canonical_no_growth raw canonical context canonicalState after (canonFinal.trans (rawFinal.trans finalized)) output internRan
  exact ⟨finished.1.trans (canonUnivs.trans rawUnivs), finished.2⟩

end Ix.CompileCert.FinalUniverses
