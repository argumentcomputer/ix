import Ix.CompileCert.PreseedState

/-! # After preseeding, universe compilation does not grow the primary table

Once the preseed has marked the primary universe table final
(`PreseedState.preseed_final`), a successful `compileAndInternUnivCanon`
leaves the table exactly as it was (`compile_no_growth`): a canonical form
the table lacks trips the production guard (canonicity §10.6 V3), so a
success only hits preseeded entries. This uses the guard itself, with no
memo, index or source premise. `FinalUniverses`. -/

namespace Ix.CompileCert.FinalUniverses

open Ix.CompileM Ix.CompileCert Ix.CompileCert.Interning Ix.CompileCert.UniversePipeline

theorem internMetaUniv_univs (value : Ixon.Univ) :
    Preserves (fun state => (state.univs, state.univsFinal)) (internMetaUniv value) := by
  intro context before
  have univs := (internMetaUniv_tables value context before).2.1
  have flag : (rawRun (internMetaUniv value) context before).2.univsFinal = before.univsFinal := by
    have same := congrArg BlockState.univsFinal (internMetaUniv_frame value context before)
    exact same
  exact Prod.ext univs flag

theorem finishSpelling_univs (raw canon : Ixon.Univ) (index : UInt64) :
    Preserves (fun state => (state.univs, state.univsFinal)) (finishSpelling raw canon index) := by
  unfold finishSpelling
  split
  · exact Preserves.pure _ _
  · exact Preserves.bind (internMetaUniv_univs raw) (fun _ => Preserves.pure _ _)

/-- **The table suffix does not grow a final table** on success. -/
theorem internCanonical_no_growth (raw canon : Ixon.Univ) (context : CompileEnv × BlockEnv)
    {before after : BlockState} (finalized : before.univsFinal = true) {output : UInt64 × Option UInt64}
    (ran : rawRun (internCanonical raw canon) context before = (.ok output, after)) :
    after.univs = before.univs ∧ after.univsFinal = true := by
  rw [internCanonical, rawRun_bind, rawRun_get] at ran
  dsimp only at ran
  rw [rawRun_bind] at ran
  cases found : before.univsIndex.get? canon with
  | some index =>
    rw [internUniv_hit canon context before found] at ran
    simp only [rawRun_bind, rawRun_get, finalized, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte] at ran
    have frame := finishSpelling_univs raw canon index context before
    rw [ran] at frame
    exact ⟨(Prod.mk.inj frame).1, (Prod.mk.inj frame).2.trans finalized⟩
  | none =>
    rw [internUniv_miss canon context before found] at ran
    by_cases room : before.univs.size + 1 < UInt64.size
    · simp [room, rawRun_bind, rawRun_get, finalized, rawRun_throw] at ran
    · simp [room, checkedTableCount, rawRun_throw] at ran

/-- **Universe compilation does not grow a final table** on success. -/
theorem compile_no_growth (source : Ix.Level) (context : CompileEnv × BlockEnv)
    {before after : BlockState} (finalized : before.univsFinal = true) {output : UInt64 × Option UInt64}
    (ran : rawRun (compileAndInternUnivCanon source) context before = (.ok output, after)) :
    after.univs = before.univs ∧ after.univsFinal = true := by
  rw [compileAndInternUnivCanon_eq] at ran
  obtain ⟨raw, rawState, rawRan, rest⟩ := bind_ok ran
  unfold canonicalTail at rest
  obtain ⟨canon, canonState, canonRan, internRan⟩ := bind_ok rest
  have rawFrame := CanonUnivCache.compileUniv_frame source context before
  rw [rawRan] at rawFrame
  have rawUnivs : rawState.univs = before.univs := by
    have same := congrArg BlockState.univs rawFrame; exact same
  have rawFinal : rawState.univsFinal = before.univsFinal := by
    have same := congrArg BlockState.univsFinal rawFrame; exact same
  have canonFrame := canonUnivCached_frame raw context rawState
  rw [canonRan] at canonFrame
  have canonUnivs : canonState.univs = rawState.univs := by
    have same := congrArg BlockState.univs canonFrame; exact same
  have canonFinal : canonState.univsFinal = rawState.univsFinal := by
    have same := congrArg BlockState.univsFinal canonFrame; exact same
  have finished := internCanonical_no_growth raw canon context (canonFinal.trans (rawFinal.trans finalized))
    internRan
  exact ⟨finished.1.trans (canonUnivs.trans rawUnivs), finished.2⟩

end Ix.CompileCert.FinalUniverses
