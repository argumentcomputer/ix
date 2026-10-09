import Compilatrix.Rt.Rc.Proof.FramePointProgress
import Compilatrix.Rt.Rc.Proof.ReleaseLoop

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

/-- The real complete release loop additionally preserves all protected
bytes. This companion retains the previously validated unframed interface. -/
theorem ReleasePoint.reaches_empty_frame (p : ReleasePoint) {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) :
    ∃ final : ReleasePoint, ∃ charges,
      final.Valid addresses external context base bump limit ∧
      final.current = none ∧ final.frames = [] ∧
      dropAll p.heap (p.current.toList ++ cursorTokens p.frames) = some final.heap ∧
      Sem.Star (semStep releaseProgram) (p.state context) charges (final.state context) ∧
      ProtectedFrame p.mem final.mem context base bump := by
  rcases ReleasePoint.progress_frame hp with ⟨hc, hf⟩ | ⟨next, hn, hframe⟩
  · exact ⟨p, 0, hp, hc, hf, by simp [hc, hf, cursorTokens, flattenPending, dropAll],
      .refl _, .refl _ _ _ _⟩
  · obtain ⟨final, laterCharges, hf, hc, hframes, hheap, hlater, hframe'⟩ :=
      ReleasePoint.reaches_empty_frame next hn.1
    obtain ⟨charges, hsteps⟩ := hn.2.2.1
    exact ⟨final, charges+laterCharges, hf, hc, hframes, hn.dropAll_eq.trans hheap,
      hsteps.trans hlater, hframe.trans hframe'⟩
termination_by p.rank
decreasing_by exact hn.2.1

theorem ReleasePoint.release_complete_frame (p : ReleasePoint) {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) :
    ∃ heap' mem' slots' lists' clock,
      dropAll p.heap (p.current.toList ++ cursorTokens p.frames) = some heap' ∧
      ReleaseInvariant heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Reaches (semStep releaseProgram) (p.state context) clock (.ok ([], mem')) ∧
      ProtectedFrame p.mem mem' context base bump := by
  obtain ⟨final, charges, hv, hc, hf, hheap, hpath, hframe⟩ := p.reaches_empty_frame hp
  have hzero : final.env[8]? = some 0 := by simpa only [hc, hf, cursorHead] using hv.2
  have hdone : Sem.Reaches (semStep releaseProgram) (final.state context) 0 (.ok ([], final.mem)) := by
    simpa [ReleasePoint.state, hc, releaseProgram, releaseState, decProgram, decState]
      using dec_done final.mem context final.env 0 hzero
  refine ⟨final.heap, final.mem, final.slots, final.lists, charges, hheap, ?_, ?_, hframe⟩
  · simpa only [hc, hf] using hv.1
  · simpa using Sem.Reaches.star hpath hdone



end Compilatrix.Rt.Rc.Procs
