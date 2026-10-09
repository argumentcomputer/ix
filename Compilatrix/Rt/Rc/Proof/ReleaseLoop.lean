import Compilatrix.Rt.Rc.Proof.PointProgress
import Compilatrix.Rt.Rc.Proof.DecShared

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

/-- Every valid concrete cutpoint reaches an empty continuation stack in
finitely many actual target charges. The result heap is exactly source
`dropAll`; the induction uses the proved concrete case transitions. -/
theorem ReleasePoint.reaches_empty (p : ReleasePoint) {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) :
    ∃ final : ReleasePoint, ∃ charges,
      final.Valid addresses external context base bump limit ∧
      final.current = none ∧ final.frames = [] ∧
      dropAll p.heap (p.current.toList ++ cursorTokens p.frames) = some final.heap ∧
      Sem.Star (semStep releaseProgram) (p.state context) charges (final.state context) := by
  rcases ReleasePoint.progress hp with ⟨hc, hf⟩ | ⟨next, hn⟩
  · exact ⟨p, 0, hp, hc, hf, by simp [hc, hf, cursorTokens, flattenPending, dropAll], .refl _⟩
  · obtain ⟨final, laterCharges, hf, hc, hframes, hheap, hlater⟩ := ReleasePoint.reaches_empty next hn.1
    obtain ⟨charges, hsteps⟩ := hn.2.2.1
    exact ⟨final, charges+laterCharges, hf, hc, hframes, hn.dropAll_eq.trans hheap, hsteps.trans hlater⟩
termination_by p.rank
decreasing_by exact hn.2.1

/-- Complete ordinary-Lir release from either loop cutpoint. This theorem
quantifies the required finite clock instead of reusing the old immortal
constant-clock rule. Initial-call and ambient-frame transport remain separate. -/
theorem ReleasePoint.release_complete (p : ReleasePoint) {addresses external context base bump limit}
    (hp : p.Valid addresses external context base bump limit) :
    ∃ heap' mem' slots' lists' clock,
      dropAll p.heap (p.current.toList ++ cursorTokens p.frames) = some heap' ∧
      ReleaseInvariant heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      Sem.Reaches (semStep releaseProgram) (p.state context) clock (.ok ([], mem')) := by
  obtain ⟨final, charges, hv, hc, hf, hheap, hpath⟩ := p.reaches_empty hp
  have hzero : final.env[8]? = some 0 := by simpa only [hc, hf, cursorHead] using hv.2
  have hdone : Sem.Reaches (semStep releaseProgram) (final.state context) 0 (.ok ([], final.mem)) := by
    simpa [ReleasePoint.state, hc, releaseProgram, releaseState,
      decProgram, decState] using dec_done final.mem context final.env 0 hzero
  refine ⟨final.heap, final.mem, final.slots, final.lists, charges, hheap, ?_, ?_⟩
  · simpa only [hc, hf] using hv.1
  · simpa using Sem.Reaches.star hpath hdone



end Compilatrix.Rt.Rc.Procs
