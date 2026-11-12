import IxCC.Rt.Rc.Gen.Proof.FrameReleaseLoop

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Transfer one externally owned token into the release worklist. -/
theorem ReleaseInvariant.begin_release
    {heap addresses mem external value context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists) :
    ReleaseInvariant cmax heap addresses mem external (some value) []
      context base bump limit slots lists := by
  refine { h with balance := ?_ }
  intro location
  have hb := h.balance location
  simpa [cursorTokens, flattenPending, refsIn, Nat.add_assoc] using hb

/-- The genuine one-argument procedure entry reaches the complete release
result. The input token is transferred from idle external ownership. -/
theorem release_entry_complete_frame
    {heap addresses mem external value context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem
      (fun location => external location + refsIn location [value]) none []
      context base bump limit slots lists)
    (word : Word) (hw : valueWord addresses value = some word) :
    ∃ heap' mem' slots' lists' clock,
      dropAll heap [value] = some heap' ∧
      ReleaseInvariant cmax heap' addresses mem' external none [] context base bump limit slots' lists' ∧
      eval releaseProgram clock [word] mem context = .ok ([], mem') ∧
      ProtectedFrame mem mem' context base bump := by
  let p : ReleasePoint := {
    heap, mem, current := some value, frames := [], slots, lists
    env := decDispatchEnv word }
  have hp : p.Valid cmax addresses external context base bump limit := by
    refine ⟨h.begin_release, word, hw, ?_, ?_⟩
    · simp only [p, decDispatchEnv, Std.HashMap.getElem?_insert]; rfl
    · simp only [p, decDispatchEnv, cursorHead, Std.HashMap.getElem?_insert]; rfl
  obtain ⟨heap', mem', slots', lists', clock, hs, hi, hr, hframe⟩ := p.release_complete_frame hp
  have hinit : State.initial releaseProgram [word] mem context =
      some (releaseState mem context (decEnv word) 0 0) := by
    simpa only [releaseProgram, releaseState, decProgram, decState] using dec_initial mem context word
  have hentry : Sem.Star (semStep releaseProgram)
      (releaseState mem context (decEnv word) 0 0) 0 (p.state context) := by
    apply Sem.Star.free
    · apply semStep_next.mpr
      simpa [p, ReleasePoint.state, releaseProgram, releaseState, decProgram, decState] using dec_entry mem context word
    · exact .refl _
  refine ⟨heap', mem', slots', lists', clock, ?_, hi, ?_, hframe⟩
  · simpa [p, cursorTokens, flattenPending] using hs
  · exact (runs_eval hinit).eq (by simpa using Sem.Reaches.star hentry hr)


end IxCC.Rt.Rc.Gen
