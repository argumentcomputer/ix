import IxCC.Cfg.Rc.Proof.Physical.SavedFrames
import IxCC.Cfg.Rc.Proof.Physical.Bridge.Tokens

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs IxCC.Cfg.Rc.Proof.Physical.Bridge

/-- The existing token-oriented saved callers become a full saved register
relation only when whole-environment bounds and actual resume layouts are
supplied independently. Token roots alone do not imply either premise. -/
theorem saved_callers_words
    {addresses : AddressMap} {heapSize : Nat}
    {resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop}
    (saved : List (SavedCaller addresses))
    (bounded : ∀ s ∈ saved, Own.Plain.EnvBounded heapSize s.frame.env)
    (layout : ∀ s ∈ saved, resume s.frame s.destination s.target s.bound) :
    SavedFramesWords addresses heapSize resume (savedStack saved) (saved.map (·.target)) := by
  induction saved with
  | nil => exact .nil
  | cons s saved ih =>
    exact .cons (bounded s (by simp)) s.registers (layout s (by simp))
      (ih (fun t ht => bounded t (by simp [ht])) (fun t ht => layout t (by simp [ht])))

/-- Rebuild address-indexed saved-caller records after an allocation without
changing a physical frame, source continuation, owned-root occurrence or
resume witness. The entire physical stack is therefore the one in the actual
allocation trace; no new return-cursor claim is inferred from token data. -/
theorem allocation_saved_callers
    {H : Own.Heap} (body : Own.Body) {addresses : AddressMap}
    {resume : Cfg.Frame → Fir.Var → Lir.Frame → Nat → Prop}
    (saved : List (SavedCaller addresses))
    (bounded : ∀ s ∈ saved, Own.Plain.EnvBounded H.size s.frame.env)
    (layout : ∀ s ∈ saved, resume s.frame s.destination s.target s.bound)
    (address : Lir.Word) :
    ∃ next : List (SavedCaller (placeFresh addresses H.size address)),
      savedStack next = savedStack saved ∧ savedRoots next = savedRoots saved ∧
      next.map (·.target) = saved.map (·.target) ∧
      (∀ s ∈ next, Own.Plain.EnvBounded (H.alloc .rc body).2.size s.frame.env) ∧
      (∀ s ∈ next, resume s.frame s.destination s.target s.bound) := by
  have grows : H.size ≤ (H.alloc .rc body).2.size := by simp [Own.Heap.alloc, Own.Heap.size]
  induction saved with
  | nil => exact ⟨[], rfl, rfl, rfl, by simp, by simp⟩
  | cons s saved ih =>
    obtain ⟨tail, stackEq, rootsEq, targetsEq, tailBound, tailLayout⟩ :=
      ih (fun t ht => bounded t (by simp [ht])) (fun t ht => layout t (by simp [ht]))
    let first : SavedCaller (placeFresh addresses H.size address) := {
      frame := s.frame, destination := s.destination, live := s.live, roots := s.roots
      exactRoots := s.exactRoots, target := s.target, bound := s.bound
      registers := s.registers.placeFresh (bounded s (by simp)) address }
    refine ⟨first :: tail, ?_, ?_, ?_, ?_, ?_⟩
    · change (s.frame, s.destination) :: savedStack tail = (s.frame, s.destination) :: savedStack saved
      rw [stackEq]
    · change s.roots ++ savedRoots tail = s.roots ++ savedRoots saved
      rw [rootsEq]
    · change s.target :: tail.map (·.target) = s.target :: saved.map (·.target)
      rw [targetsEq]
    · intro t member
      rcases List.mem_cons.mp member with rfl | member
      · exact (bounded s (by simp)).mono grows
      · exact tailBound t member
    · intro t member
      rcases List.mem_cons.mp member with rfl | member
      · exact layout s (by simp)
      · exact tailLayout t member



end IxCC.Cfg.Rc.Native
