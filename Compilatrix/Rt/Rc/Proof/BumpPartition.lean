import Compilatrix.Rt.Rc.Proof.AllocatorReady

namespace Compilatrix.Rt.Rc.Procs
open Lir

def bumpSlot (bump : Word) (fields : Nat) : Slot :=
  { address := bump, cls := smallClass fields, kind := .reserved }

/-- A bump reservation adds one occupied physical extent. It neither creates
a logical heap cell nor claims that the reserved payload is initialized. -/
theorem ArenaPartition.reserve_bump
    {heap addresses base bump limit slots}
    (h : ArenaPartition heap addresses base bump limit slots)
    {fields : Nat} (hsmall : fields < 32) (halign : bump.toNat % 8 = 0)
    {next : Word} (hnext : next.toNat = bump.toNat+8*smallClass fields)
    (hlimit : next.toNat ≤ limit.toNat) :
    ArenaPartition heap addresses base next limit (bumpSlot bump fields :: slots) := by
  have hb := h.bounds
  have hc : 1 ≤ smallClass fields ∧ smallClass fields ≤ 32 := by
    simp only [smallClass]; omega
  refine {
    bounds := by omega
    valid := ?_
    disjoint := ?_
    accounted := ?_
    live := ?_
    placed := ?_
    pending := ?_ }
  · intro slot hm
    rcases List.mem_cons.mp hm with he | hm
    · subst slot
      exact ⟨hc.1, hc.2, halign, hb.1, by simpa [bumpSlot] using Nat.le_of_eq hnext.symm⟩
    · obtain ⟨hl, hu, ha, hlo, hhi⟩ := h.valid slot hm
      exact ⟨hl, hu, ha, hlo, by omega⟩
  · intro i j si sj hi hj hne
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst si
        have hj' : slots[j]? = some sj := by simpa using hj
        have hv := h.valid sj (List.mem_of_getElem? hj')
        exact Or.inr hv.2.2.2.2
    | succ i =>
      have hi' : slots[i]? = some si := by simpa using hi
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst sj
        have hv := h.valid si (List.mem_of_getElem? hi')
        exact Or.inl hv.2.2.2.2
      | succ j =>
        exact h.disjoint i j si sj hi' (by simpa using hj) (by omega)
  · intro n hlo hhi
    by_cases hn : n < bump.toNat
    · obtain ⟨slot, hm, hl, hu⟩ := h.accounted n hlo hn
      exact ⟨slot, by simp [hm], hl, hu⟩
    · exact ⟨bumpSlot bump fields, by simp, by simp [bumpSlot]; omega,
        by simp [bumpSlot]; omega⟩
  · intro slot hm loc hk
    rcases List.mem_cons.mp hm with he | hm
    · subst slot; cases hk
    · exact h.live slot hm loc hk
  · intro loc refs body hl
    obtain ⟨slot, hm, hk⟩ := h.placed loc refs body hl
    exact ⟨slot, by simp [hm], hk⟩
  · intro slot hm loc suffix pred hk
    rcases List.mem_cons.mp hm with he | hm
    · subst slot; cases hk
    · exact h.pending slot hm loc suffix pred hk


end Compilatrix.Rt.Rc.Procs
