import IxCC.Rt.Rc.Gen.Proof.AllocatorReady

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

def bumpSlot (bump : Word) (cls : Nat) : Slot :=
  { address := bump, cls := cls, kind := .reserved }

/-- A bump reservation adds one occupied physical extent. It neither creates
a logical heap cell nor claims that the reserved payload is initialized. -/
theorem ArenaPartition.reserve_bump
    {heap addresses base bump limit slots}
    (h : ArenaPartition cmax heap addresses base bump limit slots)
    {cls : Nat} (hcls : 1 ≤ cls) (hmax : cls ≤ maxClass) (hcm : cls ≤ cmax)
    (halign : bump.toNat % 8 = 0)
    {next : Word} (hnext : next.toNat = bump.toNat+8*classWords cls)
    (hlimit : next.toNat ≤ limit.toNat) :
    ArenaPartition cmax heap addresses base next limit (bumpSlot bump cls :: slots) := by
  have hb := h.bounds
  have hw := classWords_pos hcls
  have hwm := classWords_le_max hmax
  rw [maxCellWords_eq] at hwm
  refine {
    bounds := by omega
    valid := ?_
    bounded := ?_
    disjoint := ?_
    accounted := ?_
    live := ?_
    placed := ?_
    pending := ?_ }
  · intro slot hm
    rcases List.mem_cons.mp hm with he | hm
    · subst slot
      exact ⟨hcls, hmax, halign, hb.1, by simp only [bumpSlot]; omega, hw, by simp only [bumpSlot]; omega⟩
    · obtain ⟨hl, hu, ha, hlo, hhi, hw1, hw2⟩ := h.valid slot hm
      exact ⟨hl, hu, ha, hlo, by omega, hw1, hw2⟩
  · intro slot hm
    rcases List.mem_cons.mp hm with he | hm
    · subst slot; exact hcm
    · exact h.bounded slot hm
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
        exact Or.inr (by simp only [bumpSlot]; omega)
    | succ i =>
      have hi' : slots[i]? = some si := by simpa using hi
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst sj
        have hv := h.valid si (List.mem_of_getElem? hi')
        exact Or.inl (by simp only [bumpSlot]; omega)
      | succ j =>
        exact h.disjoint i j si sj hi' (by simpa using hj) (by omega)
  · intro n hlo hhi
    by_cases hn : n < bump.toNat
    · obtain ⟨slot, hm, hl, hu⟩ := h.accounted n hlo hn
      exact ⟨slot, by simp [hm], hl, hu⟩
    · exact ⟨bumpSlot bump cls, by simp, by simp [bumpSlot]; omega,
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


end IxCC.Rt.Rc.Gen
