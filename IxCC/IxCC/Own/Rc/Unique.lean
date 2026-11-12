import IxCC.Own.Rc.Release

set_option autoImplicit false

namespace IxCC.Own.Rc

/-! ## The uniqueness test, abstractly

`uniqueOf H v` holds exactly for a location naming a live dynamic cell with one reference: the
answer the runtime's uniqueness test (`Rt.Rc.Gen.isUnique`) gives for `v`'s word
(`Rt.Rc.Gen.isUnique_spec`). With the caller's token among balanced tokens, that one reference is
the caller's (`uniqueOf_exclusive`). -/

/-- A live dynamic cell with one reference. Immediates, static cells and dead locations are never
unique. -/
def uniqueOf (H : Heap) : RVal → Bool
  | .loc l => match H.cell? l with
    | some (.live rc .dyn _) => rc == 1
    | _ => false
  | _ => false

theorem uniqueOf_loc {H : Heap} {l : Nat} :
    uniqueOf H (.loc l) = true ↔ ∃ b, H.cell? l = some (.live 1 .dyn b) := by
  simp only [uniqueOf]
  split
  · next rc b hc => simp [hc]
  · next hn => simp only [Bool.false_eq_true, false_iff, not_exists]; intro b hb; exact hn _ _ hb

/-- With the caller's token for `l` among the balanced tokens and `l` unique, nothing else refers
to `l`: no external owner, no other token, no field of a live cell. -/
theorem uniqueOf_exclusive {H : Heap} {external : Nat → Nat} {l : Nat} {rest : List RVal}
    (hb : Balance H external (.loc l :: rest)) (hu : uniqueOf H (.loc l) = true) :
    external l = 0 ∧ refsIn l rest = 0 ∧ edgeCount H l = 0 := by
  obtain ⟨b, hc⟩ := uniqueOf_loc.mp hu
  have hd : dynCount H l = 1 := by simp [dynCount, hc]
  have h := hb l
  rw [hd] at h
  simp [refsIn] at h
  refine ⟨by omega, by omega, by omega⟩

end IxCC.Own.Rc
