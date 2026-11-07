import IxCC.Rt.Rc.Proof.LiveMemory
import IxCC.Own.Rc.Proof.Shape
import IxCC.Own.Plain.Proof.Values

set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Readback
open IxCC.Own

def liveAt (H : Heap) (location : Nat) : Bool :=
  match H.cell? location with
  | some (.live _ _ _) => true
  | _ => false

def liveLocations (H : Heap) (bound : Nat) : List Nat :=
  (List.range bound).filter (liveAt H)

def liveBefore (H : Heap) (bound : Nat) : Nat := (liveLocations H bound).length

theorem liveAt_iff {H : Heap} {location : Nat} : liveAt H location = true ↔
    ∃ refs mode body, H.cell? location = some (.live refs mode body) := by
  cases hc : H.cell? location with
  | none => simp [liveAt, hc]
  | some cell => cases cell <;> simp [liveAt, hc]

theorem liveLocations_nodup (H : Heap) (bound : Nat) : (liveLocations H bound).Nodup :=
  (show (List.range bound).Nodup from List.nodup_range).filter _

theorem liveBefore_mono (H : Heap) {small big : Nat} (h : small ≤ big) :
    liveBefore H small ≤ liveBefore H big := by
  apply (liveLocations_nodup H small).length_le_of_subset
  intro location member
  simp only [liveLocations, List.mem_filter, List.mem_range] at member ⊢
  exact ⟨by omega, member.2⟩

theorem liveBefore_step {H : Heap} {location refs : Nat} {mode : OMode} {body : Body}
    (hc : H.cell? location = some (.live refs mode body)) :
    liveBefore H (location+1) = liveBefore H location+1 := by
  simp [liveBefore, liveLocations, List.range_succ, List.filter_append, liveAt, hc]

theorem liveBefore_strict {H : Heap} {child parent refs : Nat} {mode : OMode} {body : Body}
    (hc : H.cell? child = some (.live refs mode body)) (older : child < parent) :
    liveBefore H child < liveBefore H parent := by
  have hm := liveBefore_mono H (small := child+1) (big := parent) (by omega)
  rw [liveBefore_step hc] at hm
  omega

theorem toFirList_of_each {H : Heap} {fuel : Nat} {vs : List RVal} {ws : List Fir.Val}
    (den : Sem.Forall2 (Own.Proof.Den H) vs ws)
    (each : ∀ v ∈ vs, ∀ w, Own.Proof.Den H v w → Own.toFir H fuel v = some w) :
    Own.toFirList H fuel vs = some ws := by
  induction den with
  | nil => cases fuel <;> simp [Own.toFirList]
  | @cons v w vs ws hd rest ih =>
    simp only [Own.toFirList, each v (by simp) w hd,
      ih (fun v hv => each v (by simp [hv]))]

/-- Readback depth counts only currently live cells. Historical dead locations
do not consume the fuel bound, even after arbitrarily many recycled calls. -/
theorem toFir_liveFuel {H : Heap} (ordered : Own.Rc.HeapOk H) :
    ∀ fuel {v : RVal} {w : Fir.Val}, Own.Proof.Den H v w →
      (∀ location, v = .loc location → liveBefore H location < fuel) →
      Own.toFir H fuel v = some w := by
  intro fuel
  induction fuel with
  | zero =>
    intro v w den bound
    cases v with
    | loc location => have := bound location rfl; omega
    | lit _ | ctor0 _ | erased => simpa [Own.Proof.Den, Heap.value?, Own.toFir] using den
  | succ fuel ih =>
    intro v w den bound
    cases v with
    | lit _ | ctor0 _ | erased => simpa [Own.Proof.Den, Heap.value?, Own.toFir] using den
    | loc location =>
      obtain ⟨refs, mode, body, fields, cell, rfl, values⟩ := Own.Proof.den_loc den
      have shape := (ordered location refs mode body cell).2.2
      have denFields := Own.Plain.Values.dens_of_toFirList (by omega : H.size ≤ H.size+1) values
      have fields' : Own.toFirList H fuel body.fields = some fields := by
        apply toFirList_of_each denFields
        intro v member w den
        apply ih den
        intro child he
        subst v
        obtain ⟨cr, cm, cb, cw, childCell, _, _⟩ := Own.Proof.den_loc den
        have older := shape.2.2 child member
        have rank := liveBefore_strict childCell older
        have parentRank := bound location rfl
        omega
      simp [Own.toFir, cell, fields']

theorem toFir_totalLive {H : Heap} (ordered : Own.Rc.HeapOk H)
    {v : RVal} {w : Fir.Val} (den : Own.Proof.Den H v w) :
    Own.toFir H (liveBefore H H.size) v = some w := by
  apply toFir_liveFuel ordered _ den
  intro location he
  subst v
  obtain ⟨refs, mode, body, fields, cell, _, _⟩ := Own.Proof.den_loc den
  have range := Own.Proof.cell?_some cell
  exact liveBefore_strict cell range



end IxCC.Rt.Rc.Procs.Readback
