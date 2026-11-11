import IxCC.Anf.Defun
import IxCC.Src.Proof.NatMap

/-! # P8's key check is sound

`Defun.firstEqualKeys` buckets keys by `GKey.bucket` and compares them within
a bucket. When it finds no equal pair, the keys are pairwise distinct
(`firstEqualKeys_none`): every key seen so far sits in its bucket's list, so a
later equal key would have been found there. `checkSources` runs it on the
keys of the globals whose closures the program builds, and they are then
pairwise distinct (`checkSources_ownerKeys`): a dispatcher's alternatives for
one such global are never shadowed by another's (`docs/closures-design.md`,
"Proof obligation"). -/

set_option autoImplicit false

namespace IxCC.Anf.Defun.Proof

/-- Every pair seen so far is in its key's bucket. -/
def Seen (m : Src.NatMap (List (Key.GKey × GlobalId))) (seen : List (Key.GKey × GlobalId)) : Prop :=
  ∀ p ∈ seen, p ∈ m.getD p.1.bucket []

theorem firstEqualKeys_none_go : ∀ (ks : List (Key.GKey × GlobalId)) (m : Src.NatMap (List (Key.GKey × GlobalId)))
    (seen : List (Key.GKey × GlobalId)), Seen m seen → firstEqualKeys ks m = none →
    (ks.map (·.1)).Nodup ∧ ∀ p ∈ ks, ∀ q ∈ seen, p.1 ≠ q.1
  | [], _, _, _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | (k, g) :: ks, m, seen, hs, h => by
    simp only [firstEqualKeys] at h
    split at h
    · cases h
    · rename_i hf
      have hnot : ∀ q ∈ seen, k ≠ q.1 := by
        intro ⟨q1, q2⟩ hq hkq
        have hq' := hs (q1, q2) hq
        have hb : (q1, q2) ∈ m.getD k.bucket [] := by rw [hkq]; exact hq'
        have := List.find?_eq_none.1 hf (q1, q2) hb
        simp [hkq] at this
      have hs' : Seen (m.insert k.bucket ((k, g) :: m.getD k.bucket [])) ((k, g) :: seen) := by
        intro p hp
        show p ∈ ((m.insert k.bucket ((k, g) :: m.getD k.bucket [])).get? p.1.bucket).getD []
        rcases List.mem_cons.1 hp with rfl | hp
        · rw [Src.NatMap.get?_insert_self]
          exact List.mem_cons_self
        · by_cases hb : p.1.bucket = k.bucket
          · have h1 := hs p hp
            rw [hb] at h1
            rw [Src.NatMap.get?_insert, ite_eq_left hb]
            exact List.mem_cons_of_mem _ h1
          · rw [Src.NatMap.get?_insert, ite_eq_right hb]
            exact hs p hp
      obtain ⟨hnd, hall⟩ := firstEqualKeys_none_go ks _ _ hs' h
      refine ⟨List.nodup_cons.2 ⟨?_, hnd⟩, ?_⟩
      · intro hk
        obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk
        exact hall p hp (k, g) List.mem_cons_self hpk
      · intro p hp q hq
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hnot q hq
        · exact hall p hp q (List.mem_cons_of_mem _ hq)

/-- **The key check is sound**: no equal pair found, the keys are pairwise
distinct. -/
theorem firstEqualKeys_none {ks : List (Key.GKey × GlobalId)} (h : firstEqualKeys ks .leaf = none) :
    (ks.map (·.1)).Nodup :=
  (firstEqualKeys_none_go ks .leaf [] (fun _ h => absurd h List.not_mem_nil) h).1

/-- The globals whose closures the program builds, with their keys, as
`checkSources` lists them. -/
def ownerKeys (P : Program) (acc : Acc) (parents : List GlobalId) : List (Key.GKey × GlobalId) :=
  let owners := Src.NatSet.ofList ((escapeSources P acc).map (·.id) ++ parents)
  (List.range P.size).filterMap fun h =>
    if owners.contains h then (P.global? h).map fun hd => (hd.key, h) else none

/-- **Passing `checkSources`, the owners' keys are pairwise distinct.** -/
theorem checkSources_ownerKeys {P : Program} {acc : Acc} {parents : List GlobalId} {u : Unit}
    (h : checkSources P acc parents = .ok u) : ((ownerKeys P acc parents).map (·.1)).Nodup := by
  unfold checkSources at h
  cases hf : firstEqualKeys (ownerKeys P acc parents) .leaf with
  | none => exact firstEqualKeys_none hf
  | some r =>
    obtain ⟨g', h'⟩ := r
    simp only [ownerKeys] at hf
    simp only [hf] at h
    cases h

end IxCC.Anf.Defun.Proof
