import IxCC.Anf.Proof.Pass.Basic
import IxCC.Anf.Prune

/-! # Pruning: the reachable globals

`Prune.reach` is a fuelled worklist. With the fuel `Prune.run` gives it
(the size, the total number of references, the roots and one), it empties
its worklist: each step lowers the worklist's length plus the references of
the globals not yet seen. Its result then contains the roots and is closed
under the references of the globals it contains. -/

set_option autoImplicit false

namespace IxCC.Anf.Prune.Proof

/-- The references `reach` follows from a global. -/
def refsOf (P : Program) (g : GlobalId) : List GlobalId :=
  match P.global? g with
  | some gd => gd.body.refs
  | none => []

/-- The references of the globals not yet seen. -/
def unseen (P : Program) (seen : Src.NatMap Unit) : Nat :=
  ((List.range P.size).map fun x => if seen.contains x then 0 else (refsOf P x).length).sum

theorem contains_insert (seen : Src.NatMap Unit) (g x : Nat) :
    (seen.insert g ()).contains x = (decide (x = g) || seen.contains x) := by
  unfold Src.NatMap.contains
  rw [Src.NatMap.get?_insert]
  by_cases h : x = g <;> simp [h]

theorem sum_insert (w : Nat → Nat) (seen : Src.NatMap Unit) (g : Nat) (hg : seen.contains g = false) :
    ∀ (l : List Nat), l.Nodup →
      (l.map fun x => if (seen.insert g ()).contains x then 0 else w x).sum + (if g ∈ l then w g else 0) =
        (l.map fun x => if seen.contains x then 0 else w x).sum
  | [], _ => by simp
  | x :: l, hn => by
    rw [List.nodup_cons] at hn
    have ih := sum_insert w seen g hg l hn.2
    simp only [List.map_cons, List.sum_cons, List.mem_cons, contains_insert]
    simp only [contains_insert] at ih
    by_cases hx : x = g
    · subst hx
      rw [if_neg hn.1] at ih
      simp only [decide_true, Bool.true_or, if_true, true_or, hg, Bool.false_eq_true, if_false]
      omega
    · have hx' : decide (x = g) = false := by simpa using hx
      simp only [hx', Bool.false_or]
      by_cases hgl : g ∈ l
      · rw [if_pos hgl] at ih
        rw [if_pos (Or.inr hgl)]
        omega
      · rw [if_neg hgl] at ih
        rw [if_neg (fun (h : g = x ∨ g ∈ l) => h.elim (fun e => hx e.symm) hgl)]
        omega

theorem unseen_insert {P : Program} (hb : P.GlobalsBelow) {g : GlobalId} {seen : Src.NatMap Unit}
    (hg : seen.contains g = false) : unseen P (seen.insert g ()) + (refsOf P g).length = unseen P seen := by
  unfold unseen
  have hs := sum_insert (fun x => (refsOf P x).length) seen g hg (List.range P.size) List.nodup_range
  by_cases hlt : g < P.size
  · rw [if_pos (List.mem_range.2 hlt)] at hs; exact hs
  · rw [if_neg (by simpa using hlt)] at hs
    have : refsOf P g = [] := by
      unfold refsOf
      cases h : P.global? g with
      | none => rfl
      | some gd => exact absurd (hb g gd h) hlt
    rw [this]; simpa using hs

theorem reach_seen {P : Program} {fuel : Nat} {g : GlobalId} {todo : List GlobalId} {seen : Src.NatMap Unit}
    (hg : seen.contains g = true) : reach P (fuel + 1) (g :: todo) seen = reach P fuel todo seen := by
  simp only [reach, hg, if_true]

theorem reach_unseen {P : Program} {fuel : Nat} {g : GlobalId} {todo : List GlobalId} {seen : Src.NatMap Unit}
    (hg : seen.contains g = false) :
    reach P (fuel + 1) (g :: todo) seen = reach P fuel (refsOf P g ++ todo) (seen.insert g ()) := by
  simp only [reach, hg, Bool.false_eq_true, if_false]
  cases hgg : P.global? g <;> simp [refsOf, hgg]

/-- **`reach` is complete** with enough fuel: the result contains what was
seen or pending, and is closed under references. -/
theorem reach_spec {P : Program} (hb : P.GlobalsBelow) : ∀ (fuel : Nat) (todo : List GlobalId)
    (seen : Src.NatMap Unit), todo.length + unseen P seen < fuel →
    (∀ g, seen.contains g = true → ∀ h ∈ refsOf P g, seen.contains h = true ∨ h ∈ todo) →
    (∀ g, (reach P fuel todo seen).contains g = true → ∀ h ∈ refsOf P g,
        (reach P fuel todo seen).contains h = true) ∧
      ∀ g, (seen.contains g = true ∨ g ∈ todo) → (reach P fuel todo seen).contains g = true
  | 0, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | fuel + 1, [], seen, _, hinv => by
    simp only [reach]
    refine ⟨fun g hg h hh => ?_, fun g hg => ?_⟩
    · rcases hinv g hg h hh with h1 | h1
      · exact h1
      · cases h1
    · rcases hg with h1 | h1
      · exact h1
      · cases h1
  | fuel + 1, g :: todo, seen, hp, hinv => by
    cases hg : seen.contains g with
    | true =>
      rw [reach_seen hg]
      have hp' : todo.length + unseen P seen < fuel := by simp at hp; omega
      obtain ⟨h1, h2⟩ := reach_spec hb fuel todo seen hp' fun g' hg' h hh => by
        rcases hinv g' hg' h hh with h3 | h3
        · exact .inl h3
        · rcases List.mem_cons.1 h3 with rfl | h3
          · exact .inl hg
          · exact .inr h3
      refine ⟨h1, fun x hx => h2 x ?_⟩
      rcases hx with hx | hx
      · exact .inl hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact .inl hg
        · exact .inr hx
    | false =>
      rw [reach_unseen hg]
      have hp' : (refsOf P g ++ todo).length + unseen P (seen.insert g ()) < fuel := by
        have := unseen_insert hb hg
        simp only [List.length_append, List.length_cons] at hp ⊢; omega
      obtain ⟨h1, h2⟩ := reach_spec hb fuel (refsOf P g ++ todo) (seen.insert g ()) hp' fun g' hg'' h hh => by
        rw [contains_insert] at hg'' ⊢
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hg''
        rcases hg'' with rfl | hg''
        · exact .inr (List.mem_append_left _ hh)
        · rcases hinv g' hg'' h hh with h3 | h3
          · exact .inl (by simp [h3])
          · rcases List.mem_cons.1 h3 with rfl | h3
            · exact .inl (by simp)
            · exact .inr (List.mem_append_right _ h3)
      refine ⟨h1, fun x hx => h2 x ?_⟩
      rw [contains_insert]
      rcases hx with hx | hx
      · exact .inl (by simp [hx])
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact .inl (by simp)
        · exact .inr (List.mem_append_right _ hx)

theorem sum_filterMap {β : Type} (F : Nat → Option β) (w : β → Nat) : ∀ l : List Nat,
    ((l.filterMap F).map w).sum = (l.map fun x => ((F x).map w).getD 0).sum
  | [] => rfl
  | x :: l => by
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases F x with
    | none => simp [sum_filterMap F w l]
    | some y => simp [sum_filterMap F w l]

theorem foldl_add {β : Type} (w : β → Nat) : ∀ (l : List β) (a : Nat),
    l.foldl (fun n p => n + w p) a = a + (l.map w).sum
  | [], a => by simp
  | p :: l, a => by simp only [List.foldl_cons, foldl_add w l, List.map_cons, List.sum_cons]; omega

theorem unseen_leaf (P : Program) :
    unseen P .leaf = P.globalList.foldl (fun n (p : GlobalId × GDef) => n + p.2.body.refs.length) 0 := by
  rw [foldl_add (fun (p : GlobalId × GDef) => p.2.body.refs.length) P.globalList 0, Nat.zero_add]
  unfold unseen Program.globalList
  rw [sum_filterMap]
  congr 1
  apply List.map_congr_left
  intro x _
  have hc : (Src.NatMap.leaf : Src.NatMap Unit).contains x = false := rfl
  rw [hc]
  unfold refsOf
  cases P.global? x <;> rfl

/-- The seen set `run` computes contains the roots and is closed under
references. -/
theorem run_seen {P : Program} (hb : P.GlobalsBelow) :
    let total := P.globalList.foldl (fun n (p : GlobalId × GDef) => n + p.2.body.refs.length) 0
    let seen := reach P (P.size + total + P.roots.length + 1) P.roots .leaf
    (∀ g, seen.contains g = true → ∀ h ∈ refsOf P g, seen.contains h = true) ∧
      ∀ r ∈ P.roots, seen.contains r = true := by
  intro total seen
  have hp : P.roots.length + unseen P .leaf < P.size + total + P.roots.length + 1 := by
    rw [unseen_leaf]; omega
  obtain ⟨h1, h2⟩ := reach_spec hb _ P.roots .leaf hp fun g hg => by
    have : (Src.NatMap.leaf : Src.NatMap Unit).contains g = false := rfl
    rw [this] at hg; cases hg
  exact ⟨h1, fun r hr => h2 r (.inr hr)⟩

end IxCC.Anf.Prune.Proof
