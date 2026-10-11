import Ix.CompileCert.Canon.Coarsest

/-!
# M7 L1, the refinement does not depend on the presentation order

Design document §3.3 (c) and §3.5 (iii): "the ordered partition is invariant under permutation
of the input list". Under the name-hash seed (`Seed.byNameHash`, `Rules.compiler`) the
refinement starts from the members sorted by the hash of their names, an insertion sort whose
result is the unique hash-sorted permutation when the names are distinct
(`sortByName_eq_of_perm`); so `sortClasses` returns exactly the same classes, representatives
included, for every order of its input (`sortClasses_perm`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst)

/-- Name hashes strictly increasing. -/
def NameLt (a b : MutConst) : Prop := compare a.name b.name = .lt

/-- The member names are pairwise distinct under `==`. -/
def NamesDistinct (l : List MutConst) : Prop := (l.map MutConst.name).Pairwise (fun a b => (a == b) = false)

theorem names_sublist_keys : ∀ (l : List MutConst), (l.map MutConst.name).Sublist (l.flatMap keysOf)
  | [] => List.Sublist.slnil
  | m :: l => by
    simp only [List.map_cons, List.flatMap_cons, keysOf, List.cons_append]
    exact (names_sublist_keys l).trans (List.sublist_append_right _ _) |>.cons_cons _

theorem KeysDistinct.names {l : List MutConst} (h : KeysDistinct l) : NamesDistinct l :=
  List.Pairwise.sublist (names_sublist_keys l) h

theorem ne_eq_of_beq_false {a b : Name} (h : (a == b) = false) : compare a b ≠ .eq := by
  intro e
  have := nameCompare_eq_iff.1 e
  rw [h] at this; cases this

theorem nameLt_trans {a b c : MutConst} (h₁ : NameLt a b) (h₂ : NameLt b c) : NameLt a c :=
  Std.TransCmp.lt_trans (cmp := Ix.nameCompare) h₁ h₂

theorem nameLt_asymm {a b : MutConst} (h : NameLt a b) : ¬ NameLt b a := by
  intro h'
  unfold NameLt at h h'
  have := Std.OrientedCmp.eq_swap (cmp := Ix.nameCompare) (a := a.name) (b := b.name)
  change compare a.name b.name = (compare b.name a.name).swap at this
  rw [h, h'] at this; cases this

theorem insertByName_pairwise (x : MutConst) : ∀ (l : List MutConst), l.Pairwise NameLt →
    (∀ y ∈ l, compare x.name y.name ≠ .eq) → (insertByName x l).Pairwise NameLt
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hp, hd => by
    rw [List.pairwise_cons] at hp
    unfold insertByName
    split
    · rename_i hgt
      have hgt' : compare x.name y.name = .gt := by simpa using hgt
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, insertByName_pairwise x ys hp.2
        fun z hz => hd z (List.mem_cons_of_mem _ hz)⟩
      rcases List.mem_cons.1 ((insertByName_perm x ys).mem_iff.1 hz) with rfl | hz
      · show compare y.name z.name = .lt
        have := Std.OrientedCmp.eq_swap (cmp := Ix.nameCompare) (a := y.name) (b := z.name)
        change compare y.name z.name = (compare z.name y.name).swap at this
        rw [this, hgt']; rfl
      · exact hp.1 z hz
    · rename_i hgt
      have hlt : NameLt x y := by
        unfold NameLt
        have hne := hd y (by simp)
        cases h : compare x.name y.name
        · rfl
        · exact absurd h hne
        · exact absurd (by simp [h]) hgt
      refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 hp⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hlt
      · exact nameLt_trans hlt (hp.1 z hz)

theorem sortByName_pairwise : ∀ (l : List MutConst), NamesDistinct l → (sortByName l).Pairwise NameLt
  | [], _ => List.Pairwise.nil
  | x :: xs, hd => by
    unfold NamesDistinct at hd
    rw [List.map_cons, List.pairwise_cons] at hd
    unfold sortByName
    exact insertByName_pairwise x _ (sortByName_pairwise xs hd.2) fun y hy =>
      ne_eq_of_beq_false (hd.1 y.name (List.mem_map_of_mem ((sortByName_perm xs).mem_iff.1 hy)))

theorem eq_of_perm_nameLt : ∀ {l₁ l₂ : List MutConst}, l₁.Perm l₂ → l₁.Pairwise NameLt →
    l₂.Pairwise NameLt → l₁ = l₂
  | [], l₂, h, _, _ => (List.perm_nil.1 h.symm).symm
  | a :: t₁, [], h, _, _ => absurd h (by intro h'; have := h'.length_eq; simp at this)
  | a :: t₁, b :: t₂, h, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    by_cases hab : a = b
    · subst hab
      rw [eq_of_perm_nameLt h.cons_inv h₁.2 h₂.2]
    · exfalso
      have ha : a ∈ t₂ := by
        rcases List.mem_cons.1 (h.mem_iff.1 (List.mem_cons.2 (Or.inl rfl))) with e | e
        · exact absurd e hab
        · exact e
      have hb : b ∈ t₁ := by
        rcases List.mem_cons.1 (h.mem_iff.2 (List.mem_cons.2 (Or.inl rfl))) with e | e
        · exact absurd e.symm hab
        · exact e
      exact nameLt_asymm (h₁.1 b hb) (h₂.1 a ha)

/-- The name-hash sort returns the same list for every order of distinctly named members. -/
theorem sortByName_eq_of_perm {l₁ l₂ : List MutConst} (h : l₁.Perm l₂) (hd : NamesDistinct l₁) :
    sortByName l₁ = sortByName l₂ := by
  have hd₂ : NamesDistinct l₂ := by
    unfold NamesDistinct at *
    exact (List.Perm.map MutConst.name h).pairwise hd fun {a b} e => by
      cases hb : (b == a)
      · rfl
      · rw [name_beq_symm hb] at e; cases e
  exact eq_of_perm_nameLt (((sortByName_perm l₁).trans h).trans (sortByName_perm l₂).symm)
    (sortByName_pairwise l₁ hd) (sortByName_pairwise l₂ hd₂)

/-- **Seed independence for the compiler's rules** (§3.3 (c), §3.5 (iii)): under the name-hash
seed, `sortClasses` returns the same result, classes, their order and their representatives,
for every order of distinctly named members. -/
theorem sortClasses_perm {rules : Rules} (hseed : rules.seed = .byNameHash)
    (addr? : Name → Option Address) {xs ys : List MutConst} (h : xs.Perm ys) (hk : KeysDistinct xs) :
    sortClasses rules addr? xs = sortClasses rules addr? ys := by
  have he : xs.isEmpty = ys.isEmpty := by
    cases xs <;> cases ys <;> first | rfl | (have := h.length_eq; simp at this)
  unfold sortClasses
  simp only [hseed]
  rw [sortByName_eq_of_perm h hk.names, h.length_eq, he]

end Ix.CompileCert.Canon
