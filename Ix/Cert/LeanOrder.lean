import Ix.CompileM
import Ix.LeanIngress.Expr
import Ix.CompileCert.Canon.QSortSorted

/-! # Lean's order on a block's members

The compiler lays a block out in Lean's order (`Ix.CompileM.sourceMembers`): its members sorted
by `Ix.sourceOrderLt` on their keys (`orderKey`: a position and a name), ties broken by their
order in the input. Quotient Source orders a group of definitions by the same comparison. This
module proves:

* `Ix.Name.leanCmp` is a total order up to names that differ only in their hash fields:
  `leanCmp_swap`, `leanCmp_chains` (transitivity), and `ingressName_of_eq` (names it ties have
  one ingress name);
* so `Ix.sourceOrderLt` is a strict weak order: `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`,
  `lt_of_le_of_lt`, `le_trans`, and two keys neither of which is before the other tie
  (`tie_of_not_lt`);
* `sourceMembers` lists, in source order, the sorted permutation of its input (`sourceMembers_eq`):
  any permutation of the input that is sorted and has no two members that tie. -/

namespace Ix.Cert.LeanOrder

open Ix.CompileM

/-! ## Transitivity of a comparison -/

/-- The three facts a comparison's transitivity is made of, for the comparisons `u` of `a, b`,
`v` of `b, c` and `w` of `a, c`: two steps that are not `.gt` give one that is not, and it is
`.lt` when either step is. -/
abbrev Chains (u v w : Ordering) : Prop :=
  u.isLE = true → v.isLE = true → w.isLE = true ∧ (u = .lt ∨ v = .lt → w = .lt)

/-- A lawful comparison chains. -/
theorem chains_of_trans {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] (a b c : α) :
    Chains (cmp a b) (cmp b c) (cmp a c) := by
  intro h₁ h₂
  refine ⟨Std.TransCmp.isLE_trans h₁ h₂, ?_⟩
  rintro (h | h)
  · exact Std.TransCmp.lt_of_lt_of_isLE h h₂
  · exact Std.TransCmp.lt_of_isLE_of_lt h₁ h

theorem chains_lt {u v : Ordering} : Chains u v .lt := fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem chains_gt_left {v w : Ordering} : Chains .gt v w := fun h => by cases h

theorem chains_gt_mid {u w : Ordering} : Chains u .gt w := fun _ h => by cases h

/-- **A lexicographic comparison chains** when its two parts do. -/
theorem chains_then {X Y Z u v w : Ordering} (hp : Chains X Y Z) (hc : Chains u v w) :
    Chains (X.then u) (Y.then v) (Z.then w) := by
  cases X <;> cases Y <;> cases Z <;> simp only [Ordering.lt_then, Ordering.eq_then, Ordering.gt_then] <;>
    first
    | exact chains_lt
    | exact chains_gt_left
    | exact chains_gt_mid
    | exact hc
    | exact absurd ((hp rfl rfl).2 (.inl rfl)) (by decide)
    | exact absurd ((hp rfl rfl).2 (.inr rfl)) (by decide)
    | exact absurd (hp rfl rfl).1 (by decide)

/-! ## Lean's name order -/

/-- **`leanCmp` is oriented**: swapping the names swaps the result. -/
theorem leanCmp_swap (a : Ix.Name) : ∀ b, Ix.Name.leanCmp b a = (Ix.Name.leanCmp a b).swap := by
  induction a with
  | anonymous h => intro b; cases b <;> rfl
  | str p s h ih =>
    intro b
    cases b with
    | anonymous => rfl
    | num => rfl
    | str p' s' h' =>
      simp only [Ix.Name.leanCmp]
      rw [ih p', Ordering.swap_then, Std.OrientedCmp.eq_swap (cmp := compare) (a := s')]
  | num p i h ih =>
    intro b
    cases b with
    | anonymous => rfl
    | str => rfl
    | num p' i' h' =>
      simp only [Ix.Name.leanCmp]
      rw [ih p', Ordering.swap_then, Std.OrientedCmp.eq_swap (cmp := compare) (a := i')]

theorem leanCmp_self (a : Ix.Name) : Ix.Name.leanCmp a a = .eq :=
  Ordering.eq_eq_of_eq_swap (leanCmp_swap a a)

/-- **`leanCmp` is transitive.** -/
theorem leanCmp_chains (a : Ix.Name) :
    ∀ b c, Chains (Ix.Name.leanCmp a b) (Ix.Name.leanCmp b c) (Ix.Name.leanCmp a c) := by
  induction a with
  | anonymous h =>
    intro b c
    cases b <;> cases c <;>
      first | exact chains_lt | exact chains_gt_mid | exact (by decide : Chains .eq .eq .eq)
  | str p s h ih =>
    intro b c
    cases b with
    | anonymous => exact chains_gt_left
    | num => exact chains_gt_left
    | str p' s' h' =>
      cases c with
      | anonymous => exact chains_gt_mid
      | num => exact chains_gt_mid
      | str p'' s'' h'' => exact chains_then (ih p' p'') (chains_of_trans s s' s'')
  | num p i h ih =>
    intro b c
    cases b with
    | anonymous => exact chains_gt_left
    | str =>
      cases c with
      | anonymous => exact chains_gt_mid
      | num => exact chains_gt_mid
      | str => exact chains_lt
    | num p' i' h' =>
      cases c with
      | anonymous => exact chains_gt_mid
      | str => exact chains_lt
      | num p'' i'' h'' => exact chains_then (ih p' p'') (chains_of_trans i i' i'')

/-- **Names `leanCmp` ties have one ingress name**: they differ at most in their hash fields. -/
theorem ingressName_of_eq (a : Ix.Name) :
    ∀ b, Ix.Name.leanCmp a b = .eq → Ix.LeanIngress.ingressName a = Ix.LeanIngress.ingressName b := by
  induction a with
  | anonymous h =>
    intro b hb
    cases b with
    | anonymous => rfl
    | _ => cases hb
  | str p s h ih =>
    intro b hb
    cases b with
    | str p' s' h' =>
      simp only [Ix.Name.leanCmp, Ordering.then_eq_eq] at hb
      simp only [Ix.LeanIngress.ingressName]
      rw [ih p' hb.1, Std.LawfulEqCmp.eq_of_compare hb.2]
    | _ => cases hb
  | num p i h ih =>
    intro b hb
    cases b with
    | num p' i' h' =>
      simp only [Ix.Name.leanCmp, Ordering.then_eq_eq] at hb
      simp only [Ix.LeanIngress.ingressName]
      rw [ih p' hb.1, Std.LawfulEqCmp.eq_of_compare hb.2]
    | _ => cases hb

/-! ## Lean's order on keys -/

/-- Lean's order on a member's key, a position and a name, as an `Ordering`. -/
def keyCmp (a b : Nat × Ix.Name) : Ordering := (compare a.1 b.1).then (Ix.Name.leanCmp a.2 b.2)

theorem keyCmp_swap (a b : Nat × Ix.Name) : keyCmp b a = (keyCmp a b).swap := by
  unfold keyCmp
  rw [Ordering.swap_then, ← leanCmp_swap, ← Std.OrientedCmp.eq_swap]

theorem keyCmp_chains (a b c : Nat × Ix.Name) : Chains (keyCmp a b) (keyCmp b c) (keyCmp a c) :=
  chains_then (chains_of_trans a.1 b.1 c.1) (leanCmp_chains a.2 b.2 c.2)

theorem lt_iff {a b : Nat × Ix.Name} : Ix.sourceOrderLt a b = true ↔ keyCmp a b = .lt := by
  unfold Ix.sourceOrderLt keyCmp
  generalize Ix.Name.leanCmp a.2 b.2 = o
  generalize a.1 = i
  generalize b.1 = j
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · rw [Nat.compare_eq_lt.mpr h]
    simp [h]
  · rw [Nat.compare_eq_eq.mpr rfl]
    cases o <;> simp <;> decide
  · rw [Nat.compare_eq_gt.mpr h]
    simp [Nat.lt_asymm h, Nat.ne_of_gt h]

theorem not_lt_iff {a b : Nat × Ix.Name} : Ix.sourceOrderLt b a = false ↔ (keyCmp a b).isLE = true := by
  rw [← Bool.not_eq_true, lt_iff, keyCmp_swap]
  cases keyCmp a b <;> decide

theorem lt_irrefl (a : Nat × Ix.Name) : Ix.sourceOrderLt a a = false := by
  have h : keyCmp a a = .eq := Ordering.eq_eq_of_eq_swap (keyCmp_swap a a)
  rw [← Bool.not_eq_true, lt_iff, h]
  decide

theorem lt_trans {a b c : Nat × Ix.Name} (h₁ : Ix.sourceOrderLt a b = true) (h₂ : Ix.sourceOrderLt b c = true) :
    Ix.sourceOrderLt a c = true := by
  rw [lt_iff] at h₁ h₂ ⊢
  exact (keyCmp_chains a b c (by rw [h₁]; rfl) (by rw [h₂]; rfl)).2 (.inl h₁)

theorem lt_of_lt_of_le {a b c : Nat × Ix.Name} (h₁ : Ix.sourceOrderLt a b = true)
    (h₂ : Ix.sourceOrderLt c b = false) : Ix.sourceOrderLt a c = true := by
  rw [lt_iff] at h₁ ⊢
  rw [not_lt_iff] at h₂
  exact (keyCmp_chains a b c (by rw [h₁]; rfl) h₂).2 (.inl h₁)

theorem lt_of_le_of_lt {a b c : Nat × Ix.Name} (h₁ : Ix.sourceOrderLt b a = false)
    (h₂ : Ix.sourceOrderLt b c = true) : Ix.sourceOrderLt a c = true := by
  rw [lt_iff] at h₂ ⊢
  rw [not_lt_iff] at h₁
  exact (keyCmp_chains a b c h₁ (by rw [h₂]; rfl)).2 (.inr h₂)

theorem le_trans {a b c : Nat × Ix.Name} (h₁ : Ix.sourceOrderLt b a = false)
    (h₂ : Ix.sourceOrderLt c b = false) : Ix.sourceOrderLt c a = false := by
  rw [not_lt_iff] at h₁ h₂ ⊢
  exact (keyCmp_chains a b c h₁ h₂).1

/-- **Keys neither of which is before the other tie**: one position, and names that differ at
most in their hash fields. -/
theorem tie_of_not_lt {a b : Nat × Ix.Name} (h₁ : Ix.sourceOrderLt a b = false)
    (h₂ : Ix.sourceOrderLt b a = false) : a.1 = b.1 ∧ Ix.Name.leanCmp a.2 b.2 = .eq := by
  rw [not_lt_iff] at h₁ h₂
  rw [keyCmp_swap] at h₁
  have e : keyCmp a b = .eq := Ordering.eq_eq_of_isLE_of_isLE_swap h₂ h₁
  unfold keyCmp at e
  rw [Ordering.then_eq_eq] at e
  exact ⟨Nat.compare_eq_eq.mp e.1, e.2⟩

/-! ## `sourceMembers` sorts -/

/-- A block member's key in Lean's order (`sourceMembers`'): its position, and its name. -/
def orderKey : MutConst → Nat × Ix.Name
  | .indc i => (Ix.blockPosition i.all i.name, i.name)
  | .recr r => ((recursorFamilyPosition r).toNat, r.cnst.name)
  | .defn d => (Ix.blockPosition d.all d.name, d.name)

/-- The comparison `sourceMembers` sorts by: Lean's order on the members' keys, ties broken by
their positions in the input. -/
def zipBefore {α : Type} (key : α → Nat × Ix.Name) (a b : α × Nat) : Bool :=
  Ix.sourceOrderLt (key a.1) (key b.1) || (!Ix.sourceOrderLt (key b.1) (key a.1) && a.2 < b.2)

theorem zipBefore_irrefl {α : Type} (key : α → Nat × Ix.Name) (a : α × Nat) : zipBefore key a a = false := by
  simp [zipBefore, lt_irrefl]

theorem zipBefore_trans {α : Type} (key : α → Nat × Ix.Name) (a b c : α × Nat)
    (h₁ : zipBefore key a b = true) (h₂ : zipBefore key b c = true) : zipBefore key a c = true := by
  unfold zipBefore at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h₁ h₂ ⊢
  rcases h₁ with h₁ | ⟨h₁, i₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, i₂⟩
  · exact .inl (lt_trans h₁ h₂)
  · exact .inl (lt_of_lt_of_le h₁ h₂)
  · exact .inl (lt_of_le_of_lt h₁ h₂)
  · exact .inr ⟨le_trans h₁ h₂, Nat.lt_trans i₁ i₂⟩

theorem sourceMembers_def (cs : Array MutConst) :
    sourceMembers cs = (cs.zipIdx.qsort (zipBefore orderKey)).toList.map (·.1) := by
  rfl

/-- **`sourceMembers` is the sorted permutation of its input**: one entry per member, in the order
of any permutation of the input that Lean's order sorts and in which no two members tie. -/
theorem sourceMembers_eq {cs : Array MutConst} {xs : List MutConst} (perm : cs.toList.Perm xs)
    (sorted : xs.Pairwise fun a b => Ix.sourceOrderLt (orderKey b) (orderKey a) = false)
    (noTie : ∀ a ∈ xs, ∀ b ∈ xs, Ix.sourceOrderLt (orderKey a) (orderKey b) = false →
      Ix.sourceOrderLt (orderKey b) (orderKey a) = false → a = b) :
    sourceMembers cs = xs := by
  rw [sourceMembers_def]
  have hperm : ((cs.zipIdx.qsort (zipBefore orderKey)).toList.map (·.1)).Perm xs := by
    refine List.Perm.trans ?_ perm
    have p := ((Ix.CompileCert.Canon.qsort_perm cs.zipIdx (zipBefore orderKey)).toList).map (·.1)
    rw [Array.toList_zipIdx, List.zipIdx_map_fst] at p
    exact p
  refine List.Perm.eq_of_pairwise (le := fun a b => Ix.sourceOrderLt (orderKey b) (orderKey a) = false)
    (fun a b ha hb hab hba => noTie a (hperm.mem_iff.mp ha) b hb hba hab) ?_ sorted hperm
  have hs := Ix.CompileCert.Canon.qsort_pairwise cs.zipIdx (zipBefore orderKey) (zipBefore_irrefl orderKey)
    (zipBefore_trans orderKey)
  rw [List.pairwise_map]
  refine hs.imp fun {x y} h => ?_
  unfold zipBefore at h
  simp only [Bool.or_eq_false_iff] at h
  exact h.1

end Ix.Cert.LeanOrder

/-- info: 'Ix.Cert.LeanOrder.sourceMembers_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.LeanOrder.sourceMembers_eq

/-- info: 'Ix.Cert.LeanOrder.ingressName_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.LeanOrder.ingressName_of_eq
