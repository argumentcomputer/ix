import Ix.Sharing.Verify.UniformLength

/-!
# Writings: the model as a minimum over encodings

A `WTree` writes a term of the canonical DAG: as a Share, as an inline
non-telescope node over writings of its children, or as an inline
telescope of `j` spine nodes over writings of their side children, ending
in a Share of the next spine node or in a writing of the natural tail. Its
length `cost` prices Shares at `w` and telescopes by the merged-header rule.

`uCost` and `uInl` are the minimum lengths of a writing and of an inline
writing of a term with the stored terms `S` (`valid_cost`), and both minima
are attained (`exists_opt`).
-/

namespace Ix.Sharing.Verify.UniformModel

open Ix.Sharing.Exact

/-- A writing of a term. -/
inductive WTree where
  | share (x : Nat)
  | node (x : Nat) (kids : List WTree)
  | tele (x j : Nat) (sides : List WTree) (tail : WTree)
  deriving Inhabited

mutual
/-- Length of a writing (Shares at `w`). -/
def WTree.cost (p : Prep) (w : Nat) : WTree → Nat
  | .share _ => w
  | .node x kids => (p.dag.node x).head.ownBytes + WTree.costs p w kids
  | .tele x j sides tail =>
    tag4Size j + j * (p.dag.node x).sideExtra + WTree.costs p w sides + WTree.cost p w tail
/-- Total length of a list of writings. -/
def WTree.costs (p : Prep) (w : Nat) : List WTree → Nat
  | [] => 0
  | k :: ks => WTree.cost p w k + WTree.costs p w ks
end

theorem WTree.costs_eq (p : Prep) (w : Nat) (l : List WTree) :
    WTree.costs p w l = (l.map (WTree.cost p w)).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.costs, ih]

/-- Whether a writing is a Share. -/
def WTree.isShare : WTree → Bool
  | .share _ => true
  | _ => false

/-- The side child of the `k`-th spine node of `x`. -/
def sideAt (p : Prep) (x k : Nat) : Nat := (p.dag.node (spineAt p x k)).sideChild

/-- `T` is a writing of term `x` using the stored terms `S`. -/
inductive Valid (p : Prep) (S : Nat → Bool) : Nat → WTree → Prop
  | share {x : Nat} : S x = true → Valid p S x (.share x)
  | node {x : Nat} {kids : List WTree} : p.family[x]! = .none →
      kids.length = (p.dag.node x).head.arity →
      (∀ (i : Nat) (h : i < kids.length), Valid p S ((p.dag.node x).child i) kids[i]) →
      Valid p S x (.node x kids)
  | teleCut {x j : Nat} {sides : List WTree} : p.family[x]! ≠ .none →
      1 ≤ j → j < p.spineLen[x]! → sides.length = j →
      (∀ (k : Nat) (h : k < sides.length), Valid p S (sideAt p x k) sides[k]) →
      S (spineAt p x j) = true →
      Valid p S x (.tele x j sides (.share (spineAt p x j)))
  | teleFull {x : Nat} {sides : List WTree} {tail : WTree} : p.family[x]! ≠ .none →
      sides.length = p.spineLen[x]! →
      (∀ (k : Nat) (h : k < sides.length), Valid p S (sideAt p x k) sides[k]) →
      Valid p S p.tail[x]! tail →
      Valid p S x (.tele x p.spineLen[x]! sides tail)

/-! ## Spine bookkeeping -/

theorem sideExtra_of_family {a b : Node} (h : a.head.family = b.head.family) :
    a.sideExtra = b.sideExtra := by
  unfold Node.sideExtra
  cases ha : a.head <;> cases hb : b.head <;> simp_all [Head.family]

theorem PrepWF.sideExtra_spine {p : Prep} (hp : PrepWF p) {x k : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hk : k < p.spineLen[x]!) :
    (p.dag.node (spineAt p x k)).sideExtra = (p.dag.node x).sideExtra := by
  obtain ⟨_, hsp, _, _, _⟩ := hp.spine x hx hf
  obtain ⟨hle, hfam, _, _⟩ := hsp k hk
  apply sideExtra_of_family
  rw [← hp.family _ (by omega), ← hp.family _ hx, hfam]

theorem sum_map_const_add {α : Type} (c : Nat) (f : α → Nat) :
    ∀ (l : List α), (l.map fun a => c + f a).sum = l.length * c + (l.map f).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; rw [Nat.succ_mul]; omega

theorem PrepWF.prefixSides_eq {p : Prep} (hp : PrepWF p) (cost : Nat → Nat) {x j : Nat}
    (hx : x < p.dag.size) (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!) :
    prefixSides p cost x j =
      j * (p.dag.node x).sideExtra + ((List.range j).map fun k => cost (sideAt p x k)).sum := by
  rw [prefixSides_eq_sum]
  have : ∀ k ∈ List.range j, sideCost p cost (spineAt p x k) =
      (p.dag.node x).sideExtra + cost (sideAt p x k) := by
    intro k hk
    rw [List.mem_range] at hk
    unfold sideCost sideAt
    rw [hp.sideExtra_spine hx hf (by omega)]
  rw [List.map_congr_left this, sum_map_const_add]
  simp

theorem PrepWF.sideAt_lt {p : Prep} (hp : PrepWF p) {x k : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hk : k < p.spineLen[x]!) : sideAt p x k < x := by
  obtain ⟨_, hsp, _, _, _⟩ := hp.spine x hx hf
  obtain ⟨hle, hfam, _, _⟩ := hsp k hk
  have := hp.sideChild_lt (t := spineAt p x k) (by omega) (by rw [hfam]; exact hf)
  unfold sideAt
  omega

theorem costOf_le_inl (p : Prep) (w : Nat) (S : Nat → Bool) (f : Nat → Nat) (x : Nat) :
    costOf p w S f x ≤ inlOf p w S f x := by
  unfold costOf; split <;> omega

theorem PrepWF.inl_node {p : Prep} (hp : PrepWF p) (w : Nat) (S : Nat → Bool) (f : Nat → Nat)
    {x : Nat} (hx : x < p.dag.size) (hf : p.family[x]! = .none) :
    inlOf p w S f x = (p.dag.node x).head.ownBytes +
      ((List.range (p.dag.node x).head.arity).map fun i => f ((p.dag.node x).child i)).sum := by
  unfold inlOf
  rw [ite_eq_left hf, ← Array.foldl_toList, foldl_add_eq_sum]
  have har := hp.dag.arity x hx
  rw [← dag_node_eq hx] at har
  rw [children_toList har, List.map_map]
  rfl

theorem inl_tele {p : Prep} (w : Nat) (S : Nat → Bool) (f : Nat → Nat)
    {x : Nat} (hf : p.family[x]! ≠ .none) :
    inlOf p w S f x = (cutCosts p w S f x).foldl min (naturalCost p f x) := by
  unfold inlOf
  rw [ite_eq_right hf]

theorem cut_mem_cutCosts (p : Prep) (w : Nat) (S : Nat → Bool) (f : Nat → Nat) {x j : Nat}
    (hj1 : 1 ≤ j) (hj : j < p.spineLen[x]!) (hS : S (spineAt p x j) = true) :
    cutCost p w f x j ∈ cutCosts p w S f x := by
  rw [cutCosts_eq]
  unfold cutsFrom
  apply List.mem_filterMap.mpr
  refine ⟨j, List.mem_range'_1.mpr ⟨hj1, by omega⟩, ?_⟩
  rw [ite_eq_left hS]

theorem sum_le_sum_of_le {f g : Nat → Nat} :
    ∀ (l : List Nat), (∀ k ∈ l, f k ≤ g k) → (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons k ks ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    have h1 := h k List.mem_cons_self
    have h2 := ih (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    omega

theorem costs_eq_range (p : Prep) (w : Nat) (l : List WTree) :
    WTree.costs p w l = ((List.range l.length).map fun k => (l[k]?.getD default).cost p w).sum := by
  rw [WTree.costs_eq]
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getElem?_eq_getElem (by simpa using h1)]
  rfl

/-- **Lower bound.** Every writing of `x` is at least `C_S(x)` long, and
every inline writing at least `inl_S(x)`. -/
theorem PrepWF.valid_cost {p : Prep} (hp : PrepWF p) (w : Nat) (S : Nat → Bool) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      uCost p w S x ≤ T.cost p w ∧ (T.isShare = false → uInl p w S x ≤ T.cost p w) := by
  intro x T h
  induction h with
  | share hS =>
    intro hx
    refine ⟨?_, fun h => by simp [WTree.isShare] at h⟩
    rw [hp.uCost_eq w S _ hx]
    unfold costOf
    simp only [hS, ite_true, WTree.cost]
    omega
  | @node x kids hf hlen _ ih =>
    intro hx
    have hinl : uInl p w S x ≤ (WTree.node x kids).cost p w := by
      unfold uInl
      rw [hp.inl_node w S _ hx hf]
      simp only [WTree.cost]
      rw [costs_eq_range, hlen]
      have : ∀ i ∈ List.range (p.dag.node x).head.arity,
          uCost p w S ((p.dag.node x).child i) ≤ (kids[i]?.getD default).cost p w := by
        intro i hi
        rw [List.mem_range] at hi
        have hc := hp.dag.childAt_lt hx hi
        rw [show kids[i]?.getD default = kids[i]'(by omega) by simp [hlen ▸ hi]]
        exact (ih i (by omega) (by omega)).1
      have := sum_le_sum_of_le _ this
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.uCost_eq w S _ hx]
    exact Nat.le_trans (costOf_le_inl _ _ _ _ _) hinl
  | @teleCut x j sides hf hj1 hj hlen _ hS ih =>
    intro hx
    have hinl : uInl p w S x ≤ (WTree.tele x j sides (.share (spineAt p x j))).cost p w := by
      unfold uInl
      rw [inl_tele w S _ hf]
      refine Nat.le_trans (foldl_min_le _ _ _ (List.mem_cons_of_mem _
        (cut_mem_cutCosts p w S _ hj1 hj hS))) ?_
      unfold cutCost
      rw [hp.prefixSides_eq _ hx hf (by omega)]
      simp only [WTree.cost]
      rw [costs_eq_range, hlen]
      have : ∀ k ∈ List.range j, uCost p w S (sideAt p x k) ≤ (sides[k]?.getD default).cost p w := by
        intro k hk
        rw [List.mem_range] at hk
        rw [show sides[k]?.getD default = sides[k]'(by omega) by simp [hlen ▸ hk]]
        exact (ih k (by omega) (by have := hp.sideAt_lt hx hf (k := k) (by omega); omega)).1
      have := sum_le_sum_of_le _ this
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.uCost_eq w S _ hx]
    exact Nat.le_trans (costOf_le_inl _ _ _ _ _) hinl
  | @teleFull x sides tail hf hlen _ _ ih iht =>
    intro hx
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    have hinl : uInl p w S x ≤ (WTree.tele x p.spineLen[x]! sides tail).cost p w := by
      unfold uInl
      rw [inl_tele w S _ hf]
      refine Nat.le_trans (foldl_min_le _ _ _ List.mem_cons_self) ?_
      unfold naturalCost
      rw [hp.prefixSides_eq _ hx hf (Nat.le_refl _)]
      simp only [WTree.cost]
      rw [costs_eq_range, hlen]
      have : ∀ k ∈ List.range p.spineLen[x]!,
          uCost p w S (sideAt p x k) ≤ (sides[k]?.getD default).cost p w := by
        intro k hk
        rw [List.mem_range] at hk
        rw [show sides[k]?.getD default = sides[k]'(by omega) by simp [hlen ▸ hk]]
        exact (ih k (by omega) (by have := hp.sideAt_lt hx hf (k := k) (by omega); omega)).1
      have := sum_le_sum_of_le _ this
      have ht := (iht (by omega)).1
      omega
    refine ⟨?_, fun _ => hinl⟩
    rw [hp.uCost_eq w S _ hx]
    exact Nat.le_trans (costOf_le_inl _ _ _ _ _) hinl

theorem mem_cutCosts {p : Prep} {w : Nat} {S : Nat → Bool} {f : Nat → Nat} {x c : Nat}
    (h : c ∈ cutCosts p w S f x) :
    ∃ j, 1 ≤ j ∧ j < p.spineLen[x]! ∧ S (spineAt p x j) = true ∧ c = cutCost p w f x j := by
  rw [cutCosts_eq] at h
  unfold cutsFrom at h
  obtain ⟨j, hj, hjv⟩ := List.mem_filterMap.mp h
  rw [List.mem_range'_1] at hj
  split at hjv
  · rename_i hS
    simp only [Option.some.injEq] at hjv
    exact ⟨j, hj.1, by omega, hS, hjv.symm⟩
  · cases hjv

theorem costs_map_range (p : Prep) (w : Nat) (g : Nat → WTree) (n : Nat) :
    WTree.costs p w ((List.range n).map g) = ((List.range n).map fun k => (g k).cost p w).sum := by
  rw [WTree.costs_eq, List.map_map]
  rfl

/-- **Attainment.** Some writing of `x` has length `C_S(x)`, and some inline
writing has length `inl_S(x)`. -/
theorem PrepWF.exists_opt {p : Prep} (hp : PrepWF p) (w : Nat) (S : Nat → Bool) :
    ∀ x, x < p.dag.size →
      (∃ T, Valid p S x T ∧ T.cost p w = uCost p w S x) ∧
        ∃ T, Valid p S x T ∧ T.isShare = false ∧ T.cost p w = uInl p w S x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    classical
    let g : Nat → WTree := fun c =>
      if h : c < x ∧ c < p.dag.size then Classical.choose (ih c h.1 h.2).1 else default
    have hg : ∀ c, c < x → Valid p S c (g c) ∧ (g c).cost p w = uCost p w S c := by
      intro c hc
      have hcn : c < p.dag.size := by omega
      simp only [g, dite_eq_left (And.intro hc hcn)]
      exact Classical.choose_spec (ih c hc hcn).1
    -- an optimal inline writing
    have hinl : ∃ T, Valid p S x T ∧ T.isShare = false ∧ T.cost p w = uInl p w S x := by
      by_cases hf : p.family[x]! = .none
      · let ar := (p.dag.node x).head.arity
        refine ⟨.node x ((List.range ar).map fun i => g ((p.dag.node x).child i)), ?_, rfl, ?_⟩
        · refine Valid.node hf (by simp [ar]) fun i hi => ?_
          simp only [List.length_map, List.length_range] at hi
          simp only [List.getElem_map, List.getElem_range]
          exact (hg _ (hp.dag.childAt_lt hx hi)).1
        · simp only [WTree.cost, costs_map_range]
          unfold uInl
          rw [hp.inl_node w S _ hx hf]
          simp only [ar]
          congr 2
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          exact (hg _ (hp.dag.childAt_lt hx hi)).2
      · obtain ⟨hl1, _, hend, htl, _⟩ := hp.spine x hx hf
        have hmin := foldl_min_mem (cutCosts p w S (uCost p w S) x)
          (naturalCost p (uCost p w S) x)
        rw [← inl_tele w S _ hf] at hmin
        have hsides : ∀ j, j ≤ p.spineLen[x]! →
            WTree.costs p w ((List.range j).map fun k => g (sideAt p x k)) =
              ((List.range j).map fun k => uCost p w S (sideAt p x k)).sum := by
          intro j hj
          rw [costs_map_range]
          congr 1
          apply List.map_congr_left
          intro k hk
          rw [List.mem_range] at hk
          exact (hg _ (hp.sideAt_lt hx hf (by omega))).2
        have hsv : ∀ j, j ≤ p.spineLen[x]! → ∀ (k : Nat)
            (h : k < ((List.range j).map fun k => g (sideAt p x k)).length),
            Valid p S (sideAt p x k) ((List.range j).map fun k => g (sideAt p x k))[k] := by
          intro j hj k hk
          simp only [List.length_map, List.length_range] at hk
          simp only [List.getElem_map, List.getElem_range]
          exact (hg _ (hp.sideAt_lt hx hf (by omega))).1
        rcases List.mem_cons.mp hmin with hnat | hcut
        · refine ⟨.tele x p.spineLen[x]! ((List.range p.spineLen[x]!).map fun k => g (sideAt p x k))
            (g p.tail[x]!), Valid.teleFull hf (by simp) (hsv _ (Nat.le_refl _))
              (hg _ htl).1, rfl, ?_⟩
          simp only [WTree.cost]
          rw [hsides _ (Nat.le_refl _), (hg _ htl).2]
          unfold uInl
          rw [hnat]
          unfold naturalCost
          rw [hp.prefixSides_eq _ hx hf (Nat.le_refl _)]
          omega
        · obtain ⟨j, hj1, hjl, hS, hc⟩ := mem_cutCosts hcut
          refine ⟨.tele x j ((List.range j).map fun k => g (sideAt p x k))
            (.share (spineAt p x j)), Valid.teleCut hf hj1 hjl (by simp) (hsv _ (by omega)) hS,
            rfl, ?_⟩
          simp only [WTree.cost]
          rw [hsides _ (by omega)]
          unfold uInl
          rw [hc]
          unfold cutCost
          rw [hp.prefixSides_eq _ hx hf (by omega)]
          omega
    refine ⟨?_, hinl⟩
    obtain ⟨T, hT, hTs, hTc⟩ := hinl
    rw [hp.uCost_eq w S x hx]
    unfold costOf
    by_cases hS : S x = true
    · by_cases hle : w ≤ inlOf p w S (uCost p w S) x
      · refine ⟨.share x, Valid.share hS, ?_⟩
        simp only [hS, ite_true, WTree.cost]
        omega
      · refine ⟨T, hT, ?_⟩
        simp only [hS, ite_true]
        unfold uInl at hTc
        omega
    · refine ⟨T, hT, ?_⟩
      simp only [hS, Bool.false_eq_true, ite_false]
      exact hTc

/-! ## Complete encodings -/

/-- The length of a complete encoding: the table count, an entry writing for
every table term, and a writing of every root. -/
def encodingCost (p : Prep) (w : Nat) (table : List Nat) (entry : Nat → WTree)
    (rootsW : List WTree) : Nat :=
  tag0Size table.length + (table.map fun s => (entry s).cost p w).sum +
    (rootsW.map (WTree.cost p w)).sum

/-- A complete encoding: every table term has an inline writing, every root
a writing, all using only the table's terms. -/
def EncodingWF (p : Prep) (avail : Nat → Bool) (table : List Nat) (entry : Nat → WTree)
    (roots : List Nat) (rootsW : List WTree) : Prop :=
  (∀ s ∈ table, Valid p avail s (entry s) ∧ (entry s).isShare = false) ∧
    List.Forall₂ (Valid p avail) roots rootsW

theorem forall₂_sum_le {α β : Type} {R : α → β → Prop} {f : α → Nat} {g : β → Nat} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      (∀ a ∈ xs, ∀ b, R a b → f a ≤ g b) → (xs.map f).sum ≤ (ys.map g).sum
  | _, _, .nil, _ => by simp
  | _, _, .cons hr hs, hfg => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := hfg _ List.mem_cons_self _ hr
    have h2 := forall₂_sum_le hs (fun a ha b h => hfg a (List.mem_cons_of_mem _ ha) b h)
    omega

/-- **`uniformCost` is the minimum encoding length.** Every complete encoding
with table `S` is at least `uniformCost S` long. -/
theorem PrepWF.uniformCost_le {p : Prep} (hp : PrepWF p) (w : Nat) (avail : Nat → Bool)
    {table roots : List Nat} {entry : Nat → WTree} {rootsW : List WTree}
    (htable : ∀ s ∈ table, s < p.dag.size) (hroots : ∀ r ∈ roots, r < p.dag.size)
    (h : EncodingWF p avail table entry roots rootsW) :
    uniformCost p w avail table roots ≤ encodingCost p w table entry rootsW := by
  unfold uniformCost encodingCost
  have he : (table.map (uInl p w avail)).sum ≤ (table.map fun s => (entry s).cost p w).sum :=
    sum_le_sum_of_le' fun s hs => (hp.valid_cost w avail (h.1 s hs).1 (htable s hs)).2 (h.1 s hs).2
  have hr : (roots.map (uCost p w avail)).sum ≤ (rootsW.map (WTree.cost p w)).sum :=
    forall₂_sum_le h.2 fun r hr T hT => (hp.valid_cost w avail hT (hroots r hr)).1
  omega
where
  sum_le_sum_of_le' {f g : Nat → Nat} {l : List Nat} (h : ∀ k ∈ l, f k ≤ g k) :
      (l.map f).sum ≤ (l.map g).sum := sum_le_sum_of_le l h

/-- **… and it is attained.** -/
theorem PrepWF.uniformCost_attained {p : Prep} (hp : PrepWF p) (w : Nat) (avail : Nat → Bool)
    (table roots : List Nat) (htable : ∀ s ∈ table, s < p.dag.size)
    (hroots : ∀ r ∈ roots, r < p.dag.size) :
    ∃ entry rootsW, EncodingWF p avail table entry roots rootsW ∧
      encodingCost p w table entry rootsW = uniformCost p w avail table roots := by
  classical
  let entry : Nat → WTree := fun s =>
    if h : s < p.dag.size then Classical.choose (hp.exists_opt w avail s h).2 else default
  have hentry : ∀ s, s < p.dag.size → Valid p avail s (entry s) ∧ (entry s).isShare = false ∧
      (entry s).cost p w = uInl p w avail s := by
    intro s hs
    simp only [entry, dite_eq_left hs]
    exact Classical.choose_spec (hp.exists_opt w avail s hs).2
  let rootW : Nat → WTree := fun r =>
    if h : r < p.dag.size then Classical.choose (hp.exists_opt w avail r h).1 else default
  have hrootW : ∀ r, r < p.dag.size → Valid p avail r (rootW r) ∧
      (rootW r).cost p w = uCost p w avail r := by
    intro r hr
    simp only [rootW, dite_eq_left hr]
    exact Classical.choose_spec (hp.exists_opt w avail r hr).1
  refine ⟨entry, roots.map rootW, ⟨fun s hs => ⟨(hentry s (htable s hs)).1,
    (hentry s (htable s hs)).2.1⟩, ?_⟩, ?_⟩
  · clear htable
    induction roots with
    | nil => exact .nil
    | cons r rs ih =>
      exact .cons (hrootW r (hroots r List.mem_cons_self)).1
        (ih (fun r' h => hroots r' (List.mem_cons_of_mem _ h)))
  · unfold encodingCost uniformCost
    rw [List.map_congr_left fun s hs => (hentry s (htable s hs)).2.2, List.map_map]
    congr 2
    apply List.map_congr_left
    intro r hr
    exact (hrootW r (hroots r hr)).2

end Ix.Sharing.Verify.UniformModel
