import Ix.Sharing.Verify.SharingExactPasses

/-!
# Exact sharing: determinism of canonical structural IDs

`canonicalize` renumbers the reachable nodes of a hash-consed temporary DAG
by height, then by the §3.2 key. The theorem `canonicalize_det` states that
its result depends only on the root terms: two temporary DAGs (any IDs, any
unreachable nodes) whose roots denote the same terms canonicalize to the
same DAG and root IDs.
-/

namespace Ix.Sharing.Verify.SharingExact

open Ix.Sharing.Exact

section Canon

/-! ## Temporary DAGs -/

/-- Children precede their parents. -/
def CP (temp : Array Node) : Prop :=
  ∀ t, t < temp.size → ∀ c ∈ (temp[t]!).children, c < t

/-- Every node has exactly `head.arity` children. -/
def NodeArity (temp : Array Node) : Prop :=
  ∀ t, t < temp.size → (temp[t]!).children.size = (temp[t]!).head.arity

theorem getElem!_eq_getElem {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  simp [h]

theorem cp_of_childrenPrecede {temp : Array Node} (h : childrenPrecede temp = true) :
    CP temp := by
  intro t ht c hc
  unfold childrenPrecede at h
  rw [Array.all_eq_true] at h
  have := h t (by simpa using ht)
  simp only [Array.getElem_zipIdx, Nat.zero_add] at this
  rw [Array.all_eq_true] at this
  rw [getElem!_eq_getElem temp t ht] at hc
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
  simpa using this k hk

/-- The term a temporary node denotes. -/
def termOf (temp : Array Node) (t : Nat) : Ixon.Expr :=
  (temp[t]!).toExpr fun c => if _h : c < t then termOf temp c else default
termination_by t
decreasing_by assumption

theorem termOf_eq (temp : Array Node) (t : Nat) :
    termOf temp t = (temp[t]!).toExpr fun c => if c < t then termOf temp c else default := by
  rw [termOf]
  simp only [dite_eq_ite]

/-- A node is determined, up to its children's terms, by the expression it
builds. -/
theorem toExpr_inj {n₁ n₂ : Node} {f₁ f₂ : Nat → Ixon.Expr}
    (h : n₁.toExpr f₁ = n₂.toExpr f₂) :
    n₁.head = n₂.head ∧ ∀ k, k < n₁.head.arity → f₁ (n₁.child k) = f₂ (n₂.child k) := by
  unfold Node.toExpr at h
  cases h1 : n₁.head <;> cases h2 : n₂.head <;> simp only [h1, h2] at h <;> simp at h
  all_goals (refine ⟨by simp_all, fun k hk => ?_⟩; simp only [Head.arity] at hk)
  all_goals (rcases k with _ | _ | _ | k <;> first | omega | simp_all)

theorem child_eq_getElem (n : Node) (k : Nat) (hk : k < n.children.size) :
    n.child k = n.children[k] := by
  simp [Node.child, Array.getD_eq_getD_getElem?, hk]

/-- Nodes denoting the same term have the same head and children denoting
the same terms. -/
theorem children_corr {temp₁ temp₂ : Array Node} (hcp₁ : CP temp₁) (hcp₂ : CP temp₂)
    (har₁ : NodeArity temp₁) (har₂ : NodeArity temp₂) {t s : Nat}
    (ht : t < temp₁.size) (hs : s < temp₂.size) (h : termOf temp₁ t = termOf temp₂ s) :
    (temp₁[t]!).head = (temp₂[s]!).head ∧
      (temp₁[t]!).children.size = (temp₂[s]!).children.size ∧
      ∀ (k : Nat) (hk₁ : k < (temp₁[t]!).children.size) (hk₂ : k < (temp₂[s]!).children.size),
        termOf temp₁ (temp₁[t]!).children[k] = termOf temp₂ (temp₂[s]!).children[k] := by
  rw [termOf_eq, termOf_eq temp₂] at h
  obtain ⟨hhead, hk⟩ := toExpr_inj h
  have hsize : (temp₁[t]!).children.size = (temp₂[s]!).children.size := by
    rw [har₁ t ht, har₂ s hs, hhead]
  refine ⟨hhead, hsize, fun k hk₁ hk₂ => ?_⟩
  have := hk k (by rw [← har₁ t ht]; exact hk₁)
  rw [child_eq_getElem _ k hk₁, child_eq_getElem _ k hk₂] at this
  rw [ite_eq_left (hcp₁ t ht _ (Array.getElem_mem hk₁)),
    ite_eq_left (hcp₂ s hs _ (Array.getElem_mem hk₂))] at this
  exact this

/-! ## Reachability -/

/-- `t` is reachable from `roots` through child edges. -/
inductive Reach (temp : Array Node) (roots : Array Nat) : Nat → Prop
  | root {t : Nat} : t ∈ roots → Reach temp roots t
  | child {t c : Nat} : Reach temp roots t → c ∈ (temp[t]!).children → Reach temp roots c

theorem reach_lt {temp : Array Node} {roots : Array Nat} (hcp : CP temp)
    (hin : ∀ r ∈ roots, r < temp.size) {t : Nat} (h : Reach temp roots t) : t < temp.size := by
  induction h with
  | root hr => exact hin _ hr
  | child _ hc ih => exact Nat.lt_trans (hcp _ ih _ hc) ih

/-- Reachable terms of one DAG are reachable terms of any other DAG whose
roots denote the same terms. -/
theorem reach_transfer {temp₁ temp₂ : Array Node} {roots₁ roots₂ : Array Nat}
    (hcp₁ : CP temp₁) (hcp₂ : CP temp₂) (har₁ : NodeArity temp₁) (har₂ : NodeArity temp₂)
    (hin₁ : ∀ r ∈ roots₁, r < temp₁.size) (hin₂ : ∀ r ∈ roots₂, r < temp₂.size)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) {t : Nat}
    (h : Reach temp₁ roots₁ t) :
    ∃ s, Reach temp₂ roots₂ s ∧ termOf temp₁ t = termOf temp₂ s := by
  induction h with
  | root hr =>
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    have hsz : roots₁.size = roots₂.size := by
      simpa using congrArg Array.size hroots
    refine ⟨roots₂[i], .root (Array.getElem_mem _), ?_⟩
    have := congrArg (·[i]?) hroots
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem (hsz ▸ hi), Option.map_some, Option.some.injEq] at this
    exact this
  | @child t c hreach hc ih =>
    obtain ⟨s, hs, hts⟩ := ih
    have ht := reach_lt hcp₁ hin₁ hreach
    have hs' := reach_lt hcp₂ hin₂ hs
    obtain ⟨_, hsize, hk⟩ := children_corr hcp₁ hcp₂ har₁ har₂ ht hs' hts
    obtain ⟨k, hk₁, rfl⟩ := Array.mem_iff_getElem.mp hc
    exact ⟨_, .child hs (Array.getElem_mem (hsize ▸ hk₁)), hk k hk₁ (hsize ▸ hk₁)⟩

theorem getElem!_bool_iff (a : Array Bool) (i : Nat) : a[i]! = true ↔ a[i]? = some true := by
  rw [getElem!_def]
  cases a[i]? with
  | none => simp
  | some b => simp

theorem foldl_setTrue_size (l : List Nat) (arr : Array Bool) :
    (l.foldl (fun r c => r.set! c true) arr).size = arr.size := by
  induction l generalizing arr with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; simp [Array.set!]

theorem foldl_setTrue_getElem (l : List Nat) (arr : Array Bool) (t : Nat) :
    (l.foldl (fun r c => r.set! c true) arr)[t]! = true ↔
      arr[t]! = true ∨ (t ∈ l ∧ t < arr.size) := by
  induction l generalizing arr with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [Array.set!, Array.size_setIfInBounds, List.mem_cons, getElem!_bool_iff,
      Array.getElem?_setIfInBounds]
    by_cases hx : x = t
    · subst hx
      by_cases hlt : x < arr.size <;> simp [hlt]
    · simp only [hx, ite_false]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨h1 | h1, h2⟩)
        · exact Or.inl h
        · exact absurd h1.symm hx
        · exact Or.inr ⟨h1, h2⟩

/-- The marking step of `reachMarks` for node `t`. -/
def markStep (temp : Array Node) (t : Nat) (reach : Array Bool) : Array Bool :=
  if reach[t]! then temp[t]!.children.foldl (fun r c => r.set! c true) reach else reach

theorem markStep_size (temp : Array Node) (t : Nat) (reach : Array Bool) :
    (markStep temp t reach).size = reach.size := by
  unfold markStep
  split
  · rw [← Array.foldl_toList, foldl_setTrue_size]
  · rfl

/-- The marks after visiting the IDs from `m` up. -/
def marksFrom (temp : Array Node) (roots : Array Nat) (m : Nat) : Array Bool :=
  (List.range' m (temp.size - m)).foldr (markStep temp)
    (roots.foldl (fun r t => r.set! t true) (Array.replicate temp.size false))

theorem reachMarks_eq (temp : Array Node) (roots : Array Nat) :
    reachMarks temp roots = marksFrom temp roots 0 := by
  unfold reachMarks marksFrom
  rw [List.range_eq_range', Nat.sub_zero]
  rfl

theorem marksFrom_succ (temp : Array Node) (roots : Array Nat) (m : Nat) (hm : m < temp.size) :
    marksFrom temp roots m = markStep temp m (marksFrom temp roots (m + 1)) := by
  unfold marksFrom
  rw [show temp.size - m = (temp.size - (m + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem marksFrom_size (temp : Array Node) (roots : Array Nat) (m : Nat) :
    (marksFrom temp roots m).size = temp.size := by
  unfold marksFrom
  generalize List.range' m (temp.size - m) = l
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    rw [← Array.foldl_toList, foldl_setTrue_size, Array.size_replicate]
  | cons x xs ih => rw [List.foldr_cons, markStep_size, ih]

/-- The marks are exactly the reachable nodes. -/
theorem reachMarks_spec {temp : Array Node} {roots : Array Nat} (hcp : CP temp)
    (hin : ∀ r ∈ roots, r < temp.size) (t : Nat) (ht : t < temp.size) :
    (reachMarks temp roots)[t]! = true ↔ Reach temp roots t := by
  let Q (m t : Nat) : Prop :=
    t ∈ roots ∨ ∃ p, m ≤ p ∧ Reach temp roots p ∧ t ∈ (temp[p]!).children
  have hinv : ∀ k, k ≤ temp.size → ∀ t, t < temp.size →
      ((marksFrom temp roots (temp.size - k))[t]! = true ↔ Q (temp.size - k) t) := by
    intro k
    induction k with
    | zero =>
      intro _ t ht
      unfold marksFrom
      simp only [Nat.sub_zero, Nat.sub_self, List.range'_zero, List.foldr_nil]
      rw [← Array.foldl_toList, foldl_setTrue_getElem]
      have hf : ¬ (Array.replicate temp.size false)[t]! = true := by
        rw [getElem!_bool_iff, Array.getElem?_replicate]; simp
      simp only [Array.size_replicate, Array.mem_toList_iff]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact absurd h hf
        · exact Or.inl h
      · rintro (h | ⟨p, hp, hr, _⟩)
        · exact Or.inr ⟨h, ht⟩
        · exact absurd (reach_lt hcp hin hr) (by omega)
    | succ k ih =>
      intro hk t ht
      have hm : temp.size - (k + 1) < temp.size := by omega
      have hm1 : temp.size - (k + 1) + 1 = temp.size - k := by omega
      rw [marksFrom_succ temp roots _ hm, hm1]
      have hreach : (marksFrom temp roots (temp.size - k))[temp.size - (k + 1)]! = true ↔
          Reach temp roots (temp.size - (k + 1)) := by
        rw [ih (by omega) _ hm]
        constructor
        · rintro (h | ⟨p, _, hp, hc⟩)
          · exact .root h
          · exact .child hp hc
        · intro h
          cases h with
          | root h => exact Or.inl h
          | @child p _ hp hc =>
            exact Or.inr ⟨p, by have := hcp p (reach_lt hcp hin hp) _ hc; omega, hp, hc⟩
      unfold markStep
      split
      · rename_i hmark
        rw [← Array.foldl_toList, foldl_setTrue_getElem, ih (by omega) t ht, marksFrom_size,
          Array.mem_toList_iff]
        have hr := hreach.mp hmark
        constructor
        · rintro (h | ⟨hc, _⟩)
          · rcases h with h | ⟨p, hp, hpr, hc⟩
            · exact Or.inl h
            · exact Or.inr ⟨p, by omega, hpr, hc⟩
          · exact Or.inr ⟨_, Nat.le_refl _, hr, hc⟩
        · rintro (h | ⟨p, hp, hpr, hc⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hpe : p = temp.size - (k + 1)
            · subst hpe
              exact Or.inr ⟨hc, ht⟩
            · exact Or.inl (Or.inr ⟨p, by omega, hpr, hc⟩)
      · rename_i hmark
        rw [ih (by omega) t ht]
        constructor
        · rintro (h | ⟨p, hp, hpr, hc⟩)
          · exact Or.inl h
          · exact Or.inr ⟨p, by omega, hpr, hc⟩
        · rintro (h | ⟨p, hp, hpr, hc⟩)
          · exact Or.inl h
          · by_cases hpe : p = temp.size - (k + 1)
            · subst hpe
              exact absurd (hreach.mpr hpr) hmark
            · exact Or.inr ⟨p, by omega, hpr, hc⟩
  rw [reachMarks_eq]
  have := hinv temp.size (Nat.le_refl _) t ht
  rw [Nat.sub_self] at this
  rw [this]
  constructor
  · rintro (h | ⟨p, _, hp, hc⟩)
    · exact .root h
    · exact .child hp hc
  · intro h
    cases h with
    | root h => exact Or.inl h
    | @child p _ hp hc => exact Or.inr ⟨p, Nat.zero_le _, hp, hc⟩

/-! ## Heights -/

theorem setBang_getElem! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size <;> simp [hi]
  · simp [hij]

/-- One height step: one more than the highest child, `0` for a leaf. -/
def heightOf (temp : Array Node) (height : Array Nat) (t : Nat) : Nat :=
  (temp[t]!).children.foldl (fun acc c => max acc (height[c]! + 1)) 0

theorem heightOf_eq_map (temp : Array Node) (height : Array Nat) (t : Nat) :
    heightOf temp height t =
      (((temp[t]!).children.toList.map (height[·]!)).foldl (fun acc x => max acc (x + 1)) 0) := by
  unfold heightOf
  rw [← Array.foldl_toList, List.foldl_map]

theorem heightOf_congr (temp : Array Node) (h₁ h₂ : Array Nat) (t : Nat)
    (h : ∀ c ∈ (temp[t]!).children, h₁[c]! = h₂[c]!) :
    heightOf temp h₁ t = heightOf temp h₂ t := by
  rw [heightOf_eq_map, heightOf_eq_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact h c (Array.mem_toList_iff.mp hc)

theorem foldl_max_ge (l : List Nat) (acc : Nat) :
    acc ≤ l.foldl (fun acc x => max acc (x + 1)) acc ∧
      ∀ x ∈ l, x + 1 ≤ l.foldl (fun acc x => max acc (x + 1)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih (max acc (y + 1))
    refine ⟨by simp only [List.foldl_cons]; omega, fun x hx => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact h2 x hx

theorem child_height_lt (temp : Array Node) (height : Array Nat) (t c : Nat)
    (hc : c ∈ (temp[t]!).children) : height[c]! < heightOf temp height t := by
  rw [heightOf_eq_map]
  have := (foldl_max_ge ((temp[t]!).children.toList.map (height[·]!)) 0).2 (height[c]!)
    (List.mem_map_of_mem (f := (height[·]!)) (Array.mem_toList_iff.mpr hc))
  omega

/-- Each stored height is the height step of its node. -/
theorem nodeHeights_spec {temp : Array Node} (hcp : CP temp) (t : Nat) (ht : t < temp.size) :
    (nodeHeights temp)[t]! = heightOf temp (nodeHeights temp) t := by
  let step := fun (height : Array Nat) (t : Nat) => height.set! t (heightOf temp height t)
  have hinv : ∀ m, m ≤ temp.size →
      ((List.range m).foldl step (Array.replicate temp.size 0)).size = temp.size ∧
      ∀ t, t < m → ((List.range m).foldl step (Array.replicate temp.size 0))[t]! =
        heightOf temp ((List.range m).foldl step (Array.replicate temp.size 0)) t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      obtain ⟨hsize, hprev⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hH : List.foldl step (Array.replicate temp.size 0) (List.range m) = H at hsize hprev
      have hsame : ∀ c, c < m → (step H m)[c]! = H[c]! := by
        intro c hc
        simp only [step, setBang_getElem!]
        rw [ite_eq_right (by omega)]
      refine ⟨by simp [step, hsize], fun t' ht' => ?_⟩
      have hcongr : heightOf temp (step H m) t' = heightOf temp H t' :=
        heightOf_congr temp _ _ t' fun c hc =>
          hsame c (by have := hcp t' (by omega) c hc; omega)
      rw [hcongr]
      by_cases htm : t' = m
      · subst htm
        simp only [step, setBang_getElem!, hsize]
        rw [ite_eq_left (by simp; omega)]
      · rw [hsame t' (by omega)]
        exact hprev t' (by omega)
  have := (hinv temp.size (Nat.le_refl _)).2 t ht
  exact this

/-! ## Two inputs denoting the same roots -/

/-- The hypotheses on one `canonicalize` input: children precede parents (as
checked), the arity invariant, roots in range, and hash-consing (distinct
reachable nodes denote distinct terms). -/
structure Run (temp : Array Node) (roots : Array Nat) : Prop where
  precede : childrenPrecede temp = true
  arity : NodeArity temp
  inRange : ∀ r ∈ roots, r < temp.size
  hashConsed : ∀ s t, Reach temp roots s → Reach temp roots t →
    termOf temp s = termOf temp t → s = t

theorem Run.cp {temp : Array Node} {roots : Array Nat} (h : Run temp roots) : CP temp :=
  cp_of_childrenPrecede h.precede

/-- Reachable nodes of the two inputs that denote the same term. -/
def Corr (temp₁ temp₂ : Array Node) (roots₁ roots₂ : Array Nat) (t s : Nat) : Prop :=
  Reach temp₁ roots₁ t ∧ Reach temp₂ roots₂ s ∧ termOf temp₁ t = termOf temp₂ s

variable {temp₁ temp₂ : Array Node} {roots₁ roots₂ : Array Nat}

theorem Corr.symm {t s : Nat} (h : Corr temp₁ temp₂ roots₁ roots₂ t s) :
    Corr temp₂ temp₁ roots₂ roots₁ s t :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem corr_total (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) {t : Nat}
    (ht : Reach temp₁ roots₁ t) : ∃ s, Corr temp₁ temp₂ roots₁ roots₂ t s := by
  obtain ⟨s, hs, he⟩ := reach_transfer h₁.cp h₂.cp h₁.arity h₂.arity h₁.inRange h₂.inRange
    hroots ht
  exact ⟨s, ht, hs, he⟩

theorem corr_func (h₂ : Run temp₂ roots₂) {t s s' : Nat}
    (h : Corr temp₁ temp₂ roots₁ roots₂ t s) (h' : Corr temp₁ temp₂ roots₁ roots₂ t s') :
    s = s' :=
  h₂.hashConsed s s' h.2.1 h'.2.1 (h.2.2.symm.trans h'.2.2)

theorem corr_inj (h₁ : Run temp₁ roots₁) {t t' s : Nat}
    (h : Corr temp₁ temp₂ roots₁ roots₂ t s) (h' : Corr temp₁ temp₂ roots₁ roots₂ t' s) :
    t = t' :=
  h₁.hashConsed t t' h.1 h'.1 (h.2.2.trans h'.2.2.symm)

theorem corr_children (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂) {t s : Nat}
    (hc : Corr temp₁ temp₂ roots₁ roots₂ t s) :
    (temp₁[t]!).head = (temp₂[s]!).head ∧
      (temp₁[t]!).children.size = (temp₂[s]!).children.size ∧
      ∀ (k : Nat) (hk₁ : k < (temp₁[t]!).children.size) (hk₂ : k < (temp₂[s]!).children.size),
        Corr temp₁ temp₂ roots₁ roots₂ (temp₁[t]!).children[k] (temp₂[s]!).children[k] := by
  have ht := reach_lt h₁.cp h₁.inRange hc.1
  have hs := reach_lt h₂.cp h₂.inRange hc.2.1
  obtain ⟨hhead, hsize, hk⟩ := children_corr h₁.cp h₂.cp h₁.arity h₂.arity ht hs hc.2.2
  exact ⟨hhead, hsize, fun k hk₁ hk₂ =>
    ⟨.child hc.1 (Array.getElem_mem hk₁), .child hc.2.1 (Array.getElem_mem hk₂), hk k hk₁ hk₂⟩⟩

/-- Corresponding nodes have the same height. -/
theorem corr_height (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂) :
    ∀ t s, Corr temp₁ temp₂ roots₁ roots₂ t s →
      (nodeHeights temp₁)[t]! = (nodeHeights temp₂)[s]! := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro s hc
    have ht := reach_lt h₁.cp h₁.inRange hc.1
    have hs := reach_lt h₂.cp h₂.inRange hc.2.1
    rw [nodeHeights_spec h₁.cp t ht, nodeHeights_spec h₂.cp s hs, heightOf_eq_map,
      heightOf_eq_map]
    congr 1
    obtain ⟨_, hsize, hk⟩ := corr_children h₁ h₂ hc
    apply List.ext_getElem (by simp [hsize])
    intro k hk₁ hk₂
    simp only [List.getElem_map, Array.getElem_toList]
    simp only [List.length_map, Array.length_toList] at hk₁ hk₂
    exact ih _ (h₁.cp t ht _ (Array.getElem_mem hk₁)) _ (hk k hk₁ hk₂)

/-! ## Maximum height and buckets -/

/-- The largest height of a marked node (the `maxH` of `canonicalize`). -/
def maxHeight (reach : Array Bool) (height : Array Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc t => if reach[t]! then max acc height[t]! else acc) 0

theorem maxHeight_spec (reach : Array Bool) (height : Array Nat) (n : Nat) :
    (∀ t, t < n → reach[t]! = true → height[t]! ≤ maxHeight reach height n) ∧
      (maxHeight reach height n = 0 ∨
        ∃ t, t < n ∧ reach[t]! = true ∧ height[t]! = maxHeight reach height n) := by
  induction n with
  | zero => simp [maxHeight]
  | succ n ih =>
    obtain ⟨hge, hatt⟩ := ih
    have hstep : maxHeight reach height (n + 1) =
        if reach[n]! then max (maxHeight reach height n) height[n]!
        else maxHeight reach height n := by
      unfold maxHeight
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    split
    · rename_i hn
      refine ⟨fun t ht hr => ?_, ?_⟩
      · by_cases htn : t = n
        · subst htn; omega
        · have := hge t (by omega) hr; omega
      · by_cases hle : maxHeight reach height n ≤ height[n]!
        · exact Or.inr ⟨n, by omega, hn, by omega⟩
        · rcases hatt with h0 | ⟨t, ht, hr, he⟩
          · omega
          · exact Or.inr ⟨t, by omega, hr, by omega⟩
    · rename_i hn
      refine ⟨fun t ht hr => ?_, ?_⟩
      · by_cases htn : t = n
        · subst htn; exact absurd hr hn
        · exact hge t (by omega) hr
      · rcases hatt with h0 | ⟨t, ht, hr, he⟩
        · exact Or.inl h0
        · exact Or.inr ⟨t, by omega, hr, he⟩

theorem modify_getElem! {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (f : α → α)
    (hi : i < a.size) : (a.modify i f)[j]! = if i = j then f a[j]! else a[j]! := by
  simp only [getElem!_def, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    simp [Array.getElem?_eq_getElem hi]
  · simp [hij]

theorem heightBuckets_spec (reach : Array Bool) (height : Array Nat) (maxH n : Nat)
    (hle : ∀ t, t < n → reach[t]! = true → height[t]! ≤ maxH) :
    (heightBuckets reach height maxH n).size = maxH + 1 ∧
      ∀ h, h ≤ maxH → ((heightBuckets reach height maxH n)[h]!).toList =
        (List.range n).filter (fun t => reach[t]! && height[t]! == h) := by
  induction n with
  | zero =>
    unfold heightBuckets
    refine ⟨by simp, fun h hh => ?_⟩
    simp [getElem!_def, show h < maxH + 1 by omega]
  | succ n ih =>
    obtain ⟨hsize, hlist⟩ := ih (fun t ht hr => hle t (by omega) hr)
    have hstep : heightBuckets reach height maxH (n + 1) =
        if reach[n]! then (heightBuckets reach height maxH n).modify height[n]! (·.push n)
        else heightBuckets reach height maxH n := by
      unfold heightBuckets
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    split
    · rename_i hn
      have hnle := hle n (by omega) hn
      refine ⟨by simp [hsize], fun h hh => ?_⟩
      rw [List.range_succ, List.filter_append, ← hlist h hh,
        modify_getElem! _ _ _ _ (by omega)]
      by_cases hhn : height[n]! = h
      · subst hhn
        simp [hn]
      · simp [hhn]
    · rename_i hn
      refine ⟨hsize, fun h hh => ?_⟩
      rw [List.range_succ, List.filter_append, hlist h hh]
      simp [hn]

/-! ## Placing a sorted group -/

/-- The key check of `placeSorted`: keys strictly increase (after `prev`). -/
def keysIncreasing : Option Node → List Node → Bool
  | _, [] => true
  | prev, n :: ns =>
    (match prev with
      | some p => Node.compareKey p n == .lt
      | none => true) && keysIncreasing (some n) ns

/-- The assignments of `placeSorted`. -/
def placeFold (l : List (Nat × Node)) (st : Array Nat × Array Node) : Array Nat × Array Node :=
  l.foldl (fun st x => (st.1.set! x.1 st.2.size, st.2.push x.2)) st

theorem placeSorted_eq (l : List (Nat × Node)) (prev : Option Node)
    (st : Array Nat × Array Node) :
    placeSorted l prev st =
      if keysIncreasing prev (l.map (·.2)) then .ok (placeFold l st)
      else .error (.internal "structural keys not strictly increasing within a height") := by
  induction l generalizing prev st with
  | nil => simp [placeSorted, keysIncreasing, placeFold]; rfl
  | cons x rest ih =>
    obtain ⟨t, node⟩ := x
    obtain ⟨canon, out⟩ := st
    have hfold : placeFold ((t, node) :: rest) (canon, out) =
        placeFold rest (canon.set! t out.size, out.push node) := rfl
    cases prev with
    | none =>
      simp only [placeSorted, List.map_cons, keysIncreasing, Bool.true_and, hfold]
      exact ih _ _
    | some p =>
      simp only [placeSorted, List.map_cons, keysIncreasing, hfold]
      by_cases hlt : Node.compareKey p node = .lt
      · simp only [hlt]
        exact ih _ _
      · have hne : (Node.compareKey p node == .lt) = false := by
          cases h : Node.compareKey p node with
          | lt => exact absurd h hlt
          | eq => rfl
          | gt => rfl
        simp only [hne, Bool.false_and]
        rfl

theorem keysIncreasing_pairwise (ns : List Node) :
    ∀ (prev : Option Node), keysIncreasing prev ns = true →
      (∀ p, prev = some p → ∀ x ∈ ns, Node.compareKey p x = .lt) ∧
        ns.Pairwise (fun a b => Node.compareKey a b = .lt) := by
  induction ns with
  | nil => intro _ _; exact ⟨fun _ _ _ h => by simp at h, List.Pairwise.nil⟩
  | cons n ns ih =>
    intro prev h
    simp only [keysIncreasing, Bool.and_eq_true] at h
    obtain ⟨hhead, hrest⟩ := h
    obtain ⟨hfirst, hpw⟩ := ih (some n) hrest
    have hn : ∀ x ∈ ns, Node.compareKey n x = .lt := hfirst n rfl
    refine ⟨fun p hp x hx => ?_, .cons hn hpw⟩
    subst hp
    have hpn : Node.compareKey p n = .lt := by
      simp only at hhead
      revert hhead
      cases Node.compareKey p n <;> intro h <;> first | rfl | exact absurd h (by decide)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hpn
    · exact Std.TransCmp.lt_trans hpn (hn x hx)

theorem keysIncreasing_nodup {ns : List Node} (h : keysIncreasing none ns = true) : ns.Nodup := by
  have hpw := (keysIncreasing_pairwise ns none h).2
  refine hpw.imp ?_
  intro a b hab heq
  subst heq
  rw [Std.ReflCmp.compare_self (cmp := Node.compareKey)] at hab
  cases hab

theorem placeFold_spec :
    ∀ (l : List (Nat × Node)) (canon : Array Nat) (out : Array Node),
      (l.map (·.1)).Nodup → (∀ x ∈ l, x.1 < canon.size) →
      (placeFold l (canon, out)).2 = out ++ (l.map (·.2)).toArray ∧
      (placeFold l (canon, out)).1.size = canon.size ∧
      (∀ t, t ∉ l.map (·.1) → (placeFold l (canon, out)).1[t]! = canon[t]!) ∧
      ∀ (i : Nat) (hi : i < l.length), (placeFold l (canon, out)).1[l[i].1]! = out.size + i := by
  intro l
  induction l with
  | nil => intro canon out _ _; simp [placeFold]
  | cons x rest ih =>
    intro canon out hnd hlt
    obtain ⟨t, node⟩ := x
    have hfold : placeFold ((t, node) :: rest) (canon, out) =
        placeFold rest (canon.set! t out.size, out.push node) := rfl
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨htnot, hnd⟩ := hnd
    have hlt' : ∀ y ∈ rest, y.1 < (canon.set! t out.size).size := by
      intro y hy
      simpa [Array.set!] using hlt y (List.mem_cons_of_mem _ hy)
    obtain ⟨hout, hsize, hother, hpos⟩ := ih (canon.set! t out.size) (out.push node) hnd hlt'
    have ht : t < canon.size := hlt (t, node) List.mem_cons_self
    rw [hfold]
    refine ⟨?_, by simp only [Array.set!] at hsize ⊢; rw [hsize]; simp, fun u hu => ?_,
      fun i hi => ?_⟩
    · rw [hout]
      simp
    · simp only [List.map_cons, List.mem_cons, not_or] at hu
      rw [hother u hu.2, setBang_getElem!, ite_eq_right (by intro h; exact hu.1 h.1.symm)]
    · cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [hother t htnot, setBang_getElem!, ite_eq_left ⟨rfl, ht⟩]
        simp
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [hpos i (by simpa using hi)]
        simp only [Array.size_push]
        omega

/-! ## One height group -/

/-- The key of node `t` under the canonical IDs `canon`, as `placeBucket`
builds it. -/
def keyOf (temp : Array Node) (canon : Array Nat) (t : Nat) : Node :=
  { temp[t]! with children := (temp[t]!).children.map (canon[·]!) }

/-- The key-sorted group of `placeBucket`. -/
def sortedGroup (temp : Array Node) (canon : Array Nat) (bucket : Array Nat) :
    List (Nat × Node) :=
  (bucket.toList.map fun t => (t, keyOf temp canon t)).mergeSort
    fun x y => Node.compareKey x.2 y.2 != .gt

theorem placeBucket_eq (temp : Array Node) (st : Array Nat × Array Node) (bucket : Array Nat) :
    placeBucket temp st bucket = placeSorted (sortedGroup temp st.1 bucket) none st := rfl

theorem sortedGroup_perm (temp : Array Node) (canon : Array Nat) (bucket : Array Nat) :
    (sortedGroup temp canon bucket).Perm (bucket.toList.map fun t => (t, keyOf temp canon t)) :=
  List.mergeSort_perm _ _

theorem sortedGroup_nodes (temp : Array Node) (canon : Array Nat) (bucket : Array Nat) :
    (sortedGroup temp canon bucket).map (·.2) =
      (bucket.toList.map (keyOf temp canon)).mergeSort keyLe := by
  unfold sortedGroup
  rw [List.map_mergeSort (s := keyLe) (fun a _ b _ => keyLe_eq a.2 b.2), List.map_map]
  rfl

theorem sortedGroup_fst_perm (temp : Array Node) (canon : Array Nat) (bucket : Array Nat) :
    ((sortedGroup temp canon bucket).map (·.1)).Perm bucket.toList := by
  have := (sortedGroup_perm temp canon bucket).map (·.1)
  rw [List.map_map] at this
  have hid : List.map ((fun x : Nat × Node => x.fst) ∘ fun t => (t, keyOf temp canon t))
      bucket.toList = bucket.toList := by simp [Function.comp_def]
  rw [hid] at this
  exact this

/-- Canonical IDs agree on corresponding nodes below height `h`, and the
outputs agree. -/
def CanonInv (temp₁ temp₂ : Array Node) (roots₁ roots₂ : Array Nat) (h : Nat)
    (st₁ st₂ : Array Nat × Array Node) : Prop :=
  st₁.2 = st₂.2 ∧ st₁.1.size = temp₁.size ∧ st₂.1.size = temp₂.size ∧
    ∀ t s, Corr temp₁ temp₂ roots₁ roots₂ t s → (nodeHeights temp₁)[t]! < h →
      st₁.1[t]! = st₂.1[s]!

/-- The `canonicalize` group of height `h`. -/
def BucketAt (temp : Array Node) (roots : Array Nat) (h : Nat) (B : Array Nat) : Prop :=
  B.toList = (List.range temp.size).filter
    (fun t => (reachMarks temp roots)[t]! && (nodeHeights temp)[t]! == h)

theorem mem_bucket {temp : Array Node} {roots : Array Nat} (hrun : Run temp roots) {h : Nat}
    {B : Array Nat} (hB : BucketAt temp roots h B) (t : Nat) :
    t ∈ B.toList ↔ Reach temp roots t ∧ (nodeHeights temp)[t]! = h := by
  unfold BucketAt at hB
  rw [hB, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ht, hr, hh⟩
    exact ⟨(reachMarks_spec hrun.cp hrun.inRange t ht).mp hr, hh⟩
  · rintro ⟨hr, hh⟩
    have ht := reach_lt hrun.cp hrun.inRange hr
    exact ⟨ht, (reachMarks_spec hrun.cp hrun.inRange t ht).mpr hr, hh⟩

theorem bucket_nodup {temp : Array Node} {roots : Array Nat} {h : Nat} {B : Array Nat}
    (hB : BucketAt temp roots h B) : B.toList.Nodup := by
  unfold BucketAt at hB
  rw [hB]
  exact List.nodup_range.filter _

theorem corr_key (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂) {h : Nat}
    {st₁ st₂ : Array Nat × Array Node} (hinv : CanonInv temp₁ temp₂ roots₁ roots₂ h st₁ st₂)
    {t s : Nat} (hc : Corr temp₁ temp₂ roots₁ roots₂ t s) (ht : (nodeHeights temp₁)[t]! = h) :
    keyOf temp₁ st₁.1 t = keyOf temp₂ st₂.1 s := by
  obtain ⟨hhead, hsize, hk⟩ := corr_children h₁ h₂ hc
  have htlt := reach_lt h₁.cp h₁.inRange hc.1
  unfold keyOf
  simp only [Node.mk.injEq]
  refine ⟨hhead, Array.ext (by simp [hsize]) fun k hk₁ hk₂ => ?_⟩
  simp only [Array.size_map] at hk₁ hk₂
  simp only [Array.getElem_map]
  refine hinv.2.2.2 _ _ (hk k hk₁ hk₂) ?_
  have := child_height_lt temp₁ (nodeHeights temp₁) t _ (Array.getElem_mem hk₁)
  rw [← nodeHeights_spec h₁.cp t htlt, ht] at this
  exact this

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, H, d => by
    rw [List.nodup_cons] at d
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun x hx y hy =>
      H x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) d.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have := H b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    subst this
    exact d.1 hb

theorem bucket_perm
 (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) {h : Nat}
    {st₁ st₂ : Array Nat × Array Node} (hinv : CanonInv temp₁ temp₂ roots₁ roots₂ h st₁ st₂)
    {B₁ B₂ : Array Nat} (hB₁ : BucketAt temp₁ roots₁ h B₁) (hB₂ : BucketAt temp₂ roots₂ h B₂) :
    (B₂.toList.map (keyOf temp₂ st₂.1)).Perm (B₁.toList.map (keyOf temp₁ st₁.1)) := by
  classical
  let φ : Nat → Nat := fun t =>
    if hex : ∃ s, Corr temp₁ temp₂ roots₁ roots₂ t s then hex.choose else 0
  have hφ : ∀ t, Reach temp₁ roots₁ t → Corr temp₁ temp₂ roots₁ roots₂ t (φ t) := by
    intro t ht
    have hex := corr_total h₁ h₂ hroots ht
    simp only [φ, dite_eq_left hex]
    exact hex.choose_spec
  have hnd : (B₁.toList.map φ).Nodup := by
    refine nodup_map_on ?_ (bucket_nodup hB₁)
    intro a ha b hb hab
    have hca := hφ a ((mem_bucket h₁ hB₁ a).mp ha).1
    have hcb := hφ b ((mem_bucket h₁ hB₁ b).mp hb).1
    rw [hab] at hca
    exact corr_inj h₁ hca hcb
  have hperm : B₂.toList.Perm (B₁.toList.map φ) := by
    rw [List.perm_ext_iff_of_nodup (bucket_nodup hB₂) hnd]
    intro s
    constructor
    · intro hs
      obtain ⟨hreach₂, hh₂⟩ := (mem_bucket h₂ hB₂ s).mp hs
      obtain ⟨t, hct⟩ := corr_total h₂ h₁ hroots.symm hreach₂
      have hc := hct.symm
      have hht : (nodeHeights temp₁)[t]! = h := by rw [corr_height h₁ h₂ t s hc, hh₂]
      exact List.mem_map.mpr ⟨t, (mem_bucket h₁ hB₁ t).mpr ⟨hc.1, hht⟩,
        corr_func h₂ (hφ t hc.1) hc⟩
    · intro hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hreach, hh⟩ := (mem_bucket h₁ hB₁ t).mp ht
      have hc := hφ t hreach
      exact (mem_bucket h₂ hB₂ _).mpr ⟨hc.2.1, by rw [← corr_height h₁ h₂ t _ hc, hh]⟩
  have := hperm.map (keyOf temp₂ st₂.1)
  rw [List.map_map] at this
  refine this.trans (List.Perm.of_eq ?_)
  apply List.map_congr_left
  intro t ht
  obtain ⟨hreach, hh⟩ := (mem_bucket h₁ hB₁ t).mp ht
  exact (corr_key h₁ h₂ hinv (hφ t hreach) hh).symm

theorem sortedGroup_fst_lt {temp : Array Node} {roots : Array Nat} (hrun : Run temp roots)
    {h : Nat} {B : Array Nat} (hB : BucketAt temp roots h B) (canon : Array Nat)
    (hsize : canon.size = temp.size) :
    ∀ x ∈ sortedGroup temp canon B, x.1 < canon.size := by
  intro x hx
  have hm : x.1 ∈ B.toList :=
    (sortedGroup_fst_perm temp canon B).subset (List.mem_map_of_mem hx)
  rw [hsize]
  exact reach_lt hrun.cp hrun.inRange ((mem_bucket hrun hB _).mp hm).1

theorem mem_sortedGroup (temp : Array Node) {B : Array Nat} (canon : Array Nat) {t : Nat}
    (ht : t ∈ B.toList) :
    ∃ (i : Nat) (hi : i < (sortedGroup temp canon B).length),
      (sortedGroup temp canon B)[i] = (t, keyOf temp canon t) := by
  have hm : (t, keyOf temp canon t) ∈ sortedGroup temp canon B :=
    (sortedGroup_perm temp canon B).symm.subset
      (List.mem_map.mpr ⟨t, ht, rfl⟩)
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨i, hi, he⟩

/-- One height group: both inputs fail with the same error, or both succeed
and the canonical IDs agree up to height `h + 1`. -/
theorem bucket_step (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) {h : Nat}
    {B₁ B₂ : Array Nat} (hB₁ : BucketAt temp₁ roots₁ h B₁) (hB₂ : BucketAt temp₂ roots₂ h B₂)
    {st₁ st₂ : Array Nat × Array Node} (hinv : CanonInv temp₁ temp₂ roots₁ roots₂ h st₁ st₂) :
    (∃ e, placeBucket temp₁ st₁ B₁ = .error e ∧ placeBucket temp₂ st₂ B₂ = .error e) ∨
      ∃ st₁' st₂', placeBucket temp₁ st₁ B₁ = .ok st₁' ∧ placeBucket temp₂ st₂ B₂ = .ok st₂' ∧
        CanonInv temp₁ temp₂ roots₁ roots₂ (h + 1) st₁' st₂' := by
  have hnodes : (sortedGroup temp₁ st₁.1 B₁).map (·.2) = (sortedGroup temp₂ st₂.1 B₂).map (·.2) := by
    rw [sortedGroup_nodes, sortedGroup_nodes]
    exact keySort_eq_of_perm (bucket_perm h₁ h₂ hroots hinv hB₁ hB₂).symm
  rw [placeBucket_eq, placeBucket_eq, placeSorted_eq, placeSorted_eq, ← hnodes]
  by_cases hk : keysIncreasing none ((sortedGroup temp₁ st₁.1 B₁).map (·.2)) = true
  · right
    rw [ite_eq_left hk, ite_eq_left hk]
    refine ⟨_, _, rfl, rfl, ?_⟩
    obtain ⟨hout, hs₁, hs₂, hagree⟩ := hinv
    obtain ⟨canon₁, out₁⟩ := st₁
    obtain ⟨canon₂, out₂⟩ := st₂
    simp only at hout hs₁ hs₂ hagree hk hnodes ⊢
    subst hout
    have hnd := keysIncreasing_nodup hk
    have hnd₁ : ((sortedGroup temp₁ canon₁ B₁).map (·.1)).Nodup :=
      (sortedGroup_fst_perm temp₁ canon₁ B₁).nodup_iff.mpr (bucket_nodup hB₁)
    have hnd₂ : ((sortedGroup temp₂ canon₂ B₂).map (·.1)).Nodup :=
      (sortedGroup_fst_perm temp₂ canon₂ B₂).nodup_iff.mpr (bucket_nodup hB₂)
    obtain ⟨ho₁, hz₁, hu₁, hp₁⟩ := placeFold_spec _ canon₁ out₁ hnd₁
      (sortedGroup_fst_lt h₁ hB₁ canon₁ hs₁)
    obtain ⟨ho₂, hz₂, hu₂, hp₂⟩ := placeFold_spec _ canon₂ out₁ hnd₂
      (sortedGroup_fst_lt h₂ hB₂ canon₂ hs₂)
    refine ⟨by rw [ho₁, ho₂, hnodes], by rw [hz₁, hs₁], by rw [hz₂, hs₂], ?_⟩
    intro t s hc hlt
    have hhs : (nodeHeights temp₂)[s]! = (nodeHeights temp₁)[t]! :=
      (corr_height h₁ h₂ t s hc).symm
    by_cases hlow : (nodeHeights temp₁)[t]! < h
    · have ht : t ∉ (sortedGroup temp₁ canon₁ B₁).map (·.1) := by
        intro hm
        have := ((mem_bucket h₁ hB₁ t).mp
          ((sortedGroup_fst_perm temp₁ canon₁ B₁).subset hm)).2
        omega
      have hs : s ∉ (sortedGroup temp₂ canon₂ B₂).map (·.1) := by
        intro hm
        have := ((mem_bucket h₂ hB₂ s).mp
          ((sortedGroup_fst_perm temp₂ canon₂ B₂).subset hm)).2
        omega
      rw [hu₁ t ht, hu₂ s hs]
      exact hagree t s hc hlow
    · have hth : (nodeHeights temp₁)[t]! = h := by omega
      obtain ⟨i, hi, hgi⟩ := mem_sortedGroup temp₁ canon₁
        ((mem_bucket h₁ hB₁ t).mpr ⟨hc.1, hth⟩)
      obtain ⟨j, hj, hgj⟩ := mem_sortedGroup temp₂ canon₂
        ((mem_bucket h₂ hB₂ s).mpr ⟨hc.2.1, by rw [hhs, hth]⟩)
      have hkey := corr_key (st₁ := (canon₁, out₁)) (st₂ := (canon₂, out₁)) h₁ h₂
        ⟨rfl, hs₁, hs₂, hagree⟩ hc hth
      simp only at hkey
      have hij : i = j := by
        have hni : ((sortedGroup temp₁ canon₁ B₁).map (·.2))[i]'(by simpa using hi) =
            keyOf temp₁ canon₁ t := by simp [hgi]
        have hnj : ((sortedGroup temp₂ canon₂ B₂).map (·.2))[j]'(by simpa using hj) =
            keyOf temp₂ canon₂ s := by simp [hgj]
        have hj' : j < ((sortedGroup temp₁ canon₁ B₁).map (·.2)).length := by
          rw [hnodes]; simpa using hj
        have : ((sortedGroup temp₁ canon₁ B₁).map (·.2))[i]'(by simpa using hi) =
            ((sortedGroup temp₁ canon₁ B₁).map (·.2))[j]'hj' := by
          rw [hni, hkey, ← hnj]
          simp only [hnodes]
        exact (List.Nodup.getElem_inj hnd).mp this
      subst hij
      have e₁ := hp₁ i hi
      have e₂ := hp₂ i hj
      rw [hgi] at e₁
      rw [hgj] at e₂
      simp only at e₁ e₂
      rw [e₁, e₂]
  · left
    rw [ite_eq_right hk, ite_eq_right hk]
    exact ⟨_, rfl, rfl⟩

/-! ## All height groups -/

theorem foldlM_sim {σ₁ σ₂ ε : Type} (f₁ : σ₁ → Nat → Except ε σ₁) (f₂ : σ₂ → Nat → Except ε σ₂)
    (Inv : Nat → σ₁ → σ₂ → Prop) (bound : Nat)
    (hstep : ∀ h st₁ st₂, h < bound → Inv h st₁ st₂ →
      (∃ e, f₁ st₁ h = .error e ∧ f₂ st₂ h = .error e) ∨
        ∃ st₁' st₂', f₁ st₁ h = .ok st₁' ∧ f₂ st₂ h = .ok st₂' ∧ Inv (h + 1) st₁' st₂') :
    ∀ (k a : Nat) (st₁ : σ₁) (st₂ : σ₂), a + k ≤ bound → Inv a st₁ st₂ →
      (∃ e, (List.range' a k).foldlM f₁ st₁ = .error e ∧
          (List.range' a k).foldlM f₂ st₂ = .error e) ∨
        ∃ st₁' st₂', (List.range' a k).foldlM f₁ st₁ = .ok st₁' ∧
          (List.range' a k).foldlM f₂ st₂ = .ok st₂' ∧ Inv (a + k) st₁' st₂' := by
  intro k
  induction k with
  | zero =>
    intro a st₁ st₂ _ hinv
    exact Or.inr ⟨st₁, st₂, rfl, rfl, by simpa using hinv⟩
  | succ k ih =>
    intro a st₁ st₂ hle hinv
    rw [List.range'_succ, List.foldlM_cons, List.foldlM_cons]
    rcases hstep a st₁ st₂ (by omega) hinv with ⟨e, he₁, he₂⟩ | ⟨st₁', st₂', hs₁, hs₂, hinv'⟩
    · left
      rw [he₁, he₂]
      exact ⟨e, rfl, rfl⟩
    · rw [hs₁, hs₂]
      have := ih (a + 1) st₁' st₂' (by omega) hinv'
      rw [show a + 1 + k = a + (k + 1) by omega] at this
      exact this

theorem maxHeight_le (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) :
    maxHeight (reachMarks temp₁ roots₁) (nodeHeights temp₁) temp₁.size ≤
      maxHeight (reachMarks temp₂ roots₂) (nodeHeights temp₂) temp₂.size := by
  rcases (maxHeight_spec (reachMarks temp₁ roots₁) (nodeHeights temp₁) temp₁.size).2 with
    h0 | ⟨t, ht, hr, he⟩
  · rw [h0]; exact Nat.zero_le _
  · have hreach := (reachMarks_spec h₁.cp h₁.inRange t ht).mp hr
    obtain ⟨s, hc⟩ := corr_total h₁ h₂ hroots hreach
    have hs := reach_lt h₂.cp h₂.inRange hc.2.1
    have hs' := (reachMarks_spec h₂.cp h₂.inRange s hs).mpr hc.2.1
    rw [← he, corr_height h₁ h₂ t s hc]
    exact (maxHeight_spec _ _ _).1 s hs hs'

/-- `canonicalize` on an input that passes its checks. -/
theorem canonicalize_eq {temp : Array Node} {roots : Array Nat} (hrun : Run temp roots) :
    canonicalize temp roots =
      ((List.range (maxHeight (reachMarks temp roots) (nodeHeights temp) temp.size + 1)).foldlM
        (fun st h => placeBucket temp st
          (heightBuckets (reachMarks temp roots) (nodeHeights temp)
            (maxHeight (reachMarks temp roots) (nodeHeights temp) temp.size) temp.size)[h]!)
        (Array.replicate temp.size 0, #[])) >>= fun st =>
          pure ((⟨st.2⟩ : Dag), roots.map (st.1[·]!)) := by
  have hall : roots.all (· < temp.size) = true := by
    rw [Array.all_eq_true]
    intro i hi
    simpa using hrun.inRange _ (Array.getElem_mem hi)
  unfold canonicalize
  simp only [hrun.precede, hall, ↓reduceIte]
  rfl

/-- **ID determinism of `canonicalize`.** Two inputs that pass the
interner's checks (children precede parents, arity, roots in range) and are
hash-consed, whose roots denote the same terms, canonicalize to the same DAG
and root IDs: the canonical IDs depend only on the root terms, not on the
temporary IDs or on unreachable nodes. -/
theorem canonicalize_det (h₁ : Run temp₁ roots₁) (h₂ : Run temp₂ roots₂)
    (hroots : roots₁.map (termOf temp₁) = roots₂.map (termOf temp₂)) :
    canonicalize temp₁ roots₁ = canonicalize temp₂ roots₂ := by
  have hM : maxHeight (reachMarks temp₁ roots₁) (nodeHeights temp₁) temp₁.size =
      maxHeight (reachMarks temp₂ roots₂) (nodeHeights temp₂) temp₂.size :=
    Nat.le_antisymm (maxHeight_le h₁ h₂ hroots) (maxHeight_le h₂ h₁ hroots.symm)
  have hle₁ := (maxHeight_spec (reachMarks temp₁ roots₁) (nodeHeights temp₁) temp₁.size).1
  have hle₂ := (maxHeight_spec (reachMarks temp₂ roots₂) (nodeHeights temp₂) temp₂.size).1
  rw [canonicalize_eq h₁, canonicalize_eq h₂, ← hM]
  rw [← hM] at hle₂
  generalize maxHeight (reachMarks temp₁ roots₁) (nodeHeights temp₁) temp₁.size = M at hle₁ hle₂ ⊢
  rw [List.range_eq_range']
  have hstep : ∀ h st₁ st₂, h < M + 1 → CanonInv temp₁ temp₂ roots₁ roots₂ h st₁ st₂ →
      (∃ e, placeBucket temp₁ st₁ (heightBuckets (reachMarks temp₁ roots₁)
            (nodeHeights temp₁) M temp₁.size)[h]! = .error e ∧
          placeBucket temp₂ st₂ (heightBuckets (reachMarks temp₂ roots₂)
            (nodeHeights temp₂) M temp₂.size)[h]! = .error e) ∨
        ∃ st₁' st₂', placeBucket temp₁ st₁ (heightBuckets (reachMarks temp₁ roots₁)
            (nodeHeights temp₁) M temp₁.size)[h]! = .ok st₁' ∧
          placeBucket temp₂ st₂ (heightBuckets (reachMarks temp₂ roots₂)
            (nodeHeights temp₂) M temp₂.size)[h]! = .ok st₂' ∧
          CanonInv temp₁ temp₂ roots₁ roots₂ (h + 1) st₁' st₂' := by
    intro h st₁ st₂ hh hinv
    exact bucket_step h₁ h₂ hroots
      ((heightBuckets_spec _ _ M temp₁.size hle₁).2 h (by omega))
      ((heightBuckets_spec _ _ M temp₂.size hle₂).2 h (by omega)) hinv
  have hinit : CanonInv temp₁ temp₂ roots₁ roots₂ 0 (Array.replicate temp₁.size 0, #[])
      (Array.replicate temp₂.size 0, #[]) :=
    ⟨rfl, by simp, by simp, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases foldlM_sim _ _ _ (M + 1) hstep (M + 1) 0 _ _ (by omega) hinit with
    ⟨e, he₁, he₂⟩ | ⟨st₁, st₂, hs₁, hs₂, hinv⟩
  · rw [he₁, he₂]
    rfl
  · rw [hs₁, hs₂]
    obtain ⟨hout, _, _, hagree⟩ := hinv
    have hsz : roots₁.size = roots₂.size := by simpa using congrArg Array.size hroots
    have hroots' : roots₁.map (st₁.1[·]!) = roots₂.map (st₂.1[·]!) := by
      apply Array.ext (by simp [hsz])
      intro i hi₁ hi₂
      simp only [Array.size_map] at hi₁ hi₂
      simp only [Array.getElem_map]
      have hterm := congrArg (·[i]?) hroots
      simp only [Array.getElem?_map, Array.getElem?_eq_getElem hi₁,
        Array.getElem?_eq_getElem hi₂, Option.map_some, Option.some.injEq] at hterm
      have hc : Corr temp₁ temp₂ roots₁ roots₂ roots₁[i] roots₂[i] :=
        ⟨.root (Array.getElem_mem hi₁), .root (Array.getElem_mem hi₂), hterm⟩
      have hlt := reach_lt h₁.cp h₁.inRange hc.1
      have hmark := (reachMarks_spec h₁.cp h₁.inRange _ hlt).mpr hc.1
      exact hagree _ _ hc (by have := hle₁ _ hlt hmark; omega)
    change (pure ((⟨st₁.2⟩ : Dag), roots₁.map (st₁.1[·]!)) : Except SharingError _) =
      pure ((⟨st₂.2⟩ : Dag), roots₂.map (st₂.1[·]!))
    rw [hout, hroots']

end Canon

end Ix.Sharing.Verify.SharingExact
