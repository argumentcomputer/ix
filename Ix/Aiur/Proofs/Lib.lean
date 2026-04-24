module
public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.Lemmas
public import Ix.IndexMap

/-!
Generic library lemmas not tied to any project-specific type. Grows as new
utilities accumulate.
-/

public section
@[expose] section

/-! ## `List` -/

/-- In the `Except` monad, `List.mapM` succeeds whenever every element has a
successful image under `f`. Proven by structural induction on the list. -/
theorem List.mapM_except_ok {α β ε : Type}
    {f : α → Except ε β} : ∀ {l : List α},
    (∀ a ∈ l, ∃ b, f a = .ok b) →
    ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      obtain ⟨y, hy⟩ := h x (List.mem_cons_self)
      have hxs : ∀ a ∈ xs, ∃ b, f a = .ok b :=
        fun a ha => h a (List.mem_cons_of_mem _ ha)
      obtain ⟨ys, hys⟩ := @List.mapM_except_ok _ _ _ f xs hxs
      refine ⟨y :: ys, ?_⟩
      simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]

/-- If every step of a `List.foldlM` in `Except` succeeds (from any
accumulator), the whole fold succeeds. -/
theorem List.foldlM_except_ok' {α β ε : Type}
    {f : β → α → Except ε β} :
    ∀ (xs : List α) (init : β),
      (∀ acc x, x ∈ xs → ∃ acc', f acc x = .ok acc') →
      ∃ res, xs.foldlM f init = .ok res
  | [], init, _ => ⟨init, rfl⟩
  | x :: xs, init, h => by
    have ⟨acc', hx⟩ := h init x (List.Mem.head _)
    simp [List.foldlM_cons, hx, bind, Except.bind]
    exact List.foldlM_except_ok' xs acc' (fun acc y hy =>
      h acc y (List.Mem.tail _ hy))

/-- Invariant-preservation for `List.foldlM` in `Except`. If `P init` holds
and every `.ok` step preserves `P`, then `P` holds on the final result. -/
theorem List.foldlM_except_invariant
    {β ε α : Type} {P : β → Prop} {f : β → α → Except ε β} :
    ∀ (xs : List α) (init : β) (result : β),
      P init →
      (∀ acc x acc', x ∈ xs → f acc x = .ok acc' → P acc → P acc') →
      xs.foldlM f init = .ok result →
      P result
  | [], _, result, hP, _, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure] at hfold
    cases hfold; exact hP
  | x :: rest, _, result, hP, hstep, hfold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    · rename_i acc' hx
      have hP' : P acc' := hstep _ x acc' (List.Mem.head _) hx hP
      exact List.foldlM_except_invariant rest acc' result hP'
        (fun acc y acc'' hy => hstep acc y acc'' (List.Mem.tail _ hy)) hfold

/-- Monadic-to-pure bridge for `List.foldlM`: if every step of the monadic
fold returns `.ok (g acc x)`, the whole monadic fold equals `.ok (xs.foldl g init)`. -/
theorem List.foldlM_eq_foldl_of_pure {α β ε : Type}
    {f : β → α → Except ε β} {g : β → α → β}
    (hfg : ∀ acc x, f acc x = .ok (g acc x)) :
    ∀ (xs : List α) (init : β), xs.foldlM f init = .ok (xs.foldl g init)
  | [], _ => rfl
  | x :: rest, init => by
    simp only [List.foldlM_cons, List.foldl_cons, bind, Except.bind, hfg]
    exact List.foldlM_eq_foldl_of_pure hfg rest (g init x)

/-- Pointwise body-congruence for `List.foldlM`. -/
theorem List.foldlM_congr_body
    {α β : Type _} {m : Type _ → Type _} [Monad m]
    {f g : β → α → m β} (h : ∀ acc x, f acc x = g acc x) :
    ∀ (xs : List α) (init : β), xs.foldlM f init = xs.foldlM g init
  | [], _ => rfl
  | x :: xs, init => by
    simp only [List.foldlM_cons, h init x]
    congr 1
    funext b
    exact List.foldlM_congr_body h xs b

/-- `List.foldlM` over `attachWith` (with any predicate/proof) equals the
plain `foldlM` on the list. -/
theorem List.foldlM_attachWith_eq
    {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    {P : α → Prop} (step : β → α → m β) :
    ∀ (l : List α) (H : ∀ x ∈ l, P x) (init : β),
      (l.attachWith P H).foldlM (init := init) (fun acc x => step acc x.1) =
      l.foldlM step init
  | [], _, _ => by simp
  | x :: xs, H, init => by
    simp only [List.attachWith_cons, List.foldlM_cons]
    refine congrArg _ ?_
    funext b
    exact List.foldlM_attachWith_eq step xs (fun y hy => H y (List.mem_cons_of_mem _ hy)) b

/-- Per-element success reflection. If a `foldlM` over `xs` in `Except`
succeeds with final state `result`, then every element `x ∈ xs` was
processed by `f` at some intermediate state `acc` with result `acc'`.
Provides the "witness per element" view of a succeeded fold. -/
theorem List.foldlM_except_witnesses
    {α β ε : Type} {f : β → α → Except ε β} :
    ∀ (xs : List α) (init result : β),
      xs.foldlM f init = .ok result →
      ∀ x ∈ xs, ∃ acc acc', f acc x = .ok acc'
  | [], _, _, hfold, x, hx => by cases hx
  | hd :: tl, init, result, hfold, x, hx => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · cases hfold
    · rename_i acc' hstep
      cases hx with
      | head _ => exact ⟨init, acc', hstep⟩
      | tail _ hx_tl =>
        exact List.foldlM_except_witnesses tl acc' result hfold x hx_tl

/-- Indexed-witness variant: for every prefix `processed ++ (x :: rest) = xs`,
there is an intermediate accumulator from which `x` is processed successfully.
Useful when the witness for `x`'s success must reference the context
(all elements before it). -/
theorem List.foldlM_except_witness_with_context
    {α β ε : Type} {f : β → α → Except ε β} :
    ∀ (xs : List α) (init result : β),
      xs.foldlM f init = .ok result →
      ∀ (processed : List α) (x : α) (rest : List α),
        xs = processed ++ x :: rest →
        ∃ acc_prev acc_after,
          processed.foldlM f init = .ok acc_prev ∧
          f acc_prev x = .ok acc_after ∧
          rest.foldlM f acc_after = .ok result
  | [], _, _, _, processed, _, _, hsplit => by
    exfalso
    cases processed with
    | nil => cases hsplit
    | cons _ _ => cases hsplit
  | hd :: tl, init, result, hfold, processed, x, rest, hsplit => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · cases hfold
    rename_i acc' hstep
    match processed, hsplit with
    | [], heq =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨hhd, htl⟩ := heq
      subst hhd; subst htl
      refine ⟨init, acc', ?_, hstep, hfold⟩
      simp [List.foldlM_nil, pure, Except.pure]
    | phd :: ptl, heq =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨hhd, htl⟩ := heq
      subst hhd
      have ih := List.foldlM_except_witness_with_context tl acc' result hfold ptl x rest htl
      obtain ⟨acc_prev, acc_after, hp, hf, hr⟩ := ih
      refine ⟨acc_prev, acc_after, ?_, hf, hr⟩
      simp only [List.foldlM_cons, bind, Except.bind, hstep, hp]

/-! ## `Array` -/

/-- Array-level companion of `List.mapM_except_ok`. -/
theorem Array.mapM_except_ok {α β ε : Type}
    {f : α → Except ε β} {a : Array α}
    (h : ∀ x ∈ a, ∃ y, f x = .ok y) :
    ∃ ys : List β, a.mapM f = .ok ys.toArray := by
  have hlist : ∀ x ∈ a.toList, ∃ y, f x = .ok y :=
    fun x hx => h x (Array.mem_toList_iff.mp hx)
  obtain ⟨ys, hys⟩ := List.mapM_except_ok hlist
  refine ⟨ys, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hys]
  rfl

/-- Every non-empty `Array` has `sizeOf ≥ 2` — used as a fallback in
`termination_by` proofs involving nested array arguments. -/
theorem Array.two_le_sizeOf {α : Type} [SizeOf α] (a : Array α) :
    2 ≤ sizeOf a := by
  rcases a with ⟨l⟩
  show 2 ≤ 1 + sizeOf l
  cases l <;> simp +arith

/-- `Array.foldlM` over `.attach` equals `List.foldlM` on the underlying list
(after erasing the subtype projection). -/
theorem Array.foldlM_attach_to_List_foldlM
    {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : Array α) (step : β → α → m β) (init : β) :
    xs.attach.foldlM (init := init) (fun acc ⟨x, _⟩ => step acc x) =
    xs.toList.foldlM step init := by
  rw [← Array.foldlM_toList, Array.toList_attach]
  exact List.foldlM_attachWith_eq step xs.toList _ init

/-! ## `Std.HashMap` -/

/-- Generalized: lookup in a hashmap built by repeatedly inserting key/value
pairs from a list with pairwise-distinct keys factors through `find?` or falls
back to the accumulator. -/
theorem Std.HashMap.getElem?_foldl_insert_of_pairwise_distinct_aux
    {α β : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] :
    ∀ (l : List (α × β)) (name : α) (acc : Std.HashMap α β),
      l.Pairwise (fun a b => (a.1 == b.1) = false) →
      (l.foldl (fun acc (p : α × β) => acc.insert p.1 p.2) acc)[name]?
        = ((l.find? (·.1 == name)).map Prod.snd).or acc[name]?
  | [], _, _, _ => by simp
  | hd :: tl, name, acc, hdist => by
    rw [List.pairwise_cons] at hdist
    obtain ⟨hhead, htail⟩ := hdist
    simp only [List.foldl_cons]
    have ih := getElem?_foldl_insert_of_pairwise_distinct_aux
      tl name (acc.insert hd.1 hd.2) htail
    rw [ih]
    by_cases hhd : (hd.1 == name) = true
    · have htl_none : tl.find? (fun x => x.1 == name) = none := by
        rw [List.find?_eq_none]
        intro p hp hpname
        have hne : (hd.1 == p.1) = false := hhead p hp
        have htrans : (hd.1 == p.1) = true :=
          BEq.trans hhd (BEq.symm hpname)
        rw [htrans] at hne
        exact Bool.false_ne_true hne.symm
      rw [htl_none]
      have hfind_cons :
          (hd :: tl).find? (fun x => x.1 == name) = some hd :=
        List.find?_cons_of_pos (l := tl) (a := hd)
          (p := fun x => x.1 == name) hhd
      rw [hfind_cons]
      simp only [Option.map_none, Option.or, Option.map_some,
                 Std.HashMap.getElem?_insert, hhd, if_true]
    · have hhd_ff : (hd.1 == name) = false := Bool.not_eq_true _ |>.mp hhd
      have hfind_cons : (hd :: tl).find? (fun x => x.1 == name)
          = tl.find? (fun x => x.1 == name) :=
        List.find?_cons_of_neg (l := tl) (a := hd)
          (p := fun x => x.1 == name) (by simp [hhd_ff])
      rw [hfind_cons]
      have hins : (acc.insert hd.1 hd.2)[name]? = acc[name]? := by
        simp [Std.HashMap.getElem?_insert, hhd_ff]
      rw [hins]

/-- Lookup in a hashmap built by repeatedly inserting key/value pairs from a
list with pairwise-distinct keys coincides with the value that `List.find?`
associates with the key. -/
theorem Std.HashMap.getElem?_foldl_insert_of_pairwise_distinct
    {α β : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (l : List (α × β)) (name : α)
    (hdist : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (l.foldl (fun acc (p : α × β) => acc.insert p.1 p.2)
      (∅ : Std.HashMap α β))[name]?
      = (l.find? (·.1 == name)).map Prod.snd := by
  rw [getElem?_foldl_insert_of_pairwise_distinct_aux l name ∅ hdist]
  simp

end -- @[expose] section

namespace IndexMap

/-! ## Generic `foldlM` key-preservation

`List.foldlM` / `IndexMap.foldlM` over an insert-only step function preserves
keys modulo the pairs seen. The three lemmas below package this as
insert-only key-set invariants for folds that build up an `IndexMap`. -/

section FoldlM

variable {α : Type _} {β γ : Type _} [BEq α] [Hashable α]

/-- `List.foldlM` over an `insert`-only step preserves keys modulo pairs seen. -/
theorem List.foldlM_insertKey_iff
    {ε : Type}
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (pairs : List (α × β)) :
    ∀ (init : IndexMap α γ) (result : IndexMap α γ),
    _root_.List.foldlM step init pairs = .ok result →
    (result.containsKey g ↔
     init.containsKey g ∨ ∃ p ∈ pairs, (p.1 == g) = true) := by
  induction pairs with
  | nil =>
    intro init result h
    simp only [_root_.List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons hd tl ih =>
    intro init result h
    simp only [_root_.List.foldlM_cons, bind, Except.bind] at h
    rcases hok : step init hd with _ | acc'
    · rw [hok] at h; simp at h
    · rw [hok] at h
      have hihv := ih acc' result h
      have hkeys := hstep init hd acc' hok g
      constructor
      · intro hres
        rcases hihv.mp hres with h1 | ⟨p, hp, hpe⟩
        · rcases hkeys.mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨hd, _root_.List.mem_cons_self, h2⟩
        · exact Or.inr ⟨p, _root_.List.mem_cons_of_mem _ hp, hpe⟩
      · rintro (h1 | ⟨p, hp, hpe⟩)
        · exact hihv.mpr (Or.inl (hkeys.mpr (Or.inl h1)))
        · rcases _root_.List.mem_cons.mp hp with rfl | htl'
          · exact hihv.mpr (Or.inl (hkeys.mpr (Or.inr hpe)))
          · exact hihv.mpr (Or.inr ⟨p, htl', hpe⟩)

variable [EquivBEq α] [LawfulHashable α]

/-- Specialisation to `init := default`. -/
theorem List.foldlM_insertKey_default_iff
    {ε : Type}
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (pairs : List (α × β)) (result : IndexMap α γ)
    (h : _root_.List.foldlM step default pairs = .ok result) :
    result.containsKey g ↔ ∃ p ∈ pairs, (p.1 == g) = true := by
  have := List.foldlM_insertKey_iff step hstep g pairs default result h
  rw [this]; simp [IndexMap.containsKey_default]

/-- Lift `IndexMap.foldlM` (via its `.pairs : Array`) to `List.foldlM`. -/
theorem indexMap_foldlM_eq_list_foldlM.{ua, ub, us, ue}
    {α : Type ua} {β : Type ub} {State : Type us} {Err : Type ue}
    [BEq α] [Hashable α]
    (m : IndexMap α β) (step : State → α × β → Except Err State) (init : State) :
    m.foldlM (init := init) step =
    _root_.List.foldlM step init m.pairs.toList := by
  unfold IndexMap.foldlM
  rw [← Array.foldlM_toList]

/-- IndexMap-form of `List.foldlM_insertKey_default_iff`. -/
theorem indexMap_foldlM_insertKey_default_iff
    {ε : Type}
    (m : IndexMap α β)
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (result : IndexMap α γ)
    (h : m.foldlM (init := default) step = .ok result) :
    result.containsKey g ↔ ∃ p ∈ m.pairs.toList, (p.1 == g) = true := by
  have hlist : _root_.List.foldlM step default m.pairs.toList = .ok result := by
    have := indexMap_foldlM_eq_list_foldlM (State := IndexMap α γ) (Err := ε) m step default
    rw [this] at h; exact h
  exact List.foldlM_insertKey_default_iff step hstep g m.pairs.toList result hlist

end FoldlM

end IndexMap

namespace IndexMap

/-- Within `m.pairs.toList`, any two pairs with beq-equal keys are
identical. -/
theorem pairs_key_unique
    {α : Type _} {β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) {p₁ p₂ : α × β}
    (h₁ : p₁ ∈ m.pairs.toList) (h₂ : p₂ ∈ m.pairs.toList)
    (hkey : (p₁.1 == p₂.1) = true) : p₁ = p₂ := by
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem h₂
  rw [Array.length_toList] at hi hj
  have hgi : m.pairs[i]'hi = p₁ := by rw [← hi_eq, Array.getElem_toList]
  have hgj : m.pairs[j]'hj = p₂ := by rw [← hj_eq, Array.getElem_toList]
  have hpii := m.pairsIndexed i hi
  have hpij := m.pairsIndexed j hj
  rw [hgi] at hpii
  rw [hgj] at hpij
  have hcong : m.indices[p₁.1]? = m.indices[p₂.1]? :=
    Std.HashMap.getElem?_congr hkey
  rw [hpii, hpij] at hcong
  simp only [Option.some.injEq] at hcong
  subst hcong
  rw [hgi] at hgj; exact hgj

end IndexMap

end
