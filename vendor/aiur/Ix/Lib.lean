module
public import Std.Data.HashMap.Basic
public import Std.Data.HashMap.Lemmas

/-!
Generic library lemmas not tied to any project-specific type. Grows as new
utilities accumulate.
-/

public section
@[expose] section

/-! ### `List.mapM` / `Array.mapM` progress in `Except` -/

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

/-! ### `List.foldlM` progress + invariant in `Except` -/

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

/-! ### `Array` sizeOf -/

/-- Every non-empty `Array` has `sizeOf ≥ 2` — used as a fallback in
`termination_by` proofs involving nested array arguments. -/
theorem Array.two_le_sizeOf {α : Type} [SizeOf α] (a : Array α) :
    2 ≤ sizeOf a := by
  rcases a with ⟨l⟩
  show 2 ≤ 1 + sizeOf l
  cases l <;> simp +arith

/-! ### `Array.foldlM` / `List.foldlM` `.attach` bridge -/

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

/-- `Array.foldlM` over `.attach` equals `List.foldlM` on the underlying list
(after erasing the subtype projection). -/
theorem Array.foldlM_attach_to_List_foldlM
    {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : Array α) (step : β → α → m β) (init : β) :
    xs.attach.foldlM (init := init) (fun acc ⟨x, _⟩ => step acc x) =
    xs.toList.foldlM step init := by
  rw [← Array.foldlM_toList, Array.toList_attach]
  exact List.foldlM_attachWith_eq step xs.toList _ init

/-! ### `Std.HashMap` fold-insert lookup -/

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
end
