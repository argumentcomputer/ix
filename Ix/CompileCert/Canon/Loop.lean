import Ix.CompileCert.Canon.Sort

/-!
# M7 L1, the loops of Pass 1's code

Pass 1's block driver, nested data, evaporation, permutation and name map are written with `for`
loops (`forIn`) over arrays and lists, in `Id` or in `Except String`. Two facts reduce them to what
the theorems need:

* in `Id`, a loop whose body always continues is the left fold of the body's values
  (`forIn_id_list`, `forIn_id_array`);
* in `Except`, a property of the loop state that every successful step extends (and every step
  continues) holds of the result (`forIn_except_list`, `forIn_except_array`); for the loops that
  push one element per input element, the result is related pointwise to the input
  (`forIn_push_array`, `Pointwise`).
-/

namespace Ix.CompileCert.Canon

/-- A `for` loop in `Id` whose body always continues is a left fold of the body's values. -/
theorem forIn_id_list {α β : Type} (body : α → β → Id (ForInStep β))
    (h : ∀ x r, body x r = .yield (body x r).value) :
    ∀ (l : List α) (init : β), forIn (m := Id) l init body = l.foldl (fun r x => (body x r).value) init
  | [], _ => rfl
  | x :: l, init => by
    rw [List.forIn_cons, List.foldl_cons]
    have hx := h x init
    revert hx
    generalize body x init = s
    intro hx
    cases s with
    | done v => cases hx
    | yield v => exact forIn_id_list body h l v

theorem forIn_id_array {α β : Type} (body : α → β → Id (ForInStep β))
    (h : ∀ x r, body x r = .yield (body x r).value) (xs : Array α) (init : β) :
    forIn (m := Id) xs init body = xs.foldl (fun r x => (body x r).value) init := by
  rw [← Array.forIn_toList, forIn_id_list body h, Array.foldl_toList]

theorem except_pure_ok {α ε : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b := by
  simp only [pure, Except.pure, Except.ok.injEq] at h; exact h

/-- A property every successful, continuing step extends holds of the loop's result. -/
theorem forIn_except_list {α β ε : Type} (body : α → β → Except ε (ForInStep β))
    (P : List α → β → Prop)
    (hstep : ∀ pre x r s, P pre r → body x r = .ok s → ∃ r', s = .yield r' ∧ P (pre ++ [x]) r') :
    ∀ (l pre : List α) (r out : β), P pre r → forIn l r body = .ok out → P (pre ++ l) out
  | [], pre, r, out, hp, h => by
    rw [List.forIn_nil] at h
    rw [List.append_nil, ← except_pure_ok h]; exact hp
  | x :: l, pre, r, out, hp, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := except_bind_ok.1 h
    obtain ⟨r', rfl, hp'⟩ := hstep pre x r s hp hs
    have h' : forIn l r' body = .ok out := h
    have := forIn_except_list body P hstep l (pre ++ [x]) r' out hp' h'
    rwa [List.append_assoc, List.singleton_append] at this

theorem forIn_except_array {α β ε : Type} (body : α → β → Except ε (ForInStep β))
    (P : List α → β → Prop)
    (hstep : ∀ pre x r s, P pre r → body x r = .ok s → ∃ r', s = .yield r' ∧ P (pre ++ [x]) r')
    (xs : Array α) {init out : β} (h0 : P [] init) (h : forIn xs init body = .ok out) :
    P xs.toList out := by
  rw [← Array.forIn_toList] at h
  have := forIn_except_list body P hstep xs.toList [] init out h0 h
  rwa [List.nil_append] at this

/-- Two lists of the same length, related position by position. -/
def Pointwise {α β : Type} (Q : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  xs.length = ys.length ∧ ∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → Q x y

theorem Pointwise.nil {α β : Type} (Q : α → β → Prop) : Pointwise Q [] [] :=
  ⟨rfl, fun i x y hx _ => by simp at hx⟩

theorem Pointwise.snoc {α β : Type} {Q : α → β → Prop} {xs : List α} {ys : List β} {x : α} {y : β}
    (h : Pointwise Q xs ys) (hq : Q x y) : Pointwise Q (xs ++ [x]) (ys ++ [y]) := by
  refine ⟨by simp [h.1], fun i a b ha hb => ?_⟩
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi] at ha
    rw [List.getElem?_append_left (h.1 ▸ hi)] at hb
    exact h.2 i a b ha hb
  · have hi' : ys.length ≤ i := h.1 ▸ Nat.le_of_not_lt hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at ha
    rw [List.getElem?_append_right hi'] at hb
    rw [← h.1] at hb
    cases hk : i - xs.length with
    | zero =>
      rw [hk] at ha hb
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha hb; exact hq
    | succ k =>
      rw [hk] at ha; simp at ha

/-- A loop that pushes one element per input element: the result is related to the input
pointwise. -/
theorem forIn_push_array {α γ ε : Type} (xs : Array α)
    (body : α → Array γ → Except ε (ForInStep (Array γ))) (Q : α → γ → Prop)
    (hstep : ∀ x r s, body x r = .ok s → ∃ y, s = .yield (r.push y) ∧ Q x y)
    {out : Array γ} (h : forIn xs #[] body = .ok out) : Pointwise Q xs.toList out.toList := by
  refine forIn_except_array body (fun pre r => Pointwise Q pre r.toList) ?_ xs (Pointwise.nil Q) h
  intro pre x r s hp hs
  obtain ⟨y, rfl, hq⟩ := hstep x r s hs
  refine ⟨r.push y, rfl, ?_⟩
  rw [Array.toList_push]
  exact hp.snoc hq

theorem Pointwise.length {α β : Type} {Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pointwise Q xs ys) : xs.length = ys.length := h.1

/-- Every element of the result is related to the input element at its position. -/
theorem Pointwise.get {α β : Type} {Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pointwise Q xs ys) {i : Nat} {y : β} (hy : ys[i]? = some y) : ∃ x, xs[i]? = some x ∧ Q x y := by
  have hi : i < ys.length := by
    rcases Nat.lt_or_ge i ys.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at hy; cases hy
  have hi' : i < xs.length := h.1 ▸ hi
  exact ⟨xs[i], List.getElem?_eq_getElem hi', h.2 i _ y (List.getElem?_eq_getElem hi') hy⟩

theorem Pointwise.get' {α β : Type} {Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : Pointwise Q xs ys) {i : Nat} {x : α} (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ Q x y := by
  have hi : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at hx; cases hx
  have hi' : i < ys.length := h.1 ▸ hi
  exact ⟨ys[i], List.getElem?_eq_getElem hi', h.2 i x _ hx (List.getElem?_eq_getElem hi')⟩

end Ix.CompileCert.Canon

namespace Ix.CompileCert.Canon

/-- `forIn_except_list`, the step also knowing that its element belongs to a list `L` containing
the loop's list. -/
theorem forIn_except_list_mem {α β ε : Type} (L : List α) (body : α → β → Except ε (ForInStep β))
    (P : List α → β → Prop)
    (hstep : ∀ pre x r s, x ∈ L → P pre r → body x r = .ok s → ∃ r', s = .yield r' ∧ P (pre ++ [x]) r') :
    ∀ (l pre : List α) (r out : β), (∀ x ∈ l, x ∈ L) → P pre r → forIn l r body = .ok out →
      P (pre ++ l) out
  | [], pre, r, out, _, hp, h => by
    rw [List.forIn_nil] at h
    rw [List.append_nil, ← except_pure_ok h]; exact hp
  | x :: l, pre, r, out, hL, hp, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := except_bind_ok.1 h
    obtain ⟨r', rfl, hp'⟩ := hstep pre x r s (hL x (List.mem_cons_self ..)) hp hs
    have h' : forIn l r' body = .ok out := h
    have := forIn_except_list_mem L body P hstep l (pre ++ [x]) r' out
      (fun y hy => hL y (List.mem_cons_of_mem _ hy)) hp' h'
    rwa [List.append_assoc, List.singleton_append] at this

theorem forIn_except_array_mem {α β ε : Type} (body : α → β → Except ε (ForInStep β))
    (P : List α → β → Prop) (xs : Array α)
    (hstep : ∀ pre x r s, x ∈ xs.toList → P pre r → body x r = .ok s →
      ∃ r', s = .yield r' ∧ P (pre ++ [x]) r')
    {init out : β} (h0 : P [] init) (h : forIn xs init body = .ok out) : P xs.toList out := by
  rw [← Array.forIn_toList] at h
  have := forIn_except_list_mem xs.toList body P hstep xs.toList [] init out (fun _ h => h) h0 h
  rwa [List.nil_append] at this

end Ix.CompileCert.Canon
