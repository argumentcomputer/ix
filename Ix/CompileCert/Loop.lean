import Batteries.Data.List.Basic

/-! # Loops: the shared lemmas

The compiler, the reader and Source mode write their passes with `for`
loops (`forIn`) over arrays and lists, in `Id` or in `Except`. The proofs
reduce them with a few generic facts, collected here once (CS-01's
`Canon/Loop`, merged with R12's loop lemmas):

* in `Id`, a loop whose body always continues is the left fold of the
  body's values (`forIn_id_list`, `forIn_id_array`);
* in `Id`, a loop over an early exit and an array, each step of which
  either pushes the element's value or exits with a value a predicate
  describes, either exits with such a value or pushes every element's value
  (`forIn_exit`, `exit_of_fst`, `pushed_of_fst`, `forIn_all_some`,
  `no_exit`);
* in `Except`, an invariant of the processed prefix that every successful
  step extends (and every step continues) holds of the result
  (`forIn_inv`, `forIn_inv_array`); a loop that pushes one element per
  input element relates its result to its input position by position
  (`forIn_push_array`); `List.mapM` relates its result likewise
  (`mapM_forall₂`).

The proofs that use them take the inline step from the hypothesis rather
than restating the loop by `rfl`: a restated `return`-in-`for` loop does not
unify with the do-elaborator's (its `Option` matchers are core's shared
ones). -/

namespace Ix.CompileCert.Loop

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem except_pure_ok {ε α : Type} {a b : α} (h : (pure a : Except ε α) = .ok b) : a = b := by
  simp only [pure, Except.pure, Except.ok.injEq] at h; exact h

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem idPure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-! ## Loops in `Id` -/

/-- A `for` loop in `Id` whose body always continues is a left fold of the
body's values. -/
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

/-- A loop whose state is an early exit and an array, each step of which
either pushes the element's value (`H x = some b`) or exits with a value
`R` describes (`H x = none`), either exits with such a value or pushes every
element's value. -/
theorem forIn_exit {α β ρ : Type} (R : ρ → Prop) (H : α → Option β)
    (f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β)))
    (step : ∀ x p, (∀ b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) ∧
      (H x = none → ∃ r s, f x p = ForInStep.done (some r, s) ∧ R r)) :
    ∀ (l : List α) (acc : Array β),
      (∃ r, (forIn (m := Id) l (none, acc) f).1 = some r ∧ R r) ∨
      ((forIn (m := Id) l (none, acc) f).1 = none ∧ ∃ bs, List.Forall₂ (fun x b => H x = some b) l bs ∧
        (forIn (m := Id) l (none, acc) f).2 = acc ++ bs.toArray) := by
  intro l
  induction l with
  | nil => intro acc; exact .inr ⟨rfl, [], .nil, by show acc = acc ++ #[]; simp⟩
  | cons x l ih =>
    intro acc
    rw [List.forIn_cons]
    cases value : H x with
    | some b =>
      rw [(step x (none, acc)).1 b value]
      rcases ih (acc.push b) with ⟨r, exited, holds⟩ | ⟨done, bs, values, pushed⟩
      · exact .inl ⟨r, exited, holds⟩
      · refine .inr ⟨done, b :: bs, .cons value values, ?_⟩
        show (forIn (m := Id) l (none, acc.push b) f).2 = _
        rw [pushed]
        simp
    | none =>
      obtain ⟨r, s, exits, holds⟩ := (step x (none, acc)).2 value
      rw [exits]
      exact .inl ⟨r, rfl, holds⟩

theorem forIn_exit_array {α β ρ : Type} (R : ρ → Prop) (H : α → Option β)
    (f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β)))
    (step : ∀ x p, (∀ b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) ∧
      (H x = none → ∃ r s, f x p = ForInStep.done (some r, s) ∧ R r))
    (xs : Array α) (acc : Array β) :
      (∃ r, (forIn (m := Id) xs (none, acc) f).1 = some r ∧ R r) ∨
      ((forIn (m := Id) xs (none, acc) f).1 = none ∧ ∃ bs, List.Forall₂ (fun x b => H x = some b) xs.toList bs ∧
        (forIn (m := Id) xs (none, acc) f).2 = acc ++ bs.toArray) := by
  rw [← Array.forIn_toList]
  exact forIn_exit R H f step xs.toList acc

/-- The value an exited loop exits with is one `R` describes. -/
theorem exit_of_fst {α β ρ : Type} {R : ρ → Prop} {H : α → Option β}
    {f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β))} {xs : Array α} {acc : Array β} {r : ρ}
    (exited : (forIn (m := Id) xs (none, acc) f).1 = some r)
    (step : ∀ x p, (∀ b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) ∧
      (H x = none → ∃ r s, f x p = ForInStep.done (some r, s) ∧ R r)) : R r := by
  rcases forIn_exit_array R H f step xs acc with ⟨r', exited', holds⟩ | ⟨done, _⟩
  · rw [exited] at exited'
    cases exited'
    exact holds
  · rw [exited] at done
    cases done

/-- A loop that did not exit pushed every element's value. -/
theorem pushed_of_fst {α β ρ : Type} {R : ρ → Prop} {H : α → Option β}
    {f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β))} {xs : Array α} {acc : Array β}
    (done : (forIn (m := Id) xs (none, acc) f).1 = none)
    (step : ∀ x p, (∀ b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) ∧
      (H x = none → ∃ r s, f x p = ForInStep.done (some r, s) ∧ R r)) :
    ∃ bs, List.Forall₂ (fun x b => H x = some b) xs.toList bs ∧
      (forIn (m := Id) xs (none, acc) f).2 = acc ++ bs.toArray := by
  rcases forIn_exit_array R H f step xs acc with ⟨r', exited, _⟩ | ⟨_, pushed⟩
  · rw [done] at exited
    cases exited
  · exact pushed

/-- A loop every element of which has a value pushes them all. -/
theorem forIn_all_some {α β ρ : Type} {H : α → Option β}
    {f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β))}
    (step : ∀ x p b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) :
    ∀ {l : List α} {bs : List β} (acc : Array β), List.Forall₂ (fun x b => H x = some b) l bs →
      forIn (m := Id) l (none, acc) f = (none, acc ++ bs.toArray) := by
  intro l bs acc values
  induction values generalizing acc with
  | nil => show (none, acc) = (none, acc ++ #[]); simp
  | cons value _ ih =>
    rw [List.forIn_cons, step _ _ _ value]
    show forIn (m := Id) _ (none, acc.push _) f = _
    rw [ih]
    simp

/-- A loop every element of which has a value does not exit. -/
theorem no_exit {α β ρ : Type} {R : ρ → Prop} {H : α → Option β}
    {f : α → Option ρ × Array β → Id (ForInStep (Option ρ × Array β))} {xs : Array α} {acc : Array β} {r : ρ}
    (exited : (forIn (m := Id) xs (none, acc) f).1 = some r)
    (step : ∀ x p, (∀ b, H x = some b → f x p = ForInStep.yield (none, p.2.push b)) ∧
      (H x = none → ∃ r s, f x p = ForInStep.done (some r, s) ∧ R r))
    {bs : List β} (holds : List.Forall₂ (fun x b => H x = some b) xs.toList bs) : False := by
  rw [← Array.forIn_toList, forIn_all_some (fun x p b value => (step x p).1 b value) acc holds] at exited
  cases exited

/-! ## Loops in `Except` -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {m₁ : List β} {l₂ : List α} {m₂ : List β},
      List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ → List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  intro l₁ m₁ l₂ m₂ first second
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head ih

/-- A loop of a fallible step that only yields keeps an invariant of the
prefix it has processed. -/
theorem forIn_inv {α σ ε : Type} (I : List α → σ → Prop) (f : α → σ → Except ε (ForInStep σ)) (full : List α)
    (step : ∀ pre x post s r, pre ++ x :: post = full → I pre s → f x s = .ok r →
      ∃ s', r = .yield s' ∧ I (pre ++ [x]) s') :
    ∀ (post pre : List α) (s res : σ), pre ++ post = full → I pre s → forIn post s f = .ok res → I full res := by
  intro post
  induction post with
  | nil =>
    intro pre s res whole holds ran
    rw [List.append_nil] at whole
    subst whole
    cases ran
    exact holds
  | cons x post ih =>
    intro pre s res whole holds ran
    rw [List.forIn_cons] at ran
    obtain ⟨r, stepped, rest⟩ := except_bind_ok.mp ran
    obtain ⟨s', rfl, holds'⟩ := step pre x post s r whole holds stepped
    exact ih (pre ++ [x]) s' res (by rw [List.append_assoc]; exact whole) holds' rest

theorem forIn_inv_array {α σ ε : Type} (I : List α → σ → Prop) (f : α → σ → Except ε (ForInStep σ))
    (xs : Array α)
    (step : ∀ pre x post s r, pre ++ x :: post = xs.toList → I pre s → f x s = .ok r →
      ∃ s', r = .yield s' ∧ I (pre ++ [x]) s')
    {s res : σ} (holds : I [] s) (ran : forIn xs s f = .ok res) : I xs.toList res := by
  rw [← Array.forIn_toList] at ran
  exact forIn_inv I f xs.toList step xs.toList [] s res rfl holds ran

/-- A loop that pushes one element per input element: the result is related
to the input position by position. -/
theorem forIn_push_array {α γ ε : Type} (xs : Array α)
    (body : α → Array γ → Except ε (ForInStep (Array γ))) (Q : α → γ → Prop)
    (hstep : ∀ x r s, body x r = .ok s → ∃ y, s = .yield (r.push y) ∧ Q x y)
    {out : Array γ} (h : forIn xs #[] body = .ok out) : List.Forall₂ Q xs.toList out.toList := by
  have := forIn_inv_array (fun pre r => List.Forall₂ Q pre r.toList) body xs
    (fun pre x _ r s _ held ran => by
      obtain ⟨y, rfl, hq⟩ := hstep x r s ran
      refine ⟨r.push y, rfl, ?_⟩
      rw [Array.toList_push]
      exact forall₂_append held (.cons hq .nil))
    List.Forall₂.nil h
  exact this

theorem mapM_forall₂ {α β ε : Type} (f : α → Except ε β) :
    ∀ {l : List α} {bs : List β}, l.mapM f = .ok bs → List.Forall₂ (fun x b => f x = .ok b) l bs := by
  intro l
  induction l with
  | nil => intro bs ran; cases ran; exact .nil
  | cons x l ih =>
    intro bs ran
    rw [List.mapM_cons] at ran
    obtain ⟨b, head, rest⟩ := except_bind_ok.mp ran
    obtain ⟨bs', tail, done⟩ := except_bind_ok.mp rest
    cases done
    exact .cons head (ih tail)

end Ix.CompileCert.Loop
