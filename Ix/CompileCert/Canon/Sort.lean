import Ix.CompileCert.Canon.Cache

/-!
# M7 L1, the refinement: `List.sortByM` sorts

`Ix.Compile.Canon.refineClass` sorts a class with `List.sortByM` (`Ix/Common.lean`: a natural
merge sort, ascending and strictly descending runs, then rounds of pairwise merges with fuel
the number of runs) under the comparator of the round. This module proves, for a comparison
`cmp : α → α → Except ε Ordering` that is only *oriented* on the elements (`Oriented`: a
successful `cmp a b` read the other way is the swapped result), that a successful sort
returns a permutation of its input whose adjacent pairs compare `≤` (`sortByM_spec`), and
that the same sort run in `CmpM` with a cached comparison simulates the pure one
(`sortByM_sim`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

section pure
variable {α : Type} {ε : Type}

theorem except_bind_ok {β γ : Type} {e : Except ε β} {k : β → Except ε γ} {r : γ} :
    (e >>= k) = .ok r ↔ ∃ x, e = .ok x ∧ k x = .ok r := by
  cases e with
  | error e' => simp [bind, Except.bind]
  | ok x => simp [bind, Except.bind]

/-- `a` sorts no later than `b`: the comparison succeeds and is not `gt`. -/
def LeC (cmp : α → α → Except ε Ordering) (a b : α) : Prop := ∃ o, cmp a b = .ok o ∧ o ≠ .gt

/-- Adjacent pairs are related. -/
def Sorted (R : α → α → Prop) : List α → Prop
  | a :: b :: l => R a b ∧ Sorted R (b :: l)
  | _ => True

theorem sorted_cons_cons {R : α → α → Prop} {a b : α} {l : List α} :
    Sorted R (a :: b :: l) ↔ R a b ∧ Sorted R (b :: l) := Iff.rfl

theorem sorted_tail {R : α → α → Prop} {a : α} {l : List α} (h : Sorted R (a :: l)) : Sorted R l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2

/-- Extending a sorted list at the front. -/
theorem sorted_cons {R : α → α → Prop} {a : α} {l : List α} (hl : Sorted R l)
    (h : ∀ b, l.head? = some b → R a b) : Sorted R (a :: l) := by
  cases l with
  | nil => trivial
  | cons b l => exact ⟨h b rfl, hl⟩

theorem sorted_append_single {R : α → α → Prop} :
    ∀ (pre : List α) (a b : α), Sorted R (pre ++ [a]) → R a b → Sorted R (pre ++ [a, b])
  | [], _, _, _, h => ⟨h, trivial⟩
  | [_], _, _, hs, h => ⟨hs.1, h, trivial⟩
  | _ :: y :: pre, a, b, hs, h => ⟨hs.1, sorted_append_single (y :: pre) a b hs.2 h⟩

/-- The comparison is oriented on the points satisfying `S`. -/
def Oriented (S : α → Prop) (cmp : α → α → Except ε Ordering) : Prop :=
  ∀ a b, S a → S b → ∀ o, cmp a b = .ok o → cmp b a = .ok o.swap

variable {S : α → Prop} {cmp : α → α → Except ε Ordering}

theorem leC_of_gt (hS : Oriented S cmp) {a b : α} (ha : S a) (hb : S b)
    (h : cmp a b = .ok .gt) : LeC cmp b a :=
  ⟨.lt, by simpa using hS a b ha hb .gt h, by decide⟩

theorem mergeM_spec (hS : Oriented S cmp) : ∀ (n : Nat) (as bs : List α), as.length + bs.length ≤ n →
    (∀ x ∈ as, S x) → (∀ x ∈ bs, S x) → Sorted (LeC cmp) as → Sorted (LeC cmp) bs →
    ∀ ms, List.mergeM cmp as bs = .ok ms →
      ms.Perm (as ++ bs) ∧ Sorted (LeC cmp) ms ∧ (ms.head? = as.head? ∨ ms.head? = bs.head?) := by
  intro n
  induction n with
  | zero =>
    intro as bs hl _ _ _ _ ms h
    cases as <;> cases bs <;> simp at hl
    rw [List.mergeM.eq_def] at h; cases h
    exact ⟨List.Perm.refl _, trivial, .inl rfl⟩
  | succ n ih =>
    intro as bs hl has hbs sa sb ms h
    cases as with
    | nil =>
      rw [List.mergeM.eq_def] at h; cases h
      exact ⟨List.Perm.refl _, sb, .inr rfl⟩
    | cons a as' =>
      cases bs with
      | nil =>
        rw [List.mergeM.eq_def] at h; cases h
        exact ⟨by simp, sa, .inl rfl⟩
      | cons b bs' =>
        rw [List.mergeM.eq_def] at h
        simp only at h
        obtain ⟨o, ho, h⟩ := except_bind_ok.1 h
        have ha : S a := has a (by simp)
        have hb : S b := hbs b (by simp)
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte] at h
          obtain ⟨merged, hm, h⟩ := except_bind_ok.1 h
          cases h
          obtain ⟨p, s, hd⟩ := ih (a :: as') bs' (by simp at hl ⊢; omega) has
            (fun x hx => hbs x (by simp [hx])) sa (sorted_tail sb) merged hm
          refine ⟨?_, sorted_cons s fun c hc => ?_, .inr rfl⟩
          · exact (List.Perm.cons b p).trans (List.perm_middle).symm
          · rcases hd with hd | hd
            · rw [hd] at hc; cases hc; exact leC_of_gt hS ha hb ho
            · rw [hd] at hc
              cases bs' with
              | nil => cases hc
              | cons b' bs'' => cases hc; exact sb.1
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨merged, hm, h⟩ := except_bind_ok.1 h
          cases h
          obtain ⟨p, s, hd⟩ := ih as' (b :: bs') (by simp at hl ⊢; omega)
            (fun x hx => has x (by simp [hx])) hbs (sorted_tail sa) sb merged hm
          refine ⟨List.Perm.cons a p, sorted_cons s fun c hc => ?_, .inl rfl⟩
          rcases hd with hd | hd
          · rw [hd] at hc
            cases as' with
            | nil => cases hc
            | cons a' as'' => cases hc; exact sa.1
          · rw [hd] at hc; cases hc; exact ⟨o, ho, hgt⟩

theorem runs_spec (hS : Oriented S cmp) : ∀ m : Nat,
    (∀ xs : List α, 2 * xs.length < m → (∀ x ∈ xs, S x) → ∀ runs, List.sequencesM cmp xs = .ok runs →
      runs.flatten.Perm xs ∧ ∀ r ∈ runs, Sorted (LeC cmp) r) ∧
    (∀ (a : α) (as xs : List α), 2 * xs.length + 1 < m → (∀ x ∈ a :: as, S x) → (∀ x ∈ xs, S x) →
      Sorted (LeC cmp) (a :: as) → ∀ runs, List.descendingM cmp a as xs = .ok runs →
      runs.flatten.Perm (a :: as ++ xs) ∧ ∀ r ∈ runs, Sorted (LeC cmp) r) ∧
    (∀ (a : α) (f : List α → List α) (pre xs : List α), (∀ ys, f ys = pre ++ ys) →
      2 * xs.length + 1 < m → (∀ x ∈ pre ++ [a], S x) → (∀ x ∈ xs, S x) →
      Sorted (LeC cmp) (pre ++ [a]) → ∀ runs, List.ascendingM cmp a f xs = .ok runs →
      runs.flatten.Perm (pre ++ a :: xs) ∧ ∀ r ∈ runs, Sorted (LeC cmp) r) := by
  intro m
  induction m with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨ihS, ihD, ihA⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro xs hl hxs runs h
      rw [List.sequencesM.eq_def] at h
      match xs, hl, hxs, h with
      | a :: b :: xs', hl, hxs, h =>
        simp only at h
        obtain ⟨o, ho, h⟩ := except_bind_ok.1 h
        have ha : S a := hxs a (by simp)
        have hb : S b := hxs b (by simp)
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte] at h
          obtain ⟨p, s⟩ := ihD b [a] xs' (by simp at hl; omega) (by simp [ha, hb])
            (fun x hx => hxs x (by simp [hx])) ⟨leC_of_gt hS ha hb ho, trivial⟩ runs h
          refine ⟨p.trans ?_, s⟩
          exact List.Perm.swap a b xs'
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
          exact ihA b (fun ys => a :: ys) [a] xs' (fun _ => rfl) (by simp at hl; omega)
            (by simp [ha, hb]) (fun x hx => hxs x (by simp [hx])) ⟨⟨o, ho, hgt⟩, trivial⟩ runs h
      | [], _, _, h =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨by simp, fun r hr => by simp at hr; subst hr; trivial⟩
      | [a], _, _, h =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨by simp, by simp [Sorted]⟩
    · intro a as xs hl has hxs sa runs h
      rw [List.descendingM.eq_def] at h
      match xs, hl, hxs, h with
      | b :: bs, hl, hxs, h =>
        simp only at h
        obtain ⟨o, ho, h⟩ := except_bind_ok.1 h
        have ha : S a := has a (by simp)
        have hb : S b := hxs b (by simp)
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte] at h
          obtain ⟨p, s⟩ := ihD b (a :: as) bs (by simp at hl; omega)
            (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hx
              · exact hb
              · exact has x hx) (fun x hx => hxs x (by simp [hx]))
            ⟨leC_of_gt hS ha hb ho, sa⟩ runs h
          refine ⟨p.trans ?_, s⟩
          simp only [List.cons_append]
          exact (List.Perm.swap a b (as ++ bs)).trans (List.Perm.cons a List.perm_middle.symm)
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          obtain ⟨p, s⟩ := ihS (b :: bs) (by simp at hl ⊢; omega) hxs rest hr
          refine ⟨?_, fun r hr' => ?_⟩
          · simp only [List.flatten_cons]; exact List.Perm.append_left _ p
          · rcases List.mem_cons.1 hr' with rfl | hr'
            · exact sa
            · exact s r hr'
      | [], hl, _, h =>
        simp only at h
        obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨p, s⟩ := ihS [] (by simp; omega) (by simp) rest hr
        refine ⟨?_, fun r hr' => ?_⟩
        · simp only [List.flatten_cons, List.append_nil]
          have := List.Perm.append_left (a :: as) p; simpa using this
        · rcases List.mem_cons.1 hr' with rfl | hr'
          · exact sa
          · exact s r hr'
    · intro a f pre xs hf hl hpre hxs sa runs h
      rw [List.ascendingM.eq_def] at h
      match xs, hl, hxs, h with
      | b :: bs, hl, hxs, h =>
        simp only at h
        obtain ⟨o, ho, h⟩ := except_bind_ok.1 h
        have ha : S a := hpre a (by simp)
        have hb : S b := hxs b (by simp)
        by_cases hgt : o = .gt
        · have hne : (o != .gt) = false := by subst hgt; rfl
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          obtain ⟨p, s⟩ := ihS (b :: bs) (by simp at hl ⊢; omega) hxs rest hr
          refine ⟨?_, fun r hr' => ?_⟩
          · simp only [List.flatten_cons, hf]
            have := List.Perm.append_left (pre ++ [a]) p; simpa using this
          · rcases List.mem_cons.1 hr' with rfl | hr'
            · rw [hf]; exact sa
            · exact s r hr'
        · have hne : (o != .gt) = true := by simpa using hgt
          simp only [hne, ↓reduceIte] at h
          obtain ⟨p, s⟩ := ihA b (fun ys => f (a :: ys)) (pre ++ [a]) bs
            (fun ys => by rw [hf]; simp) (by simp at hl; omega)
            (fun x hx => by
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with (hx | hx) | hx
              · exact hpre x (by simp [hx])
              · subst hx; exact ha
              · subst hx; exact hb)
            (fun x hx => hxs x (by simp [hx]))
            (by have := sorted_append_single pre a b sa ⟨o, ho, hgt⟩; simpa using this) runs h
          exact ⟨by simpa using p, s⟩
      | [], hl, _, h =>
        simp only at h
        obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨p, s⟩ := ihS [] (by simp; omega) (by simp) rest hr
        refine ⟨?_, fun r hr' => ?_⟩
        · simp only [List.flatten_cons, hf]
          have := List.Perm.append_left (pre ++ [a]) p; simpa using this
        · rcases List.mem_cons.1 hr' with rfl | hr'
          · rw [hf]; exact sa
          · exact s r hr'

theorem mergePairs_spec (hS : Oriented S cmp) : ∀ (n : Nat) (xss : List (List α)), xss.length ≤ n →
    (∀ xs ∈ xss, ∀ x ∈ xs, S x) → (∀ xs ∈ xss, Sorted (LeC cmp) xs) →
    ∀ yss, List.mergePairsM cmp xss = .ok yss →
      yss.flatten.Perm xss.flatten ∧ (∀ ys ∈ yss, Sorted (LeC cmp) ys) ∧
      (∀ ys ∈ yss, ∀ y ∈ ys, S y) ∧ yss.length = (xss.length + 1) / 2 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro xss hl hS' hs yss h
    rw [List.mergePairsM.eq_def] at h
    match xss, hl, hS', hs, h with
    | a :: b :: xs, hl, hS', hs, h =>
      simp only at h
      obtain ⟨merged, hm, h⟩ := except_bind_ok.1 h
      obtain ⟨rest, hr, h⟩ := except_bind_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      obtain ⟨p1, s1, -⟩ := mergeM_spec hS _ a b (Nat.le_refl _) (hS' a (by simp)) (hS' b (by simp))
        (hs a (by simp)) (hs b (by simp)) merged hm
      obtain ⟨p2, s2, e2, l2⟩ := ih xs.length (by simp at hl; omega) xs (Nat.le_refl _)
        (fun xs' hx => hS' xs' (by simp [hx])) (fun xs' hx => hs xs' (by simp [hx])) rest hr
      refine ⟨?_, fun ys hy => ?_, fun ys hy y hyy => ?_, ?_⟩
      · simp only [List.flatten_cons, ← List.append_assoc]
        exact List.Perm.append p1 p2
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact s1
        · exact s2 ys hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · rcases List.mem_append.1 (p1.mem_iff.1 hyy) with h' | h'
          · exact hS' a (by simp) y h'
          · exact hS' b (by simp) y h'
        · exact e2 ys hy y hyy
      · simp only [List.length_cons, l2]; omega
    | [], _, _, _, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    | [a], _, hS', hs, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨List.Perm.refl _, hs, hS', by simp⟩

theorem mergeAll_spec (hS : Oriented S cmp) : ∀ (fuel : Nat) (xss : List (List α)),
    xss.length ≤ fuel + 1 → (∀ xs ∈ xss, ∀ x ∈ xs, S x) → (∀ xs ∈ xss, Sorted (LeC cmp) xs) →
    ∀ ys, List.mergeAllMFuel cmp fuel xss = .ok ys → ys.Perm xss.flatten ∧ Sorted (LeC cmp) ys := by
  intro fuel
  induction fuel with
  | zero =>
    intro xss hl _ hs ys h
    rw [List.mergeAllMFuel.eq_def] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    match xss, hl, hs with
    | [], _, _ => exact ⟨List.Perm.refl _, trivial⟩
    | [x], _, hs => simpa using hs x (by simp)
  | succ fuel ih =>
    intro xss hl hS' hs ys h
    rw [List.mergeAllMFuel.eq_def] at h
    match xss, hl, hS', hs, h with
    | [x], _, _, hs, h =>
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      simpa using hs x (by simp)
    | [], _, _, _, h =>
      simp only at h
      obtain ⟨yss, hp, h⟩ := except_bind_ok.1 h
      obtain ⟨p, s, e, l⟩ := mergePairs_spec hS _ [] (Nat.le_refl _) (by simp) (by simp) yss hp
      obtain ⟨p', s'⟩ := ih yss (by simp only [List.length_nil] at l; omega) e s ys h
      exact ⟨p'.trans p, s'⟩
    | a :: b :: xs, hl, hS', hs, h =>
      simp only at h
      obtain ⟨yss, hp, h⟩ := except_bind_ok.1 h
      obtain ⟨p, s, e, l⟩ := mergePairs_spec hS _ _ (Nat.le_refl _) hS' hs yss hp
      obtain ⟨p', s'⟩ := ih yss (by simp at l hl ⊢; omega) e s ys h
      exact ⟨p'.trans p, s'⟩

/-- **A successful sort returns a sorted permutation** of its input, for a comparison that is
oriented on the input's elements. -/
theorem sortByM_spec (hS : Oriented S cmp) (xs : List α) (hxs : ∀ x ∈ xs, S x) (ys : List α)
    (h : xs.sortByM cmp = .ok ys) : ys.Perm xs ∧ Sorted (LeC cmp) ys := by
  unfold List.sortByM at h
  obtain ⟨runs, hr, h⟩ := except_bind_ok.1 h
  obtain ⟨p, s⟩ := (runs_spec hS (2 * xs.length + 1)).1 xs (by omega) hxs runs hr
  have hS' : ∀ r ∈ runs, ∀ x ∈ r, S x := fun r hr x hx =>
    hxs x (p.mem_iff.1 (List.mem_flatten.2 ⟨r, hr, hx⟩))
  obtain ⟨p', s'⟩ := mergeAll_spec hS runs.length runs (by omega) hS' s ys h
  exact ⟨p'.trans p, s'⟩

end pure

/-! ## The sort in `CmpM` simulates the pure sort -/

section sim
variable {α : Type} {Inv : CmpState → Prop} {S : α → Prop} {cmpM : α → α → CmpM Ordering}
  {cmpE : α → α → Except String Ordering}
  (hsim : ∀ a b, S a → S b → Sim Inv (cmpM a b) (cmpE a b))
include hsim

theorem mergeM_sim : ∀ (n : Nat) (as bs : List α), as.length + bs.length ≤ n →
    (∀ x ∈ as, S x) → (∀ x ∈ bs, S x) → Sim Inv (List.mergeM cmpM as bs) (List.mergeM cmpE as bs) := by
  intro n
  induction n with
  | zero =>
    intro as bs hl _ _
    cases as <;> cases bs <;> simp at hl
    rw [List.mergeM.eq_def, List.mergeM.eq_def]; exact Sim.pure' _
  | succ n ih =>
    intro as bs hl has hbs
    rw [List.mergeM.eq_def, List.mergeM.eq_def]
    match as, bs, hl, has, hbs with
    | [], bs, _, _, _ => exact Sim.pure' _
    | a :: as', [], _, _, _ => exact Sim.pure' _
    | a :: as', b :: bs', hl, has, hbs =>
      simp only
      refine Sim.bind (hsim a b (has a (by simp)) (hbs b (by simp))) fun o _ => ?_
      split
      · exact Sim.bind (ih (a :: as') bs' (by simp at hl ⊢; omega) has
          (fun x hx => hbs x (by simp [hx]))) fun _ _ => Sim.pure' _
      · exact Sim.bind (ih as' (b :: bs') (by simp at hl ⊢; omega)
          (fun x hx => has x (by simp [hx])) hbs) fun _ _ => Sim.pure' _

theorem runs_sim : ∀ m : Nat,
    (∀ xs : List α, 2 * xs.length < m → (∀ x ∈ xs, S x) →
      Sim Inv (List.sequencesM cmpM xs) (List.sequencesM cmpE xs)) ∧
    (∀ (a : α) (as xs : List α), 2 * xs.length + 1 < m → S a → (∀ x ∈ xs, S x) →
      Sim Inv (List.descendingM cmpM a as xs) (List.descendingM cmpE a as xs)) ∧
    (∀ (a : α) (f : List α → List α) (xs : List α), 2 * xs.length + 1 < m → S a →
      (∀ x ∈ xs, S x) → Sim Inv (List.ascendingM cmpM a f xs) (List.ascendingM cmpE a f xs)) := by
  intro m
  induction m with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨ihS, ihD, ihA⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro xs hl hxs
      rw [List.sequencesM.eq_def, List.sequencesM.eq_def]
      match xs, hl, hxs with
      | a :: b :: xs', hl, hxs =>
        simp only
        refine Sim.bind (hsim a b (hxs a (by simp)) (hxs b (by simp))) fun o _ => ?_
        split
        · exact ihD b [a] xs' (by simp at hl; omega) (hxs b (by simp)) (fun x hx => hxs x (by simp [hx]))
        · exact ihA b _ xs' (by simp at hl; omega) (hxs b (by simp)) (fun x hx => hxs x (by simp [hx]))
      | [], _, _ => exact Sim.pure' _
      | [_], _, _ => exact Sim.pure' _
    · intro a as xs hl ha hxs
      rw [List.descendingM.eq_def, List.descendingM.eq_def]
      match xs, hl, hxs with
      | b :: bs, hl, hxs =>
        simp only
        refine Sim.bind (hsim a b ha (hxs b (by simp))) fun o _ => ?_
        split
        · exact ihD b (a :: as) bs (by simp at hl; omega) (hxs b (by simp))
            (fun x hx => hxs x (by simp [hx]))
        · exact Sim.bind (ihS (b :: bs) (by simp at hl ⊢; omega) hxs) fun _ _ => Sim.pure' _
      | [], hl, _ =>
        simp only
        exact Sim.bind (ihS [] (by simp; omega) (by simp)) fun _ _ => Sim.pure' _
    · intro a f xs hl ha hxs
      rw [List.ascendingM.eq_def, List.ascendingM.eq_def]
      match xs, hl, hxs with
      | b :: bs, hl, hxs =>
        simp only
        refine Sim.bind (hsim a b ha (hxs b (by simp))) fun o _ => ?_
        split
        · exact ihA b _ bs (by simp at hl; omega) (hxs b (by simp)) (fun x hx => hxs x (by simp [hx]))
        · exact Sim.bind (ihS (b :: bs) (by simp at hl ⊢; omega) hxs) fun _ _ => Sim.pure' _
      | [], hl, _ =>
        simp only
        exact Sim.bind (ihS [] (by simp; omega) (by simp)) fun _ _ => Sim.pure' _

theorem mergePairs_sim : ∀ (n : Nat) (xss : List (List α)), xss.length ≤ n →
    (∀ xs ∈ xss, ∀ x ∈ xs, S x) →
    Sim Inv (List.mergePairsM cmpM xss) (List.mergePairsM cmpE xss) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro xss hl hS'
    rw [List.mergePairsM.eq_def, List.mergePairsM.eq_def]
    match xss, hl, hS' with
    | a :: b :: xs, hl, hS' =>
      simp only
      refine Sim.bind (mergeM_sim hsim _ a b (Nat.le_refl _) (hS' a (by simp)) (hS' b (by simp)))
        fun _ _ => ?_
      exact Sim.bind (ih xs.length (by simp at hl; omega) xs (Nat.le_refl _)
        (fun xs' hx => hS' xs' (by simp [hx]))) fun _ _ => Sim.pure' _
    | [], _, _ => exact Sim.pure' _
    | [_], _, _ => exact Sim.pure' _

theorem mergeAll_sim (hS : Oriented S cmpE) : ∀ (fuel : Nat) (xss : List (List α)),
    (∀ xs ∈ xss, ∀ x ∈ xs, S x) → (∀ xs ∈ xss, Sorted (LeC cmpE) xs) →
    Sim Inv (List.mergeAllMFuel cmpM fuel xss) (List.mergeAllMFuel cmpE fuel xss) := by
  intro fuel
  induction fuel with
  | zero =>
    intro xss _ _
    rw [List.mergeAllMFuel.eq_def, List.mergeAllMFuel.eq_def]
    exact Sim.pure' _
  | succ fuel ih =>
    intro xss hS' hs
    rw [List.mergeAllMFuel.eq_def, List.mergeAllMFuel.eq_def]
    match xss, hS', hs with
    | [_], _, _ => exact Sim.pure' _
    | [], hS', hs =>
      simp only
      refine Sim.bind (mergePairs_sim hsim _ _ (Nat.le_refl _) hS') fun yss hy => ?_
      obtain ⟨-, s, e, -⟩ := mergePairs_spec hS _ _ (Nat.le_refl _) hS' hs yss hy
      exact ih yss e s
    | a :: b :: xs, hS', hs =>
      simp only
      refine Sim.bind (mergePairs_sim hsim _ _ (Nat.le_refl _) hS') fun yss hy => ?_
      obtain ⟨-, s, e, -⟩ := mergePairs_spec hS _ _ (Nat.le_refl _) hS' hs yss hy
      exact ih yss e s

/-- **The sort run in `CmpM` with a simulated comparison is the pure sort.** -/
theorem sortByM_sim (hS : Oriented S cmpE) (xs : List α) (hxs : ∀ x ∈ xs, S x) :
    Sim Inv (xs.sortByM cmpM) (xs.sortByM cmpE) := by
  unfold List.sortByM
  refine Sim.bind ((runs_sim hsim (2 * xs.length + 1)).1 xs (by omega) hxs) fun runs hr => ?_
  obtain ⟨p, s⟩ := (runs_spec hS (2 * xs.length + 1)).1 xs (by omega) hxs runs hr
  exact mergeAll_sim hsim hS _ runs (fun r hr x hx =>
    hxs x (p.mem_iff.1 (List.mem_flatten.2 ⟨r, hr, hx⟩))) s

end sim

end Ix.CompileCert.Canon
