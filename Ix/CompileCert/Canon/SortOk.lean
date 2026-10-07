import Ix.CompileCert.Canon.Group

/-!
# M7 L1, the refinement: the sort and the grouping succeed on comparable members

`sortByM_spec` and `groupAdjP_spec` describe a *successful* sort and grouping. Here: they do
succeed when every pair of members at distinct positions compares (`BothOk`, both
orientations); the fuel of the merge rounds never runs out with an error (it returns the
concatenation), so a comparison is the only way to fail. Used to run a round of the
refinement on a permuted class (`SeedFree.lean`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

section
variable {α : Type} {ε : Type} {cmp : α → α → Except ε Ordering}

/-- Both orientations of a pair compare. -/
def BothOk (cmp : α → α → Except ε Ordering) (a b : α) : Prop :=
  (∃ o, cmp a b = .ok o) ∧ (∃ o, cmp b a = .ok o)

theorem BothOk.symm {a b : α} (h : BothOk cmp a b) : BothOk cmp b a := ⟨h.2, h.1⟩

theorem pairwise_bothOk_perm {l l' : List α} (p : l.Perm l') (h : l.Pairwise (BothOk cmp)) :
    l'.Pairwise (BothOk cmp) :=
  p.pairwise h fun h => h.symm

theorem mergeM_ok : ∀ (n : Nat) (as bs : List α), as.length + bs.length ≤ n →
    (as ++ bs).Pairwise (BothOk cmp) → ∃ ms, List.mergeM cmp as bs = .ok ms ∧ ms.Perm (as ++ bs) := by
  intro n
  induction n with
  | zero =>
    intro as bs hl _
    cases as <;> cases bs <;> simp at hl
    exact ⟨[], by rw [List.mergeM.eq_def]; rfl, List.Perm.refl _⟩
  | succ n ih =>
    intro as bs hl hp
    cases as with
    | nil => exact ⟨bs, by rw [List.mergeM.eq_def]; rfl, List.Perm.refl _⟩
    | cons a as' =>
      cases bs with
      | nil => exact ⟨a :: as', by rw [List.mergeM.eq_def]; rfl, by simp⟩
      | cons b bs' =>
        have hab : BothOk cmp a b :=
          (List.pairwise_append.1 hp).2.2 a (List.mem_cons_self ..) b (List.mem_cons_self ..)
        obtain ⟨o, ho⟩ := hab.1
        rw [List.mergeM.eq_def]
        simp only [ho, bind, Except.bind]
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte]
          obtain ⟨m, hm, pm⟩ := ih (a :: as') bs' (by simp at hl ⊢; omega)
            (hp.sublist (List.Sublist.append_left (List.sublist_cons_self b bs') _))
          rw [hm]
          exact ⟨_, rfl, (List.Perm.cons b pm).trans List.perm_middle.symm⟩
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨m, hm, pm⟩ := ih as' (b :: bs') (by simp at hl ⊢; omega)
            (hp.sublist (List.sublist_cons_self a _))
          rw [hm]
          exact ⟨_, rfl, List.Perm.cons a pm⟩

theorem runs_ok : ∀ m : Nat,
    (∀ xs : List α, 2 * xs.length < m → xs.Pairwise (BothOk cmp) →
      ∃ runs, List.sequencesM cmp xs = .ok runs) ∧
    (∀ (a : α) (as xs : List α), 2 * xs.length + 1 < m → (a :: xs).Pairwise (BothOk cmp) →
      ∃ runs, List.descendingM cmp a as xs = .ok runs) ∧
    (∀ (a : α) (f : List α → List α) (xs : List α), 2 * xs.length + 1 < m →
      (a :: xs).Pairwise (BothOk cmp) → ∃ runs, List.ascendingM cmp a f xs = .ok runs) := by
  intro m
  induction m with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨ihS, ihD, ihA⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro xs hl hp
      rw [List.sequencesM.eq_def]
      match xs, hl, hp with
      | a :: b :: xs', hl, hp =>
        simp only
        have hab : BothOk cmp a b := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
        obtain ⟨o, ho⟩ := hab.1
        simp only [ho, bind, Except.bind]
        have hp' : (b :: xs').Pairwise (BothOk cmp) := List.Pairwise.of_cons hp
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte]
          exact ihD b [a] xs' (by simp at hl; omega) hp'
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          exact ihA b (fun ys => a :: ys) xs' (by simp at hl; omega) hp'
      | [], _, _ => exact ⟨_, rfl⟩
      | [a], _, _ => exact ⟨_, rfl⟩
    · intro a as xs hl hp
      rw [List.descendingM.eq_def]
      match xs, hl, hp with
      | b :: bs, hl, hp =>
        simp only
        have hab : BothOk cmp a b := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
        obtain ⟨o, ho⟩ := hab.1
        simp only [ho, bind, Except.bind]
        have hp' : (b :: bs).Pairwise (BothOk cmp) := List.Pairwise.of_cons hp
        by_cases hgt : o = .gt
        · subst hgt
          simp only [beq_self_eq_true, ↓reduceIte]
          exact ihD b (a :: as) bs (by simp at hl; omega) hp'
        · have hne : (o == .gt) = false := by simpa using hgt
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨rest, hr⟩ := ihS (b :: bs) (by simp at hl ⊢; omega) hp'
          rw [hr]; exact ⟨_, rfl⟩
      | [], hl, _ =>
        simp only
        obtain ⟨rest, hr⟩ := ihS [] (by simp; omega) List.Pairwise.nil
        simp only [hr, bind, Except.bind]; exact ⟨_, rfl⟩
    · intro a f xs hl hp
      rw [List.ascendingM.eq_def]
      match xs, hl, hp with
      | b :: bs, hl, hp =>
        simp only
        have hab : BothOk cmp a b := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
        obtain ⟨o, ho⟩ := hab.1
        simp only [ho, bind, Except.bind]
        have hp' : (b :: bs).Pairwise (BothOk cmp) := List.Pairwise.of_cons hp
        by_cases hgt : o = .gt
        · have hne : (o != .gt) = false := by subst hgt; rfl
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨rest, hr⟩ := ihS (b :: bs) (by simp at hl ⊢; omega) hp'
          rw [hr]; exact ⟨_, rfl⟩
        · have hne : (o != .gt) = true := by simpa using hgt
          simp only [hne, ↓reduceIte]
          exact ihA b _ bs (by simp at hl; omega) hp'
      | [], hl, _ =>
        simp only
        obtain ⟨rest, hr⟩ := ihS [] (by simp; omega) List.Pairwise.nil
        simp only [hr, bind, Except.bind]; exact ⟨_, rfl⟩

theorem mergePairs_ok : ∀ (n : Nat) (xss : List (List α)), xss.length ≤ n →
    xss.flatten.Pairwise (BothOk cmp) →
    ∃ yss, List.mergePairsM cmp xss = .ok yss ∧ yss.flatten.Perm xss.flatten := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro xss hl hp
    rw [List.mergePairsM.eq_def]
    match xss, hl, hp with
    | a :: b :: xs, hl, hp =>
      simp only
      simp only [List.flatten_cons, ← List.append_assoc] at hp
      obtain ⟨merged, hm, pm⟩ := mergeM_ok _ a b (Nat.le_refl _) (List.pairwise_append.1 hp).1
      obtain ⟨rest, hr, pr⟩ := ih xs.length (by simp at hl; omega) xs (Nat.le_refl _)
        (List.pairwise_append.1 hp).2.1
      simp only [hm, hr, bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_⟩
      simp only [List.flatten_cons, ← List.append_assoc]
      exact pm.append pr
    | [], _, _ => exact ⟨_, rfl, List.Perm.refl _⟩
    | [a], _, _ => exact ⟨_, rfl, List.Perm.refl _⟩

theorem mergeAll_ok : ∀ (fuel : Nat) (xss : List (List α)), xss.flatten.Pairwise (BothOk cmp) →
    ∃ ys, List.mergeAllMFuel cmp fuel xss = .ok ys := by
  intro fuel
  induction fuel with
  | zero => intro xss _; rw [List.mergeAllMFuel.eq_def]; exact ⟨_, rfl⟩
  | succ fuel ih =>
    intro xss hp
    rw [List.mergeAllMFuel.eq_def]
    match xss, hp with
    | [x], _ => exact ⟨_, rfl⟩
    | [], hp =>
      simp only
      obtain ⟨yss, hy, py⟩ := mergePairs_ok _ [] (Nat.le_refl _) hp
      obtain ⟨ys, h⟩ := ih yss (pairwise_bothOk_perm py.symm hp)
      simp only [hy, bind, Except.bind]; exact ⟨ys, h⟩
    | a :: b :: xs, hp =>
      simp only
      obtain ⟨yss, hy, py⟩ := mergePairs_ok _ _ (Nat.le_refl _) hp
      obtain ⟨ys, h⟩ := ih yss (pairwise_bothOk_perm py.symm hp)
      simp only [hy, bind, Except.bind]; exact ⟨ys, h⟩

/-- **The sort succeeds** when every two members at distinct positions compare, for a
comparison oriented everywhere. -/
theorem sortByM_ok (hS : Oriented (fun _ => True) cmp) (xs : List α)
    (hp : xs.Pairwise (BothOk cmp)) : ∃ ys, xs.sortByM cmp = .ok ys := by
  unfold List.sortByM
  obtain ⟨runs, hr⟩ := (runs_ok (cmp := cmp) (2 * xs.length + 1)).1 xs (by omega) hp
  obtain ⟨p, -⟩ := (runs_spec hS (2 * xs.length + 1)).1 xs (by omega) (fun _ _ => trivial) runs hr
  obtain ⟨ys, h⟩ := mergeAll_ok runs.length runs (pairwise_bothOk_perm p.symm hp)
  simp only [hr, bind, Except.bind]
  exact ⟨ys, h⟩

end

section
variable {α : Type} (eq : α → α → Except String Bool)

theorem groupGoP_ok : ∀ (rest : List α) (prev : α) (cur : List α) (acc : List (List α)),
    (prev :: rest).Pairwise (fun a b => ∃ v, eq b a = .ok v) →
    ∃ gs, groupGoP eq prev cur acc rest = .ok gs := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _; exact ⟨_, rfl⟩
  | cons a as ih =>
    intro prev cur acc hp
    obtain ⟨v, hv⟩ := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
    have hp' := List.Pairwise.of_cons hp
    simp only [groupGoP, hv, bind, Except.bind]
    cases v
    · exact ih a [a] _ hp'
    · exact ih a (a :: cur) acc hp'

/-- **The grouping succeeds** when every member compares with each earlier one. -/
theorem groupAdjP_ok (xs : List α) (hp : xs.Pairwise (fun a b => ∃ v, eq b a = .ok v)) :
    ∃ gs, groupAdjP eq xs = .ok gs := by
  cases xs with
  | nil => exact ⟨_, rfl⟩
  | cons x xs => exact groupGoP_ok eq xs x [x] [] hp

end

end Ix.CompileCert.Canon
