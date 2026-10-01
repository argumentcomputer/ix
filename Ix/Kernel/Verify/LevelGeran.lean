/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
module

public import Ix.Kernel.LevelGeran

@[expose] public section

/-!
# `Level.Geran.leq` decides the pointwise order (cl-level)

The sublevels of `l + k` evaluate to `l + k` (`decompose_eval`), so a
sublevel-wise domination is a pointwise inequality (`leq_sound`). Conversely,
two separating valuations show that a missing dominator is a counterexample
(`leq_complete`). For a constant sublevel `C(p, c)`, set the parameters of `p`
to 1 and the others to 0. For a variable sublevel `V(p, x, k)`, also set `x`
to one more than any value the other side's sublevels can take at
parameters worth at most 1. The argument is that of the retired intrinsic
kernel (`Ix/Kernel/Certified/LevelNorm.lean` at `8eb77018`), with valuations
as functions on names.

Level evaluation is restated here as `levelEval`, because
`Ix.Kernel.Level.eval` is defined in `Ix/Kernel/Verify/Level.lean`, which
imports this module. `Level.eval_eq_levelEval` there proves the two equal. -/

namespace Ix.Kernel.Level.Geran

/-- Level evaluation under an assignment of the parameters, as
`Ix.Kernel.Level.eval`. -/
def levelEval (φ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => levelEval φ l + 1
  | .max l r => Max.max (levelEval φ l) (levelEval φ r)
  | .imax l r => if levelEval φ r = 0 then 0 else Max.max (levelEval φ l) (levelEval φ r)
  | .param n => φ n

section Eval
variable (φ : Name → Nat)

/-- Every parameter of the condition set is nonzero. -/
def active (p : List Name) : Bool := p.all fun i => decide (0 < φ i)

/-- The value of a sublevel. -/
def Sub.eval : Sub → Nat
  | .const p c => if active φ p then c else 0
  | .var p x k => if active φ p then φ x + k else 0

/-- The value of a list of sublevels: their maximum. -/
def evalList : List Sub → Nat
  | [] => 0
  | s :: l => Max.max (s.eval φ) (evalList l)

/-- `n` under a condition set. -/
def gate (p : List Name) (n : Nat) : Nat := if active φ p then n else 0

end Eval

/-- A variable sublevel's variable is in its own condition set. -/
def Sub.WF : Sub → Prop
  | .const .. => True
  | .var p x _ => x ∈ p

section Lemmas
variable {φ : Name → Nat}

theorem active_iff {p : List Name} : active φ p = true ↔ ∀ i ∈ p, 0 < φ i := by
  simp [active]

theorem active_cons {x : Name} {p : List Name} :
    active φ (x :: p) = (decide (0 < φ x) && active φ p) := rfl

theorem active_append {c p : List Name} :
    active φ (c ++ p) = (active φ c && active φ p) := by
  simp [active, List.all_append]

theorem contains_iff {p : List Name} {x : Name} : p.contains x = true ↔ x ∈ p := by
  simp

/-- `nzConds` is exact: some condition set is active iff the level is
nonzero. -/
theorem nzConds_spec (v : Level) :
    (nzConds v).any (active φ) = true ↔ levelEval φ v ≠ 0 := by
  induction v with
  | zero => simp [nzConds, levelEval]
  | succ u _ => simp [nzConds, levelEval, active]
  | max a b iha ihb =>
    rw [nzConds, List.any_append, Bool.or_eq_true, iha, ihb]
    simp only [levelEval]; omega
  | imax a b _ ihb =>
    rw [nzConds, ihb]; simp only [levelEval]
    split <;> omega
  | param x => simp [nzConds, levelEval, active]; omega

theorem evalList_nil : evalList φ [] = 0 := rfl

theorem evalList_cons {s : Sub} {l : List Sub} :
    evalList φ (s :: l) = Max.max (s.eval φ) (evalList φ l) := rfl

/-- The `imax` step: `u` under each condition set of `cs`. -/
theorem foldl_eval {u : Level} {k : Nat} {path : List Name}
    (ih : ∀ (path : List Name) (acc : List Sub), evalList φ (decomposeAux path k u acc) =
      Max.max (gate φ path (levelEval φ u + k)) (evalList φ acc)) :
    ∀ (cs : List (List Name)) (acc : List Sub),
      evalList φ (cs.foldl (fun acc c => decomposeAux (c ++ path) k u acc) acc) =
        Max.max (if (active φ path && cs.any (active φ)) = true then levelEval φ u + k else 0)
          (evalList φ acc) := by
  intro cs
  induction cs with
  | nil => intro acc; simp
  | cons c cs ihc =>
    intro acc
    rw [List.foldl_cons, ihc, ih]
    simp only [gate, active_append, List.any_cons]
    by_cases hp : active φ path = true <;> by_cases hc : active φ c = true <;>
      by_cases he : cs.any (active φ) = true <;> simp [hp, hc, he] <;> omega

/-- The sublevels of `l + k` under `path` evaluate to `l + k` where `path`
is active. -/
theorem decomposeAux_eval (l : Level) : ∀ (path : List Name) (k : Nat) (acc : List Sub),
    evalList φ (decomposeAux path k l acc) =
      Max.max (gate φ path (levelEval φ l + k)) (evalList φ acc) := by
  induction l with
  | zero =>
    intro path k acc
    simp [decomposeAux, evalList_cons, Sub.eval, gate, levelEval]
  | succ u ih =>
    intro path k acc
    rw [decomposeAux, ih]
    simp only [gate, levelEval]
    by_cases hp : active φ path = true <;> simp [hp] <;> omega
  | max u v ihu ihv =>
    intro path k acc
    rw [decomposeAux, ihv, ihu]
    simp only [gate, levelEval]
    by_cases hp : active φ path = true <;> simp [hp] <;> omega
  | imax u v ihu ihv =>
    intro path k acc
    rw [decomposeAux, foldl_eval (fun path acc => ihu path k acc), ihv]
    simp only [gate, levelEval]
    by_cases hv : levelEval φ v = 0
    · have hany : (nzConds v).any (active φ) = false :=
        Bool.eq_false_iff.2 fun h => (nzConds_spec v).1 h hv
      rw [hany, hv]
      by_cases hp : active φ path = true <;> simp [hp]
    · have hany : (nzConds v).any (active φ) = true := (nzConds_spec v).2 hv
      rw [hany, if_neg hv]
      by_cases hp : active φ path = true <;> simp [hp] <;> omega
  | param x =>
    intro path k acc
    simp only [decomposeAux]
    split
    · simp [evalList_cons, Sub.eval, gate, levelEval]
    · simp only [evalList_cons, Sub.eval, gate, levelEval, active_cons]
      by_cases hp : active φ path = true <;> by_cases hx : 0 < φ x <;> simp [hp, hx] <;> omega

theorem decompose_eval (l : Level) (k : Nat) :
    evalList φ (decomposeAux [] k l []) = levelEval φ l + k := by
  rw [decomposeAux_eval]; simp [gate, active, evalList_nil]

theorem decomposeAux_wf (l : Level) : ∀ (path : List Name) (k : Nat) (acc : List Sub),
    (∀ a ∈ acc, a.WF) → ∀ a ∈ decomposeAux path k l acc, a.WF := by
  induction l with
  | zero =>
    intro path k acc h a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · trivial
    · exact h a ha
  | succ u ih => intro path k acc h; exact ih path (k + 1) acc h
  | max u v ihu ihv => intro path k acc h; exact ihv path k _ (ihu path k acc h)
  | imax u v ihu ihv =>
    intro path k acc h
    rw [decomposeAux]
    have : ∀ (cs : List (List Name)) (acc : List Sub), (∀ a ∈ acc, a.WF) →
        ∀ a ∈ cs.foldl (fun acc c => decomposeAux (c ++ path) k u acc) acc, a.WF := by
      intro cs
      induction cs with
      | nil => intro acc h; exact h
      | cons c cs ihc => intro acc h; exact ihc _ (ihu (c ++ path) k acc h)
    exact this _ _ (ihv path k acc h)
  | param x =>
    intro path k acc h a ha
    simp only [decomposeAux] at ha
    split at ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact contains_iff.1 ‹_›
      · exact h a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_cons_self ..
      · rcases List.mem_cons.1 ha with rfl | ha
        · trivial
        · exact h a ha

theorem eval_le {s : List Sub} {n : Nat} : evalList φ s ≤ n ↔ ∀ a ∈ s, a.eval φ ≤ n := by
  induction s with
  | nil => simp [evalList_nil]
  | cons a s ih => simp [evalList_cons, Nat.max_le, ih]

theorem le_eval {s : List Sub} {a : Sub} (h : a ∈ s) : a.eval φ ≤ evalList φ s :=
  eval_le.1 (Nat.le_refl _) a h

theorem exists_of_le_eval {s : List Sub} {c : Nat} (hc : 0 < c) (h : c ≤ evalList φ s) :
    ∃ a ∈ s, c ≤ a.eval φ := by
  induction s with
  | nil => simp [evalList_nil] at h; omega
  | cons a s ih =>
    rw [evalList_cons] at h
    by_cases h' : c ≤ a.eval φ
    · exact ⟨a, List.mem_cons_self .., h'⟩
    · obtain ⟨b, hb, hb'⟩ := ih (by omega)
      exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-! ## Soundness -/

theorem subset_active {p q : List Name} (h : subset q p = true) (hp : active φ p = true) :
    active φ q = true := by
  simp only [subset, List.all_eq_true, contains_iff] at h
  exact active_iff.2 fun i hi => active_iff.1 hp i (h i hi)

theorem dominates_sound {s t : Sub} (h : dominates s t = true) : s.eval φ ≤ t.eval φ := by
  match s, t, h with
  | .const p c, .const q c', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Sub.eval]
    by_cases hp : active φ p = true
    · rw [if_pos hp, if_pos (subset_active h.1 hp)]; exact h.2
    · rw [if_neg hp]; exact Nat.zero_le _
  | .const p c, .var q y k', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, contains_iff] at h
    obtain ⟨⟨hq, hy⟩, hc⟩ := h
    simp only [Sub.eval]
    by_cases hp : active φ p = true
    · have hq' := subset_active hq hp
      rw [if_pos hp, if_pos hq']
      have := active_iff.1 hq' _ hy
      omega
    · rw [if_neg hp]; exact Nat.zero_le _
  | .var _ _ _, .const _ _, h => simp [dominates] at h
  | .var p x k, .var q y k', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hq, rfl⟩, hk⟩ := h
    simp only [Sub.eval]
    by_cases hp : active φ p = true
    · rw [if_pos hp, if_pos (subset_active hq hp)]; omega
    · rw [if_neg hp]; exact Nat.zero_le _

theorem isZero_eval {s : Sub} (h : s.isZero = true) : s.eval φ = 0 := by
  unfold Sub.isZero at h; split at h
  · simp [Sub.eval]
  · cases h

theorem le_sound {s t : List Sub} (h : le s t = true) : evalList φ s ≤ evalList φ t := by
  refine eval_le.2 fun a ha => ?_
  simp only [le, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  rcases h a ha with hz | ⟨b, hb, hab⟩
  · rw [isZero_eval hz]; exact Nat.zero_le _
  · exact Nat.le_trans (dominates_sound hab) (le_eval hb)

end Lemmas

/-- **Soundness**: `leq l r diff = true` implies `l ≤ r + diff` at every
valuation. -/
theorem leq_sound {l r : Level} {diff : Int} (h : leq l r diff = true) (φ : Name → Nat) :
    (levelEval φ l : Int) ≤ levelEval φ r + diff := by
  unfold leq at h
  split at h
  all_goals
    have := le_sound (φ := φ) h
    rw [decompose_eval, decompose_eval] at this
    omega

/-! ## Completeness -/

/-- An upper bound on the values the sublevels of `t` take at parameters
worth at most `1`. -/
def valueBound : List Sub → Nat
  | [] => 0
  | .const _ c :: t => Max.max c (valueBound t)
  | .var _ _ k :: t => Max.max (k + 1) (valueBound t)

theorem const_le_valueBound {t : List Sub} {q : List Name} {c : Nat} (h : .const q c ∈ t) :
    c ≤ valueBound t := by
  induction t with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left ..
    · have := ih h; cases b <;> simp [valueBound] <;> omega

theorem var_le_valueBound {t : List Sub} {q : List Name} {y : Name} {k : Nat}
    (h : .var q y k ∈ t) : k + 1 ≤ valueBound t := by
  induction t with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left ..
    · have := ih h; cases b <;> simp [valueBound] <;> omega

theorem active_subset {φ : Name → Nat} {p q : List Name} (hp : ∀ i, 0 < φ i → i ∈ p)
    (hq : active φ q = true) : subset q p = true := by
  simp only [subset, List.all_eq_true, contains_iff]
  exact fun i hi => hp i (active_iff.1 hq i hi)

/-- A sublevel of `s` with no dominator in `t` is a counterexample. -/
theorem dominated_of_le {s t : List Sub} (hs : ∀ a ∈ s, a.WF) (ht : ∀ b ∈ t, b.WF)
    (h : ∀ φ, evalList φ s ≤ evalList φ t) :
    ∀ a ∈ s, a.isZero = true ∨ ∃ b ∈ t, dominates a b = true := by
  intro a ha
  match a, hs a ha with
  | .const p c, _ =>
    cases c with
    | zero => exact .inl rfl
    | succ c =>
      refine .inr ?_
      let φ : Name → Nat := fun i => if i ∈ p then 1 else 0
      have hact : active φ p = true := active_iff.2 fun i hi => by simp [φ, hi]
      have ha' : c + 1 ≤ evalList φ s := by
        have := le_eval (φ := φ) ha; simp only [Sub.eval, hact, ite_true] at this; exact this
      obtain ⟨b, hb, hb'⟩ := exists_of_le_eval (by omega) (Nat.le_trans ha' (h φ))
      have hsub : ∀ i, 0 < φ i → i ∈ p := fun i hi => by
        simp only [φ] at hi; split at hi <;> simp_all
      refine ⟨b, hb, ?_⟩
      cases b with
      | const q c' =>
        simp only [Sub.eval] at hb'
        split at hb'
        · simp [dominates, active_subset hsub ‹_›]; omega
        · omega
      | var q y k' =>
        simp only [Sub.eval] at hb'
        split at hb'
        · rename_i hq
          have hy : y ∈ q := ht _ hb
          have hyp : y ∈ p := hsub y (active_iff.1 hq y hy)
          have : φ y = 1 := by simp [φ, hyp]
          simp [dominates, active_subset hsub hq, hy]; omega
        · omega
  | .var p x k, (hx : x ∈ p) =>
    refine .inr ?_
    let N := valueBound t + 1
    let φ : Name → Nat := fun i => if i = x then N else if i ∈ p then 1 else 0
    have hsub : ∀ i, 0 < φ i → i ∈ p := fun i hi => by
      simp only [φ] at hi
      split at hi
      · subst i; exact hx
      · split at hi <;> simp_all
    have hact : active φ p = true := active_iff.2 fun i hi => by
      simp only [φ]; split <;> simp_all [N]
    have hx' : φ x = N := by simp [φ]
    have ha' : N + k ≤ evalList φ s := by
      have := le_eval (φ := φ) ha
      simp only [Sub.eval, hact, ite_true, hx'] at this; exact this
    obtain ⟨b, hb, hb'⟩ := exists_of_le_eval (by omega) (Nat.le_trans ha' (h φ))
    refine ⟨b, hb, ?_⟩
    cases b with
    | const q c' =>
      have := const_le_valueBound hb
      simp only [Sub.eval] at hb'
      split at hb' <;> omega
    | var q y k' =>
      have hk := var_le_valueBound hb
      simp only [Sub.eval] at hb'
      split at hb'
      · rename_i hq
        by_cases hyx : y = x
        · subst y; rw [hx'] at hb'
          simp [dominates, active_subset hsub hq]; omega
        · have : φ y ≤ 1 := by simp only [φ, if_neg hyx]; split <;> simp
          omega
      · omega

theorem le_complete {s t : List Sub} (hs : ∀ a ∈ s, a.WF) (ht : ∀ b ∈ t, b.WF)
    (h : ∀ φ, evalList φ s ≤ evalList φ t) : le s t = true := by
  simp only [le, List.all_eq_true, Bool.or_eq_true, List.any_eq_true]
  exact dominated_of_le hs ht h

/-- **Completeness**: if `l ≤ r + diff` at every valuation, `leq` says
so. -/
theorem leq_complete {l r : Level} {diff : Int}
    (h : ∀ φ : Name → Nat, (levelEval φ l : Int) ≤ levelEval φ r + diff) :
    leq l r diff = true := by
  unfold leq
  split
  all_goals
    refine le_complete (decomposeAux_wf _ _ _ _ (by simp)) (decomposeAux_wf _ _ _ _ (by simp))
      fun φ => ?_
    rw [decompose_eval, decompose_eval]; have := h φ; omega

/-- `leq` decides `l ≤ r + diff` at every valuation. -/
theorem leq_iff {l r : Level} {diff : Int} :
    leq l r diff = true ↔ ∀ φ : Name → Nat, (levelEval φ l : Int) ≤ levelEval φ r + diff :=
  ⟨fun h φ => leq_sound h φ, leq_complete⟩

end Ix.Kernel.Level.Geran
