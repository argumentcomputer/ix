/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.VLevel

/-! # Géran's sublevels and a complete universe-level order

Yoan Géran, "A Canonical Form for Universe Levels in Impredicative Type Theory",
decomposes a level into *sublevels*: `C(p, c)` is `c` when every parameter in
the condition set `p` is nonzero and `0` otherwise, and `V(p, x, k)` is `x + k`
under the same condition, with `x ∈ p`. A level is the maximum of its
sublevels, and (Theorem 39) `l₁ ≤ l₂` holds under every valuation exactly when
each sublevel of `l₁` is dominated by some sublevel of `l₂`.

`decompose` is the decomposition of `Ix.Tc.normalizeAux` (itself mirroring the
Rust kernel's `level.rs` and Lean4Lean's `Level.Normalize.normalizeAux`), and
`le` is its `coversConst`/`coversVar` comparison, one dominator per sublevel.
Neither the map of nodes nor subsumption is needed here: equivalence is decided
as `le` both ways, not by comparing canonical forms, so the sublevels stay a
flat list. This also avoids a subsumption slip that Ix.Tc and the Rust kernel
share (the constant bound is taken from the node's own variables rather than
the dominating node's), which is sound but makes their equivalence incomplete.

`le_sound` and `le_complete` state that `le` decides the pointwise order. -/

namespace Ix.Kernel.Certified.LevelNorm

/-- A sublevel: `const p c` is Géran's `C(p, c)` and `var p x k` is
`V(p, x, k)`. -/
inductive Sub where
  | const (path : List Nat) (c : Nat)
  | var (path : List Nat) (x : Nat) (k : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Sub

def path : Sub → List Nat
  | .const p _ | .var p _ _ => p

/-- A variable sublevel's variable is in its own condition set. -/
def WF : Sub → Prop
  | .const .. => True
  | .var p x _ => x ∈ p

end Sub

section Eval
variable (ls : List Nat)

/-- Every parameter of the condition set is nonzero. -/
def active (path : List Nat) : Bool := path.all fun i => 0 < ls.getD i 0

def Sub.eval : Sub → Nat
  | .const p c => if active ls p then c else 0
  | .var p x k => if active ls p then ls.getD x 0 + k else 0

def eval : List Sub → Nat
  | [] => 0
  | s :: l => max (s.eval ls) (eval l)

end Eval

/-! ## Decomposition -/

/-- The sublevels of `l + k` under the condition set `path`, prepended to
`acc`. -/
def decomposeAux (path : List Nat) (k : Nat) (l : VLevel) (acc : List Sub) : List Sub :=
  match l with
  | .zero => .const path k :: acc
  | .succ u => decomposeAux path (k + 1) u acc
  | .max u v => decomposeAux path k v (decomposeAux path k u acc)
  | .imax _ .zero => .const path k :: acc
  | .imax u (.succ v) => decomposeAux path (k + 1) v (decomposeAux path k u acc)
  | .imax u (.max v w) =>
    decomposeAux path k (.imax u w) (decomposeAux path k (.imax u v) acc)
  | .imax u (.imax v w) =>
    decomposeAux path k (.imax v w) (decomposeAux path k (.imax u w) acc)
  | .imax u (.param x) =>
    if x ∈ path then decomposeAux path k u (.var path x k :: acc)
    else decomposeAux (x :: path) k u (.var (x :: path) x k :: .const path k :: acc)
  | .param x =>
    if x ∈ path then .var path x k :: acc
    else .var (x :: path) x k :: .const path k :: acc
termination_by sizeOf l
decreasing_by all_goals simp_wf; all_goals omega

def decompose (l : VLevel) : List Sub := decomposeAux [] 0 l []

/-! ## The order -/

def subset (p q : List Nat) : Bool := p.all (· ∈ q)

/-- `C(p, 0)` is `0` under every valuation. -/
def Sub.isZero : Sub → Bool
  | .const _ 0 => true
  | _ => false

/-- `t` dominates `s` under every valuation. -/
def dominates : Sub → Sub → Bool
  | .const p c, .const q c' => subset q p && c ≤ c'
  | .const p c, .var q y k' => subset q p && y ∈ q && c ≤ k' + 1
  | .var _ _ _, .const _ _ => false
  | .var p x k, .var q y k' => subset q p && x == y && k ≤ k'

/-- Every sublevel of `s` is zero or dominated by a sublevel of `t`. -/
def le (s t : List Sub) : Bool := s.all fun a => a.isZero || t.any (dominates a)

/-- Pointwise order of levels, decided on their sublevels. -/
def levelLe (a b : VLevel) : Bool := le (decompose a) (decompose b)

/-! ## Evaluation lemmas -/

section
variable {ls : List Nat}

theorem active_iff {p : List Nat} : active ls p = true ↔ ∀ i ∈ p, 0 < ls.getD i 0 := by
  simp [active]

theorem active_cons {x : Nat} {p : List Nat} :
    active ls (x :: p) = (decide (0 < ls.getD x 0) && active ls p) := by
  simp [active]

theorem active_cons_iff {x : Nat} {p : List Nat} :
    active ls (x :: p) = true ↔ 0 < ls.getD x 0 ∧ active ls p = true := by
  simp only [active, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]

theorem eval_le {s : List Sub} {n : Nat} : eval ls s ≤ n ↔ ∀ a ∈ s, a.eval ls ≤ n := by
  induction s with
  | nil => simp [eval]
  | cons a s ih => simp [eval, Nat.max_le, ih]

theorem le_eval {s : List Sub} {a : Sub} (h : a ∈ s) : a.eval ls ≤ eval ls s :=
  eval_le.1 (Nat.le_refl _) a h

theorem exists_of_le_eval {s : List Sub} {c : Nat} (hc : 0 < c) (h : c ≤ eval ls s) :
    ∃ a ∈ s, c ≤ a.eval ls := by
  induction s with
  | nil => simp [eval] at h; omega
  | cons a s ih =>
    simp only [eval] at h
    by_cases h' : c ≤ a.eval ls
    · exact ⟨a, List.mem_cons_self .., h'⟩
    · obtain ⟨b, hb, hb'⟩ := ih (by omega)
      exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

theorem active_mem {p : List Nat} {x : Nat} (h : active ls p = true) (hx : x ∈ p) :
    0 < ls.getD x 0 :=
  active_iff.1 h x hx

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

/-- The value of `n` under a condition set. -/
def gate (ls : List Nat) (p : List Nat) (n : Nat) : Nat := if active ls p then n else 0

theorem eval_const {p : List Nat} {c : Nat} {acc : List Sub} :
    eval ls (.const p c :: acc) = max (gate ls p c) (eval ls acc) := rfl

theorem eval_var {p : List Nat} {x k : Nat} {acc : List Sub} :
    eval ls (.var p x k :: acc) = max (gate ls p (ls.getD x 0 + k)) (eval ls acc) := rfl

theorem natIMax_zero_right (a : Nat) : VLevel.natIMax a 0 = 0 := rfl

theorem natIMax_pos {a b : Nat} (h : 0 < b) : VLevel.natIMax a b = max a b := by
  simp only [VLevel.natIMax, nat_max_eq, Nat.pos_iff_ne_zero.1 h, ite_false]

theorem natIMax_succ (a b : Nat) : VLevel.natIMax a (b + 1) = max a (b + 1) :=
  natIMax_pos (Nat.succ_pos _)

theorem natIMax_max (a b c : Nat) :
    VLevel.natIMax a (max b c) = max (VLevel.natIMax a b) (VLevel.natIMax a c) := by
  by_cases hb : b = 0 <;> by_cases hc : c = 0
  · subst hb hc; rfl
  · subst hb; rw [natIMax_pos (by omega), natIMax_zero_right, natIMax_pos (by omega)]; omega
  · subst hc; rw [natIMax_pos (by omega), natIMax_zero_right, natIMax_pos (by omega)]; omega
  · rw [natIMax_pos (by omega), natIMax_pos (by omega), natIMax_pos (by omega)]; omega

theorem natIMax_imax (a b c : Nat) :
    VLevel.natIMax a (VLevel.natIMax b c) =
      max (VLevel.natIMax a c) (VLevel.natIMax b c) := by
  by_cases hc : c = 0
  · subst hc; simp only [natIMax_zero_right]; rfl
  · rw [natIMax_pos (b := c) (by omega), natIMax_pos (b := c) (by omega)]
    rw [natIMax_pos (by omega)]; omega

theorem decomposeAux_eval (path : List Nat) (k : Nat) (l : VLevel) (acc : List Sub) :
    eval ls (decomposeAux path k l acc) = max (gate ls path (l.eval ls + k)) (eval ls acc) := by
  fun_induction decomposeAux path k l acc <;>
    simp only [*, eval_const, eval_var, VLevel.eval, nat_max_eq, natIMax_zero_right,
      natIMax_succ, natIMax_max, natIMax_imax]
  case case8 path k acc u x hx _ =>
    simp only [gate]
    by_cases hact : active ls path = true
    · rw [natIMax_pos (active_mem hact hx)]; simp only [hact, ite_true]; omega
    · simp only [hact, Bool.false_eq_true, ite_false]; omega
  case case9 path k acc u x _ _ =>
    simp only [gate]
    by_cases hact : active ls path = true <;> by_cases h0 : 0 < ls.getD x 0
    · have hx : active ls (x :: path) = true := active_cons_iff.2 ⟨h0, hact⟩
      rw [natIMax_pos h0]; simp only [hx, hact, ite_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => h0 (active_cons_iff.1 h).1
      rw [show ls.getD x 0 = 0 by omega, natIMax_zero_right]
      simp only [hx, hact, ite_true, ite_false, Bool.false_eq_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => hact (active_cons_iff.1 h).2
      simp only [hx, hact, ite_false, Bool.false_eq_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => hact (active_cons_iff.1 h).2
      simp only [hx, hact, ite_false, Bool.false_eq_true]; omega
  case case11 path k acc x _ =>
    simp only [gate]
    by_cases hact : active ls path = true <;> by_cases h0 : 0 < ls.getD x 0
    · have hx : active ls (x :: path) = true := active_cons_iff.2 ⟨h0, hact⟩
      simp only [hx, hact, ite_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => h0 (active_cons_iff.1 h).1
      simp only [hx, hact, ite_true, ite_false, Bool.false_eq_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => hact (active_cons_iff.1 h).2
      simp only [hx, hact, ite_false, Bool.false_eq_true]; omega
    · have hx : active ls (x :: path) = false :=
        Bool.eq_false_iff.2 fun h => hact (active_cons_iff.1 h).2
      simp only [hx, hact, ite_false, Bool.false_eq_true]; omega
  all_goals simp only [gate]; split <;> omega

theorem decompose_eval (l : VLevel) : eval ls (decompose l) = l.eval ls := by
  simp [decompose, decomposeAux_eval, eval, gate, active]

end

/-! ## Well-formedness of the decomposition -/

theorem decomposeAux_wf (path : List Nat) (k : Nat) (l : VLevel) (acc : List Sub) :
    (∀ a ∈ acc, a.WF) → ∀ a ∈ decomposeAux path k l acc, a.WF := by
  fun_induction decomposeAux path k l acc
  case case1 | case4 =>
    intro h a ha; rcases List.mem_cons.1 ha with rfl | ha
    · trivial
    · exact h a ha
  case case2 ih => exact ih
  case case3 ih1 ih2 | case5 ih1 ih2 | case6 ih1 ih2 | case7 ih1 ih2 =>
    exact fun h => ih2 (ih1 h)
  case case8 hx ih =>
    intro h; refine ih fun a ha => ?_; rcases List.mem_cons.1 ha with rfl | ha
    · exact hx
    · exact h a ha
  case case9 ih =>
    intro h; refine ih fun a ha => ?_
    rcases List.mem_cons.1 ha with rfl | ha
    · exact List.mem_cons_self ..
    · rcases List.mem_cons.1 ha with rfl | ha
      · trivial
      · exact h a ha
  case case10 hx =>
    intro h a ha; rcases List.mem_cons.1 ha with rfl | ha
    · exact hx
    · exact h a ha
  case case11 =>
    intro h a ha; rcases List.mem_cons.1 ha with rfl | ha
    · exact List.mem_cons_self ..
    · rcases List.mem_cons.1 ha with rfl | ha
      · trivial
      · exact h a ha

theorem decompose_wf (l : VLevel) : ∀ a ∈ decompose l, a.WF :=
  decomposeAux_wf _ _ _ _ (by simp)

/-! ## Soundness -/

section
variable {ls : List Nat}

theorem subset_active {p q : List Nat} (h : subset q p = true) (hp : active ls p = true) :
    active ls q = true := by
  simp only [subset, List.all_eq_true, decide_eq_true_eq] at h
  exact active_iff.2 fun i hi => active_iff.1 hp i (h i hi)

theorem dominates_sound {s t : Sub} (h : dominates s t = true) : s.eval ls ≤ t.eval ls := by
  match s, t, h with
  | .const p c, .const q c', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Sub.eval]
    by_cases hp : active ls p = true
    · rw [ite_eq_left hp, ite_eq_left (subset_active h.1 hp)]; exact h.2
    · rw [ite_eq_right hp]; exact Nat.zero_le _
  | .const p c, .var q y k', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hq, hy⟩, hc⟩ := h
    simp only [Sub.eval]
    by_cases hp : active ls p = true
    · have hq' := subset_active hq hp
      rw [ite_eq_left hp, ite_eq_left hq']
      have := active_iff.1 hq' _ hy
      omega
    · rw [ite_eq_right hp]; exact Nat.zero_le _
  | .var _ _ _, .const _ _, h => simp [dominates] at h
  | .var p x k, .var q y k', h =>
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hq, rfl⟩, hk⟩ := h
    simp only [Sub.eval]
    by_cases hp : active ls p = true
    · rw [ite_eq_left hp, ite_eq_left (subset_active hq hp)]; omega
    · rw [ite_eq_right hp]; exact Nat.zero_le _

theorem isZero_eval {s : Sub} (h : s.isZero = true) : s.eval ls = 0 := by
  unfold Sub.isZero at h; split at h
  · simp [Sub.eval]
  · cases h

theorem le_sound' {s t : List Sub} (h : le s t = true) : eval ls s ≤ eval ls t := by
  refine eval_le.2 fun a ha => ?_
  simp only [le, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  rcases h a ha with hz | ⟨b, hb, hab⟩
  · rw [isZero_eval hz]; exact Nat.zero_le _
  · exact Nat.le_trans (dominates_sound hab) (le_eval hb)

end

theorem levelLe_sound {a b : VLevel} (h : levelLe a b = true) (ls : List Nat) :
    a.eval ls ≤ b.eval ls := by
  rw [← decompose_eval (ls := ls) a, ← decompose_eval (ls := ls) b]
  exact le_sound' h

/-! ## Completeness -/

/-- A valuation given by a function on the parameters below `bound`. -/
def valuation (f : Nat → Nat) (bound : Nat) : List Nat := (List.range bound).map f

theorem valuation_getD {f : Nat → Nat} {bound i : Nat} (hf : bound ≤ i → f i = 0) :
    (valuation f bound).getD i 0 = f i := by
  simp only [valuation, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < bound
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; exact (hf (by omega)).symm

/-- One more than every parameter in a condition set. -/
def pathBound (p : List Nat) : Nat := p.foldr (fun i n => max (i + 1) n) 0

theorem lt_pathBound {p : List Nat} {i : Nat} (h : i ∈ p) : i < pathBound p := by
  induction p with
  | nil => cases h
  | cons a p ih =>
    simp only [pathBound, List.foldr] at *
    rcases List.mem_cons.1 h with rfl | h
    · have := Nat.le_max_left (i + 1) (List.foldr (fun i n => max (i + 1) n) 0 p); omega
    · have := ih h
      have := Nat.le_max_right (a + 1) (List.foldr (fun i n => max (i + 1) n) 0 p); omega

/-- An upper bound on the values the sublevels of `t` can take at parameters
worth at most `1`. -/
def valueBound : List Sub → Nat
  | [] => 0
  | .const _ c :: t => max c (valueBound t)
  | .var _ _ k :: t => max (k + 1) (valueBound t)

theorem const_le_valueBound {t : List Sub} {q : List Nat} {c : Nat} (h : .const q c ∈ t) :
    c ≤ valueBound t := by
  induction t with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [valueBound]; omega
    · have := ih h; cases b <;> simp [valueBound] <;> omega

theorem var_le_valueBound {t : List Sub} {q : List Nat} {y k : Nat} (h : .var q y k ∈ t) :
    k + 1 ≤ valueBound t := by
  induction t with
  | nil => cases h
  | cons b t ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [valueBound]; omega
    · have := ih h; cases b <;> simp [valueBound] <;> omega

theorem active_subset {ls p q : List Nat} (hp : ∀ i, 0 < ls.getD i 0 → i ∈ p)
    (hq : active ls q = true) : subset q p = true := by
  simp only [subset, List.all_eq_true, decide_eq_true_eq]
  exact fun i hi => hp i (active_iff.1 hq i hi)

theorem dominated_of_le {s t : List Sub} (hs : ∀ a ∈ s, a.WF) (ht : ∀ b ∈ t, b.WF)
    (h : ∀ ls, eval ls s ≤ eval ls t) :
    ∀ a ∈ s, a.isZero = true ∨ ∃ b ∈ t, dominates a b = true := by
  intro a ha
  match a, hs a ha with
  | .const p c, _ =>
    cases c with
    | zero => exact .inl rfl
    | succ c =>
      refine .inr ?_
      let f := fun i => if i ∈ p then 1 else 0
      let ls := valuation f (pathBound p)
      have hls : ∀ i, ls.getD i 0 = f i := fun i =>
        valuation_getD fun hi => by
          simp only [f]; split
          · have := lt_pathBound ‹_›; omega
          · rfl
      have hact : active ls p = true := active_iff.2 fun i hi => by rw [hls]; simp [f, hi]
      have ha' : c + 1 ≤ eval ls s := by
        have := le_eval (ls := ls) ha; simp only [Sub.eval, hact, ite_true] at this; exact this
      obtain ⟨b, hb, hb'⟩ := exists_of_le_eval (by omega) (Nat.le_trans ha' (h ls))
      have hsub : ∀ i, 0 < ls.getD i 0 → i ∈ p := fun i hi => by
        rw [hls] at hi; simp only [f] at hi; split at hi <;> simp_all
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
          have : ls.getD y 0 = 1 := by rw [hls]; simp [f, hyp]
          simp [dominates, active_subset hsub hq, hy]; omega
        · omega
  | .var p x k, (hx : x ∈ p) =>
    refine .inr ?_
    let N := valueBound t + 1
    let f := fun i => if i = x then N else if i ∈ p then 1 else 0
    let ls := valuation f (pathBound p)
    have hls : ∀ i, ls.getD i 0 = f i := fun i =>
      valuation_getD fun hi => by
        simp only [f]; split
        · subst i; have := lt_pathBound hx; omega
        · split
          · have := lt_pathBound ‹_›; omega
          · rfl
    have hsub : ∀ i, 0 < ls.getD i 0 → i ∈ p := fun i hi => by
      rw [hls] at hi; simp only [f] at hi
      split at hi
      · subst i; exact hx
      · split at hi <;> simp_all
    have hact : active ls p = true := active_iff.2 fun i hi => by
      rw [hls]; simp only [f]; split <;> simp_all [N]
    have hx' : ls.getD x 0 = N := by rw [hls]; simp [f]
    have ha' : N + k ≤ eval ls s := by
      have := le_eval (ls := ls) ha
      simp only [Sub.eval, hact, ite_true, hx'] at this; exact this
    obtain ⟨b, hb, hb'⟩ := exists_of_le_eval (by omega) (Nat.le_trans ha' (h ls))
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
        · have : ls.getD y 0 ≤ 1 := by rw [hls]; simp only [f, ite_eq_right hyx]; split <;> simp
          omega
      · omega

theorem le_complete {s t : List Sub} (hs : ∀ a ∈ s, a.WF) (ht : ∀ b ∈ t, b.WF)
    (h : ∀ ls, eval ls s ≤ eval ls t) : le s t = true := by
  simp only [le, List.all_eq_true, Bool.or_eq_true, List.any_eq_true]
  exact dominated_of_le hs ht h

theorem levelLe_complete {a b : VLevel} (h : ∀ ls, a.eval ls ≤ b.eval ls) :
    levelLe a b = true :=
  le_complete (decompose_wf a) (decompose_wf b) fun ls => by
    rw [decompose_eval, decompose_eval]; exact h ls

/-- `levelLe` decides the pointwise order of levels. -/
theorem levelLe_iff {a b : VLevel} : levelLe a b = true ↔ ∀ ls, a.eval ls ≤ b.eval ls :=
  ⟨fun h ls => levelLe_sound h ls, levelLe_complete⟩

end Ix.Kernel.Certified.LevelNorm
