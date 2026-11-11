import Aiur.Optimized.Grouping.Layout

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

theorem sum_denote (ps : List (Polynomial F)) (a : Nat → F) :
    (sum ps).denote a = (ps.map (fun p => p.denote a)).sum := by
  have fold (ps : List (Polynomial F)) (p : Polynomial F) :
      (ps.foldl plus p).denote a = p.denote a + (ps.map (fun p => p.denote a)).sum := by
    induction ps generalizing p with
    | nil => simp
    | cons q qs ih => simp [ih, plus, Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote, add_assoc]
  simpa [sum, Scalar.Circuit.ArithExpr.denote] using fold ps (.const 0)

theorem Layout.constraints_iff (g : Layout F) (a : Nat → F) :
    Satisfies g.constraints a ↔ Satisfies g.rawConstraints a := by
  constructor
  · intro valid p hp
    by_cases zero : (Polynomial.simplify p) = .const 0
    · have h := congrArg (fun q : Polynomial F => q.denote a) zero
      simpa only [Polynomial.denote_simplify, Scalar.Circuit.ArithExpr.denote] using h
    · have present : (Polynomial.simplify p) ∈ g.constraints := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
        change (!((Polynomial.simplify p) == .const 0)) = true
        cases h : ((Polynomial.simplify p) == .const 0) with
        | false => rfl
        | true => exact (zero ((Polynomial.beq_eq _ _).mp h)).elim
      simpa only [Polynomial.denote_simplify] using valid _ present
  · intro valid p hp
    obtain ⟨hp, _⟩ := List.mem_filter.mp hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [Polynomial.denote_simplify] using valid q hq

theorem Layout.member_satisfies (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a) : Satisfies m.constraints a := by
  intro p hp
  exact (g.constraints_iff a).mp valid p
    (List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, present, hp⟩))

def Member.Shape (m : Member F) : Prop :=
  m.selector = m.columns[m.sourceSelector]?.getD 0 ∧ m.sourceSelector ∈ m.privateCols

instance (m : Member F) : Decidable m.Shape := by unfold Member.Shape; infer_instance

theorem Layout.private_zero (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (shape : m.Shape) (a : Nat → F) (valid : Satisfies g.constraints a)
    (off : a m.selector = 0) (v : Nat) (hv : v ∈ m.privateCols) :
    a (m.columns[v]?.getD 0) = 0 := by
  have h := g.member_constraints m present a valid (privateZero m.sourceSelector v)
    (List.mem_append_right _ (List.mem_map.mpr ⟨v, hv, rfl⟩))
  simpa [privateZero, Scalar.Circuit.ArithExpr.denote, ← shape.1, off] using h

theorem Layout.selector_boolean (g : Layout F) (m : Member F) (present : m ∈ g.members)
    (shape : m.Shape) (a : Nat → F) (valid : Satisfies g.constraints a) :
    a m.selector = 0 ∨ a m.selector = 1 := by
  have h := g.member_constraints m present a valid (privateZero m.sourceSelector m.sourceSelector)
    (List.mem_append_right _ (List.mem_map.mpr ⟨m.sourceSelector, shape.2, rfl⟩))
  have h : (1 - a m.selector) * a m.selector = 0 := by
    simpa [privateZero, Scalar.Circuit.ArithExpr.denote, ← shape.1] using h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (sub_eq_zero.mp h).symm
  · exact Or.inl h

theorem exclusions_sound (ps : List (Polynomial F)) (a : Nat → F)
    (booleans : ∀ p ∈ ps, p.denote a = 0 ∨ p.denote a = 1)
    (valid : Satisfies (exclusions ps) a) : Exclusive (ps.map (fun p => p.denote a)) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine ⟨booleans p (by simp), ?_, ih (fun q hq => booleans q (by simp [hq])) ?_⟩
    · simpa [exclusions, Scalar.Circuit.ArithExpr.denote, sum_denote] using valid _ (List.mem_cons_self ..)
    · intro q hq
      exact valid q (List.mem_cons_of_mem _ hq)

theorem Layout.exclusive (g : Layout F) (shapes : ∀ m ∈ g.members, m.Shape)
    (a : Nat → F) (valid : Satisfies g.constraints a) :
    Exclusive (g.members.map (fun m => a m.selector)) := by
  have h := exclusions_sound (g.members.map (fun m => Polynomial.var m.selector)) a
    (by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
      exact g.selector_boolean m hm (shapes m hm) a valid)
    (by
      intro p hp
      exact (g.constraints_iff a).mp valid p (List.mem_append_right _ hp))
  simpa [Function.comp_def, Scalar.Circuit.ArithExpr.denote] using h

def selected (mode : Option Nat) (m : Member F) : F :=
  if mode = some m.selector then 1 else 0

omit [DecidableEq F] in
theorem select_member (ms : List (Member F)) (a : Nat → F)
    (valid : Exclusive (ms.map (fun m => a m.selector))) :
    (∀ m ∈ ms, a m.selector = 0) ∨
      ∃ m ∈ ms, a m.selector = 1 ∧ ∀ n ∈ ms, a n.selector = selected (some m.selector) n := by
  induction ms with
  | nil => exact Or.inl (by simp)
  | cons m ms ih =>
    rcases valid with ⟨boolean, cross, tail⟩
    rcases boolean with off | on
    · rcases ih tail with all | ⟨n, hn, active, values⟩
      · exact Or.inl (by simpa using And.intro off all)
      · refine Or.inr ⟨n, by simp [hn], active, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with same | hq
        · subst q
          have different : n.selector ≠ m.selector := by intro h; simp_all
          simp [selected, different, off]
        · exact values q hq
    · have zero : (ms.map (fun m => a m.selector)).sum = 0 := by simpa [on] using cross
      have all := exclusive_zero tail zero
      refine Or.inr ⟨m, by simp, on, ?_⟩
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · simp [selected, on]
      · have off := all _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
        have different : m.selector ≠ n.selector := by intro h; simp_all
        simp [selected, different, off]

theorem Layout.select (g : Layout F) (shapes : ∀ m ∈ g.members, m.Shape)
    (a : Nat → F) (valid : Satisfies g.constraints a) (active : g.activation.denote a = 1) :
    ∃ m ∈ g.members, a m.selector = 1 ∧ ∀ n ∈ g.members, a n.selector = selected (some m.selector) n := by
  rcases select_member g.members a (g.exclusive shapes a valid) with off | on
  · have zero : g.activation.denote a = 0 := by
      rw [Layout.activation, sum_denote]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
      exact off m hm
    exact (zero_ne_one (zero.symm.trans active)).elim
  · exact on

theorem Layout.off (g : Layout F) (shapes : ∀ m ∈ g.members, m.Shape)
    (a : Nat → F) (valid : Satisfies g.constraints a) (inactive : g.activation.denote a = 0) :
    ∀ m ∈ g.members, a m.selector = selected none m := by
  have zero : (g.members.map (fun m => a m.selector)).sum = 0 := by
    simpa [Layout.activation, sum_denote, Function.comp_def, Scalar.Circuit.ArithExpr.denote] using inactive
  intro m hm
  exact exclusive_zero (g.exclusive shapes a valid) zero _ (List.mem_map.mpr ⟨m, hm, rfl⟩)

end Aiur.Optimized.Grouping
