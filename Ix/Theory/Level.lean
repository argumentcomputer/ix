/-
  Ix.Theory.Level: Universe level expressions for the typing judgment.

  Ported from lean4lean's Lean4Lean.Theory.VLevel (VLevel → SLevel).
  Defines SLevel, well-formedness, semantic evaluation, equivalence,
  ordering, and level substitution (inst).
-/

namespace Ix.Theory

-- Helpers (not in Lean 4.26.0 stdlib)
private theorem funext_iff {f g : α → β} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, funext⟩

private theorem forall_and {p q : α → Prop} : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun ⟨hp, hq⟩ x => ⟨hp x, hq x⟩⟩

/-- Impredicative max: `imax n m = if m = 0 then 0 else max n m`. -/
def Nat.imax (n m : Nat) : Nat :=
  if m = 0 then 0 else Nat.max n m

/-- Pointwise relation on two lists of the same length. -/
inductive SForall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : SForall₂ R [] []
  | cons : R a b → SForall₂ R l₁ l₂ → SForall₂ R (a :: l₁) (b :: l₂)

theorem SForall₂.rfl (h : ∀ a (_ : a ∈ l), R a a) : SForall₂ R l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    exact .cons (h a (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

inductive SLevel where
  | zero  : SLevel
  | succ  : SLevel → SLevel
  | max   : SLevel → SLevel → SLevel
  | imax  : SLevel → SLevel → SLevel
  | param : Nat → SLevel
  deriving Inhabited, DecidableEq, Repr

namespace SLevel

instance : BEq SLevel := ⟨fun a b => decide (a = b)⟩

variable (n : Nat) in
def WF : SLevel → Prop
  | .zero => True
  | .succ l => l.WF
  | .max l₁ l₂ => l₁.WF ∧ l₂.WF
  | .imax l₁ l₂ => l₁.WF ∧ l₂.WF
  | .param i => i < n

instance decidable_WF : ∀ {l}, Decidable (WF n l)
  | .zero => instDecidableTrue
  | .succ l => @decidable_WF _ l
  | .max .. | .imax .. => @instDecidableAnd _ _ decidable_WF decidable_WF
  | .param _ => Nat.decLt ..

variable (ls : List Nat) in
def eval : SLevel → Nat
  | .zero => 0
  | .succ l => l.eval + 1
  | .max l₁ l₂ => l₁.eval.max l₂.eval
  | .imax l₁ l₂ => Nat.imax l₁.eval l₂.eval
  | .param i => ls.getD i 0

protected def LE (a b : SLevel) : Prop := ∀ ls, a.eval ls ≤ b.eval ls

instance : LE SLevel := ⟨SLevel.LE⟩

theorem le_refl (a : SLevel) : a ≤ a := fun _ => Nat.le_refl _
theorem le_trans {a b c : SLevel} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun _ => Nat.le_trans (h1 _) (h2 _)

theorem zero_le : zero ≤ a := fun _ => Nat.zero_le _

theorem le_succ : a ≤ succ a := fun _ => Nat.le_succ _

theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := fun _ => Nat.succ_le_succ (h _)

theorem le_max_left : a ≤ max a b := fun _ => Nat.le_max_left ..
theorem le_max_right : b ≤ max a b := fun _ => Nat.le_max_right ..

protected def Equiv (a b : SLevel) : Prop := a.eval = b.eval

instance : HasEquiv SLevel := ⟨SLevel.Equiv⟩

theorem equiv_def' {a b : SLevel} : a ≈ b ↔ a.eval = b.eval := .rfl
theorem equiv_def {a b : SLevel} : a ≈ b ↔ ∀ ls, a.eval ls = b.eval ls := funext_iff

theorem equiv_congr_left {a b c : SLevel} (h : a ≈ b) : a ≈ c ↔ b ≈ c :=
  iff_of_eq (congrArg (· = _) h)

theorem equiv_congr_right {a b c : SLevel} (h : a ≈ b) : c ≈ a ↔ c ≈ b :=
  iff_of_eq (congrArg (_ = ·) h)

theorem le_antisymm_iff {a b : SLevel} : a ≈ b ↔ a ≤ b ∧ b ≤ a :=
  equiv_def.trans <| (forall_congr' fun _ => Nat.le_antisymm_iff).trans forall_and

theorem succ_congr {a b : SLevel} (h : a ≈ b) : succ a ≈ succ b := by
  simpa [equiv_def, eval] using h

theorem succ_congr_iff {a b : SLevel} : succ a ≈ succ b ↔ a ≈ b := by
  simp [equiv_def, eval]

theorem max_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : max a₁ a₂ ≈ max b₁ b₂ := by
  simp_all [equiv_def, eval]

theorem imax_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : imax a₁ a₂ ≈ imax b₁ b₂ := by
  simp only [equiv_def, eval] at *
  intro ls; simp [Nat.imax]; split <;> simp_all

theorem max_comm : max a b ≈ max b a := by simp [equiv_def, eval, Nat.max_comm]

theorem LE.max_eq_left (h : b.LE a) : max a b ≈ a := by
  simp [equiv_def, eval, Nat.max_eq_left (h _)]

theorem LE.max_eq_right (h : a.LE b) : max a b ≈ b := by
  simp [equiv_def, eval, Nat.max_eq_right (h _)]

theorem max_self : max a a ≈ a := by simp [equiv_def, eval]

theorem zero_imax : imax zero a ≈ a := by
  simp only [equiv_def, eval]; intro ls
  simp only [Nat.imax]; split
  · next h => exact h.symm
  · exact Nat.max_eq_right (Nat.zero_le _)

theorem imax_zero : imax a zero ≈ zero := by simp [equiv_def, eval, Nat.imax]

theorem imax_self : imax a a ≈ a := by
  simp only [equiv_def, eval]; intro ls
  simp only [Nat.imax]; split
  · next h => exact h.symm
  · exact Nat.max_self _

theorem imax_eq_zero : imax a b ≈ zero ↔ b ≈ zero := by
  constructor
  · intro H
    simp only [equiv_def, eval] at *
    intro ls
    have := H ls
    simp only [Nat.imax] at this
    split at this
    · assumption
    · simp [Nat.max] at this; exact absurd this.2 ‹_›
  · intro H
    simp only [equiv_def, eval] at *
    intro ls; simp [Nat.imax, H ls]

def IsNeverZero (a : SLevel) : Prop := ∀ ls, a.eval ls ≠ 0

theorem IsNeverZero.imax_eq_max (h : IsNeverZero b) : imax a b ≈ max a b := by
  simp only [equiv_def, eval, IsNeverZero] at *
  intro ls; simp [Nat.imax, h ls]

variable (ls : List SLevel) in
def inst : SLevel → SLevel
  | .zero => .zero
  | .succ l => .succ l.inst
  | .max l₁ l₂ => .max l₁.inst l₂.inst
  | .imax l₁ l₂ => .imax l₁.inst l₂.inst
  | .param i => ls.getD i .zero

theorem inst_inst {l : SLevel} : (l.inst ls).inst ls' = l.inst (ls.map (inst ls')) := by
  induction l <;> simp [inst, *, List.getD_eq_getElem?_getD, List.getElem?_map]
  case param n => cases ls[n]? <;> simp [inst]

def params (n : Nat) : List SLevel := (List.range n).map .param

@[simp] theorem params_length {n : Nat} : (params n).length = n := by simp [params]

theorem params_wf {n : Nat} : ∀ ⦃l⦄, l ∈ params n → l.WF n := by simp [params, WF]

theorem inst_id {l : SLevel} (h : l.WF u) : l.inst (params u) = l := by
  induction l <;> simp_all [params, inst, WF, List.getD_eq_getElem?_getD]

theorem inst_map_id (h : ls.length = n) : (params n).map (inst ls) = ls := by
  subst n; simp [params]; apply List.ext_get (by simp)
  intro i _ _; simp [inst]; rw [List.getElem?_eq_getElem]; rfl

theorem eval_inst {l : SLevel} : (l.inst ls).eval ns = l.eval (ls.map (eval ns)) := by
  induction l <;> simp [eval, inst, *, List.getD_eq_getElem?_getD]
  case param n => cases ls[n]? <;> simp [eval]

theorem WF.inst {l : SLevel} (H : ∀ l ∈ ls, l.WF n) : (l.inst ls).WF n := by
  induction l with
  | zero => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | param i =>
    simp [SLevel.inst, List.getD_eq_getElem?_getD]
    cases e : ls[i]? with
    | none => trivial
    | some => exact H _ (List.mem_of_getElem? e)

theorem id_WF : ∀ l ∈ (List.range u).map param, l.WF u := by simp [WF]

theorem inst_congr {l : SLevel} (h1 : l ≈ l') (h2 : SForall₂ (·≈·) ls ls') :
    l.inst ls ≈ l'.inst ls' := by
  simp [equiv_def, eval_inst, ← equiv_def.1 h1]
  intro ns; congr 1
  induction h2 with
  | nil => rfl
  | cons h2 => simp [*, equiv_def.1 h2]

theorem inst_congr_l {l : SLevel} (h1 : l ≈ l') : l.inst ls ≈ l'.inst ls :=
  inst_congr h1 <| .rfl fun _ _ => rfl

end SLevel

-- Sanity checks
#guard SLevel.eval [3] (.succ (.param 0)) == 4
#guard SLevel.eval [] (.imax (.succ .zero) .zero) == 0
#guard SLevel.eval [] (.max (.succ .zero) (.succ (.succ .zero))) == 2
#guard SLevel.inst [.succ .zero] (.param 0) == .succ .zero
#guard SLevel.inst [.zero, .succ .zero] (.max (.param 0) (.param 1)) ==
    .max .zero (.succ .zero)

end Ix.Theory
