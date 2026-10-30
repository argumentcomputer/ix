module

public import Init.Data.Array.Lemmas
public import Init.Data.Array.OfFn
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Ix.Sharing.ParallelTable

def select (lt : α → α → Bool) (a b : α) : α :=
  if lt b a then b else a

theorem not_trans (lt : α → α → Bool)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true)
    {a b c : α} (ab : lt a b = false) (bc : lt b c = false) : lt a c = false := by
  cases ac : lt a c with
  | false => rfl
  | true =>
    by_cases same : b = c
    · subst c; simp_all
    · rcases total b c same with h | h
      · simp_all
      · have := trans a c b ac h
        simp_all

theorem select_assoc (lt : α → α → Bool)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true)
    (a b c : α) : select lt (select lt a b) c = select lt a (select lt b c) := by
  cases ba : lt b a <;> cases cb : lt c b
  · have ca := not_trans lt trans total cb ba
    simp [select, ba, cb, ca]
  · simp [select, ba, cb]
  · simp [select, ba, cb]
  · have ca := trans c b a cb ba
    simp [select, ba, cb, ca]

def choose (lt : α → α → Bool) : Option α → Option α → Option α
  | a, none => a
  | none, some b => some b
  | some a, some b => some (select lt a b)

@[simp] theorem choose_none_right (lt : α → α → Bool) (a : Option α) :
    choose lt a none = a := by cases a <;> rfl

@[simp] theorem choose_none_left (lt : α → α → Bool) (a : Option α) :
    choose lt none a = a := by cases a <;> rfl

theorem choose_assoc (lt : α → α → Bool)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true)
    (a b c : Option α) : choose lt (choose lt a b) c = choose lt a (choose lt b c) := by
  cases a <;> cases b <;> cases c <;> simp [choose, select_assoc lt trans total]

abbrev Table (α : Type) := Array (Option α)

def row (table : Table α) (index : Nat) : Option α := table[index]?.getD none

/-- Merge complete per-count tables, preserving their exact maximum length,
including trailing empty cells. No retained row is rescored. -/
def merge (lt : α → α → Bool) (left right : Table α) : Table α :=
  Array.ofFn fun index : Fin (max left.size right.size) =>
    choose lt (row left index.val) (row right index.val)

@[simp] theorem merge_size (lt : α → α → Bool) (left right : Table α) :
    (merge lt left right).size = max left.size right.size := by simp [merge]

theorem row_merge (lt : α → α → Bool) (left right : Table α) (index : Nat) :
    row (merge lt left right) index = choose lt (row left index) (row right index) := by
  by_cases inside : index < max left.size right.size
  · simp [row, merge, inside]
  · have hl : ¬ index < left.size := by omega
    have hr : ¬ index < right.size := by omega
    simp [row, merge, inside, hl, hr, choose]

theorem ext_rows {left right : Table α} (size : left.size = right.size)
    (rows : ∀ index, row left index = row right index) : left = right := by
  apply Array.ext size
  intro index leftBound rightBound
  have same := rows index
  simpa [row, leftBound, rightBound] using same

@[simp] theorem merge_empty_right (lt : α → α → Bool) (left : Table α) :
    merge lt left #[] = left := by
  apply ext_rows (by simp)
  intro index
  rw [row_merge]
  simp [row]

@[simp] theorem merge_empty_left (lt : α → α → Bool) (right : Table α) :
    merge lt #[] right = right := by
  apply ext_rows (by simp)
  intro index
  rw [row_merge]
  simp [row]

theorem merge_assoc (lt : α → α → Bool)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true)
    (a b c : Table α) : merge lt (merge lt a b) c = merge lt a (merge lt b c) := by
  apply ext_rows (by simp [Nat.max_assoc])
  intro index
  simp only [row_merge]
  exact choose_assoc lt trans total _ _ _

end Ix.Sharing.ParallelTable
