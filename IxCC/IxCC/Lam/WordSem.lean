import IxCC.Lam.Syntax

/-! # The word primitives' meaning on literals (stage W1)

`Lam.wordSem` is `Lam.Prim.sem` of a word primitive (`Lam.Prim.word w op`): `WordOp.eval`'s
number on words below the width's size (`ofNat`'s argument any `Nat`), `none` on a decision, an
arity mismatch or a word out of range, where SrcEval's rule F6w is stuck. These are the facts the
passes below Lam use: a word primitive never returns a `Bool`, and where it returns a number its
arguments are in range and the number is `eval`'s. -/

namespace IxCC.Lam

open IxCC.Src (Width WordOp)

theorem Prim.sem_word (w : Width) (op : WordOp) (ns : List Nat) :
    (Prim.word w op).sem ns = wordSem w op ns := rfl

/-- A word primitive never returns a `Bool`. -/
theorem wordSem_ne_bool (w : Width) (op : WordOp) (ns : List Nat) (b : Bool) :
    wordSem w op ns ≠ some (.bool b) := by
  intro h
  match ns with
  | [] => simp [wordSem] at h
  | [a] =>
    simp only [wordSem] at h
    split at h
    · cases h
    · split at h <;> cases h
  | [a, c] =>
    simp only [wordSem] at h
    split at h
    · cases h
    · split at h <;> cases h
  | [a, c, d] =>
    simp only [wordSem] at h
    split at h
    · cases h
    · split at h
      · cases hr : op.eval3 w a c d with
        | none => simp [hr] at h
        | some r => simp [hr] at h
      · cases h
  | _ :: _ :: _ :: _ :: _ => simp [wordSem] at h

/-- A binary word primitive's number: both arguments in range, `eval`'s result. -/
theorem wordSem_two {w : Width} {op : WordOp} {p q n : Nat}
    (h : wordSem w op [p, q] = some (.nat n)) :
    op.arity = 2 ∧ op.isDecision = false ∧ p < w.size ∧ q < w.size ∧ n = (op.eval w p q).val := by
  simp only [wordSem] at h
  split at h
  · cases h
  · rename_i hne
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not, Bool.not_eq_true] at hne
    split at h
    · rename_i hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      simp only [Option.some.injEq, Src.PrimResult.nat.injEq] at h
      exact ⟨hne.1, hne.2, hr.1, hr.2, h.symm⟩
    · cases h

/-- A unary word primitive's number: the argument in range (any `Nat` for `ofNat`), `eval`'s
result with `0` as the unused second argument. -/
theorem wordSem_one {w : Width} {op : WordOp} {p n : Nat}
    (h : wordSem w op [p] = some (.nat n)) :
    op.arity = 1 ∧ op.isDecision = false ∧ (op = .ofNat ∨ p < w.size) ∧ n = (op.eval w p 0).val := by
  simp only [wordSem] at h
  split at h
  · cases h
  · rename_i hne
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not, Bool.not_eq_true] at hne
    split at h
    · rename_i hr
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      simp only [Option.some.injEq, Src.PrimResult.nat.injEq] at h
      exact ⟨hne.1, hne.2, hr, h.symm⟩
    · cases h

/-- A ternary limb-component word primitive's number: all three arguments in range and `eval3`'s
result. -/
theorem wordSem_three {w : Width} {op : WordOp} {a b c n : Nat}
    (h : wordSem w op [a, b, c] = some (.nat n)) :
    op.arity = 3 ∧ op.isDecision = false ∧ a < w.size ∧ b < w.size ∧ c < w.size ∧
      ∃ r, op.eval3 w a b c = some r ∧ n = r.val := by
  simp only [wordSem] at h
  split at h
  · cases h
  · rename_i hne
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not, Bool.not_eq_true] at hne
    split at h
    · rename_i hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      cases he : op.eval3 w a b c with
      | none => simp [he] at h
      | some r =>
        simp only [he, Option.map_some, Option.some.injEq, Src.PrimResult.nat.injEq] at h
        exact ⟨hne.1, hne.2, hr.1.1, hr.1.2, hr.2, r, rfl, h.symm⟩
    · cases h

/-- Every word primitive's result fits in 64 bits (`n < 2 ^ 64`). -/
theorem wordSem_lt_u64 {w : Width} {op : WordOp} {ns : List Nat} {n : Nat}
    (h : wordSem w op ns = some (.nat n)) : n < 2 ^ 64 := by
  have hle64 : ∀ w' : Width, w'.size ≤ 2 ^ 64 := fun w' => by cases w' <;> decide
  match ns with
  | [] => simp [wordSem] at h
  | [a] =>
    obtain ⟨_, hdec, ha, rfl⟩ := wordSem_one h
    cases hr : op.eval w a 0 with
    | word w' m =>
      have hm := WordOp.eval_word_lt w op a 0 ha w.size_pos w' m hr
      exact Nat.lt_of_lt_of_le hm (hle64 w')
    | nat m =>
      cases op <;> simp [WordOp.eval] at hr
      · subst hr
        have ha' : a < w.size := ha.resolve_left (by simp)
        exact Nat.lt_of_lt_of_le ha' (hle64 w)
      · split at hr <;> cases hr
    | dec d =>
      cases op <;> simp [WordOp.eval] at hr <;> try simp [WordOp.isDecision] at hdec
      split at hr <;> cases hr
  | [a, b] =>
    obtain ⟨_, hdec, ha, hb, rfl⟩ := wordSem_two h
    cases hr : op.eval w a b with
    | word w' m =>
      have hm := WordOp.eval_word_lt w op a b (.inr ha) hb w' m hr
      exact Nat.lt_of_lt_of_le hm (hle64 w')
    | nat m =>
      cases op <;> simp [WordOp.eval] at hr
      · subst hr
        exact Nat.lt_of_lt_of_le ha (hle64 w)
      · split at hr <;> cases hr
    | dec d =>
      cases op <;> simp [WordOp.eval] at hr <;> try simp [WordOp.isDecision] at hdec
      split at hr <;> cases hr
  | [a, b, c] =>
    obtain ⟨_, _, ha, hb, hc, r, hr, rfl⟩ := wordSem_three h
    cases r with
    | word w' m =>
      have hm := WordOp.eval3_word_lt w op a b c ha hb hc w' m hr
      exact Nat.lt_of_lt_of_le hm (hle64 w')
    | nat m => cases op <;> simp [WordOp.eval3] at hr <;> (split at hr <;> cases hr)
    | dec d => cases op <;> simp [WordOp.eval3] at hr <;> (split at hr <;> cases hr)
  | _ :: _ :: _ :: _ :: _ => simp [wordSem] at h

end IxCC.Lam
