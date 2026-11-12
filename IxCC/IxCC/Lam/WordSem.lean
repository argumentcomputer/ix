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
  | _ :: _ :: _ :: _ => simp [wordSem] at h

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

end IxCC.Lam
