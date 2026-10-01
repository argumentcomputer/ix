module

public import ConLeche.Kernel.ExprOps

public section

/-!
# Bulk instantiation equals the `instantiate1` fold (task #50)

`Expr.instantiateList` substitutes a whole replacement list in one
traversal; these lemmas identify it **unconditionally** with the chains
of `instantiate1` the checker bodies fold over spines:

* `instantiateList_nil` — the empty list is the identity;
* `instantiateList_cons` — peeling the head is one `instantiate1`
  around the tail (the head is the substitution the fold applies
  *last*, at the outermost cursor `d`);
* `instantiateList_append_one` — peeling the last entry is one
  `instantiate1` *inside* (the substitution the fold applies *first*,
  at the innermost cursor `d + vs.length`);
* `instSpine_eq_instantiateList` — the telescope-context spine
  instantiation at descending cursors is bulk instantiation of the
  reversed spine.

With these, every claim about a folded call site transports to its
bulk form by rewriting — the Model/Verify layers keep seeing the fold.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Expr

theorem instantiateList_nil : ∀ (e : Expr) (d : Nat),
    e.instantiateList [] d = e := by
  intro e
  induction e <;> intro d <;> simp [instantiateList, *] <;> omega

/-- Bulk instantiation at or above the loose-bvar bound is the
identity (task #72's scope shortcut). -/
theorem instantiateList_eq_self {vs : List Expr} :
    ∀ {e : Expr} {d : Nat}, looseBVarsBounded d e = true →
      e.instantiateList vs d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d hb
    have h1 : i < d := by
      simpa [looseBVarsBounded] using hb
    simp [instantiateList, h1]
  | _ =>
    intro d hb <;>
    simp_all [looseBVarsBounded, instantiateList, Bool.and_eq_true]

theorem instantiateList_cons :
    ∀ (vs : List Expr) (e : Expr) (v : Expr) (d : Nat),
      e.instantiateList (v :: vs) d
        = (e.instantiateList vs (d + 1)).instantiate1 v d
  | vs, .bvar j, v, d => by
    by_cases hjd : j < d
    · have hjd1 : j < d + 1 := by omega
      simp [instantiateList, instantiate1, hjd, hjd1,
        show ¬ j = d by omega, show ¬ j > d by omega]
    · by_cases hje : j = d
      · subst hje
        simp [instantiateList, hjd, instantiate1, instantiateList_nil]
      · -- j > d: either a replacement from the tail, or above the range
        obtain ⟨i, rfl⟩ : ∃ i, j = d + 1 + i := ⟨j - d - 1, by omega⟩
        have hd1 : ¬ d + 1 + i < d + 1 := by omega
        have hsub : d + 1 + i - d = i + 1 := by omega
        have hsub2 : d + 1 + i - (d + 1) = i := by omega
        by_cases hin : i < vs.length
        · -- in range: the replacement, recursively substituted
          have hin' : d + 1 + i - d < (v :: vs).length := by simp; omega
          have hin2 : d + 1 + i - (d + 1) < vs.length := by omega
          have hr : (Expr.bvar (d + 1 + i)).instantiateList vs (d + 1)
              = vs[i].instantiateList (vs.take i) (d + 1) := by
            rw [instantiateList, if_neg hd1, dif_pos hin2]
            simp only [hsub2]
          rw [instantiateList, if_neg hjd, dif_pos hin', hr]
          simp only [hsub, List.getElem_cons_succ, List.take_succ_cons]
          exact instantiateList_cons (vs.take i) vs[i] v d
        · -- above the range: lowered
          have hnin : ¬ d + 1 + i - d < (v :: vs).length := by simp; omega
          have hnin2 : ¬ d + 1 + i - (d + 1) < vs.length := by omega
          have hr : (Expr.bvar (d + 1 + i)).instantiateList vs (d + 1)
              = .bvar (d + 1 + i - vs.length) := by
            rw [instantiateList, if_neg hd1, dif_neg hnin2]
          rw [instantiateList, if_neg hjd, dif_neg hnin, hr]
          have hgt2 : d + 1 + i - vs.length > d := by omega
          simp [instantiate1, show ¬ d + 1 + i - vs.length = d by omega,
            hgt2]
          omega
  | vs, .fvar idx ty, v, d => by simp [instantiateList, instantiate1]
  | vs, .sort u, v, d => by simp [instantiateList, instantiate1]
  | vs, .const n us, v, d => by simp [instantiateList, instantiate1]
  | vs, .app f a, v, d => by
    simp only [instantiateList, instantiate1]
    rw [instantiateList_cons vs f v d, instantiateList_cons vs a v d]
  | vs, .lam ty body bi, v, d => by
    simp only [instantiateList, instantiate1]
    rw [instantiateList_cons vs ty v d, instantiateList_cons vs body v (d + 1)]
  | vs, .forallE ty body bi, v, d => by
    simp only [instantiateList, instantiate1]
    rw [instantiateList_cons vs ty v d, instantiateList_cons vs body v (d + 1)]
  | vs, .letE ty val body, v, d => by
    simp only [instantiateList, instantiate1]
    rw [instantiateList_cons vs ty v d, instantiateList_cons vs val v d,
      instantiateList_cons vs body v (d + 1)]
  | vs, .lit l, v, d => by simp [instantiateList, instantiate1]
  | vs, .proj s i e, v, d => by
    simp only [instantiateList, instantiate1]
    rw [instantiateList_cons vs e v d]
termination_by vs e => (vs.length, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp [List.length_take]; omega)
    | (apply Prod.Lex.right; simp; omega)

theorem instantiateList_append_one :
    ∀ (vs : List Expr) (e v : Expr) (d : Nat),
      e.instantiateList (vs ++ [v]) d
        = (e.instantiate1 v (d + vs.length)).instantiateList vs d
  | [], e, v, d => by
    simp [instantiateList_cons, instantiateList_nil]
  | w :: ws, e, v, d => by
    rw [List.cons_append, instantiateList_cons,
      instantiateList_append_one ws e v (d + 1), ← instantiateList_cons]
    congr 2
    simp
    omega

theorem instSpine_eq_instantiateList :
    ∀ (as : List Expr) (t : Nat) (e : Expr), as.length = t + 1 →
      Expr.instSpine as t e = e.instantiateList as.reverse 0
  | a :: as, t, e, hlen => by
    rw [instSpine]
    cases t with
    | zero =>
      have : as = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst this
      simp [instSpine, instantiateList_cons, instantiateList_nil]
    | succ t' =>
      have hlen' : as.length = t' + 1 := by simpa using hlen
      rw [show t' + 1 - 1 = t' from rfl,
        instSpine_eq_instantiateList as t' _ hlen',
        List.reverse_cons, instantiateList_append_one]
      congr 2
      simp [hlen']

end ConLeche.Expr
