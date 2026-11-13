import IxVMRefinement.Core.Steps.Whnf

/-! # Shared lemmas of the `KernelWhnf` step lemmas

* **The never-zero test is semantic** (`isNeverZero_congr`, `isNeverZero_of_eval`): it is the
  zero-ness datum's `never` (`Level.isNeverZero_eq_isNever`), and the datum is a function of the
  level's values (`zeronessOf_congr`). So it survives substitution (`isNeverZero_subst`) and the
  circuit's positional instantiation (`substLevel`) agrees with the kernel's
  `Level.subst (List.range n)` at semantically equal levels (`lvEq_subst_range`).
* **Instantiating a binder** (`instantiateList_lam`, `instantiateList_forallE`): one equation of
  `Expr.instantiateList` each. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

namespace WhnfAux

/-! ## The never-zero test -/

/-- Semantically equal levels have the same never-zero answer. -/
theorem isNeverZero_congr {u v : KLevel} (h : LvEq u v) : u.isNeverZero = v.isNeverZero := by
  rw [Ix.Kernel.Level.isNeverZero_eq_isNever, Ix.Kernel.Level.isNeverZero_eq_isNever,
    zeronessOf_congr h]

/-- A level nonzero at every assignment passes the never-zero test. -/
theorem isNeverZero_of_eval {l : KLevel} (h : ∀ φ, Ix.Kernel.Level.eval φ l ≠ 0) :
    l.isNeverZero = true := by
  have hz : l.zeronessOf = .never := Ix.Kernel.PropWhen.eq_of_holds fun φ => by
    rw [Ix.Kernel.PropWhen.zeronessOf_sound, Ix.Kernel.PropWhen.holds_never]
    simpa using h φ
  rw [Ix.Kernel.Level.isNeverZero_eq_isNever, hz]
  exact Ix.Kernel.PropWhen.isNever_never

/-- A substitution keeps a never-zero level never zero. -/
theorem isNeverZero_subst {l : KLevel} (h : l.isNeverZero = true) (ks : List Ix.Kernel.LevelParam)
    (vs : List KLevel) : (Ix.Kernel.Level.subst ks vs l).isNeverZero = true :=
  isNeverZero_of_eval fun φ => by
    rw [Ix.Kernel.Level.eval_subst]
    exact IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero h _

/-- Pointwise equal level lists have the same length. -/
theorem evalEqList_length {φ : Ix.Kernel.LevelParam → Nat} :
    ∀ (us vs : List KLevel), Ix.Kernel.Level.EvalEqList φ us vs → us.length = vs.length
  | [], [], _ => rfl
  | _ :: us, _ :: vs, h => by
    simp only [Ix.Kernel.Level.EvalEqList] at h
    simp [evalEqList_length us vs h.2]
  | [], _ :: _, h => by simp [Ix.Kernel.Level.EvalEqList] at h
  | _ :: _, [], h => by simp [Ix.Kernel.Level.EvalEqList] at h

/-- Substituting pointwise equal levels gives the same assignment. -/
theorem substFn_congr (φ : Ix.Kernel.LevelParam → Nat) :
    ∀ (ks : List Ix.Kernel.LevelParam) (us vs : List KLevel), Ix.Kernel.Level.EvalEqList φ us vs →
      Ix.Kernel.Level.substFn φ ks us = Ix.Kernel.Level.substFn φ ks vs
  | [], [], [], _ => rfl
  | [], _ :: _, _ :: _, _ => by funext n; simp [Ix.Kernel.Level.substFn]
  | _ :: _, [], [], _ => rfl
  | k :: ks, u :: us, v :: vs, h => by
    simp only [Ix.Kernel.Level.EvalEqList] at h
    funext n
    simp only [Ix.Kernel.Level.substFn]
    rw [h.1, substFn_congr φ ks us vs h.2]
  | _, [], _ :: _, h => by simp [Ix.Kernel.Level.EvalEqList] at h
  | _, _ :: _, [], h => by simp [Ix.Kernel.Level.EvalEqList] at h

/-- **The circuit's positional instantiation is the kernel's**, up to semantic equality: at a
level and a level list semantically equal to the represented ones, `Level.subst (List.range n)`
and `substLevel` agree at every assignment. -/
theorem lvEq_subst_range {u l : KLevel} {us ls : List KLevel} (hu : LvEq u l)
    (hus : LvEqList us ls) :
    LvEq (Ix.Kernel.Level.subst (List.range us.length) us u)
      (IxVM.Refinement.KernelLevels.substLevel l ls) := by
  intro φ
  have hlen : us.length = ls.length := evalEqList_length us ls (hus φ)
  rw [IxVM.Refinement.KernelLevels.eval_substLevel_eq_subst, Ix.Kernel.Level.eval_subst,
    Ix.Kernel.Level.eval_subst, ← hlen, substFn_congr φ _ us ls (hus φ)]
  exact hu _

/-- A binder datum whose level substitutes to a never-zero level substitutes to `never`. -/
theorem isNever_substPW_bmeta {ℓ : KLevel} {ks : List Ix.Kernel.LevelParam} {us : List KLevel}
    (h : (Ix.Kernel.Level.subst ks us ℓ).isNeverZero = true) :
    (Ix.Kernel.Level.substPW ks us (bmeta ℓ).pw).isNever = true := by
  show (Ix.Kernel.Level.substPW ks us ℓ.zeronessOf).isNever = true
  rw [← Ix.Kernel.Level.zeronessOf_subst, ← Ix.Kernel.Level.isNeverZero_eq_isNever]
  exact h

/-- A level the never-zero test accepts, from `level_is_not_zero`'s answer `1`. -/
theorem isNeverZero_of_answer {l : KLevel}
    (hr : (Value.field (1 : F) : SourceValue F) = .field (if l.isNeverZero then 1 else 0)) :
    l.isNeverZero = true := by
  by_contra hn
  exact field_one_ne_zero (by rw [hr, ite_eq_right hn])

/-- A level the never-zero test accepts, from an answer that is not `0`. -/
theorem isNeverZero_of_ne_zero {l : KLevel} {r : SourceValue F}
    (hr : r = .field (if l.isNeverZero then 1 else 0)) (hne : r ≠ .field 0) :
    l.isNeverZero = true := by
  by_contra hn
  exact hne (by rw [hr, ite_eq_right hn])

/-! ## Instantiating a binder -/

theorem instantiateList_lam (T B : KExpr) (m : Ix.Kernel.BinderMeta) (Cs : List KExpr) (j : Nat) :
    (Ix.Kernel.Expr.lam T B m).instantiateList Cs j =
      .lam (T.instantiateList Cs j) (B.instantiateList Cs (j + 1)) m := by
  simp only [Ix.Kernel.Expr.instantiateList]

theorem instantiateList_forallE (T B : KExpr) (m : Ix.Kernel.BinderMeta) (Cs : List KExpr)
    (j : Nat) :
    (Ix.Kernel.Expr.forallE T B m).instantiateList Cs j =
      .forallE (T.instantiateList Cs j) (B.instantiateList Cs (j + 1)) m := by
  simp only [Ix.Kernel.Expr.instantiateList]

end WhnfAux

end IxVM.Refinement.Core
