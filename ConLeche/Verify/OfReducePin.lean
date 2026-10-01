module

import ConLeche.Verify.EnvGuards
public import ConLeche.Verify.NatOpFrag

public section

/-!
# The pinned `ofReduce` axioms' shapes (V-free)

`ofReduceNat`/`ofReduceBool` differ only in their element type, so
every shape fact about them is one `split`.  Both soundness routes
consume these and neither may import the other, so they live in the
shared tier (task #148 T6).
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- `erasePw` fixes a sort (task #161 P5: `matchesPin` compares through
`Expr.erasePw`, so the pin-shape inversions must see through it).
This is a *head* inversion: `erasePw` never changes a node's
constructor. -/
theorem erasePw_sort_inv {e : Expr} {u : Level}
    (h : e.erasePw = .sort u) : e = .sort u := by
  cases e <;> simp only [Expr.erasePw] at h <;> first
    | exact h
    | exact nomatch h

/-! ## The two shapes, uniformly

`ofReduceOp` and `reduceElemName` both branch on the axiom's name, so
every fact below is stated once and discharged by `rcases` on the two
possibilities. -/

/-- The element type expression of an `ofReduce*` axiom's operation. -/
theorem ofReduce_elemTy {n : Name} :
    reduceElemTy (ofReduceOp n)
      = .const (reduceElemName (ofReduceOp n)) [] := by
  unfold reduceElemTy reduceElemName
  split <;> rfl

/-- The pinned type of an `ofReduce*` axiom, in the uniform spelling
its two instances share. -/
theorem ofReducePin_type {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName) :
    (ofReducePinA n).type =
      .forallE
        (.const (reduceElemName (ofReduceOp n)) [])
        (.forallE
          (.const (reduceElemName (ofReduceOp n)) [])
          (.forallE
            (Expr.mkAppN (.const eqName [.succ .zero])
              [.const (reduceElemName (ofReduceOp n)) [],
               .app (.const (ofReduceOp n) []) (.bvar 1), .bvar 0])
            (Expr.mkAppN (.const eqName [.succ .zero])
              [.const (reduceElemName (ofReduceOp n)) [],
               .bvar 2, .bvar 1]) ⟨.ifAllZero []⟩)
          ⟨.ifAllZero []⟩)
        ⟨.ifAllZero []⟩ := by
  rcases hn with rfl | rfl <;> rfl

/-- The pinned type of the operation itself. -/
theorem reduceOpCv_type {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName) :
    (reduceOpCvA (ofReduceOp n)).type =
      .forallE
        (.const (reduceElemName (ofReduceOp n)) [])
        (.const (reduceElemName (ofReduceOp n)) []) ⟨.never⟩ := by
  rcases hn with rfl | rfl <;> rfl

/-- The element inductive's pinned type is `Sort 1`. -/
theorem reduceElem_sort {env : Env} {c : Name}
    (h : reduceElemOk env c = true) :
    ∃ ci, env.find? (reduceElemName c) = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  by_cases hc : c = reduceNatName
  · rw [reduceElemOk, if_pos hc] at h
    refine ⟨natA, ?_, rfl, rfl⟩
    rw [reduceElemName, if_pos hc]
    simpa using h
  · rw [reduceElemOk, if_neg hc] at h
    rw [reduceElemName, if_neg hc]
    cases hf : env.find? boolName with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | indInfo cvB caps =>
        refine ⟨.indInfo cvB caps, rfl, ?_, ?_⟩
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact h.1.2
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at h
          show cvB.type = _
          exact erasePw_sort_inv (by
            simpa [boolCvA, Expr.erasePw] using h.2)
      | _ => exact nomatch h

/-- Name and level-parameter components of a `matchesPin` hit. -/
theorem matchesPin_invT {cv pin : ConstantVal}
    (h : ConstantVal.matchesPin cv pin = true) :
    cv.name = pin.name ∧ cv.levelParams = pin.levelParams := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

end ConLeche.Verify
