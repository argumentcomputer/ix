module

public import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The direct install's stage runs, inverted to their records (task #175 W4c, P3)

Each stage of `checkStruct` is a `do`-block of guards and
operation runs; the P install reads those runs (the annotated types'
inference, the definitional pins at the opened frames, the field
sorts) as its premises.  This module inverts every stage into exactly
the facts the semantic modules consume — named runs, at the frames
the checker ran them.  Shape walks only: `exceptBind_ok` per bind,
`rw [if_pos …]` per guard (BridgeWfImp's idiom — the do-notation's
join points defeat a bare `split`), `close_throw` on the failing
branches.
-/

namespace ConLeche

variable {mode : CheckMode}

private theorem dThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact dThrow_ne_ok (by assumption))
        | (exfalso; exact dThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## Stage 1: the type former -/

/-! ## Stage 2: the constructor -/

/-! ## Stage 3: the recursor, generated and compared (task #175 S2) -/

/-! ## The frame walks: binder-domain pins and field sorts -/

/-- `checkStructDomsAt`, inverted: every position below the walk's
bound carries a successful `isDefEqCore` at its own frame. -/
theorem checkStructDomsAt_inv {env : Env} {F off : Nat} {fvs doms : List Expr} :
    ∀ {j : Nat},
      checkStructDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    unfold checkStructDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    have hc' : isDefEqCore mode env F (off + j) (Expr.fvarTypeD a) b = .ok c := hc
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [if_pos rfl] at h
    try simp only at h
    rcases Nat.lt_or_ge i j with hij | hij
    · exact checkStructDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hc'⟩

end ConLeche
