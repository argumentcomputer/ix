module

public import ConLeche.Verify.NatOpFrag
public import ConLeche.Verify.InferLeaves

@[expose] public section

/-!
# The pinned-`Nat` fragment's syntactic package (task #161 S4, THE
SEPARATION)

One lemma, and it is a *split*: `natEqFrame_of_frag`
(`SetR/Bridge/Decl.lean`) proves five things about a fragment
expression with the operation's stored value substituted in — four
syntactic (scoping, `bvar`-closedness, leaf boundedness, the `Nat`
leaf annotation) and one semantic (it denotes at the collapsed
valuation).  The **graded lane consumes only the four**: both of
`Model/NatEqs.lean`'s call sites destructure `⟨hw, hb, hL, hleaf, -⟩`.

So the four move below both lanes, where a statement mentioning only
`Env` and `Expr` belongs, and `natEqFrame_of_frag` keeps its name, its
statement and its consumers — it now assembles this package with its
own denotation induction (`natFrag_subst_denotes`).  This is the design
census §3.3's split recipe applied to the last S4-tagged crossing.

The file is separate from `Verify/NatOpFrag.lean` (where `natFragOk`
lives) only because `Expr.LeavesBounded` is `Verify/InferLeaves.lean`'s,
and pulling that into `NatOpFrag` would push it onto the TT lane's
cone for one definition.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {env : Env}


/-- **The fragment's syntactic package**, model-free (task #161 S4, THE
SEPARATION).

Substituting the operation's own stored value into a fragment
expression leaves it inside the two-variable `Nat` frame: scoped at
depth `2`, `bvar`-closed, with every `fvar` leaf below `2` and
annotated by `Nat`.  Four facts, one induction over `natFragOk`'s four
constructors, and **no valuation anywhere** — the operation `c` is the
one being defined, so it is not stored, and its occurrences are exactly
what `substConst0` replaces by `v`, whose own two guards stand in.

This is the model-free half of the collapsed lane's
`natEqFrame_of_frag` (`SetR/Bridge/Decl.lean`), split out here because
the graded lane consumes **only** these four conjuncts — it drops the
denotation half at both of its call sites (`Model/NatEqs.lean`) — and
because a lemma that mentions only `Env`/`Expr` belongs below both
lanes, which is this file's own stated threshold ("a second consumer
and nothing lane-specific in the statement").  `natEqFrame_of_frag`
now calls it for its first four components. -/
theorem natFrag_subst_syntax {c : Name} {v : Expr}
    (hvf : v.hasFvar = false) (hvb : v.looseBVarsBounded 0 = true) :
    ∀ {e : Expr}, natFragOk env c e = true →
      Expr.WScoped 2 (Expr.substConst0 c v e) ∧
      (Expr.substConst0 c v e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.substConst0 c v e) ∧
      (∀ l ∈ (Expr.substConst0 c v e).fvarLeaves,
        l.1 < 2 ∧ l.2 = .const natName [])
  | .sort u, _ => by
    rw [show Expr.substConst0 c v (Expr.sort u) = Expr.sort u from rfl]
    refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_⟩
    · intro l hl; simp [Expr.fvarLeaves] at hl
    · intro l hl; simp [Expr.fvarLeaves] at hl
  | .fvar i ty, h => by
    simp only [natFragOk, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    have hilt : i < 2 := by rcases hi with rfl | rfl <;> omega
    rw [show Expr.substConst0 c v (Expr.fvar i (.const natName []))
      = Expr.fvar i (.const natName []) from rfl]
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [Expr.WScoped]
      exact ⟨hilt, by rw [Expr.WScoped]; trivial⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · simp [Expr.fvarLeaves] at hl'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨hilt, rfl⟩
      · simp [Expr.fvarLeaves] at hl'
  | .const n us, h => by
    rw [show Expr.substConst0 c v (Expr.const n us)
      = (if n = c ∧ us = [] then v else Expr.const n us) from rfl]
    by_cases hn : n = c ∧ us.isEmpty = true
    · rw [if_pos (show n = c ∧ us = [] from
        ⟨hn.1, List.isEmpty_iff.mp hn.2⟩)]
      refine ⟨Expr.WScoped.mono (Nat.zero_le 2)
          (Expr.WScoped.of_not_hasFvar hvf), hvb,
        Expr.LeavesBounded.of_not_hasFvar hvf, ?_⟩
      intro l hl
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
      exact nomatch hl
    · rw [if_neg (fun hh => hn ⟨hh.1, by rw [hh.2]; rfl⟩)]
      refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_⟩
      · intro l hl; simp [Expr.fvarLeaves] at hl
      · intro l hl; simp [Expr.fvarLeaves] at hl
  | .app f a, h => by
    simp only [natFragOk, Bool.and_eq_true] at h
    obtain ⟨hwf, hbf, hLf, hlf⟩ := natFrag_subst_syntax hvf hvb h.1
    obtain ⟨hwa, hba, hLa, hla⟩ := natFrag_subst_syntax hvf hvb h.2
    rw [show Expr.substConst0 c v (Expr.app f a)
      = Expr.app (Expr.substConst0 c v f) (Expr.substConst0 c v a)
      from rfl]
    refine ⟨by rw [Expr.WScoped]; exact ⟨hwf, hwa⟩, ?_, ?_, ?_⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf, hba⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hLf l h'
      · exact hLa l h'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hlf l h'
      · exact hla l h'
  | .bvar _, h | .lam _ _ _, h | .forallE _ _ _, h
  | .letE _ _ _, h | .proj _ _ _, h | .lit _, h => by
    simp [natFragOk] at h

end ConLeche.Verify
