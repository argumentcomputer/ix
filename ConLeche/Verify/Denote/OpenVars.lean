module

import ConLeche.Kernel.ExprOps
public import ConLeche.Term.Subst
import ConLeche.Verify.Shift
public import ConLeche.Verify.Subst

public section

/-!
# The canonical opening variables

`openFvars d k` — the `k` opening variables of a telescope at depth
`d`, outermost first.  A leaf module: `ConLeche/TTVerify/EnvTT.lean`
states the nested iota rules' parameter premise over the *opened*
stored pins, and cannot import `ConLeche/Verify/Denote/TeleOpen.lean` (which
sits far above it); the definition and its index bookkeeping live
here, and `TeleOpen.lean` re-exports them.

`denote` reads neither an opening variable's name nor its annotation
(`ConLeche/Verify/Denote.lean`), so canonical ones are as good as the
binders' own — which is what lets a single opening stand for every
telescope an alignment relates.
-/

namespace ConLeche.Verify

/-- The `k` opening variables of a telescope at depth `d`, outermost
first. -/
@[expose] def openFvars : Nat → Nat → List Expr
  | _, 0 => []
  | d, k + 1 => Expr.fvar d (.sort .zero) :: openFvars (d + 1) k

@[simp] theorem openFvars_length : ∀ (d k : Nat), (openFvars d k).length = k
  | _, 0 => rfl
  | d, k + 1 => by simp [openFvars, openFvars_length (d + 1) k]

theorem openFvars_zero (d : Nat) : openFvars d 0 = [] := by rfl

theorem openFvars_succ (d k : Nat) :
    openFvars d (k + 1) =
      Expr.fvar d (.sort .zero) :: openFvars (d + 1) k := by rfl

theorem openFvars_bounded : ∀ (d k : Nat),
    ∀ a ∈ openFvars d k, a.looseBVarsBounded 0 = true
  | _, 0 => by intro a ha; exact nomatch ha
  | d, k + 1 => by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · rfl
    · exact openFvars_bounded (d + 1) k a h

theorem openFvars_getElem? : ∀ {d k i : Nat}, i < k →
    (openFvars d k)[i]? =
      some (Expr.fvar (d + i) (.sort .zero))
  | _, 0, _, h => absurd h (by omega)
  | d, k + 1, 0, _ => by simp [openFvars]
  | d, k + 1, i + 1, h => by
    rw [openFvars_succ, List.getElem?_cons_succ,
      openFvars_getElem? (d := d + 1) (k := k) (i := i) (by omega)]
    congr 2
    omega

/-! ## The reverse opening

The bookkeeping order `denote`'s own recursion produces: substitute
the *innermost* loose variable first, each at cut `0`, the opener
indices ascending with the substitution order.  `Expr.instSeq` at real
arguments relates to *this* opening (`denote_openRev`,
`ConLeche/TTVerify/IndBottom.lean`), which is why the nested iota rules'
parameter premise is stated over it: both the fire site and the
install meet at the base-`0` reverse opening of the stored pin. -/

/-- Open `n` loose variables innermost-first, each at cut `0`, with
ascending opener indices from `d`. -/
@[expose] def openRev (d : Nat) : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    (openRev d n e).instantiate1 (.fvar (d + n) (.sort .zero)) 0

/-- The value chain `denote` produces for a real-argument instantiation
read through the reverse opening: outermost argument consumed first,
each at cut `0`, lifted past the arguments still to come. -/
@[expose] def _root_.ConLeche.Term.Term.instRevChain : List ConLeche.Term.Term →
    ConLeche.Term.Term → ConLeche.Term.Term
  | [], X => X
  | v :: vs, X =>
    ConLeche.Term.Term.instRevChain vs (X.inst (v.liftN vs.length) 0)

/-- Substituting a variable above the reverse opening's range commutes
to the outside (the opening touches only the variables below it). -/
theorem openRev_instantiate1_above {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) (d : Nat) :
    ∀ (n : Nat) (e : Expr) (k : Nat),
      openRev d n (e.instantiate1 a (n + k)) =
        (openRev d n e).instantiate1 a k := by
  intro n
  induction n with
  | zero => intro e k; rw [Nat.zero_add]; rfl
  | succ n ih =>
    intro e k
    show (openRev d n (e.instantiate1 a (n + 1 + k))).instantiate1 _ 0 = _
    rw [show n + 1 + k = n + (k + 1) from by omega, ih e (k + 1),
      Expr.instantiate1_instantiate1 hba rfl _ 0 k (Nat.zero_le k)]
    rfl

/-- The special case the induction on real arguments consumes. -/
theorem openRev_instantiate1_top {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) (d n : Nat) (e : Expr) :
    openRev d n (e.instantiate1 a n) = (openRev d n e).instantiate1 a 0 := by
  have h := openRev_instantiate1_above hba d n e 0
  rw [Nat.add_zero] at h
  exact h

end ConLeche.Verify
