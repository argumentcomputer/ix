module

public import ConLeche.Model.Annot.BitShift
import ConLeche.Semantics.DenoteClosed

public section

/-!
# `denoteMeta`, closed and depth-independent (task #161, P3.2)

The mirrors of `denoteAnnot_closed` (`Interp/DenoteClosed.lean`) and
`denote2_depth_of_closed` (`Interp/Steps/Levels.lean`).

**Closedness transposes for free, again.**  `denoteAnnot_closed` is not an
induction: it is `denoteAnnot_erase` composed with v1's `denote_closed`
and `AnnotTerm.liftN_eq_self` (a lift cannot be moved by a numeral slot).
`denoteMeta` has the *same* erasure law (`denoteMeta_erase`, `Annot/Bit.lean`)
onto the *same* `denote`, so the composition transports verbatim.  No
premise of the original fed a sort run — `hlink`/`hcl` are the leaf
valuation's, `hnf`/`hb` are the subject's scoping — so the only
deltas are the deleted `fuel` and `mode` indices.

**The depth statement drops `EnvWF`**, following the shift it is built
on (see `BitShift.lean`): its sole use in the original is inside
`denote2_shiftFrom`, whose mirror does not take it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen)

/-- **`denoteMeta`'s closedness law.**  A closed subject's validated
annotation is closed, in the lifting form `EnvModelU.acval_closed` and
`ValueResidues2.closed` state it.  Mirror of `denoteAnnot_closed`, with
`denoteMeta_erase` in place of `denoteAnnot_erase`. -/
theorem denoteMeta_closed {acval : Name → (Name → Nat) → AnnotTerm}
    {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, Term.Closed (cval n ψ))
    {e : Expr} {ea : AnnotTerm} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denoteMeta acval env φ 0 e = some ea) (n k : Nat) :
    ea.liftN n k = ea :=
  AnnotTerm.liftN_eq_self ea
    (Term.bvarsBelow.mono (Nat.zero_le k)
      (denote_closed hcl hnf hb (denoteMeta_erase hlink 0 e h))) n

/-- **A closed term's validated annotation does not depend on the
depth**, provided the annotation itself is lift-invariant.  Mirror of
`denote2_depth_of_closed`; `EnvWF` goes with `denoteMeta_shiftFrom`. -/
theorem denoteMeta_depth_of_closed {env : Env} {φ : Name → Nat}
    {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {e : Expr} {ea : AnnotTerm} (hfv : e.hasFvar = false)
    (hcl : ∀ k : Nat, ea.liftN 1 k = ea)
    (h : denoteMeta acval env φ 0 e = some ea) :
    ∀ d : Nat, denoteMeta acval env φ d e = some ea := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih =>
    have hs := denoteMeta_shiftFrom (env := env) (acval := acval) (φ := φ)
      (p := 0) hacl e d (Nat.zero_le d)
      (Expr.WScoped.of_not_hasFvar hfv)
    rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv, ih] at hs
    rw [hs]
    simp [hcl]

end ConLeche.Model
