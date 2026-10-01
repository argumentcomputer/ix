module

import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.IndZipper
public section

/-!
# The point stage's kit (task #161, IND TIER part 5)

The four small facts `pointS` reads that part 3's frame kit and part
4's stage kit left out, because they belong to the *spine* rather than
to the frame or to the fit: a read spine's pointwise lookup, `instSeq`
over an application, injectivity of `mkAppN` at equal arities, and the
determinacy of a `TeleFitPA` residual.

All four are `Term`-level facts one currency over and are transposed
verbatim — they mention no `interp`, no bit, and no environment
except through `TeleFitPA`.  `AnnotTerm.mkAppN_inj` is the one that
carries the point stage's weight: the crossed constructor residual and
the fired index pin are both applications of the *same* arity, and the
stage reads their arguments off pointwise.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- Pointwise reading of a read spine (`denoteSpine_getElem?'`). -/
theorem denoteMetaSpine_getElem?' {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs →
      ∀ (i : Nat) (x : Expr), as[i]? = some x →
        ∃ v, vs[i]? = some v ∧ denoteMeta acval env φ d x = some v := by
  intro as vs h
  induction h with
  | nil => intro i x hx; exact nomatch hx
  | @cons a v as' vs' ha _ ih =>
    intro i x hx
    cases i with
    | zero =>
      obtain rfl : a = x := Option.some.inj hx
      exact ⟨v, rfl, ha⟩
    | succ j =>
      obtain ⟨v', hv', hd⟩ := ih j x (by simpa using hx)
      exact ⟨v', by simpa using hv', hd⟩

/-- Spine instantiation distributes over one application node. -/
theorem instSeqAV_app : ∀ (as : List AnnotTerm) (t : Nat) (f a : AnnotTerm),
    AnnotTerm.instSeq as t (.app f a)
      = .app (AnnotTerm.instSeq as t f) (AnnotTerm.instSeq as t a) := by
  intro as
  induction as with
  | nil => intro t f a; rfl
  | cons b bs ih =>
    intro t f a
    rw [AnnotTerm.instSeq_cons, AnnotTerm.instSeq_cons, AnnotTerm.instSeq_cons,
      ConLeche.Semantics.AnnotTerm.inst_app, ih]

/-- Spine instantiation distributes over an application
(`instSeq_mkAppN`). -/
theorem instSeqAV_mkAppN : ∀ (as : List AnnotTerm) (t : Nat) (f : AnnotTerm)
    (args : List AnnotTerm),
    AnnotTerm.instSeq as t (AnnotTerm.mkAppN f args) =
      AnnotTerm.mkAppN (AnnotTerm.instSeq as t f)
        (args.map (AnnotTerm.instSeq as t ·)) := by
  intro as t f args
  induction args generalizing f with
  | nil => rfl
  | cons a args ih =>
    rw [ConLeche.Semantics.AnnotTerm.mkAppN_cons, ih, instSeqAV_app]
    rfl

/-- Applications of equal arity are equal only at equal heads and
equal argument lists (`Term.mkAppN_inj`). -/
theorem AnnotTerm.mkAppN_inj :
    ∀ {as bs : List AnnotTerm} {f g : AnnotTerm},
      AnnotTerm.mkAppN f as = AnnotTerm.mkAppN g bs → as.length = bs.length →
      f = g ∧ as = bs := by
  intro as
  induction as with
  | nil =>
    intro bs f g h hlen
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact ⟨h, rfl⟩
  | cons a as ih =>
    intro bs f g h hlen
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      rw [ConLeche.Semantics.AnnotTerm.mkAppN_cons,
        ConLeche.Semantics.AnnotTerm.mkAppN_cons] at h
      obtain ⟨h1, rfl⟩ := ih h (by simpa using hlen)
      injection h1 with h2 h3
      exact ⟨h2, by rw [h3]⟩

/-- A `TeleFitPA` residual is determined: the tower body,
spine-instantiated (`teleFitV_rest_eq`). -/
theorem teleFitPA_rest_eq :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ws : List AnnotTerm} {ρ : Nat → V}
        {rest : AnnotTerm},
      ws.length = k → TeleFitPA V ρ T ws rest →
      rest = AnnotTerm.instSeq ws (k - 1) R := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws ρ rest hlen hfit
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    cases hfit
    rfl
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    cases hfit with
    | cons hmem htailFit =>
      have hr := ihk (htail.inst w 0) hlen' htailFit
      rw [hr, AnnotTerm.instSeq_cons,
        show k + 1 - 1 - 1 = k - 1 from by omega, Nat.add_sub_cancel,
        Nat.zero_add]

end ConLeche.Model
