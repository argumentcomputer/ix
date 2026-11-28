module

public import IxCK.Kernel.Model.SortZero
public import IxCK.Kernel.Verify.PropWhen

@[expose] public section

/-!
# Universe zero-signatures for projection guard comparisons

`guardSignature` returns `none` for a level that is never zero, otherwise a max of the
parameters which must all be zero. `imax` keeps only its right operand; a `max` with a
never-zero operand is never zero. `guardSignatureLevel` represents the never case by `1`.

Comparing these signature levels suffices to transfer zero-ness of the original levels,
including after an arbitrary level-parameter substitution. This is an algebraic contract for
an explicit signature comparison; it does not assert that separate inference runs agree.
-/

namespace Ix.Kernel.Level

/-- `none` is the never-zero signature; a present level is a max of zero/parameters. -/
def guardSignature : Level → Option Level
  | .zero => some .zero
  | .succ _ => none
  | .param p => some (.param p)
  | .max a b => do
      let a' ← guardSignature a
      let b' ← guardSignature b
      pure (.max a' b')
  | .imax _ b => guardSignature b

/-- The signature represented as a universe expression, with `1` for never zero. -/
def guardSignatureLevel (l : Level) : Level :=
  (guardSignature l).getD (.succ .zero)

/-- The option-valued signature preserves exactly the zero-set. -/
theorem guardSignature_spec (l : Level) (φ : LevelParam → Nat) :
    match guardSignature l with
    | none => eval φ l ≠ 0
    | some s => eval φ l = 0 ↔ eval φ s = 0 := by
  induction l with
  | zero => exact Iff.rfl
  | succ a => exact Nat.succ_ne_zero _
  | param p => exact Iff.rfl
  | max a b ia ib =>
    cases ha : guardSignature a with
    | none =>
      simp only [ha] at ia
      simp only [guardSignature, ha]
      intro h
      exact ia (Nat.max_eq_zero_iff.mp h).1
    | some sa =>
      simp only [ha] at ia
      cases hb : guardSignature b with
      | none =>
        simp only [hb] at ib
        simp only [guardSignature, ha, hb]
        intro h
        exact ib (Nat.max_eq_zero_iff.mp h).2
      | some sb =>
        simp only [hb] at ib
        simp only [guardSignature, ha, hb]
        change Nat.max (eval φ a) (eval φ b) = 0 ↔ Nat.max (eval φ sa) (eval φ sb) = 0
        rw [Nat.max_eq_zero_iff, Nat.max_eq_zero_iff, ia, ib]
  | imax a b _ ib =>
    have hz := Rules.evalImax_eq_zero_iff φ a b
    cases hb : guardSignature b with
    | none =>
      simp only [hb] at ib
      simp only [guardSignature, hb]
      exact fun h => ib (hz.mp h)
    | some sb =>
      simp only [hb] at ib
      simp only [guardSignature, hb]
      exact hz.trans ib

/-- The concrete comparison level has precisely the original level's zero-set. -/
theorem guardSignatureLevel_zero_iff (l : Level) (φ : LevelParam → Nat) :
    eval φ l = 0 ↔ eval φ (guardSignatureLevel l) = 0 := by
  have h := guardSignature_spec l φ
  cases hs : guardSignature l with
  | none =>
    simp only [hs] at h
    simp [guardSignatureLevel, hs, eval, h]
  | some s =>
    simpa only [guardSignatureLevel, hs, Option.getD_some] using h

/-- An explicit semantic equality check on signatures gives zero-ness agreement after any
substitution. Its forward direction is sufficient for a stored projection guard. -/
theorem guardSignatureLevel_subst_zero_iff {l r : Level}
    (hsig : ∀ ψ, eval ψ (guardSignatureLevel l) = eval ψ (guardSignatureLevel r))
    (ks : List LevelParam) (us : List Level) (φ : LevelParam → Nat) :
    eval φ (subst ks us l) = 0 ↔ eval φ (subst ks us r) = 0 := by
  rw [eval_subst, eval_subst]
  rw [guardSignatureLevel_zero_iff l, guardSignatureLevel_zero_iff r, hsig]

/-- A successful level-equivalence test on the signatures discharges the comparison contract. -/
theorem guardSignatureLevel_checked {l r : Level}
    (h : isEquiv (guardSignatureLevel l) (guardSignatureLevel r) = some true)
    (ks : List LevelParam) (us : List Level) (φ : LevelParam → Nat) :
    eval φ (subst ks us l) = 0 ↔ eval φ (subst ks us r) = 0 :=
  guardSignatureLevel_subst_zero_iff (fun ψ => isEquiv_sound h ψ) ks us φ

/-- Dropping the domain universe in Pi formation preserves its zero-signature exactly. -/
theorem guardSignature_imax (a b : Level) : guardSignature (.imax a b) = guardSignature b := rfl

/-- A successor anywhere under max is absorbed by the never-zero signature. -/
theorem guardSignature_max_succ (a b : Level) : guardSignature (.max (.succ a) b) = none := rfl

end Ix.Kernel.Level
