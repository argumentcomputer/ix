import Ix.IxVM.Refinement.KernelLevels

/-! # Universe levels: completeness of `level_equal` at zero

`Ix.IxVM.Refinement.KernelLevels` refines `KernelLevels::level_equal` to the pure
`levelEqual` and proves the answer `1` sound (`levelEqual_eq_true_sound`). This module
proves the converse at `zero`: a level that is zero at every assignment is `levelEqual` to
`zero`, so the circuit's answer `0` to `level_equal(l, Zero)` means that `l` is nonzero at
some assignment.

The proof is by shape. A level is zero at every assignment exactly when it is `zero`, a
`max` of two such levels, or an `imax` whose right side is one (`ZeroShape`). On that shape
the normalizer, started at offset `0`, leaves its accumulator unchanged: at an `imax` it
walks only the right side (the left side of `imax a b` is dropped when `b` has no successor
and no parameter), and every leaf it reaches is `zero` at offset `0`, where `nlAddConst`
adds nothing. So such a level normalizes as `zero` does, and `nlEq` is reflexive. -/

namespace IxVM.Refinement.KernelLevels

/-- **The levels that are zero at every assignment**, by shape: `zero`, a `max` of two such
levels, or an `imax` whose right side is one. -/
inductive ZeroShape : Ix.Kernel.Level → Prop
  | zero : ZeroShape .zero
  | max {a b : Ix.Kernel.Level} : ZeroShape a → ZeroShape b → ZeroShape (.max a b)
  | imax {a b : Ix.Kernel.Level} : ZeroShape b → ZeroShape (.imax a b)

/-- **A level zero at every assignment has the zero shape.** A successor is positive; a
parameter is positive at the assignment `1`; a `max` is zero only when both sides are; an
`imax` is zero exactly when its right side is. -/
theorem ZeroShape.of_eval {l : Ix.Kernel.Level} (h : ∀ φ, Ix.Kernel.Level.eval φ l = 0) :
    ZeroShape l := by
  induction l with
  | zero => exact .zero
  | succ u _ => exact absurd (h fun _ => 0) (by simp [Ix.Kernel.Level.eval])
  | max a b iha ihb =>
    refine .max (iha fun φ => ?_) (ihb fun φ => ?_)
    · have := h φ
      simp only [Ix.Kernel.Level.eval] at this
      omega
    · have := h φ
      simp only [Ix.Kernel.Level.eval] at this
      omega
  | imax a b _ ihb =>
    refine .imax (ihb fun φ => ?_)
    have := h φ
    simp only [Ix.Kernel.Level.eval] at this
    by_contra hb
    simp only [hb, ↓reduceIte] at this
    omega
  | param n => exact absurd (h fun _ => 1) (by simp [Ix.Kernel.Level.eval])

/-- **The normalizer leaves its accumulator unchanged on a zero shape** at offset `0` (for
`normalize_imax_dispatch`, when the right side has the zero shape), at every fuel. -/
theorem normalizeStep_zeroShape (path : List Nat) (fuel : Nat) :
    ∀ (arg : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level)) (acc : List NLEntry),
      (match arg with
       | .inl l => ZeroShape l
       | .inr (_, b) => ZeroShape b) →
      normalizeStep fuel arg path 0 acc = acc := by
  induction fuel with
  | zero =>
    intro arg acc _
    simp only [normalizeStep]
  | succ fuel ih =>
    intro arg acc hz
    rcases arg with l | ⟨a, b⟩
    · change ZeroShape l at hz
      cases hz with
      | zero => simp only [normalizeStep, nlAddConst]
      | @max a b ha hb =>
        simp only [normalizeStep]
        rw [ih (.inl a) acc ha, ih (.inl b) acc hb]
      | @imax a b hb =>
        simp only [normalizeStep]
        exact ih (.inr (a, b)) acc hb
    · change ZeroShape b at hz
      cases hz with
      | zero => simp only [normalizeStep, nlAddConst]
      | @max v w hv hw =>
        simp only [normalizeStep]
        rw [ih (.inr (a, v)) acc hv, ih (.inr (a, w)) acc hw]
      | @imax v w hw =>
        simp only [normalizeStep]
        rw [ih (.inr (a, w)) acc hw, ih (.inr (v, w)) acc hw]

/-- **A zero shape normalizes as `zero` does.** -/
theorem levelNormalize_zeroShape {l : Ix.Kernel.Level} (hz : ZeroShape l) :
    levelNormalize l = levelNormalize .zero := by
  have hl : normalizeAux l [] 0 [⟨[], 0, []⟩] = [⟨[], 0, []⟩] :=
    normalizeStep_zeroShape [] (normFuel (.inl l)) (.inl l) _ hz
  have h0 : normalizeAux .zero [] 0 [⟨[], 0, []⟩] = [⟨[], 0, []⟩] :=
    normalizeStep_zeroShape [] (normFuel (.inl .zero)) (.inl .zero) _ ZeroShape.zero
  simp only [levelNormalize, hl, h0]

/-- **`nlEq` is reflexive.** -/
theorem nlEq_refl (x : List NLEntry) : nlEq x x = true := by
  rw [nlEq_unfold]
  cases hs : nlSkipEmpty x with
  | nil => rfl
  | cons e ar =>
    rcases e with ⟨p, c, v⟩
    have ih : nlEq ar ar = true := nlEq_refl ar
    simp [glistCmp_refl, nlvarsEq_iff, ih]
termination_by x.length
decreasing_by
  have := nlSkipEmpty_cons_length_lt hs
  omega

/-- **Completeness of `level_equal` at zero**: a level zero at every assignment is
`levelEqual` to `zero`. -/
theorem levelEqual_zero_of_eval {l : Ix.Kernel.Level}
    (h : ∀ φ, Ix.Kernel.Level.eval φ l = 0) : levelEqual l .zero = true := by
  unfold levelEqual
  split
  · rfl
  · rw [levelNormalize_zeroShape (ZeroShape.of_eval h)]
    exact nlEq_refl _

/-- **The answer `false` at zero refutes zero**: if `levelEqual l zero` is `false`, `l` is
nonzero at some assignment. -/
theorem not_eval_zero_of_levelEqual_false {l : Ix.Kernel.Level}
    (h : levelEqual l .zero = false) : ¬ ∀ φ, Ix.Kernel.Level.eval φ l = 0 := by
  intro hall
  rw [levelEqual_zero_of_eval hall] at h
  exact absurd h (by decide)

end IxVM.Refinement.KernelLevels
