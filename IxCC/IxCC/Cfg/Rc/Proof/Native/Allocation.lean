import IxCC.Cfg.Rc.Proof.Native.Consume

/-! Invert actual positive-allocation admission. These shape and table facts
are required by physical allocation/publication; callers need not assume that
the source constructor is fully scanned or that its tag fits the header. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec

theorem consume_allocation {P : Program} {l : Layout} {x : Nat}
    {c : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Instr}
    (positive : 0 < c.arity)
    (accepted : consume P l (.bind x (.alloc c args kind)) = .ok result) :
    kind = .shared ∧ c.nscalar = 0 ∧ c.fieldKinds.length = c.nobj ∧
      (∀ k ∈ c.fieldKinds, k = .shared) ∧ args.length = c.arity ∧
      Fir.CtorInfo.ofKey P.base.ctors c.key = some c ∧
      c.tag ≤ Rt.maxTag ∧
      P.base.known.natZero ≠ some c.key ∧ P.base.known.natSucc ≠ some c.key ∧
      args.contains (.var x) = false ∧ c.arity ≤ Rt.maxFields ∧
      ∃ index, ctorIndex l c.key = some index ∧
        result = .bind x (.fir (.call (l.allocWrapper index) args)) := by
  simp only [consume, reserved, Bool.false_eq_true, ↓reduceIte] at accepted
  by_cases hs : (kind == .shared && c.nscalar == 0 && c.fieldKinds.length == c.nobj &&
      c.fieldKinds.all (· == .shared) && args.length == c.arity &&
      Fir.CtorInfo.ofKey P.base.ctors c.key == some c) = true
  · simp only [hs, Bool.true_eq_false, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
    by_cases ht : c.tag > Rt.maxTag
    · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    · simp only [ht, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      by_cases hn : (P.base.known.natZero == some c.key || P.base.known.natSucc == some c.key) = true
      · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
      · simp only [hn, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
        have hfieldless : c.fieldless = false := by
          simp [Fir.CtorInfo.fieldless, Nat.ne_of_gt positive]
        simp only [hfieldless, Bool.false_eq_true, ↓reduceIte] at accepted
        by_cases hx : args.contains (.var x) = true
        · rw [hx] at accepted
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
        · rw [Bool.eq_false_iff.mpr hx] at accepted
          simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
          by_cases ha : c.arity > Rt.maxFields
          · simp [ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
          · simp only [ha, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
            cases hi : ctorIndex l c.key with
            | none => rw [hi] at accepted; cases accepted
            | some index =>
              simp only [hi, pure, Except.pure, Except.ok.injEq] at accepted
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
              obtain ⟨⟨⟨⟨⟨hk, hscalar⟩, hlen⟩, hshared⟩, hargs⟩, htable⟩ := hs
              have hknown : P.base.known.natZero ≠ some c.key ∧
                  P.base.known.natSucc ≠ some c.key := by simpa using hn
              exact ⟨hk, hscalar, hlen, hshared, hargs, htable,
                Nat.le_of_not_gt ht, hknown.1, hknown.2,
                Bool.eq_false_iff.mpr hx, Nat.le_of_not_gt ha, index, rfl, accepted.symm⟩
  · simp [hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted


end IxCC.Cfg.Rc.Native.Spec
