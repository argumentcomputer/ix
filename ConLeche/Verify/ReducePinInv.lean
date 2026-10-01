module

import ConLeche.Verify.EnvGuards
import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.NatOpFrag

public section

/-!
# The compiler-trust opaque pin, inverted (V-free)

`checkReducePin`'s inversion and the element type's shape.  Both
soundness routes consume them and neither may import the other, so
they live in the shared tier (task #148 T6).

The inversion records **all** of the run's data — both guards, both
annotate outputs and both `isDefEq` verdicts.  The TT lane consumes
only the identity certificate; `SetR`'s `ReducePinR` also records the
guards and the pin comparison, and the proof always had them.
-/

namespace ConLeche.Verify

variable {mode : CheckMode} {F : Nat}

/-! ## The walk

`checkReducePin` is four nested guards and two `isDefEq`s; only the
second `isDefEq` is consumed here.  The first (`valA ≡ pin`) is the
*elaborator-drift* gate — it exists so a toolchain change surfaces as a
decline rather than silently — and the bridge needs nothing from it,
which is the expected shape: a gate that protects the *checker's* other
guarantees leaves the derivation layer alone. -/

/-- The element type is a stored constant with no level parameters. -/
theorem reduceElem_shape {env : Env} {c : Name}
    (h : reduceElemOk env c = true) :
    ∃ ci, env.find? (reduceElemName c) = some ci ∧
      ci.toConstantVal.levelParams = [] := by
  by_cases hc : c = reduceNatName
  · rw [reduceElemOk, if_pos hc] at h
    refine ⟨natA, ?_, rfl⟩
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
        refine ⟨.indInfo cvB caps, rfl, ?_⟩
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          decide_eq_true_eq] at h
        exact h.1.2
      | _ => exact nomatch h

/-- Inversion of the compiler-trust pin: the identity certificate. -/
theorem checkReducePin_inv {env env2 : Env} {c : Name} {value : Expr}
    (h : checkReducePin (fueledOps mode F) env env2 c value = .ok ()) :
    reduceStoredOk env2 c = true ∧ reduceElemOk env c = true ∧
    reducePinGuard env c = true ∧
    ∃ valA pinA, annotateCore mode env F 0 value = .ok valA ∧
      annotateCore mode env F 0 (reduceDeclPin c) = .ok pinA ∧
      -- task #148 T6: the pin side, appended.  The TT lane consumes
      -- only the identity certificate and dropped the rest; `SetR`'s
      -- `ReducePinR` records the guards and the `DefEq` against the
      -- pin, and the proof below already had every one of them in
      -- scope.  Appended, never reconstructed.
      isDefEqCore mode env F 0 valA pinA = .ok true ∧
      isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) = .ok true := by
  simp only [checkReducePin, fueledOps_annotate, fueledOps_isDefEq,
    Bind.bind, Except.bind] at h
  by_cases hg : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg => rw [if_neg hg] at h; exact nomatch h
  rw [if_pos hg] at h
  by_cases hpg : reducePinGuard env c = true
  case neg => rw [if_neg hpg] at h; exact nomatch h
  rw [if_pos hpg] at h
  obtain ⟨hstored, helem⟩ := by simpa only [Bool.and_eq_true] using hg
  refine ⟨hstored, helem, hpg, ?_⟩
  cases hva : annotateCore mode env F 0 value with
  | error e => rw [hva] at h; exact nomatch h
  | ok valA =>
  rw [hva] at h
  dsimp only at h
  cases hpa : annotateCore mode env F 0 (reduceDeclPin c) with
  | error e => rw [hpa] at h; exact nomatch h
  | ok pinA =>
  rw [hpa] at h
  dsimp only at h
  cases hp1 : isDefEqCore mode env F 0 valA pinA with
  | error e => rw [hp1] at h; exact nomatch h
  | ok b1 =>
  rw [hp1] at h
  cases b1 with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
  simp only [if_true] at h
  cases hp2 : isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
      (reduceCertVar c) with
  | error e => rw [hp2] at h; exact nomatch h
  | ok b2 =>
  rw [hp2] at h
  cases b2 with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true => exact ⟨valA, pinA, rfl, rfl, hp1, hp2⟩

end ConLeche.Verify
