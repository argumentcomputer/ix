module

import IxC.Kernel.Verify.EnvGuards
import IxC.Kernel.Verify.Extend.Inversions
public import IxC.Kernel.Verify.NatOpFrag

public section

/-!
# The compiler-trust identity gate, inverted (V-free)

`checkReduceIdentity`'s inversion and the element type's shape.  Both
soundness routes consume them and neither may import the other, so
they live in the shared tier (task #148 T6).

The inversion records all of the run's data — the two guards, the
value's annotation and the identity certificate's `isDefEq` verdict.
Since step 4 there is no pin comparison (`checkReducePin` and the
toolchain pin `fun b => b` are retired): the identity certificate is
the specification.
-/

namespace Ix.Kernel.Verify

variable {mode : CheckMode} {F : Nat}

/-! ## The walk

`checkReduceIdentity` is two guards, an annotation and one `isDefEq`,
the identity certificate the model consumes. -/

/-- The element type is a stored constant with no level parameters. -/
theorem reduceElem_shape {env : Env} {c : Key}
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

/-- Inversion of the compiler-trust identity gate: the identity
certificate. -/
theorem checkReduceIdentity_inv {env env2 : Env} {c : Key} {value : Expr}
    (h : checkReduceIdentity (fueledOps mode F) env env2 c value = .ok ()) :
    reduceStoredOk env2 c = true ∧ reduceElemOk env c = true ∧
    ∃ valA, annotateCore mode env F 0 value = .ok valA ∧
      isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
        (reduceCertVar c) = .ok true := by
  simp only [checkReduceIdentity, fueledOps_annotate, fueledOps_isDefEq,
    Bind.bind, Except.bind] at h
  by_cases hg : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg => rw [if_neg hg] at h; exact nomatch h
  rw [if_pos hg] at h
  obtain ⟨hstored, helem⟩ := by simpa only [Bool.and_eq_true] using hg
  refine ⟨hstored, helem, ?_⟩
  cases hva : annotateCore mode env F 0 value with
  | error e => rw [hva] at h; exact nomatch h
  | ok valA =>
  rw [hva] at h
  dsimp only at h
  cases hp2 : isDefEqCore mode env F 1 (.app valA (reduceCertVar c))
      (reduceCertVar c) with
  | error e => rw [hp2] at h; exact nomatch h
  | ok b2 =>
  rw [hp2] at h
  cases b2 with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true => exact ⟨valA, rfl, hp2⟩

end Ix.Kernel.Verify
