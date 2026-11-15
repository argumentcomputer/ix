import IxVMRefinement.Decl.ThmBodyRole
import IxVMRefinement.Decl.ModeledRoleInstall
import IxVMRefinement.Decl.NativeReferenceStep

/-! # Storage evidence along the actual reference checking order

All ordinary steps retain the reader's exact storage relation. A native step retains its
actual checked run while normalization restoration is handled separately. Both cases add
fresh constants, so earlier storage witnesses survive the complete checking fold.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Consistency (InstallStep StoredAs)

/-- An actual checker step, retaining reader storage or the native normalization run. -/
inductive ReferenceStep (fuel : Nat) (env : Env .anon) : Declaration .anon → Env .anon → Prop
  | stored {d out} (installed : InstallStep env d out) : ReferenceStep fuel env d out
  | native {block nP parts out}
      (notPinned : basisPinHit block = none) (recognized : nativeParts? nP block = some parts)
      (run : DeclNativeRun .verified fuel env parts out) :
      ReferenceStep fuel env (.indDecl block nP) out

/-- Native normalization is isolated by the actual declaration dispatcher. -/
def NativeReferenceDecl : Declaration .anon → Prop
  | .indDecl block nP => basisPinHit block = none ∧ (nativeParts? nP block).isSome = true
  | _ => False

/-- Every reference step adds a distinct fresh prefix, including normalized native entries. -/
theorem ReferenceStep.freshChain {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : ReferenceStep fuel env d out) : ∃ new, FreshChain env new out := by
  cases step with
  | stored installed =>
    obtain ⟨new, equation, distinct, fresh, _, _⟩ := installed
    exact ⟨new, equation, distinct, fresh⟩
  | native _ recognized run =>
    obtain ⟨new, chain, _, _⟩ :=
      nativeRunJ_freshChain recognized ((verifiedRunMap _).native (declNativeRun_runJ run))
    exact ⟨new, chain⟩

/-- Non-native declarations already have the original public storage relation. -/
theorem ReferenceStep.installed {fuel : Nat} {env out : Env .anon} {d : Declaration .anon}
    (step : ReferenceStep fuel env d out) (ordinary : ¬ NativeReferenceDecl d) :
    InstallStep env d out := by
  cases step with
  | stored installed => exact installed
  | native notPinned recognized _ =>
    exact (ordinary ⟨notPinned, by rw [recognized]; rfl⟩).elim

/-- The sequence retains the actual intermediate checking environments. -/
inductive ReferenceTrace (fuel : Nat) : Env .anon → List (Declaration .anon) → Env .anon → Prop
  | nil (env) : ReferenceTrace fuel env [] env
  | cons {env middle out d ds} (step : ReferenceStep fuel env d middle)
      (tail : ReferenceTrace fuel middle ds out) : ReferenceTrace fuel env (d :: ds) out

/-- Fresh prefixes compose in checking order. -/
theorem ReferenceTrace.freshChain {fuel : Nat} {env out : Env .anon} {ds : List (Declaration .anon)}
    (trace : ReferenceTrace fuel env ds out) : ∃ new, FreshChain env new out := by
  induction trace with
  | nil env => exact ⟨[], freshChain_nil env⟩
  | cons step _ ih =>
    obtain ⟨head, first⟩ := step.freshChain
    obtain ⟨tail, rest⟩ := ih
    rw [rest.eq]
    exact ⟨tail ++ head, freshChain_prepend first rest.nodup rest.fresh⟩

/-- Existing stored constants remain members after the reference suffix. -/
theorem ReferenceTrace.mem {fuel : Nat} {env out : Env .anon} {ds : List (Declaration .anon)}
    (trace : ReferenceTrace fuel env ds out) {ci : ConstantInfo .anon}
    (member : ci ∈ env.consts) : ci ∈ out.consts := by
  obtain ⟨new, chain⟩ := trace.freshChain
  rw [chain.eq]
  exact List.mem_append_right new member

/-- Reader storage established by any ordinary declaration survives every later step. -/
theorem ReferenceTrace.stored {fuel : Nat} {env out : Env .anon} {ds : List (Declaration .anon)}
    (trace : ReferenceTrace fuel env ds out) {d : Declaration .anon}
    (declared : d ∈ ds) (ordinary : ¬ NativeReferenceDecl d)
    {ci₀ : ConstantInfo .anon} (member : ci₀ ∈ IxVM.Consistency.installs d) :
    ∃ ci ∈ out.consts, StoredAs ci ci₀ := by
  induction trace with
  | nil => cases declared
  | cons step tail ih =>
    rcases List.mem_cons.mp declared with rfl | later
    · obtain ⟨new, equation, _, _, covered, _⟩ := step.installed ordinary
      obtain ⟨ci, added, stored⟩ := covered ci₀ member
      refine ⟨ci, tail.mem ?_, stored⟩
      rw [equation]
      exact List.mem_append_left _ added
    · exact ih later

/-- The actual fresh fold supplies global distinctness of the final store. -/
theorem ReferenceTrace.distinct {fuel : Nat} {out : Env .anon} {ds : List (Declaration .anon)}
    (trace : ReferenceTrace fuel Env.empty ds out) : (out.consts.map (·.name)).Nodup := by
  obtain ⟨new, chain⟩ := trace.freshChain
  simpa only [chain.eq, Env.empty, List.append_nil] using chain.nodup

end IxVM.Refinement.Decl
