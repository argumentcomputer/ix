module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# `SetBase/LitParams` — the literal families carry no level parameters

Two theorems re-based out of `SetR/Bridge/Infer.lean` at THE
SEPARATION's S2 (task #161).  They read one arity conjunct off the
literal support guards (`natLitSupported`'s `natIndOk`,
`strLitSupported`'s `stringTyOk`) and say the stored declaration has an
empty `levelParams` list.  No model, no environment invariant — pure
`Env`/`ConstantInfo` arithmetic.

They came out with the two-edit sever: `Steps/InferP` and
`Steps/ReadsP` (graded lane) reached them through the 2U module
`Steps/InferQ`, whose import the sever removes.  Statements verbatim,
namespace (`ConLeche.SetR`) unchanged.
-/

namespace ConLeche.Semantics

/-- The `Nat` family's stored declaration carries no level parameters
(read off `natLitSupported`'s `natIndOk` conjunct). -/
theorem natName_levelParams_nil {env : Env}
    (hg : natLitSupported env = true) {ci : ConstantInfo}
    (hf : env.find? natName = some ci) :
    ci.toConstantVal.levelParams = [] := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨h1, -⟩, -⟩ := hg
  rw [hf] at h1
  cases ci with
  | indInfo cv caps =>
    simp only [natIndOk, Bool.and_eq_true] at h1
    simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h1.1
  | _ => simp [natIndOk] at h1

/-- The `String` family's stored declaration carries no level parameters
(read off `strLitSupported`'s `stringTyOk` conjunct). -/
theorem stringName_levelParams_nil {env : Env}
    (hg : strLitSupported env = true) {ci : ConstantInfo}
    (hf : env.find? stringName = some ci) :
    ci.toConstantVal.levelParams = [] := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  rw [hf] at h2
  simp only [stringTyOk, Bool.and_eq_true] at h2
  simpa [List.isEmpty_iff] using h2.1

end ConLeche.Semantics
