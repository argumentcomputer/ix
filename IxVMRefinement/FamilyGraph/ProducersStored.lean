import IxVMRefinement.FamilyGraph.Composition

/-! # A family the witness's environment stores stays installed along the fold

`FamilyRun.storedTwin` hands the twin row a family record the witness's environment stores whole,
each recursor with its model companion (`FamilyInstalled t envT rb crb`). Every environment the
fold reaches extends the witness's with distinct names, so the same constants are found there:
`familyInstalled_of_ext`. -/

namespace IxVM.Refinement.Typing

open TwinFamily (FamilyInstalled)

/-- **A family installed in the witness's environment is installed in every extension with
distinct names.** -/
theorem familyInstalled_of_ext {t : Ix.Kernel.RoleTable} {envT env : Ix.Kernel.Env .anon}
    {rb : _root_.Address} {crb : Ixon.Constant}
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    (h : FamilyInstalled t envT rb crb) : FamilyInstalled t env rb crb := by
  intro x hx
  obtain ⟨⟨cv, mI, rP, rules, hf⟩, hm⟩ := h x hx
  exact ⟨⟨cv, mI, rP, rules, find_of_ext hext hnd hf⟩,
    Ix.Kernel.Model.HasModel.mono (fun hk => find_of_ext hext hnd hk) hm⟩

end IxVM.Refinement.Typing
