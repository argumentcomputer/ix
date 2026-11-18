import IxVMRefinement.Binding.OpCertObs
import IxVMRefinement.Binding.SubstConstProj

/-! # No operation certificate projects its operation, at every run

`Binding.CertProjFree` (the composed residual's hypothesis `certProjFree`) holds of every call
list. `KernelSubst::subst_const`'s projection arm compares the projected structure with the
operation's address and refuses equality, at every projection it reaches, under binders and
`let`s included (`subst_const_path_noProj`); so at the substitution's output heap every
projection reachable from its input has its structure elsewhere (`subst_const_proj_ne`), which
is the premise of `certProjFree_of_subst`. -/

namespace IxVM.Refinement.Binding

/-- **No certificate of a well-founded operation projects the operation**, at every run. -/
theorem certProjFree_bindingRun :
    ∀ calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F), CertProjFree calls :=
  certProjFree_of_subst @subst_const_proj_ne

end IxVM.Refinement.Binding
