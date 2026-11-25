import IxVM.Mirrors.Deserialize

/-! The mirrors of the Lists, WordLists, KernelLevels, KernelSubst and KernelKlimbs
functions and their callees, with their lemmas (`Aiur.Generic.Derive.Mirrors`), derived
from `IxVM.source`. -/

namespace IxVM.Refinement.Mirrors

/-- The Lists, WordLists, KernelLevels, KernelSubst and KernelKlimbs functions. -/
def kernelLevelsRoots : List String := [
  "Lists::is_empty", "Lists::length", "Lists::concat", "Lists::lookup",
  "Lists::lookup_or_default", "Lists::drop", "Lists::take", "Lists::snoc",
  "WordLists::depth_checked", "WordLists::length_u64", "WordLists::lookup_u64",
  "KernelLevels::expr_inst_levels", "KernelLevels::level_eq", "KernelLevels::literal_eq",
  "KernelSubst::ctx_trim", "KernelSubst::expr_glb",
  "KernelSubst::expr_inst1", "KernelSubst::expr_inst_many",
  "KernelKlimbs::klimbs_add", "KernelKlimbs::klimbs_sub", "KernelKlimbs::klimbs_le",
  "KernelKlimbs::klimbs_dec", "KernelKlimbs::divmod_256", "KernelKlimbs::klimbs_mul",
  "KernelKlimbs::klimbs_div", "KernelKlimbs::klimbs_mod", "KernelKlimbs::klimbs_gcd",
  "KernelKlimbs::klimbs_pow", "KernelKlimbs::klimbs_land", "KernelKlimbs::klimbs_lor",
  "KernelKlimbs::klimbs_xor_op", "KernelKlimbs::klimbs_shl", "KernelKlimbs::klimbs_shr"]

end IxVM.Refinement.Mirrors

#ixvm_mirrors IxVM.Refinement.Mirrors.kernelLevelsRoots
  (IxVM.Refinement.Mirrors.tagNRoots ++ IxVM.Refinement.Mirrors.deserializeRoots)
