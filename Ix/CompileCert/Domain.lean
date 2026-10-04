import Ix.CompileCert.Faithful

/-! # Initial direct-cone coverage predicates

These predicates are checked on a supplied finite source inventory. They
are not the final `Dom` for L4 totality and do not classify unsupported
source features as invalid Lean. Target correspondence must still be
established from the actual reader stream.
-/

namespace Ix.CompileCert

def DirectDomain (s : Source) (roots : List Lean.Name) (m : SourceMap) : Prop :=
  CompleteSource s roots ∧ MapComplete s m

instance (s : Source) (roots : List Lean.Name) (m : SourceMap) :
    Decidable (DirectDomain s roots m) :=
  inferInstanceAs (Decidable (CompleteSource s roots ∧ MapComplete s m))

end Ix.CompileCert
