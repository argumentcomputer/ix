import Ix.IxVM.Consistency.StatementRel

namespace IxVM.Refinement.Claim
open IxVM.Consistency

/-- Safety of the record at an address and of the record of its projection owner. -/
def SourceSafe (E₀ : Ixon.Env) (a : _root_.Address) : Prop :=
  ∀ c, recordOf E₀ a = some c → InLogic c ∧
    ∀ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb → InLogic cb

end IxVM.Refinement.Claim
