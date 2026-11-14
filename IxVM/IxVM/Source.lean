import IxVM.Static

namespace IxVM

/-- The claim-verification entrypoint. -/
def entry : String := "IxVM::verify_claim"

/-- The executable source, assembled from the same named functions used in proofs. -/
def source : Aiur.Generic.Source F := ⟨program, coreTables, tablesChecked⟩

end IxVM
