import IxVM.Elab
import IxVM.Tables

/-! Elaborate the imported Aiur declarations once. The resulting named functions
are the definitions used both by `program` and by the refinement proofs. -/

set_option maxRecDepth 100000

#ixvm_program
