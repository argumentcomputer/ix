import Compilatrix.Coverage.Snapshot

/-! Shared JSON observations for source-driven heap fixtures. -/

namespace Compilatrix.Coverage

open Lean

deriving instance ToJson for IxIR1.RVal
deriving instance ToJson for IxIR1.Node
deriving instance ToJson for IxIR1.NodeBox
deriving instance ToJson for IxIR1.Store
deriving instance ToJson for IxIR2.Eval.Counters
deriving instance ToJson for IxIR2.Eval.Store

end Compilatrix.Coverage
