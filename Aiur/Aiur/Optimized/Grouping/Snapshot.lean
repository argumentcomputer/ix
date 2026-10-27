import Aiur.Optimized.Physical
import Lean

/-! Offline compiler inputs for repeatable grouping experiments. The snapshot
contains the original physical chips, not a reconstruction from grouped rows.
Candidate groups still pass the ordinary grouping certificate before export. -/
namespace Aiur
open Lean

deriving instance ToJson, FromJson for Ty
deriving instance ToJson, FromJson for WireValue
deriving instance ToJson, FromJson for Scalar.Circuit.ArithExpr
deriving instance ToJson, FromJson for Circuit.Send
deriving instance ToJson, FromJson for Circuit.MemoryLookup
deriving instance ToJson, FromJson for Circuit.Chip

namespace Optimized.Grouping

structure Snapshot (F : Type) where
  chips : List (Circuit.Chip F)
  callables : List String
  entries : List String
  representatives : List (String × String)
  groups : List (String × List String)
  deriving ToJson, FromJson

def Snapshot.capture [Field F] [DecidableEq F] (artifact : Artifact F)
    (physical : Physical.Prepared artifact) (callables : List String)
    (groups : List (String × List String)) : Snapshot F :=
  ⟨physical.system.chips, callables, artifact.entries,
    callables.map (fun name => (name, physical.representative name)), groups⟩

end Optimized.Grouping
end Aiur
