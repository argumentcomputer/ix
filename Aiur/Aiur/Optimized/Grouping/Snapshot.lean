import Aiur.Optimized.Physical
import Aiur.Optimized.Depth.Basic
import Lean

/-! Offline compiler inputs for repeatable grouping experiments. The snapshot
contains the depth pass's chips (`Depth.system` of the original physical
chips, as the trace exporter groups them), not a reconstruction from grouped
rows. Candidate groups still pass the ordinary grouping certificate before
export. -/
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

/-- Capture the grouping inputs of the depth system `Depth.system cfg physical.system`,
with `cfg` the exporter's configuration (`Trace.depthConfig`). `callables` are the
original execution callables, functions then maps; the depth pass's range maps
follow them, in the order `Trace.depthBytecode` appends them. -/
def Snapshot.capture [Field F] [DecidableEq F] (artifact : Artifact F)
    (physical : Physical.Prepared artifact) (cfg : Depth.Config) (callables : List String)
    (groups : List (String × List String)) : Snapshot F :=
  let callables := callables ++ cfg.limbs.dedup.map Depth.rangeName
  ⟨(Depth.system cfg physical.system).chips, callables, artifact.entries,
    callables.map (fun name => (name, physical.representative name)), groups⟩

end Optimized.Grouping
end Aiur
