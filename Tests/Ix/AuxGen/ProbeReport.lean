import Ix.AuxGen.SourceService
import Lean

namespace Tests.Ix.AuxGen.ProbeReport
open Lean (Json toJson)
def name : Ix.Name → Json
  | .anonymous h => .arr #[.str "anonymous", .str (toString h), toJson h.hash.size]
  | .str p s h => .arr #[.str "str", name p, .str s, .str (toString h), toJson h.hash.size]
  | .num p i h => .arr #[.str "num", name p, toJson i, .str (toString h), toJson h.hash.size]
def complete (r : Ix.AuxGen.Source.Report) : Bool :=
  r.accepted ≤ r.blocks && r.notAccepted.size == r.blocks - r.accepted && r.refused.size == r.groupsRefused
def source (r : Ix.AuxGen.Source.Report) : Json := Json.mkObj [
  ("error", toJson r.error), ("blocks", toJson r.blocks), ("accepted", toJson r.accepted), ("met", toJson r.met),
  ("groupsAccepted", toJson r.groupsAccepted), ("groupsRefused", toJson r.groupsRefused),
  ("groupsBlocked", toJson r.groupsBlocked), ("groupsTier", toJson r.groupsTier), ("synthesised", toJson r.synthesised),
  ("notAccepted", .arr (r.notAccepted.map fun (n, e) => .arr #[name n, .str e])), ("refused", toJson r.refused), ("complete", .bool (complete r))]
def emit (probe : String) (fields : List (String × Json)) : IO Unit :=
  IO.println s!"[{probe}-outcome] {(Json.mkObj fields).compress}"
end Tests.Ix.AuxGen.ProbeReport
