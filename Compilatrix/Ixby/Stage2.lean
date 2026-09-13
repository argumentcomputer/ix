import Compilatrix.Ixby.Catalog

/-! Explicit compiler budgets for the retained, complete Stage2 source.
These bounds admit the original source bytes; they do not alter guest resource
limits or claim a target execution capacity. -/

namespace Compilatrix.Ixby.Stage2

/-- Measured on all 10,757 original constants: 3,173,456 stored expression
units, 10,374,993 expanded units, and 186,475,983 layer-1 visits. The largest
single compression input is 403,187 units; the largest layer-1 count is
46,699,176. Decoder sequence and depth limits remain the catalog defaults. -/
def catalogLimits : Ixon.Catalog.Limits := {
  ingress := { maxLayer1NodeVisits := 64 * 1024 * 1024 }
  sharing := {
    maxLayer1NodeVisits := 64 * 1024 * 1024
    maxCompressionInputUnits := 512 * 1024 }
  maxExpressionUnits := 4 * 1024 * 1024
  maxExpandedExpressionUnits := 16 * 1024 * 1024
  maxLayer1NodeVisits := 256 * 1024 * 1024 }

/-- Structural checking and raw erasure budgets for the same complete input.
The current certificate planner's limits are retained until its dependency
schedule and semantic coverage have been extended. -/
def sourceLimits : Pipeline.Limits := {
  maxExpressionUnits := 4 * 1024 * 1024
  maxExpandedExpressionUnits := 16 * 1024 * 1024
  maxLayer1NodeVisits := 256 * 1024 * 1024 }

end Compilatrix.Ixby.Stage2
