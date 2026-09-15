import Compilatrix.Aiur.Check
import Compilatrix.Aiur.Derivation
import Compilatrix.Aiur.WellFounded

namespace Compilatrix.Aiur.Trace.Validated

open _root_.Aiur (G)

/-- The checked logical trace plus static row facts establishes finite
derivations. No connection to an emitted circuit or source DSL is implicit. -/
theorem public_derivation {trace : Trace} (checked : Validated trace)
    (static : StaticCertificate trace.RowId trace.Requires) {message : Message}
    (claim : message ∈ trace.publicClaims) : trace.Derivation message :=
  trace.public_derivation checked.activity checked.balanced checked.bound
    (trace.static_wellFounded checked.bound static) claim

/-- Every derived memory observation agrees with the same extracted heap. -/
theorem memory_agrees {trace : Trace} (checked : Validated trace)
    {bucket : Nat} {pointer : G} {values : List G}
    (derivation : trace.Derivation (.memory bucket pointer values)) :
    Memory.heap (Memory.cells trace) bucket pointer = some values := by
  obtain ⟨id, active, provided⟩ := derivation.has_provider
  exact Memory.row_agrees trace checked.memory id active provided

end Compilatrix.Aiur.Trace.Validated
