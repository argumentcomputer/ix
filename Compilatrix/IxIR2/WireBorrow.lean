import Compilatrix.IxIR2.WirePipeline
import Compilatrix.Borrow.Pipeline

/-! Canonical snapshots retain the actual borrowed signatures, lenders,
instructions and selected/fallback program of source-certified inference. -/

namespace Compilatrix.IxIR2.Wire

def borrowPassVersion : String := "borrowed-direct-calls/1"

def ofBorrow {constants root config world eraseFuel lowerFuel options}
    (attached : Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (selection : Compilatrix.Borrow.Selection attached options) : Artifact :=
  let base := ofCompiled attached.compiled
  { base with
    policy := { base.policy with passes := if selection.attempt.isOk then #[borrowPassVersion] else #[] }
    program := selection.program }

theorem ofBorrow_program {constants root config world eraseFuel lowerFuel options}
    (attached : Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (selection : Compilatrix.Borrow.Selection attached options) :
    (ofBorrow attached selection).program = selection.program := rfl

theorem ofBorrow_context {constants root config world eraseFuel lowerFuel options}
    (attached : Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (selection : Compilatrix.Borrow.Selection attached options) :
    (ofBorrow attached selection).context = attached.target.artifact.validationContext :=
  ofCompiled_context attached.compiled

theorem ofBorrow_validated {constants root config world eraseFuel lowerFuel options}
    (attached : Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (selection : Compilatrix.Borrow.Selection attached options) :
    ∃ stats, Validate.validateWithPolicy (ofBorrow attached selection).policy.credits Validate.defaultLimits
      (ofBorrow attached selection).context (ofBorrow attached selection).program = .ok stats := by
  rw [ofBorrow_context, ofBorrow_program]
  exact selection.valid

theorem ofBorrow_matches {constants sourceRoot config world eraseFuel lowerFuel options}
    (attached : Pipeline.Attached constants sourceRoot config world eraseFuel lowerFuel)
    (selection : Compilatrix.Borrow.Selection attached options)
    {limits : Compilatrix.IxIR.Bounded.Limits} {bytes : ByteArray} {root : Compilatrix.Ixon.Address}
    (decoded : Addressed limits bytes root) (fits : (ofBorrow attached selection).Fits limits)
    (identity : (ofBorrow attached selection).address = root)
    (collision : Compilatrix.Ixon.Address.Blake3NoCollision
      decoded.artifact.preimage (ofBorrow attached selection).preimage) :
    decoded.artifact.program = selection.program ∧
      decoded.artifact.context = attached.target.artifact.validationContext := by
  rw [decoded.matches (ofBorrow attached selection) fits identity collision]
  exact ⟨rfl, ofBorrow_context attached selection⟩

end Compilatrix.IxIR2.Wire
