import Ix.Compiler.UniqueReuse.ModeCheck
import Ix.Compiler.IxIR0.UniqueReverseSim

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Address Constant)

/-- The original successful source value is related to the checked reversal
value. Its ownership modes and syntax come from the compiler certificate;
callers supply only the established source sharing/oracle contract. -/
theorem CheckedSource.sourceValue
    {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat}
    {source : Pipeline.CertifiedErasure constants entry config .saturatedRecursorV1 .unique checkFuel eraseFuel}
    (checked : CheckedSource source) {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel entry.frame []
      entry.source = .ok sourceValue) :
    @Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
      { env := IxIR0.Env.ofList source.erasure.result.raw }
      sourceValue checked.recovery.checked.plan.value source.memberScope := by
  obtain ⟨fuel, value, heval, hrelated⟩ := source.sourceRefines horacles hctx hsource
  have heq := IxIR0.Recursion.Evaluates.unique ⟨fuel, heval⟩ checked.recovery.checked.sourceEvaluates
  simpa only [heq] using hrelated

end Ix.Compiler.UniqueReuse
