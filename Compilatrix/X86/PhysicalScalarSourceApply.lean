import Compilatrix.X86.PhysicalExportSourceApply

namespace Compilatrix.X86.PhysicalScalar
open Compilatrix.Pipeline (ValidatedCompilation validatedEvalCtx validatedMainFrame validatedMainSource)

variable {constants : List (Ixon.Address × Ixon.Constant)} {root : Ixon.Address}
  {config : Compilatrix.Pipeline.Config} {eraseFuel lowerFuel : Nat}

theorem Exported.sourceFunction
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    {fuel : Nat} {function : Ixon.Eval.Value}
    (oracles : @Compilatrix.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) fuel
      (validatedMainFrame root) [] validatedMainSource = .ok function) :
    ∃ rawFunction rawStore,
      @Compilatrix.Sim.InlinedValRel (validatedEvalCtx constants config) attached.source.rawCtx
        function rawFunction attached.source.memberScope ∧
      IxIR1.Sim.ValueGraph attached.source.functionRel rawStore
        (IxIR0.Readdress.Value.mapAddresses
          (IxIR0.MutualBlock.Renaming.apply attached.source.erasure.result.addressMap) rawFunction) (.loc 0) ∧
      IxIR1.Readdress.Store.mapAddresses
        (attached.source.lowering.result.rebuildRename attached.source.lowering.raw) rawStore =
        (closureStore exported.source.address exported.source.target).heap :=
  exported.source.sourceFunction attached oracles contextWF entry

abbrev SourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (result : Ixon.Eval.Value) :=
  SourceApplication attached exported.source values result

theorem Exported.sourceRun
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (exported : Exported attached.target.artifact.program (sourceProvenance attached))
    (values : Array Word) (arity : values.size = exported.source.target.signature.params.size)
    {entryFuel applyFuel : Nat} {function result : Ixon.Eval.Value}
    (oracles : @Compilatrix.Sim.OracleRel attached.source.memberScope
      (validatedEvalCtx constants config).inlineSharing attached.source.rawCtx)
    (contextWF : (validatedEvalCtx constants config).SharingWF)
    (entry : Ixon.Eval.eval (validatedEvalCtx constants config) entryFuel
      (validatedMainFrame root) [] validatedMainSource = .ok function)
    (applied : Ixon.Eval.applyMany (validatedEvalCtx constants config) applyFuel
      function (sourceArguments values) = .ok result) :
    Nonempty (SourceRun attached exported values result) :=
  exported.source.sourceRun attached values arity oracles contextWF entry applied

end Compilatrix.X86.PhysicalScalar
