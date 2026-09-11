import Ix.Compiler.Recursion.Pipeline
import Ix.Compiler.IxIR0.RecursionSim

/-! The validated Ixon entry composed with the exact selected IxIR₀ program.
The source certificate, not the recognizer, supplies the erasure relation.
The later lowering traces remain available on `Outcome.recovered`.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

/-- Source-facing recovery, including literal fallback after an optional
backend failure. The only source premises are the existing sharing and oracle
contracts and a successful Ixon execution. -/
theorem Compilation.sourceRefines
    {constants : List (Address × Constant)} {root : Address}
    {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}
    (compilation : Compilation constants root config eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Ix.Compiler.Sim.OracleRel compilation.source.memberScope
      (Pipeline.validatedEvalCtx constants config).inlineSharing
      { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
    (hctx : (Pipeline.validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource = .ok sourceValue) :
    ∃ targetFuel targetValue,
      IxIR0.eval { env := IxIR0.Env.ofList compilation.outcome.selected.declarations }
        targetFuel [] compilation.outcome.selected.main = .ok targetValue ∧
      @Ix.Compiler.Sim.InlinedValRel (Pipeline.validatedEvalCtx constants config)
        { env := IxIR0.Env.ofList compilation.source.erasure.result.raw }
        sourceValue targetValue compilation.source.memberScope := by
  letI : Ix.Compiler.Sim.MemberScope := compilation.source.memberScope
  have hframe : (Pipeline.validatedMainFrame root).SharingWF := by
    constructor
    · rfl
    · intro index member hget
      simp [Pipeline.validatedMainFrame] at hget
  have hbelow : Ixon.Sharing.sharesBelow (Pipeline.validatedMainFrame root).sharing.size
      Pipeline.validatedMainSource = true := rfl
  have hinlined := Ixon.Eval.eval_inlineSharing hctx hframe .nil hbelow hsource
  have hentry := compilation.source.entry.related
  rw [EraseValidator.inlineTables_tablesOfFrame] at hentry
  obtain ⟨rawFuel, rawValue, hraw, hrelated⟩ :=
    Ix.Compiler.Sim.erasure_sim_with_members compilation.source.members horacles
      hinlined.1 hentry (by
        simpa [Ixon.Eval.valuesInlineSharing] using
          (Ix.Compiler.Sim.EnvRel.nil
            (ectx := (Pipeline.validatedEvalCtx constants config).inlineSharing)
            (ictx := { env := IxIR0.Env.ofList compilation.source.erasure.result.raw })
            (refs := (Pipeline.validatedMainFrame root).inlineSharing.refs)
            (muts := (Pipeline.validatedMainFrame root).inlineSharing.selfMuts)
            (sa := (Pipeline.validatedMainFrame root).inlineSharing.selfAddr)))
  rw [compilation.source.entryTarget] at hraw
  obtain ⟨targetFuel, htarget⟩ := compilation.outcome.selected.forwardSimulation hraw
  exact ⟨targetFuel, rawValue, htarget, hrelated⟩

end Ix.Compiler.Recursion
