import Ix.Compiler.EraseAddressed
import Ix.Compiler.IxIR0.ReaddressOracle

/-!
# Semantic boundary for addressed erasure

`EraseAddressed.run` deliberately retains the legacy eraser output and then
applies the certified cycle-safe IxIR₀ readdresser.  This module exposes both
halves of that executable audit as ordinary equalities and composes the
IxIR₀ evaluator-equivariance theorem with the artifact-facing erasure API.

The source evaluator context contains the legacy declarations plus stable
aliases for derived keys.  It therefore agrees exactly with every lookup in
the legacy environment while being total enough for closures or recursor
values that already contain a derived address.
-/

namespace Ix.Compiler.EraseAddressed

open Ix.Compiler.Ixon (Address Constant)

namespace Result

/-- The exact legacy declaration environment consumed by the erasure
validator before block readdressing. -/
def rawCtx (result : Result)
    (oracle : IxIR0.Oracle := fun _ _ => none) : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList result.raw, oracle }

/-- The recorded raw declarations are exactly the grouped eraser output. -/
theorem raw_eq_grouped {result : Result} {ctx : Erase.EraseCtx}
    {consts : List (Address × Constant)} {main : IxIR0.Expr} {fuel : Nat}
    (haudit : result.semanticAudit ctx consts main fuel = true) :
    result.raw = IxIR0.Readdress.rawDeclarations result.groups := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  exact (beq_iff_eq).mp haudit.1.1

/-- The legacy eraser succeeded with exactly the raw declarations retained in
the addressed artifact. -/
theorem eraseProgram_eq_ok {result : Result} {ctx : Erase.EraseCtx}
    {consts : List (Address × Constant)} {main : IxIR0.Expr} {fuel : Nat}
    (haudit : result.semanticAudit ctx consts main fuel = true) :
    Erase.eraseProgram ctx consts fuel = .ok result.raw := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  cases herase : Erase.eraseProgram ctx consts fuel with
  | error error => simp [herase] at haudit
  | ok raw =>
      have hequal : raw = result.raw :=
        (beq_iff_eq).mp (by simpa [herase] using haudit.1.2)
      exact congrArg Except.ok hequal

/-- The addressed half retains the complete whole-program semantic audit. -/
theorem addressed_audit {result : Result} {ctx : Erase.EraseCtx}
    {consts : List (Address × Constant)} {main : IxIR0.Expr} {fuel : Nat}
    (haudit : result.semanticAudit ctx consts main fuel = true) :
    result.addressed.semanticAudit (consts.map (·.1)) result.groups main =
      true := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  exact haudit.2

end Result

/-- Successful addressed erasure transports closed IxIR₀ evaluation through
the certified mutual-block map.  Extern behavior is parameterized by the
same structural oracle-equivariance condition as the generic evaluator
theorem. -/
theorem run_semantics_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply result.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap)))
    (evalFuel : Nat := 100000) :
    (result.addressed.addressedCtx afterOracle).run result.main evalFuel =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.addressed.preAddressCtx result.groups beforeOracle).run
          main evalFuel) := by
  have haudit := semanticAudit_of_run_eq_ok hrun
  have haddressed := result.addressed_audit haudit
  simp only [Result.main, Result.addressMap]
  rw [result.addressed.main_eq_mapAddresses haddressed]
  exact IxIR0.Readdress.Ctx.run_mapAddresses
    (result.addressed.renames_preAddressCtx haddressed
      beforeOracle afterOracle horacle)
    main evalFuel

/-- Pure addressed programs require no oracle premise. -/
theorem run_emptyOracle_semantics_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (evalFuel : Nat := 100000) :
    (result.addressed.addressedCtx).run result.main evalFuel =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.addressed.preAddressCtx result.groups).run main evalFuel) := by
  apply run_semantics_of_run_eq_ok hrun
    (fun _ _ => none) (fun _ _ => none) _ evalFuel
  intro address arguments
  rfl

/-- A successful legacy-side run yields the address-renamed value in the
addressed artifact. -/
theorem run_success_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply result.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap)))
    {evalFuel : Nat} {value : IxIR0.Value}
    (hsource :
      (result.addressed.preAddressCtx result.groups beforeOracle).run
        main evalFuel = .ok value) :
    (result.addressed.addressedCtx afterOracle).run result.main evalFuel =
      .ok (IxIR0.Readdress.Value.mapAddresses
        (IxIR0.MutualBlock.Renaming.apply result.addressMap) value) := by
  rw [run_semantics_of_run_eq_ok hrun beforeOracle afterOracle horacle
    evalFuel, hsource]
  rfl

/-- A successful addressed erasure transports the validator's exact
call-aware main trace from its literal raw environment to the final emitted
environment. -/
theorem run_projectionSafeMain_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply result.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply result.addressMap)))
    {traceFuel : Nat} {value : IxIR0.Value}
    (trace : IxIR0.ProjectionSafe.Eval (result.rawCtx beforeOracle)
      traceFuel [] main value) :
    IxIR0.ProjectionSafe.Eval
      (result.addressed.addressedCtx afterOracle) traceFuel [] result.main
      (IxIR0.Readdress.Value.mapAddresses
        (IxIR0.MutualBlock.Renaming.apply result.addressMap) value) := by
  have haudit := semanticAudit_of_run_eq_ok hrun
  have hraw := result.raw_eq_grouped haudit
  have haddressed := result.addressed_audit haudit
  have trace' : IxIR0.ProjectionSafe.Eval
      (result.addressed.rawCtx result.groups beforeOracle)
      traceFuel [] main value := by
    simpa [Result.rawCtx, IxIR0.Readdress.Result.rawCtx, hraw] using trace
  exact result.addressed.projectionSafeMain_of_audit haddressed
    beforeOracle afterOracle horacle trace'

/-- Pure addressed programs transport their exact main trace without an
oracle premise. -/
theorem run_emptyOracle_projectionSafeMain_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    {traceFuel : Nat} {value : IxIR0.Value}
    (trace : IxIR0.ProjectionSafe.Eval result.rawCtx traceFuel [] main value) :
    IxIR0.ProjectionSafe.Eval result.addressed.addressedCtx traceFuel []
      result.main
      (IxIR0.Readdress.Value.mapAddresses
        (IxIR0.MutualBlock.Renaming.apply result.addressMap) value) := by
  apply run_projectionSafeMain_of_run_eq_ok hrun
    (fun _ _ => none) (fun _ _ => none) _ trace
  intro address arguments
  rfl

/-- Executable-oracle specialization of closed evaluator transport. The
caller proves only the compact legacy-oracle coherence law; the addressed
oracle and the full evaluator compatibility equation are constructed here. -/
theorem run_readdressOracle_semantics_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (beforeOracle : IxIR0.Oracle)
    (horacle : IxIR0.Readdress.Oracle.Readdressable result.addressMap
      beforeOracle)
    (evalFuel : Nat := 100000) :
    (result.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress result.addressMap beforeOracle)).run
        result.main evalFuel =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.addressed.preAddressCtx result.groups beforeOracle).run
          main evalFuel) :=
  run_semantics_of_run_eq_ok hrun beforeOracle
    (IxIR0.Readdress.Oracle.readdress result.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible horacle) evalFuel

/-- Executable-oracle specialization of exact call-aware trace transport. -/
theorem run_readdressOracle_projectionSafeMain_of_run_eq_ok
    {ctx : Erase.EraseCtx} {consts : List (Address × Constant)}
    {main : IxIR0.Expr} {eraseFuel : Nat} {result : Result}
    (hrun : run ctx consts main eraseFuel = .ok result)
    (beforeOracle : IxIR0.Oracle)
    (horacle : IxIR0.Readdress.Oracle.Readdressable result.addressMap
      beforeOracle)
    {traceFuel : Nat} {value : IxIR0.Value}
    (trace : IxIR0.ProjectionSafe.Eval (result.rawCtx beforeOracle)
      traceFuel [] main value) :
    IxIR0.ProjectionSafe.Eval
      (result.addressed.addressedCtx
        (IxIR0.Readdress.Oracle.readdress result.addressMap beforeOracle))
      traceFuel [] result.main
      (IxIR0.Readdress.Value.mapAddresses
        (IxIR0.MutualBlock.Renaming.apply result.addressMap) value) :=
  run_projectionSafeMain_of_run_eq_ok hrun beforeOracle
    (IxIR0.Readdress.Oracle.readdress result.addressMap beforeOracle)
    (IxIR0.Readdress.Oracle.readdress_compatible horacle) trace

end Ix.Compiler.EraseAddressed
