import Ix.Compiler.IxIR0.Examples
import Ix.Compiler.IxIR0.ReaddressOracle

/-!
# Coherence for the modeled IxIR₀ Nat-add oracle

The trusted-extern ledger records `IxIR0.Examples.oracle` as the concrete
test-only scalar ABI at `Examples.natAddExt`.  This module discharges the
generic readdressing adapter's coherence law for that exact implementation.
The only namespace premise is the executable isolation certificate carried by
successful whole-program readdressing.
-/

namespace Ix.Compiler.IxIR0.Readdress.Oracle

open Ix.Compiler.Ixon (Address)

private theorem examplesOracle_mapArguments
    (mapping : MutualBlock.Renaming) (address : Address)
    (arguments : List Value) :
    Examples.oracle address
        (ValueList.mapAddresses
          (MutualBlock.Renaming.apply mapping) arguments) =
      Examples.oracle address arguments := by
  by_cases haddress : address = Examples.natAddExt
  · subst address
    simp only [Examples.oracle, BEq.rfl, if_true]
    cases arguments with
    | nil => simp
    | cons first rest =>
      cases rest with
      | nil => simp
      | cons second tail =>
        cases tail with
        | nil =>
          cases first <;> cases second <;>
            simp [Value.mapAddresses]
        | cons _ _ => simp
  · simp [Examples.oracle, haddress]

/-- The concrete literal-Nat addition model is coherent with every member map
that isolates its ledger identity. -/
theorem Readdressable.examples_of_isolates
    {mapping : MutualBlock.Renaming}
    (hisolated : Renaming.isolates mapping Examples.natAddExt = true) :
    Readdressable mapping Examples.oracle := by
  apply Readdressable.of_isolated_key hisolated
  · intro address arguments haddress
    simp [Examples.oracle, haddress]
  · exact examplesOracle_mapArguments mapping

/-- Successful whole-program addressing supplies the isolation premise when
the Nat-add ABI key is stable, reserved, or externally referenced. -/
theorem Readdressable.examples_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result} (hrun : Readdress.run reserved groups main = .ok result)
    (hidentity : Examples.natAddExt ∈
      oracleIdentities reserved groups main) :
    Readdressable result.addressMap Examples.oracle :=
  Readdressable.examples_of_isolates
    (Readdress.isolates_of_run_eq_ok hrun hidentity)

end Ix.Compiler.IxIR0.Readdress.Oracle
