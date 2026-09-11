import Ix.Compiler.IxIR0.ReaddressProjectionSafe

/-!
# Executable oracle adaptation for IxIR₀ readdressing

The forward address action is intentionally not a global bijection: a newly
derived member key is fixed, while the corresponding transient key maps to it.
Consequently an addressed oracle must not pretend it can invert arbitrary
runtime values.

This module uses the narrower operation actually needed at the oracle
boundary.  It reverse-resolves only the called declaration key, passes the
already-addressed arguments to the legacy oracle, and maps any returned value
forward.  `Oracle.Readdressable` is the exact coherence condition ensuring
that this executable adapter commutes with the evaluator address action.
-/

namespace Ix.Compiler.IxIR0.Readdress

open Ix.Compiler.Ixon (Address)

namespace Renaming

private theorem source_ne_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true)
    {entry : Address × Address} (hentry : entry ∈ mapping) :
    entry.1 ≠ identity := by
  have hpair := (List.all_eq_true.mp hisolated) entry hentry
  simp only [Bool.and_eq_true] at hpair
  exact bne_iff_ne.mp hpair.1

private theorem target_ne_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true)
    {entry : Address × Address} (hentry : entry ∈ mapping) :
    entry.2 ≠ identity := by
  have hpair := (List.all_eq_true.mp hisolated) entry hentry
  simp only [Bool.and_eq_true] at hpair
  exact bne_iff_ne.mp hpair.2

theorem lookup_eq_none_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true) :
    mapping.lookup identity = none := by
  have hnone :
      List.find? (fun entry => entry.1 == identity) mapping = none :=
    List.find?_eq_none.mpr fun entry hentry hequal =>
      source_ne_of_isolates hisolated hentry
        (Address.eq_of_beq hequal)
  simp [MutualBlock.Renaming.lookup, hnone]

theorem reverseLookup_eq_none_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true) :
    reverseLookup mapping identity = none := by
  have hnone :
      List.find? (fun entry => entry.2 == identity) mapping = none :=
    List.find?_eq_none.mpr fun entry hentry hequal =>
      target_ne_of_isolates hisolated hentry
        (Address.eq_of_beq hequal)
  simp [reverseLookup, hnone]

@[simp] theorem apply_eq_self_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true) :
    MutualBlock.Renaming.apply mapping identity = identity := by
  simp [MutualBlock.Renaming.apply,
    lookup_eq_none_of_isolates hisolated]

@[simp] theorem reverseApply_eq_self_of_isolates
    {mapping : MutualBlock.Renaming} {identity : Address}
    (hisolated : isolates mapping identity = true) :
    reverseApply mapping identity = identity := by
  simp [reverseApply, reverseLookup_eq_none_of_isolates hisolated]

theorem apply_ne_of_ne_of_isolates
    {mapping : MutualBlock.Renaming} {identity address : Address}
    (hisolated : isolates mapping identity = true)
    (haddress : address ≠ identity) :
    MutualBlock.Renaming.apply mapping address ≠ identity := by
  unfold MutualBlock.Renaming.apply
  cases hlookup : mapping.lookup address with
  | none => simpa [hlookup] using haddress
  | some target =>
      obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
      have htarget : entry.2 = target := by simpa using hvalue
      subst target
      simpa [hlookup] using target_ne_of_isolates hisolated
        (List.mem_of_find?_eq_some hfind)

theorem reverseApply_ne_of_ne_of_isolates
    {mapping : MutualBlock.Renaming} {identity address : Address}
    (hisolated : isolates mapping identity = true)
    (haddress : address ≠ identity) :
    reverseApply mapping address ≠ identity := by
  unfold reverseApply
  cases hlookup : reverseLookup mapping address with
  | none => simpa [hlookup] using haddress
  | some source =>
      unfold reverseLookup at hlookup
      obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
      have hsource : entry.1 = source := by simpa using hvalue
      subst source
      simpa [hlookup] using source_ne_of_isolates hisolated
        (List.mem_of_find?_eq_some hfind)

end Renaming

namespace Oracle

/-- Executable addressed view of a legacy oracle. Arguments have already been
renamed by evaluator transport; only the call key is reverse-resolved. Any
result is mapped back into the addressed value universe. -/
def readdress (mapping : MutualBlock.Renaming) (before : IxIR0.Oracle) :
    IxIR0.Oracle :=
  let rename := MutualBlock.Renaming.apply mapping
  fun address arguments =>
    (before (Renaming.reverseApply mapping address) arguments).map
      (Value.mapAddresses rename)

/-- Exact observable coherence required by `readdress`: after reverse-resolving
the mapped call key, the legacy oracle's answer on addressed arguments must
have the same forward image as its answer on the original call and arguments.
This admits the scalar ABI and deliberately rejects an address-sensitive
oracle unless it provides its own coherent implementation. -/
def Readdressable (mapping : MutualBlock.Renaming)
    (before : IxIR0.Oracle) : Prop :=
  let rename := MutualBlock.Renaming.apply mapping
  ∀ address arguments,
    (before
          (Renaming.reverseApply mapping (rename address))
          (ValueList.mapAddresses rename arguments)).map
        (Value.mapAddresses rename) =
      (before address arguments).map (Value.mapAddresses rename)

/-- The executable adapter satisfies the exact oracle equation consumed by
evaluator and trace transport. -/
theorem readdress_compatible {mapping : MutualBlock.Renaming}
    {before : IxIR0.Oracle} (hbefore : Readdressable mapping before)
    (address : Address) (arguments : List Value) :
    readdress mapping before
        (MutualBlock.Renaming.apply mapping address)
        (ValueList.mapAddresses
          (MutualBlock.Renaming.apply mapping) arguments) =
      (before address arguments).map
        (Value.mapAddresses (MutualBlock.Renaming.apply mapping)) := by
  exact hbefore address arguments

/-- The empty oracle is readdressable for every map. -/
theorem Readdressable.empty (mapping : MutualBlock.Renaming) :
    Readdressable mapping (fun _ _ => none) := by
  intro address arguments
  rfl

/-- Split the coherence proof into independent key and argument conditions.
This is convenient for scalar oracles: their argument condition usually
follows from length preservation. -/
theorem Readdressable.of_key_and_arguments
    {mapping : MutualBlock.Renaming} {before : IxIR0.Oracle}
    (hkey : ∀ address arguments,
      before
          (Renaming.reverseApply mapping
            (MutualBlock.Renaming.apply mapping address))
          arguments = before address arguments)
    (harguments : ∀ address arguments,
      before address
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply mapping) arguments) =
        before address arguments) :
    Readdressable mapping before := by
  intro address arguments
  rw [hkey, harguments]

/-- A single-key oracle is coherent whenever the member map isolates that ABI
identity and structurally renamed arguments do not change its answer. -/
theorem Readdressable.of_isolated_key
    {mapping : MutualBlock.Renaming} {before : IxIR0.Oracle}
    {key : Address}
    (hisolated : Renaming.isolates mapping key = true)
    (hoffKey : ∀ address arguments, address ≠ key →
      before address arguments = none)
    (harguments : ∀ address arguments,
      before address
          (ValueList.mapAddresses
            (MutualBlock.Renaming.apply mapping) arguments) =
        before address arguments) :
    Readdressable mapping before := by
  apply Readdressable.of_key_and_arguments
  · intro address arguments
    by_cases haddress : address = key
    · subst address
      simp [Renaming.apply_eq_self_of_isolates hisolated,
        Renaming.reverseApply_eq_self_of_isolates hisolated]
    · have happly :
          MutualBlock.Renaming.apply mapping address ≠ key :=
        Renaming.apply_ne_of_ne_of_isolates hisolated haddress
      have hreverse :
          Renaming.reverseApply mapping
              (MutualBlock.Renaming.apply mapping address) ≠ key :=
        Renaming.reverseApply_ne_of_ne_of_isolates hisolated happly
      rw [hoffKey _ _ hreverse, hoffKey _ _ haddress]
  · exact harguments

end Oracle

namespace Result

/-- The executable oracle adapter discharges the context-renaming premise
from its compact coherence law. -/
theorem renames_preAddressCtx_readdressOracle {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    (beforeOracle : IxIR0.Oracle)
    (horacle : Oracle.Readdressable result.addressMap beforeOracle) :
    Ctx.Renames (MutualBlock.Renaming.apply result.addressMap)
      (result.preAddressCtx groups beforeOracle)
      (result.addressedCtx
        (Oracle.readdress result.addressMap beforeOracle)) :=
  result.renames_preAddressCtx haudit beforeOracle
    (Oracle.readdress result.addressMap beforeOracle)
    (Oracle.readdress_compatible horacle)

/-- Exact evaluator transport using the executable addressed oracle. -/
theorem run_readdressOracle_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result}
    (hrun : Readdress.run reserved groups main = .ok result)
    (beforeOracle : IxIR0.Oracle)
    (horacle : Oracle.Readdressable result.addressMap beforeOracle)
    (fuel : Nat := 100000) :
    (result.addressedCtx
        (Oracle.readdress result.addressMap beforeOracle)).run
        result.main fuel =
      mapResult (MutualBlock.Renaming.apply result.addressMap)
        ((result.preAddressCtx groups beforeOracle).run main fuel) :=
  run_of_run_eq_ok hrun beforeOracle
    (Oracle.readdress result.addressMap beforeOracle)
    (Oracle.readdress_compatible horacle) fuel

/-- Exact call-aware main-trace transport using the executable addressed
oracle. -/
theorem projectionSafeMain_readdressOracle_of_audit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    (beforeOracle : IxIR0.Oracle)
    (horacle : Oracle.Readdressable result.addressMap beforeOracle)
    {traceFuel : Nat} {value : Value}
    (trace : IxIR0.ProjectionSafe.Eval
      (result.rawCtx groups beforeOracle) traceFuel [] main value) :
    IxIR0.ProjectionSafe.Eval
      (result.addressedCtx
        (Oracle.readdress result.addressMap beforeOracle))
      traceFuel [] result.main
      (Value.mapAddresses
        (MutualBlock.Renaming.apply result.addressMap) value) :=
  result.projectionSafeMain_of_audit haudit beforeOracle
    (Oracle.readdress result.addressMap beforeOracle)
    (Oracle.readdress_compatible horacle) trace

end Result

end Ix.Compiler.IxIR0.Readdress
