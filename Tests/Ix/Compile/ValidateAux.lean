/-
  Comprehensive validation of the aux_gen compile pipeline.

  Eight phases:
    1. Aux_gen congruence (pre-compilation: original aux_gen matches Lean)
    2. Compilation succeeds (every input constant gets an address)
    3. No ephemeral leaks (original constants don't pollute the Ixon env)
    4. Alpha-equivalence group canonicity (same-class names share addresses)
    5. Decompilation with debug info succeeds
    6. Aux congruence roundtrip (post-compilation: decompiled aux_gen matches Lean)
    7. Decompilation without debug info succeeds
    8. Nested detection (build_compile_flat_block finds expected auxiliaries)

  Invoked via `lake test -- --ignored validate-aux`.
-/
import Ix.Common
import Ix.Meta
import Tests.Ix.Compile.Mutual
import Tests.Ix.Compile.Canonicity
import Tests.Ix.Kernel.TutorialDefs
import Lean

/-- Collect the transitive closure of constants referenced by a set of seed names. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .inductInfo v =>
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- The aux-heavy fixture corpus: seed names (fixture namespaces + aux_gen
    prereqs) resolved against `env` and closed over transitive deps. Shared
    between the `validate-aux` runner below and the `aux-gen-diff`
    cross-compiler harness (`Tests.Ix.Compile.AuxGenDiff`), so both gates
    always see the same corpus. -/
def validateAuxClosure (env : Lean.Environment)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let prefixes := [
    `Tests.Ix.Compile.Mutual,
    `Tests.Ix.Compile.Canonicity,
    -- IxVM ingress fixtures (Tests.Ix.IxVM) — nested/dedup shapes like
    -- IxVMInd.DedupM (two nested occurrences of one external inductive
    -- with distinct spec_params) that only otherwise compile under the
    -- full-env `rust-compile` runner.
    `IxVMInd,
    -- Partial/WellFounded fixture families: `partial def` mutual blocks
    -- whose opaques + `_unsafe_rec` witnesses form SCCs through the
    -- implementation edges — the alpha-collapse shape testCrossImpl
    -- caught diverging (Test.Ix.Fixtures.Partial.H._unsafe_rec, A9).
    `Test.Ix.Fixtures,
    --`Init,
    --`_private.Init,
    --`State,
    --`Lean,
    --`Tests.Ix.Kernel.TutorialDefs
  ]
  -- Module-system fixtures declared without `public` get private-mangled
  -- names (`_private.<module>.0.<name>` — e.g. the AuxDedup namespaces in
  -- Tests.Ix.Compile.Mutual). Match prefixes against the user-visible form
  -- so those constants are seeded too; otherwise Phase 4b's AuxDedup
  -- identity groups are fully absent and silently skipped.
  let mut seeds := env.constants.toList.filterMap fun (n, _) =>
    let visible := (Lean.privateToUserName? n).getD n
    if prefixes.any (·.isPrefixOf visible) then some n else none
  -- Add prereqs that aux_gen references but test fixtures don't directly use.
  -- .below uses PUnit/PProd (Type-level), .brecOn uses Eq/True.
  -- We need the full inductive family: type, constructors, and recursor.
  seeds := seeds ++ [
    `PUnit, `PUnit.unit, `PUnit.rec,
    `PProd, `PProd.mk, `PProd.rec,
    `Eq, `Eq.refl, `Eq.rec,
    `True, `True.intro, `True.rec,
    `OfNat, `OfNat.rec, `SizeOf, `SizeOf.rec,
    `Iff, `Iff.rec, `Add, `Add.rec, `HAdd, `HAdd.rec, `Nat, `Nat.rec,
    `Nat.brecOn.eq, `PULift, `PULift.rec,
    -- Tutorial fixtures declared with bare top-level names via `good_decl`
    -- (no `Tests.Ix.Kernel.TutorialDefs.` prefix). These are the rec-shape
    -- cases that fail aux_gen congruence under rust-compile.
    `reduceCtorParam, `reduceCtorParam.mk, `reduceCtorParam.rec,
    `reduceCtorParamRefl, `reduceCtorParamRefl.mk, `reduceCtorParamRefl.rec,
    `reduceCtorParamRefl2, `reduceCtorParamRefl2.mk, `reduceCtorParamRefl2.rec,
  ]
  return collectDeps env seeds

def runCompileValidateAux (env : Lean.Environment) : IO UInt32 := do
  IO.println "[validate-aux] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[validate-aux] {filtered.length} constants"

  IO.println "[validate-aux] calling Rust FFI..."
  let failures := Ix.CompileM.rsCompileValidateAuxFFI filtered
  IO.println s!"[validate-aux] total failures: {failures}"
  return if failures == 0 then 0 else 1
