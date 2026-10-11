/-
  Comprehensive validation of the aux_gen compile pipeline.

  Main phases, with additional canonicity and source-fidelity checks:
    1. Compilation succeeds (every input constant gets an address)
    2. Aux_gen congruence (standard-fixture oracle and production source claims)
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
import Tests.Ix.Compile.LevelSpellings
import Tests.Ix.Compile.Fixtures.LetNonDep
import Tests.Ix.Compile.Fixtures.NestedLevels
import Tests.Ix.Compile.Fixtures.AuxiliaryIdentity
import Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity
import Tests.Ix.Kernel.TutorialDefs
import Lean

/-- The fixture corpus uses standard Lean-generated auxiliaries, so retain the
extra generator/source oracle even for declarations compiled through their own
source bodies. Arbitrary source files use `rsCompileValidateAuxFFI` instead. -/
@[extern "rs_compile_validate_aux_oracle"]
opaque rsCompileValidateAuxOracleFFI
  : @& List (Lean.Name × Lean.ConstantInfo) → @& String → USize

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
        -- A definition's `all` (its `mutual` siblings) is metadata the
        -- compiled entry names, and meta kernel ingress resolves each name
        -- through `named`: the sibling must be in the closure even when the
        -- value does not mention it (structural, well-founded and `partial`
        -- mutual definitions go through auxiliaries).
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do refs := refs.insert mutName
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
    -- Level-spelling fixtures (canonicity §10.6): mk*-reducible spellings
    -- per rule, spelling twins, Géran order twins, a WF eq_def.
    `Tests.Ix.Compile.LevelSpellings,
    `Tests.Ix.Compile.Fixtures.LetNonDep,
    `Tests.Ix.Compile.Fixtures.NestedLevels,
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

private def validateSourceReport (path : System.FilePath) (sourceCount : Nat)
    (expectedOracleFailures : Array String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let check : Except String Unit := do
    let report ← Lean.Json.parse contents
    let phases ← (← report.getObjVal? "phases").getArr?
    unless (← report.getObjVal? "aborted") == .null do throw "validator aborted"
    unless (← (← report.getObjVal? "totalFailures").getNat?) == expectedOracleFailures.size do
      throw "unexpected total failure count"
    let required := #["1. Compilation", "2. Aux_gen congruence", "3. No ephemeral leaks",
      "4. Alpha-equivalence canonicity", "4b. Cross-namespace canonicity",
      "5. Decompile (with debug)", "6. Aux congruence (roundtrip)",
      "7. Decompile (without debug)", "7b. Roundtrip fidelity (per-constant)", "8. Nested detection"]
    unless phases.size == required.size do throw "missing or extra phase rows"
    for phaseName in required do
      let some row := phases.find? fun row => (row.getObjValAs? String "name").toOption == some phaseName
        | throw s!"missing phase {phaseName}"
      let failures ← (← row.getObjVal? "fail").getNat?
      let expected := if phaseName == "2. Aux_gen congruence" then expectedOracleFailures.size else 0
      unless failures == expected do throw s!"{phaseName}: expected {expected} failures, got {failures}"
      if phaseName == "1. Compilation" || phaseName == "7b. Roundtrip fidelity (per-constant)" then
        unless (← (← row.getObjVal? "pass").getNat?) == sourceCount do
          throw s!"{phaseName}: incomplete source coverage"
      if phaseName == "2. Aux_gen congruence" then
        unless (← (← row.getObjVal? "pass").getNat?) > 0 do throw "no positive recipe controls"
        let messages ← (← row.getObjVal? "failures").getArr?
        unless messages.size == expectedOracleFailures.size do throw "incomplete oracle failure details"
        let messages ← messages.mapM Lean.Json.getStr?
        for name in expectedOracleFailures do
          unless messages.any (·.startsWith (name ++ ":")) do
            throw s!"oracle failed for the wrong declaration; missing {name}"
  IO.ofExcept check

/-- Custom source bodies must pass ordinary validation. Treating the same
declarations as standard-generator fixtures is an intentionally false oracle
premise, and must fail for exactly the ten changed definitions. -/
def runCompileValidateAuxSource (env : Lean.Environment) : IO UInt32 := do
  let roots := #[`Tests.Ix.Compile.Fixtures.AuxiliaryIdentity,
    `Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity]
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if roots.any (·.isPrefixOf name) then some name else none
  unless !seeds.isEmpty do throw <| IO.userError "custom auxiliary source fixtures missing"
  let source := collectDeps env seeds
  let dir : System.FilePath := (← IO.getEnv "VALIDATE_AUX_SOURCE_KEEP").getD
    "plans/tasks/lean-to-ixon-correctness/aux-source-validation-gate"
  IO.FS.createDirAll dir
  let normalReport := dir / "source.json"
  let ordinary := Ix.CompileM.rsCompileValidateAuxFFI source normalReport.toString
  unless ordinary == 0 do throw <| IO.userError s!"ordinary source validator failed: {ordinary}"
  validateSourceReport normalReport source.length #[]
  let oracleReport := dir / "oracle.json"
  IO.println "[validate-aux-source] negative control: ten custom definitions must fail the standard-generator oracle"
  let oracle := rsCompileValidateAuxOracleFFI source oracleReport.toString
  let expected := #[
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.BeforeOwner.Tree.below",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Changed.A.casesOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Changed.B.casesOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.DifferentType.Box.casesOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.SameType.Box.casesOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.SameType.Box.recOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryIdentity.Unrelated.Box.casesOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity.Main.Odd.brecOn",
    "Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity.Go.Odd.brecOn.go",
    "Tests.Ix.Compile.Fixtures.AuxiliaryFamilyIdentity.Below.Odd.below"]
  unless oracle.toNat == expected.size do throw <| IO.userError s!"wrong oracle result: {oracle}"
  validateSourceReport oracleReport source.length expected
  IO.println s!"[validate-aux-source] {source.length} source declarations preserved; all phases covered; ten incorrect oracle assumptions rejected"
  return 0

def runCompileValidateAux (env : Lean.Environment) : IO UInt32 := do
  IO.println "[validate-aux] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[validate-aux] {filtered.length} constants"

  IO.println "[validate-aux] calling Rust FFI..."
  let failures := rsCompileValidateAuxOracleFFI filtered ""
  IO.println s!"[validate-aux] total failures: {failures}"
  if failures != 0 then return 1
  runCompileValidateAuxSource env
