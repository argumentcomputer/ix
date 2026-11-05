/-
  Kernel tutorial test runner.
  Reads test cases registered by TutorialDefs.lean via the env extension,
  then checks each through the full pipeline: Lean env → Ixon → kernel.
  Good constants must pass; bad constants must be rejected.

  The tutorial was written for the Rust kernel. The certified checker (IxC)
  gives four kinds of fixture another verdict, each with the check that
  stands in for the tutorial's (`nativeEvaluationFixtures`,
  `axiomFixtures`, `modelDeclines`, `sourceOnlyBad`), as
  `Tests.Ix.Kernel.Arena` does for the IxVM kernel.
-/
import Ix.Common
import Ix.Meta
import Ix.KernelCheck
import Ix.RoleBinding.Compile
import Ix.Resource.Typing
import Tests.Ix.Kernel.FocusedLeanCheck
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.Kernel.SourceIngressStep
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.TutorialDefs
import Tests.Ix.Kernel.NatReduction
import Tests.Ix.Kernel.StringReduction
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Tutorial

-- Re-export the shared `CheckError` type so existing call sites
-- (e.g. `Tests/Ix/Kernel/CheckEnv.lean`) keep working unchanged.
-- The single source of truth lives in `Ix/KernelCheck.lean`.
export Ix.KernelCheck (CheckError)

-- Re-export the shared check helper so existing call sites keep working
-- without an explicit `Ix.KernelCheck.` qualifier.
export Ix.KernelCheck (rsCheckConstsFFI)

private def defs : Lean.Name := `Tests.Ix.Kernel.TutorialDefs

/-- The `native_decide` fixtures (`Arena.nativeEvaluationFixtures` for the
IxVM kernel). Their proof is an auxiliary axiom that asserts the compiled
evaluation's result, a non-standard axiom IxC's strict policy declines, so
they must not pass. The kernel's own reduction of `Nat.ble`/`Nat.beq` on
literals is checked by `NatReduction`'s `natBle*`/`natBeq*` declarations. -/
def nativeEvaluationFixtures : Array Lean.Name := #[
  `natBleTrue, `natBleFalse, `natBeqTrue, `natBeqFalse]

/-- The tutorial's axioms. -/
def tutorialAxioms : Array Lean.Name :=
  #[defs ++ `aDepProp, defs ++ `mkADepProp, defs ++ `aType, defs ++ `aProp]

/-- Good fixtures that use the tutorial's axioms. IxC's strict policy
declines a non-standard axiom, so the strict check blocks them; with user
axioms admitted (`ix check-lean --allow-user-axioms` on the bound artifact,
`checkWithUserAxioms`) they must be accepted, conditional on tutorial
axioms only. -/
def axiomFixtures : Array Lean.Name := #[`letTypeDep, `letRed]

/-- Good fixtures IxC declines as outside its model, with the decline's
reason. `nestedSpecLocalF`'s field `P n F` looks nested, but `P`'s parameter
mentions a field binder: Lean's elaborator rejects the declaration, the Rust
kernel skipped the occurrence and accepted it, and IxC declines it, which
is neither an acceptance nor a rejection. -/
def modelDeclines : Array (Lean.Name × String) :=
  let reason := "decline: direct rec: a nested occurrence of the block (not modeled here)"
  #[(`nestedSpecLocalF, reason), (`nestedSpecLocalF.mk, reason), (`nestedSpecLocalF.rec, reason)]

/-- Bad fixtures whose badness is the duplicate names of their level
parameters (`Arena.knownIncompatible` for the IxVM kernel). The anonymous
compile keeps only their count and resolves a name to its first occurrence,
so the selected check, whose verdict is the anonymous run's, cannot see
them. Source mode reads the names, and its acceptance gives distinct level
parameters (`Ix.Cert.TraceSource.axiom_nodup` and its siblings), so it must
not accept them (`sourceVerdict`). -/
def sourceOnlyBad : Array Lean.Name := #[`tut06_bad01]

/-- The Source-mode verdict on `n` in `closure` (`kernel-source-ingress`'s
check, `Tests.Ix.Kernel.SourceIngressStep.run`), as `(outcome, reason)`. -/
def sourceVerdict (closure : List (Lean.Name × Lean.ConstantInfo)) (n : Lean.Name) :
    IO (Option (String × String)) := do
  let env := Tests.Ix.Kernel.SourceIngressStep.canon closure.toArray
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let r ← Tests.Ix.Kernel.SourceIngressStep.run pre env blocks
  return (r.rowOf (Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n))).map
    fun row => (row.outcome, row.reason)

/-- `names` checked with user axioms admitted: `closure` compiled and bound
as `ix compile` binds it (`Ix.RoleBinding.Compile.finalize`), then checked
as `ix check-lean --allow-user-axioms` checks a selection. Each name's
`(outcome, reason)`, and the names of the user axioms the checks admitted. -/
def checkWithUserAxioms (env : Lean.Environment) (closure : List (Lean.Name × Lean.ConstantInfo))
    (names : Array Lean.Name) :
    IO (Except String (Std.HashMap String (String × String) × Array String)) := do
  let out ← match ← Ix.CompileM.compileCertified env closure 8 with
    | .ok out => pure out
    | .error e => return .error s!"compile: {e}"
  unless out.failures.isEmpty do
    return .error s!"compile: {out.failures.toMap.size} constants failed"
  let artifact ← Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.certifiedBackend 8) env
    Ix.RoleBinding.Compile.nativeCertSource (Ix.Compile.CompileInput.plain closure) out.env
    Ix.Resource.typingLimits (existing? := out.existing?)
  let bytes ← IO.ofExcept (Ixon.serEnv artifact)
  let prepared ← match ← Ix.Cli.CheckLeanCmd.prepareInput bytes (allowUserAxioms := true) with
    | .ok p => pure p
    | .error e => return .error s!"prepare: {e.message}"
  let cfg : Ix.Cli.CheckLeanCmd.CheckCfg := { workers := 1, silent := true, progressMs := 0, slowMs := 0 }
  match ← Ix.Cli.CheckLeanCmd.runPrepared prepared cfg (.only (names.map toString)) with
  | .error e => return .error s!"check: {e.message}"
  | .ok report =>
    let outcomes := report.targets.foldl (init := {}) fun m t =>
      m.insert t.target.label (t.outcome, t.reason)
    let axiomNames := report.userAxioms.flatMap fun a =>
      (artifact.named.toList.filter (·.2.addr == a)).toArray.map (·.1.pretty)
    return .ok (outcomes, axiomNames)

def rsCheckMalformedRecRuleIxonFFI
    (consts : List (Lean.Name × Lean.ConstantInfo))
    (recName : Lean.Name) :
    IO (Option CheckError) := do
  let rawEnv := Ix.CompileM.canonInput consts.toArray 32
  let (compiledEnv, _) ← match Ix.Cert.compileReport rawEnv with
    | .ok res => pure res
    | .error err => return some (.compileError (toString err))
  let ixRecName := Ix.Name.fromLeanName recName
  let some named := compiledEnv.named[ixRecName]?
    | return some (.kernelException s!"missing recursor {recName}")
  let some lc := compiledEnv.consts[named.addr]?
    | return some (.kernelException s!"missing constant record for {recName}")
  let c ← match lc.get with
    | .ok c => pure c
    | .error e => return some (.kernelException e)
  let mutateRec (r : Ixon.Recursor) : Ixon.Recursor :=
    if h : r.rules.size ≥ 2 then
      let r0 := r.rules[0]
      let r1 := r.rules[1]
      { r with rules := r.rules.set! 1 { r1 with rhs := r0.rhs } }
    else r
  let mutatedInfo : Ixon.ConstantInfo := match c.info with
    | .recr r => .recr (mutateRec r)
    | .muts ms => .muts (ms.map fun
      | .recr r => .recr (mutateRec r)
      | m => m)
    | info => info
  let mutatedConst : Ixon.Constant := { c with info := mutatedInfo }
  let mutatedLazy := Ixon.LazyConstant.ofConstant mutatedConst
  let mutatedEnv : Ixon.Env := { compiledEnv with consts := compiledEnv.consts.insert named.addr mutatedLazy }
  let rows ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts mutatedEnv
  match rows[Ix.LeanIngress.ingressKey ixRecName]? with
  | some ("accept", _) | some ("typed", _) => return none
  | some (outcome, reason) => return some (.kernelException s!"{outcome}: {reason}")
  | none => return some (.kernelException s!"missing verdict for {recName}")

def testTutorialConsts : TestSeq :=
  .individualIO "kernel tutorial checks" none (do
    let leanEnv ← get_env!
    let testCases := TutorialMeta.getTestCases leanEnv

    -- Collect all constant names that need checking
    -- (skip renaming test cases — their collision check is done on the Lean side)
    let mut allNames : Array Lean.Name := #[]
    for tc in testCases do
      if tc.renamings.size == 0 then
        for n in tc.decls do
          allNames := allNames.push n

    -- Also add stdlib constants we want to verify. Using the `` `Foo.bar ``
    -- name-quotation syntax keeps the source compact and removes the old
    -- string → `Name` round-trip that `String.toName` used to do.
    let stdlibConsts : Array Lean.Name := #[
      `Acc, `Acc.intro, `Acc.rec,
      `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
      `Prod, `Prod.mk, `Prod.rec,
      `Eq, `Eq.refl, `Eq.rec,
      `List, `List.nil, `List.cons, `List.rec,
      `Exists, `Exists.intro, `Exists.rec
    ]
    for n in stdlibConsts do
      allNames := allNames.push n

    -- Also add the non-macro theorems/inductives defined directly
    -- (good_def/good_thm/bad_thm are auto-registered; these are plain defs/theorems/inductives).
    -- `p` is the common namespace; `p ++ n` uses `Lean.Name.append` to
    -- produce the fully-qualified name structurally (no string concat).
    let p : Lean.Name := `Tests.Ix.Kernel.TutorialDefs
    let directConsts : Array Lean.Name := #[
      -- TN (custom Nat)
      p ++ `TN, p ++ `TN.zero, p ++ `TN.succ, p ++ `TN.rec,
      p ++ `TN.add, p ++ `tnAddZero, p ++ `tnAddSucc,
      -- TRTree (reflexive)
      p ++ `TRTree, p ++ `TRTree.leaf, p ++ `TRTree.node,
      p ++ `TRTree.rec, p ++ `TRTree.left, p ++ `trtreeRecReduction,
      -- Good inductives
      p ++ `TTwoBool, p ++ `TTwoBool.mk, p ++ `TTwoBool.rec,
      p ++ `TN2, p ++ `TN2.zero, p ++ `TN2.succ, p ++ `TN2.rec,
      -- TColor + TRBTree
      p ++ `TColor, p ++ `TColor.r, p ++ `TColor.b, p ++ `TColor.rec,
      p ++ `TRBTree, p ++ `TRBTree.leaf, p ++ `TRBTree.red,
      p ++ `TRBTree.black, p ++ `TRBTree.rec, p ++ `TRBTree.id,
      -- TBoolProp
      p ++ `TBoolProp, p ++ `TBoolProp.a, p ++ `TBoolProp.b, p ++ `TBoolProp.rec,
      -- TSortElimProp
      p ++ `TSortElimProp, p ++ `TSortElimProp.mk, p ++ `TSortElimProp.rec,
      p ++ `TSortElimProp2, p ++ `TSortElimProp2.mk, p ++ `TSortElimProp2.rec,
      -- Universe level inductives
      p ++ `PredWithTypeField, p ++ `PredWithTypeField.mk, p ++ `PredWithTypeField.rec,
      p ++ `TypeWithTypeField, p ++ `TypeWithTypeField.mk, p ++ `TypeWithTypeField.rec,
      p ++ `TypeWithTypeFieldPoly, p ++ `TypeWithTypeFieldPoly.mk, p ++ `TypeWithTypeFieldPoly.rec,
      -- Recursor reduction defs
      p ++ `TN2.add, p ++ `myListAppended,
      -- Acc recursor type
      p ++ `accRecType,
      -- Eta corner cases: T structure
      p ++ `T, p ++ `T.mk, p ++ `T.rec,
      -- Adversarial: AdvNat (for nat-rec-rules test; AdvNat.rec tested via bad_raw_consts)
      p ++ `AdvNat, p ++ `AdvNat.zero, p ++ `AdvNat.succ,
      -- PropStructure (projection tests)
      p ++ `PropStructure, p ++ `PropStructure.mk, p ++ `PropStructure.rec,
      -- ProjDataIndex (projection tests)
      p ++ `ProjDataIndex, p ++ `ProjDataIndex.mk, p ++ `ProjDataIndex.rec,
      p ++ `projDataIndexRec,
      -- PropPair (struct eta for Prop test)
      p ++ `PropPair, p ++ `PropPair.mk, p ++ `PropPair.rec
    ]
    for n in directConsts do
      allNames := allNames.push n

    -- Deduplicate
    let constNames := allNames.toList.eraseDups.toArray

    -- The names of bad test cases (excluding renaming tests, whose constants
    -- are individually valid)
    let mut badNames : Std.HashSet Lean.Name := Std.HashSet.emptyWithCapacity 64
    for tc in testCases do
      if tc.outcome == .bad && tc.renamings.size == 0 then
        for n in tc.decls do
          badNames := badNames.insert n
    let advNatRec := p ++ `AdvNat.rec

    -- Raw constants stored by good_raw_consts/bad_raw_consts
    -- (inductInfo/ctorInfo/recInfo that couldn't go through the Lean kernel).
    let rawConsts := TutorialMeta.getRawConsts leanEnv
    let rawByName : Std.HashMap Lean.Name Lean.ConstantInfo :=
      rawConsts.foldl (fun m ci => m.insert ci.name ci)
        (Std.HashMap.emptyWithCapacity rawConsts.size)
    -- A compile input: the closure of `seeds` (filtering the Lean env down
    -- keeps the compile to the test constants), with the raw payloads among
    -- them added. A payload replaces the environment's declaration of its
    -- name (`AdvNat.rec`'s replaces the recursor Lean generated).
    let inputOf (seeds : Array Lean.Name) : List (Lean.Name × Lean.ConstantInfo) :=
      let payloads := seeds.filterMap fun n => rawByName[n]?.map fun ci => (n, ci)
      let pay : Std.HashMap Lean.Name Lean.ConstantInfo :=
        payloads.foldl (fun m (n, ci) => m.insert n ci) {}
      let (_, closed) := TutorialMeta.collectDepsWithExtras leanEnv pay seeds.toList
      closed.filter (!pay.contains ·.1) ++ payloads.toList

    -- The good constants (good cases, stdlib and direct constants) are
    -- compiled and checked together; each bad case is compiled and checked
    -- on its own. The certified compile is fail-closed: its report checks
    -- refuse an input whole when one family breaks the shapes its proof
    -- needs (`Ix.Cert.compileReport`; a raw recursor without its family's
    -- level parameters, `inductWrongCtorResLevel`, or the raw `AdvNat.rec`
    -- beside its alpha twin `Nat`, `twinRefusal` below). In one shared
    -- compile, a single adversarial payload would refuse every good
    -- constant and make every bad case pass vacuously.
    let goodNames := constNames.filter (!badNames.contains ·)
    let goodInput := inputOf goodNames
    IO.println s!"[kernel-tutorial] {testCases.size} test cases, {constNames.size} constants to check \
      ({goodNames.size} good in one closure of {goodInput.length} consts; bad cases one by one)"

    -- Tutorial batches are small and targeted — every constant's outcome
    -- is individually meaningful, so keep the verbose per-constant log.
    -- Results come back in the order of the names asked for, so we zip
    -- them back into a `Name → result` map below.
    let results ← rsCheckConstsFFI goodInput goodNames (goodNames.map fun _ => true) false
    let mut resultMap : Std.HashMap Lean.Name (Option CheckError) :=
      Std.HashMap.emptyWithCapacity constNames.size
    for i in [:goodNames.size] do
      resultMap := resultMap.insert goodNames[i]! results[i]!
    for tc in testCases do
      if tc.outcome == .bad && tc.renamings.size == 0 then
        let rs ← rsCheckConstsFFI (inputOf tc.decls) tc.decls (tc.decls.map fun _ => false) true
        for i in [:tc.decls.size] do
          resultMap := resultMap.insert tc.decls[i]! rs[i]!

    -- `AdvNat.rec` is an adversarial raw recursor payload. For this one
    -- test, compile `AdvNat`'s genuine family, mutate its compiled
    -- recursor's rule and check that exact malformed stored rule directly.
    if constNames.contains advNatRec then
      let advNatConsts := #[
        p ++ `AdvNat, p ++ `AdvNat.zero, p ++ `AdvNat.succ, advNatRec
      ]
      let malformedConstList := advNatConsts.toList.filterMap fun n =>
        (leanEnv.constants.find? n).map fun ci => (n, ci)
      let malformedResult ←
        rsCheckMalformedRecRuleIxonFFI malformedConstList advNatRec
      resultMap := resultMap.insert advNatRec malformedResult

    -- Check test case outcomes
    let mut passed := 0
    let mut failed := 0
    let mut errors : Array String := #[]

    -- `twinRefusal`: the raw `AdvNat.rec` beside `Nat`'s family. `AdvNat` is
    -- alpha-equivalent to `Nat` (and `TN`, `TN2`), so their one inductive
    -- block would hold two recursor records; the recursor index files
    -- `Nat.rec`'s under the block, which is not a published recursor of
    -- `AdvNat`'s family, and the compile's recursor check
    -- (`Ix.Cert.RecursorsOwned`) refuses the input whole. It is the refusal
    -- that refused the shared tutorial corpus while the payload was in it.
    match rawByName[advNatRec]? with
    | none =>
      failed := failed + 1
      errors := errors.push s!"  ✗ the raw payload {advNatRec} is missing"
    | some payload =>
      let named (ns : List Lean.Name) := ns.filterMap fun n =>
        (leanEnv.constants.find? n).map fun ci => (n, ci)
      let twin := named [``Nat, ``Nat.zero, ``Nat.succ, ``Nat.rec] ++
        named [p ++ `AdvNat, p ++ `AdvNat.zero, p ++ `AdvNat.succ] ++ [(advNatRec, payload)]
      match Ix.Cert.compileReport (Ix.CompileM.canonInput twin.toArray 32) with
      | .error e =>
        if ((toString e).splitOn "recursor check failed").length > 1 then
          passed := passed + 1
        else
          failed := failed + 1
          errors := errors.push s!"  ✗ BAD raw {advNatRec} beside Nat: refused, but not by \
            the recursor check: {e}"
      | .ok _ =>
        failed := failed + 1
        errors := errors.push s!"  ✗ BAD raw {advNatRec} beside Nat: the certified compile \
          accepted it"

    -- The axiom fixtures with the tutorial's axioms admitted (`axiomFixtures`).
    -- The opt-in needs a binding that binds the axiom roles
    -- (`Ix.RoleBinding.UserAxioms.axiomRoles`), so the input carries them.
    let conditional ← checkWithUserAxioms leanEnv
      (inputOf (axiomFixtures ++ #[``sorryAx, ``propext, ``Classical.choice])) axiomFixtures
    match conditional with
    | .error e =>
      failed := failed + 1
      errors := errors.push s!"  ✗ axiom fixtures with user axioms admitted: {e}"
    | .ok (_, admitted) =>
      IO.println s!"[kernel-tutorial] {axiomFixtures} with user axioms admitted: \
        conditional on {admitted}"
      let allowed := tutorialAxioms.map toString
      if admitted.isEmpty || !admitted.all allowed.contains then
        failed := failed + 1
        errors := errors.push s!"  ✗ axiom fixtures: admitted user axioms {admitted}, \
          expected tutorial axioms among {allowed}"
      else passed := passed + 1

    -- Check good test cases (must pass, but for the IxC verdicts above).
    -- When a good constant is rejected, pull the raw message string out of
    -- `CheckError.kernelException` rather than calling `repr err` — derived
    -- `Repr` for long multi-line strings is extremely slow (seconds per
    -- call) and can make the test appear to hang.
    for tc in testCases do
      if tc.outcome == .good then
        for n in tc.decls do
          let msg? : Option String := (resultMap.get? n).map fun
            | none => "accepted"
            | some (.kernelException m) => s!"kernel: {m}"
            | some (.compileError m) => s!"compile: {m}"
          if nativeEvaluationFixtures.contains n then
            -- must not pass: its proof is a declined `native_decide` axiom
            match resultMap.get? n with
            | some (some _) => passed := passed + 1
            | _ =>
              failed := failed + 1
              errors := errors.push s!"  ✗ GOOD {n} (native_decide): {msg?.getD "not found"}, \
                expected IxC not to accept it"
          else if let some (_, reason) := modelDeclines.find? (·.1 == n) then
            if msg? == some s!"kernel: {reason}" then passed := passed + 1
            else
              failed := failed + 1
              errors := errors.push s!"  ✗ GOOD {n} (outside IxC's model): {msg?.getD "not found"}, \
                expected kernel: {reason}"
          else if axiomFixtures.contains n then
            -- strict: blocked by the declined axiom; admitted: accepted
            let admitted := match conditional with
              | .ok (outcomes, _) => outcomes[toString n]?
              | .error _ => none
            match resultMap.get? n, admitted with
            | some (some (.kernelException m)), some (o, _) =>
              if m.startsWith "blocked: " && (o == "accept" || o == "typed") then
                passed := passed + 1
              else
                failed := failed + 1
                errors := errors.push s!"  ✗ GOOD {n} (tutorial axioms): strict {m}, with user \
                  axioms admitted {o}"
            | _, _ =>
              failed := failed + 1
              errors := errors.push s!"  ✗ GOOD {n} (tutorial axioms): strict {msg?.getD "not found"}; \
                with user axioms admitted {admitted}"
          else
            match resultMap.get? n with
            | some none => passed := passed + 1
            | _ =>
              failed := failed + 1
              errors := errors.push s!"  ✗ GOOD {n}: rejected with {msg?.getD "not found in results"}"

    -- Check bad test cases (must fail)
    for tc in testCases do
      if tc.outcome == .bad then
        if tc.renamings.size > 0 then
          -- Name collision test: check that the full renamed constant set has duplicates.
          -- Collect all target names, including auto-generated names (.rec, .mk, etc.)
          -- for renamed inductives.
          let mut allTargets : Array Lean.Name := #[]
          -- Build source→target map
          let renamingMap : Std.HashMap Lean.Name Lean.Name :=
            tc.renamings.foldl (fun m (s, t) => m.insert s t) (Std.HashMap.emptyWithCapacity tc.renamings.size)
          for (_, target) in tc.renamings do
            allTargets := allTargets.push target
          -- For each renamed inductive, add its expected auto-generated names
          -- (.rec, constructor suffixes) under the renamed prefix. These are
          -- "reserved" — any other constant mapping to them is a collision.
          for n in tc.decls do
            if let some ci := leanEnv.find? n then
              if let .inductInfo iv := ci then
                let indTarget := renamingMap.getD n n
                allTargets := allTargets.push (indTarget ++ `rec)
                for ctorName in iv.ctors do
                  let ctorSuffix := ctorName.componentsRev.head!
                  allTargets := allTargets.push (indTarget ++ ctorSuffix)
          let uniqueTargets := allTargets.toList.eraseDups
          if uniqueTargets.length < allTargets.size then
            passed := passed + 1  -- correctly detected collision
          else
            failed := failed + 1
            let targetStrs := allTargets.map toString
            errors := errors.push s!"  ✗ BAD renaming: expected name collision but none found in {targetStrs}"
          continue
        for n in tc.decls do
          if sourceOnlyBad.contains n then
            -- duplicate level-parameter names: Source mode must not accept it
            match ← sourceVerdict (inputOf tc.decls) n with
            | some (outcome, reason) =>
              IO.println s!"[kernel-tutorial] {n}: Source mode {outcome}: {reason}"
              if outcome != "accept" && outcome != "typed" then passed := passed + 1
              else
                failed := failed + 1
                errors := errors.push s!"  ✗ BAD {n}: Source mode {outcome} {reason}, \
                  expected it not to accept duplicate level parameters"
            | none =>
              failed := failed + 1
              errors := errors.push s!"  ✗ BAD {n}: no Source-mode verdict"
            continue
          match resultMap.get? n with
          | some (some _) => passed := passed + 1  -- correctly rejected
          | some none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ BAD {n}: should have been rejected but was accepted"
          | none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ BAD {n}: not found in results"

    -- Check direct theorems (must pass)
    for name in directConsts do
      match resultMap.get? name with
      | some none => passed := passed + 1
      | some (some err) =>
        failed := failed + 1
        let msg := match err with
          | .kernelException m => m
          | .compileError m    => s!"(compile) {m}"
        errors := errors.push s!"  ✗ {name}: {msg}"
      | none =>
        failed := failed + 1
        errors := errors.push s!"  ✗ {name}: not found"

    -- Check stdlib (must pass)
    for name in stdlibConsts do
      match resultMap.get? name with
      | some none => passed := passed + 1
      | some (some err) =>
        failed := failed + 1
        let msg := match err with
          | .kernelException m => m
          | .compileError m    => s!"(compile) {m}"
        errors := errors.push s!"  ✗ stdlib {name}: {msg}"
      | none =>
        failed := failed + 1
        errors := errors.push s!"  ✗ stdlib {name}: not found"

    for e in errors do
      IO.println e

    IO.println s!"[kernel-tutorial] {passed} passed, {failed} failed"
    if failed == 0 then
      return (true, passed, 0, none)
    else
      return (false, passed, passed + failed, some s!"{failed} checks failed")
  ) .done

def suite : List TestSeq := [testTutorialConsts]

end Tests.Ix.Kernel.Tutorial
