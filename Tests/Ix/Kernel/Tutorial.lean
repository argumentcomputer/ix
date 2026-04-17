/-
  Kernel tutorial test runner.
  Reads test cases registered by TutorialDefs.lean via the env extension,
  then checks each through the full pipeline: Lean env → Ixon → kernel.
  Good constants must pass; bad constants must be rejected.
-/
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.TutorialDefs
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Tutorial

/-- Type-check errors returned from the Rust kernel FFI.
    Only one variant: rejection is reported as a formatted string. Matches
    `KERNEL_EXCEPTION_TAG` in `src/ffi/kernel.rs`. -/
inductive CheckError where
  | kernelException (msg : String)
  deriving Repr

/-- FFI: type-check a batch of constants through the full pipeline
    (Lean env → Ixon compile → kernel ingress → typecheck).

    Implemented in `src/ffi/kernel.rs::rs_kernel_check_consts`, which is
    only built with the `test-ffi` Cargo feature (enabled automatically by
    `lake test` via `ix_rs_test`). -/
@[extern "rs_kernel_check_consts"]
opaque rsCheckConstsFFI :
    @& List (Lean.Name × Lean.ConstantInfo) →
    @& Array String →
    @& Array Bool →
    IO (Array (String × Option CheckError))

def testTutorialConsts : TestSeq :=
  .individualIO "kernel tutorial checks" none (do
    let leanEnv ← get_env!
    let testCases := TutorialMeta.getTestCases leanEnv

    -- Collect all constant names that need checking
    -- (skip renaming test cases — their collision check is done on the Lean side)
    let mut allNames : Array String := #[]
    for tc in testCases do
      if tc.renamings.size == 0 then
        for n in tc.decls do
          allNames := allNames.push (toString n)

    -- Also add stdlib constants we want to verify
    let stdlibConsts := #[
      "Acc", "Acc.intro", "Acc.rec",
      "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound",
      "Prod", "Prod.mk", "Prod.rec",
      "Eq", "Eq.refl", "Eq.rec",
      "List", "List.nil", "List.cons", "List.rec",
      "Exists", "Exists.intro", "Exists.rec"
    ]
    for n in stdlibConsts do
      allNames := allNames.push n

    -- Also add the non-macro theorems/inductives defined directly
    -- (good_def/good_thm/bad_thm are auto-registered; these are plain defs/theorems/inductives)
    let p := "Tests.Ix.Kernel.TutorialDefs."
    let directConsts := #[
      -- TN (custom Nat)
      p ++ "TN", p ++ "TN.zero", p ++ "TN.succ", p ++ "TN.rec",
      p ++ "TN.add", p ++ "tnAddZero", p ++ "tnAddSucc",
      -- TRTree (reflexive)
      p ++ "TRTree", p ++ "TRTree.leaf", p ++ "TRTree.node",
      p ++ "TRTree.rec", p ++ "TRTree.left", p ++ "trtreeRecReduction",
      -- Good inductives
      p ++ "TTwoBool", p ++ "TTwoBool.mk", p ++ "TTwoBool.rec",
      p ++ "TN2", p ++ "TN2.zero", p ++ "TN2.succ", p ++ "TN2.rec",
      -- TColor + TRBTree
      p ++ "TColor", p ++ "TColor.r", p ++ "TColor.b", p ++ "TColor.rec",
      p ++ "TRBTree", p ++ "TRBTree.leaf", p ++ "TRBTree.red",
      p ++ "TRBTree.black", p ++ "TRBTree.rec", p ++ "TRBTree.id",
      -- TBoolProp
      p ++ "TBoolProp", p ++ "TBoolProp.a", p ++ "TBoolProp.b", p ++ "TBoolProp.rec",
      -- TSortElimProp
      p ++ "TSortElimProp", p ++ "TSortElimProp.mk", p ++ "TSortElimProp.rec",
      p ++ "TSortElimProp2", p ++ "TSortElimProp2.mk", p ++ "TSortElimProp2.rec",
      -- Universe level inductives
      p ++ "PredWithTypeField", p ++ "PredWithTypeField.mk", p ++ "PredWithTypeField.rec",
      p ++ "TypeWithTypeField", p ++ "TypeWithTypeField.mk", p ++ "TypeWithTypeField.rec",
      p ++ "TypeWithTypeFieldPoly", p ++ "TypeWithTypeFieldPoly.mk", p ++ "TypeWithTypeFieldPoly.rec",
      -- Recursor reduction defs
      p ++ "TN2.add", p ++ "myListAppended",
      -- Acc recursor type
      p ++ "accRecType",
      -- Eta corner cases: T structure
      p ++ "T", p ++ "T.mk", p ++ "T.rec",
      -- Adversarial: AdvNat (for nat-rec-rules test; AdvNat.rec tested via bad_raw_consts)
      p ++ "AdvNat", p ++ "AdvNat.zero", p ++ "AdvNat.succ",
      -- PropStructure (projection tests)
      p ++ "PropStructure", p ++ "PropStructure.mk", p ++ "PropStructure.rec",
      -- ProjDataIndex (projection tests)
      p ++ "ProjDataIndex", p ++ "ProjDataIndex.mk", p ++ "ProjDataIndex.rec",
      p ++ "projDataIndexRec",
      -- PropPair (struct eta for Prop test)
      p ++ "PropPair", p ++ "PropPair.mk", p ++ "PropPair.rec"
    ]
    for n in directConsts do
      allNames := allNames.push n

    -- Deduplicate
    let constNames := allNames.toList.eraseDups.toArray

    -- Build expected outcomes: false for names in bad test cases (excluding
    -- renaming tests, whose constants are individually valid), true otherwise
    let mut badNames : Std.HashSet String := Std.HashSet.emptyWithCapacity 64
    for tc in testCases do
      if tc.outcome == .bad && tc.renamings.size == 0 then
        for n in tc.decls do
          badNames := badNames.insert (toString n)
    let expectPass := constNames.map (fun n => !badNames.contains n)

    IO.println s!"[kernel-tutorial] {testCases.size} test cases, {constNames.size} constants to check"

    -- Collect raw constants stored by bad_raw_consts (inductInfo/ctorInfo/recInfo
    -- that couldn't go through the Lean kernel)
    let rawConsts := TutorialMeta.getRawConsts leanEnv
    let extraConstList := rawConsts.toList.map (fun ci => (ci.name, ci))
    let allConstList := leanEnv.constants.toList ++ extraConstList

    let results ← rsCheckConstsFFI allConstList constNames expectPass

    -- Build name → result map
    let mut resultMap : Std.HashMap String (Option CheckError) := Std.HashMap.emptyWithCapacity results.size
    for (name, result) in results do
      resultMap := resultMap.insert name result

    -- Check test case outcomes
    let mut passed := 0
    let mut failed := 0
    let mut errors : Array String := #[]

    -- Check good test cases (must pass)
    for tc in testCases do
      if tc.outcome == .good then
        for n in tc.decls do
          let name := toString n
          match resultMap.get? name with
          | some none => passed := passed + 1
          | some (some err) =>
            failed := failed + 1
            errors := errors.push s!"  ✗ GOOD {name}: rejected with {repr err}"
          | none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ GOOD {name}: not found in results"

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
          let name := toString n
          match resultMap.get? name with
          | some (some _) => passed := passed + 1  -- correctly rejected
          | some none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ BAD {name}: should have been rejected but was accepted"
          | none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ BAD {name}: not found in results"

    -- Check direct theorems (must pass)
    for name in directConsts do
      match resultMap.get? name with
      | some none => passed := passed + 1
      | some (some err) =>
        failed := failed + 1
        errors := errors.push s!"  ✗ {name}: {repr err}"
      | none =>
        failed := failed + 1
        errors := errors.push s!"  ✗ {name}: not found"

    -- Check stdlib (must pass)
    for name in stdlibConsts do
      match resultMap.get? name with
      | some none => passed := passed + 1
      | some (some err) =>
        failed := failed + 1
        errors := errors.push s!"  ✗ stdlib {name}: {repr err}"
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
