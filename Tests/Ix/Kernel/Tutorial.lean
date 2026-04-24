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

    Two variants:
    - `kernelException msg` — rejection during kernel typechecking (tag 0).
    - `compileError msg`    — rejection during `compile_env` (tag 1), emitted
      when `compile_env`'s tolerant scheduler records a block as ungrounded
      (e.g. `inductBadNonSort` failing `compute_is_large_and_k`).

    **Important**: keep at least two constructors so Lean's LCNF trivial
    structure optimization does NOT elide the enum to just `String`. With
    only one ctor + one field, `hasTrivialStructure?` fires and the runtime
    representation becomes identical to `String`, which breaks any FFI that
    allocates a heap ctor. See
    `refs/lean4/src/Lean/Compiler/LCNF/MonoTypes.lean:20-28`.

    Tags are stable across the Rust FFI — see `KERNEL_EXCEPTION_TAG` and
    `COMPILE_ERROR_TAG` in `src/ffi/kernel.rs`. -/
inductive CheckError where
  | kernelException (msg : String)
  | compileError    (msg : String)
  deriving Repr

/-- Compute the transitive closure of constants referenced by `seeds`, and
    return the subset of `env.constants` reachable from them.

    Mirrors `Ix/Cli/ValidateCmd.lean`'s `collectDeps` exactly, but extends the
    lookup with `extraConsts` so seeds that only exist in `bad_raw_consts`
    (e.g. `inductBadNonSort`, which the Lean kernel rejected and therefore
    never entered `env.constants`) still get their transitive dependencies
    pulled in.

    Returns `(needed : Std.HashSet Name, closed : List (Name × ConstantInfo))`
    so callers can both inspect membership and ship the closed subset. -/
private partial def collectDepsWithExtras
    (env : Lean.Environment)
    (extraConsts : Std.HashMap Lean.Name Lean.ConstantInfo)
    (seeds : List Lean.Name)
    : Std.HashSet Lean.Name × List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      -- Prefer env.constants; fall back to extraConsts for bad_raw_consts.
      let ci? := env.constants.find? n <|> extraConsts.get? n
      if let some ci := ci? then
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
            if let some ctorCi :=
                env.constants.find? ctorName <|> extraConsts.get? ctorName then
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
  let closed := env.constants.toList.filter fun (n, _) => needed.contains n
  return (needed, closed)

/-- FFI: type-check a batch of constants through the full pipeline
    (Lean env → Ixon compile → kernel ingress → typecheck).

    Implemented in `src/ffi/kernel.rs::rs_kernel_check_consts`, which is
    only built with the `test-ffi` Cargo feature (enabled automatically by
    `lake test` via `ix_rs_test`).

    The trailing `Bool` toggles ephemeral progress printing on the Rust
    side:
    - `false` (verbose): every constant is logged on its own line with
      elapsed time and `def_eq` depth — ideal for small, targeted batches
      where every result matters.
    - `true` (quiet / ephemeral): the current `[i/N] name ...` label is
      rewritten in place, and only slow constants (>=1s), unexpected
      passes/failures, and ungrounded compile errors are promoted to
      persistent lines. Ideal for full-env runs (`kernel-check-env`)
      where thousands of fast constants would otherwise swamp the log.

    Results come back in input-array order — the caller pairs each
    `results[i]` with its `names[i]`. We pass `Lean.Name` structurally
    (rather than shipping `name.toString` strings) because Lean's
    default `toString` wraps non-identifier components in `«…»`, and
    round-tripping that through a Rust string parser was brittle:
    names like `Lean.Order.«term_⊑_»` failed lookup against the
    kernel's unescaped `Lean.Order.term_⊑_` key. Rust decodes each
    `Lean.Name` structurally via `decode_name_array`, so the kernel
    lookup is an exact structural match. -/
@[extern "rs_kernel_check_consts"]
opaque rsCheckConstsFFI :
    @& List (Lean.Name × Lean.ConstantInfo) →
    @& Array Lean.Name →
    @& Array Bool →
    @& Bool →
    IO (Array (Option CheckError))

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

    -- Build expected outcomes: false for names in bad test cases (excluding
    -- renaming tests, whose constants are individually valid), true otherwise
    let mut badNames : Std.HashSet Lean.Name := Std.HashSet.emptyWithCapacity 64
    for tc in testCases do
      if tc.outcome == .bad && tc.renamings.size == 0 then
        for n in tc.decls do
          badNames := badNames.insert n
    let expectPass := constNames.map (fun n => !badNames.contains n)

    -- Collect raw constants stored by bad_raw_consts (inductInfo/ctorInfo/recInfo
    -- that couldn't go through the Lean kernel).
    let rawConsts := TutorialMeta.getRawConsts leanEnv
    let extraConstList := rawConsts.toList.map (fun ci => (ci.name, ci))

    -- Filter the Lean env down to the transitive closure of the test
    -- constants before shipping to Rust. Without this, `compile_env` processes
    -- ~200k unrelated blocks (full Mathlib if imported), turning a 5s test
    -- into a 45s test. Mirrors `Ix/Cli/ValidateCmd.lean`'s `collectDeps`.
    let rawConstsMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
      rawConsts.foldl (fun m ci => m.insert ci.name ci)
        (Std.HashMap.emptyWithCapacity rawConsts.size)
    let seeds : List Lean.Name :=
      constNames.toList ++ (rawConsts.toList.map (·.name))
    let (_, closedConsts) := collectDepsWithExtras leanEnv rawConstsMap seeds
    let allConstList := closedConsts ++ extraConstList

    IO.println s!"[kernel-tutorial] {testCases.size} test cases, {constNames.size} constants to check ({allConstList.length} consts in closure)"

    -- Tutorial batches are small and targeted — every constant's outcome
    -- is individually meaningful, so keep the verbose per-constant log.
    -- Rust returns results in the same order as `constNames`, so we zip
    -- them back into a `Name → result` map below.
    let results ← rsCheckConstsFFI allConstList constNames expectPass false

    -- Build Name → result map by pairing each input name with its result.
    -- Rust preserves input order, so `results[i]` corresponds to
    -- `constNames[i]`.
    let mut resultMap : Std.HashMap Lean.Name (Option CheckError) :=
      Std.HashMap.emptyWithCapacity results.size
    for i in [:constNames.size] do
      resultMap := resultMap.insert constNames[i]! results[i]!

    -- Check test case outcomes
    let mut passed := 0
    let mut failed := 0
    let mut errors : Array String := #[]

    -- Check good test cases (must pass). When a good constant is rejected,
    -- pull the raw message string out of `CheckError.kernelException` rather
    -- than calling `repr err` — derived `Repr` for long multi-line strings is
    -- extremely slow (seconds per call) and can make the test appear to hang.
    for tc in testCases do
      if tc.outcome == .good then
        for n in tc.decls do
          match resultMap.get? n with
          | some none => passed := passed + 1
          | some (some err) =>
            failed := failed + 1
            let msg := match err with
              | .kernelException m => s!"kernel: {m}"
              | .compileError m    => s!"compile: {m}"
            errors := errors.push s!"  ✗ GOOD {n}: rejected with {msg}"
          | none =>
            failed := failed + 1
            errors := errors.push s!"  ✗ GOOD {n}: not found in results"

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
