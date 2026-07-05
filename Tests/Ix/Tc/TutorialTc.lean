/-
  Kernel tutorial test cases through the pure-Lean `Ix.Tc` kernel
  (`tc-tutorial`, ignored suite).

  Mirrors `Tests/Ix/Kernel/Tutorial.lean` (the Rust-kernel runner): reads
  the same good/bad test cases registered by `TutorialDefs.lean`, compiles
  each batch through the Rust compiler to Ixon bytes, and checks verdicts
  with `Ix.Tc.checkEnvAnon` instead of `rsCheckConstsFFI`.

  Differences from the Rust runner, by necessity:
  - Renaming test cases are skipped (their collision check is Lean-side
    metadata validation, not kernel work — the Rust runner also resolves
    them without the kernel).
  - Bad test cases compile as separate batches: `rsCheckConstsFFI`
    produces per-constant compile errors inside one batch, while
    `rsCompileEnvBytesFFI` fails wholesale — a wholesale compile failure
    counts as rejection of that case's constants (same verdict, coarser
    error). Good constants live in one shared batch.
  - The `AdvNat.rec` malformed-stored-rule variant is skipped: it works
    by mutating the compiled Ixon inside a dedicated Rust FFI
    (`rsCheckMalformedRecRuleIxonFFI`) and never exposes the mutated
    bytes. The sanitized `AdvNat.rec` in the good batch still runs.
  - Verdicts are per anon ADDRESS: alpha-equivalent constants collapse
    to one verdict (fine — expectations are uniform within a class).
-/
import Ix.Common
import Ix.Meta
import Ix.CompileM
import Ix.Tc
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.TutorialDefs
import LSpec

open LSpec

namespace Tests.Tc.TutorialTc

/-- Same closure walk as `Tutorial.lean`'s `collectDepsWithExtras` (that one
    is `private`). -/
partial def collectDepsWithExtras
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

/-- Compile a batch and check it through Ix.Tc. Returns
    `name ↦ (none = passed | some err)`; `.error` when the whole batch
    failed to compile (callers decide how that maps to expectations). -/
def checkBatchTc (consts : List (Lean.Name × Lean.ConstantInfo))
    (names : List Lean.Name) :
    IO (Except String (Std.HashMap Lean.Name (Option String))) := do
  let bytes ← try
      -- The compile FFI streams to a file; round-trip via a temp path.
      let dir ← IO.FS.createTempDir
      let path := dir / "tc-tutorial-batch.ixe"
      let _ ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString
      let b ← IO.FS.readBinFile path
      IO.FS.removeDirAll dir
      pure (Except.ok b)
    catch e =>
      pure (Except.error s!"compile failed: {e}")
  match bytes with
  | .error e => return .error e
  | .ok bytes =>
    -- Full parse for name → addr; anon parse feeds the kernel.
    let fullEnv ← match Ixon.deEnv bytes with
      | .ok env => pure env
      | .error e => return .error s!"deEnv failed: {e}"
    let verdicts ← match Ix.Tc.checkIxeBytesAnon bytes with
      | .ok results => pure (results.foldl (init :=
          (Std.HashMap.emptyWithCapacity results.size :
            Std.HashMap Address (Option String)))
          fun acc r => acc.insert r.addr r.err?)
      | .error e => return .error s!"Ix.Tc driver failed: {e}"
    let mut out : Std.HashMap Lean.Name (Option String) := {}
    for n in names do
      let ixName := Ix.Name.fromLeanName n
      match fullEnv.named[ixName]? with
      | none => out := out.insert n (some "not in compiled env")
      | some named =>
        match verdicts[named.addr]? with
        | none => out := out.insert n (some "no kernel verdict for address")
        | some err? => out := out.insert n err?
    return .ok out

def testTutorialTc : TestSeq :=
  .individualIO "Ix.Tc kernel tutorial checks" none (do
    let leanEnv ← get_env!
    let testCases := Tests.Ix.Kernel.TutorialMeta.getTestCases leanEnv
    let rawConsts := Tests.Ix.Kernel.TutorialMeta.getRawConsts leanEnv
    let rawConstsMap : Std.HashMap Lean.Name Lean.ConstantInfo :=
      rawConsts.foldl (fun m ci => m.insert ci.name ci)
        (Std.HashMap.emptyWithCapacity rawConsts.size)

    -- Good seeds: good-case decls + the stdlib/direct lists from the Rust
    -- runner.
    let stdlibConsts : Array Lean.Name := #[
      `Acc, `Acc.intro, `Acc.rec,
      `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
      `Prod, `Prod.mk, `Prod.rec,
      `Eq, `Eq.refl, `Eq.rec,
      `List, `List.nil, `List.cons, `List.rec,
      `Exists, `Exists.intro, `Exists.rec
    ]
    let p : Lean.Name := `Tests.Ix.Kernel.TutorialDefs
    let directConsts : Array Lean.Name := #[
      p ++ `TN, p ++ `TN.zero, p ++ `TN.succ, p ++ `TN.rec,
      p ++ `TN.add, p ++ `tnAddZero, p ++ `tnAddSucc,
      p ++ `TRTree, p ++ `TRTree.leaf, p ++ `TRTree.node,
      p ++ `TRTree.rec, p ++ `TRTree.left, p ++ `trtreeRecReduction,
      p ++ `TTwoBool, p ++ `TTwoBool.mk, p ++ `TTwoBool.rec,
      p ++ `TN2, p ++ `TN2.zero, p ++ `TN2.succ, p ++ `TN2.rec,
      p ++ `TColor, p ++ `TColor.r, p ++ `TColor.b, p ++ `TColor.rec,
      p ++ `TRBTree, p ++ `TRBTree.leaf, p ++ `TRBTree.red,
      p ++ `TRBTree.black, p ++ `TRBTree.rec, p ++ `TRBTree.id,
      p ++ `TBoolProp, p ++ `TBoolProp.a, p ++ `TBoolProp.b, p ++ `TBoolProp.rec,
      p ++ `TSortElimProp, p ++ `TSortElimProp.mk, p ++ `TSortElimProp.rec,
      p ++ `TSortElimProp2, p ++ `TSortElimProp2.mk, p ++ `TSortElimProp2.rec,
      p ++ `PredWithTypeField, p ++ `PredWithTypeField.mk, p ++ `PredWithTypeField.rec,
      p ++ `TypeWithTypeField, p ++ `TypeWithTypeField.mk, p ++ `TypeWithTypeField.rec,
      p ++ `TypeWithTypeFieldPoly, p ++ `TypeWithTypeFieldPoly.mk, p ++ `TypeWithTypeFieldPoly.rec,
      p ++ `TN2.add, p ++ `myListAppended,
      p ++ `accRecType,
      p ++ `T, p ++ `T.mk, p ++ `T.rec,
      p ++ `AdvNat, p ++ `AdvNat.zero, p ++ `AdvNat.succ,
      p ++ `PropStructure, p ++ `PropStructure.mk, p ++ `PropStructure.rec,
      p ++ `ProjDataIndex, p ++ `ProjDataIndex.mk, p ++ `ProjDataIndex.rec,
      p ++ `projDataIndexRec,
      p ++ `PropPair, p ++ `PropPair.mk, p ++ `PropPair.rec
    ]
    let mut goodNames : Array Lean.Name := stdlibConsts ++ directConsts
    for tc in testCases do
      if tc.outcome == .good && tc.renamings.size == 0 then
        for n in tc.decls do
          goodNames := goodNames.push n
    let goodList := goodNames.toList.eraseDups

    let mut passed := 0
    let mut failed := 0
    let mut errors : Array String := #[]

    -- Good batch: one shared compile+check. `good_raw_consts` cases (e.g.
    -- nestedSpecLocal*) exist only in the extension, not `env.constants` —
    -- ship them as extras alongside the closure, like the Rust runner's
    -- `closedConsts ++ extraConstList`.
    let (goodNeeded, goodClosure) :=
      collectDepsWithExtras leanEnv rawConstsMap goodList
    let goodExtras := rawConsts.toList.filterMap fun ci =>
      if goodNeeded.contains ci.name && !goodClosure.any (·.1 == ci.name) then
        some (ci.name, ci)
      else none
    match (← checkBatchTc (goodClosure ++ goodExtras) goodList) with
    | .error e =>
      failed := failed + goodList.length
      errors := errors.push s!"  ✗ GOOD batch: {e}"
    | .ok verdicts =>
      for n in goodList do
        match verdicts[n]? with
        | some none => passed := passed + 1
        | some (some err) =>
          failed := failed + 1
          errors := errors.push s!"  ✗ GOOD {n}: rejected with {(err.take 160).toString}"
        | none =>
          failed := failed + 1
          errors := errors.push s!"  ✗ GOOD {n}: no verdict"

    -- Anon-scope skips among the bad cases:
    -- * duplicate-universe-param cases (`tut06_bad01`, `inductLevelParam`)
    --   are meta-only rejections: the check compares level param NAMES,
    --   which anon mode erases (`Mode.F.hasDups` on `Unit` is vacuous —
    --   same in Rust's anon kernel via `CheckDupLevelParams` for `()`).
    --   Their anon forms (`lvls := 2`, positional universes) are
    --   well-formed.
    -- * `AdvNat.rec` is sanitized by compile-side aux regeneration; the
    --   Rust runner also expects it to PASS in the batch (the malformed
    --   variant needs the Rust-internal mutation FFI, skipped here).
    let anonSkips : Std.HashSet Lean.Name := .ofList
      [`tut06_bad01, `inductLevelParam, p ++ `AdvNat.rec]

    -- Bad cases: separate batches (a wholesale compile failure counts as
    -- rejection — same verdict as Rust's per-constant compileError).
    for tc in testCases do
      if tc.outcome == .bad && tc.renamings.size == 0 then
        let seeds := tc.decls.toList.filter (!anonSkips.contains ·)
        if seeds.isEmpty then
          continue
        let (_, closure) := collectDepsWithExtras leanEnv rawConstsMap seeds
        let extras := seeds.filterMap fun n =>
          (rawConstsMap[n]?).map fun ci => (n, ci)
        let batch := closure ++ extras.filter fun (n, _) =>
          !closure.any (·.1 == n)
        match (← checkBatchTc batch seeds) with
        | .error _ =>
          -- Whole batch failed to compile — the bad constants never
          -- reached a checkable env: rejected.
          passed := passed + seeds.length
        | .ok verdicts =>
          for n in seeds do
            match verdicts[n]? with
            | some (some _) => passed := passed + 1
            | some none =>
              failed := failed + 1
              errors := errors.push s!"  ✗ BAD {n}: should have been rejected but was accepted"
            | none =>
              failed := failed + 1
              errors := errors.push s!"  ✗ BAD {n}: no verdict"

    for e in errors do
      IO.println e
    IO.println s!"[tc-tutorial] {passed} passed, {failed} failed"
    if failed == 0 then
      return (true, passed, 0, none)
    else
      return (false, passed, passed + failed, some s!"{failed} checks failed")
  ) .done

def suite : List TestSeq := [testTutorialTc]

end Tests.Tc.TutorialTc
