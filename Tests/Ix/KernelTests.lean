/-
  Kernel test suite.
  - Integration tests (convertEnv, const checks, roundtrip)
  - Negative tests (malformed declarations)
  - Re-exports unit and soundness suites from submodules
-/
import Ix.Kernel
import Ix.Kernel.DecompileM
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Helpers
import Tests.Ix.Kernel.Unit
import Tests.Ix.Kernel.Soundness
import LSpec

open LSpec
open Ix.Kernel
open Tests.Ix.Kernel.Helpers

namespace Tests.KernelTests

/-! ## Integration tests: Const pipeline -/

def testConvertEnv : TestSeq :=
  .individualIO "rsCompileEnv + convertEnv" (do
    let leanEnv ← get_env!
    let leanCount := leanEnv.constants.toList.length
    IO.println s!"[kernel] Lean env: {leanCount} constants"
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    let ixonCount := ixonEnv.consts.size
    let namedCount := ixonEnv.named.size
    IO.println s!"[kernel] rsCompileEnv: {ixonCount} consts, {namedCount} named in {compileMs.formatMs}"
    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, _, _) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      let kenvCount := kenv.size
      IO.println s!"[kernel] convertEnv: {kenvCount} consts in {convertMs.formatMs} ({ixonCount - kenvCount} muts blocks)"
      -- Verify every Lean constant is present in the Kernel.Env
      let mut missing : Array String := #[]
      let mut notCompiled : Array String := #[]
      let mut checked := 0
      for (leanName, _) in leanEnv.constants.toList do
        let ixName := leanNameToIx leanName
        match ixonEnv.named.get? ixName with
        | none => notCompiled := notCompiled.push (toString leanName)
        | some named =>
          checked := checked + 1
          if !kenv.contains named.addr then
            missing := missing.push (toString leanName)
      if !notCompiled.isEmpty then
        IO.println s!"[kernel] {notCompiled.size} Lean constants not in ixonEnv.named (unexpected)"
        for n in notCompiled[:min 10 notCompiled.size] do
          IO.println s!"  not compiled: {n}"
      if missing.isEmpty then
        IO.println s!"[kernel] All {checked} named constants found in Kernel.Env"
        return (true, none)
      else
        IO.println s!"[kernel] {missing.size}/{checked} named constants missing from Kernel.Env"
        for n in missing[:min 20 missing.size] do
          IO.println s!"  missing: {n}"
        return (false, some s!"{missing.size} constants missing from Kernel.Env")
  ) .done

/-- Typecheck specific constants through the Lean kernel. -/
def testConsts : TestSeq :=
  .individualIO "kernel const checks" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    IO.println s!"[kernel-const] rsCompileEnv: {ixonEnv.consts.size} consts in {compileMs.formatMs}"

    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel-const] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      IO.println s!"[kernel-const] convertEnv: {kenv.size} consts in {convertMs.formatMs}"

      let constNames := #[
        -- Basic inductives
        "Nat", "Nat.zero", "Nat.succ", "Nat.rec",
        "Bool", "Bool.true", "Bool.false", "Bool.rec",
        "Eq", "Eq.refl",
        "List", "List.nil", "List.cons",
        "Nat.below",
        -- Quotient types
        "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
        -- K-reduction exercisers
        "Eq.rec", "Eq.subst", "Eq.symm", "Eq.trans",
        -- Proof irrelevance
        "And.intro", "Or.inl", "Or.inr",
        -- K-like reduction with congr
        "congr", "congrArg", "congrFun",
        -- Structure projections + eta
        "Prod.fst", "Prod.snd", "Prod.mk", "Sigma.mk", "Subtype.mk",
        -- Nat primitives
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
        "Nat.gcd", "Nat.beq", "Nat.ble",
        "Nat.land", "Nat.lor", "Nat.xor",
        "Nat.shiftLeft", "Nat.shiftRight", "Nat.pow",
        -- Recursors
        "List.rec",
        -- Delta unfolding
        "id", "Function.comp",
        -- Various inductives
        "Empty", "PUnit", "Fin", "Sigma", "Prod",
        -- Proofs / proof irrelevance
        "True", "False", "And", "Or",
        -- Mutual/nested inductives
        "List.map", "List.foldl", "List.append",
        -- Universe polymorphism
        "ULift", "PLift",
        -- More complex
        "Option", "Option.some", "Option.none",
        "String", "String.mk", "Char",
        -- Partial definitions
        "WellFounded.fix",
        -- Well-founded recursion scaffolding
        "Nat.brecOn",
        -- PProd (used by Nat.below)
        "PProd", "PProd.mk", "PProd.fst", "PProd.snd",
        "PUnit.unit",
        -- noConfusion
        "Lean.Meta.Grind.Origin.noConfusionType",
        "Lean.Meta.Grind.Origin.noConfusion",
        "Lean.Meta.Grind.Origin.stx.noConfusion",
        -- Complex proofs (fuel-sensitive)
        "Nat.Linear.Poly.of_denote_eq_cancel",
        "String.length_empty",
        "_private.Init.Grind.Ring.Basic.«0».Lean.Grind.IsCharP.mk'_aux._proof_1_5",
        -- BVDecide regression test (fuel-sensitive)
        "Std.Tactic.BVDecide.BVExpr.bitblast.blastUdiv.instLawfulVecOperatorShiftConcatInputBlastShiftConcat",
        -- Theorem with sub-term type mismatch (requires inferOnly)
        "Std.Do.Spec.tryCatch_ExceptT",
        -- Nested inductive positivity check (requires whnf)
        "Lean.Elab.Term.Do.Code.action",
        -- UInt64/BitVec isDefEq regression
        "UInt64.decLt",
        -- Recursor-only Ixon block regression (rec.all was empty)
        "Lean.Elab.Tactic.RCases.RCasesPatt.rec_1",
        -- Dependencies of _sunfold (check these first to rule out lazy blowup)
        "Std.Time.FormatPart",
        "Std.Time.FormatConfig",
        "Std.Time.FormatString",
        "Std.Time.FormatType",
        "Std.Time.FormatType.match_1",
        "Std.Time.TypeFormat",
        "Std.Time.Modifier",
        "List.below",
        "List.brecOn",
        "Std.Internal.Parsec.String.Parser",
        "Std.Internal.Parsec.instMonad",
        "Std.Internal.Parsec.instAlternative",
        "Std.Internal.Parsec.String.skipString",
        "Std.Internal.Parsec.eof",
        "Std.Internal.Parsec.fail",
        "Bind.bind",
        "Monad.toBind",
        "SeqRight.seqRight",
        "Applicative.toSeqRight",
        "Applicative.toPure",
        "Alternative.toApplicative",
        "Pure.pure",
        "_private.Std.Time.Format.Basic.«0».Std.Time.parseWith",
        "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go.match_3",
        "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go.match_1",
        "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go",
        -- Deeply nested let chain (stack overflow regression)
        "_private.Std.Time.Format.Basic.«0».Std.Time.GenericFormat.builderParser.go._sunfold"
      ]
      let mut passed := 0
      let mut failures : Array String := #[]
      for name in constNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do failures := failures.push s!"{name}: not found"; continue
        let addr := cNamed.addr
        IO.println s!"  checking {name} ..."
        (← IO.getStdout).flush
        -- if name.containsSubstr "builderParser" then
        --   if let some ci := kenv.find? addr then
        --     let safety := match ci with | .defnInfo v => s!"{repr v.safety}" | _ => "n/a"
        --     IO.println s!"  [{name}] kind={ci.kindName} safety={safety}"
        --     IO.println s!"  type: {ci.type.pp}"
        --     if let some val := ci.value? then
        --       IO.println s!"  value ({val.nodeCount} nodes): {val.pp}"
        --     (← IO.getStdout).flush
        let start ← IO.monoMsNow
        match Ix.Kernel.typecheckConst kenv prims addr quotInit with
        | .ok () =>
          let ms := (← IO.monoMsNow) - start
          IO.println s!"  ✓ {name} ({ms.formatMs})"
          passed := passed + 1
        | .error e =>
          let ms := (← IO.monoMsNow) - start
          IO.println s!"  ✗ {name} ({ms.formatMs}): {e}"
          failures := failures.push s!"{name}: {e}"
      IO.println s!"[kernel-const] {passed}/{constNames.size} passed"
      if failures.isEmpty then
        return (true, none)
      else
        return (false, some s!"{failures.size} failure(s)")
  ) .done

/-! ## Primitive address verification -/

/-- Look up a primitive address by name (for verification only). -/
private def lookupPrim (ixonEnv : Ixon.Env) (name : String) : Address :=
  let ixName := parseIxName name
  match ixonEnv.named.get? ixName with
  | some n => n.addr
  | none => default

/-- Verify hardcoded primitive addresses match actual compiled addresses. -/
def testVerifyPrimAddrs : TestSeq :=
  .individualIO "verify primitive addresses" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let hardcoded := Ix.Kernel.buildPrimitives
    let mut failures : Array String := #[]
    let checks : Array (String × String × Address) := #[
      ("nat", "Nat", hardcoded.nat),
      ("natZero", "Nat.zero", hardcoded.natZero),
      ("natSucc", "Nat.succ", hardcoded.natSucc),
      ("natAdd", "Nat.add", hardcoded.natAdd),
      ("natSub", "Nat.sub", hardcoded.natSub),
      ("natMul", "Nat.mul", hardcoded.natMul),
      ("natPow", "Nat.pow", hardcoded.natPow),
      ("natGcd", "Nat.gcd", hardcoded.natGcd),
      ("natMod", "Nat.mod", hardcoded.natMod),
      ("natDiv", "Nat.div", hardcoded.natDiv),
      ("natBeq", "Nat.beq", hardcoded.natBeq),
      ("natBle", "Nat.ble", hardcoded.natBle),
      ("natLand", "Nat.land", hardcoded.natLand),
      ("natLor", "Nat.lor", hardcoded.natLor),
      ("natXor", "Nat.xor", hardcoded.natXor),
      ("natShiftLeft", "Nat.shiftLeft", hardcoded.natShiftLeft),
      ("natShiftRight", "Nat.shiftRight", hardcoded.natShiftRight),
      ("bool", "Bool", hardcoded.bool),
      ("boolTrue", "Bool.true", hardcoded.boolTrue),
      ("boolFalse", "Bool.false", hardcoded.boolFalse),
      ("string", "String", hardcoded.string),
      ("stringMk", "String.mk", hardcoded.stringMk),
      ("char", "Char", hardcoded.char),
      ("charMk", "Char.ofNat", hardcoded.charMk),
      ("list", "List", hardcoded.list),
      ("listNil", "List.nil", hardcoded.listNil),
      ("listCons", "List.cons", hardcoded.listCons)
    ]
    for (field, name, expected) in checks do
      let actual := lookupPrim ixonEnv name
      if actual != expected then
        failures := failures.push s!"{field}: expected {expected}, got {actual}"
        IO.println s!"  [MISMATCH] {field} ({name}): {actual} != {expected}"
    if failures.isEmpty then
      IO.println s!"[prims] All {checks.size} primitive addresses verified"
      return (true, none)
    else
      return (false, some s!"{failures.size} primitive address mismatch(es). Run `lake test -- kernel-dump-prims` to update.")
  ) .done

/-- Dump all primitive addresses for hardcoding. Use this to update buildPrimitives. -/
def testDumpPrimAddrs : TestSeq :=
  .individualIO "dump primitive addresses" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let names := #[
      ("nat", "Nat"), ("natZero", "Nat.zero"), ("natSucc", "Nat.succ"),
      ("natAdd", "Nat.add"), ("natSub", "Nat.sub"), ("natMul", "Nat.mul"),
      ("natPow", "Nat.pow"), ("natGcd", "Nat.gcd"), ("natMod", "Nat.mod"),
      ("natDiv", "Nat.div"), ("natBeq", "Nat.beq"), ("natBle", "Nat.ble"),
      ("natLand", "Nat.land"), ("natLor", "Nat.lor"), ("natXor", "Nat.xor"),
      ("natShiftLeft", "Nat.shiftLeft"), ("natShiftRight", "Nat.shiftRight"),
      ("bool", "Bool"), ("boolTrue", "Bool.true"), ("boolFalse", "Bool.false"),
      ("string", "String"), ("stringMk", "String.mk"),
      ("char", "Char"), ("charMk", "Char.ofNat"),
      ("list", "List"), ("listNil", "List.nil"), ("listCons", "List.cons")
    ]
    for (field, name) in names do
      IO.println s!"{field} := \"{lookupPrim ixonEnv name}\""
    return (true, none)
  ) .done

/-! ## Anon mode conversion test -/

/-- Test that convertEnv in .anon mode produces the same number of constants. -/
def testAnonConvert : TestSeq :=
  .individualIO "anon mode conversion" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let metaResult := Ix.Kernel.Convert.convertEnv .meta ixonEnv
    let anonResult := Ix.Kernel.Convert.convertEnv .anon ixonEnv
    match metaResult, anonResult with
    | .ok (metaEnv, _, _), .ok (anonEnv, _, _) =>
      let metaCount := metaEnv.size
      let anonCount := anonEnv.size
      IO.println s!"[kernel-anon] meta: {metaCount}, anon: {anonCount}"
      if metaCount == anonCount then
        return (true, none)
      else
        return (false, some s!"meta ({metaCount}) != anon ({anonCount})")
    | .error e, _ => return (false, some s!"meta conversion failed: {e}")
    | _, .error e => return (false, some s!"anon conversion failed: {e}")
  ) .done

/-! ## Negative tests -/

/-- Negative test suite: verify that the typechecker rejects malformed declarations. -/
def negativeTests : TestSeq :=
  .individualIO "kernel negative tests" (do
    let testAddr := Address.blake3 (ByteArray.mk #[1, 0, 42])
    let badAddr := Address.blake3 (ByteArray.mk #[99, 0, 42])
    let prims := buildPrimitives
    let mut passed := 0
    let mut failures : Array String := #[]

    -- Test 1: Theorem not in Prop (type = Sort 1, which is Type 0 not Prop)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ .zero), name := (), levelParams := () }
      let ci : ConstantInfo .anon := .thmInfo { toConstantVal := cv, value := .sort .zero, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "theorem-not-prop: expected error"

    -- Test 2: Type mismatch (definition type = Sort 0, value = Sort 1)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .sort .zero, name := (), levelParams := () }
      let ci : ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort (.succ .zero), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "type-mismatch: expected error"

    -- Test 3: Unknown constant reference (type references non-existent address)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .const badAddr #[] (), name := (), levelParams := () }
      let ci : ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort .zero, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "unknown-const: expected error"

    -- Test 4: Variable out of range (type = bvar 0 in empty context)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .bvar 0 (), name := (), levelParams := () }
      let ci : ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort .zero, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "var-out-of-range: expected error"

    -- Test 5: Application of non-function (Sort 0 is not a function)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ .zero)), name := (), levelParams := () }
      let ci : ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := .app (.sort .zero) (.sort .zero), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "app-non-function: expected error"

    -- Test 6: Let value type doesn't match annotation (Sort 1 : Sort 2, not Sort 0)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ (.succ .zero))), name := (), levelParams := () }
      let letVal : Expr .anon := .letE (.sort .zero) (.sort (.succ .zero)) (.bvar 0 ()) ()
      let ci : ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := letVal, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "let-type-mismatch: expected error"

    -- Test 7: Lambda applied to wrong type (domain expects Prop, given Type 0)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ .zero)), name := (), levelParams := () }
      let lam : Expr .anon := .lam (.sort .zero) (.bvar 0 ()) () ()
      let ci : ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := .app lam (.sort (.succ .zero)), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "app-wrong-type: expected error"

    -- Test 8: Axiom with non-sort type (type = App (Sort 0) (Sort 0), not a sort)
    do
      let cv : ConstantVal .anon :=
        { numLevels := 0, type := .app (.sort .zero) (.sort .zero), name := (), levelParams := () }
      let ci : ConstantInfo .anon := .axiomInfo { toConstantVal := cv, isUnsafe := false }
      let env := (default : Env .anon).insert testAddr ci
      match typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "axiom-non-sort-type: expected error"

    IO.println s!"[kernel-negative] {passed}/8 passed"
    if failures.isEmpty then
      return (true, none)
    else
      for f in failures do IO.println s!"  [fail] {f}"
      return (false, some s!"{failures.size} failure(s)")
  ) .done

/-! ## Roundtrip test: Lean → Ixon → Kernel → Lean -/

/-- Roundtrip test: compile Lean env to Ixon, convert to Kernel, decompile back to Lean,
    and structurally compare against the original. -/
def testRoundtrip : TestSeq :=
  .individualIO "kernel roundtrip Lean→Ixon→Kernel→Lean" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[roundtrip] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, _, _) =>
      -- Build Lean.Name → EnvId map from ixonEnv.named (name-aware lookup)
      let mut nameToEnvId : Std.HashMap Lean.Name (Ix.Kernel.EnvId .meta) := {}
      for (ixName, named) in ixonEnv.named do
        nameToEnvId := nameToEnvId.insert (Ix.Kernel.Decompile.ixNameToLean ixName) ⟨named.addr, ixName⟩
      -- Build work items (filter to constants we can check)
      let mut workItems : Array (Lean.Name × Lean.ConstantInfo × Ix.Kernel.ConstantInfo .meta) := #[]
      let mut notFound := 0
      for (leanName, origCI) in leanEnv.constants.toList do
        let some envId := nameToEnvId.get? leanName
          | do notFound := notFound + 1; continue
        let some kernelCI := kenv.findByEnvId envId
          | continue
        workItems := workItems.push (leanName, origCI, kernelCI)
      -- Chunked parallel comparison
      let numWorkers := 32
      let total := workItems.size
      let chunkSize := (total + numWorkers - 1) / numWorkers
      let mut tasks : Array (Task (Array (Lean.Name × Array (String × String × String)))) := #[]
      let mut offset := 0
      while offset < total do
        let endIdx := min (offset + chunkSize) total
        let chunk := workItems[offset:endIdx]
        let task := Task.spawn (prio := .dedicated) fun () => Id.run do
          let mut results : Array (Lean.Name × Array (String × String × String)) := #[]
          for (leanName, origCI, kernelCI) in chunk.toArray do
            let roundtrippedCI := Ix.Kernel.Decompile.decompileConstantInfo kernelCI
            let diffs := Ix.Kernel.Decompile.constInfoStructEq origCI roundtrippedCI
            if !diffs.isEmpty then
              results := results.push (leanName, diffs)
          results
        tasks := tasks.push task
        offset := endIdx
      -- Collect results
      let checked := total
      let mut mismatches := 0
      for task in tasks do
        for (leanName, diffs) in task.get do
          mismatches := mismatches + 1
          let diffMsgs := diffs.toList.map fun (path, lhs, rhs) =>
            s!"    {path}: {lhs} ≠ {rhs}"
          IO.println s!"[roundtrip] MISMATCH {leanName}:"
          for msg in diffMsgs do IO.println msg
      IO.println s!"[roundtrip] checked {checked}, mismatches {mismatches}, not found {notFound}"
      if mismatches == 0 then
        return (true, none)
      else
        return (false, some s!"{mismatches}/{checked} constants have structural mismatches")
  ) .done

/-! ## Test suites -/

def unitSuite : List TestSeq := Tests.Ix.Kernel.Unit.suite

def convertSuite : List TestSeq := [
  testConvertEnv,
]

def constSuite : List TestSeq := [
  testConsts,
]

def negativeSuite : List TestSeq :=
  [negativeTests] ++ Tests.Ix.Kernel.Soundness.suite

def anonConvertSuite : List TestSeq := [
  testAnonConvert,
]

def roundtripSuite : List TestSeq := [
  testRoundtrip,
]

end Tests.KernelTests
