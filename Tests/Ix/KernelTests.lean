/-
  Kernel test suite.
  - Unit tests for Kernel types, expression operations, and level operations
  - Convert tests (Ixon.Env → Kernel.Env)
  - Targeted constant-checking tests (individual constants through the full pipeline)
-/
import Ix.Kernel
import Ix.Kernel.DecompileM
import Ix.CompileM
import Ix.Common
import Ix.Meta
import LSpec

open LSpec
open Ix.Kernel

namespace Tests.KernelTests

/-! ## Unit tests: Expression equality -/

def testExprHashEq : TestSeq :=
  let bv0 : Expr .anon := Expr.mkBVar 0
  let bv0' : Expr .anon := Expr.mkBVar 0
  let bv1 : Expr .anon := Expr.mkBVar 1
  test "mkBVar 0 == mkBVar 0" (bv0 == bv0') ++
  test "mkBVar 0 != mkBVar 1" (bv0 != bv1) ++
  -- Sort equality
  let s0 : Expr .anon := Expr.mkSort Level.zero
  let s0' : Expr .anon := Expr.mkSort Level.zero
  let s1 : Expr .anon := Expr.mkSort (Level.succ Level.zero)
  test "mkSort 0 == mkSort 0" (s0 == s0') ++
  test "mkSort 0 != mkSort 1" (s0 != s1) ++
  -- App equality
  let app1 := Expr.mkApp bv0 bv1
  let app1' := Expr.mkApp bv0 bv1
  let app2 := Expr.mkApp bv1 bv0
  test "mkApp bv0 bv1 == mkApp bv0 bv1" (app1 == app1') ++
  test "mkApp bv0 bv1 != mkApp bv1 bv0" (app1 != app2) ++
  -- Lambda equality
  let lam1 := Expr.mkLam s0 bv0
  let lam1' := Expr.mkLam s0 bv0
  let lam2 := Expr.mkLam s1 bv0
  test "mkLam s0 bv0 == mkLam s0 bv0" (lam1 == lam1') ++
  test "mkLam s0 bv0 != mkLam s1 bv0" (lam1 != lam2) ++
  -- Forall equality
  let pi1 := Expr.mkForallE s0 s1
  let pi1' := Expr.mkForallE s0 s1
  test "mkForallE s0 s1 == mkForallE s0 s1" (pi1 == pi1') ++
  -- Const equality
  let addr1 := Address.blake3 (ByteArray.mk #[1])
  let addr2 := Address.blake3 (ByteArray.mk #[2])
  let c1 : Expr .anon := Expr.mkConst addr1 #[]
  let c1' : Expr .anon := Expr.mkConst addr1 #[]
  let c2 : Expr .anon := Expr.mkConst addr2 #[]
  test "mkConst addr1 == mkConst addr1" (c1 == c1') ++
  test "mkConst addr1 != mkConst addr2" (c1 != c2) ++
  -- Const with levels
  let c1l : Expr .anon := Expr.mkConst addr1 #[Level.zero]
  let c1l' : Expr .anon := Expr.mkConst addr1 #[Level.zero]
  let c1l2 : Expr .anon := Expr.mkConst addr1 #[Level.succ Level.zero]
  test "mkConst addr1 [0] == mkConst addr1 [0]" (c1l == c1l') ++
  test "mkConst addr1 [0] != mkConst addr1 [1]" (c1l != c1l2) ++
  -- Literal equality
  let nat0 : Expr .anon := Expr.mkLit (.natVal 0)
  let nat0' : Expr .anon := Expr.mkLit (.natVal 0)
  let nat1 : Expr .anon := Expr.mkLit (.natVal 1)
  let str1 : Expr .anon := Expr.mkLit (.strVal "hello")
  let str1' : Expr .anon := Expr.mkLit (.strVal "hello")
  let str2 : Expr .anon := Expr.mkLit (.strVal "world")
  test "lit nat 0 == lit nat 0" (nat0 == nat0') ++
  test "lit nat 0 != lit nat 1" (nat0 != nat1) ++
  test "lit str hello == lit str hello" (str1 == str1') ++
  test "lit str hello != lit str world" (str1 != str2) ++
  .done

/-! ## Unit tests: Expression operations -/

def testExprOps : TestSeq :=
  -- getAppFn / getAppArgs
  let bv0 : Expr .anon := Expr.mkBVar 0
  let bv1 : Expr .anon := Expr.mkBVar 1
  let bv2 : Expr .anon := Expr.mkBVar 2
  let app := Expr.mkApp (Expr.mkApp bv0 bv1) bv2
  test "getAppFn (app (app bv0 bv1) bv2) == bv0" (app.getAppFn == bv0) ++
  test "getAppNumArgs == 2" (app.getAppNumArgs == 2) ++
  test "getAppArgs[0] == bv1" (app.getAppArgs[0]! == bv1) ++
  test "getAppArgs[1] == bv2" (app.getAppArgs[1]! == bv2) ++
  -- mkAppN round-trips
  let rebuilt := Expr.mkAppN bv0 #[bv1, bv2]
  test "mkAppN round-trips" (rebuilt == app) ++
  -- Predicates
  test "isApp" app.isApp ++
  test "isSort" (Expr.mkSort (Level.zero : Level .anon)).isSort ++
  test "isLambda" (Expr.mkLam bv0 bv1).isLambda ++
  test "isForall" (Expr.mkForallE bv0 bv1).isForall ++
  test "isLit" (Expr.mkLit (.natVal 42) : Expr .anon).isLit ++
  test "isBVar" bv0.isBVar ++
  test "isConst" (Expr.mkConst (m := .anon) default #[]).isConst ++
  -- Accessors
  let s1 : Expr .anon := Expr.mkSort (Level.succ Level.zero)
  test "sortLevel!" (s1.sortLevel! == Level.succ Level.zero) ++
  test "bvarIdx!" (bv1.bvarIdx! == 1) ++
  .done

/-! ## Unit tests: Level operations -/

def testLevelOps : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- reduce
  test "reduce zero" (Level.reduce l0 == l0) ++
  test "reduce (succ zero)" (Level.reduce l1 == l1) ++
  -- equalLevel
  test "zero equiv zero" (Level.equalLevel l0 l0) ++
  test "succ zero equiv succ zero" (Level.equalLevel l1 l1) ++
  test "max a b equiv max b a"
    (Level.equalLevel (Level.max p0 p1) (Level.max p1 p0)) ++
  test "zero not equiv succ zero" (!Level.equalLevel l0 l1) ++
  -- leq
  test "zero <= zero" (Level.leq l0 l0 0) ++
  test "succ zero <= zero + 1" (Level.leq l1 l0 1) ++
  test "not (succ zero <= zero)" (!Level.leq l1 l0 0) ++
  test "param 0 <= param 0" (Level.leq p0 p0 0) ++
  test "succ (param 0) <= param 0 + 1"
    (Level.leq (Level.succ p0) p0 1) ++
  test "not (succ (param 0) <= param 0)"
    (!Level.leq (Level.succ p0) p0 0) ++
  .done

/-! ## Integration tests: Const pipeline -/

/-- Parse a dotted name string like "Nat.add" into an Ix.Name. -/
private def parseIxName (s : String) : Ix.Name :=
  let parts := s.splitOn "."
  parts.foldl (fun acc part => Ix.Name.mkStr acc part) Ix.Name.mkAnon

/-- Convert a Lean.Name to an Ix.Name (reproducing the Blake3 hashing). -/
private partial def leanNameToIx : Lean.Name → Ix.Name
  | .anonymous => Ix.Name.mkAnon
  | .str pre s => Ix.Name.mkStr (leanNameToIx pre) s
  | .num pre n => Ix.Name.mkNat (leanNameToIx pre) n

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

/-- Const pipeline: compile, convert, typecheck specific constants. -/
def testConstPipeline : TestSeq :=
  .individualIO "kernel const pipeline" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    IO.println s!"[kernel] rsCompileEnv: {ixonEnv.consts.size} consts in {compileMs.formatMs}"

    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      IO.println s!"[kernel] convertEnv: {kenv.size} consts in {convertMs.formatMs}"

      -- Check specific constants
      let constNames := #[
        "Nat", "Nat.zero", "Nat.succ", "Nat.rec",
        "Bool", "Bool.true", "Bool.false", "Bool.rec",
        "Eq", "Eq.refl",
        "List", "List.nil", "List.cons",
        "Nat.below"
      ]
      let checkStart ← IO.monoMsNow
      let mut passed := 0
      let mut failures : Array String := #[]
      for name in constNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do failures := failures.push s!"{name}: not found"; continue
        let addr := cNamed.addr
        match Ix.Kernel.typecheckConst kenv prims addr quotInit with
        | .ok () => passed := passed + 1
        | .error e => failures := failures.push s!"{name}: {e}"
      let checkMs := (← IO.monoMsNow) - checkStart
      IO.println s!"[kernel] {passed}/{constNames.size} passed in {checkMs.formatMs}"
      if failures.isEmpty then
        return (true, none)
      else
        for f in failures do IO.println s!"  [fail] {f}"
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

/-! ## Unit tests: Level reduce/imax edge cases -/

def testLevelReduceIMax : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- imax u 0 = 0
  test "imax u 0 = 0" (Level.reduceIMax p0 l0 == l0) ++
  -- imax u (succ v) = max u (succ v)
  test "imax u (succ v) = max u (succ v)"
    (Level.equalLevel (Level.reduceIMax p0 l1) (Level.reduceMax p0 l1)) ++
  -- imax u u = u (same param)
  test "imax u u = u" (Level.reduceIMax p0 p0 == p0) ++
  -- imax u v stays imax (different params)
  test "imax u v stays imax"
    (Level.reduceIMax p0 p1 == Level.imax p0 p1) ++
  -- nested: imax u (imax v 0) — reduce inner first, then outer
  let inner := Level.reduceIMax p1 l0  -- = 0
  test "imax u (imax v 0) = imax u 0 = 0"
    (Level.reduceIMax p0 inner == l0) ++
  .done

def testLevelReduceMax : TestSeq :=
  let l0 : Level .anon := Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- max 0 u = u
  test "max 0 u = u" (Level.reduceMax l0 p0 == p0) ++
  -- max u 0 = u
  test "max u 0 = u" (Level.reduceMax p0 l0 == p0) ++
  -- max (succ u) (succ v) = succ (max u v)
  test "max (succ u) (succ v) = succ (max u v)"
    (Level.reduceMax (Level.succ p0) (Level.succ p1)
      == Level.succ (Level.reduceMax p0 p1)) ++
  -- max p0 p0 = p0
  test "max p0 p0 = p0" (Level.reduceMax p0 p0 == p0) ++
  .done

def testLevelLeqComplex : TestSeq :=
  let l0 : Level .anon := Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- max u v <= max v u (symmetry)
  test "max u v <= max v u"
    (Level.leq (Level.max p0 p1) (Level.max p1 p0) 0) ++
  -- u <= max u v
  test "u <= max u v"
    (Level.leq p0 (Level.max p0 p1) 0) ++
  -- imax u (succ v) <= max u (succ v) — after reduce they're equal
  let lhs := Level.reduce (Level.imax p0 (.succ p1))
  let rhs := Level.reduce (Level.max p0 (.succ p1))
  test "imax u (succ v) <= max u (succ v)"
    (Level.leq lhs rhs 0) ++
  -- imax u 0 <= 0
  test "imax u 0 <= 0"
    (Level.leq (Level.reduce (.imax p0 l0)) l0 0) ++
  -- not (succ (max u v) <= max u v)
  test "not (succ (max u v) <= max u v)"
    (!Level.leq (Level.succ (Level.max p0 p1)) (Level.max p0 p1) 0) ++
  -- imax u u <= u
  test "imax u u <= u"
    (Level.leq (Level.reduce (Level.imax p0 p0)) p0 0) ++
  -- imax 1 (imax 1 u) = u (nested imax decomposition)
  let l1 : Level .anon := Level.succ Level.zero
  let nested := Level.reduce (Level.imax l1 (Level.imax l1 p0))
  test "imax 1 (imax 1 u) <= u"
    (Level.leq nested p0 0) ++
  test "u <= imax 1 (imax 1 u)"
    (Level.leq p0 nested 0) ++
  .done

def testLevelInstBulkReduce : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- Basic: param 0 with [zero] = zero
  test "param 0 with [zero] = zero"
    (Level.instBulkReduce #[l0] p0 == l0) ++
  -- Multi: param 1 with [zero, succ zero] = succ zero
  test "param 1 with [zero, succ zero] = succ zero"
    (Level.instBulkReduce #[l0, l1] p1 == l1) ++
  -- Out-of-bounds: param 2 with 2-element array shifts
  let p2 : Level .anon := Level.param 2 default
  test "param 2 with 2-elem array shifts to param 0"
    (Level.instBulkReduce #[l0, l1] p2 == Level.param 0 default) ++
  -- Compound: imax (param 0) (param 1) with [zero, succ zero]
  let compound := Level.imax p0 p1
  let result := Level.instBulkReduce #[l0, l1] compound
  -- imax 0 (succ 0) = max 0 (succ 0) = succ 0
  test "imax (param 0) (param 1) subst [zero, succ zero]"
    (Level.equalLevel result l1) ++
  .done

def testReducibilityHintsLt : TestSeq :=
  test "regular 1 < regular 2" (ReducibilityHints.lt' (.regular 1) (.regular 2)) ++
  test "not (regular 2 < regular 1)" (!ReducibilityHints.lt' (.regular 2) (.regular 1)) ++
  test "regular _ < opaque" (ReducibilityHints.lt' (.regular 5) .opaque) ++
  test "abbrev < opaque" (ReducibilityHints.lt' .abbrev .opaque) ++
  test "not (opaque < opaque)" (!ReducibilityHints.lt' .opaque .opaque) ++
  test "not (regular 5 < regular 5)" (!ReducibilityHints.lt' (.regular 5) (.regular 5)) ++
  .done

/-! ## Expanded integration tests -/

/-- Expanded constant pipeline: more constants including quotients, recursors, projections. -/
def testMoreConstants : TestSeq :=
  .individualIO "expanded kernel const pipeline" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e => return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let constNames := #[
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
        "Bool.rec", "List.rec",
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
        "WellFounded.fix"
      ]
      let mut passed := 0
      let mut failures : Array String := #[]
      for name in constNames do
        let ixName := parseIxName name
        let some cNamed := ixonEnv.named.get? ixName
          | do failures := failures.push s!"{name}: not found"; continue
        let addr := cNamed.addr
        match Ix.Kernel.typecheckConst kenv prims addr quotInit with
        | .ok () => passed := passed + 1
        | .error e => failures := failures.push s!"{name}: {e}"
      IO.println s!"[kernel-expanded] {passed}/{constNames.size} passed"
      if failures.isEmpty then
        return (true, none)
      else
        for f in failures do IO.println s!"  [fail] {f}"
        return (false, some s!"{failures.size} failure(s)")
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

/-! ## Focused NbE constant tests -/

/-- Test individual constants through the NbE kernel to isolate failures. -/
def testNbeConsts : TestSeq :=
  .individualIO "nbe focused const checks" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e => return (false, some s!"convertEnv: {e}")
    | .ok (kenv, prims, quotInit) =>
      let constNames := #[
        -- Nat basics
        "Nat", "Nat.zero", "Nat.succ", "Nat.rec",
        -- Below / brecOn (well-founded recursion scaffolding)
        "Nat.below", "Nat.brecOn",
        -- PProd (used by Nat.below)
        "PProd", "PProd.mk", "PProd.fst", "PProd.snd",
        "PUnit", "PUnit.unit",
        -- noConfusion (stuck neutral in fresh-state mode)
        "Lean.Meta.Grind.Origin.noConfusionType",
        "Lean.Meta.Grind.Origin.noConfusion",
        "Lean.Meta.Grind.Origin.stx.noConfusion",
        -- The previously-hanging constant
        "Nat.Linear.Poly.of_denote_eq_cancel",
        -- String theorem (fuel-sensitive)
        "String.length_empty",
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
      IO.println s!"[nbe-focus] {passed}/{constNames.size} passed"
      if failures.isEmpty then
        return (true, none)
      else
        return (false, some s!"{failures.size} failure(s)")
  ) .done

def nbeFocusSuite : List TestSeq := [
  testNbeConsts,
]

/-! ## Test suites -/

def unitSuite : List TestSeq := [
  testExprHashEq,
  testExprOps,
  testLevelOps,
  testLevelReduceIMax,
  testLevelReduceMax,
  testLevelLeqComplex,
  testLevelInstBulkReduce,
  testReducibilityHintsLt,
]

def convertSuite : List TestSeq := [
  testConvertEnv,
]

def constSuite : List TestSeq := [
  testConstPipeline,
  testMoreConstants,
]

def negativeSuite : List TestSeq := [
  negativeTests,
]

def anonConvertSuite : List TestSeq := [
  testAnonConvert,
]

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

def roundtripSuite : List TestSeq := [
  testRoundtrip,
]

end Tests.KernelTests
