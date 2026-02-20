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

/-- Parse a dotted name string like "Nat.add" into an Ix.Name.
    Handles `«...»` quoted name components (e.g. `Foo.«0».Bar`). -/
private partial def parseIxName (s : String) : Ix.Name :=
  let parts := splitParts s.toList []
  parts.foldl (fun acc part =>
    match part with
    | .inl str => Ix.Name.mkStr acc str
    | .inr nat => Ix.Name.mkNat acc nat
  ) Ix.Name.mkAnon
where
  /-- Split a dotted name into parts: .inl for string components, .inr for numeric (guillemet). -/
  splitParts : List Char → List (String ⊕ Nat) → List (String ⊕ Nat)
    | [], acc => acc
    | '.' :: rest, acc => splitParts rest acc
    | '«' :: rest, acc =>
      let (inside, rest') := collectUntilClose rest ""
      let part := match inside.toNat? with
        | some n => .inr n
        | none => .inl inside
      splitParts rest' (acc ++ [part])
    | cs, acc =>
      let (word, rest) := collectUntilDot cs ""
      splitParts rest (if word.isEmpty then acc else acc ++ [.inl word])
  collectUntilClose : List Char → String → String × List Char
    | [], s => (s, [])
    | '»' :: rest, s => (s, rest)
    | c :: rest, s => collectUntilClose rest (s.push c)
  collectUntilDot : List Char → String → String × List Char
    | [], s => (s, [])
    | '.' :: rest, s => (s, '.' :: rest)
    | '«' :: rest, s => (s, '«' :: rest)
    | c :: rest, s => collectUntilDot rest (s.push c)

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

/-! ## Soundness negative tests (inductive validation) -/

/-- Helper: make unique addresses from a seed byte. -/
private def mkAddr (seed : UInt8) : Address :=
  Address.blake3 (ByteArray.mk #[seed, 0xAA, 0xBB])

/-- Soundness negative test suite: verify that the typechecker rejects unsound
    inductive declarations (positivity, universe constraints, K-flag, recursor rules). -/
def soundnessNegativeTests : TestSeq :=
  .individualIO "kernel soundness negative tests" (do
    let prims := buildPrimitives
    let mut passed := 0
    let mut failures : Array String := #[]

    -- ========================================================================
    -- Test 1: Positivity violation — Bad | mk : (Bad → Bad) → Bad
    -- The inductive appears in negative position (Pi domain).
    -- ========================================================================
    do
      let badAddr := mkAddr 10
      let badMkAddr := mkAddr 11
      let badType : Expr .anon := .sort (.succ .zero) -- Sort 1
      let badCv : ConstantVal .anon :=
        { numLevels := 0, type := badType, name := (), levelParams := () }
      let badInd : ConstantInfo .anon := .inductInfo {
        toConstantVal := badCv, numParams := 0, numIndices := 0,
        all := #[badAddr], ctors := #[badMkAddr], numNested := 0,
        isRec := true, isUnsafe := false, isReflexive := false
      }
      -- mk : (Bad → Bad) → Bad
      -- The domain (Bad → Bad) has Bad in negative position
      let mkType : Expr .anon :=
        .forallE
          (.forallE (.const badAddr #[] ()) (.const badAddr #[] ()) () ())
          (.const badAddr #[] ())
          () ()
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := mkType, name := (), levelParams := () }
      let mkCtor : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := badAddr, cidx := 0,
        numParams := 0, numFields := 1, isUnsafe := false
      }
      let env := ((default : Env .anon).insert badAddr badInd).insert badMkAddr mkCtor
      match typecheckConst env prims badAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "positivity-violation: expected error (Bad → Bad in domain)"

    -- ========================================================================
    -- Test 2: Universe constraint violation — Uni1Bad : Sort 1 | mk : Sort 2 → Uni1Bad
    -- Field lives in Sort 3 (Sort 2 : Sort 3) but inductive is in Sort 1.
    -- (Note: Prop inductives have special exception allowing any field universe,
    --  so we test with a Sort 1 inductive instead.)
    -- ========================================================================
    do
      let ubAddr := mkAddr 20
      let ubMkAddr := mkAddr 21
      let ubType : Expr .anon := .sort (.succ .zero) -- Sort 1
      let ubCv : ConstantVal .anon :=
        { numLevels := 0, type := ubType, name := (), levelParams := () }
      let ubInd : ConstantInfo .anon := .inductInfo {
        toConstantVal := ubCv, numParams := 0, numIndices := 0,
        all := #[ubAddr], ctors := #[ubMkAddr], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      -- mk : Sort 2 → Uni1Bad
      -- Sort 2 : Sort 3, so field sort = 3. Inductive sort = 1. 3 ≤ 1 fails.
      let mkType : Expr .anon :=
        .forallE (.sort (.succ (.succ .zero))) (.const ubAddr #[] ()) () ()
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := mkType, name := (), levelParams := () }
      let mkCtor : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := ubAddr, cidx := 0,
        numParams := 0, numFields := 1, isUnsafe := false
      }
      let env := ((default : Env .anon).insert ubAddr ubInd).insert ubMkAddr mkCtor
      match typecheckConst env prims ubAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "universe-constraint: expected error (Sort 2 field in Sort 1 inductive)"

    -- ========================================================================
    -- Test 3: K-flag invalid — K=true on non-Prop inductive (Sort 1, 2 ctors)
    -- ========================================================================
    do
      let indAddr := mkAddr 30
      let mk1Addr := mkAddr 31
      let mk2Addr := mkAddr 32
      let recAddr := mkAddr 33
      let indType : Expr .anon := .sort (.succ .zero) -- Sort 1 (not Prop)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mk1Addr, mk2Addr], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mk1Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk1CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk1Cv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let mk2Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk2CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk2Cv, induct := indAddr, cidx := 1,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      -- Recursor with k=true on a non-Prop inductive
      let recCv : ConstantVal .anon :=
        { numLevels := 1, type := .sort (.param 0 ()), name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
        rules := #[
          { ctor := mk1Addr, nfields := 0, rhs := .sort .zero },
          { ctor := mk2Addr, nfields := 0, rhs := .sort .zero }
        ],
        k := true, -- INVALID: not Prop
        isUnsafe := false
      }
      let env := ((((default : Env .anon).insert indAddr indCI).insert mk1Addr mk1CI).insert mk2Addr mk2CI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "k-flag-not-prop: expected error"

    -- ========================================================================
    -- Test 4: Recursor wrong rule count — 1 rule for 2-ctor inductive
    -- ========================================================================
    do
      let indAddr := mkAddr 40
      let mk1Addr := mkAddr 41
      let mk2Addr := mkAddr 42
      let recAddr := mkAddr 43
      let indType : Expr .anon := .sort (.succ .zero)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mk1Addr, mk2Addr], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mk1Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk1CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk1Cv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let mk2Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk2CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk2Cv, induct := indAddr, cidx := 1,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      -- Recursor with only 1 rule (should be 2)
      let recCv : ConstantVal .anon :=
        { numLevels := 1, type := .sort (.param 0 ()), name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
        rules := #[{ ctor := mk1Addr, nfields := 0, rhs := .sort .zero }], -- only 1!
        k := false, isUnsafe := false
      }
      let env := ((((default : Env .anon).insert indAddr indCI).insert mk1Addr mk1CI).insert mk2Addr mk2CI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "rec-wrong-rule-count: expected error"

    -- ========================================================================
    -- Test 5: Recursor wrong nfields — ctor has 0 fields but rule claims 5
    -- ========================================================================
    do
      let indAddr := mkAddr 50
      let mkAddr' := mkAddr 51
      let recAddr := mkAddr 52
      let indType : Expr .anon := .sort (.succ .zero)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mkAddr'], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mkCI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let recCv : ConstantVal .anon :=
        { numLevels := 1, type := .sort (.param 0 ()), name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 0, numIndices := 0, numMotives := 1, numMinors := 1,
        rules := #[{ ctor := mkAddr', nfields := 5, rhs := .sort .zero }], -- wrong nfields
        k := false, isUnsafe := false
      }
      let env := (((default : Env .anon).insert indAddr indCI).insert mkAddr' mkCI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "rec-wrong-nfields: expected error"

    -- ========================================================================
    -- Test 6: Recursor wrong num_params — rec claims 5 params, inductive has 0
    -- ========================================================================
    do
      let indAddr := mkAddr 60
      let mkAddr' := mkAddr 61
      let recAddr := mkAddr 62
      let indType : Expr .anon := .sort (.succ .zero)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mkAddr'], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mkCI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let recCv : ConstantVal .anon :=
        { numLevels := 1, type := .sort (.param 0 ()), name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 5, -- wrong: inductive has 0
        numIndices := 0, numMotives := 1, numMinors := 1,
        rules := #[{ ctor := mkAddr', nfields := 0, rhs := .sort .zero }],
        k := false, isUnsafe := false
      }
      let env := (((default : Env .anon).insert indAddr indCI).insert mkAddr' mkCI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "rec-wrong-num-params: expected error"

    -- ========================================================================
    -- Test 7: Constructor param count mismatch — ctor claims 3 params, ind has 0
    -- ========================================================================
    do
      let indAddr := mkAddr 70
      let mkAddr' := mkAddr 71
      let indType : Expr .anon := .sort (.succ .zero)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mkAddr'], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mkCI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := indAddr, cidx := 0,
        numParams := 3, -- wrong: inductive has 0
        numFields := 0, isUnsafe := false
      }
      let env := ((default : Env .anon).insert indAddr indCI).insert mkAddr' mkCI
      match typecheckConst env prims indAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "ctor-param-mismatch: expected error"

    -- ========================================================================
    -- Test 8: K-flag invalid — K=true on Prop inductive with 2 ctors
    -- ========================================================================
    do
      let indAddr := mkAddr 80
      let mk1Addr := mkAddr 81
      let mk2Addr := mkAddr 82
      let recAddr := mkAddr 83
      let indType : Expr .anon := .sort .zero -- Prop
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mk1Addr, mk2Addr], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mk1Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk1CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk1Cv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let mk2Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk2CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk2Cv, induct := indAddr, cidx := 1,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let recCv : ConstantVal .anon :=
        { numLevels := 0, type := .sort .zero, name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
        rules := #[
          { ctor := mk1Addr, nfields := 0, rhs := .sort .zero },
          { ctor := mk2Addr, nfields := 0, rhs := .sort .zero }
        ],
        k := true, -- INVALID: 2 ctors
        isUnsafe := false
      }
      let env := ((((default : Env .anon).insert indAddr indCI).insert mk1Addr mk1CI).insert mk2Addr mk2CI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "k-flag-two-ctors: expected error"

    -- ========================================================================
    -- Test 9: Recursor wrong ctor order — rules in wrong order
    -- ========================================================================
    do
      let indAddr := mkAddr 90
      let mk1Addr := mkAddr 91
      let mk2Addr := mkAddr 92
      let recAddr := mkAddr 93
      let indType : Expr .anon := .sort (.succ .zero)
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mk1Addr, mk2Addr], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mk1Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk1CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk1Cv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let mk2Cv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mk2CI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mk2Cv, induct := indAddr, cidx := 1,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let recCv : ConstantVal .anon :=
        { numLevels := 1, type := .sort (.param 0 ()), name := (), levelParams := () }
      let recCI : ConstantInfo .anon := .recInfo {
        toConstantVal := recCv, all := #[indAddr],
        numParams := 0, numIndices := 0, numMotives := 1, numMinors := 2,
        rules := #[
          { ctor := mk2Addr, nfields := 0, rhs := .sort .zero }, -- wrong order!
          { ctor := mk1Addr, nfields := 0, rhs := .sort .zero }
        ],
        k := false, isUnsafe := false
      }
      let env := ((((default : Env .anon).insert indAddr indCI).insert mk1Addr mk1CI).insert mk2Addr mk2CI).insert recAddr recCI
      match typecheckConst env prims recAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "rec-wrong-ctor-order: expected error"

    -- ========================================================================
    -- Test 10: Valid single-ctor inductive passes (sanity check)
    -- ========================================================================
    do
      let indAddr := mkAddr 100
      let mkAddr' := mkAddr 101
      let indType : Expr .anon := .sort (.succ .zero) -- Sort 1
      let indCv : ConstantVal .anon :=
        { numLevels := 0, type := indType, name := (), levelParams := () }
      let indCI : ConstantInfo .anon := .inductInfo {
        toConstantVal := indCv, numParams := 0, numIndices := 0,
        all := #[indAddr], ctors := #[mkAddr'], numNested := 0,
        isRec := false, isUnsafe := false, isReflexive := false
      }
      let mkCv : ConstantVal .anon :=
        { numLevels := 0, type := .const indAddr #[] (), name := (), levelParams := () }
      let mkCI : ConstantInfo .anon := .ctorInfo {
        toConstantVal := mkCv, induct := indAddr, cidx := 0,
        numParams := 0, numFields := 0, isUnsafe := false
      }
      let env := ((default : Env .anon).insert indAddr indCI).insert mkAddr' mkCI
      match typecheckConst env prims indAddr with
      | .ok () => passed := passed + 1
      | .error e => failures := failures.push s!"valid-inductive: unexpected error: {e}"

    let totalTests := 10
    IO.println s!"[kernel-soundness] {passed}/{totalTests} passed"
    if failures.isEmpty then
      return (true, none)
    else
      for f in failures do IO.println s!"  [fail] {f}"
      return (false, some s!"{failures.size} failure(s)")
  ) .done

/-! ## Unit tests: helper functions -/

def testHelperFunctions : TestSeq :=
  -- exprMentionsConst
  let addr1 := mkAddr 200
  let addr2 := mkAddr 201
  let c1 : Expr .anon := .const addr1 #[] ()
  let c2 : Expr .anon := .const addr2 #[] ()
  test "exprMentionsConst: direct match"
    (exprMentionsConst c1 addr1) ++
  test "exprMentionsConst: no match"
    (!exprMentionsConst c2 addr1) ++
  test "exprMentionsConst: in app fn"
    (exprMentionsConst (.app c1 c2) addr1) ++
  test "exprMentionsConst: in app arg"
    (exprMentionsConst (.app c2 c1) addr1) ++
  test "exprMentionsConst: in forallE domain"
    (exprMentionsConst (.forallE c1 c2 () () : Expr .anon) addr1) ++
  test "exprMentionsConst: in forallE body"
    (exprMentionsConst (.forallE c2 c1 () () : Expr .anon) addr1) ++
  test "exprMentionsConst: in lam"
    (exprMentionsConst (.lam c1 c2 () () : Expr .anon) addr1) ++
  test "exprMentionsConst: absent in sort"
    (!exprMentionsConst (.sort .zero : Expr .anon) addr1) ++
  test "exprMentionsConst: absent in bvar"
    (!exprMentionsConst (.bvar 0 () : Expr .anon) addr1) ++
  -- checkStrictPositivity
  let indAddrs := #[addr1]
  test "checkStrictPositivity: no mention is positive"
    (checkStrictPositivity c2 indAddrs) ++
  test "checkStrictPositivity: head occurrence is positive"
    (checkStrictPositivity c1 indAddrs) ++
  test "checkStrictPositivity: in Pi domain is negative"
    (!checkStrictPositivity (.forallE c1 c2 () () : Expr .anon) indAddrs) ++
  test "checkStrictPositivity: in Pi codomain positive"
    (checkStrictPositivity (.forallE c2 c1 () () : Expr .anon) indAddrs) ++
  -- getIndResultLevel
  test "getIndResultLevel: sort zero"
    (getIndResultLevel (.sort .zero : Expr .anon) == some .zero) ++
  test "getIndResultLevel: sort (succ zero)"
    (getIndResultLevel (.sort (.succ .zero) : Expr .anon) == some (.succ .zero)) ++
  test "getIndResultLevel: forallE _ (sort zero)"
    (getIndResultLevel (.forallE (.sort .zero) (.sort (.succ .zero)) () () : Expr .anon) == some (.succ .zero)) ++
  test "getIndResultLevel: bvar (no sort)"
    (getIndResultLevel (.bvar 0 () : Expr .anon) == none) ++
  -- levelIsNonZero
  test "levelIsNonZero: zero is false"
    (!levelIsNonZero (.zero : Level .anon)) ++
  test "levelIsNonZero: succ zero is true"
    (levelIsNonZero (.succ .zero : Level .anon)) ++
  test "levelIsNonZero: param is false"
    (!levelIsNonZero (.param 0 () : Level .anon)) ++
  test "levelIsNonZero: max(succ 0, param) is true"
    (levelIsNonZero (.max (.succ .zero) (.param 0 ()) : Level .anon)) ++
  test "levelIsNonZero: imax(param, succ 0) is true"
    (levelIsNonZero (.imax (.param 0 ()) (.succ .zero) : Level .anon)) ++
  test "levelIsNonZero: imax(succ, param) depends on second"
    (!levelIsNonZero (.imax (.succ .zero) (.param 0 ()) : Level .anon)) ++
  -- checkCtorPositivity
  test "checkCtorPositivity: no inductive mention is ok"
    (checkCtorPositivity c2 0 indAddrs == none) ++
  test "checkCtorPositivity: negative occurrence"
    (checkCtorPositivity (.forallE (.forallE c1 c2 () ()) (.const addr1 #[] ()) () () : Expr .anon) 0 indAddrs != none) ++
  -- getCtorReturnType
  test "getCtorReturnType: no binders returns expr"
    (getCtorReturnType c1 0 0 == c1) ++
  test "getCtorReturnType: skips foralls"
    (getCtorReturnType (.forallE c2 c1 () () : Expr .anon) 0 1 == c1) ++
  .done

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
        "_private.Init.Grind.Ring.Basic.«0».Lean.Grind.IsCharP.mk'_aux._proof_1_5",
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
  testHelperFunctions,
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
  soundnessNegativeTests,
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
