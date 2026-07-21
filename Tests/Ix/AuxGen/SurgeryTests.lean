module

public import LSpec
public import Ix.AuxGen.Surgery

/-!
Property tests for `Ix.AuxGen.Surgery` (the pure-Lean port of the
plan-computation half of `crates/compile/src/compile/surgery.rs`).

The `computeCallSitePlans` fixtures are 1:1 ports of the Rust unit tests
(surgery.rs:1497-2205): the same hand-built environments
(`build_test_env` / `build_test_env_with_nested`), the same
`sortedClasses` / `originalAll` / `AuxLayout` inputs, and the same
expected keep-masks and source→canon permutations. Expression assertions
are hash-based `==` (`Ix.Expr`'s `BEq` compares embedded blake3
addresses).

Not registered in `Tests/Main.lean`; suite entry point is
`Tests.AuxGen.Surgery.suite`.
-/

public section

namespace Tests.AuxGen.Surgery

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr ConstantVal ConstantInfo Environment)

/-- Mirrors the Rust test helper `n` (surgery.rs:1503). -/
def nm (s : String) : Name := Name.mkStr .mkAnon s

/-- Mirrors the Rust test helper `nn` (surgery.rs:1507). -/
def nn (parent child : String) : Name := Name.mkStr (nm parent) child

def cval (name : Name) : ConstantVal :=
  { name, levelParams := #[], type := Expr.mkSort Level.mkZero }

/-- Mirrors Rust `build_test_env` (surgery.rs:1616): a minimal environment
    with mutual inductives (`Sort 0` types throughout), constructors, and
    per-inductive recursors. -/
def buildTestEnv (names : Array String) (ctorCounts : Array Nat) :
    Environment := Id.run do
  let all : Array Name := names.map nm
  let mut consts : Std.HashMap Name ConstantInfo := {}
  for (nameStr, i) in names.zipIdx do
    let indName := nm nameStr
    let ctors : Array Name :=
      (Array.range ctorCounts[i]!).map fun j => nn nameStr s!"ctor{j}"
    consts := consts.insert indName (.inductInfo {
      cnst := cval indName
      numParams := 0, numIndices := 0
      all, ctors, numNested := 0
      isRec := false, isUnsafe := false, isReflexive := false })
    for ctorName in ctors do
      consts := consts.insert ctorName (.ctorInfo {
        cnst := cval ctorName
        induct := indName, cidx := 0
        numParams := 0, numFields := 0, isUnsafe := false })
    let recName := nn nameStr "rec"
    consts := consts.insert recName (.recInfo {
      cnst := cval recName
      all
      numParams := 0, numIndices := 0
      numMotives := names.size
      numMinors := ctorCounts.foldl (· + ·) 0
      rules := #[], k := false, isUnsafe := false })
  return { consts }

/-- Mirrors Rust `build_test_env_with_nested` (surgery.rs:1804): overwrite
    each recursor with `auxMotives` / `auxMinors` added on top of the
    user-visible counts (simulating Lean's nested-mutual recursors). -/
def buildTestEnvWithNested (names : Array String) (ctorCounts : Array Nat)
    (auxMotives auxMinors : Nat) : Environment := Id.run do
  let base := buildTestEnv names ctorCounts
  let totalMotives := names.size + auxMotives
  let totalMinors := ctorCounts.foldl (· + ·) 0 + auxMinors
  let mut consts := base.consts
  for nameStr in names do
    let recName := nn nameStr "rec"
    consts := consts.insert recName (.recInfo {
      cnst := cval recName
      all := names.map nm
      numParams := 0, numIndices := 0
      numMotives := totalMotives, numMinors := totalMinors
      rules := #[], k := false, isUnsafe := false })
  return { consts }

/-- Register `<head>.rec_1 … <head>.rec_count` recursors (the Rust tests
    insert these inline; surgery.rs:1971/2032/2099). -/
def withAuxRecs (env : Environment) (head : String) (count : Nat)
    (all : Array Name) (numMotives numMinors : Nat) : Environment :=
  Id.run do
    let mut consts := env.consts
    for j in [1:count + 1] do
      let recName := nn head s!"rec_{j}"
      consts := consts.insert recName (.recInfo {
        cnst := cval recName
        all
        numParams := 0, numIndices := 0
        numMotives, numMinors
        rules := #[], k := false, isUnsafe := false })
    return { consts }

/-- Run `computeCallSitePlans` purely against a hand-built environment. -/
def runPlans (env : Environment) (sortedClasses : Array (Array Name))
    (originalAll : Array Name) (layout : Option Ixon.AuxLayout := none) :
    Option (Std.HashMap Name CallSitePlan) :=
  let cenv := Ix.CompileM.CompileEnv.new env
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] }
  match Ix.CompileM.CompileM.run cenv blockEnv {}
      (computeCallSitePlans sortedClasses originalAll layout) with
  | .ok (plans, _) => some plans
  | .error _ => none

def planFor (plans : Option (Std.HashMap Name CallSitePlan)) (name : Name) :
    Option CallSitePlan :=
  plans.bind (·.get? name)

/-! ## Telescope utilities (surgery.rs:1515) -/

def telescopeTests : TestSeq :=
  test "collectLeanTelescope: peels a 3-arg spine in application order"
    ((let f := Expr.mkConst (nm "f") #[]
      let a1 := Expr.mkBVar 0
      let a2 := Expr.mkBVar 1
      let a3 := Expr.mkBVar 2
      let app := Expr.mkApp (Expr.mkApp (Expr.mkApp f a1) a2) a3
      let (head, args) := collectLeanTelescope app
      head == f && args == #[a1, a2, a3] : Bool))
  ++ test "collectIxonTelescope: peels a 2-arg spine in application order"
    ((let f := Ixon.Expr.ref 7 #[]
      let a1 := Ixon.Expr.var 0
      let a2 := Ixon.Expr.var 1
      let app := Ixon.Expr.app (Ixon.Expr.app f a1) a2
      let (head, args) := collectIxonTelescope app
      head == f && args == #[a1, a2] : Bool))

/-! ## CallSitePlan identity detection (surgery.rs:1533) -/

/-- Rust `test_identity_plan` fixture (surgery.rs:1538). -/
def identityPlan : CallSitePlan :=
  { nParams := 1
    nSourceMotives := 2
    nSourceMinors := 2
    nIndices := 0
    motiveKeep := #[true, true]
    minorKeep := #[true, true]
    sourceToCanonMotive := #[0, 1]
    sourceToCanonMinor := #[0, 1]
    sourceInBlock := #[true, true]
    headRewrite := none }

def identityTests : TestSeq :=
  test "isIdentity: no reorder, no collapse"
    identityPlan.isIdentity
  ++ test "nCanonicalArgs: params + kept motives + kept minors + indices + major"
    ((identityPlan.nCanonicalArgs == 6 : Bool))
  ++ test "isIdentity: head rewrite is never identity"
    -- surgery.rs:1555 — the spine must be rebuilt onto the external
    -- recursor's telescope even when no motive/minor is dropped.
    ((!({ identityPlan with
          nParams := 0
          nSourceMotives := 1, nSourceMinors := 1
          motiveKeep := #[true], minorKeep := #[true]
          sourceToCanonMotive := #[0], sourceToCanonMinor := #[0]
          sourceInBlock := #[true]
          headRewrite := some { targetRec := nn "List" "rec"
                                targetMotivePos := 0 } : CallSitePlan
        }).isIdentity : Bool))
  ++ test "isIdentity: collapsed third motive is not identity"
    -- surgery.rs:1578.
    ((!({ identityPlan with
          nParams := 0
          nSourceMotives := 3, nSourceMinors := 3
          motiveKeep := #[true, true, false]
          minorKeep := #[true, true, false]
          sourceToCanonMotive := #[0, 1, 0]
          sourceToCanonMinor := #[0, 1, 0]
          sourceInBlock := #[true, true, true] : CallSitePlan
        }).isIdentity : Bool))
  ++ test "isIdentity: permuted motives are not identity"
    -- surgery.rs:1595.
    ((!({ identityPlan with
          nParams := 0
          nSourceMotives := 3, nSourceMinors := 3
          motiveKeep := #[true, true, true]
          minorKeep := #[true, true, true]
          sourceToCanonMotive := #[2, 0, 1]
          sourceToCanonMinor := #[2, 0, 1]
          sourceInBlock := #[true, true, true] : CallSitePlan
        }).isIdentity : Bool))

/-! ## BRecOnCallSitePlan -/

def breconPlanTests : TestSeq :=
  test "fromRecPlan copies the motive layout"
    ((let p := BRecOnCallSitePlan.fromRecPlan
        { identityPlan with sourceToCanonMotive := #[1, 0] }
      p.nParams == 1 && p.nSourceMotives == 2 && p.nIndices == 0
        && p.motiveKeep == #[true, true]
        && p.sourceToCanonMotive == #[1, 0]
        && !p.isIdentity && p.nCanonicalMotives == 2 : Bool))
  ++ test "BRecOnCallSitePlan.isIdentity on an identity motive layout"
    ((BRecOnCallSitePlan.fromRecPlan identityPlan).isIdentity : Bool)

/-! ## Name mappers (surgery.rs:177/189) -/

def nameMapperTests : TestSeq :=
  test "recNameToBreconName: X.rec → X.brecOn"
    ((recNameToBreconName (nn "List" "rec") == some (nn "List" "brecOn") : Bool))
  ++ test "recNameToBreconName: X.rec_2 → X.brecOn_2"
    ((recNameToBreconName (nn "A" "rec_2") == some (nn "A" "brecOn_2") : Bool))
  ++ test "recNameToBreconName: non-rec suffixes map to none"
    ((recNameToBreconName (nn "A" "recOn") == none
      && recNameToBreconName (nn "A" "below") == none
      && recNameToBreconName (Name.mkNat (nm "A") 3) == none
      && recNameToBreconName Name.mkAnon == none : Bool))
  ++ test "recNameToBelowName: X.rec → X.below"
    ((recNameToBelowName (nn "List" "rec") == some (nn "List" "below") : Bool))
  ++ test "recNameToBelowName: X.rec_11 → X.below_11"
    ((recNameToBelowName (nn "A" "rec_11") == some (nn "A" "below_11") : Bool))
  ++ test "recNameToBelowName: non-rec suffixes map to none"
    ((recNameToBelowName (nn "A" "cases") == none
      && recNameToBelowName (Name.mkNat (nm "A") 1) == none : Bool))

/-! ## computeCallSitePlans (surgery.rs:1611) -/

/-- surgery.rs:1692 `test_plan_no_collapse_no_reorder`. -/
def noCollapseTests : TestSeq :=
  test "computeCallSitePlans: identity plans are skipped"
    (((runPlans (buildTestEnv #["A", "B"] #[1, 1])
        #[#[nm "A"], #[nm "B"]] #[nm "A", nm "B"]).map (·.isEmpty)
      == some true : Bool))

/-- surgery.rs:1704 `test_plan_reorder_no_collapse` fixture. -/
def reorderPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans (buildTestEnv #["C", "A", "B"] #[1, 1, 1])
    #[#[nm "A"], #[nm "B"], #[nm "C"]] #[nm "C", nm "A", nm "B"]

def reorderTests : TestSeq :=
  test "reorder: all three recursors get plans"
    (((reorderPlans.map fun p =>
        p.contains (nn "C" "rec") && p.contains (nn "A" "rec")
          && p.contains (nn "B" "rec")) == some true : Bool))
  ++ test "reorder: C.rec permutes source motives [C,A,B] → canon [A,B,C]"
    (((planFor reorderPlans (nn "C" "rec")).map (·.sourceToCanonMotive)
      == some #[2, 0, 1] : Bool))
  ++ test "reorder: C.rec keeps all motives (no collapse)"
    (((planFor reorderPlans (nn "C" "rec")).map (·.motiveKeep)
      == some #[true, true, true] : Bool))

/-- surgery.rs:1728 `test_plan_collapse_a_b_equivalent` fixture. -/
def collapsePlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans (buildTestEnv #["A", "B", "C"] #[1, 1, 1])
    #[#[nm "A", nm "B"], #[nm "C"]] #[nm "A", nm "B", nm "C"]

def collapseTests : TestSeq :=
  test "collapse A~B: A.rec keeps its own motive"
    (((planFor collapsePlans (nn "A" "rec")).map fun p =>
        p.motiveKeep == #[true, false, true]
          && p.sourceToCanonMotive == #[0, 0, 1]
          && p.nCanonicalMotives == 2) == some true : Bool)
  ++ test "collapse A~B: B.rec keeps its own motive"
    (((planFor collapsePlans (nn "B" "rec")).map fun p =>
        p.motiveKeep == #[false, true, true]
          && p.sourceToCanonMotive == #[0, 0, 1]
          && p.nCanonicalMotives == 2) == some true : Bool)
  ++ test "collapse A~B: C.rec keeps the class representative's motive"
    (((planFor collapsePlans (nn "C" "rec")).map fun p =>
        p.motiveKeep == #[true, false, true]
          && p.sourceToCanonMotive == #[0, 0, 1]) == some true : Bool)

/-- surgery.rs:1757 `test_plan_minor_collapse` fixture. -/
def minorCollapsePlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans (buildTestEnv #["A", "B"] #[2, 1])
    #[#[nm "A", nm "B"]] #[nm "A", nm "B"]

def minorCollapseTests : TestSeq :=
  test "minor collapse: A.rec keeps A's minors, drops B's"
    (((planFor minorCollapsePlans (nn "A" "rec")).map fun p =>
        p.minorKeep == #[true, true, false]
          && p.nCanonicalMinors == 2) == some true : Bool)
  ++ test "minor collapse: B.rec drops A's minors, keeps B's"
    (((planFor minorCollapsePlans (nn "B" "rec")).map fun p =>
        p.minorKeep == #[false, false, true]
          && p.nCanonicalMinors == 1) == some true : Bool)

/-! ## Nested-inductive plan computation (surgery.rs:1779) -/

/-- surgery.rs:1838 `test_plan_nested_n_source_motives_reads_recursor`. -/
def nestedIdentityTests : TestSeq :=
  test "nested: identity plan sized from the recursor is skipped"
    (((runPlans (buildTestEnvWithNested #["T"] #[1] 1 2)
        #[#[nm "T"]] #[nm "T"]).map (·.isEmpty)) == some true : Bool)

/-- surgery.rs:1860 `test_plan_nested_with_reorder` fixture. -/
def nestedReorderPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans (buildTestEnvWithNested #["Y", "X"] #[1, 1] 2 2)
    #[#[nm "X"], #[nm "Y"]] #[nm "Y", nm "X"]

def nestedReorderTests : TestSeq :=
  test "nested reorder: counts come from the recursor (user + aux)"
    (((planFor nestedReorderPlans (nn "Y" "rec")).map fun p =>
        p.nSourceMotives == 4 && p.nSourceMinors == 4) == some true : Bool)
  ++ test "nested reorder: user motives permute, aux band identity-maps"
    (((planFor nestedReorderPlans (nn "Y" "rec")).map fun p =>
        p.motiveKeep == #[true, true, true, true]
          && p.sourceToCanonMotive == #[1, 0, 2, 3]
          && p.sourceToCanonMinor == #[1, 0, 2, 3]
          && p.minorKeep == #[true, true, true, true]) == some true : Bool)

/-- surgery.rs:1906 `test_plan_nested_lcnf_shape` fixture. -/
def lcnfPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans
    (buildTestEnvWithNested #["Alt", "FunDecl", "Cases", "Code"]
      #[1, 1, 1, 1] 1 1)
    #[#[nm "Alt"], #[nm "Cases"], #[nm "Code"], #[nm "FunDecl"]]
    #[nm "Alt", nm "FunDecl", nm "Cases", nm "Code"]

def lcnfTests : TestSeq :=
  test "LCNF shape: Alt.rec plan matches the alphabetical permutation"
    (((planFor lcnfPlans (nn "Alt" "rec")).map fun p =>
        p.nSourceMotives == 5 && p.nSourceMinors == 5
          && p.sourceToCanonMotive == #[0, 3, 1, 2, 4]
          && p.motiveKeep == #[true, true, true, true, true]
          && p.sourceToCanonMinor == #[0, 3, 1, 2, 4]
          && p.minorKeep == #[true, true, true, true, true])
      == some true : Bool)

/-- surgery.rs:1951 `test_plan_nested_registers_rec_N_names` fixture. -/
def recNPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans
    (withAuxRecs (buildTestEnvWithNested #["Y", "X"] #[1, 1] 2 2)
      "Y" 2 #[nm "Y", nm "X"] 4 4)
    #[#[nm "X"], #[nm "Y"]] #[nm "Y", nm "X"]

def recNTests : TestSeq :=
  test "rec_N registration: user and aux recursors all get plans"
    (((recNPlans.map fun p =>
        p.contains (nn "Y" "rec") && p.contains (nn "X" "rec")
          && p.contains (nn "Y" "rec_1") && p.contains (nn "Y" "rec_2"))
      == some true : Bool))
  ++ test "rec_N registration: aux plans share the user motive permutation"
    ((((planFor recNPlans (nn "Y" "rec_1")).map (·.sourceToCanonMotive))
      == ((planFor recNPlans (nn "Y" "rec")).map (·.sourceToCanonMotive))
      && (planFor recNPlans (nn "Y" "rec_1")).isSome : Bool))

/-- surgery.rs:2019
    `test_plan_nested_aux_perm_registers_rec_N_without_user_reorder`. -/
def auxPermPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans
    (withAuxRecs (buildTestEnvWithNested #["A", "B"] #[1, 1] 2 2)
      "A" 2 #[nm "A", nm "B"] 4 4)
    #[#[nm "A"], #[nm "B"]] #[nm "A", nm "B"]
    (some { perm := #[1, 0], sourceCtorCounts := #[1, 1] })

def auxPermTests : TestSeq :=
  test "aux perm only: A.rec_1 / A.rec_2 get plans"
    (((auxPermPlans.map fun p =>
        p.contains (nn "A" "rec_1") && p.contains (nn "A" "rec_2"))
      == some true : Bool))
  ++ test "aux perm only: user motives fixed, aux band follows the perm"
    (((planFor auxPermPlans (nn "A" "rec_1")).map fun p =>
        p.sourceToCanonMotive == #[0, 1, 3, 2]
          && p.sourceToCanonMinor == #[0, 1, 3, 2]) == some true : Bool)

/-- surgery.rs:2085 `test_plan_nested_skips_out_of_scc_rec_N` fixture. -/
def outOfSccPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans
    (withAuxRecs (buildTestEnvWithNested #["A", "B", "C"] #[1, 1, 1] 3 6)
      "A" 3 #[nm "A", nm "B", nm "C"] 6 9)
    #[#[nm "A"], #[nm "B"]] #[nm "A", nm "B", nm "C"]
    (some { perm := #[1, 0, UInt64.ofNat PERM_OUT_OF_SCC]
            sourceCtorCounts := #[2, 2, 2] })

def outOfSccTests : TestSeq :=
  test "out-of-SCC: rec_1/rec_2 planned, rec_3 left to its owning block"
    (((outOfSccPlans.map fun p =>
        p.contains (nn "A" "rec_1") && p.contains (nn "A" "rec_2")
          && !p.contains (nn "A" "rec_3")) == some true : Bool))
  ++ test "out-of-SCC: C and List-C source motives/minors are collapsed"
    (((planFor outOfSccPlans (nn "A" "rec_2")).map fun p =>
        p.motiveKeep == #[true, true, false, true, true, false]
          && p.minorKeep
            == #[true, true, false, true, true, true, true, false, false])
      == some true : Bool)
  ++ test "out-of-SCC: kept aux minors map bijectively into canon positions"
    (((planFor outOfSccPlans (nn "A" "rec_2")).map fun p =>
        (p.minorKeep.zip p.sourceToCanonMinor).filterMap
          (fun (keep, canon) => if keep then some canon else none))
      == some #[0, 1, 4, 5, 2, 3] : Bool)

/-- surgery.rs:2168 `test_plan_nested_aux_minors_span_multiple` fixture. -/
def auxMinorSpanPlans : Option (Std.HashMap Name CallSitePlan) :=
  runPlans (buildTestEnvWithNested #["A", "B"] #[1, 1] 1 3)
    #[#[nm "B"], #[nm "A"]] #[nm "A", nm "B"]

def auxMinorSpanTests : TestSeq :=
  test "aux minors span: identity band even when counts differ from motives"
    (((planFor auxMinorSpanPlans (nn "A" "rec")).map fun p =>
        p.nSourceMotives == 3 && p.nSourceMinors == 5
          && p.sourceToCanonMinor.extract 2 p.sourceToCanonMinor.size
            == #[2, 3, 4]
          && (p.minorKeep.extract 2 p.minorKeep.size).all (fun k => k))
      == some true : Bool)

def suite : List TestSeq :=
  [telescopeTests, identityTests, breconPlanTests, nameMapperTests,
   noCollapseTests, reorderTests, collapseTests, minorCollapseTests,
   nestedIdentityTests, nestedReorderTests, lcnfTests, recNTests,
   auxPermTests, outOfSccTests, auxMinorSpanTests]

end Tests.AuxGen.Surgery
