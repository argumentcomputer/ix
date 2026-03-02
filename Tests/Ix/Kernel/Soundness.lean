/-
  Soundness negative tests: verify that the typechecker rejects unsound
  inductive declarations (positivity, universe constraints, K-flag, recursor rules).

  Each test is an individual named function using shared helpers.
-/
import Ix.Kernel
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec
open Ix.Kernel
open Tests.Ix.Kernel.Helpers

namespace Tests.Ix.Kernel.Soundness

/-! ## Shared Wrap inductive (reused across several positive-nesting tests) -/

/-- Insert Wrap : Sort 1 → Sort 1 and Wrap.mk into the env. -/
private def addWrap (env : Env .anon) : Env .anon :=
  let wrapAddr := mkAddr 110
  let wrapMkAddr := mkAddr 111
  -- Wrap : Sort 1 → Sort 1
  let wrapType : Expr .anon := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) () ()
  let env := addInductive env wrapAddr wrapType #[wrapMkAddr] (numParams := 1)
  -- Wrap.mk : ∀ (α : Sort 1), α → Wrap α
  let wrapMkType : Expr .anon :=
    .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0 ()) (.app (.const wrapAddr #[] ()) (.bvar 1 ())) () ())
      () ()
  addCtor env wrapMkAddr wrapAddr wrapMkType 0 1 1

private def wrapAddr := mkAddr 110

/-! ## Positivity tests -/

/-- Test 1: Positivity violation — Bad | mk : (Bad → Bad) → Bad -/
def positivityViolation : TestSeq :=
  test "rejects (Bad → Bad) → Bad" (
    let badAddr := mkAddr 10
    let badMkAddr := mkAddr 11
    let env := addInductive default badAddr (.sort (.succ .zero)) #[badMkAddr] (isRec := true)
    -- mk : (Bad → Bad) → Bad — Bad in negative position
    let mkType : Expr .anon :=
      .forallE
        (.forallE (.const badAddr #[] ()) (.const badAddr #[] ()) () ())
        (.const badAddr #[] ())
        () ()
    let env := addCtor env badMkAddr badAddr mkType 0 0 1
    (expectError env buildPrimitives badAddr "positivity").1
  )

/-- Test 11: Nested positive via Wrap (should PASS) — Tree | node : Wrap Tree → Tree -/
def nestedWrapPositive : TestSeq :=
  test "accepts Wrap Tree → Tree" (
    let treeAddr := mkAddr 112
    let treeMkAddr := mkAddr 113
    let env := addWrap default
    let env := addInductive env treeAddr (.sort (.succ .zero)) #[treeMkAddr]
      (numNested := 1) (isRec := true)
    -- Tree.node : Wrap Tree → Tree
    let treeMkType : Expr .anon :=
      .forallE (.app (.const wrapAddr #[] ()) (.const treeAddr #[] ()))
        (.const treeAddr #[] ()) () ()
    let env := addCtor env treeMkAddr treeAddr treeMkType 0 0 1
    (expectOk env buildPrimitives treeAddr "nested-wrap").1
  )

/-- Test 12: Double nesting (should PASS) — Forest | grove : Wrap (Wrap Forest) → Forest -/
def doubleNestedPositive : TestSeq :=
  test "accepts Wrap (Wrap Forest) → Forest" (
    let forestAddr := mkAddr 114
    let forestMkAddr := mkAddr 115
    let env := addWrap default
    let env := addInductive env forestAddr (.sort (.succ .zero)) #[forestMkAddr]
      (numNested := 1) (isRec := true)
    let forestMkType : Expr .anon :=
      .forallE
        (.app (.const wrapAddr #[] ()) (.app (.const wrapAddr #[] ()) (.const forestAddr #[] ())))
        (.const forestAddr #[] ()) () ()
    let env := addCtor env forestMkAddr forestAddr forestMkType 0 0 1
    (expectOk env buildPrimitives forestAddr "double-nested").1
  )

/-- Test 13: Multi-field nested (should PASS) — Rose | node : Rose → Wrap Rose → Rose -/
def multiFieldNestedPositive : TestSeq :=
  test "accepts Rose → Wrap Rose → Rose" (
    let roseAddr := mkAddr 116
    let roseMkAddr := mkAddr 117
    let env := addWrap default
    let env := addInductive env roseAddr (.sort (.succ .zero)) #[roseMkAddr]
      (numNested := 1) (isRec := true)
    let roseMkType : Expr .anon :=
      .forallE (.const roseAddr #[] ())
        (.forallE (.app (.const wrapAddr #[] ()) (.const roseAddr #[] ()))
          (.const roseAddr #[] ()) () ())
        () ()
    let env := addCtor env roseMkAddr roseAddr roseMkType 0 0 2
    (expectOk env buildPrimitives roseAddr "multi-field-nested").1
  )

/-- Test 14: Nested with multiple params — only one tainted (should PASS)
    Pair α β | mk : α → β → Pair α β; U | star; MyInd | mk : Pair MyInd U → MyInd -/
def multiParamNestedPositive : TestSeq :=
  test "accepts Pair MyInd U → MyInd" (
    let pairAddr := mkAddr 120
    let pairMkAddr := mkAddr 121
    let uAddr := mkAddr 122
    let uMkAddr := mkAddr 123
    let myAddr := mkAddr 124
    let myMkAddr := mkAddr 125
    -- Pair : Sort 1 → Sort 1 → Sort 1
    let pairType : Expr .anon :=
      .forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)) () ()) () ()
    let env := addInductive default pairAddr pairType #[pairMkAddr] (numParams := 2)
    -- Pair.mk : ∀ (α β : Sort 1), α → β → Pair α β
    let pairMkType : Expr .anon :=
      .forallE (.sort (.succ .zero))
        (.forallE (.sort (.succ .zero))
          (.forallE (.bvar 1 ())
            (.forallE (.bvar 1 ())
              (.app (.app (.const pairAddr #[] ()) (.bvar 3 ())) (.bvar 2 ()))
              () ())
            () ())
          () ())
        () ()
    let env := addCtor env pairMkAddr pairAddr pairMkType 0 2 2
    -- U : Sort 1
    let env := addInductive env uAddr (.sort (.succ .zero)) #[uMkAddr]
    let env := addCtor env uMkAddr uAddr (.const uAddr #[] ()) 0 0 0
    -- MyInd : Sort 1
    let env := addInductive env myAddr (.sort (.succ .zero)) #[myMkAddr]
      (numNested := 1) (isRec := true)
    -- MyInd.mk : Pair MyInd U → MyInd
    let myMkType : Expr .anon :=
      .forallE (.app (.app (.const pairAddr #[] ()) (.const myAddr #[] ())) (.const uAddr #[] ()))
        (.const myAddr #[] ()) () ()
    let env := addCtor env myMkAddr myAddr myMkType 0 0 1
    (expectOk env buildPrimitives myAddr "multi-param-nested").1
  )

/-- Test 15: Negative via nested contravariant param (should FAIL)
    Contra α | mk : (α → Prop) → Contra α; Bad | mk : Contra Bad → Bad -/
def nestedContravariantFails : TestSeq :=
  test "rejects Contra Bad → Bad (α negative in Contra)" (
    let contraAddr := mkAddr 130
    let contraMkAddr := mkAddr 131
    let badAddr := mkAddr 132
    let badMkAddr := mkAddr 133
    -- Contra : Sort 1 → Sort 1
    let contraType : Expr .anon := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) () ()
    let env := addInductive default contraAddr contraType #[contraMkAddr] (numParams := 1)
    -- Contra.mk : ∀ (α : Sort 1), (α → Prop) → Contra α
    let contraMkType : Expr .anon :=
      .forallE (.sort (.succ .zero))
        (.forallE
          (.forallE (.bvar 0 ()) (.sort .zero) () ())
          (.app (.const contraAddr #[] ()) (.bvar 1 ()))
          () ())
        () ()
    let env := addCtor env contraMkAddr contraAddr contraMkType 0 1 1
    -- Bad : Sort 1
    let env := addInductive env badAddr (.sort (.succ .zero)) #[badMkAddr] (isRec := true)
    let badMkType : Expr .anon :=
      .forallE (.app (.const contraAddr #[] ()) (.const badAddr #[] ()))
        (.const badAddr #[] ()) () ()
    let env := addCtor env badMkAddr badAddr badMkType 0 0 1
    (expectError env buildPrimitives badAddr "nested-contravariant").1
  )

/-- Test 16: Inductive in index position (should FAIL)
    PIdx : Prop → Prop (numParams=0, numIndices=1); PBad | mk : PIdx PBad → PBad -/
def inductiveInIndexFails : TestSeq :=
  test "rejects PBad in index of PIdx" (
    let pidxAddr := mkAddr 140
    let pidxMkAddr := mkAddr 141
    let pbadAddr := mkAddr 142
    let pbadMkAddr := mkAddr 143
    -- PIdx : Prop → Prop
    let pidxType : Expr .anon := .forallE (.sort .zero) (.sort .zero) () ()
    let env := addInductive default pidxAddr pidxType #[pidxMkAddr] (numIndices := 1)
    -- PIdx.mk : ∀ (p : Prop), PIdx p
    let pidxMkType : Expr .anon :=
      .forallE (.sort .zero) (.app (.const pidxAddr #[] ()) (.bvar 0 ())) () ()
    let env := addCtor env pidxMkAddr pidxAddr pidxMkType 0 0 1
    -- PBad : Prop
    let env := addInductive env pbadAddr (.sort .zero) #[pbadMkAddr] (isRec := true)
    let pbadMkType : Expr .anon :=
      .forallE (.app (.const pidxAddr #[] ()) (.const pbadAddr #[] ()))
        (.const pbadAddr #[] ()) () ()
    let env := addCtor env pbadMkAddr pbadAddr pbadMkType 0 0 1
    (expectError env buildPrimitives pbadAddr "inductive-in-index").1
  )

/-- Test 17: Non-inductive head — axiom wrapping inductive (should FAIL)
    axiom F : Sort 1 → Sort 1; Bad | mk : F Bad → Bad -/
def nonInductiveHeadFails : TestSeq :=
  test "rejects F Bad → Bad (F is axiom)" (
    let fAddr := mkAddr 150
    let badAddr := mkAddr 152
    let badMkAddr := mkAddr 153
    -- F : Sort 1 → Sort 1 (axiom)
    let fType : Expr .anon := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) () ()
    let env := addAxiom default fAddr fType
    -- Bad : Sort 1
    let env := addInductive env badAddr (.sort (.succ .zero)) #[badMkAddr] (isRec := true)
    let badMkType : Expr .anon :=
      .forallE (.app (.const fAddr #[] ()) (.const badAddr #[] ()))
        (.const badAddr #[] ()) () ()
    let env := addCtor env badMkAddr badAddr badMkType 0 0 1
    (expectError env buildPrimitives badAddr "non-inductive-head").1
  )

/-- Test 18: Unsafe outer inductive — not trusted for nesting (should FAIL)
    unsafe UWrap α | mk : (α → α) → UWrap α; Bad | mk : UWrap Bad → Bad -/
def unsafeOuterFails : TestSeq :=
  test "rejects UWrap Bad → Bad (UWrap is unsafe)" (
    let uwAddr := mkAddr 160
    let uwMkAddr := mkAddr 161
    let badAddr := mkAddr 162
    let badMkAddr := mkAddr 163
    -- UWrap : Sort 1 → Sort 1 (unsafe)
    let uwType : Expr .anon := .forallE (.sort (.succ .zero)) (.sort (.succ .zero)) () ()
    let env := addInductive default uwAddr uwType #[uwMkAddr] (numParams := 1) (isUnsafe := true)
    -- UWrap.mk : ∀ (α : Sort 1), (α → α) → UWrap α (unsafe)
    let uwMkType : Expr .anon :=
      .forallE (.sort (.succ .zero))
        (.forallE (.forallE (.bvar 0 ()) (.bvar 1 ()) () ())
          (.app (.const uwAddr #[] ()) (.bvar 1 ()))
          () ())
        () ()
    let env := addCtor env uwMkAddr uwAddr uwMkType 0 1 1 (isUnsafe := true)
    -- Bad : Sort 1
    let env := addInductive env badAddr (.sort (.succ .zero)) #[badMkAddr] (isRec := true)
    let badMkType : Expr .anon :=
      .forallE (.app (.const uwAddr #[] ()) (.const badAddr #[] ()))
        (.const badAddr #[] ()) () ()
    let env := addCtor env badMkAddr badAddr badMkType 0 0 1
    (expectError env buildPrimitives badAddr "unsafe-outer").1
  )

/-! ## Universe constraints -/

/-- Test 2: Universe constraint violation — Sort 2 field in Sort 1 inductive -/
def universeViolation : TestSeq :=
  test "rejects Sort 2 field in Sort 1 inductive" (
    let ubAddr := mkAddr 20
    let ubMkAddr := mkAddr 21
    let env := addInductive default ubAddr (.sort (.succ .zero)) #[ubMkAddr]
    -- mk : Sort 2 → Uni1Bad — Sort 2 : Sort 3, but inductive is Sort 1
    let mkType : Expr .anon :=
      .forallE (.sort (.succ (.succ .zero))) (.const ubAddr #[] ()) () ()
    let env := addCtor env ubMkAddr ubAddr mkType 0 0 1
    (expectError env buildPrimitives ubAddr "universe-constraint").1
  )

/-! ## K-flag tests -/

/-- Test 3: K=true on non-Prop inductive (Sort 1, 2 ctors) -/
def kFlagNotProp : TestSeq :=
  test "rejects K=true on Sort 1 inductive" (
    let indAddr := mkAddr 30
    let mk1Addr := mkAddr 31
    let mk2Addr := mkAddr 32
    let recAddr := mkAddr 33
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mk1Addr, mk2Addr]
    let env := addCtor env mk1Addr indAddr (.const indAddr #[] ()) 0 0 0
    let env := addCtor env mk2Addr indAddr (.const indAddr #[] ()) 1 0 0
    let env := addRec env recAddr 1 (.sort (.param 0 ())) #[indAddr] 0 0 1 2
      #[
        { ctor := mk1Addr, nfields := 0, rhs := .sort .zero },
        { ctor := mk2Addr, nfields := 0, rhs := .sort .zero }
      ] (k := true)
    (expectError env buildPrimitives recAddr "k-flag-not-prop").1
  )

/-- Test 8: K=true on Prop inductive with 2 ctors -/
def kFlagTwoCtors : TestSeq :=
  test "rejects K=true with 2 ctors in Prop" (
    let indAddr := mkAddr 80
    let mk1Addr := mkAddr 81
    let mk2Addr := mkAddr 82
    let recAddr := mkAddr 83
    let env := addInductive default indAddr (.sort .zero) #[mk1Addr, mk2Addr]
    let env := addCtor env mk1Addr indAddr (.const indAddr #[] ()) 0 0 0
    let env := addCtor env mk2Addr indAddr (.const indAddr #[] ()) 1 0 0
    let env := addRec env recAddr 0 (.sort .zero) #[indAddr] 0 0 1 2
      #[
        { ctor := mk1Addr, nfields := 0, rhs := .sort .zero },
        { ctor := mk2Addr, nfields := 0, rhs := .sort .zero }
      ] (k := true)
    (expectError env buildPrimitives recAddr "k-flag-two-ctors").1
  )

/-! ## Recursor tests -/

/-- Test 4: Recursor wrong rule count — 1 rule for 2-ctor inductive -/
def recWrongRuleCount : TestSeq :=
  test "rejects 1 rule for 2-ctor inductive" (
    let indAddr := mkAddr 40
    let mk1Addr := mkAddr 41
    let mk2Addr := mkAddr 42
    let recAddr := mkAddr 43
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mk1Addr, mk2Addr]
    let env := addCtor env mk1Addr indAddr (.const indAddr #[] ()) 0 0 0
    let env := addCtor env mk2Addr indAddr (.const indAddr #[] ()) 1 0 0
    let env := addRec env recAddr 1 (.sort (.param 0 ())) #[indAddr] 0 0 1 2
      #[{ ctor := mk1Addr, nfields := 0, rhs := .sort .zero }]  -- only 1!
    (expectError env buildPrimitives recAddr "rec-wrong-rule-count").1
  )

/-- Test 5: Recursor wrong nfields — ctor has 0 fields but rule claims 5 -/
def recWrongNfields : TestSeq :=
  test "rejects nfields=5 for 0-field ctor" (
    let indAddr := mkAddr 50
    let mkAddr' := mkAddr 51
    let recAddr := mkAddr 52
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mkAddr']
    let env := addCtor env mkAddr' indAddr (.const indAddr #[] ()) 0 0 0
    let env := addRec env recAddr 1 (.sort (.param 0 ())) #[indAddr] 0 0 1 1
      #[{ ctor := mkAddr', nfields := 5, rhs := .sort .zero }]  -- wrong nfields
    (expectError env buildPrimitives recAddr "rec-wrong-nfields").1
  )

/-- Test 6: Recursor wrong num_params — rec claims 5 params, inductive has 0 -/
def recWrongNumParams : TestSeq :=
  test "rejects numParams=5 for 0-param inductive" (
    let indAddr := mkAddr 60
    let mkAddr' := mkAddr 61
    let recAddr := mkAddr 62
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mkAddr']
    let env := addCtor env mkAddr' indAddr (.const indAddr #[] ()) 0 0 0
    let env := addRec env recAddr 1 (.sort (.param 0 ())) #[indAddr]
      (numParams := 5) 0 1 1  -- wrong: inductive has 0
      #[{ ctor := mkAddr', nfields := 0, rhs := .sort .zero }]
    (expectError env buildPrimitives recAddr "rec-wrong-num-params").1
  )

/-- Test 9: Recursor wrong ctor order — rules in wrong order -/
def recWrongCtorOrder : TestSeq :=
  test "rejects wrong ctor order in rules" (
    let indAddr := mkAddr 90
    let mk1Addr := mkAddr 91
    let mk2Addr := mkAddr 92
    let recAddr := mkAddr 93
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mk1Addr, mk2Addr]
    let env := addCtor env mk1Addr indAddr (.const indAddr #[] ()) 0 0 0
    let env := addCtor env mk2Addr indAddr (.const indAddr #[] ()) 1 0 0
    let env := addRec env recAddr 1 (.sort (.param 0 ())) #[indAddr] 0 0 1 2
      #[
        { ctor := mk2Addr, nfields := 0, rhs := .sort .zero },  -- wrong order!
        { ctor := mk1Addr, nfields := 0, rhs := .sort .zero }
      ]
    (expectError env buildPrimitives recAddr "rec-wrong-ctor-order").1
  )

/-! ## Constructor validation -/

/-- Test 7: Constructor param count mismatch — ctor claims 3 params, ind has 0 -/
def ctorParamMismatch : TestSeq :=
  test "rejects ctor with numParams=3 for 0-param inductive" (
    let indAddr := mkAddr 70
    let mkAddr' := mkAddr 71
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mkAddr']
    let env := addCtor env mkAddr' indAddr (.const indAddr #[] ()) 0 3 0  -- wrong: 3 params
    (expectError env buildPrimitives indAddr "ctor-param-mismatch").1
  )

/-! ## Sanity -/

/-- Test 10: Valid single-ctor inductive passes -/
def validSingleCtor : TestSeq :=
  test "accepts valid single-ctor inductive" (
    let indAddr := mkAddr 100
    let mkAddr' := mkAddr 101
    let env := addInductive default indAddr (.sort (.succ .zero)) #[mkAddr']
    let env := addCtor env mkAddr' indAddr (.const indAddr #[] ()) 0 0 0
    (expectOk env buildPrimitives indAddr "valid-inductive").1
  )

/-! ## Suite -/

def suite : List TestSeq := [
  group "Positivity"
    (positivityViolation ++
     nestedWrapPositive ++
     doubleNestedPositive ++
     multiFieldNestedPositive ++
     multiParamNestedPositive ++
     nestedContravariantFails ++
     inductiveInIndexFails ++
     nonInductiveHeadFails ++
     unsafeOuterFails),
  group "Universe constraints"
    universeViolation,
  group "K-flag"
    (kFlagNotProp ++
     kFlagTwoCtors),
  group "Recursors"
    (recWrongRuleCount ++
     recWrongNfields ++
     recWrongNumParams ++
     recWrongCtorOrder),
  group "Constructor validation"
    ctorParamMismatch,
  group "Sanity"
    validSingleCtor,
]

end Tests.Ix.Kernel.Soundness
