import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CondenseM
import Ix.GraphM
import Ix.CompileM
import Ix.CanonM
import Ix.Cronos
import Ix.Store
import Ix.Meta
import Ix.Sharing
import Lean
import Tests.Ix.Fixtures
import Tests.Ix.Fixtures.Mutual

open LSpec
open Ix
open Ixon
open Ix.CompileM
open Ix.CanonM (Leon)
open Lean (Environment)

/-- Get a minimal Lean environment for testing (empty) -/
def getTestEnv : IO Environment := do
  Lean.runFrontend "" ⟨"test"⟩

/-- Get a full Lean environment with prelude for testing constants -/
def getFullTestEnv : IO Environment := do
  -- Initialize search path so imports work
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.runFrontend "import Init" ⟨"test_full"⟩


namespace Test.Ix.Inductives

mutual
  unsafe inductive A | a : B → C → A
  unsafe inductive B | b : A → B
  unsafe inductive C | c : A → C
end

end Test.Ix.Inductives

namespace Test.Ix.Mutual

mutual
  unsafe def A : Nat → Nat
  | 0 => 0
  | n + 1 => B n + C n + 1

  unsafe def B : Nat → Nat
  | 0 => 0
  | n + 1 => A n + 1

  unsafe def C : Nat → Nat
  | 0 => 0
  | n + 1 => A n + 1
end

end Test.Ix.Mutual

def time (starts stops: Nat) : Float := Cronos.nanoToSec (stops - starts)

/-!
## Cross-Implementation Compilation Tests

These tests verify that the Lean compiler (CompileM) produces the exact same
output as the Rust compiler by comparing byte-for-byte.
-/

/-- FFI: Compare Lean's compiled Expr with Rust's compilation of the same input.
    Takes the Lean.Expr, the serialized Ixon.Expr from Lean, and the univ context size.
    Returns true if Rust produces the same bytes. -/
@[extern "rs_compare_expr_compilation"]
opaque rsCompareExprCompilation : @& Lean.Expr → @& ByteArray → UInt64 → Bool

/-- FFI: Compare Lean's compiled Constant with Rust's compilation of the same input.
    Takes the Lean.ConstantInfo and the serialized Ixon.Constant from Lean.
    Returns true if Rust produces the same bytes. -/
@[extern "rs_compare_constant_compilation"]
opaque rsCompareConstantCompilation : @& Lean.ConstantInfo → @& ByteArray → Bool

/-!
### Cross-Implementation Expression Compilation Tests

These tests compile expressions with both Lean and Rust, comparing byte-for-byte.
-/

/-- Helper: Compile an expression with Lean and compare with Rust -/
def testExprCrossImpl (name : String) (leanExpr : Lean.Expr) (univCtxSize : Nat := 0) : IO TestSeq := do
  let env ← get_env!
  -- Create empty canon cache for tests
  let canonExprs : Std.HashMap USize Leon.Expr := {}
  let stt := CompileState.new env canonExprs
  -- Create universe context with names u0, u1, u2, ...
  let univCtx := (List.range univCtxSize).map fun i => Lean.Name.mkSimple s!"u{i}"
  let blockEnv : BlockEnv := {
    all := {}
    current := `test
    mutCtx := {}
    univCtx := univCtx
  }
  -- Convert Lean.Expr to Leon.Expr
  let leonExpr := Leon.Expr.ofLean leanExpr
  let result := CompileM.run blockEnv stt {} (compileExpr leonExpr)
  match result with
  | .error e => do
    IO.println s!"  Lean compilation failed for {name}: {repr e}"
    return test name false
  | .ok (ixonExpr, _) =>
    -- Serialize the Lean-compiled expression
    let leanBytes := serExpr ixonExpr
    -- Compare with Rust
    let isMatch := rsCompareExprCompilation leanExpr leanBytes univCtxSize.toUInt64
    if !isMatch then
      IO.println s!"  Cross-impl mismatch for {name}"
      IO.println s!"    Lean output: {repr ixonExpr}"
      IO.println s!"    Lean bytes: {leanBytes.toList.map (·.toNat)}"
    return test name isMatch

/-- Cross-implementation tests for simple expressions (no const refs) -/
def testCrossImplExprs : IO TestSeq := do
  -- Simple expressions that don't require an environment
  let t1 ← testExprCrossImpl "bvar 0" (Lean.Expr.bvar 0)
  let t2 ← testExprCrossImpl "bvar 42" (Lean.Expr.bvar 42)
  let t3 ← testExprCrossImpl "sort zero" (Lean.Expr.sort .zero)
  let t4 ← testExprCrossImpl "sort (succ zero)" (Lean.Expr.sort (.succ .zero))
  let t5 ← testExprCrossImpl "app (bvar 1) (bvar 0)" (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
  let t6 ← testExprCrossImpl "lam" (Lean.Expr.lam `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .default)
  let t7 ← testExprCrossImpl "forall" (Lean.Expr.forallE `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .default)
  let t8 ← testExprCrossImpl "let" (Lean.Expr.letE `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) (Lean.Expr.bvar 0) false)
  let t9 ← testExprCrossImpl "let nonDep" (Lean.Expr.letE `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) (Lean.Expr.bvar 0) true)

  -- Nested expressions
  let t10 ← testExprCrossImpl "nested app" (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
  let t11 ← testExprCrossImpl "nested lam" (Lean.Expr.lam `x (Lean.Expr.sort .zero)
    (Lean.Expr.lam `y (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .default) .default)

  -- Expressions with universe parameters (need univCtx)
  let t12 ← testExprCrossImpl "sort (param u)" (Lean.Expr.sort (.param `u0)) 1
  let t13 ← testExprCrossImpl "sort (max u v)" (Lean.Expr.sort (.max (.param `u0) (.param `u1))) 2
  let t14 ← testExprCrossImpl "sort (imax u v)" (Lean.Expr.sort (.imax (.param `u0) (.param `u1))) 2
  let t15 ← testExprCrossImpl "sort (succ (param u))" (Lean.Expr.sort (.succ (.param `u0))) 1

  -- Lambda with different binder info
  let t16 ← testExprCrossImpl "lam implicit" (Lean.Expr.lam `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .implicit)
  let t17 ← testExprCrossImpl "lam strictImplicit" (Lean.Expr.lam `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .strictImplicit)
  let t18 ← testExprCrossImpl "lam instImplicit" (Lean.Expr.lam `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .instImplicit)

  -- ForallE with different binder info
  let t19 ← testExprCrossImpl "forall implicit" (Lean.Expr.forallE `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .implicit)

  -- Large bvar index
  let t20 ← testExprCrossImpl "bvar 1000" (Lean.Expr.bvar 1000)

  -- Deep nesting - manually build Sort 15
  let deepSort := Lean.Expr.sort (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))))
  let t21 ← testExprCrossImpl "deep sort nesting" deepSort

  -- Complex forall (multiple bindings)
  let complexForall := Lean.Expr.forallE `a (Lean.Expr.sort .zero)
    (Lean.Expr.forallE `b (Lean.Expr.bvar 0)
      (Lean.Expr.forallE `c (Lean.Expr.bvar 1) (Lean.Expr.bvar 0) .default) .default) .default
  let t22 ← testExprCrossImpl "complex forall" complexForall

  return t1 ++ t2 ++ t3 ++ t4 ++ t5 ++ t6 ++ t7 ++ t8 ++ t9 ++ t10 ++ t11 ++ t12 ++ t13 ++ t14 ++ t15 ++ t16 ++ t17 ++ t18 ++ t19 ++ t20 ++ t21 ++ t22

/-!
### Cross-Implementation Constant Compilation Tests

These tests compile constants with both Lean and Rust, comparing byte-for-byte.
-/

/-- Helper to run a constant cross-impl test given the constant info -/
def runConstCrossImplTest (constInfo : Lean.ConstantInfo) (testName : String) : IO TestSeq := do
  let env ← getTestEnv
  -- Create empty canon cache for tests
  let canonExprs : Std.HashMap USize Leon.Expr := {}
  let stt := CompileState.new env canonExprs
  let name := constInfo.name

  -- Set up block environment (singleton)
  let blockEnv : BlockEnv := {
    all := Std.HashSet.ofList [name]
    current := name
    mutCtx := {}
    univCtx := []
  }

  -- Compile with Lean using compileConstantInfo (takes ConstantInfo directly)
  let result := CompileM.run blockEnv stt {} (compileConstantInfo constInfo)
  match result with
  | .error e => do
    IO.println s!"  Lean compilation failed for {testName}: {repr e}"
    pure (test testName false)
  | .ok (blockResult, _) =>
    -- For comparison, use the block directly (these are simple non-inductive constants)
    let leanBytes := serConstant blockResult.block
    -- Compare with Rust
    let isMatch := rsCompareConstantCompilation constInfo leanBytes
    if !isMatch then
      IO.println s!"  Cross-impl mismatch for {testName}"
      IO.println s!"    Lean bytes: {leanBytes.size} bytes"
    pure (test testName isMatch)

/-- Cross-implementation tests for constants using hardcoded ConstantInfo values -/
def testCrossImplConsts : IO TestSeq := do
  -- Test 1: Simple axiom (Prop → Prop) - uses only Sort 0, no external refs
  let axiom1 : Lean.ConstantInfo := .axiomInfo {
    name := `TestAxiom1
    levelParams := []
    type := Lean.Expr.forallE `p (Lean.Expr.sort .zero) (Lean.Expr.sort .zero) .default
    isUnsafe := false
  }
  let t1 ← runConstCrossImplTest axiom1 "axiom Prop→Prop"

  -- Test 2: Axiom with universe parameter (∀ α : Sort u, α → α)
  let axiom2 : Lean.ConstantInfo := .axiomInfo {
    name := `TestAxiom2
    levelParams := [`u]
    type := Lean.Expr.forallE `α
      (Lean.Expr.sort (.param `u))
      (Lean.Expr.forallE `x (Lean.Expr.bvar 0) (Lean.Expr.bvar 1) .default)
      .implicit
    isUnsafe := false
  }
  let t2 ← runConstCrossImplTest axiom2 "axiom ∀α,α→α"

  -- Test 3: Unsafe axiom (Sort 1)
  let axiom3 : Lean.ConstantInfo := .axiomInfo {
    name := `TestAxiomUnsafe
    levelParams := []
    type := Lean.Expr.sort (.succ .zero)  -- Type 0
    isUnsafe := true
  }
  let t3 ← runConstCrossImplTest axiom3 "unsafe axiom"

  -- Test 4: Quotient type
  let quot1 : Lean.ConstantInfo := .quotInfo {
    name := `TestQuot
    levelParams := [`u]
    type := Lean.Expr.sort (.param `u)
    kind := .type
  }
  let t4 ← runConstCrossImplTest quot1 "quot type"

  -- Test 5: Quotient constructor
  let quot2 : Lean.ConstantInfo := .quotInfo {
    name := `TestQuotMk
    levelParams := [`u]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u)) (Lean.Expr.bvar 0) .default
    kind := .ctor
  }
  let t5 ← runConstCrossImplTest quot2 "quot ctor"

  -- Test 6: Quotient lift
  let quot3 : Lean.ConstantInfo := .quotInfo {
    name := `TestQuotLift
    levelParams := [`u, `v]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u))
      (Lean.Expr.forallE `β (Lean.Expr.sort (.param `v)) (Lean.Expr.bvar 1) .default)
      .default
    kind := .lift
  }
  let t6 ← runConstCrossImplTest quot3 "quot lift"

  -- Test 7: Quotient ind
  let quot4 : Lean.ConstantInfo := .quotInfo {
    name := `TestQuotInd
    levelParams := [`u]
    type := Lean.Expr.sort (.param `u)
    kind := .ind
  }
  let t7 ← runConstCrossImplTest quot4 "quot ind"

  -- Test 8: Simple definition (identity on Prop)
  -- def id : Prop → Prop := λ x => x
  let defn1 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefId
    levelParams := []
    type := Lean.Expr.forallE `x (Lean.Expr.sort .zero) (Lean.Expr.sort .zero) .default
    value := Lean.Expr.lam `x (Lean.Expr.sort .zero) (Lean.Expr.bvar 0) .default
    hints := .regular 0
    safety := .safe
    all := [`TestDefId]
  }
  let t8 ← runConstCrossImplTest defn1 "def id Prop→Prop"

  -- Test 9: Definition with universe parameter
  -- def id.{u} : Sort u → Sort u := λ x => x
  let defn2 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefIdPoly
    levelParams := [`u]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u)) (Lean.Expr.sort (.param `u)) .default
    value := Lean.Expr.lam `α (Lean.Expr.sort (.param `u)) (Lean.Expr.bvar 0) .default
    hints := .regular 0
    safety := .safe
    all := [`TestDefIdPoly]
  }
  let t9 ← runConstCrossImplTest defn2 "def id polymorphic"

  -- Test 10: Unsafe definition
  let defn3 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefUnsafe
    levelParams := []
    type := Lean.Expr.sort (.succ .zero)  -- Type
    value := Lean.Expr.sort .zero          -- Prop
    hints := .regular 0
    safety := .unsafe
    all := [`TestDefUnsafe]
  }
  let t10 ← runConstCrossImplTest defn3 "def unsafe"

  -- Test 11: Partial definition
  let defn4 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefPartial
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    hints := .regular 0
    safety := .partial
    all := [`TestDefPartial]
  }
  let t11 ← runConstCrossImplTest defn4 "def partial"

  -- Test 12: Definition with abbrev hint
  let defn5 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefAbbrev
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    hints := .abbrev
    safety := .safe
    all := [`TestDefAbbrev]
  }
  let t12 ← runConstCrossImplTest defn5 "def abbrev hint"

  -- Test 13: Theorem
  -- theorem trivial : Prop := Prop
  let thm1 : Lean.ConstantInfo := .thmInfo {
    name := `TestThm1
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    all := [`TestThm1]
  }
  let t13 ← runConstCrossImplTest thm1 "theorem simple"

  -- Test 14: Theorem with universe parameter
  let thm2 : Lean.ConstantInfo := .thmInfo {
    name := `TestThm2
    levelParams := [`u]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u)) (Lean.Expr.bvar 0) .implicit
    value := Lean.Expr.lam `α (Lean.Expr.sort (.param `u)) (Lean.Expr.bvar 0) .implicit
    all := [`TestThm2]
  }
  let t14 ← runConstCrossImplTest thm2 "theorem polymorphic"

  -- Test 15: Opaque
  let opaq1 : Lean.ConstantInfo := .opaqueInfo {
    name := `TestOpaq1
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    isUnsafe := false
    all := [`TestOpaq1]
  }
  let t15 ← runConstCrossImplTest opaq1 "opaque safe"

  -- Test 16: Unsafe opaque
  let opaq2 : Lean.ConstantInfo := .opaqueInfo {
    name := `TestOpaq2
    levelParams := [`u]
    type := Lean.Expr.sort (.param `u)
    value := Lean.Expr.sort (.param `u)
    isUnsafe := true
    all := [`TestOpaq2]
  }
  let t16 ← runConstCrossImplTest opaq2 "opaque unsafe"

  -- Test 17: Simple recursor (like Unit.rec)
  -- A recursor for a unit-like type with one constructor, no fields
  -- rec.{u} : (motive : Unit → Sort u) → motive unit → (t : Unit) → motive t
  let rec1 : Lean.ConstantInfo := .recInfo {
    name := `TestRec1
    levelParams := [`u]
    type := Lean.Expr.forallE `motive
      (Lean.Expr.forallE `_x (Lean.Expr.sort .zero) (Lean.Expr.sort (.param `u)) .default)
      (Lean.Expr.forallE `_h
        (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.sort .zero))
        (Lean.Expr.forallE `t (Lean.Expr.sort .zero)
          (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0)) .default) .default) .default
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 1
    rules := [
      { ctor := `TestUnit.unit, nfields := 0, rhs := Lean.Expr.bvar 0 }
    ]
    k := true
    isUnsafe := false
    all := [`TestRec1]
  }
  let t17 ← runConstCrossImplTest rec1 "recursor simple"

  -- Test 18: Recursor with fields (like Bool.rec with two constructors)
  -- Simplified: rec with two rules, each with 0 fields
  let rec2 : Lean.ConstantInfo := .recInfo {
    name := `TestRec2
    levelParams := [`u]
    type := Lean.Expr.forallE `motive
      (Lean.Expr.forallE `_x (Lean.Expr.sort .zero) (Lean.Expr.sort (.param `u)) .default)
      (Lean.Expr.forallE `_h1
        (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.sort .zero))
        (Lean.Expr.forallE `_h2
          (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.sort .zero))
          (Lean.Expr.forallE `t (Lean.Expr.sort .zero)
            (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0)) .default) .default) .default) .default
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 2
    rules := [
      { ctor := `TestBool.false, nfields := 0, rhs := Lean.Expr.bvar 1 },
      { ctor := `TestBool.true, nfields := 0, rhs := Lean.Expr.bvar 0 }
    ]
    k := true
    isUnsafe := false
    all := [`TestRec2]
  }
  let t18 ← runConstCrossImplTest rec2 "recursor two ctors"

  -- Test 19: Unsafe recursor
  let rec3 : Lean.ConstantInfo := .recInfo {
    name := `TestRec3
    levelParams := []
    type := Lean.Expr.forallE `motive
      (Lean.Expr.forallE `_x (Lean.Expr.sort .zero) (Lean.Expr.sort .zero) .default)
      (Lean.Expr.forallE `t (Lean.Expr.sort .zero)
        (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) .default) .default
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 0
    rules := []
    k := false
    isUnsafe := true
    all := [`TestRec3]
  }
  let t19 ← runConstCrossImplTest rec3 "recursor unsafe"

  -- Test 20: Recursor with parameters
  -- Like List.rec: rec.{u,v} (α : Type u) (motive : List α → Sort v) ...
  let rec4 : Lean.ConstantInfo := .recInfo {
    name := `TestRec4
    levelParams := [`u, `v]
    type := Lean.Expr.forallE `α
      (Lean.Expr.sort (.succ (.param `u)))
      (Lean.Expr.forallE `motive
        (Lean.Expr.forallE `_x (Lean.Expr.bvar 0) (Lean.Expr.sort (.param `v)) .default)
        (Lean.Expr.forallE `t (Lean.Expr.bvar 1)
          (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0)) .default) .default) .default
    numParams := 1
    numIndices := 0
    numMotives := 1
    numMinors := 0
    rules := []
    k := false
    isUnsafe := false
    all := [`TestRec4]
  }
  let t20 ← runConstCrossImplTest rec4 "recursor with params"

  -- Test 21: Definition with opaque hint
  let defn6 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefOpaque
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    hints := .opaque
    safety := .safe
    all := [`TestDefOpaque]
  }
  let t21 ← runConstCrossImplTest defn6 "def opaque hint"

  -- Test 22: Definition with higher reducibility level
  let defn7 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefReducible
    levelParams := []
    type := Lean.Expr.sort .zero
    value := Lean.Expr.sort .zero
    hints := .regular 10
    safety := .safe
    all := [`TestDefReducible]
  }
  let t22 ← runConstCrossImplTest defn7 "def regular 10"

  -- Test 23: Axiom with multiple universe params
  let axiom4 : Lean.ConstantInfo := .axiomInfo {
    name := `TestAxiom4
    levelParams := [`u, `v, `w]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u))
      (Lean.Expr.forallE `β (Lean.Expr.sort (.param `v))
        (Lean.Expr.forallE `γ (Lean.Expr.sort (.param `w))
          (Lean.Expr.bvar 2) .default) .default) .default
    isUnsafe := false
  }
  let t23 ← runConstCrossImplTest axiom4 "axiom 3 univ params"

  -- Test 24: Complex definition (const combinator)
  -- const.{u,v} : Sort u → Sort v → Sort u
  -- const = λ α β x => x
  let defn8 : Lean.ConstantInfo := .defnInfo {
    name := `TestDefConst
    levelParams := [`u, `v]
    type := Lean.Expr.forallE `α (Lean.Expr.sort (.param `u))
      (Lean.Expr.forallE `β (Lean.Expr.sort (.param `v))
        (Lean.Expr.forallE `x (Lean.Expr.bvar 1)
          (Lean.Expr.bvar 2) .default) .default) .default
    value := Lean.Expr.lam `α (Lean.Expr.sort (.param `u))
      (Lean.Expr.lam `β (Lean.Expr.sort (.param `v))
        (Lean.Expr.lam `x (Lean.Expr.bvar 1)
          (Lean.Expr.bvar 0) .default) .default) .default
    hints := .regular 0
    safety := .safe
    all := [`TestDefConst]
  }
  let t24 ← runConstCrossImplTest defn8 "def const combinator"

  -- Test 25: Recursor with indices
  let rec5 : Lean.ConstantInfo := .recInfo {
    name := `TestRec5
    levelParams := [`u]
    type := Lean.Expr.forallE `n (Lean.Expr.sort .zero)  -- index type
      (Lean.Expr.forallE `motive
        (Lean.Expr.forallE `_n (Lean.Expr.sort .zero)
          (Lean.Expr.forallE `_v (Lean.Expr.sort .zero) (Lean.Expr.sort (.param `u)) .default) .default)
        (Lean.Expr.forallE `v (Lean.Expr.sort .zero)
          (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 2)) (Lean.Expr.bvar 0)) .default) .default) .default
    numParams := 0
    numIndices := 1
    numMotives := 1
    numMinors := 0
    rules := []
    k := false
    isUnsafe := false
    all := [`TestRec5]
  }
  let t25 ← runConstCrossImplTest rec5 "recursor with indices"

  -- Test 26: Recursor with rule having fields
  let rec6 : Lean.ConstantInfo := .recInfo {
    name := `TestRec6
    levelParams := [`u]
    type := Lean.Expr.forallE `motive
      (Lean.Expr.forallE `_x (Lean.Expr.sort .zero) (Lean.Expr.sort (.param `u)) .default)
      (Lean.Expr.forallE `_h
        (Lean.Expr.forallE `field (Lean.Expr.sort .zero)
          (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.sort .zero)) .default)
        (Lean.Expr.forallE `t (Lean.Expr.sort .zero)
          (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0)) .default) .default) .default
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 1
    rules := [
      { ctor := `TestWrap.mk, nfields := 1, rhs := Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0) }
    ]
    k := false
    isUnsafe := false
    all := [`TestRec6]
  }
  let t26 ← runConstCrossImplTest rec6 "recursor with fields"

  return t1 ++ t2 ++ t3 ++ t4 ++ t5 ++ t6 ++ t7 ++ t8 ++ t9 ++ t10 ++ t11 ++ t12 ++ t13 ++ t14 ++ t15 ++ t16 ++ t17 ++ t18 ++ t19 ++ t20 ++ t21 ++ t22 ++ t23 ++ t24 ++ t25 ++ t26

/-!
## Environment Compilation Benchmark

Times how long the Lean compiler takes to compile the full environment.
Run with: `lake test -- compile-env`
-/

/-- FFI: Compare environment compilation between Lean and Rust.
    Takes the environment's constants list and Lean's compiled (Name, ByteArray) pairs.
    Returns the number of mismatches (0 = success). -/
@[extern "rs_compare_env_compilation"]
opaque rsCompareEnvCompilation : @& List (Lean.Name × Lean.ConstantInfo) → @& List (Lean.Name × ByteArray) → UInt64

/-- Extract compiled constants from Ixon.Env as (Name, serialized bytes) pairs -/
def extractCompiledConstants (env : Ixon.Env) : List (Lean.Name × ByteArray) :=
  env.named.toList.filterMap fun (name, addr) =>
    match env.consts.get? addr with
    | some constant => some (name, serConstant constant)
    | none => none

/-!
## Incremental Block-by-Block Compilation Comparison

These FFI functions allow comparing Lean and Rust compilation block-by-block,
which helps identify exactly which blocks have mismatches.
-/

/-- Opaque type for Rust-compiled environment -/
opaque RustCompiledEnv.nonemptyType : NonemptyType
def RustCompiledEnv : Type := RustCompiledEnv.nonemptyType.type
instance : Nonempty RustCompiledEnv := RustCompiledEnv.nonemptyType.property

/-- Result of comparing a single block between Lean and Rust -/
structure BlockComparisonResult where
  isMatch : Bool
  leanBytesSize : UInt64
  rustBytesSize : UInt64
  leanSharingLen : UInt64
  rustSharingLen : UInt64
  firstDiffOffset : UInt64
  deriving Repr

/-- FFI: Simple test to verify FFI round-trip works -/
@[extern "c_rs_test_ffi_roundtrip"]
opaque rsTestFfiRoundtrip : @& Lean.Name → UInt64

/-- FFI: Compile entire environment with Rust, returns handle to RustCompiledEnv -/
@[extern "c_rs_compile_env_rust_first"]
opaque rsCompileEnvRustFirst : @& List (Lean.Name × Lean.ConstantInfo) → IO RustCompiledEnv

/-- FFI: Compare a single block (quick check).
    Returns packed u64: high 32 bits = 1 (match), 0 (mismatch), 2 (not found)
                        low 32 bits = first diff offset if mismatch -/
@[extern "c_rs_compare_block"]
opaque rsCompareBlock : @& RustCompiledEnv → @& Lean.Name → @& ByteArray → UInt64

/-- FFI: Free a RustCompiledEnv -/
@[extern "c_rs_free_rust_env"]
opaque rsFreeRustEnv : RustCompiledEnv → IO Unit

/-- FFI: Get the number of blocks in a RustCompiledEnv -/
@[extern "c_rs_get_rust_env_block_count"]
opaque rsGetRustEnvBlockCount : @& RustCompiledEnv → UInt64

/-- FFI: Get Rust's compiled bytes for a block -/
@[extern "c_rs_get_block_bytes"]
opaque rsGetBlockBytes : @& RustCompiledEnv → @& Lean.Name → IO ByteArray

/-- FFI: Get Rust's sharing vector length for a block -/
@[extern "c_rs_get_block_sharing_len"]
opaque rsGetBlockSharingLen : @& RustCompiledEnv → @& Lean.Name → UInt64

/-- Parse the packed comparison result. Returns (isMatch, firstDiffOffset) -/
def parseCompareResult (packed : UInt64) : Bool × UInt32 :=
  let code := (packed >>> 32).toUInt32
  let offset := packed.toUInt32
  (code == 1, offset)

/-- Cross-implementation environment compilation test with per-phase timing.
    Uses dbg_trace for progress tracking during pure phases. -/
def testCompileEnvCrossImpl : IO TestSeq := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Cross-Implementation Environment Compilation Test"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Get environment
  IO.println "Loading environment..."
  let envStart ← IO.monoNanosNow
  let env ← get_env!
  let envStop ← IO.monoNanosNow
  let envConsts := env.constants.toList
  let envSize := envConsts.length
  IO.println s!"  Loaded {envSize} constants in {Cronos.nanoToSec (envStop - envStart)}s"

  -- Phase 1: Canonicalize
  IO.println "Phase 1: Canonicalize..."
  let canonStart ← IO.monoNanosNow
  let canonExprs := Ix.CanonicalizeM.env env (dbg := true) (total := envSize)
  -- Force evaluation by folding over the HashMap
  let canonSize ← pure (canonExprs.fold (init := 0) fun n _ _ => n + 1)
  let canonStop ← IO.monoNanosNow
  IO.println s!"  Canonicalized {canonSize} exprs in {Cronos.nanoToSec (canonStop - canonStart)}s"

  -- Phase 2: Build dependency graph
  IO.println "Phase 2: Graph..."
  let graphStart ← IO.monoNanosNow
  let refs := Ix.GraphM.env env (dbg := true) (total := envSize)
  -- Force evaluation by folding over the Map
  let refsSize ← pure (refs.fold (init := 0) fun n _ _ => n + 1)
  let graphStop ← IO.monoNanosNow
  IO.println s!"  Graph built ({refsSize} entries) in {Cronos.nanoToSec (graphStop - graphStart)}s"

  -- Phase 3: Compute SCCs
  IO.println "Phase 3: Condense (SCC)..."
  let condenseStart ← IO.monoNanosNow
  let blocks := Ix.CondenseM.run env refs (dbg := true) (total := envSize)
  -- Force evaluation by folding over the blocks Map
  let blocksSize ← pure (blocks.blocks.fold (init := 0) fun n _ _ => n + 1)
  let condenseStop ← IO.monoNanosNow
  IO.println s!"  Condensed into {blocksSize} blocks in {Cronos.nanoToSec (condenseStop - condenseStart)}s"

  -- Phase 4: Compile blocks
  IO.println "Phase 4: Compile blocks..."
  let compileStart ← IO.monoNanosNow
  let result := Ix.CompileM.compileBlocks env canonExprs blocks (dbg := true)
  let compileStop ← IO.monoNanosNow
  let compileTime := Cronos.nanoToSec (compileStop - compileStart)

  let totalTime := Cronos.nanoToSec (compileStop - canonStart)

  match result with
  | .error msg =>
    IO.println s!"  FAILED: {msg}"
    return test "Lean compileEnv" false
  | .ok (ixonEnv, totalBytes) =>
    let numConsts := ixonEnv.constCount
    IO.println s!"  Compiled {numConsts} constants ({totalBytes} bytes) in {compileTime}s"

    -- Extract compiled constants
    IO.println "Extracting compiled constants..."
    let extractStart ← IO.monoNanosNow
    let leanCompiled := extractCompiledConstants ixonEnv
    let extractStop ← IO.monoNanosNow
    IO.println s!"  Extracted {leanCompiled.length} constants in {Cronos.nanoToSec (extractStop - extractStart)}s"

    -- Compare with Rust
    IO.println "Comparing with Rust compilation..."
    let compareStart ← IO.monoNanosNow
    let mismatches := rsCompareEnvCompilation envConsts leanCompiled
    let compareStop ← IO.monoNanosNow
    IO.println s!"  Comparison took {Cronos.nanoToSec (compareStop - compareStart)}s"

    IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    if mismatches == 0 then
      IO.println s!"✓ All {leanCompiled.length} constants match between Lean and Rust!"
      IO.println s!"  Total compile time: {totalTime}s"
      return test "cross-impl env compilation" true
    else
      IO.println s!"✗ {mismatches} mismatches found!"
      return test "cross-impl env compilation" false

/-- Incremental cross-implementation environment compilation test.
    Compiles with Rust first, then compiles each block with Lean and compares. -/
def testCompileEnvCrossImplIncremental : IO TestSeq := do
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Incremental Cross-Implementation Compilation Test"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  -- Test FFI round-trip first
  IO.println "Testing FFI round-trip..."
  let ffiResult := rsTestFfiRoundtrip `Nat.add
  let expectedMagic : UInt64 := 0xDEAD_BEEF_0000_0000
  if ffiResult &&& 0xFFFF_FFFF_0000_0000 != expectedMagic then
    IO.println s!"  FFI round-trip FAILED: got {ffiResult}, expected magic prefix {expectedMagic}"
    return test "FFI round-trip" false
  IO.println s!"  FFI round-trip OK: {ffiResult}"

  -- Load environment
  IO.println "Loading environment..."
  let envStart ← IO.monoNanosNow
  let env ← get_env!
  let envStop ← IO.monoNanosNow
  let envConsts := env.constants.toList
  let envSize := envConsts.length
  IO.println s!"  Loaded {envSize} constants in {Cronos.nanoToSec (envStop - envStart)}s"

  -- Compile with Rust first
  IO.println "Compiling with Rust first..."
  let rustEnv ← rsCompileEnvRustFirst envConsts
  let rustBlockCount := rsGetRustEnvBlockCount rustEnv
  IO.println s!"  Rust compiled {rustBlockCount} blocks"

  -- Lean preprocessing: canonicalize, graph, condense
  IO.println "Lean Phase 1: Canonicalize..."
  let canonStart ← IO.monoNanosNow
  let canonExprs := Ix.CanonicalizeM.env env (dbg := false) (total := envSize)
  let canonSize := canonExprs.fold (init := 0) fun n _ _ => n + 1
  let canonStop ← IO.monoNanosNow
  IO.println s!"  Canonicalized {canonSize} exprs in {Cronos.nanoToSec (canonStop - canonStart)}s"

  IO.println "Lean Phase 2: Graph..."
  let graphStart ← IO.monoNanosNow
  let refs := Ix.GraphM.env env (dbg := false) (total := envSize)
  let graphStop ← IO.monoNanosNow
  IO.println s!"  Graph built in {Cronos.nanoToSec (graphStop - graphStart)}s"

  IO.println "Lean Phase 3: Condense..."
  let condenseStart ← IO.monoNanosNow
  let blocks := Ix.CondenseM.run env refs (dbg := false) (total := envSize)
  let blocksSize := blocks.blocks.fold (init := 0) fun n _ _ => n + 1
  let condenseStop ← IO.monoNanosNow
  IO.println s!"  Condensed into {blocksSize} blocks in {Cronos.nanoToSec (condenseStop - condenseStart)}s"

  -- Initialize Lean compilation state
  let mut stt : Ix.CompileM.CompileState := Ix.CompileM.CompileState.new env canonExprs

  -- Build work queue (same as compileBlocks)
  let mut blockInfo : Std.HashMap Lean.Name (Set Lean.Name × Nat) := {}
  let mut reverseDeps : Std.HashMap Lean.Name (Array Lean.Name) := {}

  for (lo, all) in blocks.blocks do
    let deps := blocks.blockRefs.get! lo
    blockInfo := blockInfo.insert lo (all, deps.size)
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]

  let mut readyQueue : Array (Lean.Name × Set Lean.Name) := #[]
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.push (lo, all)

  -- Compile and compare each block
  IO.println "Lean Phase 4: Compile and compare blocks incrementally..."
  let compileStart ← IO.monoNanosNow
  let mut blocksCompiled : Nat := 0
  let mut mismatches : Nat := 0
  let mut mismatchedNames : Array Lean.Name := #[]
  let mut lastPct : Nat := 0

  while !readyQueue.isEmpty do
    let (lo, all) := readyQueue.back!
    readyQueue := readyQueue.pop

    -- Compile block with Lean
    match Ix.CompileM.compileBlockPure stt all lo with
    | Except.ok (result, cache) =>
      -- Get the constant for the lowlink name (projection if it exists, otherwise block)
      let loConstant := match result.projections.find? (·.1 == lo) with
        | some (_, proj) => proj
        | none => result.block
      let leanBytes := serConstant loConstant

      -- Compare with Rust's output
      let packed := rsCompareBlock rustEnv lo leanBytes
      let (isMatch, firstDiffOffset) := parseCompareResult packed

      if !isMatch then
        mismatches := mismatches + 1
        mismatchedNames := mismatchedNames.push lo
        if mismatches <= 10 then
          -- Get Rust's bytes for comparison
          let rustBytes ← rsGetBlockBytes rustEnv lo
          let rustSharingLen := rsGetBlockSharingLen rustEnv lo
          let leanSharingLen := loConstant.sharing.size

          IO.println s!"  MISMATCH block: {lo}"
          IO.println s!"    Lean bytes: {leanBytes.size}, Rust bytes: {rustBytes.size}"
          IO.println s!"    Lean sharing: {leanSharingLen}, Rust sharing: {rustSharingLen}"
          IO.println s!"    First diff at offset: {firstDiffOffset}"

          -- Show first few bytes of each
          let showLen := min 40 (min leanBytes.size rustBytes.size)
          if showLen > 0 then
            let leanPrefix := (leanBytes.toList.take showLen).map (·.toNat)
            let rustPrefix := (rustBytes.toList.take showLen).map (·.toNat)
            IO.println s!"    Lean prefix: {leanPrefix}"
            IO.println s!"    Rust prefix: {rustPrefix}"

          -- Deserialize both and compare sharing vectors
          match desConstant rustBytes with
          | .error e => IO.println s!"    Failed to deserialize Rust constant: {e}"
          | .ok rustConst =>
            IO.println s!"    Lean sharing vector ({loConstant.sharing.size} items):"
            for i in [:min 5 loConstant.sharing.size] do
              IO.println s!"      [{i}] {repr loConstant.sharing[i]!}"
            if loConstant.sharing.size > 5 then
              IO.println s!"      ... ({loConstant.sharing.size - 5} more)"

            IO.println s!"    Rust sharing vector ({rustConst.sharing.size} items):"
            for i in [:min 5 rustConst.sharing.size] do
              IO.println s!"      [{i}] {repr rustConst.sharing[i]!}"
            if rustConst.sharing.size > 5 then
              IO.println s!"      ... ({rustConst.sharing.size - 5} more)"

            -- Find first differing expression in sharing vectors
            let minLen := min loConstant.sharing.size rustConst.sharing.size
            for i in [:minLen] do
              if loConstant.sharing[i]! != rustConst.sharing[i]! then
                IO.println s!"    First sharing diff at index {i}:"
                IO.println s!"      Lean: {repr loConstant.sharing[i]!}"
                IO.println s!"      Rust: {repr rustConst.sharing[i]!}"
                break

            -- Analyze sharing with debug: extract root expressions from Rust constant and analyze
            if leanSharingLen != rustSharingLen.toNat && mismatches == 1 then
              IO.println s!"    [Debug] Analyzing usage counts for expressions in Rust constant:"
              -- Extract root expressions from Rust's ConstantInfo
              let rustRootExprs := match rustConst.info with
                | .defn d => #[d.typ, d.value]
                | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
                | .axio a => #[a.typ]
                | .quot q => #[q.typ]
                | .muts _ => #[]  -- complex case, skip for now
                | _ => #[]
              IO.println s!"      Analyzing {rustRootExprs.size} root expressions"
              let analyzeResult := Ix.Sharing.analyzeBlock rustRootExprs
              let effectiveSizes := Ix.Sharing.computeEffectiveSizes analyzeResult.infoMap analyzeResult.topoOrder
              IO.println s!"      Found {analyzeResult.infoMap.size} unique subterms, {analyzeResult.topoOrder.size} in topo order"
              -- Show all subterms with usage >= 2
              IO.println s!"      Subterms with usage >= 2:"
              for (hash, info) in analyzeResult.infoMap do
                if info.usageCount >= 2 then
                  let size := effectiveSizes.getD hash 0
                  let potential : Int := (info.usageCount - 1 : Int) * size - info.usageCount
                  let gross : Int := (info.usageCount - 1 : Int) * size
                  IO.println s!"        usage={info.usageCount} size={size} gross={gross} potential={potential}"
                  IO.println s!"          expr={repr info.expr}"

      -- Update state: store block and projections
      let blockBytes := Ixon.ser result.block
      let blockAddr := Address.blake3 blockBytes
      stt := { stt with
        totalBytes := stt.totalBytes + blockBytes.size
        constants := stt.constants.insert blockAddr result.block
        blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) stt.blobs
      }

      if result.projections.isEmpty then
        stt := { stt with nameToAddr := stt.nameToAddr.insert lo blockAddr }
      else
        for (name, proj) in result.projections do
          let projBytes := Ixon.ser proj
          let projAddr := Address.blake3 projBytes
          stt := { stt with
            totalBytes := stt.totalBytes + projBytes.size
            constants := stt.constants.insert projAddr proj
            nameToAddr := stt.nameToAddr.insert name projAddr
          }

      -- Update ready queue
      for name in all do
        if let some dependents := reverseDeps.get? name then
          for dependentLo in dependents do
            if let some (depAll, depCount) := blockInfo.get? dependentLo then
              let newCount := depCount - 1
              blockInfo := blockInfo.insert dependentLo (depAll, newCount)
              if newCount == 0 then
                readyQueue := readyQueue.push (dependentLo, depAll)

      blocksCompiled := blocksCompiled + 1
      let pct := (blocksCompiled * 100) / blocksSize
      if pct >= lastPct + 10 then
        IO.println s!"  [Compile] {pct}% ({blocksCompiled}/{blocksSize})"
        lastPct := pct

    | Except.error e =>
      IO.println s!"  Lean compilation error in {lo}: {repr e}"
      rsFreeRustEnv rustEnv
      return test "incremental cross-impl" false

  let compileStop ← IO.monoNanosNow

  -- Free Rust environment
  rsFreeRustEnv rustEnv

  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println s!"Compiled {blocksCompiled}/{blocksSize} blocks in {Cronos.nanoToSec (compileStop - compileStart)}s"

  if mismatches == 0 then
    IO.println s!"✓ All {blocksCompiled} blocks match between Lean and Rust!"
    return test "incremental cross-impl" true
  else
    IO.println s!"✗ {mismatches} block mismatches found!"
    if mismatchedNames.size > 10 then
      IO.println s!"  (showing first 10 of {mismatchedNames.size})"
    return test "incremental cross-impl" false

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
  testCrossImplExprs,
  testCrossImplConsts,
]

/-- Environment compilation cross-impl test suite (run with `lake test -- compile-env`) -/
def Tests.Ix.Compile.envSuiteIO: List (IO TestSeq) := [
  testCompileEnvCrossImpl,
]

/-- Incremental compilation cross-impl test suite (run with `lake test -- compile-env-incr`) -/
def Tests.Ix.Compile.envIncrSuiteIO: List (IO TestSeq) := [
  testCompileEnvCrossImplIncremental,
]
