module
public import Ix.GraphM
public import Ix.Compile.FrontEnd
public import Ix.Environment
public import Ix.Meta
public import LSpec

/-!
  Tests for Ix.GraphM module.
  - Unit tests for reference extraction from expressions and constants
-/

open LSpec Ix

namespace Tests.Ix.GraphM

/-! ## Helper functions -/

/-- Create a simple Ix.Name from a string -/
def mkName (s : String) : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon s

/-- Create an Ix constant expression -/
def mkConstExpr (s : String) : Ix.Expr := Ix.Expr.mkConst (mkName s) #[]

/-- Simple type expression (Nat) -/
def natType : Ix.Expr := mkConstExpr "Nat"

/-- Create a simple ConstantVal -/
def mkConstVal (name : String) (type : Ix.Expr) : Ix.ConstantVal :=
  { name := mkName name, levelParams := #[], type := type }

/-- Convert Set to sorted list for deterministic comparison -/
def setToSortedList (s : Set Ix.Name) : List String :=
  (s.toList.map toString).mergeSort

/-! ## Test: graphExpr reference extraction -/

def testGraphExprConst : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let expr := mkConstExpr "Foo"
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "const extracts name" (refs.contains (mkName "Foo"))

def testGraphExprBvar : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let expr := Ix.Expr.mkBVar 0
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "bvar has no refs" (refs.isEmpty)

def testGraphExprSort : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let expr := Ix.Expr.mkSort Ix.Level.mkZero
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "sort has no refs" (refs.isEmpty)

def testGraphExprApp : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let f := mkConstExpr "f"
  let a := mkConstExpr "a"
  let expr := Ix.Expr.mkApp f a
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "app collects f" (refs.contains (mkName "f")) ++
  test "app collects a" (refs.contains (mkName "a")) ++
  test "app has 2 refs" (refs.size == 2)

def testGraphExprLam : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let body := mkConstExpr "B"
  let expr := Ix.Expr.mkLam (mkName "x") ty body .default
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "lam collects type" (refs.contains (mkName "T")) ++
  test "lam collects body" (refs.contains (mkName "B")) ++
  test "lam has 2 refs" (refs.size == 2)

def testGraphExprForallE : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let body := mkConstExpr "B"
  let expr := Ix.Expr.mkForallE (mkName "x") ty body .default
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "forallE collects type" (refs.contains (mkName "T")) ++
  test "forallE collects body" (refs.contains (mkName "B")) ++
  test "forallE has 2 refs" (refs.size == 2)

def testGraphExprLetE : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let val := mkConstExpr "V"
  let body := mkConstExpr "B"
  let expr := Ix.Expr.mkLetE (mkName "x") ty val body false
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "letE collects type" (refs.contains (mkName "T")) ++
  test "letE collects val" (refs.contains (mkName "V")) ++
  test "letE collects body" (refs.contains (mkName "B")) ++
  test "letE has 3 refs" (refs.size == 3)

def testGraphExprProj : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let struct := mkConstExpr "S"
  let expr := Ix.Expr.mkProj (mkName "MyType") 0 struct
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "proj collects typeName" (refs.contains (mkName "MyType")) ++
  test "proj collects struct" (refs.contains (mkName "S")) ++
  test "proj has 2 refs" (refs.size == 2)

def testGraphExprLit : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let expr := Ix.Expr.mkLit (.natVal 42)
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphExpr expr)
  test "lit has no refs" (refs.isEmpty)

/-! ## Test: graphConst for each ConstantInfo variant -/

def testGraphConstAxiom : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let ax := Ix.ConstantInfo.axiomInfo {
    cnst := mkConstVal "myAxiom" ty,
    isUnsafe := false
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst ax)
  test "axiom refs type" (refs.contains (mkName "T")) ++
  test "axiom has 1 ref" (refs.size == 1)

def testGraphConstDefn : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let val := mkConstExpr "V"
  let defn := Ix.ConstantInfo.defnInfo {
    cnst := mkConstVal "myDef" ty,
    value := val,
    hints := .opaque,
    safety := .safe,
    all := #[]
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst defn)
  test "defn refs type" (refs.contains (mkName "T")) ++
  test "defn refs value" (refs.contains (mkName "V")) ++
  test "defn has 2 refs" (refs.size == 2)

def testGraphConstThm : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let val := mkConstExpr "V"
  let thm := Ix.ConstantInfo.thmInfo {
    cnst := mkConstVal "myThm" ty,
    value := val,
    all := #[]
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst thm)
  test "thm refs type" (refs.contains (mkName "T")) ++
  test "thm refs value" (refs.contains (mkName "V")) ++
  test "thm has 2 refs" (refs.size == 2)

def testGraphConstOpaque : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let val := mkConstExpr "V"
  let opq := Ix.ConstantInfo.opaqueInfo {
    cnst := mkConstVal "myOpaque" ty,
    value := val,
    isUnsafe := false,
    all := #[]
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst opq)
  test "opaque refs type" (refs.contains (mkName "T")) ++
  test "opaque refs value" (refs.contains (mkName "V")) ++
  test "opaque has 2 refs" (refs.size == 2)

def testGraphConstQuot : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let quot := Ix.ConstantInfo.quotInfo {
    cnst := mkConstVal "myQuot" ty,
    kind := .type
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst quot)
  test "quot refs type" (refs.contains (mkName "T")) ++
  test "quot has 1 ref" (refs.size == 1)

def testGraphConstInduct : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let induct := Ix.ConstantInfo.inductInfo {
    cnst := mkConstVal "MyInductive" ty,
    numParams := 0,
    numIndices := 0,
    all := #[mkName "MyInductive"],
    ctors := #[mkName "MyInductive.mk"],
    numNested := 0,
    isRec := false,
    isUnsafe := false,
    isReflexive := false
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst induct)
  test "induct refs type" (refs.contains (mkName "T")) ++
  test "induct refs ctor name" (refs.contains (mkName "MyInductive.mk")) ++
  test "induct has 2 refs" (refs.size == 2)

def testGraphConstCtor : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let ctor := Ix.ConstantInfo.ctorInfo {
    cnst := mkConstVal "MyType.mk" ty,
    induct := mkName "MyType",
    cidx := 0,
    numParams := 0,
    numFields := 0,
    isUnsafe := false
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst ctor)
  test "ctor refs type" (refs.contains (mkName "T")) ++
  test "ctor refs induct" (refs.contains (mkName "MyType")) ++
  test "ctor has 2 refs" (refs.size == 2)

def testGraphConstRec : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let ty := mkConstExpr "T"
  let rhs := mkConstExpr "R"
  let recConst := Ix.ConstantInfo.recInfo {
    cnst := { name := Ix.Name.mkStr (mkName "MyType") "rec", levelParams := #[], type := ty },
    all := #[mkName "MyType"],
    numParams := 0,
    numIndices := 0,
    numMotives := 1,
    numMinors := 1,
    rules := #[{ ctor := mkName "MyType.mk", nfields := 0, rhs := rhs }],
    k := false,
    isUnsafe := false
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst recConst)
  test "rec refs type" (refs.contains (mkName "T")) ++
  test "rec refs ctor name" (refs.contains (mkName "MyType.mk")) ++
  test "rec refs rhs" (refs.contains (mkName "R")) ++
  test "rec has 3 refs" (refs.size == 3)

/-- A recursor of a mutual block refers to its family: the other members'
recursors and the nested auxiliaries' `rec_N`, not to itself. -/
def testGraphConstRecFamily : TestSeq :=
  let env : Ix.Environment := { consts := {} }
  let a := mkName "A"
  let b := mkName "B"
  let recConst := Ix.ConstantInfo.recInfo {
    cnst := { name := Ix.Name.mkStr b "rec", levelParams := #[], type := mkConstExpr "T" },
    all := #[a, b],
    numParams := 0,
    numIndices := 0,
    numMotives := 3,
    numMinors := 0,
    rules := #[],
    k := false,
    isUnsafe := false
  }
  let (refs, _) := Ix.GraphM.run env .init (Ix.graphConst recConst)
  test "mutual rec refs its sibling's recursor" (refs.contains (Ix.Name.mkStr a "rec")) ++
  test "mutual rec refs the nested auxiliary's recursor" (refs.contains (Ix.Name.mkStr a "rec_1")) ++
  test "mutual rec does not ref itself" (!refs.contains (Ix.Name.mkStr b "rec")) ++
  test "mutual rec has 3 refs" (refs.size == 3)

/-! ## Test: GraphM.envSerial builds complete graph -/

def testGraphMEnv : TestSeq :=
  -- Create a small synthetic environment
  let a := mkName "A"
  let b := mkName "B"
  let c := mkName "C"

  -- A: type refs B
  let aConst := Ix.ConstantInfo.axiomInfo {
    cnst := { name := a, levelParams := #[], type := mkConstExpr "B" },
    isUnsafe := false
  }
  -- B: type refs C
  let bConst := Ix.ConstantInfo.axiomInfo {
    cnst := { name := b, levelParams := #[], type := mkConstExpr "C" },
    isUnsafe := false
  }
  -- C: type refs nothing (just a sort)
  let cConst := Ix.ConstantInfo.axiomInfo {
    cnst := { name := c, levelParams := #[], type := Ix.Expr.mkSort Ix.Level.mkZero },
    isUnsafe := false
  }

  let env : Ix.Environment := {
    consts := ({} : Std.HashMap _ _).insert a aConst |>.insert b bConst |>.insert c cConst
  }

  let graph := Ix.GraphM.envSerial env
  test "graph has 3 entries" (graph.size == 3) ++
  test "A refs B" ((graph.get? a).map (·.contains b) |>.getD false) ++
  test "B refs C" ((graph.get? b).map (·.contains c) |>.getD false) ++
  test "C refs empty" ((graph.get? c).map (·.isEmpty) |>.getD false)

/-! ## Test: FrontEnd.graph vs envSerial equivalence -/

def testFrontEndVsSerial : TestSeq := Id.run do
  -- Create a synthetic environment
  let names := #["A", "B", "C", "D", "E"].map mkName
  let mut consts : Std.HashMap Ix.Name Ix.ConstantInfo := {}

  -- Create chain: A->B->C->D->E->()
  for i in [:names.size] do
    let name := names[i]!
    let ty := if i + 1 < names.size
      then Ix.Expr.mkConst names[i+1]! #[]
      else Ix.Expr.mkSort Ix.Level.mkZero
    let c := Ix.ConstantInfo.axiomInfo {
      cnst := { name := name, levelParams := #[], type := ty },
      isUnsafe := false
    }
    consts := consts.insert name c

  let env : Ix.Environment := { consts := consts }

  let graphFrontEnd := Ix.Compile.FrontEnd.graph env
  let graphSerial := Ix.GraphM.envSerial env

  -- Compare sizes
  let sizeMatch := graphFrontEnd.size == graphSerial.size

  -- Compare all entries
  let mut allMatch := true
  for (name, feRefs) in graphFrontEnd do
    match graphSerial.get? name with
    | none => allMatch := false
    | some serialRefs =>
      if feRefs.size != serialRefs.size then
        allMatch := false
      else
        for r in feRefs do
          if !serialRefs.contains r then
            allMatch := false

  return test "sizes match" sizeMatch ++
    test "all entries match" allMatch

/-! ## Full Test Suite (unit tests) -/

public def suite : List TestSeq := [
  group "graphExpr" (
    testGraphExprConst ++
    testGraphExprBvar ++
    testGraphExprSort ++
    testGraphExprApp ++
    testGraphExprLam ++
    testGraphExprForallE ++
    testGraphExprLetE ++
    testGraphExprProj ++
    testGraphExprLit
  ),
  group "graphConst" (
    testGraphConstAxiom ++
    testGraphConstDefn ++
    testGraphConstThm ++
    testGraphConstOpaque ++
    testGraphConstQuot ++
    testGraphConstInduct ++
    testGraphConstCtor ++
    testGraphConstRec ++
    testGraphConstRecFamily
  ),
  group "GraphM.envSerial" (
    testGraphMEnv ++
    testFrontEndVsSerial
  )
]

end Tests.Ix.GraphM
