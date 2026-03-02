/-
  Unit tests for kernel types: Expr equality, Expr operations, Level operations,
  reducibility hints, and inductive helper functions.
-/
import Ix.Kernel
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec
open Ix.Kernel
open Tests.Ix.Kernel.Helpers

namespace Tests.Ix.Kernel.Unit

/-! ## Expression equality -/

def testExprHashEq : TestSeq :=
  let bv0 : Expr .anon := Expr.mkBVar 0
  let bv0' : Expr .anon := Expr.mkBVar 0
  let bv1 : Expr .anon := Expr.mkBVar 1
  test "mkBVar 0 == mkBVar 0" (bv0 == bv0') $
  test "mkBVar 0 != mkBVar 1" (bv0 != bv1) $
  -- Sort equality
  let s0 : Expr .anon := Expr.mkSort Level.zero
  let s0' : Expr .anon := Expr.mkSort Level.zero
  let s1 : Expr .anon := Expr.mkSort (Level.succ Level.zero)
  test "mkSort 0 == mkSort 0" (s0 == s0') $
  test "mkSort 0 != mkSort 1" (s0 != s1) $
  -- App equality
  let app1 := Expr.mkApp bv0 bv1
  let app1' := Expr.mkApp bv0 bv1
  let app2 := Expr.mkApp bv1 bv0
  test "mkApp bv0 bv1 == mkApp bv0 bv1" (app1 == app1') $
  test "mkApp bv0 bv1 != mkApp bv1 bv0" (app1 != app2) $
  -- Lambda equality
  let lam1 := Expr.mkLam s0 bv0
  let lam1' := Expr.mkLam s0 bv0
  let lam2 := Expr.mkLam s1 bv0
  test "mkLam s0 bv0 == mkLam s0 bv0" (lam1 == lam1') $
  test "mkLam s0 bv0 != mkLam s1 bv0" (lam1 != lam2) $
  -- Forall equality
  let pi1 := Expr.mkForallE s0 s1
  let pi1' := Expr.mkForallE s0 s1
  test "mkForallE s0 s1 == mkForallE s0 s1" (pi1 == pi1') $
  -- Const equality
  let addr1 := Address.blake3 (ByteArray.mk #[1])
  let addr2 := Address.blake3 (ByteArray.mk #[2])
  let c1 : Expr .anon := Expr.mkConst addr1 #[]
  let c1' : Expr .anon := Expr.mkConst addr1 #[]
  let c2 : Expr .anon := Expr.mkConst addr2 #[]
  test "mkConst addr1 == mkConst addr1" (c1 == c1') $
  test "mkConst addr1 != mkConst addr2" (c1 != c2) $
  -- Const with levels
  let c1l : Expr .anon := Expr.mkConst addr1 #[Level.zero]
  let c1l' : Expr .anon := Expr.mkConst addr1 #[Level.zero]
  let c1l2 : Expr .anon := Expr.mkConst addr1 #[Level.succ Level.zero]
  test "mkConst addr1 [0] == mkConst addr1 [0]" (c1l == c1l') $
  test "mkConst addr1 [0] != mkConst addr1 [1]" (c1l != c1l2) $
  -- Literal equality
  let nat0 : Expr .anon := Expr.mkLit (.natVal 0)
  let nat0' : Expr .anon := Expr.mkLit (.natVal 0)
  let nat1 : Expr .anon := Expr.mkLit (.natVal 1)
  let str1 : Expr .anon := Expr.mkLit (.strVal "hello")
  let str1' : Expr .anon := Expr.mkLit (.strVal "hello")
  let str2 : Expr .anon := Expr.mkLit (.strVal "world")
  test "lit nat 0 == lit nat 0" (nat0 == nat0') $
  test "lit nat 0 != lit nat 1" (nat0 != nat1) $
  test "lit str hello == lit str hello" (str1 == str1') $
  test "lit str hello != lit str world" (str1 != str2)

/-! ## Expression operations -/

def testExprOps : TestSeq :=
  -- getAppFn / getAppArgs
  let bv0 : Expr .anon := Expr.mkBVar 0
  let bv1 : Expr .anon := Expr.mkBVar 1
  let bv2 : Expr .anon := Expr.mkBVar 2
  let app := Expr.mkApp (Expr.mkApp bv0 bv1) bv2
  test "getAppFn (app (app bv0 bv1) bv2) == bv0" (app.getAppFn == bv0) $
  test "getAppNumArgs == 2" (app.getAppNumArgs == 2) $
  test "getAppArgs[0] == bv1" (app.getAppArgs[0]! == bv1) $
  test "getAppArgs[1] == bv2" (app.getAppArgs[1]! == bv2) $
  -- mkAppN round-trips
  let rebuilt := Expr.mkAppN bv0 #[bv1, bv2]
  test "mkAppN round-trips" (rebuilt == app) $
  -- Predicates
  test "isApp" app.isApp $
  test "isSort" (Expr.mkSort (Level.zero : Level .anon)).isSort $
  test "isLambda" (Expr.mkLam bv0 bv1).isLambda $
  test "isForall" (Expr.mkForallE bv0 bv1).isForall $
  test "isLit" (Expr.mkLit (.natVal 42) : Expr .anon).isLit $
  test "isBVar" bv0.isBVar $
  test "isConst" (Expr.mkConst (m := .anon) default #[]).isConst $
  -- Accessors
  let s1 : Expr .anon := Expr.mkSort (Level.succ Level.zero)
  test "sortLevel!" (s1.sortLevel! == Level.succ Level.zero) $
  test "bvarIdx!" (bv1.bvarIdx! == 1)

/-! ## Level operations -/

def testLevelOps : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- reduce
  test "reduce zero" (Level.reduce l0 == l0) $
  test "reduce (succ zero)" (Level.reduce l1 == l1) $
  -- equalLevel
  test "zero equiv zero" (Level.equalLevel l0 l0) $
  test "succ zero equiv succ zero" (Level.equalLevel l1 l1) $
  test "max a b equiv max b a"
    (Level.equalLevel (Level.max p0 p1) (Level.max p1 p0)) $
  test "zero not equiv succ zero" (!Level.equalLevel l0 l1) $
  -- leq
  test "zero <= zero" (Level.leq l0 l0 0) $
  test "succ zero <= zero + 1" (Level.leq l1 l0 1) $
  test "not (succ zero <= zero)" (!Level.leq l1 l0 0) $
  test "param 0 <= param 0" (Level.leq p0 p0 0) $
  test "succ (param 0) <= param 0 + 1"
    (Level.leq (Level.succ p0) p0 1) $
  test "not (succ (param 0) <= param 0)"
    (!Level.leq (Level.succ p0) p0 0)

def testLevelReduceIMax : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- imax u 0 = 0
  test "imax u 0 = 0" (Level.reduceIMax p0 l0 == l0) $
  -- imax u (succ v) = max u (succ v)
  test "imax u (succ v) = max u (succ v)"
    (Level.equalLevel (Level.reduceIMax p0 l1) (Level.reduceMax p0 l1)) $
  -- imax u u = u (same param)
  test "imax u u = u" (Level.reduceIMax p0 p0 == p0) $
  -- imax u v stays imax (different params)
  test "imax u v stays imax"
    (Level.reduceIMax p0 p1 == Level.imax p0 p1) $
  -- nested: imax u (imax v 0) — reduce inner first, then outer
  let inner := Level.reduceIMax p1 l0  -- = 0
  test "imax u (imax v 0) = imax u 0 = 0"
    (Level.reduceIMax p0 inner == l0)

def testLevelReduceMax : TestSeq :=
  let l0 : Level .anon := Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- max 0 u = u
  test "max 0 u = u" (Level.reduceMax l0 p0 == p0) $
  -- max u 0 = u
  test "max u 0 = u" (Level.reduceMax p0 l0 == p0) $
  -- max (succ u) (succ v) = succ (max u v)
  test "max (succ u) (succ v) = succ (max u v)"
    (Level.reduceMax (Level.succ p0) (Level.succ p1)
      == Level.succ (Level.reduceMax p0 p1)) $
  -- max p0 p0 = p0
  test "max p0 p0 = p0" (Level.reduceMax p0 p0 == p0)

def testLevelLeqComplex : TestSeq :=
  let l0 : Level .anon := Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- max u v <= max v u (symmetry)
  test "max u v <= max v u"
    (Level.leq (Level.max p0 p1) (Level.max p1 p0) 0) $
  -- u <= max u v
  test "u <= max u v"
    (Level.leq p0 (Level.max p0 p1) 0) $
  -- imax u (succ v) <= max u (succ v) — after reduce they're equal
  let lhs := Level.reduce (Level.imax p0 (.succ p1))
  let rhs := Level.reduce (Level.max p0 (.succ p1))
  test "imax u (succ v) <= max u (succ v)"
    (Level.leq lhs rhs 0) $
  -- imax u 0 <= 0
  test "imax u 0 <= 0"
    (Level.leq (Level.reduce (.imax p0 l0)) l0 0) $
  -- not (succ (max u v) <= max u v)
  test "not (succ (max u v) <= max u v)"
    (!Level.leq (Level.succ (Level.max p0 p1)) (Level.max p0 p1) 0) $
  -- imax u u <= u
  test "imax u u <= u"
    (Level.leq (Level.reduce (Level.imax p0 p0)) p0 0) $
  -- imax 1 (imax 1 u) = u (nested imax decomposition)
  let l1 : Level .anon := Level.succ Level.zero
  let nested := Level.reduce (Level.imax l1 (Level.imax l1 p0))
  test "imax 1 (imax 1 u) <= u"
    (Level.leq nested p0 0) $
  test "u <= imax 1 (imax 1 u)"
    (Level.leq p0 nested 0)

def testLevelInstBulkReduce : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- Basic: param 0 with [zero] = zero
  test "param 0 with [zero] = zero"
    (Level.instBulkReduce #[l0] p0 == l0) $
  -- Multi: param 1 with [zero, succ zero] = succ zero
  test "param 1 with [zero, succ zero] = succ zero"
    (Level.instBulkReduce #[l0, l1] p1 == l1) $
  -- Out-of-bounds: param 2 with 2-element array shifts
  let p2 : Level .anon := Level.param 2 default
  test "param 2 with 2-elem array shifts to param 0"
    (Level.instBulkReduce #[l0, l1] p2 == Level.param 0 default) $
  -- Compound: imax (param 0) (param 1) with [zero, succ zero]
  let compound := Level.imax p0 p1
  let result := Level.instBulkReduce #[l0, l1] compound
  -- imax 0 (succ 0) = max 0 (succ 0) = succ 0
  test "imax (param 0) (param 1) subst [zero, succ zero]"
    (Level.equalLevel result l1)

/-! ## Reducibility hints -/

def testReducibilityHintsLt : TestSeq :=
  -- ordering: opaque < regular(n) < abbrev (abbrev unfolds first)
  test "regular 1 < regular 2" (ReducibilityHints.lt' (.regular 1) (.regular 2)) $
  test "not (regular 2 < regular 1)" (!ReducibilityHints.lt' (.regular 2) (.regular 1)) $
  test "opaque < regular" (ReducibilityHints.lt' .opaque (.regular 5)) $
  test "opaque < abbrev" (ReducibilityHints.lt' .opaque .abbrev) $
  test "regular < abbrev" (ReducibilityHints.lt' (.regular 5) .abbrev) $
  test "not (regular < opaque)" (!ReducibilityHints.lt' (.regular 5) .opaque) $
  test "not (abbrev < regular)" (!ReducibilityHints.lt' .abbrev (.regular 5)) $
  test "not (abbrev < opaque)" (!ReducibilityHints.lt' .abbrev .opaque) $
  test "not (opaque < opaque)" (!ReducibilityHints.lt' .opaque .opaque) $
  test "not (regular 5 < regular 5)" (!ReducibilityHints.lt' (.regular 5) (.regular 5))

/-! ## Inductive helper functions -/

def testHelperFunctions : TestSeq :=
  -- exprMentionsConst
  let addr1 := mkAddr 200
  let addr2 := mkAddr 201
  let c1 : Expr .anon := .const addr1 #[] ()
  let c2 : Expr .anon := .const addr2 #[] ()
  test "exprMentionsConst: direct match"
    (exprMentionsConst c1 addr1) $
  test "exprMentionsConst: no match"
    (!exprMentionsConst c2 addr1) $
  test "exprMentionsConst: in app fn"
    (exprMentionsConst (.app c1 c2) addr1) $
  test "exprMentionsConst: in app arg"
    (exprMentionsConst (.app c2 c1) addr1) $
  test "exprMentionsConst: in forallE domain"
    (exprMentionsConst (.forallE c1 c2 () () : Expr .anon) addr1) $
  test "exprMentionsConst: in forallE body"
    (exprMentionsConst (.forallE c2 c1 () () : Expr .anon) addr1) $
  test "exprMentionsConst: in lam"
    (exprMentionsConst (.lam c1 c2 () () : Expr .anon) addr1) $
  test "exprMentionsConst: absent in sort"
    (!exprMentionsConst (.sort .zero : Expr .anon) addr1) $
  test "exprMentionsConst: absent in bvar"
    (!exprMentionsConst (.bvar 0 () : Expr .anon) addr1) $
  -- getIndResultLevel
  test "getIndResultLevel: sort zero"
    (getIndResultLevel (.sort .zero : Expr .anon) == some .zero) $
  test "getIndResultLevel: sort (succ zero)"
    (getIndResultLevel (.sort (.succ .zero) : Expr .anon) == some (.succ .zero)) $
  test "getIndResultLevel: forallE _ (sort zero)"
    (getIndResultLevel (.forallE (.sort .zero) (.sort (.succ .zero)) () () : Expr .anon) == some (.succ .zero)) $
  test "getIndResultLevel: bvar (no sort)"
    (getIndResultLevel (.bvar 0 () : Expr .anon) == none) $
  -- levelIsNonZero
  test "levelIsNonZero: zero is false"
    (!levelIsNonZero (.zero : Level .anon)) $
  test "levelIsNonZero: succ zero is true"
    (levelIsNonZero (.succ .zero : Level .anon)) $
  test "levelIsNonZero: param is false"
    (!levelIsNonZero (.param 0 () : Level .anon)) $
  test "levelIsNonZero: max(succ 0, param) is true"
    (levelIsNonZero (.max (.succ .zero) (.param 0 ()) : Level .anon)) $
  test "levelIsNonZero: imax(param, succ 0) is true"
    (levelIsNonZero (.imax (.param 0 ()) (.succ .zero) : Level .anon)) $
  test "levelIsNonZero: imax(succ, param) depends on second"
    (!levelIsNonZero (.imax (.succ .zero) (.param 0 ()) : Level .anon)) $
  -- getCtorReturnType
  test "getCtorReturnType: no binders returns expr"
    (getCtorReturnType c1 0 0 == c1) $
  test "getCtorReturnType: skips foralls"
    (getCtorReturnType (.forallE c2 c1 () () : Expr .anon) 0 1 == c1)

/-! ## Suite -/

def suite : List TestSeq := [
  group "Expr equality" testExprHashEq,
  group "Expr operations" testExprOps,
  group "Level operations" $
    testLevelOps ++
    group "imax reduction" testLevelReduceIMax ++
    group "max reduction" testLevelReduceMax ++
    group "complex leq" testLevelLeqComplex ++
    group "bulk instantiation" testLevelInstBulkReduce,
  group "Reducibility hints" testReducibilityHintsLt,
  group "Inductive helpers" testHelperFunctions,
]

end Tests.Ix.Kernel.Unit
