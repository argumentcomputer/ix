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

/-! ## Normalization fallback tests -/

def testLevelNormalizeFallback : TestSeq :=
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  let p2 : Level .anon := Level.param 2 default
  -- imax u u = u (normalization handles this even when heuristic already does)
  test "normalize: imax u u = u"
    (Level.equalLevel (.imax p0 p0) p0) $
  -- max(imax u v, imax v u) = max(imax u v, imax v u) (symmetric)
  test "normalize: max(imax u v, imax v u) = max(imax v u, imax u v)"
    (Level.equalLevel
      (.max (.imax p0 p1) (.imax p1 p0))
      (.max (.imax p1 p0) (.imax p0 p1))) $
  -- imax(imax u v, w) = imax(imax u w, v) — cross-nested imax equivalences
  -- These exercise the canonical form's ability to handle nested imax
  test "normalize: max(w, imax(imax u w) v) = max(v, imax(imax u v) w)"
    (Level.equalLevel
      (.max p1 (.imax (.imax p0 p1) p2))
      (.max p2 (.imax (.imax p0 p2) p1))) $
  -- Soundness: distinct params are NOT equal
  test "normalize: param 0 != param 1"
    (!Level.equalLevel p0 p1) $
  -- Soundness: succ(param 0) != param 0
  test "normalize: succ(param 0) != param 0"
    (!Level.equalLevel (.succ p0) p0) $
  -- imax(u+1, u) = u+1 (via canonical form: when u>0, max(u+1,u) = u+1; when u=0, imax(1,0) = 0 ≠ 1)
  -- Actually imax(u+1, u): if u=0, result=0; if u>0, result=max(u+1,u)=u+1. So it's max(1, imax(u+1, u)).
  -- lean4lean: normalize(imax u (u+1)) = max 1 (imax (u+1) u), so imax(u+1,u) ≠ u+1 in general.
  test "normalize: imax(u+1, u) != u+1"
    (!Level.equalLevel (.imax (.succ p0) p0) (.succ p0)) $
  -- leq via normalize: imax(u,v) ≤ max(u,v) always holds
  test "normalize: imax(u,v) <= max(u,v)"
    (Level.leq (.imax p0 p1) (.max p0 p1) 0) $
  -- leq via normalize: max(u,v) ≥ imax(u,v) always holds
  test "normalize: max(u,v) >= imax(u,v)"
    (Level.leq (.imax p0 p1) (.max p0 p1) 0)

/-! ## Normalization fallback leq tests (exercises the canonical form path) -/

def testLevelLeqNormFallback : TestSeq :=
  let l0 : Level .anon := Level.zero
  let l1 : Level .anon := Level.succ Level.zero
  let l2 : Level .anon := Level.succ (Level.succ Level.zero)
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  let p2 : Level .anon := Level.param 2 default
  -- The original bug: normalization fallback had swapped arguments
  test "norm: not (succ(param 0) <= param 0)"
    (!Level.leq (.succ p0) p0 0) $
  test "norm: param 0 <= succ(param 0)"
    (Level.leq p0 (.succ p0) 0) $
  -- Concrete numeric through normalization
  test "norm: not (succ(succ zero) <= succ zero)"
    (!Level.leq l2 l1 0) $
  test "norm: succ zero <= succ(succ zero)"
    (Level.leq l1 l2 0) $
  -- imax vs max
  test "norm: imax(u,v) <= max(u,v)"
    (Level.leq (.imax p0 p1) (.max p0 p1) 0) $
  test "norm: not (max(u,v) <= imax(u,v))"
    (!Level.leq (.max p0 p1) (.imax p0 p1) 0) $
  -- imax distributes over max
  test "norm: imax(max(u,v), w) <= max(imax(u,w), imax(v,w))"
    (Level.leq
      (Level.reduce (.imax (.max p0 p1) p2))
      (Level.reduce (.max (.imax p0 p2) (.imax p1 p2))) 0) $
  -- succ of imax
  test "norm: not (succ(imax(u,v)) <= imax(u,v))"
    (!Level.leq (.succ (Level.reduce (.imax p0 p1))) (Level.reduce (.imax p0 p1)) 0) $
  -- imax edge cases
  test "norm: imax(0, u) <= u"
    (Level.leq (Level.reduce (.imax l0 p0)) p0 0) $
  test "norm: imax(succ u, v) <= max(succ u, v)"
    (Level.leq
      (Level.reduce (.imax (.succ p0) p1))
      (Level.reduce (.max (.succ p0) p1)) 0)

/-! ## Multi-parameter leq tests -/

def testLevelLeqParams : TestSeq :=
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  let p2 : Level .anon := Level.param 2 default
  -- Unrelated params
  test "not (param 0 <= param 1)"
    (!Level.leq p0 p1 0) $
  test "not (param 1 <= param 0)"
    (!Level.leq p1 p0 0) $
  test "not (succ(param 0) <= param 1)"
    (!Level.leq (.succ p0) p1 0) $
  -- max subset relationships
  test "max(u,v) <= max(u, max(v,w))"
    (Level.leq (.max p0 p1) (.max p0 (.max p1 p2)) 0) $
  test "not (max(u,v,w) <= max(u,v))"
    (!Level.leq (.max p0 (.max p1 p2)) (.max p0 p1) 0) $
  -- param <= max containing it
  test "param 0 <= max(param 0, param 1)"
    (Level.leq p0 (.max p0 p1) 0) $
  test "param 1 <= max(param 0, param 1)"
    (Level.leq p1 (.max p0 p1) 0) $
  -- succ(max) not <= max
  test "not (succ(max(u,v)) <= max(u,v))"
    (!Level.leq (.succ (.max p0 p1)) (.max p0 p1) 0)

/-! ## Equality via normalization tests -/

def testLevelEqualNorm : TestSeq :=
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  let p2 : Level .anon := Level.param 2 default
  let l1 : Level .anon := Level.succ Level.zero
  -- From lean4lean's test patterns
  test "norm eq: imax(1, u) = u"
    (Level.equalLevel (Level.reduce (.imax l1 p0)) p0) $
  test "norm eq: imax(u, u) = u"
    (Level.equalLevel (Level.reduce (.imax p0 p0)) p0) $
  -- Cross-nested imax
  test "norm eq: max(w, imax(imax(u,w), v)) = max(v, imax(imax(u,v), w))"
    (Level.equalLevel
      (.max p2 (.imax (.imax p0 p2) p1))
      (.max p1 (.imax (.imax p0 p1) p2))) $
  -- Soundness: things that should NOT be equal
  test "norm neq: succ(param 0) != param 0"
    (!Level.equalLevel (.succ p0) p0) $
  test "norm neq: param 0 != param 1"
    (!Level.equalLevel p0 p1) $
  test "norm neq: imax(succ u, u) != succ u"
    (!Level.equalLevel (.imax (.succ p0) p0) (.succ p0)) $
  test "norm neq: max(u, v) != imax(u, v)"
    (!Level.equalLevel (.max p0 p1) (.imax p0 p1))

/-! ## Canonical form property tests -/

def testLevelNormalizeCanonical : TestSeq :=
  let p0 : Level .anon := Level.param 0 default
  let p1 : Level .anon := Level.param 1 default
  -- Normalization respects commutativity of max
  test "canon: normalize(max(u,v)) = normalize(max(v,u))"
    (Level.Normalize.normalize (.max p0 p1) == Level.Normalize.normalize (.max p1 p0)) $
  -- max(max(u,v),w) = max(u,max(v,w)) (associativity)
  let p2 : Level .anon := Level.param 2 default
  test "canon: normalize(max(max(u,v),w)) = normalize(max(u,max(v,w)))"
    (Level.Normalize.normalize (.max (.max p0 p1) p2) ==
     Level.Normalize.normalize (.max p0 (.max p1 p2))) $
  -- imax(u, succ v) = max(u, succ v) after reduce
  test "canon: normalize(imax(u, succ v)) = normalize(max(u, succ v))"
    (Level.Normalize.normalize (Level.reduce (.imax p0 (.succ p1))) ==
     Level.Normalize.normalize (Level.reduce (.max p0 (.succ p1))))

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

/-! ## Primitive helpers -/

def testToCtorIfLit : TestSeq :=
  let prims := buildPrimitives
  -- natVal 0 => Nat.zero
  test "toCtorIfLit 0 = Nat.zero"
    (toCtorIfLit prims (.lit (.natVal 0) : Expr .anon) == Expr.mkConst prims.natZero #[]) $
  -- natVal 1 => Nat.succ (natVal 0)
  test "toCtorIfLit 1 = Nat.succ 0"
    (toCtorIfLit prims (.lit (.natVal 1) : Expr .anon) ==
      Expr.mkApp (Expr.mkConst prims.natSucc #[]) (.lit (.natVal 0))) $
  -- natVal 5 => Nat.succ (natVal 4)
  test "toCtorIfLit 5 = Nat.succ 4"
    (toCtorIfLit prims (.lit (.natVal 5) : Expr .anon) ==
      Expr.mkApp (Expr.mkConst prims.natSucc #[]) (.lit (.natVal 4))) $
  -- non-nat unchanged
  test "toCtorIfLit sort = sort"
    (toCtorIfLit prims (.sort .zero : Expr .anon) == (.sort .zero : Expr .anon)) $
  test "toCtorIfLit strVal = strVal"
    (toCtorIfLit prims (.lit (.strVal "hi") : Expr .anon) == (.lit (.strVal "hi") : Expr .anon))

def testStrLitToConstructor : TestSeq :=
  let prims := buildPrimitives
  -- empty string => String.mk (List.nil Char)
  let empty := strLitToConstructor (m := .anon) prims ""
  test "strLitToConstructor empty head is stringMk"
    (empty.getAppFn.isConstOf prims.stringMk) $
  test "strLitToConstructor empty has 1 arg"
    (empty.getAppNumArgs == 1) $
  -- the arg of empty string should be List.nil applied to Char
  test "strLitToConstructor empty arg head is listNil"
    (empty.appArg!.getAppFn.isConstOf prims.listNil) $
  -- single char string
  let single := strLitToConstructor (m := .anon) prims "a"
  test "strLitToConstructor \"a\" head is stringMk"
    (single.getAppFn.isConstOf prims.stringMk) $
  -- roundtrip: foldLiterals should recover the string literal
  test "foldLiterals roundtrips empty"
    (foldLiterals prims empty == .lit (.strVal "")) $
  test "foldLiterals roundtrips \"a\""
    (foldLiterals prims single == .lit (.strVal "a"))

def testIsPrimOp : TestSeq :=
  let prims := buildPrimitives
  test "isPrimOp natAdd" (isPrimOp prims prims.natAdd) $
  test "isPrimOp natSucc" (isPrimOp prims prims.natSucc) $
  test "isPrimOp natSub" (isPrimOp prims prims.natSub) $
  test "isPrimOp natMul" (isPrimOp prims prims.natMul) $
  test "isPrimOp natGcd" (isPrimOp prims prims.natGcd) $
  test "isPrimOp natMod" (isPrimOp prims prims.natMod) $
  test "isPrimOp natDiv" (isPrimOp prims prims.natDiv) $
  test "isPrimOp natBeq" (isPrimOp prims prims.natBeq) $
  test "isPrimOp natBle" (isPrimOp prims prims.natBle) $
  test "isPrimOp natLand" (isPrimOp prims prims.natLand) $
  test "isPrimOp natLor" (isPrimOp prims prims.natLor) $
  test "isPrimOp natXor" (isPrimOp prims prims.natXor) $
  test "isPrimOp natShiftLeft" (isPrimOp prims prims.natShiftLeft) $
  test "isPrimOp natShiftRight" (isPrimOp prims prims.natShiftRight) $
  test "isPrimOp natPow" (isPrimOp prims prims.natPow) $
  test "not isPrimOp nat" (!isPrimOp prims prims.nat) $
  test "not isPrimOp bool" (!isPrimOp prims prims.bool) $
  test "not isPrimOp default" (!isPrimOp prims default)

def testFoldLiterals : TestSeq :=
  let prims := buildPrimitives
  -- Nat.zero => lit 0
  test "foldLiterals Nat.zero = lit 0"
    (foldLiterals prims (Expr.mkConst prims.natZero #[] : Expr .anon) == .lit (.natVal 0)) $
  -- Nat.succ (lit 0) => lit 1
  let succZero : Expr .anon := Expr.mkApp (Expr.mkConst prims.natSucc #[]) (.lit (.natVal 0))
  test "foldLiterals Nat.succ(lit 0) = lit 1"
    (foldLiterals prims succZero == .lit (.natVal 1)) $
  -- Nat.succ (lit 4) => lit 5
  let succ4 : Expr .anon := Expr.mkApp (Expr.mkConst prims.natSucc #[]) (.lit (.natVal 4))
  test "foldLiterals Nat.succ(lit 4) = lit 5"
    (foldLiterals prims succ4 == .lit (.natVal 5)) $
  -- non-nat expressions are unchanged
  test "foldLiterals bvar = bvar"
    (foldLiterals prims (.bvar 0 () : Expr .anon) == (.bvar 0 () : Expr .anon))

/-! ## Suite -/

def suite : List TestSeq := [
  group "Expr equality" testExprHashEq,
  group "Expr operations" testExprOps,
  group "Level operations" $
    testLevelOps ++
    group "imax reduction" testLevelReduceIMax ++
    group "max reduction" testLevelReduceMax ++
    group "complex leq" testLevelLeqComplex ++
    group "normalize fallback" testLevelNormalizeFallback ++
    group "norm fallback leq" testLevelLeqNormFallback ++
    group "multi-param leq" testLevelLeqParams ++
    group "equality via norm" testLevelEqualNorm ++
    group "canonical form" testLevelNormalizeCanonical ++
    group "bulk instantiation" testLevelInstBulkReduce,
  group "Reducibility hints" testReducibilityHintsLt,
  group "Inductive helpers" testHelperFunctions,
  group "Primitive helpers" $
    group "toCtorIfLit" testToCtorIfLit ++
    group "strLitToConstructor" testStrLitToConstructor ++
    group "isPrimOp" testIsPrimOp ++
    group "foldLiterals" testFoldLiterals,
]

end Tests.Ix.Kernel.Unit
