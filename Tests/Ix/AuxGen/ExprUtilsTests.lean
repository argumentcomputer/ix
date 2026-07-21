module

public import LSpec
public import Ix.AuxGen.ExprUtils

/-!
Hash-identity property tests for `Ix.AuxGen.ExprUtils` (the pure-Lean port
of `crates/compile/src/compile/aux_gen/expr_utils.rs`).

All expressions are built through the hash-maintaining smart constructors
in `Ix.Environment`, and every assertion is a hash-based `==` (`Ix.Expr`'s
`BEq` compares embedded blake3 addresses) — so each roundtrip check is a
bit-parity check, not just a structural one.

Not yet registered in `Tests/Main.lean`; suite entry point is
`Tests.AuxGen.ExprUtils.suite`.
-/

public section

namespace Tests.AuxGen.ExprUtils

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr)

def nm (s : String) : Name := Name.mkStr .mkAnon s
def sort0 : Expr := .mkSort .mkZero
def bv (i : Nat) : Expr := .mkBVar i
def cst (s : String) : Expr := .mkConst (nm s) #[]

/-- `∀ (a : α) (b : β) (c : γ), body` -/
def tripleForall (a b c body : Expr) : Expr :=
  .mkForallE (nm "a") a
    (.mkForallE (nm "b") b (.mkForallE (nm "c") c body .default) .default)
    .default

def freshFVarTests : TestSeq :=
  test "freshFVar name scheme is _{prefix}_{idx}"
    (((freshFVar "p" 0).1.pretty == "_p_0"
      && (freshFVar "motive" 7).1.pretty == "_motive_7" : Bool))
  ++ test "freshFVar builds hash-consistent fvar node"
    ((let (n, fv) := freshFVar "p" 0
      fv == Expr.mkFVar n : Bool))
  ++ test "freshFVar distinct idx/prefix give distinct names"
    (((freshFVar "p" 0).1 != (freshFVar "p" 1).1
      && (freshFVar "a" 0).1 != (freshFVar "b" 0).1 : Bool))

def roundtripTests : TestSeq :=
  test "instantiate1 ∘ abstractFVar is identity"
    ((let (n, fv) := freshFVar "x" 0
      let e := Expr.mkApp (Expr.mkApp (cst "f") fv)
        (Expr.mkLam (nm "z") sort0 fv .default)
      instantiate1 (abstractFVar e n 0) fv == e : Bool))
  ++ test "forallTelescope/mkForall roundtrip"
    ((let orig := tripleForall sort0 sort0 sort0 (bv 0)
      let (_, decls, body) := forallTelescope orig 3 "p" 0
      mkForall body decls == orig : Bool))
  ++ test "forallTelescope/mkForall roundtrip with dependent domains"
    ((let orig := tripleForall sort0 (bv 0) (bv 1) (bv 2)
      let (_, decls, body) := forallTelescope orig 3 "p" 0
      mkForall body decls == orig : Bool))
  ++ test "lambdaTelescope/mkLambda roundtrip"
    ((let orig := Expr.mkLam (nm "x") sort0
        (Expr.mkLam (nm "y") (bv 0) (bv 1) .default) .default
      let (_, decls, body) := lambdaTelescope orig 2 "p" 0
      mkLambda body decls == orig : Bool))
  ++ test "decomposeApps/mkAppN roundtrip"
    ((let f := cst "f"
      let e := mkAppN f #[sort0, bv 0, cst "a"]
      let (head, args) := decomposeApps e
      head == f && args.size == 3 && mkAppN head args == e : Bool))

def substShiftTests : TestSeq :=
  test "shiftVars on closed term is identity"
    ((let e := tripleForall sort0 sort0 sort0 (bv 2)
      shiftVars e 5 0 == e : Bool))
  ++ test "shiftVars lifts loose bvars, respects cutoff"
    ((shiftVars (bv 0) 3 0 == bv 3 && shiftVars (bv 1) 2 2 == bv 1 : Bool))
  ++ test "instantiate1 substitutes bvar 0 and decrements the rest"
    ((instantiate1 (bv 0) sort0 == sort0
      && instantiate1 (bv 3) sort0 == bv 2
      && instantiate1At (bv 2) sort0 2 == sort0 : Bool))
  ++ test "instantiateRev substitutes bvar 0..n-1 simultaneously"
    ((let body := Expr.mkApp (bv 0) (bv 1)
      instantiateRev body #[cst "a", cst "b"]
        == Expr.mkApp (cst "a") (cst "b") : Bool))
  ++ test "instantiatePiParams peels and substitutes"
    ((instantiatePiParams (tripleForall sort0 sort0 sort0 (bv 2)) 3
        #[cst "x", cst "y", cst "z"] == cst "x" : Bool))

def betaTests : TestSeq :=
  test "betaReduce ((fun x => x) a) = a"
    ((betaReduce (Expr.mkApp (Expr.mkLam (nm "x") sort0 (bv 0) .default)
        (cst "a")) == cst "a" : Bool))
  ++ test "betaReduce reduces head spine and reapplies leftover args"
    ((let lam2 := Expr.mkLam (nm "x") sort0
        (Expr.mkLam (nm "y") sort0 (bv 1) .default) .default
      betaReduce (mkAppN lam2 #[cst "a", cst "b", cst "c"])
        == Expr.mkApp (cst "a") (cst "c") : Bool))

def miscTests : TestSeq :=
  test "consumeTypeAnnotations strips outParam/optParam, keeps others"
    ((consumeTypeAnnotations (Expr.mkApp (cst "outParam") sort0) == sort0
      && consumeTypeAnnotations (mkAppN (cst "optParam") #[sort0, cst "d"]) == sort0
      && consumeTypeAnnotations (cst "A") == cst "A" : Bool))
  ++ test "countForalls counts leading foralls only"
    ((countForalls (tripleForall sort0 sort0 sort0 (bv 0)) == 3
      && countForalls sort0 == 0 : Bool))
  ++ test "forallTelescope peels mdata between binders"
    ((let inner := Expr.mkForallE (nm "y") sort0 (bv 0) .default
      let outer := Expr.mkForallE (nm "x") sort0 (Expr.mkMData #[] inner) .default
      let (_, decls, _) := forallTelescope outer 2 "p" 0
      decls.size == 2 : Bool))
  ++ test "substFVar replaces under binders"
    ((let (n, fv) := freshFVar "x" 0
      substFVar (Expr.mkLam (nm "z") sort0 fv .default) n sort0
        == Expr.mkLam (nm "z") sort0 sort0 .default : Bool))
  ++ test "replaceConstNames renames const and proj heads"
    ((let map := Std.HashMap.ofList [(nm "A", nm "B")]
      replaceConstNames (Expr.mkApp (cst "A") (Expr.mkProj (nm "A") 0 (cst "A"))) map
        == Expr.mkApp (cst "B") (Expr.mkProj (nm "B") 0 (cst "B")) : Bool))
  ++ test "exprMentionsAnyName sees consts through binders"
    ((let names := Std.HashSet.ofList [nm "A"]
      exprMentionsAnyName
        (Expr.mkForallE (nm "x") sort0 (Expr.mkApp (bv 0) (cst "A")) .default) names
      && !exprMentionsAnyName sort0 names : Bool))
  ++ test "findMotiveFVar peels foralls then matches head fvar"
    ((let (_, m0) := freshFVar "motive" 0
      let (_, m1) := freshFVar "motive" 1
      let dom := Expr.mkForallE (nm "x") sort0 (Expr.mkApp m1 (bv 0)) .default
      findMotiveFVar dom #[m0, m1] == some 1
      && findMotiveFVar sort0 #[m0, m1] == none : Bool))

def levelTests : TestSeq :=
  test "levelMaxSmart simplifications"
    ((let u := Level.mkParam (nm "u")
      let v := Level.mkParam (nm "v")
      levelMaxSmart Level.mkZero u == u
      && levelMaxSmart u Level.mkZero == u
      && levelMaxSmart u u == u
      && levelMaxSmart (Level.mkSucc Level.mkZero)
          (Level.mkSucc (Level.mkSucc Level.mkZero))
          == Level.mkSucc (Level.mkSucc Level.mkZero)
      && levelMaxSmart u v == Level.mkMax u v : Bool))
  ++ test "levelImaxSmart simplifications"
    ((let u := Level.mkParam (nm "u")
      let v := Level.mkParam (nm "v")
      levelImaxSmart u (Level.mkSucc v) == levelMaxSmart u (Level.mkSucc v)
      && levelImaxSmart u Level.mkZero == Level.mkZero
      && levelImaxSmart Level.mkZero u == u
      && levelImaxSmart (Level.mkSucc Level.mkZero) u == u
      && levelImaxSmart u v == Level.mkIMax u v : Bool))
  ++ test "substLevels substitutes params in sorts"
    ((let u := nm "u"
      substLevels (Expr.mkSort (Level.mkParam u)) #[u] #[Level.mkZero]
        == sort0 : Bool))

def restoreTests : TestSeq :=
  test "RestoreCtx renames aux recursor consts in application position"
    ((let ctx := RestoreCtx.new ∅ ∅
        (Std.HashMap.ofList [(nm "auxrec", nm "origrec")]) #[] 0
      let (out, _) := ctx.restore (Expr.mkApp (cst "auxrec") (cst "a"))
      out == Expr.mkApp (cst "origrec") (cst "a") : Bool))

public def suite : List TestSeq :=
  [freshFVarTests, roundtripTests, substShiftTests, betaTests, miscTests,
   levelTests, restoreTests]

end Tests.AuxGen.ExprUtils

end
