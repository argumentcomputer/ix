module

public import LSpec
public import Ix.AuxGen.Levels

/-!
Hash-identity property tests for `Ix.AuxGen.Levels` (the pure-Lean port of
the level-arithmetic suite in `crates/compile/src/compile/aux_gen/below.rs`).

Every expected value below was derived BY HAND by tracing the Rust
algorithm (`level_max` match arms, `level_normalize`'s
flatten/sort/subsume/rebuild pipeline), and every assertion is a
hash-based `==` (`Ix.Level`'s `BEq` compares embedded blake3 addresses) —
so each check is a bit-parity check, not just a structural one.

Not yet registered in `Tests/Main.lean`; suite entry point is
`Tests.AuxGen.Levels.suite`.
-/

public section

namespace Tests.AuxGen.Levels

open LSpec
open Ix.AuxGen
open Ix (Name Level Expr)

def nm (s : String) : Name := Name.mkStr .mkAnon s
def u : Level := Level.mkParam (nm "u")
def v : Level := Level.mkParam (nm "v")
def zero : Level := Level.mkZero
def one : Level := Level.mkSucc zero
def two : Level := Level.mkSucc one

/-- One case per `level_max` early return (below.rs:1391-1412). -/
def levelMaxTests : TestSeq :=
  test "levelMax: equal operands"
    ((levelMax u u == u : Bool))
  ++ test "levelMax: zero absorption both sides"
    ((levelMax zero u == u && levelMax u zero == u : Bool))
  ++ test "levelMax: subsumption by direct max child, both directions"
    ((let m := Level.mkMax u v
      levelMax m u == m && levelMax m v == m
      && levelMax u m == m && levelMax v m == m : Bool))
  ++ test "levelMax: explicit absorption max(succ u, 1) = succ u"
    ((levelMax (Level.mkSucc u) one == Level.mkSucc u
      && levelMax one (Level.mkSucc u) == Level.mkSucc u : Bool))
  ++ test "levelMax: same-base offsets keep the larger"
    ((levelMax (Level.mkSucc (Level.mkSucc u)) (Level.mkSucc u)
        == Level.mkSucc (Level.mkSucc u)
      && levelMax (Level.mkSucc u) (Level.mkSucc (Level.mkSucc u))
        == Level.mkSucc (Level.mkSucc u) : Bool))
  ++ test "levelMax: default falls through to a raw Max node"
    ((levelMax u v == Level.mkMax u v : Bool))

/-- Hand-traced through the Rust `level_normalize` max pipeline:
    flatten -> sort_by(norm_lt) -> skip_explicit/is_explicit_subsumed ->
    mk_max_aux. -/
def normalizeMaxFixtureTests : TestSeq :=
  test "levelNormalize sorts max args (max v u -> max u v)"
    ((levelNormalize (Level.mkMax v u) == Level.mkMax u v : Bool))
  ++ test "levelNormalize drops subsumed numeral (max 1 (succ u) -> succ u)"
    ((levelNormalize (Level.mkMax one (Level.mkSucc u)) == Level.mkSucc u : Bool))
  ++ test "levelNormalize keeps dominating numeral (max 2 u stays, sorted)"
    ((levelNormalize (Level.mkMax two u) == Level.mkMax two u
      && levelNormalize (Level.mkMax u two) == Level.mkMax two u : Bool))
  ++ test "levelNormalize combines same-base args by max offset"
    ((levelNormalize (Level.mkMax u (Level.mkMax (Level.mkSucc u) v))
        == Level.mkMax (Level.mkSucc u) v : Bool))
  ++ test "levelNormalize distributes outer offset into max args"
    ((levelNormalize (Level.mkSucc (Level.mkMax v u))
        == Level.mkMax (Level.mkSucc u) (Level.mkSucc v) : Bool))

/-- Hand-traced through the Rust `level_normalize` imax branch and
    `mk_imax_aux`. -/
def normalizeImaxFixtureTests : TestSeq :=
  test "levelNormalize imax: never-zero rhs collapses to max"
    ((levelNormalize (Level.mkIMax u (Level.mkSucc v))
        == Level.mkMax u (Level.mkSucc v) : Bool))
  ++ test "levelNormalize imax: rhs zero collapses to zero"
    ((levelNormalize (Level.mkIMax u zero) == zero : Bool))
  ++ test "levelNormalize imax: lhs zero or one collapses to rhs"
    ((levelNormalize (Level.mkIMax zero u) == u
      && levelNormalize (Level.mkIMax one u) == u : Bool))
  ++ test "levelNormalize imax: equal sides collapse"
    ((levelNormalize (Level.mkIMax u u) == u : Bool))
  ++ test "levelNormalize imax: undecidable rhs keeps imax"
    ((levelNormalize (Level.mkIMax v u) == Level.mkIMax v u : Bool))
  ++ test "levelNormalize imax: offset re-added outside residual imax"
    ((levelNormalize (Level.mkSucc (Level.mkIMax u v))
        == Level.mkSucc (Level.mkIMax u v) : Bool))

def normalizeCorpus : List Level :=
  [zero, one, two, u, Level.mkSucc u,
   Level.mkMax v u, Level.mkMax u v,
   Level.mkMax u (Level.mkMax (Level.mkSucc u) v),
   Level.mkMax one (Level.mkSucc u), Level.mkMax two u, Level.mkMax u two,
   Level.mkSucc (Level.mkMax v u),
   Level.mkIMax u v, Level.mkIMax v u, Level.mkIMax u zero,
   Level.mkIMax zero u, Level.mkIMax one u, Level.mkIMax u (Level.mkSucc v),
   Level.mkIMax (Level.mkMax u v) (Level.mkIMax v u),
   Level.mkSucc (Level.mkIMax u v)]

def idempotenceTests : TestSeq :=
  test "levelNormalize is idempotent on the fixture corpus"
    ((normalizeCorpus.all fun l =>
        levelNormalize (levelNormalize l) == levelNormalize l : Bool))
  ++ test "levelNormalize is a no-op on cheap-normal levels"
    (([zero, two, u, Level.mkSucc u].all fun l =>
        levelNormalize l == l : Bool))

/-- Distinct MVars are `normLt`-incomparable (same `ctorToNat` slot), so
    the sorted output order is exactly the input order — this witnesses
    the STABLE sort (Rust `slice::sort_by`); an unstable sort could
    legally swap them. -/
def stableSortTests : TestSeq :=
  test "normalization preserves original order of tied (incomparable) mvars"
    ((let m1 := Level.mkMvar (nm "m1")
      let m2 := Level.mkMvar (nm "m2")
      levelNormalize (Level.mkMax m2 m1) == Level.mkMax m2 m1
      && levelNormalize (Level.mkMax m1 m2) == Level.mkMax m1 m2 : Bool))

def builderTests : TestSeq :=
  test "mkLevelSucc distributes over max/imax via levelMax, wraps otherwise"
    ((mkLevelSucc (Level.mkMax u v)
        == Level.mkMax (Level.mkSucc u) (Level.mkSucc v)
      && mkLevelSucc (Level.mkIMax u v)
        == Level.mkMax (Level.mkSucc u) (Level.mkSucc v)
      && mkLevelSucc u == Level.mkSucc u : Bool))
  ++ test "mkPProd builds PProd.{u,v} a b"
    ((let a := Expr.mkConst (nm "A") #[]
      let b := Expr.mkConst (nm "B") #[]
      mkPProd u v a b
        == Expr.mkApp (Expr.mkApp (Expr.mkConst (nm "PProd") #[u, v]) a) b : Bool))
  ++ test "punitConst / mkPUnitUnit / mkPProdMk name paths and spines"
    ((punitConst u == Expr.mkConst (nm "PUnit") #[u]
      && mkPUnitUnit u == Expr.mkConst (Name.mkStr (nm "PUnit") "unit") #[u]
      && (let a := Expr.mkConst (nm "A") #[]
          let b := Expr.mkConst (nm "B") #[]
          let x := Expr.mkConst (nm "x") #[]
          let y := Expr.mkConst (nm "y") #[]
          mkPProdMk u v a b x y
            == Expr.mkApp (Expr.mkApp (Expr.mkApp (Expr.mkApp
                 (Expr.mkConst (Name.mkStr (nm "PProd") "mk") #[u, v]) a) b) x) y)
      : Bool))
  ++ test "replaceResultSortWithProp rewrites the result sort only"
    ((let dom := Expr.mkConst (nm "A") #[]
      replaceResultSortWithProp
          (Expr.mkForallE (nm "x") dom (Expr.mkSort u) .default)
        == Expr.mkForallE (nm "x") dom (Expr.mkSort Level.mkZero) .default
      && replaceResultSortWithProp dom == dom : Bool))

public def suite : List TestSeq :=
  [levelMaxTests, normalizeMaxFixtureTests, normalizeImaxFixtureTests,
   idempotenceTests, stableSortTests, builderTests]

end Tests.AuxGen.Levels

end
