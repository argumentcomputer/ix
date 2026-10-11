import LSpec
import Ix.Compile.Image.Expr

namespace Tests.Ix.Compile.AlphaEq

open LSpec
open _root_.Ix (Expr Name Level)
open _root_.Ix.Compile.Image (alphaEq)

private def addr (n : UInt8) : Address := ⟨⟨Array.replicate 32 n⟩⟩

/-- The labels and constructor cases are mirrored in Rust's alpha_eq_tests.
These are arbitrary raw inputs; no collision resistance or source WF is assumed. -/
def controls : List (String × Expr × Expr × Bool) :=
  let h := addr 0
  let a := addr 1
  let b := addr 2
  let n : Name := .anonymous h
  let m : Name := .str n "different" h
  let na : Name := .str (.anonymous a) "same" h
  let nb : Name := .str (.anonymous b) "same" h
  let z : Level := .zero h
  let s : Level := .succ z h
  let za : Level := .succ (.zero a) h
  let zb : Level := .succ (.zero b) h
  let t : Expr := .sort z h
  let x : Expr := .bvar 0 a
  let y : Expr := .bvar 0 b
  [
    ("identical-bvar", .bvar 0 h, .bvar 0 h, true),
    ("expression-hash-collision", .bvar 0 h, .bvar 1 h, false),
    ("expression-cache-ignored", x, y, true),
    ("constructor-hash-collision", .bvar 0 h, t, false),
    ("fvar-name-collision", .fvar n a, .fvar m b, false),
    ("mvar-name-collision", .mvar n a, .mvar m b, false),
    ("sort-level-collision", .sort z a, .sort s b, false),
    ("constant-name-collision", .const n #[] a, .const m #[] b, false),
    ("constant-level-collision", .const n #[z] a, .const n #[s] b, false),
    ("constant-level-count", .const n #[] a, .const n #[z] b, false),
    ("projection-name-collision", .proj n 0 x a, .proj m 0 y b, false),
    ("nested-name-cache-retained", .fvar na a, .fvar nb b, false),
    ("nested-level-cache-retained", .sort za a, .sort zb b, false),
    ("level-param-name-cache-retained", .sort (.param na h) a, .sort (.param nb h) b, false),
    ("level-max-child-collision", .sort (.max z z h) a, .sort (.max z s h) b, false),
    ("constant-nested-level-cache", .const n #[za] a, .const n #[zb] b, false),
    ("lambda-binder-neighbour", .lam n t x .default a, .lam m t y .implicit b, true),
    ("forall-binder-neighbour", .forallE n t x .default a, .forallE m t y .instImplicit b, true),
    ("let-flag-neighbour", .letE n t x x false a, .letE m t y y true b, true),
    ("paired-metadata-neighbour", .mdata #[(n, .ofNat 0)] x a, .mdata #[(m, .ofBool true)] y b, true),
    ("one-sided-metadata-left", .mdata #[] x h, x, false),
    ("one-sided-metadata-right", x, .mdata #[] x h, false),
    ("metadata-child-collision", .mdata #[] (.bvar 0 h) a, .mdata #[] (.bvar 1 h) b, false),
    ("projection-index", .proj n 0 x a, .proj n 1 y b, false),
    ("equal-literal-neighbour", .lit (.natVal 0) a, .lit (.natVal 0) b, true),
    ("different-literal", .lit (.natVal 0) a, .lit (.natVal 1) b, false),
    ("literal-constructor", .lit (.natVal 0) a, .lit (.strVal "0") b, false),
    ("equal-constant-neighbour", .const n #[z] a, .const n #[z] b, true),
    ("universe-order", .const n #[z, s] a, .const n #[s, z] b, false),
    ("sibling-memo-collision", .app x (.bvar 1 a) (addr 3), .app y (.bvar 2 b) (addr 4), false),
    ("repeated-pair-neighbour", .app x x (addr 3), .app y y (addr 4), true),
    ("false-child-neighbour", .app x x (addr 3), .app (.bvar 1 b) y (addr 4), false),
    ("equal-fvar-neighbour", .fvar n a, .fvar n b, true),
    ("smart-lambda-neighbour",
      Expr.mkLam (Name.fromLeanName `x) (Expr.mkSort Level.mkZero) (Expr.mkBVar 0) .default,
      Expr.mkLam (Name.fromLeanName `y) (Expr.mkSort Level.mkZero) (Expr.mkBVar 0) .implicit, true),
    ("smart-constant-neighbour", Expr.mkConst (Name.fromLeanName `Nat) #[],
      Expr.mkConst (Name.fromLeanName `Nat) #[], true)
  ]

def suite : List TestSeq := controls.map fun (label, a, b, expected) =>
  test s!"image alpha: {label}" (alphaEq a b == expected)

end Tests.Ix.Compile.AlphaEq
