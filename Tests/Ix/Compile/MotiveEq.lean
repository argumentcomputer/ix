import LSpec
import Ix.Compile.Image.MotiveEq

namespace Tests.Ix.Compile.MotiveEq

open LSpec
open _root_.Ix (Name Level Expr)
open _root_.Ix.Compile.Image (alphaEq motiveEq)

private def addr (n : UInt8) : Address := ⟨⟨Array.replicate 32 n⟩⟩

/-- Compare motives without erasing distinctions in names, parameter positions,
array arities or metadata placement. Canonical universe identities are tested
beside unequal and unresolved neighbours; raw alpha equality stays separate. -/
def controls : List (String × Array Name × Expr × Expr × Bool × Bool) :=
  let h := addr 0
  let root : Name := .anonymous h
  let u : Name := .str root "u" h
  let v : Name := .str root "v" h
  let symbol : Name := .str root "F" h
  let zero : Level := .zero h
  let one : Level := .succ zero h
  let p : Level := .param u h
  let q : Level := .param v h
  let max00 : Level := .max zero zero h
  let sort := fun l => Expr.sort l h
  let cnst := fun us => Expr.const symbol us h
  let params := #[u, v]
  [
    ("zero-max00", #[], sort zero, sort max00, true, false),
    ("commuting-parameters", params, sort (.max p q h), sort (.max q p h), true, false),
    ("idempotent-max", params, sort (.max p p h), sort p, true, false),
    ("imax-zero", params, sort (.imax p zero h), sort zero, true, false),
    ("imax-is-not-max", params, sort (.imax p q h), sort (.max p q h), false, false),
    ("unequal-constants", #[], sort zero, sort one, false, false),
    ("distinct-parameters-with-colliding-caches", params, sort p, sort q, false, false),
    ("unknown-exact-parameter", #[], sort p, sort p, true, true),
    ("unknown-semantic-alias", #[], sort p, sort (.max p zero h), false, false),
    ("unknown-metavariable", params, sort (.mvar u h), sort zero, false, false),
    ("constant-universe-alias", #[], cnst #[max00], cnst #[zero], true, false),
    ("constant-universe-count", params, cnst #[p], cnst #[p, q], false, false),
    ("constant-universe-order", params, cnst #[p, q], cnst #[q, p], false, false),
    ("constant-name-collision", #[], cnst #[zero], .const u #[zero] h, false, false),
    ("paired-metadata", #[], .mdata #[] (sort max00) h, .mdata #[] (sort zero) h, true, false),
    ("one-sided-metadata", #[], .mdata #[] (sort max00) h, sort zero, false, false)
  ]

def suite : List TestSeq := controls.flatMap fun (label, params, left, right, expected, raw) =>
  [test s!"image motive: {label}" (motiveEq params left right == expected),
   test s!"image motive retains raw alpha: {label}" (alphaEq left right == raw)]

end Tests.Ix.Compile.MotiveEq
