/-! Src admission diagnostics (design note 01 §10 part 5): one root per
expected `Src.Admit` outcome. Compiled by `lake exe pin-src-tables
--diagnostics`; see `README.md`. -/

namespace SrcDiag

/-- A `partial def` is an opaque with a placeholder value: rejected as
`opaque` (no hint marks it `partial`). -/
partial def spin (n : Nat) : Nat := spin (n + 1)

def rootPartial (n : Nat) : Nat := spin n

/-- An `@[extern]` opaque (`mixHash`) in a relevant position: `opaque`. -/
def rootMixHash (n : Nat) : UInt64 := mixHash n.toUInt64 7

/-- In Lean 4.34 `Float.add` is an `@[extern]` *definition* with a logical
model (`Float.Model`), not an opaque: admitted, and SrcEval runs the model. -/
def rootFloat (n : Nat) : Float := Float.ofNat n + 1.5

/-- `Classical.propDecidable` in a relevant `if`: its body reaches
`Classical.choice`, a `relevant-axiom`. -/
noncomputable def rootClassical (n : Nat) : Nat :=
  @ite Nat (n = n) (Classical.propDecidable (n = n)) 1 0

/-- The `sorry` axiom `sorryAx` (named directly): `relevant-axiom`. -/
def rootSorry (n : Nat) : Nat := n + sorryAx Nat false

/-- `Lean.opaqueId` is on the opaque-by-value allowlist: admitted. -/
def rootOpaqueId (n : Nat) : Nat := Lean.opaqueId (n + 1)

end SrcDiag
