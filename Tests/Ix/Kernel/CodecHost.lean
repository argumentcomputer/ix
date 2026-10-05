import Tests.Ix.Ixon
import IxC.Ixon.Canonical
import IxC.Ixon.Bounded.Size

/-! Host-only production codec regressions, including generated values and
Rust serialization comparisons. This runner is outside the certified closure. -/

open LSpec SlimCheck Ixon

def boundedUnivMatchesRust (value : Univ) : Bool :=
  let bytes := serUniv value
  match Bounded.deUniv bytes.size value.nodeCount bytes with
  | .error _ => false
  | .ok decoded =>
    decoded == value && Tests.FFI.Ixon.rsEqUnivSerialization decoded bytes &&
      !(Bounded.deUniv bytes.size (value.nodeCount - 1) bytes).isOk &&
      !(Bounded.deUniv (bytes.size - 1) value.nodeCount bytes).isOk

def boundedConstantMatchesRust (value : Constant) : Bool :=
  let bytes := serConstant value
  let nodes := Bounded.univNodes value.univs
  match Bounded.deConstant bytes.size nodes bytes with
  | .error _ => false
  | .ok decoded =>
    decoded == value && Tests.FFI.Ixon.rsEqConstantSerialization decoded bytes &&
      decoded.resourceSize + Bounded.univNodes decoded.univs ≤ 2 * bytes.size + nodes &&
      !(Bounded.deConstant (bytes.size - 1) nodes bytes).isOk &&
      (nodes == 0 || !(Bounded.deConstant bytes.size (nodes - 1) bytes).isOk)

def canonicalConstantMatchesRust (value : Constant) : Bool :=
  let bytes := serConstant value
  match Canonical.deConstant bytes.size (Bounded.univNodes value.univs) bytes with
  | .error _ => false
  | .ok decoded => decoded == value && Tests.FFI.Ixon.rsEqConstantSerialization decoded bytes

def resourceExprMatchesRust (value : Expr) : Bool :=
  let payload := serExpr value
  let bytes := (⟨#[0xff, 0xee]⟩ : ByteArray) ++ payload ++ ⟨#[0xdd]⟩
  match getExpr { bytes, idx := 2 } with
  | .error _ _ => false
  | .ok decoded finish =>
    decoded == value && finish.bytes == bytes && finish.idx == 2 + payload.size &&
      decoded.resourceSize + 1 ≤ 2 * (finish.idx - 2) &&
      Tests.FFI.Ixon.rsEqExprSerialization decoded payload

def main : IO UInt32 :=
  LSpec.lspecIO (.ofList [
    ("certified-codec-production", Tests.Ixon.suite),
    ("bounded-universe", [checkIO "exact limits and Rust serialization"
      (∀ value : Univ, boundedUnivMatchesRust value)]),
    ("bounded-constant", [checkIO "aggregate limits and Rust serialization"
      (∀ value : Constant, boundedConstantMatchesRust value)]),
    ("canonical-constant", [checkIO "canonical round trips and Rust serialization"
      (∀ value : Constant, canonicalConstantMatchesRust value)]),
    ("expression-resources", [checkIO "consumed-byte bounds, nonzero cursor, and Rust serialization"
      (∀ value : Expr, resourceExprMatchesRust value)])]) []
