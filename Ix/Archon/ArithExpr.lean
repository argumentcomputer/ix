import Ix.Archon.OracleIdx
import Ix.Unsigned

namespace Archon

/-- Arithmetic expression type for BinaryField128b -/
inductive ArithExpr
  | const : UInt128 → ArithExpr
  | var : USize → ArithExpr
  | oracle : OracleIdx → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
  | pow : ArithExpr → UInt64 → ArithExpr
  deriving Inhabited, Ord

instance : Add ArithExpr := ⟨.add⟩
instance : Sub ArithExpr := ⟨.add⟩
instance : Mul ArithExpr := ⟨.mul⟩
instance : HPow ArithExpr UInt64 ArithExpr where
  hPow x e := .pow x e

instance : Zero ArithExpr := ⟨.const 0⟩

instance : Coe OracleIdx ArithExpr := ⟨.oracle⟩

namespace ArithExpr

@[inline] def zero : ArithExpr := Zero.zero
@[inline] def one : ArithExpr := .const 1

def toString : ArithExpr → String
  | const c => s!"Const({c})"
  | var v => s!"Var({v})"
  | oracle o => s!"Oracle({o.toUSize})"
  | add x y => s!"Add({x.toString}, {y.toString})"
  | mul x y => s!"Mul({x.toString}, {y.toString})"
  | pow x e => s!"Pow({x.toString}, {e})"

instance : ToString ArithExpr := ⟨toString⟩

def toBytes : @& ArithExpr → ByteArray
  | const u128 => ⟨#[0]⟩ ++ u128.toLEBytes
  | var v => ⟨#[1]⟩ ++ v.toLEBytes
  | oracle o => ⟨#[2]⟩ ++ o.toUSize.toLEBytes
  | add x y =>
    let xBytes := x.toBytes
    ⟨#[3, xBytes.size.toUInt8]⟩ ++ xBytes ++ y.toBytes
  | mul x y =>
    let xBytes := x.toBytes
    ⟨#[4, xBytes.size.toUInt8]⟩ ++ xBytes ++ y.toBytes
  | pow x e => ⟨#[5]⟩ ++ x.toBytes ++ e.toLEBytes

/--
Function meant for testing that tells whether the Lean→Rust mapping of ArithExpr
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_arith_expr_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& ArithExpr → @& ByteArray → Bool

end ArithExpr

end Archon
