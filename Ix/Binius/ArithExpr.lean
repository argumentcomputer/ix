import Ix.UInt128
import Ix.UInt64
import Ix.USize

namespace Binius

inductive ArithExpr
  | const : UInt128 → ArithExpr
  | var : USize → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
  | pow : ArithExpr → UInt64 → ArithExpr
  deriving Inhabited

namespace ArithExpr

def toString : ArithExpr → String
  | const _ => "Const"
  | var v => s!"Var({v})"
  | add x y => s!"Add({x.toString}, {y.toString})"
  | mul x y => s!"Mul({x.toString}, {y.toString})"
  | pow x e => s!"Pow({x.toString}, {e})"

def toBytes : @& ArithExpr → ByteArray
  | const u128 => ⟨#[0]⟩ ++ u128.toLEBytes
  | var usize => ⟨#[1]⟩ ++ usize.toLEBytes
  | add x y =>
    let xBytes := x.toBytes
    ⟨#[2, xBytes.size.toUInt8]⟩ ++ xBytes ++ y.toBytes
  | mul x y =>
    let xBytes := x.toBytes
    ⟨#[3, xBytes.size.toUInt8]⟩ ++ xBytes ++ y.toBytes
  | pow x e => ⟨#[4]⟩ ++ x.toBytes ++ e.toLEBytes

/--
Function meant for testing that tells whether the Lean→Rust mapping of ArithExpr
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_binius_arith_expr_is_equivalent"]
opaque isEquivalentToBytes : @& ArithExpr → @& ByteArray → Bool

end ArithExpr

end Binius
