import Ix.Archon.OracleIdx
import Ix.Archon.TowerField
import Ix.Unsigned

namespace Archon

inductive OracleOrConst
  | oracle : OracleIdx → OracleOrConst
  | const : UInt128 → TowerField → OracleOrConst
  deriving Inhabited

namespace OracleOrConst

def toString : OracleOrConst → String
  | oracle o => s!"Oracle({o.toUSize})"
  | const base tf => s!"Const({base}, {tf})"

instance : ToString OracleOrConst := ⟨toString⟩

def toBytes : @& OracleOrConst → ByteArray
  | oracle o => ⟨#[0]⟩ ++ o.toUSize.toLEBytes
  | const base tf => ⟨#[1]⟩ ++ base.toLEBytes |>.push tf.logDegree.toUInt8

/--
Function meant for testing that tells whether the Lean→Rust mapping of OracleOrConst
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_oracle_or_const_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& OracleOrConst → @& ByteArray → Bool

end OracleOrConst

end Archon
