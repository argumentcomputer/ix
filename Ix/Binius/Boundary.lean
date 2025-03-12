import Ix.Binius.Common
import Ix.Unsigned

namespace Binius

structure Boundary where
  values : Array UInt128
  channelId : ChannelId
  direction : FlushDirection
  multiplicity : UInt64

namespace Boundary

def toString (boundary : @& Boundary) : String :=
  let numValues := boundary.values.size
  let channelId := boundary.channelId.toUSize
  s!"⟨{numValues}, {channelId}, {boundary.direction}, {boundary.multiplicity}⟩"

def toBytes (boundary : @& Boundary) : ByteArray :=
  let numValues := boundary.values.size
  let valuesBytes := boundary.values.foldl (init := .mkEmpty (16 * numValues))
    fun acc u128 => acc ++ u128.toLEBytes
  let channelBytes := boundary.channelId.toUSize.toLEBytes
  let directionByte := match boundary.direction with | .push => 0 | .pull => 1
  numValues.toUSize.toLEBytes ++ valuesBytes ++ channelBytes ++
    ⟨#[directionByte]⟩ ++ boundary.multiplicity.toLEBytes

/--
Function meant for testing that tells whether the Lean→Rust mapping of Boundary
results on the same boundary as deserializing the provided bytes.
-/
@[extern "rs_binius_boundary_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& Boundary → @& ByteArray → Bool

end Boundary

end Binius
