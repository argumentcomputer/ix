module
public import Ix.MultiStark.Verify.Codec.Wire
public import Ix.Ixby.Blake3

/-! Binary BLAKE3 MMCS for the power-of-two matrix heights used by Stage 2.
Dimensions and query indices are verifier-owned. Matrix boundaries are not
encoded in a leaf hash, so checking every row width is a security condition.
This module does not claim support for arbitrary-height or N-ary MMCS. -/

public section
@[expose] section

namespace MultiStark.Verify.Mmcs

structure Dimension where
  logHeight : Nat
  width : Nat
  deriving BEq, DecidableEq, Repr

inductive Error where
  | emptyMatrices | height | capShape | unboundMatrix
  | queryCount | matrixCount | rowWidth | index
  | duplicateRow | groupRow | frontier | capMismatch | internalShape
  deriving BEq, DecidableEq, Repr, Inhabited

def hashBytes (bytes : Bytes) : Digest :=
  ⟨Ix.Ixby.Blake3.hash bytes, Ix.Ixby.Blake3.hash_size bytes⟩

/-- Canonical u64 little-endian words, concatenated without lengths or tags. -/
def hashRow (values : Array Field) : Digest :=
  hashBytes (values.flatMap fun value => Codec.Wire.littleEndian 8 value.val)

def compress (left right : Digest) : Digest := hashBytes (left.bytes ++ right.bytes)

def getAt {α : Type} (values : Array α) (index : Nat) : Except Error α :=
  match values[index]? with | some value => .ok value | none => .error .internalShape

def maxLogHeight (dimensions : Array Dimension) : Nat :=
  dimensions.foldl (fun height dim => max height dim.logHeight) 0

/-- The supported class never cuts off an injection layer above the cap.
Without this condition a shorter matrix's rows would not be authenticated by
the cap walk. It is an explicit admission restriction, not a claim that the
native generic MMCS imposes the same check. Small single-height FRI trees
still shorten an oversized configured cap exactly as the native builder does. -/
def geometry (capHeight : Nat) (dimensions : Array Dimension) (cap : MerkleCap) :
    Except Error (Nat × Nat) := do
  ensure (!dimensions.isEmpty) .emptyMatrices
  ensure (dimensions.all (·.logHeight ≤ 32)) .height
  let height := maxLogHeight dimensions
  let effectiveCap := min capHeight height
  ensure (cap.size == 2 ^ effectiveCap) .capShape
  ensure (dimensions.all (effectiveCap ≤ ·.logHeight)) .unboundMatrix
  return (height, effectiveCap)

end MultiStark.Verify.Mmcs
