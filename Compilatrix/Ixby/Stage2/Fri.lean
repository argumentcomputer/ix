import Ix.MultiStark.Verify.Fri.Inputs

/-! A source-level specialization of the pinned FRI point reduction. The
equivalence proofs live in `FriSound`; the vendored source stays unchanged. -/

namespace Compilatrix.Ixby.Stage2.Fri

open MultiStark.Verify

/-- Traverse matching arrays once, carrying the two accumulators separately.
The size proof is erased; each coordinate is read in its original order. -/
def reduceLoop (alpha reciprocal : Ext) (row : Array Field) (opened : Array Ext)
    (sizes : row.size = opened.size) (index : Nat) (power value : Ext) : Ext × Ext :=
  if inside : index < row.size then
    let difference := (opened[index]'(by omega)).sub (Arithmetic.embed row[index])
    reduceLoop alpha reciprocal row opened sizes (index + 1)
      (power.mul alpha)
      (value.add (power.mul (difference.mul reciprocal)))
  else (power, value)
termination_by row.size - index

/-- The coordinate guard compares array sizes directly, without materializing
or measuring either source list. -/
def reduceCoordinates (alpha reciprocal : Ext) (row : Array Field) (opened : Array Ext)
    (power value : Ext) : Except MultiStark.Verify.Fri.Error (Ext × Ext) :=
  if sizes : row.size = opened.size then
    .ok (reduceLoop alpha reciprocal row opened sizes 0 power value)
  else .error .width

/-- The width and reciprocal checks retain the source order, including empty
rows and the first failing point. Only coordinate collection processing changes. -/
def reducePoints (alpha x : Ext) (width : Nat) (row : Array Field) :
    List Pcs.PointOpening → Ext → Ext → Except MultiStark.Verify.Fri.Error (Ext × Ext)
  | [], power, value => .ok (power, value)
  | opening :: openings, power, value => do
    ensure (row.size == width && row.size == opening.values.size) .width
    let reciprocal ← (Arithmetic.inverse (opening.point.sub x)).mapError
      MultiStark.Verify.Fri.Error.arithmetic
    let (power, value) ← reduceCoordinates alpha reciprocal row opening.values power value
    reducePoints alpha x width row openings power value

end Compilatrix.Ixby.Stage2.Fri
