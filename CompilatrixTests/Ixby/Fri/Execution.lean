import CompilatrixTests.Ixby.Fri.Checking
import Compilatrix.Ixby.Inline.Image

namespace CompilatrixTests.Ixby.Fri

open Lean MultiStark.Verify Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend

private def ext (a b : Nat) : Ext := ⟨Ix.Ixby.Goldilocks.reduce a, Ix.Ixby.Goldilocks.reduce b⟩
private def encodeExt (value : Ext) : Ix.Ixby.Value := .scalar (.extField value)

private def ctor (image : Image) (name : Name) (fields : Array Ix.Ixby.Value := #[]) : IO Ix.Ixby.Value := do
  return .ctor (← checked (image.ctorId name)) fields

private def array (image : Image) (values : Array Ix.Ixby.Value) : IO Ix.Ixby.Value :=
  ctor image `Ixby.Runtime.Array #[.array values]

private def encodeOpenings (image : Image) : List Pcs.PointOpening → IO Ix.Ixby.Value
  | [] => ctor image ``List.nil
  | opening :: rest => do
    let value ← ctor image ``Pcs.PointOpening.mk
      #[encodeExt opening.point, ← array image (opening.values.map encodeExt)]
    ctor image ``List.cons #[value, ← encodeOpenings image rest]

private def encodeResult (image : Image) : Except MultiStark.Verify.Fri.Error (Ext × Ext) → IO Ix.Ixby.Value
  | .ok (power, value) => do
    ctor image ``Except.ok #[← ctor image ``Prod.mk #[encodeExt power, encodeExt value]]
  | .error error => do
    let value ← match error with
      | .width => ctor image ``MultiStark.Verify.Fri.Error.width
      | .arithmetic .zeroDenominator => do
        ctor image ``MultiStark.Verify.Fri.Error.arithmetic
          #[← ctor image ``Arithmetic.Error.zeroDenominator]
      | _ => throw (IO.userError s!"unexpected FRI oracle error: {reprStr error}")
    ctor image ``Except.error #[value]

private def compare (images : Array Image) (alpha x : Ext) (width : Nat) (row : Array Field)
    (openings : List Pcs.PointOpening) (power value : Ext) : IO Unit := do
  let expected := MultiStark.Verify.Fri.reducePoints alpha x width row openings power value
  for image in images do
    let args := #[encodeExt alpha, encodeExt x, .scalar (.nat width),
      ← array image (row.map fun field => .scalar (.nat field.val)),
      ← encodeOpenings image openings, encodeExt power, encodeExt value]
    let actual := Ix.Ixby.execute image.state.limits image.program args 2000000
    let chunked := Compilatrix.Ixby.Runtime.Chunked.execute image.state.limits image.program args 2000000
    need (Native.same actual chunked) "FRI chunked/reference disagreement"
    need (Native.same actual (.ok (← encodeResult image expected)))
      s!"FRI source/image mismatch: width={width}, row={row.size}, openings={openings.length}"

def execution (env : Environment) : IO Unit := do
  let original ← compileImage env ``MultiStark.Verify.Fri.reducePoints
  let fused ← compileImage env ``MultiStark.Verify.Fri.reducePoints
    #[``Compilatrix.Ixby.Stage2.Fri.reducePoints_eq]
  need (fused.state.sourceReplacementRejection.isNone && fused.state.sourceReplacements.size == 1)
    "FRI equality did not select fusion"
  need (fused.state.functionNames[`Compilatrix.Ixby.Stage2.Fri.reduceLoop._redArg]?.isSome)
    "fused loop was not compiled"
  need (!(fused.state.functionNames.contains ``MultiStark.Verify.Fri.reduceCoordinatePairs))
    "fused image still compiles the list fold"
  let inlined ← checked (Compilatrix.Ixby.Inline.optimizeImage fused { protectedPrefix := 110 })
  discard <| checked inlined.image.certifyWireRuntime
  let images := #[original, fused, inlined.image]
  let x := ext 17 23
  let point := ext 31 41
  let second := ext 43 47
  let mut count := 0
  for width in #[0, 1, 2, 3, 8, 33, 64] do
    let row := (Array.range width).map fun i => Ix.Ixby.Goldilocks.reduce (i * 7919 + 19)
    let opened := (Array.range width).map fun i => ext (i * 53 + 29) (i * 97 + 31)
    for alpha in #[ext 0 0, ext 1 0, ext 7 11] do
      for (power, value) in #[(ext 1 0, ext 0 0), (ext 13 17, ext 19 23)] do
        for (declared, openings) in #[
            (width, []), (width + 1, []),
            (width, [⟨point, opened⟩]),
            (width, [⟨point, opened⟩, ⟨second, opened.reverse⟩]),
            (width + 1, [⟨x, opened⟩]),
            (width, [⟨x, opened⟩]),
            (width, [⟨point, opened.push (ext 0 0)⟩]),
            (width, [⟨point, opened⟩, ⟨x, opened⟩]),
            (width, [⟨point, opened⟩, ⟨x, opened.push (ext 0 0)⟩]),
            (2 ^ 80, [⟨point, opened⟩])] do
          compare images alpha x declared row openings power value
          count := count + 1
  IO.println s!"FRI execution: {count} source cases across original, fused and inlined images; reference/chunked agreement"

end CompilatrixTests.Ixby.Fri
