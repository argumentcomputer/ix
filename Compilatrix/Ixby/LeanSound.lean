import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.ScalarCertificate

/-! The first typed-frontend proof boundary: exact number decoding and checked
execution of seven native extension helpers from the actual compiled image.
This does not certify Lean proof erasure or the general LCNF lowering. -/

namespace Compilatrix.Ixby.LeanFrontend

open Lean Ix.Ixby _root_.Compilatrix.Ixby.Runtime
open _root_.Compilatrix.Ixby.Runtime.Representation

def Image.HasNumberLayout (image : Image) (layout : NumberLayout) : Prop :=
  image.ctorId `Ixby.Runtime.Number = .ok layout.cached ∧
  image.ctorId `Ixby.Runtime.RawNumber = .ok layout.raw ∧
  image.ctorId `Ixby.Runtime.FieldNumber = .ok layout.field

structure Image.NumberLayoutWitness (image : Image) where
  layout : NumberLayout
  layouts : image.HasNumberLayout layout

def Image.certifyNumberLayout (image : Image) : Except String image.NumberLayoutWitness := do
  match cached : image.ctorId `Ixby.Runtime.Number with
  | .error message => throw message
  | .ok cachedId =>
    match raw : image.ctorId `Ixby.Runtime.RawNumber with
    | .error message => throw message
    | .ok rawId =>
      match field : image.ctorId `Ixby.Runtime.FieldNumber with
      | .error message => throw message
      | .ok fieldId => return {
          layout := ⟨cachedId, rawId, fieldId⟩
          layouts := ⟨cached, raw, field⟩ }

theorem Image.decodeNumber_represents {image : Image} {layout : NumberLayout}
    (layouts : image.HasNumberLayout layout) {n : Nat} {value : Value}
    (represented : Number layout n value) : image.decodeNumber value = .ok n := by
  cases represented with
  | cached n =>
    change (do
      unless layout.cached == (← image.ctorId `Ixby.Runtime.Number) && n.toUInt32 == n.toUInt32 do
        throw "typed Ixby output number invariant failed"
      return n : Except String Nat) = .ok n
    simp [layouts.1, bind, Except.bind, pure, Except.pure]
  | raw n =>
    change (do
      unless layout.raw == (← image.ctorId `Ixby.Runtime.RawNumber) do
        throw "typed Ixby raw number layout failed"
      return n : Except String Nat) = .ok n
    simp [layouts.2.1, bind, Except.bind, pure, Except.pure]
  | field f =>
    change (do
      unless layout.field == (← image.ctorId `Ixby.Runtime.FieldNumber) do
        throw "typed Ixby field number layout failed"
      return f.val : Except String Nat) = .ok f.val
    simp [layouts.2.2, bind, Except.bind, pure, Except.pure]

theorem Image.number_represents {image : Image} {layout : NumberLayout}
    (layouts : image.HasNumberLayout layout) (n : Nat) :
    ∃ value, image.number n = .ok value ∧ Number layout n value := by
  exact ⟨_, by simp [Image.number, layouts.1, bind, Except.bind, pure, Except.pure], .cached n⟩

theorem Image.number_decode_roundtrip {image : Image} {layout : NumberLayout}
    (layouts : image.HasNumberLayout layout) (n : Nat) :
    (image.number n).bind image.decodeNumber = .ok n := by
  obtain ⟨value, encoded, represented⟩ := image.number_represents layouts n
  rw [encoded]
  exact image.decodeNumber_represents layouts represented

theorem Image.number_representation_unique {image : Image} {layout : NumberLayout}
    (layouts : image.HasNumberLayout layout) {a b : Nat} {value : Value}
    (left : Number layout a value) (right : Number layout b value) : a = b := by
  have h := (image.decodeNumber_represents layouts left).symm.trans
    (image.decodeNumber_represents layouts right)
  exact Except.ok.inj h

theorem Image.decodeNumber_rejects_bad_cache {image : Image} {layout : NumberLayout}
    (layouts : image.HasNumberLayout layout) (n : Nat) (word : UInt32)
    (bad : word ≠ n.toUInt32) :
    image.decodeNumber (.ctor layout.cached #[.scalar (.nat n), .scalar (.word32 word)]) =
      .error "typed Ixby output number invariant failed" := by
  change (do
    unless layout.cached == (← image.ctorId `Ixby.Runtime.Number) && word == n.toUInt32 do
      throw "typed Ixby output number invariant failed"
    return n : Except String Nat) = _
  simp [layouts.1, bad, bind, Except.bind, pure, Except.pure] <;> rfl

/-- Names are used only to locate candidates. `certifyScalars` then checks
their complete code and projection layout against the executable contracts. -/
def Image.scalarLinks (image : Image) : Except String ScalarLinks := do
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing scalar runtime name {name}"
  let some fieldBox := image.state.constructorNames[`Ixby.Runtime.FieldNumber]? |
    throw "missing scalar runtime field constructor"
  let field ← (image.program.getConstructor fieldBox).mapError reprStr
  return {
    add := ← function `Ix.Ixby.ExtGoldilocks.add
    sub := ← function `Ix.Ixby.ExtGoldilocks.sub
    mul := ← function `Ix.Ixby.ExtGoldilocks.mul
    inverse := ← function `Ix.Ixby.ExtGoldilocks.inverse
    equal := ← function `Ix.Ixby.instBEqExtGoldilocks.beq
    first := ← function `Ixby.Runtime.extFirst
    second := ← function `Ixby.Runtime.extSecond
    fieldBox, fieldId := field.id }

structure Image.ScalarCertified (image : Image) where
  links : ScalarLinks
  names : image.scalarLinks = .ok links
  certificate : ScalarCertificate image.program links

def Image.certifyScalars (image : Image) : Except String image.ScalarCertified := do
  match names : image.scalarLinks with
  | .error message => throw message
  | .ok links => return { links, names, certificate := ← Runtime.certifyScalars image.program links }

end Compilatrix.Ixby.LeanFrontend
