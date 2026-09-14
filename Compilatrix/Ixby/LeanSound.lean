import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.ScalarCertificate
import Compilatrix.Ixby.Runtime.NumberConversion
import Compilatrix.Ixby.Runtime.NatArithmetic
import Compilatrix.Ixby.Runtime.FieldArithmetic
import Compilatrix.Ixby.Runtime.NatLoops
import Compilatrix.Ixby.Runtime.Words
import Compilatrix.Ixby.Runtime.ArrayTrees

/-! Typed-frontend proof boundaries: exact number decoding and checked
execution of all emitted field helpers, complete number conversions, and Nat
arithmetic, comparisons, and recursive shift, logarithm, and power helpers.
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

structure Image.ConversionCandidates (image : Image) where
  links : Conversion.Links
  layouts : image.HasNumberLayout links.layout

/-- Source names locate all call and constructor indices. The layout witness
is retained for the image's own decoder; the certificate subsequently checks
every complete function and constructor declaration in the actual program. -/
def Image.conversionCandidates (image : Image) : Except String image.ConversionCandidates := do
  let layout ← image.certifyNumberLayout
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing conversion runtime name {name}"
  let constructor (name : Name) : Except String Nat :=
    match image.state.constructorNames[name]? with
    | some id => .ok id
    | none => .error s!"missing conversion constructor name {name}"
  let links : Conversion.Links := {
    toWord := ← function `Ixby.Runtime.toWord
    fromWordLoop := ← function `Ixby.Runtime.fromWordLoop
    fromWord := ← function `Ixby.Runtime.fromWord
    fromRaw := ← function `Ixby.Runtime.fromRaw
    lowWord := ← function `Ixby.Runtime.lowWord
    natural := ← function `Ixby.Runtime.natural
    fieldNatural := ← function `Ixby.Runtime.fieldNatural
    asField := ← function `Ixby.Runtime.asField
    fieldFromNatural := ← function `Ixby.Runtime.fieldFromNatural
    nibbleWord := ← function `Ixby.Runtime.nibbleWord
    nibbleNat := ← function `Ixby.Runtime.nibbleNat
    cachedCtor := ← constructor `Ixby.Runtime.Number
    rawCtor := ← constructor `Ixby.Runtime.RawNumber
    fieldCtor := ← constructor `Ixby.Runtime.FieldNumber
    layout := layout.layout }
  return { links, layouts := layout.layouts }

structure Image.ConversionCertified (image : Image) where
  candidates : image.ConversionCandidates
  names : image.conversionCandidates = .ok candidates
  certificate : Conversion.Certificate image.program candidates.links

def Image.ConversionCertified.links {image : Image} (certified : image.ConversionCertified) :
    Conversion.Links := certified.candidates.links

theorem Image.ConversionCertified.layouts {image : Image} (certified : image.ConversionCertified) :
    image.HasNumberLayout certified.links.layout := certified.candidates.layouts

def Image.certifyConversions (image : Image) : Except String image.ConversionCertified := do
  match names : image.conversionCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← Conversion.certify image.program candidates.links }

structure Image.NatArithmeticCandidates (image : Image) where
  links : NatArithmetic.Links
  layouts : image.HasNumberLayout links.conversions.layout

def Image.natArithmeticCandidates (image : Image) : Except String image.NatArithmeticCandidates := do
  let conversions ← image.conversionCandidates
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing Nat arithmetic runtime name {name}"
  let links : NatArithmetic.Links := {
    conversions := conversions.links
    add := ← function `Nat.add
    sub := ← function `Nat.sub
    mul := ← function `Nat.mul
    div := ← function `Nat.div
    mod := ← function `Nat.mod
    equal := ← function `Nat.decEq
    less := ← function `Nat.decLt
    lessEqual := ← function `Nat.decLe }
  return { links, layouts := conversions.layouts }

structure Image.NatArithmeticCertified (image : Image) where
  candidates : image.NatArithmeticCandidates
  names : image.natArithmeticCandidates = .ok candidates
  certificate : NatArithmetic.Certificate image.program candidates.links

def Image.NatArithmeticCertified.links {image : Image} (certified : image.NatArithmeticCertified) :
    NatArithmetic.Links := certified.candidates.links

theorem Image.NatArithmeticCertified.layouts {image : Image} (certified : image.NatArithmeticCertified) :
    image.HasNumberLayout certified.links.conversions.layout := certified.candidates.layouts

/-- Check all eight arithmetic/comparison bodies together with their conversion callees,
constructor declarations, distinct tags, and image name bindings. -/
def Image.certifyNatArithmetic (image : Image) : Except String image.NatArithmeticCertified := do
  match names : image.natArithmeticCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← NatArithmetic.certify image.program candidates.links }

structure Image.FieldCandidates (image : Image) where
  links : FieldArithmetic.Links
  layouts : image.HasNumberLayout links.conversions.layout

def Image.fieldCandidates (image : Image) : Except String image.FieldCandidates := do
  let conversions ← image.conversionCandidates
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing field runtime name {name}"
  let links : FieldArithmetic.Links := {
    conversions := conversions.links
    reduce := ← function `Ix.Ixby.Goldilocks.reduce
    add := ← function `Ix.Ixby.Goldilocks.add
    sub := ← function `Ix.Ixby.Goldilocks.sub
    mul := ← function `Ix.Ixby.Goldilocks.mul
    neg := ← function `Ix.Ixby.Goldilocks.neg
    inverse := ← function `Ix.Ixby.Goldilocks.inverse
    pack := ← function `Ix.Ixby.ExtGoldilocks.mk }
  return { links, layouts := conversions.layouts }

structure Image.FieldCertified (image : Image) where
  candidates : image.FieldCandidates
  names : image.fieldCandidates = .ok candidates
  certificate : FieldArithmetic.Certificate image.program candidates.links

def Image.FieldCertified.links {image : Image} (certified : image.FieldCertified) :
    FieldArithmetic.Links := certified.candidates.links

theorem Image.FieldCertified.layouts {image : Image} (certified : image.FieldCertified) :
    image.HasNumberLayout certified.links.conversions.layout := certified.candidates.layouts

/-- Check the six base-field wrappers and extension packing together with all
conversion dependencies, number layouts, and image name bindings. -/
def Image.certifyFields (image : Image) : Except String image.FieldCertified := do
  match names : image.fieldCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← FieldArithmetic.certify image.program candidates.links }

structure Image.NatLoopCandidates (image : Image) where
  links : NatLoops.Links
  layouts : image.HasNumberLayout links.arithmetic.conversions.layout

def Image.natLoopCandidates (image : Image) : Except String image.NatLoopCandidates := do
  let arithmetic ← image.natArithmeticCandidates
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing Nat loop runtime name {name}"
  let links : NatLoops.Links := {
    arithmetic := arithmetic.links
    shiftRightLoop := ← function `Ixby.Runtime.shiftRightLoop
    log2Loop := ← function `Ixby.Runtime.log2Loop
    powLoop := ← function `Ixby.Runtime.powLoop
    shiftRight := ← function `Nat.shiftRight
    log2 := ← function `Nat.log2
    pow := ← function `Nat.pow }
  return { links, layouts := arithmetic.layouts }

structure Image.NatLoopCertified (image : Image) where
  candidates : image.NatLoopCandidates
  names : image.natLoopCandidates = .ok candidates
  certificate : NatLoops.Certificate image.program candidates.links

def Image.NatLoopCertified.links {image : Image} (certified : image.NatLoopCertified) :
    NatLoops.Links := certified.candidates.links

theorem Image.NatLoopCertified.layouts {image : Image} (certified : image.NatLoopCertified) :
    image.HasNumberLayout certified.links.arithmetic.conversions.layout := certified.candidates.layouts

/-- Check all six loop/wrapper bodies together with multiplication and its
conversion dependencies, number layouts, and image name bindings. -/
def Image.certifyNatLoops (image : Image) : Except String image.NatLoopCertified := do
  match names : image.natLoopCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← NatLoops.certify image.program candidates.links }


structure Image.WordCandidates (image : Image) where
  links : Words.Links
  layouts : image.HasNumberLayout links.conversions.layout

def Image.wordCandidates (image : Image) : Except String image.WordCandidates := do
  let conversions ← image.conversionCandidates
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing word runtime name {name}"
  let links : Words.Links := {
    conversions := conversions.links
    u8OfNat := ← function `UInt8.ofNat
    u8ToNat := ← function `UInt8.toNat
    u8ToU32 := ← function `UInt8.toUInt32
    u8Equal := ← function `UInt8.decEq
    u8Add := ← function `UInt8.add
    u8ShiftLeft := ← function `UInt8.shiftLeft
    u8ShiftRight := ← function `UInt8.shiftRight
    u32OfNat := ← function `UInt32.ofNat
    u32OfNatLT := ← function `UInt32.ofNatLT
    u32ToU8 := ← function `UInt32.toUInt8
    u32ToNat := ← function `UInt32.toNat
    u32Add := ← function `UInt32.add
    u32Sub := ← function `UInt32.sub
    u32Mul := ← function `UInt32.mul
    u32And := ← function `UInt32.land
    u32Or := ← function `UInt32.lor
    u32Xor := ← function `UInt32.xor
    u32ShiftLeft := ← function `UInt32.shiftLeft
    u32ShiftRight := ← function `UInt32.shiftRight
    u32Equal := ← function `UInt32.decEq
    u32Less := ← function `UInt32.decLt
    usizeOfNat := ← function `USize.ofNat
    usizeToNat := ← function `USize.toNat
    usizeAdd := ← function `USize.add
    usizeSub := ← function `USize.sub
    usizeEqual := ← function `USize.decEq
    usizeLess := ← function `USize.decLt }
  return { links, layouts := conversions.layouts }

structure Image.WordCertified (image : Image) where
  candidates : image.WordCandidates
  names : image.wordCandidates = .ok candidates
  certificate : Words.Certificate image.program candidates.links

def Image.WordCertified.links {image : Image} (certified : image.WordCertified) :
    Words.Links := certified.candidates.links

theorem Image.WordCertified.layouts {image : Image} (certified : image.WordCertified) :
    image.HasNumberLayout certified.links.conversions.layout := certified.candidates.layouts

/-- Check all twenty-seven word helpers together with the complete conversion
dependencies, number layouts, and source name bindings. -/
def Image.certifyWords (image : Image) : Except String image.WordCertified := do
  match names : image.wordCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← Words.certify image.program candidates.links }

def Image.HasArrayTreeLayout (image : Image) (layout : ArrayTrees.Layout) : Prop :=
  image.ctorId `Ixby.Runtime.Empty = .ok layout.empty ∧
  image.ctorId `Ixby.Runtime.Leaf = .ok layout.leaf ∧
  image.ctorId `Ixby.Runtime.Node = .ok layout.node ∧
  image.ctorId `Ixby.Runtime.Array = .ok layout.array ∧
  image.ctorId `Ixby.Runtime.Bytes = .ok layout.bytes ∧
  image.ctorId `Ixby.Runtime.Rope = .ok layout.rope

structure Image.ArrayTreeLayoutWitness (image : Image) where
  layout : ArrayTrees.Layout
  layouts : image.HasArrayTreeLayout layout

def Image.certifyArrayTreeLayout (image : Image) : Except String image.ArrayTreeLayoutWitness := do
  match empty : image.ctorId `Ixby.Runtime.Empty with
  | .error message => throw message
  | .ok emptyId =>
    match leaf : image.ctorId `Ixby.Runtime.Leaf with
    | .error message => throw message
    | .ok leafId =>
      match node : image.ctorId `Ixby.Runtime.Node with
      | .error message => throw message
      | .ok nodeId =>
        match array : image.ctorId `Ixby.Runtime.Array with
        | .error message => throw message
        | .ok arrayId =>
          match bytes : image.ctorId `Ixby.Runtime.Bytes with
          | .error message => throw message
          | .ok bytesId =>
            match rope : image.ctorId `Ixby.Runtime.Rope with
            | .error message => throw message
            | .ok ropeId =>
              return {
                layout := ⟨emptyId, leafId, nodeId, arrayId, bytesId, ropeId⟩
                layouts := ⟨empty, leaf, node, array, bytes, rope⟩ }

structure Image.ArrayTreeCandidates (image : Image) where
  links : ArrayTrees.Links
  numbers : image.HasNumberLayout links.arithmetic.conversions.layout
  layouts : image.HasArrayTreeLayout links.layout

def Image.arrayTreeCandidates (image : Image) : Except String image.ArrayTreeCandidates := do
  let arithmetic ← image.natArithmeticCandidates
  let layout ← image.certifyArrayTreeLayout
  let function (name : Name) : Except String Nat :=
    match image.state.functionNames[name]? with
    | some id => .ok id
    | none => .error s!"missing array runtime name {name}"
  let constructor (name : Name) : Except String Nat :=
    match image.state.constructorNames[name]? with
    | some id => .ok id
    | none => .error s!"missing array constructor name {name}"
  let links : ArrayTrees.Links := {
    arithmetic := arithmetic.links
    layout := layout.layout
    emptyCtor := ← constructor `Ixby.Runtime.Empty
    leafCtor := ← constructor `Ixby.Runtime.Leaf
    nodeCtor := ← constructor `Ixby.Runtime.Node
    arrayCtor := ← constructor `Ixby.Runtime.Array
    bytesCtor := ← constructor `Ixby.Runtime.Bytes
    ropeCtor := ← constructor `Ixby.Runtime.Rope
    treeGet := ← function `Ixby.Runtime.treeGet
    treeSet := ← function `Ixby.Runtime.treeSet
    size := ← function `Array.size
    usize := ← function `Array.usize
    empty := ← function `Array.emptyWithCapacity
    mkEmpty := ← function `Array.mkEmpty
    get := ← function `Array.getInternal
    getBorrowed := ← function `Array.getInternalBorrowed
    uget := ← function `Array.uget
    ugetBorrowed := ← function `Array.ugetBorrowed
    getBang := ← function `Array.get!Internal
    getBangBorrowed := ← function `Array.get!InternalBorrowed
    push := ← function `Array.push
    set := ← function `Array.set!
    uset := ← function `Array.uset
    usizeOfNat := ← function `USize.ofNat
    copyArray := ← function `Ixby.Runtime.copyArray
    byteGet := ← function `Ixby.Runtime.byteGet
  }
  return { links := links, numbers := arithmetic.layouts, layouts := layout.layouts }

structure Image.ArrayTreeCertified (image : Image) where
  candidates : image.ArrayTreeCandidates
  names : image.arrayTreeCandidates = .ok candidates
  certificate : ArrayTrees.Certificate image.program candidates.links

def Image.ArrayTreeCertified.links {image : Image} (certified : image.ArrayTreeCertified) :
    ArrayTrees.Links := certified.candidates.links

theorem Image.ArrayTreeCertified.numbers {image : Image} (certified : image.ArrayTreeCertified) :
    image.HasNumberLayout certified.links.arithmetic.conversions.layout := certified.candidates.numbers

theorem Image.ArrayTreeCertified.layouts {image : Image} (certified : image.ArrayTreeCertified) :
    image.HasArrayTreeLayout certified.links.layout := certified.candidates.layouts

/-- Bind all fifteen tree-slice helper bodies and their numeric dependencies
to this image. Byte callbacks are located for exact code matching; their
executions are outside the tree-backed contracts. -/
def Image.certifyArrayTrees (image : Image) : Except String image.ArrayTreeCertified := do
  match names : image.arrayTreeCandidates with
  | .error message => throw message
  | .ok candidates => return {
      candidates
      names
      certificate := ← ArrayTrees.certify image.program candidates.links }

end Compilatrix.Ixby.LeanFrontend
